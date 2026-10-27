module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndRoots
public import CFSG.LieType.Multipliers.U62

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem inf_conjR_decomp [Finite G] {M M' T : Subgroup G} (hc : ⁅M, M'⁆ = ⊥)
    (hodd : Odd (Nat.card (M ⊓ M' : Subgroup G))) (hT : IsSylowOf 2 T (M ⊔ M'))
    (hn : M ⊔ M' ≤ normalizer (M : Set G)) (hn' : M ⊔ M' ≤ normalizer (M' : Set G)) {g : G}
    (hgM : g ∈ normalizer (M : Set G)) (hgM' : g ∈ normalizer (M' : Set G)) :
    T ⊓ conjR T g = ((T ⊓ conjR T g) ⊓ M) ⊔ ((T ⊓ conjR T g) ⊓ M') := by
  have hT' := sylow_eq_sup hc hodd hT hn hn'
  have hgM₁ : conjR M g = M := conjR_eq_self hgM
  have hgM₂ : conjR M' g = M' := conjR_eq_self hgM'
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hdec : T ⊓ conjR T g = ((T ⊓ M) ⊓ conjR (T ⊓ M) g) ⊔
      ((T ⊓ M') ⊓ conjR (T ⊓ M') g) := by
    conv_lhs => rw [hT', conjR_sup]
    exact sup_inf_sup hc hodd inf_le_right
      ((conjR_mono (inf_le_right : T ⊓ M ≤ M) g).trans hgM₁.le) inf_le_right
      ((conjR_mono (inf_le_right : T ⊓ M' ≤ M') g).trans hgM₂.le) (hT2.to_le inf_le_left)
      ((hT2.to_le inf_le_left).map _)
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  conv_lhs => rw [hdec]
  exact sup_le_sup (le_inf (hdec ▸ le_sup_left) (inf_le_left.trans inf_le_right))
    (le_inf (hdec ▸ le_sup_right) (inf_le_left.trans inf_le_right))

theorem le_sup_inf_of_mul_conj_mem {M M' W : Subgroup G} {t : G} (hc : ⁅M, M'⁆ = ⊥)
    (hWM : W ≤ M) (hconj : ∀ m ∈ M, t * m * t⁻¹ ∈ M')
    (hx : ∀ m ∈ M, m * (t * m * t⁻¹) ∈ W ⊔ M') : M ≤ W ⊔ (M ⊓ M') := by
  have hMC : M ≤ centralizer (M' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  intro m hm
  have hxWM : m * (t * m * t⁻¹) ∈ (W : Set G) * (M' : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right W M'
      (hWM.trans (hMC.trans (centralizer_le_normalizer _)))]
    exact hx m hm
  obtain ⟨w, hw, m', hm', hwm⟩ := hxWM
  beta_reduce at hwm
  have hz : w⁻¹ * m ∈ M ⊓ M' := by
    refine ⟨M.mul_mem (M.inv_mem (hWM hw)) hm, ?_⟩
    have : w⁻¹ * m = m' * (t * m * t⁻¹)⁻¹ := by
      calc w⁻¹ * m = w⁻¹ * (m * (t * m * t⁻¹)) * (t * m * t⁻¹)⁻¹ := by group
        _ = w⁻¹ * (w * m') * (t * m * t⁻¹)⁻¹ := by rw [← hwm]
        _ = m' * (t * m * t⁻¹)⁻¹ := by group
    rw [this]
    exact M'.mul_mem hm' (M'.inv_mem (hconj m hm))
  have : m = w * (w⁻¹ * m) := by group
  rw [this]
  exact mul_mem (mem_sup_left hw) (mem_sup_right hz)

theorem le_of_mul_conj_mem_of_perfect {M M' W : Subgroup G} {t : G} (hc : ⁅M, M'⁆ = ⊥)
    (hWM : W ≤ M) (hperf : ⁅M, M⁆ = M) (hconj : ∀ m ∈ M, t * m * t⁻¹ ∈ M')
    (hx : ∀ m ∈ M, m * (t * m * t⁻¹) ∈ W ⊔ M') : M ≤ W := by
  have hMC : M ≤ centralizer (M' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have hMeq : M = W ⊔ (M ⊓ M') :=
    le_antisymm (le_sup_inf_of_mul_conj_mem hc hWM hconj hx) (sup_le hWM inf_le_left)
  have hWZ : ∀ w ∈ W, ∀ z ∈ M ⊓ M', w * z = z * w := fun w hw z hz =>
    (mem_centralizer_iff.mp (hMC (hWM hw)) z hz.2).symm
  have hZZ : ∀ z ∈ M ⊓ M', ∀ z' ∈ M ⊓ M', z * z' = z' * z := fun z hz z' hz' =>
    (mem_centralizer_iff.mp (hMC hz.1) z' hz'.2).symm
  rw [← hperf]
  conv_lhs => rw [hMeq]
  exact YamadaSection4.commutator_sup_le hWZ hZZ

theorem le_of_mul_conj_mem_of_inf_eq_bot {M M' W : Subgroup G} {t : G} (hc : ⁅M, M'⁆ = ⊥)
    (hWM : W ≤ M) (hinf : M ⊓ M' = ⊥) (hconj : ∀ m ∈ M, t * m * t⁻¹ ∈ M')
    (hx : ∀ m ∈ M, m * (t * m * t⁻¹) ∈ W ⊔ M') : M ≤ W := by
  have := le_sup_inf_of_mul_conj_mem hc hWM hconj hx
  rwa [hinf, sup_bot_eq] at this

theorem le_or_le_of_quasisimple {G₁ G₂ Q : Subgroup G} (hQ : CFSG.Open.IsQuasisimple Q)
    (hc : ⁅G₁, G₂⁆ = ⊥) (hQle : Q ≤ G₁ ⊔ G₂) (hQn : G₁ ⊔ G₂ ≤ normalizer (Q : Set G)) :
    Q ≤ G₁ ∨ Q ≤ G₂ := by
  have h12 : G₁ ≤ centralizer (G₂ : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have h21 : G₂ ≤ centralizer (G₁ : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp (by rw [commutator_comm]; exact hc)
  have hn₁ : Q ≤ normalizer (G₁ : Set G) :=
    hQle.trans (sup_le le_normalizer (h21.trans (centralizer_le_normalizer _)))
  have hn₂ : Q ≤ normalizer (G₂ : Set G) :=
    hQle.trans (sup_le (h12.trans (centralizer_le_normalizer _)) le_normalizer)
  have hperf := commutator_eq_self_of_quasisimple hQ
  have key : ∀ X : Subgroup G, Q ≤ normalizer (X : Set G) → X ≤ normalizer (Q : Set G) →
      Q ⊓ X ≤ centralizer (Q : Set G) → ⁅Q, X⁆ = ⊥ := by
    intro X hQX hXQ hcen
    have h1 : ⁅⁅Q, X⁆, Q⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      exact (commutator_le_inf_of_le_normalizer hQX hXQ).trans hcen
    have h2 : ⁅⁅X, Q⁆, Q⁆ = ⊥ := by rw [commutator_comm X Q]; exact h1
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hperf] at h3
  have hQN : ∀ X : Subgroup G, Q ≤ normalizer (X : Set G) →
      Q ≤ normalizer ((Q ⊓ X : Subgroup G) : Set G) := fun X hQX q hq =>
    YamadaEnd.mem_normalizer_inf (le_normalizer hq) (hQX hq)
  by_cases h₁ : Q ⊓ G₁ ≤ centralizer (Q : Set G)
  · by_cases h₂ : Q ⊓ G₂ ≤ centralizer (Q : Set G)
    · exfalso
      have hne₁ := key G₁ hn₁ (le_sup_left.trans hQn) h₁
      have hne₂ := key G₂ hn₂ (le_sup_right.trans hQn) h₂
      apply not_le_centralizer_self_of_quasisimple hQ
      intro q hq
      have hq1 := (commutator_eq_bot_iff_le_centralizer).mp hne₁ hq
      have hq2 := (commutator_eq_bot_iff_le_centralizer).mp hne₂ hq
      have hcen := mem_centralizer_sup (A := G₁) (B := G₂) (y := q)
        (fun a ha => mem_centralizer_iff.mp hq1 a ha) (fun b hb => mem_centralizer_iff.mp hq2 b hb)
      rw [mem_centralizer_iff] at hcen ⊢
      exact fun z hz => hcen z (hQle hz)
    · right
      have := eq_of_le_of_not_le_centralizer hQ inf_le_left (hQN G₂ hn₂) h₂
      exact this ▸ inf_le_right
  · left
    have := eq_of_le_of_not_le_centralizer hQ inf_le_left (hQN G₁ hn₁) h₁
    exact this ▸ inf_le_right

theorem isQuasisimple_of_injective {X Y : Subgroup G} (φ : X →* G)
    (hinj : Function.Injective φ) (hrange : φ.range = Y) (hY : CFSG.Open.IsQuasisimple Y) :
    CFSG.Open.IsQuasisimple X :=
  isQuasisimple_of_mulEquiv ((MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr hrange)).symm hY

theorem commutator_eq_top_of_commutator_eq {X : Subgroup G} (h : ⁅X, X⁆ = X) :
    commutator X = ⊤ := by
  apply map_injective X.subtype_injective
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype, h]

theorem commutator_eq_self_of_isSimpleGroup {X : Subgroup G} [IsSimpleGroup X]
    (hX : ¬ X ≤ centralizer (X : Set G)) : ⁅X, X⁆ = X := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    apply hX
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have : ⁅(⟨y, hy⟩ : X), ⟨x, hx⟩⁆ ∈ commutator X :=
      commutator_mem_commutator (mem_top _) (mem_top _)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact congrArg Subtype.val this
  · have := congrArg (map X.subtype) h
    rwa [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at this

theorem exists_mul_conj_mul_of_fixed {A A' : Subgroup G} {t : G} (hc : ⁅A, A'⁆ = ⊥)
    (hconj : ∀ a ∈ A, t * a * t⁻¹ ∈ A') (hconj' : ∀ a ∈ A', t * a * t⁻¹ ∈ A) {g : G}
    (hg : g ∈ A ⊔ A') (hgt : t * g * t⁻¹ = g) :
    ∃ x ∈ A, ∃ z ∈ A ⊓ A', g = x * (t * x * t⁻¹) * z := by
  have hAC : A ≤ centralizer (A' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have hmul : g ∈ (A : Set G) * (A' : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right A A' (hAC.trans (centralizer_le_normalizer _))]
    exact hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hmul
  beta_reduce at hgt ⊢
  have ha : t * x * t⁻¹ ∈ A' := hconj x hx
  have hb : t * y * t⁻¹ ∈ A := hconj' y hy
  have hba : t * y * t⁻¹ * (t * x * t⁻¹) = x * y := by
    have hcomm : t * x * t⁻¹ * (t * y * t⁻¹) = t * y * t⁻¹ * (t * x * t⁻¹) :=
      mem_centralizer_iff.mp (hAC hb) _ ha
    rw [← hcomm, ← hgt]
    group
  have hc' : x⁻¹ * (t * y * t⁻¹) ∈ A := A.mul_mem (A.inv_mem hx) hb
  have hy' : y = x⁻¹ * (t * y * t⁻¹) * (t * x * t⁻¹) := by
    calc y = x⁻¹ * (x * y) := by group
      _ = x⁻¹ * (t * y * t⁻¹ * (t * x * t⁻¹)) := by rw [hba]
      _ = x⁻¹ * (t * y * t⁻¹) * (t * x * t⁻¹) := by group
  have hcomm2 : t * x * t⁻¹ * (x⁻¹ * (t * y * t⁻¹)) =
      x⁻¹ * (t * y * t⁻¹) * (t * x * t⁻¹) := mem_centralizer_iff.mp (hAC hc') _ ha
  have hz : (t * x * t⁻¹)⁻¹ * y = x⁻¹ * (t * y * t⁻¹) := by
    calc (t * x * t⁻¹)⁻¹ * y
        = (t * x * t⁻¹)⁻¹ * (x⁻¹ * (t * y * t⁻¹) * (t * x * t⁻¹)) := by rw [← hy']
      _ = (t * x * t⁻¹)⁻¹ * (t * x * t⁻¹ * (x⁻¹ * (t * y * t⁻¹))) := by rw [hcomm2]
      _ = x⁻¹ * (t * y * t⁻¹) := by group
  refine ⟨x, hx, (t * x * t⁻¹)⁻¹ * y, ⟨hz ▸ hc', A'.mul_mem (A'.inv_mem ha) hy⟩, by group⟩

theorem le_range_diagHom {A A' K : Subgroup G} {t : G} (hc : ⁅A, A'⁆ = ⊥)
    (hconj : ∀ a ∈ A, t * a * t⁻¹ ∈ A') (hconj' : ∀ a ∈ A', t * a * t⁻¹ ∈ A)
    (hcomm : ∀ u ∈ A, ∀ v ∈ A, v * (t * u * t⁻¹) = t * u * t⁻¹ * v)
    (hK : K ≤ A ⊔ A') (hKt : K ≤ centralizer ({t} : Set G)) (hperf : ⁅K, K⁆ = K) :
    K ≤ (diagHom A t hcomm).range := by
  have hAC : A ≤ centralizer (A' : Set G) := (commutator_eq_bot_iff_le_centralizer).mp hc
  have hA'C : A' ≤ centralizer (A : Set G) :=
    (commutator_eq_bot_iff_le_centralizer).mp (by rw [commutator_comm]; exact hc)
  have hRle : (diagHom A t hcomm).range ≤ A ⊔ A' := by
    rintro _ ⟨x, rfl⟩
    rw [diagHom_apply]
    exact mul_mem (mem_sup_left x.2) (mem_sup_right (hconj x x.2))
  have hZc : ∀ z ∈ A ⊓ A', z ∈ centralizer ((A ⊔ A' : Subgroup G) : Set G) := fun z hz =>
    mem_centralizer_sup (fun a ha => mem_centralizer_iff.mp (hA'C hz.2) a ha)
      (fun b hb => mem_centralizer_iff.mp (hAC hz.1) b hb)
  have hKR : K ≤ (diagHom A t hcomm).range ⊔ (A ⊓ A') := by
    intro g hg
    have hgt : t * g * t⁻¹ = g := by
      rw [← mem_centralizer_singleton_iff.mp (hKt hg), mul_inv_cancel_right]
    obtain ⟨x, hx, z, hz, rfl⟩ := exists_mul_conj_mul_of_fixed hc hconj hconj' (hK hg) hgt
    exact mul_mem (mem_sup_left ⟨⟨x, hx⟩, rfl⟩) (mem_sup_right hz)
  have hRZ : ∀ r ∈ (diagHom A t hcomm).range, ∀ z ∈ A ⊓ A', r * z = z * r := fun r hr z hz =>
    mem_centralizer_iff.mp (hZc z hz) r (hRle hr)
  have hZZ : ∀ z ∈ A ⊓ A', ∀ z' ∈ A ⊓ A', z * z' = z' * z := fun z hz z' hz' =>
    mem_centralizer_iff.mp (hZc z' hz') z (mem_sup_left hz.1)
  rw [← hperf]
  exact (commutator_mono hKR hKR).trans (YamadaSection4.commutator_sup_le hRZ hZZ)

theorem card_ker_dvd_twelve
    {E S : Type} [Group E] [Group S] [Group.IsPerfect E]
    (hS : LieModel S .PSU 6 2 1) (q : E →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) : Nat.card q.ker ∣ 12 := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U62.multiplier_PSU_six_two S hS
  have hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) = 12 := by
    rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv,
      Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
      Nat.card_prod]
    simp
  rw [← CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker, ← hM]
  exact Subgroup.card_map_dvd _ _

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
