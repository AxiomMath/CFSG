module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveMFix
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWCat

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section BarImage

variable {G : Type} [Group G] (W : Subgroup G)

@[expose] def barImg (H : Subgroup G) : Subgroup (seitzBar W) :=
  (H.subgroupOf (normalizer (W : Set G))).map
    (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))

variable {W}

theorem mem_barImg_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H)
    (hxN : x ∈ normalizer (W : Set G)) :
    QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨x, hxN⟩ ∈ barImg W H :=
  ⟨⟨x, hxN⟩, mem_subgroupOf.2 hx, rfl⟩

theorem exists_of_mem_barImg {H : Subgroup G} {z : seitzBar W} (hz : z ∈ barImg W H) :
    ∃ x ∈ H, ∃ hxN : x ∈ normalizer (W : Set G),
      QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨x, hxN⟩ = z := by
  obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := hz
  exact ⟨x, mem_subgroupOf.1 hx, hxN, rfl⟩

theorem mk_eq_one_iff_mem {x : G} (hxN : x ∈ normalizer (W : Set G)) :
    QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) ⟨x, hxN⟩ = 1 ↔ x ∈ W := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem le_of_barImg_eq_bot {H : Subgroup G} (hH : H ≤ normalizer (W : Set G))
    (h : barImg W H = ⊥) : H ≤ W := by
  intro x hx
  have h1 := mem_barImg_of_mem hx (hH hx)
  rw [h, mem_bot, mk_eq_one_iff_mem] at h1
  exact h1

theorem le_sup_of_barImg_le {H H' : Subgroup G} (hH : H ≤ normalizer (W : Set G))
    (h : barImg W H ≤ barImg W H') : H ≤ H' ⊔ W := by
  intro x hx
  obtain ⟨y, hy, hyN, hyx⟩ := exists_of_mem_barImg (h (mem_barImg_of_mem hx (hH hx)))
  have h1 : y⁻¹ * x ∈ W := by
    have h2 : QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
        ((⟨y, hyN⟩ : normalizer (W : Set G))⁻¹ * ⟨x, hH hx⟩) = 1 := by
      rw [map_mul, map_inv, hyx, inv_mul_cancel]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h2
    exact h2
  have h3 := mul_mem (mem_sup_left hy) (mem_sup_right h1 : y⁻¹ * x ∈ H' ⊔ W)
  rwa [mul_inv_cancel_left] at h3

theorem barImg_mono {H H' : Subgroup G} (h : H ≤ H') : barImg W H ≤ barImg W H' :=
  map_mono fun _ hx => mem_subgroupOf.2 (h (mem_subgroupOf.1 hx))

theorem barImg_inf_le (H H' : Subgroup G) : barImg W (H ⊓ H') ≤ barImg W H ⊓ barImg W H' :=
  le_inf (barImg_mono inf_le_left) (barImg_mono inf_le_right)

theorem commutator_subgroupOf_of_le_both {N H H' : Subgroup G} (hH : H ≤ N) (hH' : H' ≤ N) :
    ⁅H, H'⁆.subgroupOf N = ⁅H.subgroupOf N, H'.subgroupOf N⁆ := by
  apply Subgroup.map_injective N.subtype_injective
  have hc : ⁅H, H'⁆ ≤ N :=
    (commutator_mono hH hH').trans (CFSG.Quasithin.A3.commutator_self_le N)
  rw [map_commutator, map_subgroupOf_eq_of_le hc, map_subgroupOf_eq_of_le hH,
    map_subgroupOf_eq_of_le hH']

theorem sup_subgroupOf_of_le {N H H' : Subgroup G} (hH : H ≤ N) (hH' : H' ≤ N) :
    (H ⊔ H').subgroupOf N = H.subgroupOf N ⊔ H'.subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hH hH'), map_subgroupOf_eq_of_le hH,
    map_subgroupOf_eq_of_le hH']

theorem barImg_commutator {H H' : Subgroup G} (hH : H ≤ normalizer (W : Set G))
    (hH' : H' ≤ normalizer (W : Set G)) :
    barImg W ⁅H, H'⁆ = ⁅barImg W H, barImg W H'⁆ := by
  rw [barImg, barImg, barImg, ← map_commutator, commutator_subgroupOf_of_le_both hH hH']

theorem barImg_sup {H H' : Subgroup G} (hH : H ≤ normalizer (W : Set G))
    (hH' : H' ≤ normalizer (W : Set G)) :
    barImg W (H ⊔ H') = barImg W H ⊔ barImg W H' := by
  rw [barImg, barImg, barImg, ← Subgroup.map_sup, sup_subgroupOf_of_le hH hH']

theorem barImg_map_conj {H : Subgroup G} (hH : H ≤ normalizer (W : Set G)) {t : G}
    (htN : t ∈ normalizer (W : Set G)) :
    barImg W (H.map (MulAut.conj t).toMonoidHom) =
      (barImg W H).map (MulAut.conj (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
        ⟨t, htN⟩)).toMonoidHom := by
  set q := QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))) with hq
  apply le_antisymm
  · rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    obtain ⟨h, hh, rfl⟩ := mem_subgroupOf.1 hx
    refine ⟨q ⟨h, hH hh⟩, mem_barImg_of_mem hh (hH hh), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  · rintro _ ⟨_, ⟨⟨h, hhN⟩, hh, rfl⟩, rfl⟩
    have hh' : h ∈ H := mem_subgroupOf.1 hh
    have hxN : t * h * t⁻¹ ∈ normalizer (W : Set G) := mul_mem (mul_mem htN hhN) (inv_mem htN)
    refine ⟨⟨t * h * t⁻¹, hxN⟩, mem_subgroupOf.2 ⟨h, hh', rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem card_eq_card_barImg_mul [Finite G] {H : Subgroup G} (hH : H ≤ normalizer (W : Set G)) :
    Nat.card H = Nat.card (barImg W H) * Nat.card (H ⊓ W : Subgroup G) := by
  set N := normalizer (W : Set G) with hN
  set q := QuotientGroup.mk' (W.subgroupOf N) with hq
  set φ : H.subgroupOf N →* seitzBar W := q.comp (H.subgroupOf N).subtype with hφ
  have hrange : φ.range = barImg W H := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
    rfl
  have hker : (φ.ker.map (H.subgroupOf N).subtype).map N.subtype = H ⊓ W := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hx' : q (x : N) = 1 := MonoidHom.mem_ker.1 hx
      exact mem_inf.2 ⟨mem_subgroupOf.1 x.2, (mk_eq_one_iff_mem (x : N).2).1 hx'⟩
    · intro hg
      obtain ⟨hgH, hgW⟩ := mem_inf.1 hg
      have hgN : g ∈ N := hH hgH
      refine ⟨⟨g, hgN⟩, ⟨⟨⟨g, hgN⟩, mem_subgroupOf.2 hgH⟩, ?_, rfl⟩, rfl⟩
      exact MonoidHom.mem_ker.2 ((mk_eq_one_iff_mem hgN).2 hgW)
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card (H.subgroupOf N) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv
  rw [← hker, Subgroup.card_map_of_injective N.subtype_injective,
    Subgroup.card_map_of_injective (H.subgroupOf N).subtype_injective, ← hrange, mul_comm, h1, h2]

end BarImage

section BarLift

variable {G : Type} [Group G] {W : Subgroup G}

@[expose] def barLift (A : Subgroup (seitzBar W)) : Subgroup G :=
  (CFSG.Quasithin.perfectCore
    (A.comap (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))))).map
      (normalizer (W : Set G)).subtype

theorem barLift_le_normalizer (A : Subgroup (seitzBar W)) :
    barLift A ≤ normalizer (W : Set G) :=
  map_subtype_le _

variable [Finite G]

theorem barLift_perfect (A : Subgroup (seitzBar W)) : ⁅barLift A, barLift A⁆ = barLift A := by
  rw [barLift, ← map_commutator, CFSG.Quasithin.perfectCore_perfect]

theorem barImg_barLift {A : Subgroup (seitzBar W)} (hA : ⁅A, A⁆ = A) :
    barImg W (barLift A) = A := by
  have h1 : (barLift A).subgroupOf (normalizer (W : Set G)) = CFSG.Quasithin.perfectCore
      (A.comap (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G))))) :=
    comap_map_eq_self_of_injective (subtype_injective _) _
  rw [barImg, h1, CFSG.Quasithin.map_perfectCore,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hA]

theorem le_normalizer_barLift (A : Subgroup (seitzBar W)) :
    W ≤ normalizer (barLift A : Set G) := by
  intro w hw
  have hwN : w ∈ normalizer (W : Set G) := le_normalizer hw
  set P := A.comap (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))) with hP
  have hwP : (⟨w, hwN⟩ : normalizer (W : Set G)) ∈ P := by
    rw [hP, mem_comap, (mk_eq_one_iff_mem hwN).2 hw]
    exact one_mem A
  have hwNP : (⟨w, hwN⟩ : normalizer (W : Set G)) ∈
      normalizer (CFSG.Quasithin.perfectCore P : Set (normalizer (W : Set G))) :=
    CFSG.Quasithin.normalizer_le_normalizer_perfectCore P (le_normalizer hwP)
  apply mem_normalizer_of_conj_mem_finite
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨_, (mem_normalizer_iff.1 hwNP x).1 hx, rfl⟩

theorem barLift_swap_facts {t : G} (htN : t ∈ normalizer (W : Set G))
    {A : Subgroup (seitzBar W)} (hA : ⁅A, A⁆ = A)
    (hcomm : ⁅A, A.map (MulAut.conj (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
      ⟨t, htN⟩)).toMonoidHom⁆ = ⊥)
    (hinf : A ⊓ A.map (MulAut.conj (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
      ⟨t, htN⟩)).toMonoidHom = ⊥)
    {D : Subgroup G} (hDN : D ≤ normalizer (W : Set G))
    (hD : barImg W D ≤ A ⊔ A.map (MulAut.conj (QuotientGroup.mk' (W.subgroupOf
      (normalizer (W : Set G))) ⟨t, htN⟩)).toMonoidHom) :
    ⁅barLift A, barLift A⁆ = barLift A ∧ barLift A ≤ normalizer (W : Set G) ∧
      W ≤ normalizer (barLift A : Set G) ∧
      ⁅barLift A, (barLift A).map (MulAut.conj t).toMonoidHom⁆ ≤ W ∧
      barLift A ⊓ (barLift A).map (MulAut.conj t).toMonoidHom ≤ W ∧
      D ≤ (barLift A ⊔ (barLift A).map (MulAut.conj t).toMonoidHom) ⊔ W := by
  have hXN := barLift_le_normalizer A
  have hYN : (barLift A).map (MulAut.conj t).toMonoidHom ≤ normalizer (W : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem htN (hXN hx)) (inv_mem htN)
  have hX := barImg_barLift hA
  have hY : barImg W ((barLift A).map (MulAut.conj t).toMonoidHom) =
      A.map (MulAut.conj (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
        ⟨t, htN⟩)).toMonoidHom := by
    rw [barImg_map_conj hXN htN, hX]
  refine ⟨barLift_perfect A, hXN, le_normalizer_barLift A, ?_, ?_, ?_⟩
  · apply le_of_barImg_eq_bot
      ((commutator_mono hXN hYN).trans (CFSG.Quasithin.A3.commutator_self_le _))
    rw [barImg_commutator hXN hYN, hX, hY, hcomm]
  · apply le_of_barImg_eq_bot (inf_le_left.trans hXN)
    rw [eq_bot_iff, ← hinf]
    exact (barImg_inf_le _ _).trans (le_of_eq (by rw [hX, hY]))
  · apply le_sup_of_barImg_le hDN
    rw [barImg_sup hXN hYN, hX, hY]
    exact hD

theorem commutator_barLift_map_conj_le {t : G} (htN : t ∈ normalizer (W : Set G))
    {A : Subgroup (seitzBar W)} (hA : ⁅A, A⁆ = A)
    (hcomm : ⁅A, A.map (MulAut.conj (QuotientGroup.mk' (W.subgroupOf (normalizer (W : Set G)))
      ⟨t, htN⟩)).toMonoidHom⁆ = ⊥) :
    ⁅barLift A, (barLift A).map (MulAut.conj t).toMonoidHom⁆ ≤ W := by
  have hXN := barLift_le_normalizer A
  have hYN : (barLift A).map (MulAut.conj t).toMonoidHom ≤ normalizer (W : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem htN (hXN hx)) (inv_mem htN)
  apply le_of_barImg_eq_bot
    ((commutator_mono hXN hYN).trans (CFSG.Quasithin.A3.commutator_self_le _))
  rw [barImg_commutator hXN hYN, barImg_map_conj hXN htN, barImg_barLift hA, hcomm]

theorem barImg_le_normalizer {X M : Subgroup G} (h : X ≤ normalizer (M : Set G)) :
    barImg W X ≤ normalizer (barImg W M : Set (seitzBar W)) := by
  intro z hz
  obtain ⟨x, hx, hxN, rfl⟩ := exists_of_mem_barImg hz
  apply mem_normalizer_of_conj_mem_finite
  intro w hw
  obtain ⟨m, hm, hmN, rfl⟩ := exists_of_mem_barImg hw
  rw [← map_inv, ← map_mul, ← map_mul]
  exact mem_barImg_of_mem ((mem_normalizer_iff.1 (h hx) m).1 hm) _

theorem le_centralizer_or_inf_le_of_simple {A : Subgroup (seitzBar W)} (hA : ⁅A, A⁆ = A)
    (hsimp : ∀ M : Subgroup (seitzBar W), M ≤ A → A ≤ normalizer (M : Set (seitzBar W)) →
      M = ⊥ ∨ M = A)
    (hW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) {U : Subgroup G} (hUW : U ≤ W)
    (hXU : barLift A ≤ normalizer (U : Set G)) :
    barLift A ≤ centralizer (U : Set G) ∨ barLift A ⊓ centralizer (U : Set G) ≤ W := by
  have hXN := barLift_le_normalizer A
  have hX := barImg_barLift hA
  have hMN : barLift A ⊓ centralizer (U : Set G) ≤ normalizer (W : Set G) := inf_le_left.trans hXN
  have hXM : barLift A ≤ normalizer ((barLift A ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
    apply le_normalizer_of_mul_mul_inv_mem
    intro x hx m hm
    obtain ⟨hmX, hmC⟩ := mem_inf.1 hm
    refine mem_inf.2 ⟨mul_mem (mul_mem hx hmX) (inv_mem hx), mem_centralizer_iff.2 fun u hu => ?_⟩
    have hu' : x⁻¹ * u * x ∈ U := by
      have h1 := (mem_normalizer_iff.1 (hXU (inv_mem hx)) u).1 hu
      rwa [inv_inv] at h1
    have h2 : (x⁻¹ * u * x) * m = m * (x⁻¹ * u * x) := mem_centralizer_iff.1 hmC _ hu'
    calc u * (x * m * x⁻¹) = x * ((x⁻¹ * u * x) * m) * x⁻¹ := by group
      _ = x * (m * (x⁻¹ * u * x)) * x⁻¹ := by rw [h2]
      _ = x * m * x⁻¹ * u := by group
  have hle : barImg W (barLift A ⊓ centralizer (U : Set G)) ≤ A :=
    (barImg_mono inf_le_left).trans hX.le
  have hnorm : A ≤ normalizer (barImg W (barLift A ⊓ centralizer (U : Set G)) : Set (seitzBar W)) :=
    hX.symm.le.trans (barImg_le_normalizer hXM)
  rcases hsimp _ hle hnorm with h | h
  · exact Or.inr (le_of_barImg_eq_bot hMN h)
  · left
    have h1 : barLift A ≤ (barLift A ⊓ centralizer (U : Set G)) ⊔ W :=
      le_sup_of_barImg_le hXN (by rw [h, hX])
    refine h1.trans (sup_le inf_le_right fun w hw => mem_centralizer_iff.2 fun u hu => ?_)
    exact hW u (hUW hu) w hw

end BarLift

end CFSG.SeitzReduction.LinearPilot
