module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Closure
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndings

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)
open scoped commutatorElement

namespace GMS43

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_mul_eq {K : Subgroup G} {e p : G} (he : ∀ k ∈ K, e * k = k * e) :
    K ⊓ centralizer ({e * p} : Set G) = K ⊓ centralizer ({p} : Set G) := by
  ext k
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hk, hc⟩ => ⟨hk, ?_⟩, fun ⟨hk, hc⟩ => ⟨hk, ?_⟩⟩
  · have h1 : e * (k * p) = e * (p * k) := by
      calc e * (k * p) = (e * k) * p := by group
        _ = (k * e) * p := by rw [he k hk]
        _ = k * (e * p) := by group
        _ = e * p * k := hc
        _ = e * (p * k) := by group
    exact mul_left_cancel h1
  · calc k * (e * p) = (k * e) * p := by group
      _ = (e * k) * p := by rw [he k hk]
      _ = e * (k * p) := by group
      _ = e * (p * k) := by rw [hc]
      _ = e * p * k := by group

theorem relIndex_le_two_of_mul_mem {H Y : Subgroup G}
    (hmul : ∀ a ∈ Y, ∀ b ∈ Y, a ∉ H → b ∉ H → a * b ∈ H) : H.relIndex Y ≤ 2 := by
  have hc := GMS28.card_le_two_mul_of_mul_mem (E := Y) (H := H ⊓ Y) fun a ha b hb haH hbH =>
    mem_inf.mpr ⟨hmul a ha b hb (fun h' => haH (mem_inf.mpr ⟨h', ha⟩))
      (fun h' => hbH (mem_inf.mpr ⟨h', hb⟩)), mul_mem ha hb⟩
  have h1 := relIndex_mul_card H Y
  have hpos : 0 < Nat.card (H ⊓ Y : Subgroup G) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : 3 * Nat.card (H ⊓ Y : Subgroup G) ≤ Nat.card Y := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ hlt
  omega

theorem exists_mul_conj_eq_of_card {A : Subgroup G} (hA2 : ∀ a ∈ A, a * a = 1)
    {y : G} (hyA : ∀ a ∈ A, y⁻¹ * a * y ∈ A) (hy2 : ∀ a ∈ A, (y * y) * a = a * (y * y))
    (hcard : Nat.card (A ⊓ centralizer ({y} : Set G) : Subgroup G) ^ 2 ≤ Nat.card A) :
    ∀ c ∈ A ⊓ centralizer ({y} : Set G), ∃ a ∈ A, a * (y⁻¹ * a * y) = c := by
  classical
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hA2 a ha)
    have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hA2 b hb)
    have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hA2 _ (mul_mem ha hb))
    rw [mul_inv_rev, h1, h2] at h3
    exact h3.symm
  let ψ : A →* A :=
    { toFun := fun a => ⟨a * (y⁻¹ * a * y), mul_mem a.2 (hyA a a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (a : G) * b * (y⁻¹ * (a * b) * y) = a * (y⁻¹ * a * y) * (b * (y⁻¹ * b * y))
        have h1 : (b : G) * (y⁻¹ * a * y) = (y⁻¹ * a * y) * b := hAcomm _ b.2 _ (hyA _ a.2)
        calc (a : G) * b * (y⁻¹ * (a * b) * y) = a * (b * (y⁻¹ * a * y)) * (y⁻¹ * b * y) := by
              group
          _ = a * ((y⁻¹ * a * y) * b) * (y⁻¹ * b * y) := by rw [h1]
          _ = _ := by group) }
  have hψ : ∀ a : A, (ψ a : G) = a * (y⁻¹ * a * y) := fun _ => rfl
  set C := A ⊓ centralizer ({y} : Set G) with hC
  have hrange : ψ.range.map A.subtype ≤ C := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    refine mem_inf.mpr ⟨(ψ a).2, mem_centralizer_singleton_iff.mpr ?_⟩
    show (a : G) * (y⁻¹ * a * y) * y = y * (a * (y⁻¹ * a * y))
    have h2 : (a : G) * (y⁻¹ * a * y) = (y⁻¹ * a * y) * a := hAcomm _ a.2 _ (hyA _ a.2)
    have h3 := hy2 _ (hyA _ a.2)
    have hb : y * a * y⁻¹ = y⁻¹ * a * y := by
      calc y * a * y⁻¹ = (y * y) * (y⁻¹ * a * y) * (y * y)⁻¹ := by group
        _ = (y⁻¹ * a * y) * (y * y) * (y * y)⁻¹ := by rw [h3]
        _ = y⁻¹ * a * y := by group
    calc (a : G) * (y⁻¹ * a * y) * y = (y⁻¹ * a * y) * a * y := by rw [h2]
      _ = (y * a * y⁻¹) * a * y := by rw [hb]
      _ = y * (a * (y⁻¹ * a * y)) := by group
  have hker : Nat.card ψ.ker ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun a => ⟨a.1.1, mem_inf.mpr ⟨a.1.2, ?_⟩⟩) ?_
    · have h1 : (a.1 : G) * (y⁻¹ * a.1 * y) = 1 := by
        rw [← hψ, MonoidHom.mem_ker.mp a.2, coe_one]
      have h2 : y⁻¹ * a.1 * y = (a.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [inv_eq_of_mul_eq_one_right (hA2 _ a.1.2)] at h2
      rw [mem_centralizer_singleton_iff]
      calc (a.1 : G) * y = y * (y⁻¹ * a.1 * y) := by group
        _ = y * a.1 := by rw [h2]
    · intro a b hab
      have h' := congrArg Subtype.val hab
      simp only at h'
      exact Subtype.ext (Subtype.ext h')
  have h1 := card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv] at h1
  have hRcard : Nat.card (ψ.range.map A.subtype) = Nat.card ψ.range :=
    card_map_of_injective A.subtype_injective
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hle : Nat.card C ≤ Nat.card ψ.range := by
    have h2 : Nat.card C * Nat.card C ≤ Nat.card ψ.range * Nat.card C := by
      calc Nat.card C * Nat.card C = Nat.card C ^ 2 := (sq _).symm
        _ ≤ Nat.card A := hcard
        _ = Nat.card ψ.range * Nat.card ψ.ker := h1
        _ ≤ Nat.card ψ.range * Nat.card C := Nat.mul_le_mul_left _ hker
    exact Nat.le_of_mul_le_mul_right h2 hCpos
  have heq : ψ.range.map A.subtype = C :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hRcard]; exact hle)
  intro c hc
  rw [← heq] at hc
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hc
  exact ⟨a, a.2, rfl⟩

structure Hyp (L : Subgroup G) (f : ℕ) (t : G) (T V₁ U₁ : Subgroup G) (y d : G) : Prop where
  gold : Goldschmidt1974
  setting : Endings.Setting G L f t T
  result : GMS28.Result (zpowers t) L (T ⊓ L) T f t V₁ U₁ y d
  elem : ∀ u ∈ U₁, u * u = 1

namespace Hyp

variable {L : Subgroup G} {f : ℕ} {t : G} {T V₁ U₁ : Subgroup G} {y d : G}
  (h : Hyp L f t T V₁ U₁ y d)
include h

theorem mem_T : t ∈ T := (Endings.psl2_ending_facts h.gold h.setting).1

theorem t_mul_t : t * t = 1 := (Endings.psl2_ending_facts h.gold h.setting).2.1

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t

theorem le_centralizer : T ≤ centralizer ({t} : Set G) :=
  (Endings.psl2_ending_facts h.gold h.setting).2.2.2.1

theorem three_le : 3 ≤ f := h.setting.three_le

theorem eight_le : 8 ≤ 2 ^ f :=
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.three_le

theorem card_U₁ : Nat.card U₁ = (2 ^ f) ^ 2 := h.result.card

theorem card_U : Nat.card (T ⊓ L : Subgroup G) = 2 ^ f :=
  (Endings.psl2_ending_facts h.gold h.setting).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem inv_eq : ∀ a ∈ U₁, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (h.elem a ha)

theorem comm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := by
  intro a ha b hb
  have h3 : (a * b)⁻¹ = a * b := h.inv_eq _ (mul_mem ha hb)
  rw [mul_inv_rev, h.inv_eq a ha, h.inv_eq b hb] at h3
  exact h3.symm

theorem U_le : T ⊓ L ≤ U₁ := h.result.U_le

theorem T_le_normalizer : T ≤ normalizer (U₁ : Set G) := h.result.le_normalizer_P

theorem t_mem_normalizer : t ∈ normalizer (U₁ : Set G) := h.T_le_normalizer h.mem_T

theorem sup_le_normalizer : U₁ ⊔ T ≤ normalizer (U₁ : Set G) :=
  sup_le le_normalizer h.T_le_normalizer

theorem zpowers_le_normalizer : zpowers t ≤ normalizer (U₁ : Set G) :=
  zpowers_le.mpr h.t_mem_normalizer

theorem inf_T : U₁ ⊓ T = T ⊓ L := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.U_le inf_le_left)
  rw [← h.result.centralizer_eq]
  exact mem_inf.mpr ⟨(mem_inf.mp hx).1, h.le_centralizer (mem_inf.mp hx).2⟩

theorem isPGroup_sup : IsPGroup 2 (U₁ ⊔ T : Subgroup G) :=
  h.result.sylow_sup.isPGroup.to_le (sup_le_sup_right h.result.le_V₁ T)

theorem isPGroup_U₁ : IsPGroup 2 U₁ := h.isPGroup_sup.to_le le_sup_left

theorem ne_bot : U₁ ≠ ⊥ := by
  intro hb
  have h1 := h.card_U₁
  rw [hb, card_bot] at h1
  have := h.eight_le
  nlinarith

theorem not_conj_mem : ∀ g : G, g⁻¹ * t * g ∉ U₁ := by
  refine Endings.not_conj_mem_of_card h.gold h.setting h.isPGroup_U₁ fun w hw _ => ?_
  have heq : U₁ ⊓ centralizer ({w} : Set G) = U₁ :=
    inf_eq_left.mpr fun x hx => mem_centralizer_singleton_iff.mpr (h.comm x hx w hw)
  rw [heq, h.card_U₁]

theorem card_le_card_inf_mul {K M : Subgroup G} (hK : K ≤ U₁)
    (hM : ∀ k ∈ K, k * t * k⁻¹ * t ∈ M) :
    Nat.card K ≤ Nat.card (K ⊓ (T ⊓ L) : Subgroup G) * Nat.card M := by
  classical
  let φ : K →* M :=
    { toFun := fun k => ⟨k * t * (k : G)⁻¹ * t, hM k k.2⟩
      map_one' := Subtype.ext (by
        show (1 : G) * t * (1 : G)⁻¹ * t = 1
        rw [inv_one, one_mul, mul_one, h.t_mul_t])
      map_mul' := fun a b => Subtype.ext (h.result.comm_mul a (hK a.2) b (hK b.2)) }
  have hker : ∀ k : K, k ∈ φ.ker → (k : G) ∈ T ⊓ L := fun k hk =>
    (h.result.comm_eq_one_iff k (hK k.2)).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hk))
  have h1 := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.ker ≤ Nat.card (K ⊓ (T ⊓ L) : Subgroup G) :=
    Nat.card_le_card_of_injective (fun k => ⟨k.1.1, mem_inf.mpr ⟨k.1.2, hker k.1 k.2⟩⟩)
      (fun a b hab => by
        have h' := congrArg Subtype.val hab
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  have h3 : Nat.card φ.range ≤ Nat.card M := card_le_card_group _
  calc Nat.card K = Nat.card φ.range * Nat.card φ.ker := h1
    _ ≤ Nat.card M * Nat.card (K ⊓ (T ⊓ L) : Subgroup G) := Nat.mul_le_mul h3 h2
    _ = _ := mul_comm _ _

theorem exists_mul_eq_of_not_mem {w : G} (hw : w ∈ U₁ ⊔ T) (hwV : w ∉ U₁ ⊔ zpowers t) :
    ∃ e ∈ U₁, ∃ p ∈ T, e * p = w ∧ p ∉ T ⊓ L ⊔ zpowers t := by
  obtain ⟨e, he, p, hp, rfl⟩ := Endings.exists_mul_eq_of_mem_sup h.T_le_normalizer hw
  refine ⟨e, he, p, hp, rfl, fun hpV => hwV (mul_mem (mem_sup_left he) ?_)⟩
  exact (sup_le (h.U_le.trans le_sup_left) le_sup_right : T ⊓ L ⊔ zpowers t ≤ U₁ ⊔ zpowers t) hpV

theorem card_inf_centralizer_sq_le {w : G} (hw : w ∈ U₁ ⊔ T) (hwV : w ∉ U₁ ⊔ zpowers t) :
    Nat.card (T ⊓ L ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ f := by
  obtain ⟨-, -, -, -, -, -, -, -, hfix, -⟩ := Endings.psl2_ending_facts h.gold h.setting
  obtain ⟨e, he, p, hp, rfl, hpV⟩ := h.exists_mul_eq_of_not_mem hw hwV
  rw [inf_centralizer_mul_eq fun k hk => h.comm e he k (h.U_le hk)]
  exact hfix p hp hpV

theorem card_inf_centralizer_le_sq {p : G} (hp : p ∈ T) :
    Nat.card (U₁ ⊓ centralizer ({p} : Set G) : Subgroup G) ≤
      Nat.card (T ⊓ L ⊓ centralizer ({p} : Set G) : Subgroup G) ^ 2 := by
  have hpt : Commute t p := (mem_centralizer_singleton_iff.mp (h.le_centralizer hp)).symm
  have hM : ∀ k ∈ U₁ ⊓ centralizer ({p} : Set G),
      k * t * k⁻¹ * t ∈ T ⊓ L ⊓ centralizer ({p} : Set G) := by
    intro k hk
    have hkp : Commute k p := mem_centralizer_singleton_iff.mp (mem_inf.mp hk).2
    refine mem_inf.mpr ⟨h.result.comm_mem k (mem_inf.mp hk).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (((hkp.mul_left hpt).mul_left hkp.inv_left).mul_left hpt).eq
  have h1 := h.card_le_card_inf_mul (inf_le_left : U₁ ⊓ centralizer ({p} : Set G) ≤ U₁) hM
  have h2 : Nat.card (U₁ ⊓ centralizer ({p} : Set G) ⊓ (T ⊓ L) : Subgroup G) ≤
      Nat.card (T ⊓ L ⊓ centralizer ({p} : Set G) : Subgroup G) :=
    card_le_of_le fun x hx => mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).2⟩
  calc _ ≤ _ := h1
    _ ≤ _ := Nat.mul_le_mul_right _ h2
    _ = _ := (sq _).symm

theorem card_inf_centralizer_le {w : G} (hw : w ∈ U₁ ⊔ T) (hwE : w ∉ U₁) :
    Nat.card (U₁ ⊓ centralizer ({w} : Set G) : Subgroup G) ≤ 2 ^ f := by
  obtain ⟨-, -, -, -, -, -, -, -, hfix, -⟩ := Endings.psl2_ending_facts h.gold h.setting
  obtain ⟨e, he, p, hp, rfl⟩ := Endings.exists_mul_eq_of_mem_sup h.T_le_normalizer hw
  rw [inf_centralizer_mul_eq fun k hk => h.comm e he k hk]
  by_cases hpV : p ∈ T ⊓ L ⊔ zpowers t
  · have htU : zpowers t ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      zpowers_le.mpr ((Endings.psl2_ending_facts h.gold h.setting).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        h.mem_T)
    obtain ⟨u, hu, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers h.t_mul_t htU hpV
    · exact absurd (mul_mem he (h.U_le hu)) hwE
    · rw [inf_centralizer_mul_eq fun k hk => h.comm u (h.U_le hu) k hk, h.result.centralizer_eq,
        h.card_U]
  · exact (h.card_inf_centralizer_le_sq hp).trans (hfix p hp hpV)

theorem mul_mem_of_sq_mem {p p' : G} (hp : p ∈ T) (hp' : p' ∈ T)
    (hpV : p ∉ T ⊓ L ⊔ zpowers t) (hp'V : p' ∉ T ⊓ L ⊔ zpowers t)
    (hp2 : p * p ∈ T ⊓ L ⊔ zpowers t) (hp'2 : p' * p' ∈ T ⊓ L ⊔ zpowers t) :
    p * p' ∈ T ⊓ L ⊔ zpowers t := by
  obtain ⟨-, -, -, -, -, -, hVn, hcyc, -⟩ := Endings.psl2_ending_facts h.gold h.setting
  have hcyc' := @hcyc hVn
  set N := (T ⊓ L ⊔ zpowers t).subgroupOf T with hN
  have hsq : ∀ x : T, (x : G) * x ∈ T ⊓ L ⊔ zpowers t →
      (QuotientGroup.mk x : T ⧸ N) ^ 2 = 1 := by
    intro x hx
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, mem_subgroupOf, sq]
    exact hx
  have hne : ∀ x : T, (x : G) ∉ T ⊓ L ⊔ zpowers t → (QuotientGroup.mk x : T ⧸ N) ≠ 1 := by
    intro x hx h1
    rw [QuotientGroup.eq_one_iff, hN, mem_subgroupOf] at h1
    exact hx h1
  have heq := CFSG.RankTwoShapes.eq_of_sq_eq_one_of_isCyclic (hsq ⟨p, hp⟩ hp2)
    (hne ⟨p, hp⟩ hpV) (hsq ⟨p', hp'⟩ hp'2) (hne ⟨p', hp'⟩ hp'V)
  rw [QuotientGroup.eq, hN, mem_subgroupOf] at heq
  have e1 : p * p' = (p * p) * (p⁻¹ * p') := by group
  rw [e1]
  exact mul_mem hp2 heq

theorem mul_self_mem_of_mul_mul_eq_one {e p : G} (he : e ∈ U₁) (hp : p ∈ T)
    (h1 : e * p * (e * p) = 1) : p * p ∈ T ⊓ L := by
  have hpe : p * e * p⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (h.T_le_normalizer hp) e).mp he
  have h2 : e * (p * e * p⁻¹) * (p * p) = 1 := by rw [← h1]; group
  have h3 : p * p = (e * (p * e * p⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h.inf_T]
  exact mem_inf.mpr ⟨by rw [h3]; exact inv_mem (mul_mem he hpe), mul_mem hp hp⟩

theorem relIndex_le_four {X : Subgroup G} (hX : X ≤ U₁ ⊔ T) (hX2 : ∀ x ∈ X, x * x = 1) :
    U₁.relIndex X ≤ 4 := by
  set W := U₁ ⊔ zpowers t with hW
  have hVW : T ⊓ L ⊔ zpowers t ≤ W := sup_le (h.U_le.trans le_sup_left) le_sup_right
  have ha : U₁.relIndex (W ⊓ X) ≤ 2 := by
    refine GMS43.relIndex_le_two_of_mul_mem fun a ha b hb haE hbE => ?_
    obtain ⟨e, he, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers h.t_mul_t
      h.zpowers_le_normalizer (mem_inf.mp ha).1
    · exact absurd he haE
    obtain ⟨e', he', rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers h.t_mul_t
      h.zpowers_le_normalizer (mem_inf.mp hb).1
    · exact absurd he' hbE
    have hte : t * e' * t⁻¹ ∈ U₁ := (mem_normalizer_iff.mp h.t_mem_normalizer e').mp he'
    rw [show e * t * (e' * t) = e * (t * e' * t⁻¹) * (t * t) by group, h.t_mul_t, mul_one]
    exact mul_mem he hte
  have hb : W.relIndex X ≤ 2 := by
    refine GMS43.relIndex_le_two_of_mul_mem fun a ha b hb haW hbW => ?_
    obtain ⟨e, he, p, hp, rfl, hpV⟩ := h.exists_mul_eq_of_not_mem (hX ha) haW
    obtain ⟨e', he', p', hp', rfl, hp'V⟩ := h.exists_mul_eq_of_not_mem (hX hb) hbW
    have hpp := h.mul_mem_of_sq_mem hp hp' hpV hp'V
      (mem_sup_left (h.mul_self_mem_of_mul_mul_eq_one he hp (hX2 _ ha)))
      (mem_sup_left (h.mul_self_mem_of_mul_mul_eq_one he' hp' (hX2 _ hb)))
    have hpe' : p * e' * p⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (h.T_le_normalizer hp) e').mp he'
    rw [show e * p * (e' * p') = e * (p * e' * p⁻¹) * (p * p') by group]
    exact mul_mem (mem_sup_left (mul_mem he hpe')) (hVW hpp)
  have h3 := relIndex_inf_mul_relIndex U₁ W X
  rw [inf_eq_left.mpr (le_sup_left : U₁ ≤ W)] at h3
  rw [← h3]
  calc _ ≤ 2 * 2 := Nat.mul_le_mul ha hb
    _ = 4 := by norm_num

theorem rightConjugate_mul_self {U : Subgroup G} (hU : U ≤ U₁) (g : G) :
    ∀ x ∈ rightConjugate U g, x * x = 1 := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h1 := h.elem _ (hU hx)
  calc x * x = g⁻¹ * ((g * x * g⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = 1 := by rw [h1]; group

theorem not_conj_mem_rightConjugate {U : Subgroup G} (hU : U ≤ U₁) (g : G) :
    ∀ x ∈ rightConjugate U g, ∀ k : G, k⁻¹ * t * k ≠ x := by
  intro x hx k hk
  rw [mem_rightConjugate_iff, ← hk] at hx
  exact h.not_conj_mem (k * g⁻¹) (by
    rw [show (k * g⁻¹)⁻¹ * t * (k * g⁻¹) = g * (k⁻¹ * t * k) * g⁻¹ by group]
    exact hU hx)

theorem false_of_commutator_bound {S : Subgroup G} (hES : U₁ ≤ S)
    (hsyl : IsSylowOf 2 S (normalizer (U₁ : Set G)))
    (hX : ∀ U ≤ U₁, ∀ g : G, rightConjugate U g ≤ S → ¬ rightConjugate U g ≤ U₁ →
      ∃ w ∈ rightConjugate U g,
        U₁.relIndex (rightConjugate U g) < Nat.card (⁅U₁, zpowers w⁆ : Subgroup G)) :
    False := by
  obtain ⟨P, hPS, hcl⟩ := exists_sylow_stronglyClosed_of_commutator_bound hES h.elem hsyl hX
  refine false_of_stronglyClosed_abelian_of_goldschmidt h.gold h.setting.seitz
    (Or.inl ⟨f, h.setting.three_le, h.setting.lieModel⟩) P (hPS ▸ hES)
    ⟨⟨fun a b => Subtype.ext (h.comm _ a.2 _ b.2)⟩⟩ h.ne_bot ?_
  rw [hPS]
  exact hcl

theorem false_of_isSylowOf (hsyl : IsSylowOf 2 (U₁ ⊔ T) (normalizer (U₁ : Set G))) : False := by
  refine h.false_of_commutator_bound le_sup_left hsyl fun U hU g hUS hUE => ?_
  obtain ⟨w, hwX, hwE⟩ := IsConcreteLE.not_le_iff_exists.mp hUE
  refine ⟨w, hwX, lt_card_commutator_of_mul_lt h.comm (h.sup_le_normalizer (hUS hwX)) ?_⟩
  have h4 := h.relIndex_le_four hUS (h.rightConjugate_mul_self hU g)
  have hC := h.card_inf_centralizer_le (hUS hwX) hwE
  have h8 := h.eight_le
  rw [h.card_U₁]
  calc _ ≤ 2 ^ f * 4 := Nat.mul_le_mul hC h4
    _ < 2 ^ f * 2 ^ f := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ = (2 ^ f) ^ 2 := (sq _).symm

theorem exists_mul_self_eq_one {p : G} (hp : p ∈ T) (hpV : p ∉ T ⊓ L ⊔ zpowers t)
    (hp2 : p * p ∈ T ⊓ L) : ∃ u ∈ T ⊓ L, p * u * (p * u) = 1 := by
  obtain ⟨-, -, -, -, hU2, -, -, -, hfix, -, -, -, -, -, hTU, hUcard⟩ :=
    Endings.psl2_ending_facts h.gold h.setting
  have hUcomm : ∀ a ∈ T ⊓ L, ∀ b ∈ T ⊓ L, a * b = b * a := fun a ha b hb =>
    h.comm a (h.U_le ha) b (h.U_le hb)
  have hpU : ∀ u ∈ T ⊓ L, p⁻¹ * u * p ∈ T ⊓ L := fun u hu => by
    have h1 := (mem_normalizer_iff.mp (inv_mem (hTU hp)) u).mp hu
    rwa [inv_inv] at h1
  have hpC : p * p ∈ T ⊓ L ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨hp2, mem_centralizer_singleton_iff.mpr (by group)⟩
  obtain ⟨u, hu, hu'⟩ := exists_mul_conj_eq_of_card hU2 hpU (fun a ha => hUcomm _ hp2 _ ha)
    ((hfix p hp hpV).trans hUcard.ge) (p * p) hpC
  refine ⟨u, hu, ?_⟩
  have h2 : (p⁻¹ * u * p) * u = u * (p⁻¹ * u * p) := hUcomm _ (hpU _ hu) _ hu
  calc p * u * (p * u) = (p * p) * ((p⁻¹ * u * p) * u) := by group
    _ = (p * p) * (p * p) := by rw [h2, hu']
    _ = 1 := hU2 _ hp2

theorem exists_involution_iff :
    (∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t) ↔
      ∃ τ ∈ T, τ * τ = 1 ∧ τ ∉ T ⊓ L ⊔ zpowers t := by
  constructor
  · rintro ⟨x, hx, hxx, hxV⟩
    obtain ⟨e, he, p, hp, rfl, hpV⟩ := h.exists_mul_eq_of_not_mem hx hxV
    obtain ⟨u, hu, hpu⟩ := h.exists_mul_self_eq_one hp hpV
      (h.mul_self_mem_of_mul_mul_eq_one he hp hxx)
    refine ⟨p * u, mul_mem hp (mem_inf.mp hu).1, hpu, fun hV => hpV ?_⟩
    rw [show p = p * u * u⁻¹ by group]
    exact mul_mem hV (mem_sup_left (inv_mem hu))
  · rintro ⟨τ, hτ, hττ, hτV⟩
    refine ⟨τ, mem_sup_right hτ, hττ, fun hτW => hτV ?_⟩
    obtain ⟨e, he, rfl | rfl⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers h.t_mul_t
      h.zpowers_le_normalizer hτW
    · rw [← h.inf_T]
      exact mem_sup_left (mem_inf.mpr ⟨he, hτ⟩)
    · have heT : e ∈ T := by
        rw [show e = e * t * t⁻¹ by group]
        exact mul_mem hτ (inv_mem h.mem_T)
      have heU : e ∈ T ⊓ L := by
        rw [← h.inf_T]
        exact mem_inf.mpr ⟨he, heT⟩
      exact mul_mem (mem_sup_left heU) (mem_sup_right (mem_zpowers t))

theorem sixteen_le (hx : ∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t) : 16 ≤ 2 ^ f := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h16, -⟩ := Endings.psl2_ending_facts h.gold h.setting
  obtain ⟨τ, hτ, -, hτV⟩ := h.exists_involution_iff.mp hx
  exact h16 fun hle => hτV (hle hτ)

end Hyp

end GMS43

end CFSG.SeitzReduction.RankOne
