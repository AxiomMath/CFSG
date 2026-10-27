module

public import CFSG.ClassicalInvolution.SmallOrth.Layer
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.ClassicalGroups.Orthogonal.Perfect

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open scoped commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_zero_or_eq_one_or_eq_neg_one_of_card_eq_three [Finite K] (hK : Nat.card K = 3)
    (x : K) : x = 0 ∨ x = 1 ∨ x = -1 := by
  have : Fintype K := Fintype.ofFinite K
  have h3 : x ^ 3 = x := by
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have h0 : x * ((x - 1) * (x + 1)) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl h
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

theorem eq_or_eq_neg_of_card_eq_three [Finite K] (hK : Nat.card K = 3) {x y : K} (hx : x ≠ 0)
    (hy : y ≠ 0) : x = y ∨ x = -y := by
  rcases eq_zero_or_eq_one_or_eq_neg_one_of_card_eq_three hK x with h | h | h <;>
  rcases eq_zero_or_eq_one_or_eq_neg_one_of_card_eq_three hK y with h' | h' | h' <;>
  simp_all

theorem exists_mem_elementaryGroup_fix_e_neg (P : HypPair Q) {v w : V} (hv : v ∈ P.perp)
    (hw : w ∈ P.perp) (hvw : polar Q v w = 0) (hQw : Q w = Q v) (ha : Q v ≠ 0) :
    ∃ g ∈ elementaryGroup Q, g P.e = P.e ∧ g v = -v := by
  obtain ⟨hev, hfv⟩ := HypPair.mem_perp.mp hv
  obtain ⟨hew, hfw⟩ := HypPair.mem_perp.mp hw
  set a := Q v
  have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have h1' : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
  set h := P.e - a • P.f with hh
  have hwv : polar Q w v = 0 := by rw [polar_comm, hvw]
  have hve : polar Q v P.e = 0 := by rw [polar_comm, hev]
  have hvf : polar Q v P.f = 0 := by rw [polar_comm, hfv]
  have hwe : polar Q w P.e = 0 := by rw [polar_comm, hew]
  have hwf : polar Q w P.f = 0 := by rw [polar_comm, hfw]
  have hvv : polar Q v v = 2 * a := polar_self_eq_two_mul Q v
  have hww : polar Q w w = 2 * a := by rw [polar_self_eq_two_mul, hQw]
  have hvh : polar Q v h = 0 := by
    rw [hh, polar_sub_right, polar_smul_right_eq, hve, hvf]; ring
  have hwh : polar Q w h = 0 := by
    rw [hh, polar_sub_right, polar_smul_right_eq, hwe, hwf]; ring
  have hhv : polar Q h v = 0 := by rw [polar_comm, hvh]
  have hhw : polar Q h w = 0 := by rw [polar_comm, hwh]
  have heh : polar Q P.e h = -a := by
    rw [hh, polar_sub_right, polar_smul_right_eq, P.polar_ee, P.polar_ef]; ring
  have hQh : Q h = -a := by
    rw [hh, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq, P.Q_e,
      P.Q_f, polar_neg_right, polar_smul_right_eq, P.polar_ef]; ring
  have hhh : polar Q h h = -(2 * a) := by rw [polar_self_eq_two_mul, hQh]; ring
  have hu₁ : Q (v + h) = 0 := by rw [QuadraticMap.map_add Q, hQh, hvh]; ring
  have hu₂ : Q (w + h) = 0 := by rw [QuadraticMap.map_add Q, hQh, hwh, hQw]; ring
  have hx₁ : polar Q (v + h) (-a⁻¹ • w) = 0 := by
    rw [polar_smul_right_eq, polar_add_left, hvw, hhw]; ring
  have hx₂ : polar Q (w + h) (a⁻¹ • v) = 0 := by
    rw [polar_smul_right_eq, polar_add_left, hwv, hhv]; ring
  have hQx₁ : Q (-a⁻¹ • w) = a⁻¹ := by
    rw [map_smul_eq_sq, hQw]; linear_combination a⁻¹ * h1'
  have hQx₂ : Q (a⁻¹ • v) = a⁻¹ := by
    rw [map_smul_eq_sq]; linear_combination a⁻¹ * h1'
  refine ⟨eichler Q (w + h) (a⁻¹ • v) * eichler Q (v + h) (-a⁻¹ • w),
    mul_mem (eichler_mem_elementaryGroup Q _ _) (eichler_mem_elementaryGroup Q _ _), ?_, ?_⟩
  · have hA : eichler Q (v + h) (-a⁻¹ • w) P.e = P.e + w + (v + h) := by
      rw [eichler_apply hu₁ hx₁, hQx₁, polar_add_right, heh, hev, polar_smul_right_eq, hew]
      linear_combination (norm := module) h1 • w + h1' • (v + h)
    have hp1 : polar Q (P.e + w + (v + h)) (w + h) = -a := by
      simp only [polar_add_left, polar_add_right]
      rw [hew, heh, hww, hwh, hvw, hvh, hhw, hhh]; ring
    have hp2 : polar Q (P.e + w + (v + h)) (a⁻¹ • v) = 2 := by
      rw [polar_smul_right_eq]
      simp only [polar_add_left]
      rw [hev, hwv, hvv, hhv]; linear_combination 2 * h1'
    have hB : eichler Q (w + h) (a⁻¹ • v) (P.e + w + (v + h)) = P.e := by
      rw [eichler_apply hu₂ hx₂, hQx₂, hp1, hp2]
      linear_combination (norm := module) h1' • (w + h) - h1 • v
    rw [LinearEquiv.mul_apply, hA, hB]
  · have hC : eichler Q (v + h) (-a⁻¹ • w) v = -v - (2 : K) • w - (2 : K) • h := by
      rw [eichler_apply hu₁ hx₁, hQx₁, polar_add_right, hvv, hvh, polar_smul_right_eq, hvw]
      linear_combination (norm := module) (-2 : K) • (h1 • w) + (-2 : K) • (h1' • (v + h))
    have hp3 : polar Q (-v - (2 : K) • w - (2 : K) • h) (w + h) = 0 := by
      simp only [polar_sub_left, polar_neg_left, polar_smul_left_eq, polar_add_right]
      rw [hvw, hvh, hww, hwh, hhw, hhh]; ring
    have hp4 : polar Q (-v - (2 : K) • w - (2 : K) • h) (a⁻¹ • v) = -2 := by
      rw [polar_smul_right_eq]
      simp only [polar_sub_left, polar_neg_left, polar_smul_left_eq]
      rw [hvv, hwv, hhv]; linear_combination -2 * h1'
    have hD : eichler Q (w + h) (a⁻¹ • v) (-v - (2 : K) • w - (2 : K) • h) = -v := by
      rw [eichler_apply hu₂ hx₂, hQx₂, hp3, hp4]
      module
    rw [LinearEquiv.mul_apply, hC, hD]

theorem eichler_mem_commutator_of_partner (h2 : (2 : K) ≠ 0) (P : HypPair Q) {v w : V}
    (hv : v ∈ P.perp) (hw : w ∈ P.perp) (hvw : polar Q v w = 0) (hQw : Q w = Q v)
    (ha : Q v ≠ 0) :
    (⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈
      commutator (elementaryGroup Q) := by
  obtain ⟨g, hg, hge, hgv⟩ := exists_mem_elementaryGroup_fix_e_neg P hv hw hvw hQw ha
  have hev : polar Q P.e ((-2⁻¹ : K) • v) = 0 := by
    rw [polar_smul_right_eq, (HypPair.mem_perp.mp hv).1, mul_zero]
  have key := commutatorElement_eichler (elementaryGroup_le_orthogonalGroup Q hg) hge hev
  have hval : g ((-2⁻¹ : K) • v) - (-2⁻¹ : K) • v = v := by
    have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
    rw [map_smul, hgv]
    linear_combination (norm := module) h22 • v
  rw [hval] at key
  have hmem := Subgroup.commutator_mem_commutator
    (Subgroup.mem_top (⟨g, hg⟩ : elementaryGroup Q))
    (Subgroup.mem_top (⟨eichler Q P.e ((-2⁻¹ : K) • v), eichler_mem_elementaryGroup Q _ _⟩ :
      elementaryGroup Q))
  have heq : (⁅(⟨g, hg⟩ : elementaryGroup Q),
      ⟨eichler Q P.e ((-2⁻¹ : K) • v), eichler_mem_elementaryGroup Q _ _⟩⁆ :
        elementaryGroup Q) = ⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ :=
    Subtype.ext key
  rw [heq] at hmem
  exact hmem

theorem finrank_le_one_add_finrank_inf_ker [FiniteDimensional K V] (W : Submodule K V)
    (φ : V →ₗ[K] K) : Module.finrank K W ≤ 1 + Module.finrank K ↥(W ⊓ LinearMap.ker φ) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker φ)
  have h2 := Submodule.finrank_le (W ⊔ LinearMap.ker φ)
  have h3 := LinearMap.finrank_range_add_finrank_ker φ
  have h4 : Module.finrank K (LinearMap.range φ) ≤ 1 :=
    (Submodule.finrank_le _).trans (Module.finrank_self K).le
  omega

theorem exists_partner_of_three_le_finrank_perp [Finite K] [FiniteDimensional K V]
    (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (h3 : 3 ≤ Module.finrank K P.perp) {v : V} (hv : v ∈ P.perp) (ha : Q v ≠ 0) :
    ∃ w ∈ P.perp, polar Q v w = 0 ∧ Q w = Q v := by
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set W := P.perp ⊓ LinearMap.ker (polarBilin Q v) with hW
  have hmem : ∀ x, x ∈ W ↔ x ∈ P.perp ∧ polar Q v x = 0 := fun x => by
    rw [hW, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
  have hdim : Module.finrank K P.perp ≤ 1 + Module.finrank K W :=
    finrank_le_one_add_finrank_inf_ker P.perp (polarBilin Q v)
  have hvv : polar Q v v ≠ 0 := by
    rw [polar_self_eq_two_mul]
    exact mul_ne_zero h2 ha
  have hnd : PolarNondegOn Q W := by
    intro x hx hxW
    obtain ⟨hxP, hvx⟩ := (hmem x).mp hx
    refine P.polarNondegOn_perp hQ x hxP fun z hz => ?_
    have hzc : z - (polar Q v z / polar Q v v) • v ∈ W :=
      (hmem _).mpr ⟨P.perp.sub_mem hz (P.perp.smul_mem _ hv), by
        rw [polar_sub_right, polar_smul_right_eq, div_mul_cancel₀ _ hvv, sub_self]⟩
    have := hxW _ hzc
    rwa [polar_sub_right, polar_smul_right_eq, polar_comm Q x v, hvx, mul_zero, sub_zero] at this
  obtain ⟨w, hwW, hw⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_mem_eq_unit hodd
    (nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hnd)) (by omega)
    (Units.mk0 (Q v) ha)
  obtain ⟨hwP, hvw⟩ := (hmem w).mp hwW
  exact ⟨w, hwP, hvw, by rw [hw, Units.val_mk0]⟩

theorem exists_partner_of_card_eq_three [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (P : HypPair Q) (h2 : 2 ≤ Module.finrank K P.perp)
    (haniso : ∀ x ∈ P.perp, Q x = 0 → x = 0) {v : V} (hv : v ∈ P.perp) (ha : Q v ≠ 0) :
    ∃ w ∈ P.perp, polar Q v w = 0 ∧ Q w = Q v := by
  have hdim := finrank_le_one_add_finrank_inf_ker P.perp (polarBilin Q v)
  have hne : P.perp ⊓ LinearMap.ker (polarBilin Q v) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply] at hwW
  obtain ⟨hwP, hvw⟩ := hwW
  have hQw : Q w ≠ 0 := fun h => hw0 (haniso w hwP h)
  refine ⟨w, hwP, hvw, ?_⟩
  rcases eq_or_eq_neg_of_card_eq_three hK hQw ha with h | h
  · exact h
  · exfalso
    have h2' : (2 : K) ≠ 0 :=
      CatalogueBOddQuadratic.two_ne_zero_of_odd_card (by rw [hK]; decide)
    have hvw0 : v + w = 0 := haniso _ (P.perp.add_mem hv hwP) (by
      rw [QuadraticMap.map_add Q, h, hvw]; ring)
    rw [eq_neg_of_add_eq_zero_right hvw0, polar_neg_right, polar_self_eq_two_mul,
      neg_eq_zero] at hvw
    exact mul_ne_zero h2' ha hvw

theorem exists_anisotropic_split (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (P : HypPair Q) {v : V} (hv : v ∈ P.perp) (hv0 : v ≠ 0) (hQv : Q v = 0) :
    ∃ y ∈ P.perp, Q y ≠ 0 ∧ Q (v + y) ≠ 0 := by
  obtain ⟨z, hzP, hz⟩ := (P.polarNondegOn_perp hQ).exists_polar_ne_zero hv hv0
  obtain ⟨y₀, hy₀P, hvy₀⟩ : ∃ y₀ ∈ P.perp, polar Q v y₀ = 1 :=
    ⟨(polar Q v z)⁻¹ • z, P.perp.smul_mem _ hzP, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hz]⟩
  have hy₀v : polar Q y₀ v = 1 := by rw [polar_comm, hvy₀]
  obtain ⟨t, ht⟩ : ∃ t : K, t = 1 - Q y₀ := ⟨_, rfl⟩
  have hQy : Q (y₀ + t • v) = 1 := by
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, hQv, polar_smul_right_eq, hy₀v, ht]
    ring
  refine ⟨y₀ + t • v, P.perp.add_mem hy₀P (P.perp.smul_mem _ hv), ?_, ?_⟩
  · rw [hQy]
    exact one_ne_zero
  · rw [QuadraticMap.map_add Q, hQy, hQv, polar_add_right, polar_smul_right_eq, hvy₀,
      polar_self_eq_zero hQv]
    convert h2 using 1
    ring

section Finite

variable [Finite K] [FiniteDimensional K V]

theorem commutator_elementaryGroup_eq_top_three (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (hne : Module.finrank K V ≠ 4 ∨ ∀ P P' : HypPair Q, ¬ P.Orth P') :
    commutator (elementaryGroup Q) = ⊤ := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨x₀, hx₀0, hx₀⟩ :=
    CatalogueBOddQuadratic.exists_isotropic_of_three_le hodd Q hQ (by omega)
  obtain ⟨P, rfl⟩ := exists_hypPair hQ hx₀ hx₀0
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ (by omega)
  have hP := finrank_le_two_add_finrank_perp P
  have hpart : ∀ v ∈ P.perp, Q v ≠ 0 → ∃ w ∈ P.perp, polar Q v w = 0 ∧ Q w = Q v := by
    by_cases hW1 : ∀ P₁ P₂ : HypPair Q, ¬ P₁.Orth P₂
    · have haniso : ∀ x ∈ P.perp, Q x = 0 → x = 0 := fun x hx hQx => by
        by_contra hx0
        obtain ⟨P', hP', -⟩ := exists_orth_hypPair_of_mem_perp hQ P hx hx0 hQx
        exact hW1 P P' hP'
      exact fun v hv ha => exists_partner_of_card_eq_three hK P (by omega) haniso hv ha
    · push Not at hW1
      obtain ⟨P₁, P₂, h₁₂⟩ := hW1
      have h4 := four_le_finrank_of_orth h₁₂
      have h5 : Module.finrank K V ≠ 4 := by
        rcases hne with h | h
        · exact h
        · exact absurd h₁₂ (h P₁ P₂)
      exact fun v hv ha => exists_partner_of_three_le_finrank_perp hodd hQ P (by omega) hv ha
  set N := commutator (elementaryGroup Q)
  have haniso_mem : ∀ v ∈ P.perp, Q v ≠ 0 →
      (⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈ N := by
    intro v hv ha
    obtain ⟨w, hw, hvw, hQw⟩ := hpart v hv ha
    exact eichler_mem_commutator_of_partner h2 P hv hw hvw hQw ha
  have hroot : ∀ v ∈ P.perp,
      (⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈ N := by
    intro v hv
    by_cases hQv : Q v = 0
    · by_cases hv0 : v = 0
      · subst hv0
        have : (⟨eichler Q P.e 0, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) = 1 :=
          Subtype.ext (eichler_zero_right Q P.e)
        rw [this]
        exact N.one_mem
      obtain ⟨y, hy, hQy, hQvy⟩ := exists_anisotropic_split h2 hQ P hv hv0 hQv
      have hmem := N.mul_mem (haniso_mem (v + y) (P.perp.add_mem hv hy) hQvy)
        (haniso_mem (-y) (P.perp.neg_mem hy) (by rwa [QuadraticMap.map_neg]))
      have hvy : polar Q P.e (v + y) = 0 := (HypPair.mem_perp.mp (P.perp.add_mem hv hy)).1
      have hny : polar Q P.e (-y) = 0 := (HypPair.mem_perp.mp (P.perp.neg_mem hy)).1
      convert hmem using 1
      exact Subtype.ext (by
        change eichler Q P.e v = eichler Q P.e (v + y) * eichler Q P.e (-y)
        rw [eichler_mul hvy hny, add_neg_cancel_right])
    · exact haniso_mem v hv hQv
  have hcenter : ∀ v, polar Q P.e v = 0 →
      (⟨eichler Q P.e v, eichler_mem_elementaryGroup Q _ _⟩ : elementaryGroup Q) ∈ N := by
    intro v hv
    have hdecomp : v = P.proj v + polar Q v P.f • P.e := by
      have := P.eq_add_proj v
      rw [polar_comm Q v P.e, hv, zero_smul, add_zero] at this
      rw [add_comm]
      exact this
    have h := eichler_add_smul_self P.Q_e (P.proj v) (polar Q v P.f)
    rw [← hdecomp] at h
    convert hroot _ (P.proj_mem_perp v) using 1
    exact Subtype.ext h
  have hN : N.Normal := inferInstance
  have hgen : ∀ u w, Q u = 0 → polar Q u w = 0 →
      (⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ : elementaryGroup Q) ∈ N := by
    intro u w hu hw
    by_cases hu0 : u = 0
    · subst hu0
      have : (⟨eichler Q 0 w, eichler_mem_elementaryGroup Q 0 w⟩ : elementaryGroup Q) = 1 :=
        Subtype.ext (eichler_zero_left Q w)
      rw [this]
      exact N.one_mem
    obtain ⟨g, hg, c, hc0, hgu⟩ := exists_mem_elementaryGroup_apply_eq_smul hQ hA P.Q_e hu
      P.e_ne_zero hu0
    have hgO := elementaryGroup_le_orthogonalGroup Q hg
    have hv : polar Q P.e (c⁻¹ • g⁻¹ w) = 0 := by
      rw [polar_smul_right_eq, ← polar_map_of_mem hgO P.e (g⁻¹ w), hgu,
        LinearEquiv.apply_inv_apply', polar_smul_left_eq, hw, mul_zero, mul_zero]
    have hmem := hN.conj_mem _ (hcenter _ hv) ⟨g, hg⟩
    convert hmem using 1
    apply Subtype.ext
    change eichler Q u w = g * eichler Q P.e (c⁻¹ • g⁻¹ w) * g⁻¹
    rw [eichler_conj hgO, hgu, map_smul, LinearEquiv.apply_inv_apply', eichler_smul_left,
      smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hx
    exact hgen u w hu hw
  | one => exact N.one_mem
  | mul x y hx hy ihx ihy => exact N.mul_mem ihx ihy
  | inv x hx ihx => exact N.inv_mem ihx

end Finite

theorem isQuasisimple_elementaryGroup_of_perfect (P : HypPair Q) (hA : HasAnisoPerp Q)
    (hperf : commutator (elementaryGroup Q) = ⊤)
    (hprim : MulAction.IsPreprimitive (elementaryGroup Q) (singularLines Q)) :
    CFSG.Open.IsQuasisimple ↥(elementaryGroup Q) := by
  obtain ⟨a, ha, hc⟩ := hA P
  refine isQuasisimple_of_iwasawa (iwasawa Q) hperf ?_ ?_
  · intro g hg
    have hscal := mem_scalars_of_forall_singular_small P ha hc
      (elementaryGroup_le_orthogonalGroup Q g.2) (fun v hv hQv => by
        have := hg (lineMk v hv hQv)
        rw [smul_lineMk, lineMk_eq_lineMk_iff] at this
        obtain ⟨c, hc⟩ := this
        exact ⟨c, hc.symm⟩)
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (commute_of_mem_scalars hscal h.1).symm
  · obtain ⟨g, hg, c, hc0, hgc⟩ := exists_mem_elementaryGroup_apply_e_eq_smul_f P ha hc
    refine ⟨⟨g, hg⟩, lineMk P.e P.e_ne_zero P.Q_e, fun h => ?_⟩
    rw [smul_lineMk, lineMk_eq_lineMk_iff] at h
    obtain ⟨b, hb⟩ := h
    have h1 : (g : V ≃ₗ[K] V) P.e = c • P.f := hgc
    have := congrArg (polar Q P.e) (hb.trans h1)
    rw [polar_smul_right_eq, polar_smul_right_eq, P.polar_ee, P.polar_ef] at this
    exact hc0 (by simpa using this.symm)

theorem isQuasisimple_elementaryGroup_three [Finite K] [FiniteDimensional K V]
    (hK : Nat.card K = 3) (hQ : (polarBilin Q).Nondegenerate) (hdim : 4 ≤ Module.finrank K V)
    (hne : Module.finrank K V ≠ 4 ∨ ∀ P P' : HypPair Q, ¬ P.Orth P') :
    CFSG.Open.IsQuasisimple ↥(elementaryGroup Q) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have hA : HasAnisoPerp Q := hasAnisoPerp_of_three_le_finrank hQ (by omega)
  obtain ⟨x₀, hx₀0, hx₀⟩ :=
    CatalogueBOddQuadratic.exists_isotropic_of_three_le hodd Q hQ (by omega)
  obtain ⟨P₁, -⟩ := exists_hypPair hQ hx₀ hx₀0
  refine isQuasisimple_elementaryGroup_of_perfect P₁ hA
    (commutator_elementaryGroup_eq_top_three hK hQ hdim hne) ?_
  by_cases hW1 : ∀ P P' : HypPair Q, ¬ P.Orth P'
  · exact isPreprimitive_singularLines_of_noOrth hQ hA hW1 P₁
  have h5 : 5 ≤ Module.finrank K V := by
    push Not at hW1
    obtain ⟨P, P', h⟩ := hW1
    have := four_le_finrank_of_orth h
    rcases hne with h' | h'
    · omega
    · exact absurd h (h' P P')
  obtain ⟨P₂, h₁₂⟩ := exists_orth_hypPair_of_five_le_finrank hodd hQ h5 P₁
  have hQ' := nondegenerate_polarBilin_restrict (P₁.polarNondegOn_perp hQ)
  have hdim' : 3 ≤ Module.finrank K P₁.perp := by
    have := finrank_le_two_add_finrank_perp P₁
    omega
  exact isPreprimitive_singularLines_of_orth h₁₂ hQ hA (hasAnisoPerp_of_three_le_finrank hQ' hdim')

end CFSG.ComponentClassification.HarrisLit.T1
