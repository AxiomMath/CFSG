module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryDihedral

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryModel

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (f : ℕ) (hf : 2 ≤ f)
  (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)

include hcard hfixed in
theorem card_unitaryRootCenter : Nat.card (unitaryRootCenter J hJ) = 2 ^ f := by
  have : CharP K 2 := charP_two_of_card f hcard
  rw [Subgroup.card_map_of_injective (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ),
    card_ker_firstCoord J hfixed]

include hcard hfixed in
theorem card_le_of_fst_mem_fixed {R₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hR₀R : R₀ ≤ unitaryCoverRoot J hJ) {a : K} (ha : a ≠ 0)
    (h : ∀ z : hermitianUnipotentCoord J, hermitianUnipotentPSU J hJ z ∈ R₀ →
      J.conj (z.1.1 / a) = z.1.1 / a) :
    Nat.card R₀ ≤ 2 ^ f * 2 ^ f := by
  have : CharP K 2 := charP_two_of_card f hcard
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  choose zf hzf using fun x : R₀ => hR₀R x.2
  choose w hw using exists_fst_eq J (2 ^ f) hcard hfixed
  have hmem : ∀ x : R₀, hermitianUnipotentPSU J hJ (zf x) ∈ R₀ := fun x => (hzf x).symm ▸ x.2
  let F : R₀ → {x : K // J.conj x = x} × unitaryRootCenter J hJ := fun x =>
    (⟨(zf x).1.1 / a, h _ (hmem x)⟩,
      ⟨hermitianUnipotentPSU J hJ (zf x * (w (zf x).1.1)⁻¹),
        ⟨_, by
          change (zf x * (w (zf x).1.1)⁻¹).1.1 = 0
          rw [fst_mul, fst_inv, hw]
          ring, rfl⟩⟩)
  have hF : Function.Injective F := by
    intro x y hxy
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have h1' : (zf x).1.1 = (zf y).1.1 := by
      rw [div_left_inj' ha] at h1
      exact h1
    have h2' : hermitianUnipotentPSU J hJ (zf x * (w (zf x).1.1)⁻¹) =
        hermitianUnipotentPSU J hJ (zf y * (w (zf y).1.1)⁻¹) := congrArg Subtype.val h2
    rw [h1'] at h2'
    have h3 := mul_right_cancel (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ h2')
    exact Subtype.ext (by rw [← hzf x, ← hzf y, h3])
  calc Nat.card R₀ ≤ Nat.card ({x : K // J.conj x = x} × unitaryRootCenter J hJ) :=
        Nat.card_le_card_of_injective F hF
    _ = 2 ^ f * 2 ^ f := by rw [Nat.card_prod, hfixed, card_unitaryRootCenter J hJ f hcard hfixed]

include hf hcard hfixed in
theorem not_forall_fst_mem_fixed {R₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hR₀R : R₀ ≤ unitaryCoverRoot J hJ) (hidx : R₀.relIndex (unitaryCoverRoot J hJ) ≤ 2)
    {a : K} (ha : a ≠ 0)
    (h : ∀ z : hermitianUnipotentCoord J, hermitianUnipotentPSU J hJ z ∈ R₀ →
      J.conj (z.1.1 / a) = z.1.1 / a) : False := by
  have h1 := card_le_of_fst_mem_fixed J hJ f hcard hfixed hR₀R ha h
  have h2 : (2 ^ f) ^ 3 ≤ 2 * Nat.card R₀ := by
    have h' := Subgroup.relIndex_mul_card (H := R₀) (K := unitaryCoverRoot J hJ)
    rw [inf_of_le_left hR₀R, (unitaryCoverRoot_nativeStructure J (2 ^ f) hcard hfixed hJ).1] at h'
    rw [← h']
    exact Nat.mul_le_mul_right _ hidx
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  nlinarith

include hf hcard hfixed in
theorem sq_mem_conj_center {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hγ : γ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ))
    (hsq : γ ^ 2 ∈ (unitaryRootCenter J hJ).map MulAut.conj) :
    γ ∈ (unitaryCoverRoot J hJ).map MulAut.conj ∨ γ ^ 2 = 1 := by
  have : CharP K 2 := charP_two_of_card f hcard
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨u, hu, hu'⟩ := hsq
  have huR : u ∈ unitaryCoverRoot J hJ := Subgroup.map_le_range _ _ hu
  obtain ⟨r, hr, c, ε, rfl⟩ := exists_eq_conj_diag_bar J hJ f hf hcard hfixed hγ
  fin_cases ε
  · left
    simp only [pow_zero, mul_one] at hu' ⊢
    have hδr : diagAut J hJ c r ∈ unitaryCoverRoot J hJ := by
      rw [← (diagAut_mem_rootCenterAut J hJ c).1]
      exact Subgroup.mem_map_of_mem _ hr
    have hsq' : (MulAut.conj r * diagAut J hJ c) ^ 2 =
        MulAut.conj (r * diagAut J hJ c r) * diagAut J hJ (c * c) *
          barAut J hJ ^ ((0 : Fin 2) : ℕ) := by
      rw [Fin.val_zero, pow_zero, mul_one, map_mul, ← mul_conj_mul_inv, diagAut_mul, pow_two]
      group
    have e : MulAut.conj u * diagAut J hJ 1 * barAut J hJ ^ ((0 : Fin 2) : ℕ) =
        MulAut.conj (r * diagAut J hJ c r) * diagAut J hJ (c * c) *
          barAut J hJ ^ ((0 : Fin 2) : ℕ) := by
      rw [← hsq', diagAut_one, Fin.val_zero, pow_zero, mul_one, mul_one, hu']
    obtain ⟨-, hcc, -⟩ := eq_of_conj_diag_bar_eq J hJ f hf hcard hfixed huR
      (Subgroup.mul_mem _ hr hδr) e
    have hc1 : c = 1 := by
      have hk : ((c : Kˣ) : K) * ((c : Kˣ) : K) = 1 := by
        have := congrArg (fun d : normOne J => ((d : Kˣ) : K)) hcc
        simpa using this.symm
      have hsq0 : (((c : Kˣ) : K) - 1) ^ 2 = 0 := by
        linear_combination hk + (1 - ((c : Kˣ) : K)) * h2
      exact Subtype.ext (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq0)))
    rw [hc1, diagAut_one, mul_one]
    exact ⟨r, hr, rfl⟩
  · right
    simp only [pow_one] at hu' ⊢
    have hsqinj : Function.Injective fun d : normOne J => d * d := by
      intro d e hde
      simp only at hde
      have hk := congrArg (fun x : normOne J => ((x : Kˣ) : K)) hde
      simp only [Subgroup.coe_mul, Units.val_mul] at hk
      have hsq0 : (((d : Kˣ) : K) - ((e : Kˣ) : K)) ^ 2 = 0 := by
        linear_combination hk + (((e : Kˣ) : K) - ((d : Kˣ) : K)) * ((e : Kˣ) : K) * h2
      exact Subtype.ext (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq0)))
    have : Finite (normOne J) := Subtype.finite
    obtain ⟨d, hd⟩ := (Finite.injective_iff_surjective.1 hsqinj) c
    simp only at hd
    set δd := diagAut J hJ d
    set τ := barAut J hJ
    have hτ2 : τ * τ = 1 := barAut_mul_self J hJ
    have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
    set r' := δd⁻¹ r with hr'
    have hr'R : r' ∈ unitaryCoverRoot J hJ := by
      rw [← (Subgroup.inv_mem _ (diagAut_mem_rootCenterAut J hJ d)).1]
      exact Subgroup.mem_map_of_mem _ hr
    have hγ' : δd⁻¹ * (MulAut.conj r * diagAut J hJ c * τ) * δd = MulAut.conj r' * τ := by
      have e1 : δd⁻¹ * MulAut.conj r * δd = MulAut.conj r' := by
        rw [← mul_conj_mul_inv δd⁻¹ r, inv_inv]
      have e2 : δd⁻¹ * diagAut J hJ c * (τ * δd) = τ := by
        rw [barAut_mul_diagAut, ← diagAut_inv, ← diagAut_mul, ← mul_assoc, ← diagAut_mul, ← hd]
        rw [show d⁻¹ * (d * d) * d⁻¹ = 1 by group, diagAut_one, one_mul]
      calc δd⁻¹ * (MulAut.conj r * diagAut J hJ c * τ) * δd
          = (δd⁻¹ * MulAut.conj r * δd) * (δd⁻¹ * diagAut J hJ c * (τ * δd)) := by group
        _ = MulAut.conj r' * τ := by rw [e1, e2]
    have hτr' : τ r' ∈ unitaryCoverRoot J hJ := by
      rw [← (barAut_mem_rootCenterAut J hJ).1]
      exact Subgroup.mem_map_of_mem _ hr'R
    have hsq2 : (MulAut.conj r' * τ) ^ 2 = MulAut.conj (r' * τ r') := by
      rw [map_mul, ← mul_conj_mul_inv τ r', pow_two, hτinv]
      calc MulAut.conj r' * τ * (MulAut.conj r' * τ)
          = MulAut.conj r' * (τ * MulAut.conj r' * τ) * 1 := by group
        _ = MulAut.conj r' * (τ * MulAut.conj r' * τ) * (τ * τ) := by rw [hτ2]
        _ = MulAut.conj r' * (τ * MulAut.conj r' * τ) := by rw [hτ2, mul_one]
    have hδu : δd⁻¹ u = u := (Subgroup.inv_mem _ (diagAut_mem_rootCenterAut J hJ d)).2 u hu
    have e1 := mul_conj_mul_inv δd⁻¹ u
    rw [inv_inv, hδu] at e1
    have hconjsq : (MulAut.conj r' * τ) ^ 2 = MulAut.conj u := by
      rw [← hγ', show (δd⁻¹ * (MulAut.conj r * diagAut J hJ c * τ) * δd) ^ 2 =
        δd⁻¹ * (MulAut.conj r * diagAut J hJ c * τ) ^ 2 * δd by simp only [pow_two]; group,
        ← hu', e1]
    rw [hsq2] at hconjsq
    have hru : r' * τ r' = u := unitaryRoot_injOn_conj J hJ f hf hcard hfixed
      (Subgroup.mul_mem _ hr'R hτr') huR hconjsq
    obtain ⟨z, hz⟩ := hr'R
    have hτz : τ r' = hermitianUnipotentPSU J hJ (rootTau J z) := by
      rw [← hz]
      exact barAut_hermitianUnipotentPSU J hJ z
    have hmem : hermitianUnipotentPSU J hJ (z * rootTau J z) ∈ unitaryRootCenter J hJ := by
      rw [map_mul, hz, ← hτz, hru]
      exact hu
    rw [hermitianUnipotentPSU_mem_center_iff, fst_mul, fst_rootTau] at hmem
    have hz1 : J.conj z.1.1 = z.1.1 := by linear_combination hmem - z.1.1 * h2
    have hone : z * rootTau J z = 1 := by
      refine coord_ext ?_ ?_
      · rw [fst_mul, fst_rootTau, fst_one]
        exact hmem
      · rw [snd_mul, snd_rootTau, fst_rootTau, snd_one, J.conj_involutive]
        have hz2 := z.2
        rw [hz1] at hz2
        linear_combination hz2 - z.1.1 * z.1.1 * h2
    have hr'1 : r' * τ r' = 1 := by
      rw [hτz, ← hz, ← map_mul, hone, map_one]
    have hsq1 : (MulAut.conj r' * τ) ^ 2 = 1 := by rw [hsq2, hr'1, map_one]
    rw [← hγ'] at hsq1
    calc (MulAut.conj r * diagAut J hJ c * τ) ^ 2
        = δd * (δd⁻¹ * (MulAut.conj r * diagAut J hJ c * τ) * δd) ^ 2 * δd⁻¹ := by
          simp only [pow_two]
          group
      _ = 1 := by rw [hsq1, mul_one, mul_inv_cancel]

include hf hcard hfixed in
theorem fix_eq_conj_center {R₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hR₀R : R₀ ≤ unitaryCoverRoot J hJ)
    (hidx : R₀.relIndex (unitaryCoverRoot J hJ) ≤ 2) :
    {γ | γ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) ∧
      ∀ x ∈ R₀, γ x = x} = ((unitaryRootCenter J hJ).map MulAut.conj : Set (MulAut _)) := by
  have : CharP K 2 := charP_two_of_card f hcard
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hnot : ∀ {a : K}, a ≠ 0 → (∀ z : hermitianUnipotentCoord J,
      hermitianUnipotentPSU J hJ z ∈ R₀ → J.conj (z.1.1 / a) = z.1.1 / a) → False :=
    fun ha h => not_forall_fst_mem_fixed J hJ f hf hcard hfixed hR₀R hidx ha h
  ext γ
  refine ⟨fun ⟨hγ, hfix⟩ => ?_, ?_⟩
  · obtain ⟨_, ⟨y, rfl⟩, c, ε, rfl⟩ := exists_eq_conj_diag_bar J hJ f hf hcard hfixed hγ
    have hfst : ∀ z : hermitianUnipotentCoord J, hermitianUnipotentPSU J hJ z ∈ R₀ →
        (J.conj ^ (ε : ℕ)) z.1.1 * J.conj ((c : Kˣ) : K) = z.1.1 := by
      intro z hz
      obtain ⟨w, hw, hw1⟩ := exists_conj_diag_bar_apply J hJ y c ε z
      rw [hfix _ hz] at hw
      rw [← hw1, CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hw]
    have hc0 : J.conj ((c : Kˣ) : K) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
    have hεc : ε = 0 ∧ c = 1 := by
      fin_cases ε
      · refine ⟨rfl, ?_⟩
        by_contra hc1
        have hc' : J.conj ((c : Kˣ) : K) ≠ 1 := by
          intro h1
          apply hc1
          apply Subtype.ext
          apply Units.ext
          rw [← J.conj_involutive ((c : Kˣ) : K), h1, map_one]
          rfl
        refine hnot one_ne_zero fun z hz => ?_
        have e : z.1.1 * J.conj ((c : Kˣ) : K) = z.1.1 := hfst z hz
        have hz1 : z.1.1 = 0 := by
          have e' : z.1.1 * (J.conj ((c : Kˣ) : K) - 1) = 0 := by linear_combination e
          exact (mul_eq_zero.1 e').resolve_right (sub_ne_zero.2 hc')
        rw [hz1, zero_div, map_zero]
      · exfalso
        simp only [pow_one] at hfst
        by_cases hall : ∀ z : hermitianUnipotentCoord J, hermitianUnipotentPSU J hJ z ∈ R₀ →
            z.1.1 = 0
        · exact hnot one_ne_zero fun z hz => by rw [hall z hz, zero_div, map_zero]
        · rw [not_forall] at hall
          obtain ⟨z₀, hall⟩ := hall
          rw [Classical.not_imp] at hall
          obtain ⟨hz₀, ha₀⟩ := hall
          refine hnot ha₀ fun z hz => ?_
          have e := hfst z hz
          have e₀ := hfst z₀ hz₀
          have hb : J.conj z₀.1.1 ≠ 0 := (map_ne_zero _).2 ha₀
          rw [map_div₀, div_eq_div_iff hb ha₀]
          linear_combination (J.conj z₀.1.1) * e - (J.conj z.1.1) * e₀
    obtain ⟨rfl, rfl⟩ := hεc
    simp only [Fin.val_zero, pow_zero, mul_one, diagAut_one] at hfix ⊢
    refine ⟨hermitianUnipotentPSU J hJ y, ⟨y, ?_, rfl⟩, rfl⟩
    by_contra hy
    change y.1.1 ≠ 0 at hy
    refine hnot hy fun z hz => ?_
    have hcomm := hfix _ hz
    rw [conj_hermitianUnipotentPSU] at hcomm
    have hyz : y * z = z * y := by
      have := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hcomm
      calc y * z = y * z * y⁻¹ * y := by group
        _ = z * y := by rw [this]
    have hc := congrArg (fun x : hermitianUnipotentCoord J => x.1.2)
      (commutatorElement_eq_one_iff_mul_comm.2 hyz)
    simp only [snd_commutator, snd_one] at hc
    have hb : J.conj y.1.1 ≠ 0 := (map_ne_zero _).2 hy
    rw [map_div₀, div_eq_div_iff hb hy]
    linear_combination hc - (z.1.1 * J.conj y.1.1) * h2
  · rintro ⟨u, hu, rfl⟩
    have huR : u ∈ unitaryCoverRoot J hJ := Subgroup.map_le_range _ _ hu
    refine ⟨conj_mem_rootCenterAut J hJ huR, fun x hx => ?_⟩
    rw [MulAut.conj_apply,
      ((mem_unitaryRootCenter_iff J hJ f hcard hfixed).1 hu).2 x (hR₀R hx), mul_inv_cancel_right]

include hcard in
theorem unitaryRootCenter_isElementaryAbelian :
    IsElementaryAbelian 2 (unitaryRootCenter J hJ) := by
  have : CharP K 2 := charP_two_of_card f hcard
  refine isElementaryAbelian_of_isElemAbelian ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨z, hz, rfl⟩⟩ := x
    obtain ⟨_, ⟨w, -, rfl⟩⟩ := y
    change hermitianUnipotentPSU J hJ z * hermitianUnipotentPSU J hJ w =
      hermitianUnipotentPSU J hJ w * hermitianUnipotentPSU J hJ z
    rw [← map_mul, ← map_mul, mul_comm_of_fst_eq_zero J hz w]
  · rintro _ ⟨z, hz, rfl⟩
    rw [← map_pow, pow_two_eq_one_of_fst_eq_zero J hz, map_one]

include hf hcard hfixed in
theorem conj_unitaryRootCenter :
    IsElementaryAbelian 2 ((unitaryRootCenter J hJ).map MulAut.conj) ∧
      Nat.card ((unitaryRootCenter J hJ).map MulAut.conj) = 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := unitaryRootCenter_isElementaryAbelian J hJ f hcard
  refine ⟨IsElementaryAbelian.map _, ?_⟩
  rw [← card_unitaryRootCenter J hJ f hcard hfixed]
  refine (Nat.card_image_of_injOn ((unitaryRoot_injOn_conj J hJ f hf hcard hfixed).mono
    (Subgroup.map_le_range _ _))).trans ?_
  rfl

end CFSG.ProperTwoGeneratedCore.RootCenter
