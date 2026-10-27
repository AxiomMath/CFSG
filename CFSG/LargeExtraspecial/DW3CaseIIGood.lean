module

public import CFSG.LargeExtraspecial.DW3CaseIIMbar
public import CFSG.LargeExtraspecial.DWCaseIIGoodTI
public import CFSG.LargeExtraspecial.TSComplExtend
public import CFSG.LargeExtraspecial.DWCaseIIBNoSp
public import CFSG.LargeExtraspecial.AS35DFourNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem conj_mem_QG_of_mem_M_of_good (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A) (hw : S.width = 3)
    (hgood : ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g)
    {g₀ : G} (hg₀A : g₀ * S.z * g₀⁻¹ ∈ A) (hg₀z : g₀ * S.z * g₀⁻¹ ≠ S.z)
    (hNS : ∀ B : Submodule (ZMod 2) S.Qt, IsMbarInvariant S B → (∀ b ∈ B, S.q b = 0) →
      ¬ IsCompl (S.clSub A) B)
    {h : G} (hyM : h * S.z * h⁻¹ ∈ S.M) : h * S.z * h⁻¹ ∈ S.QG := by
  classical
  let y : G := h * S.z * h⁻¹
  change y ∈ S.QG
  by_contra hyQ
  haveI : FiniteDimensional (ZMod 2) S.Qt := finiteDimensional_Qt (S := S)
  have hyM0 : h * S.z * h⁻¹ ∈ S.M := hyM
  have hyQ0 : h * S.z * h⁻¹ ∉ S.QG := hyQ
  have hyy : h * S.z * h⁻¹ * (h * S.z * h⁻¹) = 1 := by
    rw [show h * S.z * h⁻¹ * (h * S.z * h⁻¹) = h * (S.z * S.z) * h⁻¹ by group,
      S.z_mul_z, mul_one, mul_inv_cancel]
  have hsurj : Function.Surjective (resAt S A hM) :=
    hA.resAt_surjective_of_good hM hg₀A hg₀z (hgood g₀ hg₀A)
  have hconj : ∀ a ∈ A, a ≠ 1 → ∃ g : G, g * S.z * g⁻¹ = a :=
    fun a ha ha1 => hA.exists_conj_eq_of_surjective hM hsurj hg₀A hg₀z ha ha1
  obtain ⟨hcomm, hsq⟩ :=
    hA.commute_and_mul_self_of_mem_QG_inf_centralizer hM hII hconj hgood hyM0 hyQ0
  let e : S.M := ⟨h * S.z * h⁻¹, hyM0⟩
  let p : S.Mbar := S.ρM e
  let T : S.Qt ≃ₗ[ZMod 2] S.Qt := ((p : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  let C : Subgroup G := S.QG ⊓ centralizer ({h * S.z * h⁻¹} : Set G)
  let W : Submodule (ZMod 2) S.Qt := S.clSub C
  have he2 : (e : G) ^ 2 = 1 := by
    rw [pow_two]
    exact hyy
  have hT : T ∈ S.O := p.1.2
  have htt : T * T = 1 := S.ρ_mul_self e.2 he2
  have hpne : p ≠ 1 := by
    intro hp
    exact hyQ0 ((S.ρM_eq_one_iff (m := e)).mp (by simpa using hp))
  have hpp2 : p * p = 1 := by
    calc p * p = S.ρM (e * e) := (map_mul S.ρM e e).symm
      _ = S.ρM 1 := by rw [show e * e = 1 from Subtype.ext hyy]
      _ = 1 := map_one S.ρM
  have hTU : ∀ u ∈ S.clSub A, T u ∈ S.clSub A := by
    intro u hu
    exact MaxEA.apply_mem_clSub hM (x := (p : S.O)) p.2 hu
  have ht1U : ∃ u ∈ S.clSub A, T u ≠ u := by
    by_contra hcon
    push Not at hcon
    have hres : resAt S A hM p = 1 := by
      refine LinearEquiv.ext fun v => Subtype.ext ?_
      rw [coe_resAt_apply]
      exact hcon v v.2
    exact hpne (hA.resAt_injective hM (by rw [hres, map_one]))
  have hE6 : finrank (ZMod 2) S.Qt = 6 := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hU3 : finrank (ZMod 2) (S.clSub A) = 3 := by
    rw [hA.finrank_clSub, hw]
  have hUq : ∀ u ∈ S.clSub A, S.q u = 0 := fun u hu => q_clSub hu
  have hfix4 : finrank (ZMod 2) (fixSpace T) = 4 :=
    finrank_fixSpace_eq_four_of_stabilizes (q := S.q) (U := S.clSub A) (t := T)
      S.q_nondegenerate hE6 hU3 hUq hT htt hTU ht1U
  have hCQ : C ≤ S.QG := inf_le_left
  have hzC : S.z ∈ C :=
    mem_inf.mpr ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hyM0).symm⟩
  have hCcard : Nat.card C = 2 * Nat.card W := by
    have h := S.card_clPre W
    rw [show S.clPre W = C from S.clPre_clSub hCQ hzC] at h
    exact h
  have hPCle : Nat.card (S.clPre (fixSpace T)) ≤ 2 * Nat.card C :=
    S.card_clPre_fixSpace_le hyM0
  have hle16 : 16 ≤ Nat.card C := by
    have hPcard : Nat.card (S.clPre (fixSpace T)) = 32 := by
      rw [S.card_clPre, S.card_submodule, hfix4]
      norm_num
    omega
  have hWfr : 3 ≤ finrank (ZMod 2) W := by
    rw [hCcard, S.card_submodule] at hle16
    have h8 : 8 ≤ 2 ^ finrank (ZMod 2) W := by omega
    have h3 : (2 : ℕ) ^ 3 ≤ 2 ^ finrank (ZMod 2) W := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
      exact h8
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  have hWtot : ∀ v ∈ W, S.q v = 0 := by
    intro v hv
    obtain ⟨c, hcC, hcQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [S.q_cl_eq_zero_iff hcQ, pow_two]
    exact hsq c hcC
  have hWfix : W ≤ fixSpace T := by
    intro v hv
    obtain ⟨c, hcC, hcQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [mem_fixSpace]
    have hρc : T (S.cl c) = S.cl ((e : G) * c * (e : G)⁻¹) := S.ρ_cl e hcQ
    have hcy : (e : G) * c * (e : G)⁻¹ = c := by
      have hcy' : (e : G) * c = c * (e : G) :=
        (mem_centralizer_singleton_iff.mp hcC.2).symm
      rw [hcy', mul_assoc, mul_inv_cancel, mul_one]
    rw [hρc, hcy]
  have horth : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin W) =
      finrank (ZMod 2) S.Qt - finrank (ZMod 2) W :=
    LinearMap.BilinForm.finrank_orthogonal (B := S.q.polarBilin) S.q_nondegenerate W
  have hWle : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W :=
    le_orthogonal_of_totallySingular hWtot
  have hWfr3 : finrank (ZMod 2) W = 3 := by
    have h1 : finrank (ZMod 2) W ≤
        finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin W) :=
      Submodule.finrank_mono hWle
    rw [horth, hE6] at h1
    omega
  have hWeq : LinearMap.BilinForm.orthogonal S.q.polarBilin W = W := by
    refine (Submodule.eq_of_le_of_finrank_eq hWle ?_).symm
    rw [horth, hE6, hWfr3]
  have hcommW : commSpace T ≤ W := by
    have h1 : commSpace T ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
      intro v hv
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      rw [polarBilin_apply_apply, polar_comm, polar_sub_eq_polar_sub hT htt u w,
        mem_fixSpace.mp (hWfix hw), sub_self, polar_zero_right]
    rwa [hWeq] at h1
  have hts : ∀ v ∈ commSpace T, S.q v = 0 := fun v hv => hWtot v (hcommW hv)
  obtain ⟨B, hB, hBmap⟩ :=
    exists_mem_tsCompl_map_eq (q := S.q) (U := S.clSub A) (t := T)
      S.q_nondegenerate hE6 hU3 hUq hT htt hTU ht1U hts
  exact (hA.map_ne_of_noInvariantCompl hM hw hsurj hNS hpne hpp2 hB) hBmap

end MaxEA

end CFSG.LargeExtraspecial.DW
