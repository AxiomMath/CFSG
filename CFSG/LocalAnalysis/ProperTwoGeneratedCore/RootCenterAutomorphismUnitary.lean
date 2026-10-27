module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryRoot

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K]

structure UnitaryRootCenterAutomorphisms (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (q : ℕ) : Prop where
  mem_root_iff : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, g ∈ unitaryCoverRoot J hJ ↔
    ∃ (a b : K) (M : GL (Fin 3) K), a * J.conj a + (b + J.conj b) = 0 ∧
      (M : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix J a b ∧
      (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M
  mem_center_iff : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J, g ∈ unitaryRootCenter J hJ ↔
    ∃ (b : K) (M : GL (Fin 3) K), J.conj b = b ∧
      (M : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix J 0 b ∧
      (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M
  coe_diagAut : ∀ (c : normOne J) (g : GL (Fin 3) K) (hg : g ∈ J.specialSubgroup),
    ((diagAut J hJ c ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
      ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (diag3 1 (c : Kˣ) 1 * g * (diag3 1 (c : Kˣ) 1)⁻¹)
  coe_barAut : ∀ (g : GL (Fin 3) K) (hg : g ∈ J.specialSubgroup),
    ((barAut J hJ ⟨ProjGenLinGroup.mk g, Subgroup.mem_map_of_mem _ hg⟩ :
      ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk (glAut J.conj g)
  exists_sylow : ∃ S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
    (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ
  center_iff : ∀ x, x ∈ unitaryRootCenter J hJ ↔
    x ∈ unitaryCoverRoot J hJ ∧ ∀ y ∈ unitaryCoverRoot J hJ, x * y = y * x
  omega_eq : (CFSG.omega₁ (G := unitaryCoverRoot J hJ) (p := 2)).map
    (unitaryCoverRoot J hJ).subtype = unitaryRootCenter J hJ
  injOn_conj : Set.InjOn MulAut.conj
    (unitaryCoverRoot J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  mem_aut_iff : ∀ γ, γ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) ↔
    ∃ r ∈ unitaryCoverRoot J hJ, ∃ c : normOne J, ∃ ε : Fin 2,
      γ = MulAut.conj r * diagAut J hJ c * barAut J hJ ^ (ε : ℕ)
  eq_of_eq : ∀ r ∈ unitaryCoverRoot J hJ, ∀ r' ∈ unitaryCoverRoot J hJ,
    ∀ (c c' : normOne J) (ε ε' : Fin 2),
      MulAut.conj r * diagAut J hJ c * barAut J hJ ^ (ε : ℕ) =
        MulAut.conj r' * diagAut J hJ c' * barAut J hJ ^ (ε' : ℕ) → r = r' ∧ c = c' ∧ ε = ε'
  inf_eq_bot : (unitaryCoverRoot J hJ).map MulAut.conj ⊓ diagBar J hJ = ⊥
  sup_eq : (unitaryCoverRoot J hJ).map MulAut.conj ⊔ diagBar J hJ =
    rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ)
  normal : (((unitaryCoverRoot J hJ).map MulAut.conj).subgroupOf
    (rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ))).Normal
  card_diagBar : Nat.card (diagBar J hJ) = 2 * (q + 1)
  diagBar_dihedral : Nonempty (diagBar J hJ ≃* DihedralGroup (q + 1))
  sq_mem : ∀ γ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ),
    γ ^ 2 ∈ (unitaryRootCenter J hJ).map MulAut.conj →
      γ ∈ (unitaryCoverRoot J hJ).map MulAut.conj ∨ γ ^ 2 = 1
  fix_eq : ∀ R₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
    unitaryRootCenter J hJ ≤ R₀ → R₀ ≤ unitaryCoverRoot J hJ →
      R₀.relIndex (unitaryCoverRoot J hJ) ≤ 2 →
      {γ | γ ∈ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) ∧
        ∀ x ∈ R₀, γ x = x} = ((unitaryRootCenter J hJ).map MulAut.conj : Set (MulAut _))
  conj_isElementaryAbelian : IsElementaryAbelian 2 ((unitaryRootCenter J hJ).map MulAut.conj)
  card_conj : Nat.card ((unitaryRootCenter J hJ).map MulAut.conj) = q

theorem mem_unitaryRootCenter_iff_heisenberg [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (g : ProjectiveSpecialUnitaryMatrixGroup J) :
    g ∈ unitaryRootCenter J hJ ↔ ∃ (b : K) (M : GL (Fin 3) K), J.conj b = b ∧
      (M : Matrix (Fin 3) (Fin 3) K) = heisenbergMatrix J 0 b ∧
      (g : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1.2, hermitianUnipotentGL J z, conj_snd_of_fst_eq_zero J hz, ?_,
      hermitianUnipotentPSU_val J hJ z⟩
    rw [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq_heisenbergMatrix,
      show z.1.1 = 0 from hz, map_zero, neg_zero]
  · rintro ⟨b, M, hb, hM, hg⟩
    let z : hermitianUnipotentCoord J := ⟨(0, b), by
      rw [hb, CharTwo.add_self_eq_zero, zero_mul, add_zero]⟩
    refine ⟨z, rfl, Subtype.ext ?_⟩
    rw [hermitianUnipotentPSU_val, hg]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq_heisenbergMatrix, hM]
    simp [z]

theorem unitaryRootCenterAutomorphisms [Finite K] (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    UnitaryRootCenterAutomorphisms J hJ (2 ^ f) := by
  have : CharP K 2 := charP_two_of_card f hcard
  obtain ⟨hD, hDiso⟩ := diagBar_dihedral J hJ f hf hcard hfixed
  obtain ⟨hcU, hcUcard⟩ := conj_unitaryRootCenter J hJ f hf hcard hfixed
  exact
    { mem_root_iff := mem_root_iff J hJ
      mem_center_iff := mem_unitaryRootCenter_iff_heisenberg J hJ
      coe_diagAut := fun c g hg => coe_psuAut_mk J _ _ hg
      coe_barAut := fun g hg => coe_psuAut_mk J _ _ hg
      exists_sylow := ⟨unitaryCoverSylow J f hf hcard hfixed hJ, rfl⟩
      center_iff := fun _ => mem_unitaryRootCenter_iff J hJ f hcard hfixed
      omega_eq := map_omega₁_unitaryCoverRoot J hJ
      injOn_conj := unitaryRoot_injOn_conj J hJ f hf hcard hfixed
      mem_aut_iff := fun γ => ⟨exists_eq_conj_diag_bar J hJ f hf hcard hfixed, by
        rintro ⟨r, hr, c, ε, rfl⟩
        exact conj_diag_bar_mem_rootCenterAut J hJ hr c ε⟩
      eq_of_eq := fun r hr r' hr' c c' ε ε' h =>
        eq_of_conj_diag_bar_eq J hJ f hf hcard hfixed hr hr' h
      inf_eq_bot := conj_root_inf_diagBar J hJ f hf hcard hfixed
      sup_eq := conj_root_sup_diagBar J hJ f hf hcard hfixed
      normal := conj_root_normal J hJ
      card_diagBar := hD
      diagBar_dihedral := hDiso
      sq_mem := fun γ hγ hsq => sq_mem_conj_center J hJ f hf hcard hfixed hγ hsq
      fix_eq := fun R₀ _ hR₀R hidx => fix_eq_conj_center J hJ f hf hcard hfixed hR₀R hidx
      conj_isElementaryAbelian := hcU
      card_conj := hcUcard }

theorem even_unitary_root_center_automorphisms_and_large_root_centralizers {f : ℕ}
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    UnitaryRootCenterAutomorphisms (fieldDataHermitianForm h) rfl (2 ^ f) :=
  have := h.finite
  unitaryRootCenterAutomorphisms (fieldDataHermitianForm h) f hf h.card_eq_sq
    (card_fixed_fieldDataHermitianForm h) rfl

end CFSG.ProperTwoGeneratedCore.RootCenter
