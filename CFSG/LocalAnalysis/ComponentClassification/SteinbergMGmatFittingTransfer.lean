module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseGeneric
public import CFSG.Monster.Generated.Data

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.BMCase

open CFSG.Monster.Generated

theorem gmat_eq_top_of_inner {X : Type*} [Group X] {F : Subgroup X} [F.Normal]
    (hC : Subgroup.centralizer (F : Set X) ≤ F)
    (hinner : ∀ φ : MulAut F, ∃ f : F, φ = MulAut.conj f) : F = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨f, hf⟩ := hinner (MulAut.conjNormal x)
  have hact : ∀ y ∈ F, x * y * x⁻¹ = (f : X) * y * (f : X)⁻¹ := by
    intro y hy
    have h := congrArg (fun φ : MulAut F => ((φ ⟨y, hy⟩ : F) : X)) hf
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using h
  have hcent : (f : X)⁻¹ * x ∈ Subgroup.centralizer (F : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hact y hy
    calc y * ((f : X)⁻¹ * x) = (f : X)⁻¹ * ((f : X) * y * (f : X)⁻¹) * x := by group
      _ = (f : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h]
      _ = (f : X)⁻¹ * x * y := by group
  have h := F.mul_mem f.2 (hC hcent)
  rwa [mul_inv_cancel_left] at h

@[expose] def gmatCentralizerEquiv {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y) (t : X) :
    Subgroup.centralizer ({t} : Set X) ≃* Subgroup.centralizer ({ψ t} : Set Y) where
  toFun c := ⟨ψ c, Subgroup.mem_centralizer_singleton_iff.2 (by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 c.2])⟩
  invFun d := ⟨ψ.symm d, Subgroup.mem_centralizer_singleton_iff.2 (by
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply,
      Subgroup.mem_centralizer_singleton_iff.1 d.2])⟩
  left_inv c := Subtype.ext (ψ.symm_apply_apply (c : X))
  right_inv d := Subtype.ext (ψ.apply_symm_apply (d : Y))
  map_mul' c d := Subtype.ext (map_mul ψ (c : X) (d : X))

theorem gmat_oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem gmat_pPrimeCore_eq_bot_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : CFSG.pPrimeCore 2 G' = ⊥) : CFSG.pPrimeCore 2 G = ⊥ := by
  have hmap := CFSG.pPrimeCore_map_iso 2 e
  rw [h] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 hmap

theorem gmat_generalizedFitting_transfer
    (hautG : ∀ α : MulAut Gmat, ∃ g : Gmat, α = MulAut.conj g)
    (hodd : ∀ s : Gmat, orderOf s = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer {s}) = ⊥ ∧
        CFSG.oddCore (Subgroup.centralizer {s}) = ⊥)
    {X : Type*} [Group X] [Finite X] (e : CFSG.generalizedFitting X ≃* Gmat) :
    CFSG.generalizedFitting X = ⊤ ∧ ∀ t : X, orderOf t = 2 →
      CFSG.pPrimeCore 2 (Subgroup.centralizer ({t} : Set X)) = ⊥ ∧
        CFSG.oddCore (Subgroup.centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have htop : CFSG.generalizedFitting X = ⊤ :=
    gmat_eq_top_of_inner (CFSG.centralizer_generalizedFitting_le X) (inner_of_equiv e hautG)
  refine ⟨htop, fun t ht => ?_⟩
  let ψ : X ≃* Gmat := (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm).trans e
  have hψ : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  have h2 := gmat_pPrimeCore_eq_bot_of_mulEquiv (gmatCentralizerEquiv ψ t) (hodd _ hψ).1
  exact ⟨h2, (gmat_oddCore_eq_pPrimeCore_two _).trans h2⟩

end CFSG.ComponentClassification.BMCase
