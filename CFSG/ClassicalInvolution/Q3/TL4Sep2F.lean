module

public import CFSG.ClassicalInvolution.Q3.TL4SepCompo

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.eq_component_of_inv_mem (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : NoInvO2 Δ) {L₀ : Subgroup G} (hL₀ : CFSG.IsComponent L₀)
    (hmem : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → z ∈ L₀) {M : Subgroup G}
    (hM : CFSG.IsComponent M) : M = L₀ := by
  by_contra hML
  have hle : omegaGen Δ ≤ Subgroup.centralizer (M : Set G) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨z, hz⟩ := (h.hyp.omega1 K hK).1
    exact h.le_centralizer_component hgen hno hK hz hM
      (h.not_mem_component_of_ne hno hK hz hL₀ hM (Ne.symm hML) (hmem K hK z hz))
  rw [hgen] at hle
  obtain ⟨a, b, hab⟩ := hM.1.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top (b' : G)))) a' a'.2)

theorem T4Hyp.layer_eq_of_inv_mem (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : NoInvO2 Δ) {L₀ : Subgroup G} (hL₀ : CFSG.IsComponent L₀)
    (hmem : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → z ∈ L₀) : layer G = L₀ :=
  le_antisymm (sSup_le fun _ hM => (h.eq_component_of_inv_mem hgen hno hL₀ hmem hM).le)
    (le_sSup hL₀)

theorem T4Hyp.pCore_eq_center (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤) (hno : NoInvO2 Δ) :
    pCore 2 G = Subgroup.center G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (h.le_center_of_normal_two hgen hno pCore_normal pCore_isPGroup) ?_
  have hZ2 : IsPGroup 2 ↥(Subgroup.center G) :=
    TightA.isPGroup_two_of_normal_nilpotent h.odd inferInstance inferInstance
  exact le_sSup ⟨inferInstance, hZ2⟩

theorem fittingSubgroup_eq_pCore (hO : classicalInvolutionOddCore G = ⊥) :
    fittingSubgroup G = pCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_antisymm (le_sSup ⟨fittingSubgroup_normal, isPGroup_fittingSubgroup hO⟩)
    (CFSG.LocalCores.fitting_characteristic.2.2 _ pCore_normal pCore_isNilpotent)

theorem T4Hyp.generalizedFitting_eq_of_inv_mem (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : NoInvO2 Δ) {L₀ : Subgroup G} (hL₀ : CFSG.IsComponent L₀)
    (hmem : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → z ∈ L₀) :
    generalizedFitting G = L₀ ⊔ pCore 2 G := by
  rw [generalizedFitting, fittingSubgroup_eq_pCore h.odd, h.layer_eq_of_inv_mem hgen hno hL₀ hmem,
    sup_comm]

theorem T4Hyp.centralizer_eq_center_of_inv_mem (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : NoInvO2 Δ) {L₀ : Subgroup G} (hL₀ : CFSG.IsComponent L₀)
    (hmem : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → z ∈ L₀) :
    Subgroup.centralizer (L₀ : Set G) = Subgroup.center G := by
  refine le_antisymm (fun x hx => ?_) (Subgroup.center_le_centralizer _)
  have hZ := h.pCore_eq_center hgen hno
  have hxE : x ∈ Subgroup.centralizer (layer G : Set G) := by
    rw [h.layer_eq_of_inv_mem hgen hno hL₀ hmem]
    exact hx
  have hxF : x ∈ Subgroup.centralizer (fittingSubgroup G : Set G) := by
    rw [fittingSubgroup_eq_pCore h.odd, hZ]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (Subgroup.mem_center_iff.mp hy x).symm
  have hxC : x ∈ Subgroup.centralizer (generalizedFitting G : Set G) :=
    le_centralizer_sup (Subgroup.zpowers_le.mpr hxF) (Subgroup.zpowers_le.mpr hxE)
      (Subgroup.mem_zpowers x)
  have hxFs : x ∈ generalizedFitting G := centralizer_generalizedFitting_le G hxC
  have : (generalizedFitting G).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).1
  have hZn : (generalizedFitting G ⊓
      Subgroup.centralizer (generalizedFitting G : Set G)).Normal := by
    infer_instance
  have hle : generalizedFitting G ⊓ Subgroup.centralizer (generalizedFitting G : Set G) ≤
      pCore 2 G := le_sSup ⟨hZn, isPGroup_center_fstar h.odd⟩
  rw [← hZ]
  exact hle ⟨hxFs, hxC⟩

end CFSG.ClassicalInvolution.Q3.TL4
