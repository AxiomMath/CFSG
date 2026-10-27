module

public import CFSG.ClassicalInvolution.Q3.TL4SepComm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

@[expose] def NoInvO2 (Δ : Set (Subgroup G)) : Prop :=
  ∀ J ∈ Δ, ∀ u : G, IsUniqueInvolution J u → ¬ TightInO2 u

theorem T4Hyp.le_center_of_normal_two (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : NoInvO2 Δ) {P : Subgroup G} (hP : P.Normal) (hP2 : IsPGroup 2 P) :
    P ≤ Subgroup.center G := by
  have hle : omegaGen Δ ≤ Subgroup.centralizer (P : Set G) := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨u, hu⟩ := (h.hyp.omega1 J hJ).1
    exact h.le_centralizer_of_not_mem hJ hu hP fun huP => hno J hJ u hu ⟨P, hP, hP2, huP⟩
  rw [hgen] at hle
  intro p hp
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g))) p hp).symm

theorem isPGroup_fittingSubgroup (hO : classicalInvolutionOddCore G = ⊥) :
    IsPGroup 2 (fittingSubgroup G) :=
  TightA.isPGroup_two_of_normal_nilpotent hO fittingSubgroup_normal inferInstance

omit [Finite G] in
theorem le_centralizer_sup {J A B : Subgroup G} (hA : J ≤ Subgroup.centralizer (A : Set G))
    (hB : J ≤ Subgroup.centralizer (B : Set G)) :
    J ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
  Subgroup.le_centralizer_iff.mpr
    (sup_le (Subgroup.le_centralizer_iff.mp hA) (Subgroup.le_centralizer_iff.mp hB))

theorem T4Hyp.mem_layer (h : T4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) (hno : ¬ TightInO2 u) : u ∈ layer G := by
  by_contra huE
  have hEn : (layer G).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := G)
    infer_instance
  have hE := h.le_centralizer_of_not_mem hJ hu hEn huE
  have hF := h.le_centralizer_of_not_mem hJ hu fittingSubgroup_normal fun huF =>
    hno ⟨_, fittingSubgroup_normal, isPGroup_fittingSubgroup h.odd, huF⟩
  have hC : J ≤ Subgroup.centralizer (generalizedFitting G : Set G) := le_centralizer_sup hF hE
  have hJF : J ≤ generalizedFitting G := hC.trans (centralizer_generalizedFitting_le G)
  obtain ⟨-, P, hP, hPnc⟩ := h.hyp.omega1 J hJ
  refine hPnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hb := Subgroup.mem_centralizer_iff.mp (hC (hP.1 a.2)) b (hJF (hP.1 b.2))
  exact hb.symm

end CFSG.ClassicalInvolution.Q3.TL4
