module

public import CFSG.ClassicalInvolution.Q3.TL4SepThmAD
public import CFSG.ClassicalInvolution.Q3.TL4SepCent

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

theorem T4Hyp.component_normal (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤) (hno : NoInvO2 Δ)
    {L : Subgroup G} (hL : CFSG.IsComponent L) : L.Normal := by
  have hle : omegaGen Δ ≤ Subgroup.normalizer (L : Set G) := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨z, hz⟩ := (h.hyp.omega1 K hK).1
    intro x hx
    exact mem_normalizer_iff_conjSub_eq.mpr (h.conjSub_component_eq hK hz (hno K hK z hz) hL hx)
  rw [hgen] at hle
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hle)

theorem T4Hyp.exists_component (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤) (hno : NoInvO2 Δ)
    {J : Subgroup G} (hJ : J ∈ Δ) {u : G} (hu : IsUniqueInvolution J u) :
    ∃ L : Subgroup G, CFSG.IsComponent L ∧ L.Normal ∧ u ∈ L := by
  have huE := h.mem_layer hJ hu (hno J hJ u hu)
  have hex : ∃ L : Subgroup G, CFSG.IsComponent L ∧ ¬ ∀ x ∈ L, x * u = u * x := by
    by_contra hcon
    push Not at hcon
    have hle : layer G ≤ Subgroup.centralizer ({u} : Set G) :=
      sSup_le fun L hL x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcon L hL x hx)
    have hC : u ∈ Subgroup.centralizer (layer G : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
    exact hno J hJ u hu ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup h.odd, huE, hC⟩
  obtain ⟨L, hL, hLu⟩ := hex
  have hLn := h.component_normal hgen hno hL
  refine ⟨L, hL, hLn, ?_⟩
  by_contra huL
  exact hLu fun x hx =>
    Subgroup.mem_centralizer_iff.mp (h.le_centralizer_of_not_mem hJ hu hLn huL hu.mem) x hx

theorem T4Hyp.le_centralizer_component (h : T4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : NoInvO2 Δ) {K : Subgroup G} (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z)
    {M : Subgroup G} (hM : CFSG.IsComponent M) (hzM : z ∉ M) :
    K ≤ Subgroup.centralizer (M : Set G) :=
  h.le_centralizer_of_not_mem hK hz (h.component_normal hgen hno hM) hzM

theorem T4Hyp.not_mem_component_of_ne (h : T4Hyp r G Δ) (hno : NoInvO2 Δ) {K : Subgroup G}
    (hK : K ∈ Δ) {z : G} (hz : IsUniqueInvolution K z) {L M : Subgroup G}
    (hL : CFSG.IsComponent L) (hM : CFSG.IsComponent M) (hLM : L ≠ M) (hzL : z ∈ L) : z ∉ M := by
  intro hzM
  have hzZ := TightA.mem_centerLayer_of_mem_center hL hzL fun y hy =>
    comm_of_ne hL hM hLM hy hzM
  exact hno K hK z hz ⟨_, TightA.centerLayer_normal, TightA.centerLayer_isPGroup h.odd, hzZ⟩

theorem T4Hyp.le_centralizer_component_of_le (h : T4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ)
    {u : G} (hu : IsUniqueInvolution J u) {L : Subgroup G} (hL : CFSG.IsComponent L)
    (hLn : L.Normal) (hLu : L ≤ Subgroup.centralizer ({u} : Set G)) :
    J ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  have hsub : CFSG.Open.IsSubnormal L (Subgroup.centralizer ({u} : Set G)) :=
    CFSG.Open.IsSubnormal.step hLu inferInstance (CFSG.Open.IsSubnormal.refl _)
  exact (h.tightDatum hJ hu S).le_centralizer_of_isSubnormal hsub
    ⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩

theorem isPGroup_center_fstar (hO : classicalInvolutionOddCore G = ⊥) :
    IsPGroup 2 ↥(generalizedFitting G ⊓
      Subgroup.centralizer (generalizedFitting G : Set G)) := by
  have : (generalizedFitting G).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).1
  have hZn : (generalizedFitting G ⊓
      Subgroup.centralizer (generalizedFitting G : Set G)).Normal := by
    infer_instance
  have hZc : IsMulCommutative ↥(generalizedFitting G ⊓
      Subgroup.centralizer (generalizedFitting G : Set G)) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      fun y hy h hh => Subgroup.mem_centralizer_iff.mp hy.2 h hh.1
  exact TightA.isPGroup_two_of_normal_nilpotent hO hZn inferInstance

end CFSG.ClassicalInvolution.Q3.TL4
