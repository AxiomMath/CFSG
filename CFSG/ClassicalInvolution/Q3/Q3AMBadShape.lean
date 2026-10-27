module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadConj
public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Shape


variable {G : Type} [Group G] [Finite G]

theorem nbrCoreFam_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g : G) (M : Subgroup G)
    (a : G) :
    nbrCoreFam Ω (conjSub g M) (g * a * g⁻¹) = conjSub g '' nbrCoreFam Ω M a := by
  ext C
  constructor
  · rintro ⟨N, hN, rfl⟩
    have hN₀ : conjSub g⁻¹ N ∈ omegaNbr Ω M := by
      have := omegaNbr_conj hΩ hN g⁻¹
      rwa [conjSub_inv_conjSub] at this
    refine ⟨exactCore3 a (conjSub g⁻¹ N), ⟨_, hN₀, rfl⟩, ?_⟩
    rw [← exactCore3_conjSub g a (conjSub g⁻¹ N), conjSub_conjSub_inv]
  · rintro ⟨_, ⟨N, hN, rfl⟩, rfl⟩
    exact ⟨conjSub g N, omegaNbr_conj hΩ hN g, (exactCore3_conjSub g a N).symm⟩

theorem PspNbhdSp4.conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {M : Subgroup G} {a : G}
    (g : G) (h : PspNbhdSp4 Ω M a) : PspNbhdSp4 Ω (conjSub g M) (g * a * g⁻¹) := by
  obtain ⟨ι, hι, D, ha, hS⟩ := h
  have hΛ := nbrCoreFam_conj hΩ g M a
  have hΛ' := centralizingMembers_conj_image hΛ a
  have hY := centralizingLayer_conj_image hΛ a
  obtain ⟨D', hS'⟩ := ShapeSingle.conj_exists (conjQuotEquiv g hY)
    (map_oddQuotientFamily_conj hY hΛ') D (c := CompData.model .PSp 2)
    (zb := QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (nbrCoreFam Ω M a) {a})) ⟨a, ha⟩) hS
  have ha' : g * a * g⁻¹ ∈ centralizingLayer (nbrCoreFam Ω (conjSub g M) (g * a * g⁻¹))
      {g * a * g⁻¹} := by
    rw [hY]
    exact conj_mem_conjSub ha
  exact ⟨ι, hι, D', ha', hS'⟩

theorem PspNbhdL4.conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {M : Subgroup G} {a : G}
    (g : G) (h : PspNbhdL4 Ω M a) : PspNbhdL4 Ω (conjSub g M) (g * a * g⁻¹) := by
  obtain ⟨ι, hι, D, ha, hS⟩ := h
  have hΛ := nbrCoreFam_conj hΩ g M a
  have hΛ' := centralizingMembers_conj_image hΛ a
  have hY := centralizingLayer_conj_image hΛ a
  obtain ⟨D', hS'⟩ := ShapeSingle.conj_exists (conjQuotEquiv g hY)
    (map_oddQuotientFamily_conj hY hΛ') D (c := CompData.model .PSL 4)
    (zb := QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (nbrCoreFam Ω M a) {a})) ⟨a, ha⟩) hS
  have ha' : g * a * g⁻¹ ∈ centralizingLayer (nbrCoreFam Ω (conjSub g M) (g * a * g⁻¹))
      {g * a * g⁻¹} := by
    rw [hY]
    exact conj_mem_conjSub ha
  exact ⟨ι, hι, D', ha', hS'⟩

theorem PspNbhdSp4.of_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K M : Subgroup G}
    {z a : G} (hK : IsUniqueInvolution K z) (hM : IsUniqueInvolution M a) {g : G}
    (hg : conjSub g K = M) (h : PspNbhdSp4 Ω K z) : PspNbhdSp4 Ω M a := by
  have h1 := hK.conj g
  rw [hg] at h1
  have h2 : a = g * z * g⁻¹ := hM.eq h1
  subst hg
  rw [h2]
  exact h.conj hΩ g

theorem PspNbhdL4.of_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K M : Subgroup G}
    {z a : G} (hK : IsUniqueInvolution K z) (hM : IsUniqueInvolution M a) {g : G}
    (hg : conjSub g K = M) (h : PspNbhdL4 Ω K z) : PspNbhdL4 Ω M a := by
  have h1 := hK.conj g
  rw [hg] at h1
  have h2 : a = g * z * g⁻¹ := hM.eq h1
  subst hg
  rw [h2]
  exact h.conj hΩ g

end Shape

section Triangle


variable {G : Type} [Group G] [Finite G]

variable {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
  {z t : G}

theorem PspSetting.uniq_K' [IsSimpleGroup G] (h : PspSetting Ω K J S R T W z t K') :
    IsUniqueInvolution K' (z * t) := by
  have hΩ : HypOmegaMod Ω := h.bad.std.stand.hyp
  obtain ⟨u, hu⟩ := hΩ.exists_uniqueInvolution h.nbrK.1
  have h1 := h.bad.eq_mul_of_nbr_nbr h.nbrK h.nbrJ hu
  rwa [h1] at hu

theorem PspSetting.shapeE4_of_sp4 [IsSimpleGroup G] (h : PspSetting Ω K J S R T W z t K')
    (hK : PspNbhdSp4 Ω K z) : PspShapeE4 Ω K J K' z t := by
  have hΩ : HypOmegaMod Ω := h.bad.std.stand.hyp
  have hinv := hΩ.conjInvariant
  obtain ⟨gJ, hgJ⟩ := h.bad.std.stand.trans J h.bad.std.hJ.1
  obtain ⟨gK', hgK'⟩ := h.bad.std.stand.trans K' h.nbrK.1
  exact Or.inl ⟨hK, PspNbhdSp4.of_conj hinv h.bad.std.hz h.bad.std.ht hgJ hK,
    PspNbhdSp4.of_conj hinv h.bad.std.hz h.uniq_K' hgK' hK⟩

theorem PspSetting.shapeE4_of_l4 [IsSimpleGroup G] (h : PspSetting Ω K J S R T W z t K')
    (hK : PspNbhdL4 Ω K z) : PspShapeE4 Ω K J K' z t := by
  have hΩ : HypOmegaMod Ω := h.bad.std.stand.hyp
  have hinv := hΩ.conjInvariant
  obtain ⟨gJ, hgJ⟩ := h.bad.std.stand.trans J h.bad.std.hJ.1
  obtain ⟨gK', hgK'⟩ := h.bad.std.stand.trans K' h.nbrK.1
  exact Or.inr ⟨hK, PspNbhdL4.of_conj hinv h.bad.std.hz h.bad.std.ht hgJ hK,
    PspNbhdL4.of_conj hinv h.bad.std.hz h.uniq_K' hgK' hK⟩

end Triangle

end CFSG.ClassicalInvolution.Q3.Q3AM
