module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23A04

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3OCL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3T8
open CFSG.ClassicalInvolution.Asc77 (alphaOf oddCoreOf IsElemAbelian2)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 (Hyp23Setting)
open CFSG.ClassicalInvolution.Asc77 (Hyp23bData e189_commute_of_mem)
open CFSG.ClassicalInvolution.Asc77.T7A (isElemAbelian2_closure_pair)
open CFSG.ClassicalInvolution.Asc77.T7K (generators_mem_B comm_e_of_mem_W)
open CFSG.ClassicalInvolution.Asc77.T7Y (commute_of_alphaOf_eq_bot)
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Delta

variable {G : Type} [Group G]

theorem deltaCore_le_alphaOf' (A : Subgroup G) : deltaCore A ≤ alphaOf A := by
  rw [CFSG.ClassicalInvolution.Asc77.Lemma54Proof.alphaOf_eq A]
  exact le_sup_right

end Delta

section Ex23

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem exactMembers_of_alpha_23 [IsSimpleGroup G] (hs : Hyp23Setting Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) : ExactMembers Ω := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hzK : IsUniqueInvolution K z := hs.hz
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    Q3T8.Asc77.T7Y.le_centralizer_e hs hd hα hKΩ hzK hR hRN
  have hKz : ∀ k ∈ K, k * z = z * k := fun k hk =>
    (e189_commute_of_mem hzK hk).symm
  obtain ⟨hzB, huB, heB⟩ := generators_mem_B z u e
  have hze : z ≠ e := fun h => Q3T8.Asc77.T7K.e_not_mem_sup hs hd
    (h ▸ Subgroup.mem_sup_left hzK.mem)
  have hA : IsElemAbelian2 (Subgroup.closure ({z, e} : Set G)) 2 :=
    isElemAbelian2_closure_pair hzK.sq hd.he2 hzK.ne_one hd.he1 hze
      (comm_e_of_mem_W hd hd.hzW)
  have hAB : Subgroup.closure ({z, e} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hzB
    · exact heB
  obtain ⟨-, halpha⟩ := Q3T8.Asc77.T7K.c23_5X_one_proved hs hd
  have hαA : alphaOf (Subgroup.closure ({z, e} : Set G)) = ⊥ := (halpha _ hAB hA).trans hα
  have hΔ : deltaCore (Subgroup.closure ({z, e} : Set G)) = ⊥ :=
    le_bot_iff.mp (hαA ▸ deltaCore_le_alphaOf' _)
  have hKF : K ≤ Subgroup.centralizer
      ((Subgroup.closure ({z, e} : Set G) : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hle : Subgroup.closure ({z, e} : Set G) ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hKz k hk).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hKe hk)).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
  have hcenter : Subgroup.center G = ⊥ :=
    CoreAssembly.center_eq_bot (Q3T8.Asc77.T7Y.exists_noncomm hst)
  have hnc : ∀ f ∈ Subgroup.closure ({z, e} : Set G), f ≠ 1 → f ∉ Subgroup.center G := by
    intro f _ hf1 hfc
    rw [hcenter, Subgroup.mem_bot] at hfc
    exact hf1 hfc
  have hK3 : IsClassicalMember3 K z :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hKΩ hzK).toQ3 (by norm_num)
  have hLoc : LocalLieSystems3 Ω :=
    localLieSystems3_of_cit3Below (Q3T7.inClass3_of_stand3 hst.toStand3)
      (Q3T7.cit3Below_of_stand3 hst.toStand3)
  have hKo : classicalInvolutionOddCore ↥K = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hst.hyp.conjInvariant hLoc hKΩ hK3
      hKF hnc hΔ
  exact exactMembers3_of_conjugates hKo fun L hL => by
    obtain ⟨g', hg'⟩ := hst.trans L hL
    exact ⟨g', hg'.symm⟩

end Ex23

section Ex22

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' K₃ : Subgroup G}
  {z u₁ u₂ u₃ : G}

theorem exactMembers_of_alpha_22 [IsSimpleGroup G]
    (hs : Q3T8.Asc77.Hyp22Setting Ω K K' K₃ z u₁ u₂ u₃)
    (hα : alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥) : ExactMembers Ω := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hK₃Ω : K₃ ∈ Ω := hs.hK₃.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := hs.hzK'
  have hzK₃ : IsUniqueInvolution K₃ z := hs.hzK₃
  set c : G := u₁ * u₂ with hcdef
  have hc2 : c * c = 1 := hs.sq_12
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have hc1 : c ≠ 1 :=
    (Q3T8.Asc77.T7S22.mul_ne_one_of_twins hΩ hK hK' hs.hne.symm hz hs.hu₁.1 hs.hu₂.1
      hs.hu₂.2).1
  have hu₁K₃ : u₁ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK hK₃Ω hs.hK₃K.symm hz hzK₃ hs.hu₁.1
  have hu₂K₃ : u₂ ∈ trivialOnQuot K₃ :=
    Q3T8.Asc77.T7J.twin_le_trivialOnQuot hΩ hK' hK₃Ω hs.hK₃K'.symm hzK' hzK₃ hs.hu₂.1
  have hctq : c ∈ trivialOnQuot K₃ := Subgroup.mul_mem _ hu₁K₃ hu₂K₃
  have hcl : Q3T8.Generic.IsClassicalMember K₃ z :=
    Q3T8.Asc77.isClassicalMember_of_twin hΩ hK₃Ω hzK₃
  have hK₃c : K₃ ≤ Subgroup.centralizer ({c} : Set G) := by
    intro ℓ hℓ
    obtain ⟨i, hi, n, hn, rfl⟩ := Q3T8.Asc77.ExactLayer.exactCore_cover hcl hc2' hctq ℓ hℓ
    refine Subgroup.mul_mem _ (Q3T8.Asc77.ExactLayer.exactCore_le_centralizer c K₃ hi) ?_
    have hnO : n ∈ oddCoreOf (Subgroup.centralizer ({z} : Set G)) :=
      oddCoreIn_le_of_isSubnormal (Q3T8.Asc77.T7A.isSubnormal_centralizer hΩ hK₃Ω hzK₃) hn
    have hnc : n * c = c * n :=
      commute_of_alphaOf_eq_bot
        (Subgroup.subset_closure (by simp)) hz.ne_one hα hnO (Subgroup.subset_closure (by simp))
    exact Subgroup.mem_centralizer_singleton_iff.mpr hnc
  have hK₃z : ∀ k ∈ K₃, k * z = z * k := fun k hk =>
    (e189_commute_of_mem hzK₃ hk).symm
  have hΔ : deltaCore (Subgroup.closure ({c, z} : Set G)) = ⊥ :=
    le_bot_iff.mp (hα ▸ deltaCore_le_alphaOf' _)
  have hKF : K₃ ≤ Subgroup.centralizer ((Subgroup.closure ({c, z} : Set G) : Subgroup G) :
      Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hle : Subgroup.closure ({c, z} : Set G) ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hK₃c hk)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hK₃z k hk).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
  have hcenter : Subgroup.center G = ⊥ :=
    CoreAssembly.center_eq_bot (Q3T8.Asc77.T7Y.exists_noncomm hst)
  have hnc : ∀ f ∈ Subgroup.closure ({c, z} : Set G), f ≠ 1 → f ∉ Subgroup.center G := by
    intro f _ hf1 hfc
    rw [hcenter, Subgroup.mem_bot] at hfc
    exact hf1 hfc
  have hK3 : IsClassicalMember3 K₃ z := hcl.toQ3 (by norm_num)
  have hLoc : LocalLieSystems3 Ω :=
    localLieSystems3_of_cit3Below (Q3T7.inClass3_of_stand3 hst.toStand3)
      (Q3T7.cit3Below_of_stand3 hst.toStand3)
  have hKo : classicalInvolutionOddCore ↥K₃ = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hst.hyp.conjInvariant hLoc hK₃Ω hK3
      hKF hnc hΔ
  exact exactMembers3_of_conjugates hKo fun L hL => by
    obtain ⟨g', hg'⟩ := hst.trans L hL
    obtain ⟨g'', hg''⟩ := hst.trans K₃ hK₃Ω
    refine ⟨g' * g''⁻¹, ?_⟩
    rw [conjSub_mul, ← hg'', conjSub_inv_conjSub] at *
    exact hg'.symm

end Ex22

end CFSG.ClassicalInvolution.Q3.Q3OCL
