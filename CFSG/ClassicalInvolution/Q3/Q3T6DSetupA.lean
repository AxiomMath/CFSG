module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOmegaStep
public import CFSG.ClassicalInvolution.Q3.Q3CLSeven1
public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Data

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_hexagon_data3 (hΩ : HypOmegaGen Ω)
    {K J : Subgroup G} {z j : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (hj : IsUniqueInvolution J j) (hstar : J ∈ omegaStarNbr Ω K) (hnot : J ∉ omegaNbr Ω K)
    (hA : ∀ g ∈ pairNormalizers K J z j, conjSub g K ≠ J) :
    ∃ (v : G) (K' : Subgroup G), Subgroup.zpowers v ∈ USet Ω ∧ Subgroup.zpowers v ≤ J ∧
      IsSylow2In (Subgroup.zpowers v) (J ⊓ Subgroup.centralizer ({z} : Set G)) ∧
      K' ≠ K ∧ twinSet Ω K = {K, K'} ∧ v * v ∈ K ⊔ K' := by
  obtain ⟨u, v, R, T, c⟩ := Sec6Gen.exists_cfg64 hΩ hK hJ hz hj hstar hnot
  have hInA : InA Ω K J := ⟨hstar, hnot, z, j, hz, hj, fun ⟨g, hg, hgK⟩ => hA g hg hgK⟩
  obtain ⟨-, -, ⟨Kstar, hKs, htw, -, hvv, -, -⟩, ⟨-, -, hVsyl⟩, -⟩ :=
    Sec6Gen.l6_4ThreeGenAll G Ω hΩ K hK J hJ hInA z j hz hj _ _ rfl rfl u v c.hU
      c.hUK c.hV c.hVJ c.hUV R T c.hR c.hT c.huR c.hvT c.hRN c.hTN
  exact ⟨v, Kstar, c.hV, c.hVJ, hVsyl, hKs, htw, hvv⟩

theorem mem_sup_of_hexagon3 (hΩ : HypOmegaGen Ω) {J M Ms : Subgroup G}
    {zJ v : G} (hzJ : IsUniqueInvolution J zJ) (hVU : Subgroup.zpowers v ∈ USet Ω)
    (hVJ : Subgroup.zpowers v ≤ J) (hvv : v * v ∈ M ⊔ Ms) : zJ ∈ M ⊔ Ms := by
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := Sec6Gen.isPGroup_of_mem_USet hΩ hVU
  obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hVU
  obtain ⟨w, hw, hww⟩ := exists_sq_eq_of_cyclic hzJ hVJ hVc hV2 h4V
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hww, ← (Commute.refl v).mul_zpow]
  exact Subgroup.zpow_mem _ hvv k

theorem aSet_mem_dComp3 (hΩ : HypOmegaGen Ω) {M : Subgroup G}
    (hM : M ∈ Ω) (hL : ∃ L ∈ omegaNbr Ω M, L ∉ twinSet Ω M) {J' : Subgroup G}
    (hJ' : J' ∈ aSet Ω M) : J' ∈ dComp Ω M := by
  obtain ⟨L, hLnbr, hLtw⟩ := hL
  obtain ⟨zM, zJ, hv⟩ := hJ'
  obtain ⟨v, Ms, hVU, hVJ, -, hMsM, htw, hvv⟩ :=
    exists_hexagon_data3 hΩ hM hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hMsT : Ms ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  have hMsΩ : Ms ∈ Ω := hMsT.1
  have hzMs : IsUniqueInvolution Ms zM := isUniqueInvolution_of_mem_twinSet hv.hzK hMsT
  have hzJM : zJ ∈ M ⊔ Ms := mem_sup_of_hexagon3 hΩ hv.hzJ hVU hVJ hvv
  have hLnbr' := hLnbr
  obtain ⟨hLΩ, hLM, T, hTR, hTL, hTN⟩ := hLnbr'
  have hTsyl : IsSylow2In T L := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hLΩ hTR hTL
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := Sec6Gen.eight_le_of_mem_RSet hΩ hTR
  have hLMs : L ≠ Ms := fun h => hLtw (by rw [htw]; exact Or.inr h)
  have hTC : T ≤ Subgroup.centralizer ({zM} : Set G) := fun x hx =>
    mem_centralizer_singleton_of_conj_eq
      (hv.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hx)))
  have hTMs : T ≤ Subgroup.normalizer (Ms : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hMsΩ hLΩ (Ne.symm hLMs) hzMs hTL hT2
      (by omega) hTC
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution hΩ hLΩ
  have hcM : ∀ x ∈ T, ∀ m ∈ M, ⁅x, m⁆ ∈ oddCoreOf M := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hM hLΩ (Ne.symm hLM)
      hv.hzK hzL hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hcMs : ∀ x ∈ T, ∀ m ∈ Ms, ⁅x, m⁆ ∈ oddCoreOf Ms := fun x hx m hm =>
    Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hMsΩ hLΩ (Ne.symm hLMs)
      hzMs hzL hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hMsN : Ms ≤ Subgroup.normalizer (M : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hMsΩ hM hMsM hzMs hv.hzK
  have hMN : M ≤ Subgroup.normalizer (Ms : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hM hMsΩ (Ne.symm hMsM) hv.hzK hzMs
  have hcN := commutator_mem_oddCore_sup hMsN hMN hcM hcMs
  obtain ⟨q, hqN₀, hqfix⟩ := exists_conj_fixed_involution (N₀ := M ⊔ Ms) hT2 hzJM hv.hzJ.sq
    (fun x hx => Asc77.T3CII.mem_normalizer_sup (hTN hx) (hTMs hx))
    (fun x hx => hcN x hx zJ hzJM)
  have hqM : q ∈ Subgroup.normalizer (M : Set G) := (sup_le Subgroup.le_normalizer hMsN) hqN₀
  have hJ''Ω : conjSub q J' ∈ Ω := hΩ.conjInvariant q J' hv.mem
  have hzJ'' : IsUniqueInvolution (conjSub q J') (q * zJ * q⁻¹) := hv.hzJ.conj q
  have hcent : T ≤ Subgroup.centralizer ({q * zJ * q⁻¹} : Set G) := fun x hx =>
    mem_centralizer_singleton_of_conj_eq (hqfix x hx)
  have hqMinv : conjSub q⁻¹ M = M :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (M : Set G)).inv_mem hqM)
  have hJ''L : conjSub q J' ≠ L := by
    intro h
    have h1 : conjSub q J' ∈ omegaNbr Ω M := h ▸ hLnbr
    have h2 := omegaNbr_conj hΩ.conjInvariant h1 q⁻¹
    rw [conjSub_inv_conjSub, hqMinv] at h2
    exact hv.not_nbr h2
  have hTJ'' : T ≤ Subgroup.normalizer ((conjSub q J' : Subgroup G) : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ''Ω hLΩ hJ''L hzJ'' hTL hT2 (by omega) hcent
  have hpath : conjSub q J' ∈ dComp Ω M :=
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hLΩ, Or.inl hLnbr⟩)
      ⟨hJ''Ω, Or.inr ⟨hLΩ, hJ''L.symm, T, hTR, hTL, hTJ''⟩⟩
  have hqσ : q ∈ sigmaNorm Ω M := T8.normalizer_le_sigmaNorm hΩ.conjInvariant hM hqM
  exact (hqσ J').mpr hpath

theorem aStar_subset_dComp3 (hΩ : HypOmegaGen Ω) {K : Subgroup G}
    (hK : K ∈ Ω) (hall : ∀ M ∈ Ω, ∃ L ∈ omegaNbr Ω M, L ∉ twinSet Ω M) :
    ∀ J ∈ aStar Ω K, J ∈ dComp Ω K := by
  have key : ∀ J, Relation.ReflTransGen (aGraphAdj Ω) K J → J ∈ Ω ∧ J ∈ dComp Ω K := by
    intro J hJ
    induction hJ with
    | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hbΩ, hbd⟩ := ih
      obtain ⟨hcΩ, hc⟩ := hbc
      refine ⟨hcΩ, ?_⟩
      rcases hc with hc | hc | ⟨hc, hcb⟩
      · exact Relation.ReflTransGen.trans hbd (aSet_mem_dComp3 hΩ hbΩ (hall b hbΩ) hc)
      · have h1 : b ∈ dComp Ω c := aSet_mem_dComp3 hΩ hcΩ (hall c hcΩ) hc
        exact Relation.ReflTransGen.trans hbd (reflTransGen_dAdj_symm hcΩ h1)
      · obtain ⟨-, z, hzb, hzc⟩ := hc
        exact Relation.ReflTransGen.tail hbd
          ⟨hcΩ, Or.inl (Q3CL.T3.twin_mem_omegaNbr hΩ hbΩ hcΩ hcb hzb hzc)⟩
  exact fun J hJ => (key J hJ).2

end Data

section Twin


theorem CaseIIHyp3.omegaNbr_twin {G : Type} [Group G] [Finite G] {K J : Subgroup G}
    {z t a g : G} (h : CaseIIHyp3 K J z t a g) :
    ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K := by
  intro L hL
  by_contra hLtw
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := h.hypGen
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hall : ∀ M ∈ CoreAssembly.conjClass K, ∃ L' ∈ omegaNbr (CoreAssembly.conjClass K) M,
      L' ∉ twinSet (CoreAssembly.conjClass K) M := by
    rintro M ⟨g', rfl⟩
    refine ⟨conjSub g' L, omegaNbr_conj hΩ.conjInvariant hL g', fun hmem => hLtw ?_⟩
    have := twinSet_conj hΩ.conjInvariant hmem g'⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hdc := aStar_subset_dComp3 hΩ hKΩ hall
  refine h.branch.dDisconnected ?_
  intro K₁ h₁ J₁ hJ₁
  have hK₁ : K₁ ∈ dComp (CoreAssembly.conjClass K) K := hdc K₁ (by rw [h.star]; exact h₁)
  have hJ₁' : J₁ ∈ dComp (CoreAssembly.conjClass K) K := hdc J₁ (by rw [h.star]; exact hJ₁)
  exact Relation.ReflTransGen.trans (reflTransGen_dAdj_symm hKΩ hK₁) hJ₁'

theorem omegaNbrTwin3 :
    ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K J : Subgroup G) (z t a g : G),
      CaseIIHyp3 K J z t a g →
        ∀ L ∈ omegaNbr (CoreAssembly.conjClass K) K, L ∈ twinSet (CoreAssembly.conjClass K) K := by
  intro G _ _ _ K J z t a g h
  exact h.omegaNbr_twin

end Twin

end CFSG.ClassicalInvolution.Q3.Q3T6D
