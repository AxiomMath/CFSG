module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthGen
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthLift
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTransport

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (fixedGroup mem_fixedGroup)
open CFSG.ClassicalInvolution.ModelFacts (commutatorElement_mul_central)
open scoped commutatorElement

section FixLift

variable {K Γ : Type*} [Group K] [Group Γ]

theorem le_map_fixedGroup (θ : K →* Γ) (hker : θ.ker ≤ Subgroup.center K) (α : K ≃* K) (s : Γ)
    (hα : ∀ y, θ (α y) = s * θ y * s⁻¹) {N : Subgroup Γ} (hNp : ⁅N, N⁆ = N)
    (hNr : N ≤ θ.range) (hNs : ∀ n ∈ N, s * n = n * s) : N ≤ (fixedGroup α).map θ := by
  have hM : (N.comap θ).map θ = N := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hNr]
  have hcomm : ⁅N.comap θ, N.comap θ⁆ ≤ fixedGroup α := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hc : ∀ z : K, θ z ∈ N → z⁻¹ * α z ∈ Subgroup.center K := fun z hz => by
      refine hker ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα z, hNs _ hz]
      group
    rw [mem_fixedGroup, map_commutatorElement]
    have e₁ : α x = x * (x⁻¹ * α x) := by group
    have e₂ : α y = y * (y⁻¹ * α y) := by group
    rw [e₁, e₂]
    exact commutatorElement_mul_central (hc x hx) (hc y hy)
  calc N = ⁅N, N⁆ := hNp.symm
    _ = ⁅(N.comap θ).map θ, (N.comap θ).map θ⁆ := by rw [hM]
    _ = (⁅N.comap θ, N.comap θ⁆).map θ := (Subgroup.map_commutator _ _ _).symm
    _ ≤ (fixedGroup α).map θ := Subgroup.map_mono hcomm

end FixLift

section Quasisimple

variable {K Γ : Type*} [Group K] [Group Γ] {θ : K →* Γ}

theorem isQuasisimple_perfLift (hker : θ.ker ≤ Subgroup.center K) {C : Subgroup K}
    {N : Subgroup Γ} (hN : N ≤ C.map θ) (hNp : ⁅N, N⁆ = N)
    (hq : CFSG.Open.IsQuasisimple ↥N) : CFSG.Open.IsQuasisimple ↥(perfLift θ C N) := by
  have hP : Group.IsPerfect ↥(perfLift θ C N) :=
    Subgroup.isPerfect_iff.mpr (perfLift_perfect hker hN hNp)
  set f : ↥(perfLift θ C N) →* ↥N :=
    (θ.comp (perfLift θ C N).subtype).codRestrict N (fun y => perfLift_le_comap C N y.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨n, hn⟩
    have : n ∈ (perfLift θ C N).map θ := by rw [map_perfLift hN hNp]; exact hn
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩
  have hfk : f.ker ≤ Subgroup.center ↥(perfLift θ C N) := by
    intro y hy
    have h1 : θ (y : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have h2 : (y : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro z
    exact Subtype.ext (h2 z)
  have hq' := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    ((CFSG.LocalCores.isQuasisimple_iff_of_surjective hP f hfs hfk).mpr hq')

end Quasisimple

section Side

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem elemOn_le_map_centralizer [Finite F] [FiniteDimensional F V] {K X : Type} [Group K]
    [Group X] [Finite X] (h2 : (2 : F) ≠ 0) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (ψ : K →* X) (hψker : ψ.ker ≤ Subgroup.center K)
    (hψnorm : ψ.range.Normal) (θ : K →* (V ≃ₗ[F] V)) (hθker : θ.ker ≤ Subgroup.center K)
    (hθrange : θ.range = elementaryGroup Q) (f : X) (α : K ≃* K)
    (hαψ : ∀ y, f * ψ y * f⁻¹ = ψ (α y)) (s : V ≃ₗ[F] V)
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : s * s = 1)
    (hαθ : ∀ y, θ (α y) = s * θ y * s⁻¹) {ε : F} (hε : ε * ε = 1) {d : X}
    (hd : d ∈ involutionOddCore f) :
    elemOn Q (eigenSub s ε) ≤ ((Subgroup.centralizer ({d} : Set X)).comap ψ).map θ := by
  set S : Submodule F V := eigenSub s ε with hS
  have hSnd : PolarNondegOn Q S := polarNondegOn_eigenSub h2 hQ hs hs2 hε
  by_cases h3 : 3 ≤ Module.finrank F S
  swap
  · rw [elemOn_eq_bot_of_finrank_le_two hSnd (by omega)]
    exact bot_le
  obtain ⟨𝓗, h𝓗, hcover⟩ := layerGenOn hodd h5 (nondegenerate_polarBilin_restrict hSnd) h3
  set N : Subgroup (V ≃ₗ[F] V) := elemOn Q S with hN
  have hNperf : ⁅N, N⁆ = N := by
    refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) (hcover.trans ?_)
    refine iSup₂_le fun H hH => ?_
    obtain ⟨hle, hq, -⟩ := h𝓗 H hH
    have hHp : ⁅H, H⁆ = H := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hq.1)
    calc H = ⁅H, H⁆ := hHp.symm
      _ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hle hle
  have hNr : N ≤ θ.range := by
    rw [hθrange]
    exact elemOn_le_elementaryGroup
  have hNs : ∀ n ∈ N, s * n = n * s := fun n hn =>
    comm_of_scalar_elemOn hs hε (fun x hx => mem_eigenSub.mp hx) hn
  have hNfix : N ≤ (fixedGroup α).map θ := le_map_fixedGroup θ hθker α s hαθ hNperf hNr hNs
  have hfixcomm : ∀ c ∈ fixedGroup α, θ c * s = s * θ c := by
    intro c hc
    have h := hαθ c
    rw [mem_fixedGroup.mp hc] at h
    calc θ c * s = (s * θ c * s⁻¹) * s := by rw [← h]
      _ = s * θ c := by group
  have hstable : ∀ c ∈ fixedGroup α, N.map (MulAut.conj (θ c)).toMonoidHom = N := by
    intro c hc
    have hgO : ∀ g ∈ θ.range, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg => by
      rw [hθrange] at hg
      exact elementaryGroup_le_orthogonalGroup Q hg
    have hconj : ∀ c' ∈ fixedGroup α, ∀ n ∈ N, θ c' * n * (θ c')⁻¹ ∈ N := by
      intro c' hc' n hn
      refine conj_mem_elemOn (hgO _ ⟨c', rfl⟩) (fun x => ?_) hn
      exact mem_eigenSub_iff_of_comm (hfixcomm c' hc')
    refine le_antisymm ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      exact hconj c hc n hn
    · intro n hn
      refine ⟨(θ c)⁻¹ * n * θ c, ?_, ?_⟩
      · have := hconj c⁻¹ ((fixedGroup α).inv_mem hc) n hn
        simpa [map_inv] using this
      · show θ c * ((θ c)⁻¹ * n * θ c) * (θ c)⁻¹ = n
        group
  refine hcover.trans (iSup₂_le fun H hH => ?_)
  obtain ⟨hle, hq, hnormal⟩ := h𝓗 H hH
  have hHp : ⁅H, H⁆ = H := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hq.1)
  have hHfix : H ≤ (fixedGroup α).map θ := hle.trans hNfix
  set Ĥ : Subgroup K := perfLift θ (fixedGroup α) H with hĤ
  have hĤmap : Ĥ.map θ = H := map_perfLift hHfix hHp
  have hĤsub : CFSG.Open.IsSubnormal Ĥ (fixedGroup α) :=
    isSubnormal_perfLift hθker hNfix hNperf hHfix hHp hle hnormal hstable
  have hĤcomp : CFSG.Open.IsComponentOf Ĥ (fixedGroup α) :=
    ⟨perfLift_le _ _, hĤsub, isQuasisimple_perfLift hθker hHfix hHp hq⟩
  have hmain := CFSG.ClassicalInvolution.Balance.isComponentOf_map_centralizer hψker 1 f α
    (fun y => by simpa using hαψ y) hĤcomp
  have e1 : (MulAut.conj (1 : K)).toMonoidHom = MonoidHom.id _ := by
    ext; simp
  rw [e1, MonoidHom.comp_id] at hmain
  have : ψ.range.Normal := hψnorm
  have hsub : CFSG.Open.IsSubnormal ψ.range ⊤ :=
    CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf
  have hlayer := CFSG.ClassicalInvolution.Balance.le_centralizerLayer_of_isComponentOf hsub hmain
  have hĤC : Ĥ ≤ (Subgroup.centralizer ({d} : Set X)).comap ψ := by
    intro y hy
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (CFSG.ClassicalInvolution.Balance.commute_of_mem_involutionOddCore_of_mem_centralizerLayer
      hd (hlayer ⟨y, hy, rfl⟩)).symm
  calc H = Ĥ.map θ := hĤmap.symm
    _ ≤ _ := Subgroup.map_mono hĤC

end Side

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
