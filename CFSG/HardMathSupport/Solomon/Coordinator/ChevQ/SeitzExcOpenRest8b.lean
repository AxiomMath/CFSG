module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFixedNC
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwToral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwOuterHeis
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerShiftAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTorusDet
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThreeProved
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree TauCeti
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

set_option linter.unusedSectionVars false

section Model

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def F4TwLayerModel : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → 3 ≤ Nat.card K →
    ∀ (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ), orderOf ω = 3 →
    ∀ z : adjointGroup TwClass.f4Six.tag K,
      baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
        D.g * rootDiagUnit TwClass.f4Six.tag
          (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D.g⁻¹ →
    ∃ (ℓ f : ℕ) (K' : Type) (_ : Field K') (h : UnitaryFieldData ℓ f K')
      (ρ : Fin 2 → unitarySU ℓ f K' 3 →* adjointGroup TwClass.f4Six.tag K),
      ℓ ^ f = Nat.card K ∧ (∀ i, Function.Injective (ρ i)) ∧
      (ρ 0).range = frameIn (TwClass.f4Six.X₁ D) ∧ (ρ 1).range = frameIn (TwClass.f4Six.X₂ D) ∧
      ∀ x : adjointGroup TwClass.f4Six.tag K, x * z = z * x →
        ∀ i, ∃ γ : unitaryIsom3 h, ∀ y, x * ρ i y * x⁻¹ = ρ i (suConj h γ y)

end Model

namespace SeitzExcOpenRest8bAux

section Twisted

open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8Aux


theorem twClosingFrameAt (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ) (hω3 : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag K)
    (hzbc : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
      D.g * rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D.g⁻¹) :
    ClosingFrameAt z (frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D)) := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set i₁ : Fin TwClass.f4Six.tag.rank := ⟨1, by decide⟩ with hi₁
  set a : Fin TwClass.f4Six.tag.rank → D.Lˣ := Pi.mulSingle i₁ ω with ha
  have hchar : ∀ α : Fin TwClass.f4Six.tag.rank → ℤ, rootChar a α = ω ^ (α i₁) := by
    intro α
    unfold rootChar
    rw [Finset.prod_eq_single i₁]
    · simp [ha]
    · intro j _ hj
      simp [ha, Pi.mulSingle_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hS : ∀ S : Set (Fin TwClass.f4Six.tag.rank → ℤ), (∀ α ∈ S, 3 ∣ α i₁) →
      (∀ α ∈ S, IsRoot TwClass.f4Six.tag α) → ∀ α ∈ S, IsRoot TwClass.f4Six.tag α ∧
        rootChar a α = 1 := by
    intro S h3S hrS α hα
    refine ⟨hrS α hα, ?_⟩
    rw [hchar, ← orderOf_dvd_iff_zpow_eq_one, hω3]
    exact_mod_cast h3S α hα
  have hS₁ : ∀ α ∈ TwClass.f4Six.S₁, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ f4LongList} := by rw [← QuasiF4.S₁_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.F4 1 3 := by
      rw [coset_eq]
      exact Or.inl hα'
    exact hmem.2
  have hS₂ : ∀ α ∈ TwClass.f4Six.S₂, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1 := by
    refine hS _ (fun α hα => ?_) (fun α hα => hα.1)
    have hα' : α ∈ {r | r ∈ f4ShortList} := by rw [← QuasiF4.S₂_eq]; exact hα
    have hmem : α ∈ cosetRoots Tag.F4 1 3 := by
      rw [coset_eq]
      exact Or.inr hα'
    exact hmem.2
  have hcomm : ∀ S : Set (Fin TwClass.f4Six.tag.rank → ℤ),
      (∀ α ∈ S, IsRoot TwClass.f4Six.tag α ∧ rootChar a α = 1) →
      D.frame S ≤ Subgroup.centralizer
        ({(z : ModGL TwClass.f4Six.tag K)} : Set (ModGL TwClass.f4Six.tag K)) := by
    intro S hS' x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxc := rootSpan_le_centralizer_rootDiagUnit (K := D.L) a hS' hx.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxc
    apply baseChangeGL_injective (algebraMap K D.L)
    rw [map_mul, map_mul, hzbc]
    calc baseChangeGL (algebraMap K D.L) x * (D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹)
        = D.g * ((D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g⁻¹⁻¹) *
            rootDiagUnit TwClass.f4Six.tag a) * D.g⁻¹ := by group
      _ = D.g * (rootDiagUnit TwClass.f4Six.tag a * (D.g⁻¹ * baseChangeGL (algebraMap K D.L) x *
            D.g⁻¹⁻¹)) * D.g⁻¹ := by rw [hxc]
      _ = (D.g * rootDiagUnit TwClass.f4Six.tag a * D.g⁻¹) * baseChangeGL (algebraMap K D.L) x := by
          group
  have hKq : TwClass.f4Six.minQ ≤ Nat.card K := h3
  have hle : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤ adjointGroup TwClass.f4Six.tag K :=
    sup_le inf_le_left inf_le_left
  have hq3 := twQuasi_of_ne_e6Six TwClass.f4Six (by decide) K hKq D
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hy' : (y : ModGL TwClass.f4Six.tag K) ∈ TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D := hy
    have hsup : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤
        Subgroup.centralizer ({(z : ModGL TwClass.f4Six.tag K)} :
          Set (ModGL TwClass.f4Six.tag K)) :=
      sup_le (hcomm _ hS₁) (hcomm _ hS₂)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hsup hy')
  · refine nonsolvable_frameIn hle ?_
    intro hs
    haveI := hs
    haveI h2 : Group.IsSolvable ↥(TwClass.f4Six.X₂ D) :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective
        (le_sup_right : TwClass.f4Six.X₂ D ≤ TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D))
    obtain ⟨hperf, -, a₀, b₀, hab⟩ := hq3.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a₀
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b₀
    haveI : Nontrivial ↥(TwClass.f4Six.X₂ D) := ⟨⟨x, 1, fun h => hab (by rw [h]; simp)⟩⟩
    exact (IsSolvable.commutator_lt_top_of_nontrivial
      (↥(TwClass.f4Six.X₂ D))).ne hperf.commutator_eq_top
  · exact closing_of_twFrameClosing hle (twClosing_f4Six K h3 D)
  · exact normalizerSolvable_of_twFrame hle (twNormalizer_f4Six K hKq D)

theorem twClosingFrameAt_conj (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ) (hω3 : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag K)
    (hzbc : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
      D.g * rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D.g⁻¹)
    {e g : adjointGroup TwClass.f4Six.tag K} (hg : g * e * g⁻¹ = z) :
    ClosingFrameAt e
      ((frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D)).map (MulAut.conj g⁻¹).toMonoidHom) := by
  have h := (twClosingFrameAt K h3 D ω hω3 z hzbc).conj g⁻¹
  rwa [show g⁻¹ * z * g⁻¹⁻¹ = e by rw [← hg]; group] at h

theorem twFrame_le_hyperClosure (hM : F4TwLayerModel) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ) (hω3 : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag K)
    (hzbc : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
      D.g * rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D.g⁻¹)
    {E₀ : Subgroup (adjointGroup TwClass.f4Six.tag K)} (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) (hz : z ∈ E₀) :
    frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) ≤ hyperClosure 3 ⊤ E₀ := by
  classical
  obtain ⟨ℓ, f, K', _, h, ρ, hq, hinj, hr0, hr1, hact⟩ := hM K hK h3 D ω hω3 z hzbc
  have hcl := twClosingFrameAt K h3 D ω hω3 z hzbc
  have hKq : TwClass.f4Six.minQ ≤ Nat.card K := h3
  have hle₁ : TwClass.f4Six.X₁ D ≤ adjointGroup TwClass.f4Six.tag K := inf_le_left
  have hle₂ : TwClass.f4Six.X₂ D ≤ adjointGroup TwClass.f4Six.tag K := inf_le_left
  have hZ : Subgroup.center (adjointGroup TwClass.f4Six.tag K) = ⊥ := center_adjointGroup_eq_bot
  have hinjc := conj_injective_of_center hZ
  set E : Subgroup (MulAut (adjointGroup TwClass.f4Six.tag K)) := E₀.map MulAut.conj with hEdef
  have hEa : IsElemAbelian 3 E :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _
  have hEc : Nat.card E = 27 := by
    rw [hEdef, Subgroup.card_map_of_injective hinjc, hc]
    norm_num
  have hYq : CFSG.IsQuasisimple (unitarySU ℓ f K' 3) := by
    have e1 : unitarySU ℓ f K' 3 ≃* (ρ 0).range := MonoidHom.ofInjective (hinj 0)
    have e2 : (ρ 0).range ≃* frameIn (TwClass.f4Six.X₁ D) := MulEquiv.subgroupCongr hr0
    have e3 : frameIn (TwClass.f4Six.X₁ D) ≃* TwClass.f4Six.X₁ D :=
      Subgroup.subgroupOfEquivOfLe hle₁
    exact CFSG.IsQuasisimple.of_mulEquiv (e1.trans (e2.trans e3))
      (twQuasi_of_ne_e6Six TwClass.f4Six (by decide) K hKq D).1
  have hq3 : 3 ∣ ℓ ^ f + 1 := by omega
  have hq2 : ℓ ^ f ≠ 2 := by omega
  have M : E6Three.TwLayerFacts (unitarySU ℓ f K' 3) (suConj h).range :=
    E6Three.twLayerFacts_of_stmts E6Three.twFixedNonCentral_holds E6Three.twToralPlane_holds
      E6Three.twInnerHeisPlane_holds E6Three.twOuterHeisPlane_holds h hq3 hq2
      (E6Three.shiftQs_exists_noncomm hYq) (fun N hN => E6Three.shiftQs_normal_dichotomy hYq N)
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 : D.g * rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D.g⁻¹ = 1 := by
      rw [← hzbc, h1, OneMemClass.coe_one, map_one]
    have h3' : rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) = 1 := by
      have := congrArg (fun x => D.g⁻¹ * x * D.g) h2
      simpa [mul_assoc] using this
    have h4 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective
      (h3'.trans (rootDiagUnit_one (τ := TwClass.f4Six.tag) (K := D.L)).symm)
    have h5 := congrFun h4 ⟨1, by decide⟩
    simp only [Pi.mulSingle_eq_same, Pi.one_apply] at h5
    rw [h5, orderOf_one] at hω3
    omega
  have hzX : ∀ y ∈ frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D), y * z = z * y :=
    fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hcl.centralizes hy)
  have hmem₁ : ∀ y, ρ 0 y ∈ frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) := by
    intro y
    have h1 : ρ 0 y ∈ frameIn (TwClass.f4Six.X₁ D) := by rw [← hr0]; exact ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 h1))
  have hmem₂ : ∀ y, ρ 1 y ∈ frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) := by
    intro y
    have h1 : ρ 1 y ∈ frameIn (TwClass.f4Six.X₂ D) := by rw [← hr1]; exact ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 h1))
  have hmem : ∀ i y, ρ i y ∈ frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) := by
    intro i y
    fin_cases i
    · exact hmem₁ y
    · exact hmem₂ y
  have key : ∀ i, (ρ i).range ≤ hyperClosure 3 ⊤ E₀ := by
    intro i
    have hσ1 : MulAut.conj z ≠ 1 := fun h1 => hz1 (hinjc (h1.trans (map_one _).symm))
    have hσρ : ∀ y, MulAut.conj z (ρ i y) = ρ i y := by
      intro y
      rw [MulAut.conj_apply, ← hzX _ (hmem i y), mul_inv_cancel_right]
    have hρact : ∀ ε ∈ E, ∃ a ∈ (suConj h).range, ∀ y, ε (ρ i y) = ρ i (a y) := by
      rintro ε ⟨x, hx, rfl⟩
      have hxz : x * z = z * x :=
        congrArg Subtype.val (hE₀.1.is_comm.comm (⟨x, hx⟩ : E₀) ⟨z, hz⟩)
      obtain ⟨γ, hγ⟩ := hact x hxz i
      exact ⟨suConj h γ, ⟨γ, rfl⟩, fun y => by rw [MulAut.conj_apply, hγ y]⟩
    exact (E6Three.le_seitzHyperGamma_of_acts_abs M hEa hEc (hinj i) ⟨z, hz, rfl⟩ hσ1 hσρ
      hρact).trans (seitzHyperGamma_conj_le_hyperClosure E₀)
  have hX : TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D ≤
      (hyperClosure 3 ⊤ E₀).map (adjointGroup TwClass.f4Six.tag K).subtype := by
    refine sup_le ?_ ?_
    · intro x hx
      have hx' : (⟨x, hle₁ hx⟩ : adjointGroup TwClass.f4Six.tag K) ∈ (ρ 0).range := by
        rw [hr0]
        exact hx
      exact ⟨_, key 0 hx', rfl⟩
    · intro x hx
      have hx' : (⟨x, hle₂ hx⟩ : adjointGroup TwClass.f4Six.tag K) ∈ (ρ 1).range := by
        rw [hr1]
        exact hx
      exact ⟨_, key 1 hx', rfl⟩
  intro y hy
  obtain ⟨g, hg, hgy⟩ := hX (Subgroup.mem_subgroupOf.1 hy)
  have : g = y := Subtype.ext hgy
  exact this ▸ hg

theorem twFrame_conj_le_hyperClosure (hM : F4TwLayerModel) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) (ω : D.Lˣ) (hω3 : orderOf ω = 3)
    (z : adjointGroup TwClass.f4Six.tag K)
    (hzbc : baseChangeGL (algebraMap K D.L) (z : ModGL TwClass.f4Six.tag K) =
      D.g * rootDiagUnit TwClass.f4Six.tag
        (Pi.mulSingle (⟨1, by decide⟩ : Fin TwClass.f4Six.tag.rank) ω) * D.g⁻¹)
    {E₀ : Subgroup (adjointGroup TwClass.f4Six.tag K)} (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) {e g : adjointGroup TwClass.f4Six.tag K} (he : e ∈ E₀)
    (hg : g * e * g⁻¹ = z) :
    (frameIn (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D)).map (MulAut.conj g⁻¹).toMonoidHom ≤
      hyperClosure 3 ⊤ E₀ := by
  have hE₁a : IsElemAbelian 3 (E₀.map (MulAut.conj g).toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _
  have hE₁c : Nat.card (E₀.map (MulAut.conj g).toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  have hz : z ∈ E₀.map (MulAut.conj g).toMonoidHom := ⟨e, he, by rw [← hg]; rfl⟩
  have h1 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (twFrame_le_hyperClosure hM hK h3 D ω hω3 z hzbc hE₁a hE₁c hz)
  refine h1.trans ?_
  have h2 := map_hyperClosure_le (p := 3) (⊤ : Subgroup (adjointGroup TwClass.f4Six.tag K))
    (E₀.map (MulAut.conj g).toMonoidHom) g⁻¹
  rwa [map_conj_map_conj_inv'] at h2

end Twisted

section UnitaryModel

open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.SeitzReduction
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (unitarySet fixSubgroup mem_fixSubgroup
  sln_root_permuting_frobenius_fixed_unitary)
open scoped MatrixGroups


theorem exists_unitaryFrame_model {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) (hK3 : 3 ≤ Nat.card K) {ℓ f : ℕ} [hℓF : Fact ℓ.Prime] (hf : 1 ≤ f)
    (hcard : Nat.card K = ℓ ^ f) (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2)
    {K' : Type} [Field K'] [Algebra K' D.L] (h : UnitaryFieldData ℓ f K')
    {S : Set (Fin τ.rank → ℤ)} {ψ : SL(3, D.L) →* ModGL τ D.L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ} (hψ : IsA2Frame ψ σ)
    (hS : S = {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j})
    (π : Equiv.Perm (Fin 3)) (hπ : ∀ i j, i ≠ j → w • σ i j = σ (π j) (π i)) :
    ∃ ρ : unitarySU ℓ f K' 3 →* adjointGroup τ K, Function.Injective ρ ∧
      ρ.range = frameIn (D.frame S) ∧
      ∀ x : adjointGroup τ K,
        D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g ∈ E6Three.frameActSub ψ →
        ∃ γ : unitaryIsom3 h, ∀ y, x * ρ y * x⁻¹ = ρ (suConj h γ y) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  have hℓ : ℓ.Prime := hℓF.out
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  haveI : CharP D.L ℓ := charP_of_injective_algebraMap (algebraMap K D.L).injective ℓ
  have hFr : ∀ c, D.Fr c = c ^ (ℓ ^ f) := fun c => by rw [D.hFr, hcard]
  choose! ε hε using hψ.transv
  have hnm : D.nW ∈ monomialSubgroup τ D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : (D.L)ˣ, ∀ c : D.L,
      D.nW * pinnedX τ D.L (σ i j) c * D.nW⁻¹ =
        pinnedX τ D.L (σ (π j) (π i)) ((b : D.L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (hψ.isRoot i j hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, weylQuotientHom_eq (mapsRootLines_canonicalRep w), hπ i j hij]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := τ) (ν := 3) ψ hψ.injective σ ε
    (fun i j hij t => hε i j hij t) D.Fr D.Fr_bijective D.nW (fun i j => (π j, π i))
    (fun i j hij => (π.injective.ne hij).symm)
    (fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : D.L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, D.L)) :
        Matrix (Fin 3) (Fin 3) D.L) =
        1 + Matrix.single (π j) (π i) ((b i j : D.L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ := sln_root_permuting_frobenius_fixed_unitary (k := K) hℓ hf
    hcard le_rfl π Φ' b hshape'
  have hfix : ∀ X : SL(3, D.L), X ∈ fixSubgroup Φ' ↔
      ∃ y : unitarySU ℓ f K' 3, E6Three.twUnitaryFrame h H y = X :=
    E6Three.mem_fixSubgroup_iff_exists_twUnitaryFrame h hH
  have hperf : Group.IsPerfect ↥(D.fixedRoot S) := (D.isQuasisimple_fixedRoot_A2Frame hK3 hψ hS π hπ).1
  set F : unitarySU ℓ f K' 3 →* ModGL τ D.L := ψ.comp (E6Three.twUnitaryFrame h H) with hFdef
  have hψS : ψ.range = rootSpan τ D.L S := by rw [hψ.range, hS]
  have hFmem : ∀ y, F y ∈ D.fixedRoot S := by
    intro y
    refine ⟨?_, ?_⟩
    · rw [← hψS]
      exact ⟨_, rfl⟩
    · show D.nW * D.frobGL (F y) * D.nW⁻¹ = F y
      have hX : E6Three.twUnitaryFrame h H y ∈ fixSubgroup Φ' := (hfix _).2 ⟨y, rfl⟩
      rw [hFdef, MonoidHom.comp_apply, hΦ', (mem_fixSubgroup Φ').1 hX]
  have hle : D.frame S ≤ adjointGroup τ K := inf_le_left
  set ρ : unitarySU ℓ f K' 3 →* adjointGroup τ K := (Subgroup.inclusion hle).comp
    ((D.frameEquivFixedRoot hperf).symm.toMonoidHom.comp (F.codRestrict (D.fixedRoot S) hFmem))
    with hρdef
  have hρF : ∀ y, D.g⁻¹ * baseChangeGL (algebraMap K D.L)
      ((ρ y : adjointGroup τ K) : ModGL τ K) * D.g = F y := by
    intro y
    have h1 := D.coe_frameToFixedRoot S ((D.frameEquivFixedRoot hperf).symm ⟨F y, hFmem y⟩)
    have h2 : D.frameToFixedRoot S ((D.frameEquivFixedRoot hperf).symm ⟨F y, hFmem y⟩) =
        ⟨F y, hFmem y⟩ :=
      (D.frameEquivFixedRoot hperf).apply_symm_apply _
    rw [h2] at h1
    exact h1.symm
  have hconjinj : ∀ x x' : adjointGroup τ K,
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g =
        D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL τ K) * D.g → x = x' := by
    intro x x' hxx'
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K D.L)
    have := congrArg (fun z => D.g * z * D.g⁻¹) hxx'
    simpa [mul_assoc] using this
  have hρinj : Function.Injective ρ := by
    intro y y' hyy'
    have h1 := congrArg (fun x : adjointGroup τ K =>
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g) hyy'
    simp only [hρF] at h1
    exact E6Three.twUnitaryFrame_injective h H (hψ.injective h1)
  have hρrange : ρ.range = frameIn (D.frame S) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_subgroupOf.2 ((D.frameEquivFixedRoot hperf).symm ⟨F y, hFmem y⟩).2
    · intro hx
      have hx' : (x : ModGL τ K) ∈ D.frame S := Subgroup.mem_subgroupOf.1 hx
      have hv := D.conj_mem_fixedRoot hx'
      obtain ⟨X, hX⟩ : ∃ X, ψ X = D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g := by
        have : D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g ∈ ψ.range := by
          rw [hψS]
          exact hv.1
        exact this
      have hXfix : X ∈ fixSubgroup Φ' := by
        rw [mem_fixSubgroup]
        apply hψ.injective
        rw [← hΦ', hX]
        exact hv.2
      obtain ⟨y, hy⟩ := (hfix X).1 hXfix
      refine ⟨y, hconjinj _ _ ?_⟩
      rw [hρF y, hFdef, MonoidHom.comp_apply, hy, hX]
  refine ⟨ρ, hρinj, hρrange, fun x hx => ?_⟩
  obtain ⟨γL, hγL⟩ := hx
  set m := D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g with hm
  have hmθ : D.nW * D.frobGL m * D.nW⁻¹ = m := by
    rw [hm, map_mul, map_mul, map_inv, D.frobGL_baseChangeGL, D.frobGL_g]
    group
  have hpres : ∀ X ∈ fixSubgroup Φ', E6Three.conjSL γL X ∈ fixSubgroup Φ' := by
    intro X hX
    rw [mem_fixSubgroup] at hX ⊢
    apply hψ.injective
    rw [← hΦ', ← hγL X, map_mul, map_mul, map_inv]
    calc D.nW * (D.frobGL m * D.frobGL (ψ X) * (D.frobGL m)⁻¹) * D.nW⁻¹
        = (D.nW * D.frobGL m * D.nW⁻¹) * (D.nW * D.frobGL (ψ X) * D.nW⁻¹) *
            (D.nW * D.frobGL m * D.nW⁻¹)⁻¹ := by group
      _ = m * ψ X * m⁻¹ := by rw [hmθ, hΦ', hX]
  set N : GL (Fin 3) D.L := (Matrix.SpecialLinearGroup.toGL H)⁻¹ * γL *
    Matrix.SpecialLinearGroup.toGL H with hN
  have hNnorm : ∀ Y : GL (Fin 3) D.L, Y ∈ unitarySet (ℓ ^ f) 3 →
      N * Y * N⁻¹ ∈ unitarySet (ℓ ^ f) 3 := by
    intro Y hY
    obtain ⟨B, hB, rfl⟩ := E6Three.exists_gl3Emb_of_mem_unitarySet h hY
    have hX : E6Three.twUnitaryFrame h H ⟨B, hB⟩ ∈ fixSubgroup Φ' := (hfix _).2 ⟨_, rfl⟩
    obtain ⟨Y', hY', hXY'⟩ := (hH _).1 (hpres _ hX)
    have e1 := E6Three.toGL_conjSL_eq_mul γL (E6Three.twUnitaryFrame h H ⟨B, hB⟩)
    have e2 := E6Three.toGL_twUnitaryFrame h H ⟨B, hB⟩
    have h3 : Matrix.SpecialLinearGroup.toGL H * Y' * (Matrix.SpecialLinearGroup.toGL H)⁻¹ =
        γL * (Matrix.SpecialLinearGroup.toGL H * E6Three.gl3Emb K' D.L B *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) * γL⁻¹ := by
      rw [← hXY', e1, e2]
    have h4 : N * E6Three.gl3Emb K' D.L B * N⁻¹ = Y' := by
      calc N * E6Three.gl3Emb K' D.L B * N⁻¹
          = (Matrix.SpecialLinearGroup.toGL H)⁻¹ * (γL * (Matrix.SpecialLinearGroup.toGL H *
              E6Three.gl3Emb K' D.L B * (Matrix.SpecialLinearGroup.toGL H)⁻¹) * γL⁻¹) *
                Matrix.SpecialLinearGroup.toGL H := by rw [hN]; group
        _ = (Matrix.SpecialLinearGroup.toGL H)⁻¹ * (Matrix.SpecialLinearGroup.toGL H * Y' *
              (Matrix.SpecialLinearGroup.toGL H)⁻¹) * Matrix.SpecialLinearGroup.toGL H := by
            rw [h3]
        _ = Y' := by group
    rw [h4]
    exact hY'
  obtain ⟨c, B, hc0, hB, hNB⟩ := E6Three.twExists_isom_of_normalizes h hℓ3 hq1 N hNnorm
  refine ⟨⟨B, hB⟩, fun y => hconjinj _ _ ?_⟩
  rw [hρF]
  have hL : D.g⁻¹ * baseChangeGL (algebraMap K D.L)
      ((x * ρ y * x⁻¹ : adjointGroup τ K) : ModGL τ K) * D.g = m * F y * m⁻¹ := by
    rw [← hρF y, hm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    group
  rw [hL, hFdef, MonoidHom.comp_apply, MonoidHom.comp_apply, hγL]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [E6Three.toGL_conjSL_eq_mul, E6Three.toGL_twUnitaryFrame, E6Three.toGL_twUnitaryFrame]
  have hγ : γL = Matrix.SpecialLinearGroup.toGL H * N * (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by
    rw [hN]
    group
  have key := E6Three.conj_eq_gl3Emb hc0 hNB (E6Three.gl3Emb K' D.L (y : GL (Fin 3) K'))
  rw [show ((suConj h ⟨B, hB⟩ y : unitarySU ℓ f K' 3) : GL (Fin 3) K') =
      B * (y : GL (Fin 3) K') * B⁻¹ from coe_suConj _ _, map_mul, map_mul, map_inv, hγ]
  have e3 : Matrix.SpecialLinearGroup.toGL H * N * (Matrix.SpecialLinearGroup.toGL H)⁻¹ *
        (Matrix.SpecialLinearGroup.toGL H * E6Three.gl3Emb K' D.L (y : GL (Fin 3) K') *
          (Matrix.SpecialLinearGroup.toGL H)⁻¹) *
        (Matrix.SpecialLinearGroup.toGL H * N * (Matrix.SpecialLinearGroup.toGL H)⁻¹)⁻¹
      = Matrix.SpecialLinearGroup.toGL H *
          (N * E6Three.gl3Emb K' D.L (y : GL (Fin 3) K') * N⁻¹) *
            (Matrix.SpecialLinearGroup.toGL H)⁻¹ := by group
  rw [e3, key]

end UnitaryModel


end SeitzExcOpenRest8bAux

section F4Model

open CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.SeitzReduction
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4 CFSG.RankThree.E6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8Aux
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8bAux
open scoped MatrixGroups


theorem f4TwLayerModel_holds : F4TwLayerModel := by
  intro K _ _ hK h3 D ω hω z hzbc
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpp, hcardn⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have hcard : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcardn]
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h3K : 3 ∣ Nat.card K := by rw [hcard]; exact dvd_pow_self 3 n.ne_zero
    omega
  have hq1 : p ^ (n : ℕ) % 3 = 2 := by rw [← hcard]; exact hK
  haveI : CharP D.L p := charP_of_injective_algebraMap (algebraMap K D.L).injective p
  let _ : Fintype (GaloisField p (2 * (n : ℕ))) := Fintype.ofFinite _
  let _ := ZMod.algebra D.L p
  let ι : GaloisField p (2 * (n : ℕ)) →+* D.L :=
    (IsAlgClosed.lift (R := ZMod p) (S := GaloisField p (2 * (n : ℕ))) (M := D.L)).toRingHom
  letI : Algebra (GaloisField p (2 * (n : ℕ))) D.L := ι.toAlgebra
  have hU : UnitaryFieldData p n (GaloisField p (2 * (n : ℕ))) :=
    ⟨hpp, n.one_le, GaloisField.card p (2 * (n : ℕ)) (by have := n.pos; omega)⟩
  obtain ⟨πA, hπA⟩ := QuasiF4.long_graph
  obtain ⟨πB, hπB⟩ := QuasiF4.short_graph
  have hA := (f4Long_frame (L := D.L)).transport f4LongV
  have hB := f4Short_frame (L := D.L)
  obtain ⟨ρA, hρAi, hρAr, hρAa⟩ := exists_unitaryFrame_model D h3 n.one_le hcard hp3 hq1 hU hA
    QuasiF4.S₁_eq_chain πA (fun i j hij => by
      show (QuasiF4.wF4 • (f4LongV • chainRoot f4chainLong i j) : Fin Tag.F4.rank → ℤ) =
        f4LongV • chainRoot f4chainLong (πA j) (πA i)
      rw [QuasiF4.w_smul, f4LongV_smul, f4LongV_smul]
      exact hπA i j hij)
  obtain ⟨ρB, hρBi, hρBr, hρBa⟩ := exists_unitaryFrame_model D h3 n.one_le hcard hp3 hq1 hU hB
    QuasiF4.S₂_eq_chain πB (fun i j hij => by
      show (QuasiF4.wF4 • f4ShortSigma i j : Fin Tag.F4.rank → ℤ) = f4ShortSigma (πB j) (πB i)
      rw [QuasiF4.w_smul]
      exact hπB i j hij)
  have hSA : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4LongV • chainRoot f4chainLong i j} = S1set :=
    QuasiF4.S₁_eq_chain.symm.trans QuasiF4.S₁_eq
  have hSB : {r | ∃ i j : Fin 3, i ≠ j ∧ r = f4ShortSigma i j} = S2set :=
    QuasiF4.S₂_eq_chain.symm.trans QuasiF4.S₂_eq
  have hrA : ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) D.L f4LongV)).toMonoidHom.comp
      (f4rhoLong D.L)).range = X1 D.L := by rw [hA.range, hSA]
  have hrB : (f4rhoShort D.L).range = X2 D.L := by rw [hB.range, hSB]
  have hcomm : ∀ A B, Commute
      (((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) D.L f4LongV)).toMonoidHom.comp
        (f4rhoLong D.L)) A) (f4rhoShort D.L B) := by
    intro A B
    refine X1_X2_commute D.L _ ?_ _ ?_
    · rw [← hrA]
      exact ⟨A, rfl⟩
    · rw [← hrB]
      exact ⟨B, rfl⟩
  have hact := toralRootGroup_le_frameActSub hω hA hB hcomm hSA hSB
  have h3a : ∀ i, (Pi.mulSingle (1 : Fin Tag.F4.rank) ω : Fin Tag.F4.rank → (D.L)ˣ) i ^ 3 = 1 := by
    intro i
    by_cases hi : i = 1
    · subst hi
      simp only [Pi.mulSingle_eq_same]
      rw [← hω]
      exact pow_orderOf_eq_one ω
    · simp [Pi.mulSingle_eq_of_ne hi]
  have hgG : D.g ∈ adjointGroup Tag.F4 D.L :=
    parabolicLevi_le_adjointGroup (τ := Tag.F4) (K := D.L) _ D.g_mem
  have hmem : ∀ x : adjointGroup TwClass.f4Six.tag K, x * z = z * x →
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL TwClass.f4Six.tag K) * D.g ∈
        E6Three.frameActSub ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) D.L
          f4LongV)).toMonoidHom.comp (f4rhoLong D.L)) ⊓ E6Three.frameActSub (f4rhoShort D.L) := by
    intro x hxz
    let a : Fin Tag.F4.rank → (D.L)ˣ := Pi.mulSingle (1 : Fin Tag.F4.rank) ω
    let x' : adjointGroup Tag.F4 K := x
    let z' : adjointGroup Tag.F4 K := z
    let g' : ModGL Tag.F4 D.L := D.g
    have hxz' : x' * z' = z' * x' := hxz
    have hzbc' : baseChangeGL (algebraMap K D.L) (z' : ModGL Tag.F4 K) =
        g' * rootDiagUnit Tag.F4 a * g'⁻¹ := hzbc
    have hgG' : g' ∈ adjointGroup Tag.F4 D.L := hgG
    show g'⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) * g' ∈ _
    have hm1 : g'⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) * g' ∈
        adjointGroup Tag.F4 D.L := mul_mem (mul_mem (inv_mem hgG')
      (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K D.L) x'.2)) hgG'
    have hxz'' : baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) *
        (g' * rootDiagUnit Tag.F4 a * g'⁻¹) =
        (g' * rootDiagUnit Tag.F4 a * g'⁻¹) * baseChangeGL (algebraMap K D.L)
          (x' : ModGL Tag.F4 K) := by
      have h1 := congrArg (fun y : adjointGroup Tag.F4 K =>
        baseChangeGL (algebraMap K D.L) (y : ModGL Tag.F4 K)) hxz'
      simp only [Subgroup.coe_mul, map_mul] at h1
      rw [hzbc'] at h1
      exact h1
    have hm2 : rootDiagUnit Tag.F4 a *
        (g'⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) * g') *
        (rootDiagUnit Tag.F4 a)⁻¹ =
        g'⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) * g' := by
      calc rootDiagUnit Tag.F4 a *
            (g'⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) * g') *
            (rootDiagUnit Tag.F4 a)⁻¹
          = g'⁻¹ * ((g' * rootDiagUnit Tag.F4 a * g'⁻¹) *
              baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K)) *
            (g' * rootDiagUnit Tag.F4 a * g'⁻¹)⁻¹ * g' := by group
        _ = g'⁻¹ * (baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) *
              (g' * rootDiagUnit Tag.F4 a * g'⁻¹)) *
            (g' * rootDiagUnit Tag.F4 a * g'⁻¹)⁻¹ * g' := by rw [← hxz'']
        _ = g'⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) * g' := by group
    have hmT : g'⁻¹ * baseChangeGL (algebraMap K D.L) (x' : ModGL Tag.F4 K) * g' ∈
        toralRootGroup Tag.F4 D.L a := by
      rw [← CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_F4_three
        D.L _ h3a, mem_toralCentralizer]
      exact ⟨hm1, hm2⟩
    exact hact hmT
  refine ⟨p, n, GaloisField p (2 * (n : ℕ)), inferInstance, hU, ![ρA, ρB], hcard.symm, ?_, hρAr,
    hρBr, ?_⟩
  · intro i
    fin_cases i
    · exact hρAi
    · exact hρBi
  · intro x hxz i
    fin_cases i
    · exact hρAa x (hmem x hxz).1
    · exact hρBa x (hmem x hxz).2

end F4Model

section F4Twisted

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8Aux
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest8bAux


theorem hyperGen_F4_two_of_regularPlane {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 3 = 2) (h3 : 3 ≤ Nat.card K) {E₀ : Subgroup (adjointGroup .F4 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) {P : Subgroup (adjointGroup .F4 K)}
    (hPE : P ≤ E₀) (hPc : Nat.card P = 3 ^ 2) (D : LangPlaneData .F4 K P)
    (hreg : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → ¬ D.Kills α) : HyperGen 3 ⊤ E₀ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnd : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨D₁⟩ := exists_langLevi TwClass.f4Six.tag K TwClass.f4Six.w
    (TwClass.w_theta TwClass.f4Six)
  obtain ⟨ω, hω⟩ := exists_cube_root_langLevi K hnd D₁
  obtain ⟨z, hzbc, -, -, -⟩ := f4TwistedFrame_of K hK h3 D₁ ω hω
  have hPexp : ∀ x ∈ P, x ^ 3 = 1 := fun x hx => hE₀.2 x (hPE hx)
  obtain ⟨e, heP, e', he'P, he1, he'1, hgen⟩ := exists_gens_of_plane (p := 3) hPexp hPc
  obtain ⟨g, hg⟩ := f4PureTwisted_holds K hK h3 D₁ ω hω z hzbc P hPexp hPc D hreg e heP he1
  obtain ⟨g', hg'⟩ := f4PureTwisted_holds K hK h3 D₁ ω hω z hzbc P hPexp hPc D hreg e' he'P he'1
  exact hyperGen_of_two_closingFrames hgen (isSolvable_centralizer_of_regular D hreg)
    (twClosingFrameAt_conj K h3 D₁ ω hω z hzbc hg) (twClosingFrameAt_conj K h3 D₁ ω hω z hzbc hg')
    (twFrame_conj_le_hyperClosure f4TwLayerModel_holds hK h3 D₁ ω hω z hzbc hE₀ hc (hPE heP) hg)
    (twFrame_conj_le_hyperClosure f4TwLayerModel_holds hK h3 D₁ ω hω z hzbc hE₀ hc (hPE he'P)
      hg')

end F4Twisted

theorem three_le_card_of_threeScope_F4 {K : Type} [Field K] [Finite K]
    (hs : ThreeScope LieTypeIndex.F4 K) : 3 ≤ Nat.card K := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨q, hv, hKq, -, hlist⟩ := hs
  have h2 : Nat.card K ≠ 2 := by
    intro h2
    apply hlist
    have hpe : q.p ^ q.exponent = 2 := by rw [← PrimePower.card_def, ← hKq, h2]
    have hp2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1
      (hpe ▸ dvd_pow_self _ q.exponent_pos.ne')
    have he1 : q.exponent = 1 := by
      rw [hp2] at hpe
      have : (2 : ℕ) ^ q.exponent = 2 ^ 1 := by rw [hpe, pow_one]
      exact Nat.pow_right_injective le_rfl this
    unfold CFSG.AGLEmbedding.P1ThreeLieList
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, q, hp2, he1, ?_⟩))))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  omega

section KilledPlaneDef

open CFSG.HardMathSupport.Timmesfeld.Torality


@[expose] def F4ThreeKilledPlaneWeyl : Prop :=
  ∀ (L : Type) [Field L] (a : Fin 2 → Fin Tag.F4.rank → Lˣ),
    (∀ (s : Fin 2) (i : Fin Tag.F4.rank), a s i ^ 3 = 1) →
    (familyKernel (τ := Tag.F4) a).Nonempty →
    ∀ w : WeylGroup Tag.F4, (∀ s, w ∈ rootCharStabilizer (a s)) →
      w ∈ kernelWeylGroup (familyChar a)

end KilledPlaneDef

section KilledPlane

open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


namespace SeitzExcOpenRest8bAux

theorem langPlaneData_of_toral {τ : Tag} {p : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hpK : ¬ p ∣ Nat.card K) {A : Subgroup (adjointGroup τ K)} (hAp : ∀ x ∈ A, x ^ p = 1)
    {g : ModGL τ (AlgebraicClosure K)} (hgG : g ∈ adjointGroup τ (AlgebraicClosure K))
    (hg : ∀ x ∈ A, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K) * g ∈ torusGroup τ (AlgebraicClosure K)) :
    Nonempty (LangPlaneData τ K A) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have he : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hpq : Nat.Coprime p (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (hq ▸ hpK)
  set ι : K →+* L := algebraMap K L with hι
  set φ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype with hφ
  have hT : ∀ x : A, g⁻¹ * φ x * g ∈ torusGroup τ L := fun x => hg x x.2
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hT x)
  have hexp : ∀ (x : A) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ (a x) ^ p :=
        ((rootDiagUnitHom τ L).map_pow (a x) p)
      rw [this, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * φ x * g) ^ p = g⁻¹ * (φ x) ^ p * g := by
            have := conj_pow (a := g⁻¹) (b := φ x) (i := p)
            rwa [inv_inv] at this
        _ = 1 := by
            rw [← map_pow, hAp x x.2, map_one]
            group
    have h2 : a x ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι y) = baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hFix' : ∀ x : A, entrywiseFrobGL τ L ℓ (f : ℕ) (φ x) = φ x := fun x => hFix (x : ModGL τ K)
  have hn : ∀ x : A, (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g) *
      entrywiseFrobGL τ L ℓ (f : ℕ) (rootDiagUnit τ (a x)) *
      (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g)⁻¹ = rootDiagUnit τ (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix' x]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane ℓ (f : ℕ) he hpq a hexp hgG hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL τ L ℓ (f : ℕ) (g * z) =
      (g * z) * canonicalRep (coxeterSystem τ) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨LangPlaneData.mk w' (iterateFrobenius L ℓ (f : ℕ)) (fun c => ?_) (g * z)
    (mul_mem hgG hzG) hu 1 ?_⟩
  · rw [iterateFrobenius_def, hq]
  · intro x hx
    set xA : A := ⟨x, hx⟩ with hxA
    set d := rootDiagUnit τ (a xA) with hd
    have hzd : z⁻¹ * d * z = d := by
      have := hzcomm xA
      rw [← hd, mul_inv_eq_iff_eq_mul] at this
      calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
        _ = z⁻¹ * (z * d) := by rw [this]
        _ = d := by group
    have ht : (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z) = d := by
      have h0 : φ xA = baseChangeGL ι (x : ModGL τ K) := rfl
      calc (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z)
          = z⁻¹ * (g⁻¹ * φ xA * g) * z := by rw [h0]; group
        _ = d := by rw [ha xA, hzd]
    refine ⟨(g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_twistedTorusOf, ht]
      refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      have hfx : entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι (x : ModGL τ K)) =
          baseChangeGL ι (x : ModGL τ K) := hFix _
      have hFd : entrywiseFrobGL τ L ℓ (f : ℕ) d =
          (canonicalRep (coxeterSystem τ) L w')⁻¹ * d * canonicalRep (coxeterSystem τ) L w' := by
        rw [← ht, map_mul, map_mul, map_inv, hfx, hu]
        group
      change canonicalRep (coxeterSystem τ) L w' * entrywiseFrobGL τ L ℓ (f : ℕ) d *
        (canonicalRep (coxeterSystem τ) L w')⁻¹ = d
      rw [hFd]
      group
    · change (g * z) * ((g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z)) * (g * z)⁻¹ =
        baseChangeGL ι ((1 * x * 1⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K)
      simp only [one_mul, inv_one, mul_one]
      group

theorem nonempty_langPlaneData_of_kills (hW : F4ThreeKilledPlaneWeyl) {K : Type} [Field K]
    [Finite K] (hK3 : ¬ 3 ∣ Nat.card K) {E₀ : Subgroup (adjointGroup .F4 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) {P : Subgroup (adjointGroup .F4 K)}
    (hPE : P ≤ E₀) (hPc : Nat.card P = 3 ^ 2) (D : LangPlaneData .F4 K P)
    {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hk : D.Kills α) :
    Nonempty (LangPlaneData .F4 K E₀) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  set L := AlgebraicClosure K with hLdef
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hℓ : ℓ ≠ 3 := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 3
    apply hK3
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 3 n.ne_zero
  have hLp : ringChar L ≠ 3 := by rw [ringChar.eq L ℓ]; exact hℓ
  have halg := isAlgebraic_zmod_algebraicClosure_of_finite K ℓ
  have hmon : MonomialToralAt Tag.F4 3 := monomialToralAt_three_of_block a2BlockToral_F4
  have hexpE : ∀ x ∈ E₀, x ^ 3 = 1 := hE₀.2
  have hcommE : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set ι : K →+* L := algebraMap K L with hι
  set φ : ↥(adjointGroup Tag.F4 K) →* ModGL Tag.F4 L :=
    (baseChangeGL ι).comp (adjointGroup Tag.F4 K).subtype with hφ
  have hφG : ∀ x, φ x ∈ adjointGroup Tag.F4 L := fun x =>
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι x.2
  set C₀ : ModGL Tag.F4 L := D.g0⁻¹ * φ D.c with hC₀
  have hC₀G : C₀ ∈ adjointGroup Tag.F4 L := mul_mem (inv_mem D.hg0C) (hφG D.c)
  have hconj : ∀ x : adjointGroup Tag.F4 K, D.g0⁻¹ * baseChangeGL ι
      ((D.c * x * D.c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * D.g0 =
        C₀ * φ x * C₀⁻¹ := by
    intro x
    have e : baseChangeGL ι ((D.c * x * D.c⁻¹ : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
        φ D.c * φ x * (φ D.c)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e, hC₀]
    group
  obtain ⟨x₀, hx₀P, y₀, hy₀P, hP⟩ := SeitzExcOpenRest3.exists_two_gen_of_card_sq' hp3 P hPc
    (fun x hx => hexpE x (hPE hx))
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hPc]; norm_num)
  obtain ⟨w₀, hw₀E, hw₀P⟩ : ∃ w₀ ∈ E₀, w₀ ∉ P := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show E₀ ≤ P from fun x hx => h x hx)
    rw [hc, hPc] at hle
    omega
  have hgen : E₀ = Subgroup.closure {x₀, y₀, w₀} := by
    set C := Subgroup.closure ({x₀, y₀, w₀} : Set (adjointGroup Tag.F4 K)) with hCdef
    have hCE : C ≤ E₀ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (rfl | rfl | rfl)
      · exact hPE hx₀P
      · exact hPE hy₀P
      · exact hw₀E
    have hPC : P ≤ C := by
      rw [hP]
      refine Subgroup.closure_mono ?_
      rintro _ (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have hw₀C : w₀ ∈ C := Subgroup.subset_closure (Or.inr (Or.inr rfl))
    have hlt : P < C := lt_of_le_of_ne hPC fun h => hw₀P (h ▸ hw₀C)
    haveI : Finite C :=
      Finite.of_injective (Subgroup.inclusion hCE) (Subgroup.inclusion_injective _)
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 : Nat.card C ∣ 3 ^ 3 := hc ▸ Subgroup.card_dvd_of_le hCE
    obtain ⟨k, hk3, hkC⟩ := (Nat.dvd_prime_pow hp3).1 h2
    rw [hPc, hkC] at h1
    have hk : k = 3 := by
      have : 2 < k := (Nat.pow_lt_pow_iff_right hp3.one_lt).1 h1
      omega
    exact (Subgroup.eq_of_le_of_card_ge hCE (by rw [hc, hkC, hk])).symm
  obtain ⟨a, ha, haα⟩ := hk x₀ hx₀P
  obtain ⟨b, hb, hbα⟩ := hk y₀ hy₀P
  rw [hconj] at ha hb
  have hexpDiag : ∀ x ∈ E₀, ∀ a' : Fin Tag.F4.rank → Lˣ,
      rootDiagUnit Tag.F4 a' = C₀ * φ x * C₀⁻¹ → ∀ i, a' i ^ 3 = 1 := by
    intro x hx a' ha'
    have h : rootDiagUnit Tag.F4 (a' ^ 3) = rootDiagUnit Tag.F4 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ha']
      exact conj_pow_eq_one' C₀ (by rw [← map_pow, hexpE x hx, map_one])
    intro i
    have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
    simpa using this
  let a2 : Fin 2 → Fin Tag.F4.rank → Lˣ := ![a, b]
  let gens : Fin 2 → adjointGroup Tag.F4 K := ![x₀, y₀]
  have ha2 : ∀ s, rootDiagUnit Tag.F4 (a2 s) = C₀ * φ (gens s) * C₀⁻¹ := by
    intro s
    fin_cases s
    · exact ha
    · exact hb
  have hgensE : ∀ s, gens s ∈ E₀ := by
    intro s
    fin_cases s
    · exact hPE hx₀P
    · exact hPE hy₀P
  have ha2p : ∀ s i, a2 s i ^ 3 = 1 := fun s => hexpDiag _ (hgensE s) _ (ha2 s)
  have hker : (familyKernel (τ := Tag.F4) a2).Nonempty := by
    refine ⟨α, hα, fun s => ?_⟩
    fin_cases s
    · exact haα
    · exact hbα
  set A'' : Subgroup (ModGL Tag.F4 L) := (E₀.map φ).map (MulAut.conj C₀).toMonoidHom with hA''
  have hA''mem : ∀ y ∈ A'', ∃ x ∈ E₀, y = C₀ * φ x * C₀⁻¹ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hA''C : A'' ≤ adjointGroup Tag.F4 L := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := hA''mem y hy
    exact mul_mem (mul_mem hC₀G (hφG x)) (inv_mem hC₀G)
  have hA''fin : (A'' : Set (ModGL Tag.F4 L)).Finite := by
    have : Finite (E₀.map φ) := by
      haveI : Finite ↥E₀ := inferInstance
      exact Finite.of_surjective _ (Subgroup.equivMapOfInjective E₀ φ
        ((baseChangeGL_injective ι).comp Subtype.val_injective)).surjective
    exact Set.Finite.image _ (Set.toFinite _)
  have hA''a : ∀ y ∈ A'', ∀ s, rootDiagUnit Tag.F4 (a2 s) * y = y * rootDiagUnit Tag.F4 (a2 s) := by
    intro y hy s
    obtain ⟨x, hx, rfl⟩ := hA''mem y hy
    rw [ha2 s]
    have h := hcommE _ (hgensE s) x hx
    calc C₀ * φ (gens s) * C₀⁻¹ * (C₀ * φ x * C₀⁻¹) = C₀ * φ (gens s * x) * C₀⁻¹ := by
          rw [map_mul]; group
      _ = C₀ * φ (x * gens s) * C₀⁻¹ := by rw [h]
      _ = C₀ * φ x * C₀⁻¹ * (C₀ * φ (gens s) * C₀⁻¹) := by rw [map_mul]; group
  have hA''exp : ∀ y ∈ A'', y ^ 3 = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hA''mem y hy
    refine conj_pow_eq_one' C₀ ?_
    rw [← map_pow, hexpE x hx, map_one]
  obtain ⟨z₂, hz₂, hz₂d, hz₂N⟩ :=
    SeitzExcOpenRest3.exists_conj_le_monomial_familyCentralizer_bar hℓ halg a2 hA''C hA''fin
      hA''a hA''exp
  have hw₀A'' : C₀ * φ w₀ * C₀⁻¹ ∈ A'' := ⟨φ w₀, ⟨w₀, hw₀E, rfl⟩, rfl⟩
  set n'' := z₂ * (C₀ * φ w₀ * C₀⁻¹) * z₂⁻¹ with hn''
  have hn''N : n'' ∈ monomialSubgroup Tag.F4 L := hz₂N _ hw₀A''
  have hz₂d' : ∀ s, rootDiagUnit Tag.F4 (a2 s) * z₂⁻¹ = z₂⁻¹ * rootDiagUnit Tag.F4 (a2 s) := by
    intro s
    calc rootDiagUnit Tag.F4 (a2 s) * z₂⁻¹ =
          z₂⁻¹ * (z₂ * rootDiagUnit Tag.F4 (a2 s)) * z₂⁻¹ := by group
      _ = z₂⁻¹ * (rootDiagUnit Tag.F4 (a2 s) * z₂) * z₂⁻¹ := by rw [hz₂d s]
      _ = z₂⁻¹ * rootDiagUnit Tag.F4 (a2 s) := by group
  have hn''a : ∀ s, rootDiagUnit Tag.F4 (a2 s) * n'' = n'' * rootDiagUnit Tag.F4 (a2 s) := by
    intro s
    have h1 := hA''a _ hw₀A'' s
    calc rootDiagUnit Tag.F4 (a2 s) * n'' =
          (rootDiagUnit Tag.F4 (a2 s) * z₂) * (C₀ * φ w₀ * C₀⁻¹) * z₂⁻¹ := by rw [hn'']; group
      _ = z₂ * (rootDiagUnit Tag.F4 (a2 s) * (C₀ * φ w₀ * C₀⁻¹)) * z₂⁻¹ := by
          rw [hz₂d s]; group
      _ = z₂ * (C₀ * φ w₀ * C₀⁻¹) * (rootDiagUnit Tag.F4 (a2 s) * z₂⁻¹) := by rw [h1]; group
      _ = n'' * rootDiagUnit Tag.F4 (a2 s) := by rw [hz₂d' s, hn'']; group
  have hn''p : n'' ^ 3 = 1 := conj_pow_eq_one' z₂ (hA''exp _ hw₀A'')
  obtain ⟨g'', hg'', hg''d, hg''n⟩ :=
    SeitzExcOpenRest3.exists_conj_mem_torusGroup_of_mem_monomial_familyCentralizer hmon hLp
      (hW L a2 ha2p hker) hn''N hn''a hn''p
  set C := g'' * z₂ * C₀ with hCdef
  have hCG : C ∈ adjointGroup Tag.F4 L := mul_mem (mul_mem hg'' hz₂) hC₀G
  have hfix2 : ∀ s, C * φ (gens s) * C⁻¹ = rootDiagUnit Tag.F4 (a2 s) := by
    intro s
    have e : C * φ (gens s) * C⁻¹ = g'' * (z₂ * (C₀ * φ (gens s) * C₀⁻¹) * z₂⁻¹) * g''⁻¹ := by
      rw [hCdef]
      group
    have hz₂c : z₂ * rootDiagUnit Tag.F4 (a2 s) * z₂⁻¹ = rootDiagUnit Tag.F4 (a2 s) := by
      rw [← hz₂d s, mul_inv_cancel_right]
    have hg''c : g'' * rootDiagUnit Tag.F4 (a2 s) * g''⁻¹ = rootDiagUnit Tag.F4 (a2 s) := by
      rw [← hg''d s, mul_inv_cancel_right]
    rw [e, ← ha2 s, hz₂c, hg''c]
  set S : Subgroup (adjointGroup Tag.F4 K) :=
    E₀ ⊓ (torusGroup Tag.F4 L).comap ((MulAut.conj C).toMonoidHom.comp φ) with hS
  have hgensS : ∀ s, gens s ∈ S := by
    intro s
    refine ⟨hgensE s, ?_⟩
    change C * φ (gens s) * C⁻¹ ∈ torusGroup Tag.F4 L
    rw [hfix2 s]
    exact rootDiagUnit_mem_torusGroup _
  have hw₀S : w₀ ∈ S := by
    refine ⟨hw₀E, ?_⟩
    change C * φ w₀ * C⁻¹ ∈ torusGroup Tag.F4 L
    have e : C * φ w₀ * C⁻¹ = g'' * n'' * g''⁻¹ := by
      rw [hCdef, hn'']
      group
    rw [e]
    exact hg''n
  have hES : E₀ ≤ S := by
    rw [hgen]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl | rfl)
    · exact hgensS 0
    · exact hgensS 1
    · exact hw₀S
  refine langPlaneData_of_toral hp3 hK3 hexpE (inv_mem hCG) fun x hx => ?_
  rw [inv_inv]
  exact (hES hx).2

end SeitzExcOpenRest8bAux

theorem f4NonToralRegularPlane_of_killedPlaneWeyl (hW : F4ThreeKilledPlaneWeyl) :
    F4NonToralRegularPlane := by
  intro K _ _ hK3 _ E₀ hE₀ hc _ hD
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E₀ := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) 3 (n := 2)
    (by rw [hc]; exact pow_dvd_pow 3 (by norm_num))
  set P : Subgroup (adjointGroup .F4 K) := F'.map E₀.subtype with hPdef
  have hPE : P ≤ E₀ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hPc : Nat.card P = 3 ^ 2 := by
    rw [hPdef, Subgroup.card_map_of_injective E₀.subtype_injective]
    exact hF'
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩ :=
    langToralPlane_F4_three K hK3 P (fun x hx => hE₀.2 x (hPE hx)) hPc
  let D : LangPlaneData .F4 K P := ⟨w, Fr, hFr, g0, hg0C, hg0, c, hcP⟩
  refine ⟨P, hPE, hPc, D, fun α hα hk => ?_⟩
  obtain ⟨D₀⟩ := SeitzExcOpenRest8bAux.nonempty_langPlaneData_of_kills hW hK3 hE₀ hc hPE hPc D hα hk
  exact hD.false D₀

end KilledPlane

section KilledPlaneWeyl

open CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Torality

namespace SeitzExcOpenRest8bAux

local instance kpNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def kpPosTuples : List (ℤ × ℤ × ℤ × ℤ) :=
  [(0, 0, 0, 1), (0, 0, 1, 0), (0, 0, 1, 1), (0, 1, 0, 0), (0, 1, 1, 0), (0, 1, 1, 1),
    (0, 1, 2, 0), (0, 1, 2, 1), (0, 1, 2, 2), (1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 1, 0),
    (1, 1, 1, 1), (1, 1, 2, 0), (1, 1, 2, 1), (1, 1, 2, 2), (1, 2, 2, 0), (1, 2, 2, 1),
    (1, 2, 2, 2), (1, 2, 3, 1), (1, 2, 3, 2), (1, 2, 4, 2), (1, 3, 4, 2), (2, 3, 4, 2)]

@[expose] def kpTuples : List (ℤ × ℤ × ℤ × ℤ) :=
  kpPosTuples ++ kpPosTuples.map fun t => (-t.1, -t.2.1, -t.2.2.1, -t.2.2.2)

@[expose] def kpOfCoords (t : ℤ × ℤ × ℤ × ℤ) : Fin Tag.F4.rank → ℤ := ![t.1, t.2.1, t.2.2.1, t.2.2.2]

@[expose] def kpCoords (v : Fin Tag.F4.rank → ℤ) : ℤ × ℤ × ℤ × ℤ := (v 0, v 1, v 2, v 3)

@[expose] def kpForm (x y : Fin Tag.F4.rank → ℤ) : ℤ :=
  4 * x 0 * y 0 - 2 * x 0 * y 1 - 2 * x 1 * y 0 + 4 * x 1 * y 1 - 2 * x 1 * y 2 - 2 * x 2 * y 1 +
    2 * x 2 * y 2 - x 2 * y 3 - x 3 * y 2 + 2 * x 3 * y 3

@[expose] def kpRefl (β v : Fin Tag.F4.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  fun i => v i - (2 * kpForm β v / kpForm β β) * β i

@[expose] def kpTupN (c : ℕ) : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  fun j i => ((c / 16 ^ (4 * (j : ℕ) + i) % 16 : ℕ) : ℤ) - 8

@[expose] def kpCode (T : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) : ℕ :=
  ∑ j : Fin Tag.F4.rank, ∑ i : Fin Tag.F4.rank, (T j i + 8).toNat * 16 ^ (4 * (j : ℕ) + i)

@[expose] def kpAct (T : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ) (v : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → ℤ :=
  fun i => v 0 * T 0 i + v 1 * T 1 i + v 2 * T 2 i + v 3 * T 3 i

@[expose] def kpPair (b : Fin Tag.F4.rank → ZMod 3) (v : Fin Tag.F4.rank → ℤ) : ZMod 3 :=
  b 0 * ((v 0 : ℤ) : ZMod 3) + b 1 * ((v 1 : ℤ) : ZMod 3) + b 2 * ((v 2 : ℤ) : ZMod 3) +
    b 3 * ((v 3 : ℤ) : ZMod 3)

@[expose] def kpHt (v : Fin Tag.F4.rank → ℤ) : ℤ := v 0 + v 1 + v 2 + v 3

@[expose] def kpVec (a b c d : ZMod 3) : Fin Tag.F4.rank → ZMod 3 := ![a, b, c, d]

@[expose] def kpIdCode : ℕ := 10991186110097950857

@[expose] def kpCodesOne : List ℕ :=
  [10991186110097950857, 8685360693070301321, 11063241505146177673, 9910302408890157193,
    8613301999554300041, 9766188320325929097, 10991186178815330457, 8685360761787680921,
    11063243772819704473, 9910339859862039193, 8613304267227826841, 9766225771297811097,
    11067745036054071449, 9914805939798050969, 11139802630058445465, 11139785037872409241,
    9914804840286423705, 11067726344356407961, 8608798399926929561, 9761684720698558617,
    8536741905367075481, 8536724313181039257, 9761683621186931353, 8608779708229266073,
    11067747303727598249, 9914843390769932969, 11139802698775825065, 11139785106589788841,
    9914842291258305705, 11067728612029934761, 8608800667600456361, 9761722171670440617,
    8536741974084455081, 8536724381898418857, 9761721072158813353, 8608781975902792873,
    9910301240659053225, 11063222744729037481, 9766187152094825129, 8613283239137159849,
    10991166250169183401, 8685340833141533865, 9910338691630935225, 11063225012402564281,
    9766224603066707129, 8613285506810686649, 10991166318886563001, 8685340901858913465]

@[expose] def kpCodesTwo : List ℕ :=
  [10991186110097950857, 10991186110098007126, 8685360693070357590, 11063241505146233942,
    9910302408890213462, 8613301999554356310, 9766188320325985366, 10991186110097941591,
    8685360693070292055, 11063241505146168407, 9910302408890147927, 8613301999554290775,
    9766188320325919831, 10991186110098016391, 8685360693070366855, 11063241505146243207,
    9910302408890222727, 8613301999554365575, 9766188320325994631, 10991186109490769081,
    8685360692463119545, 11063241504538995897, 9910302408282975417, 8613301998947118265,
    9766188319718747321, 8685360693070301321, 11063241505146177673, 9910302408890157193,
    8613301999554300041, 9766188320325929097, 10991186109490769082, 8685360692463119546,
    11063241504538995898, 9910302408282975418, 8613301998947118266, 9766188319718747322]

@[expose] def kpCodesThree : List ℕ :=
  [10991186110097950857, 10991186110097941591, 8685360693070292055, 10991186178815321191,
    8685360761787671655, 11140084100774847575, 11140066509125674071, 11144587700401169511,
    11144570108751996007, 8536460430425023575, 8536442838775850071, 8531956899516081255,
    8531939307866907751, 10991166246480405591, 8685340829452756055, 10991166246480405607,
    8685340829452756071, 11140086441460590200, 11140104033109771896, 11144589972369532536,
    11144607564018714232, 8536462771110766200, 8536480362759947896, 8531959171484444280,
    8531976763133625976, 11144570108751996536, 11144587700401178232, 11140066509125674616,
    11140084100774856312, 8531939307866908280, 8531956899516089976, 8536442838775850616,
    8536460430425032312, 10991206042432866441, 8685380625405216905, 10991206042432866457,
    8685380625405216921, 11144607564018714761, 11144589972369541257, 11140104033109772441,
    11140086441460598937, 8531976763133626505, 8531959171484453001, 8536480362759948441,
    8536462771110774937, 8685360693070301321, 10991186178815330457, 8685360761787680921]

theorem kpClosedOne : ∀ c ∈ kpCodesOne, ∀ t ∈ kpTuples, kpPair (kpVec 1 0 0 0) (kpOfCoords t) = 0 →
    kpTupN (kpCode fun j => kpRefl (kpOfCoords t) (kpTupN c j)) =
        (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∧
      kpCode (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∈ kpCodesOne := by
  decide +kernel

theorem kpOmegaOne : ∀ a b c d : ZMod 3, ∀ e ∈ kpCodesOne,
    (∀ j, kpPair (kpVec a b c d) (kpTupN e j) = kpVec a b c d j) →
    (∃ t ∈ kpTuples, kpPair (kpVec 1 0 0 0) (kpOfCoords t) = 0 ∧
      kpPair (kpVec a b c d) (kpOfCoords t) = 0) →
    (∀ t ∈ kpPosTuples, kpPair (kpVec 1 0 0 0) (kpOfCoords t) = 0 →
      kpPair (kpVec a b c d) (kpOfCoords t) = 0 → 0 < kpHt (kpAct (kpTupN e) (kpOfCoords t))) →
    e = kpIdCode := by
  decide +kernel

theorem kpClosedTwo : ∀ c ∈ kpCodesTwo, ∀ t ∈ kpTuples, kpPair (kpVec 0 1 0 0) (kpOfCoords t) = 0 →
    kpTupN (kpCode fun j => kpRefl (kpOfCoords t) (kpTupN c j)) =
        (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∧
      kpCode (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∈ kpCodesTwo := by
  decide +kernel

theorem kpOmegaTwo : ∀ a b c d : ZMod 3, ∀ e ∈ kpCodesTwo,
    (∀ j, kpPair (kpVec a b c d) (kpTupN e j) = kpVec a b c d j) →
    (∃ t ∈ kpTuples, kpPair (kpVec 0 1 0 0) (kpOfCoords t) = 0 ∧
      kpPair (kpVec a b c d) (kpOfCoords t) = 0) →
    (∀ t ∈ kpPosTuples, kpPair (kpVec 0 1 0 0) (kpOfCoords t) = 0 →
      kpPair (kpVec a b c d) (kpOfCoords t) = 0 → 0 < kpHt (kpAct (kpTupN e) (kpOfCoords t))) →
    e = kpIdCode := by
  decide +kernel

theorem kpClosedThree : ∀ c ∈ kpCodesThree, ∀ t ∈ kpTuples, kpPair (kpVec 1 0 1 0) (kpOfCoords t) = 0 →
    kpTupN (kpCode fun j => kpRefl (kpOfCoords t) (kpTupN c j)) =
        (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∧
      kpCode (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∈ kpCodesThree := by
  decide +kernel

theorem kpOmegaThree : ∀ a b c d : ZMod 3, ∀ e ∈ kpCodesThree,
    (∀ j, kpPair (kpVec a b c d) (kpTupN e j) = kpVec a b c d j) →
    (∃ t ∈ kpTuples, kpPair (kpVec 1 0 1 0) (kpOfCoords t) = 0 ∧
      kpPair (kpVec a b c d) (kpOfCoords t) = 0) →
    (∀ t ∈ kpPosTuples, kpPair (kpVec 1 0 1 0) (kpOfCoords t) = 0 →
      kpPair (kpVec a b c d) (kpOfCoords t) = 0 → 0 < kpHt (kpAct (kpTupN e) (kpOfCoords t))) →
    e = kpIdCode := by
  decide +kernel

theorem kpTuples_isRoot : ∀ t ∈ kpTuples, kpOfCoords t ∈ rootFinset .F4 := by decide +kernel

theorem kpCoords_mem : ∀ v ∈ rootFinset .F4, kpCoords v ∈ kpTuples := by decide +kernel

theorem kpPosTuples_sub : ∀ t ∈ kpPosTuples, t ∈ kpTuples ∧ 0 < kpHt (kpOfCoords t) := by
  decide +kernel

theorem kpIdCode_spec : ∀ j : Fin Tag.F4.rank, kpTupN kpIdCode j = Pi.single j 1 := by decide

theorem kpOfCoords_kpCoords (v : Fin Tag.F4.rank → ℤ) : kpOfCoords (kpCoords v) = v := by
  funext i
  fin_cases i <;> rfl

theorem kp_sum_four {M : Type*} [AddCommMonoid M] (f : Fin Tag.F4.rank → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

@[expose] def kpB : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  ![![4, -2, 0, 0], ![-2, 4, -2, 0], ![0, -2, 2, -1], ![0, 0, -1, 2]]

theorem kp_symCartan (i j : Fin Tag.F4.rank) : Tag.F4.symmetrizedCartan i j = kpB i j := by
  fin_cases i <;> fin_cases j <;> rfl

section Bridge


theorem kp_isRoot_iff {v : Fin Tag.F4.rank → ℤ} : IsRoot .F4 v ↔ kpCoords v ∈ kpTuples := by
  rw [← mem_rootFinset]
  refine ⟨kpCoords_mem v, fun h => ?_⟩
  have := kpTuples_isRoot _ h
  rwa [kpOfCoords_kpCoords] at this

theorem kp_triPairing (b : Fin Tag.F4.rank → ZMod 3) (v : Fin Tag.F4.rank → ℤ) :
    triPairing b v = kpPair b v :=
  kp_sum_four _

theorem kp_height (v : Fin Tag.F4.rank → ℤ) : height v = kpHt v :=
  kp_sum_four _

theorem kp_iform (x y : Fin Tag.F4.rank → ℤ) : iform x y = kpForm x y := by
  simp only [iform, kp_sum_four, kp_symCartan]
  simp [kpB, kpForm]
  ring

theorem kp_rootReflection_smul {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β)
    (v : Fin Tag.F4.rank → ℤ) : rootReflection β • v = kpRefl β v := by
  rw [rootReflection_smul hβ]
  funext i
  simp [kpRefl, corootPair, kp_iform]

theorem kp_smul_eq {w : WeylGroup Tag.F4} {T : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ}
    (hT : ∀ j, w • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = T j) (v : Fin Tag.F4.rank → ℤ) :
    w • v = kpAct T v := by
  have hv : v = ∑ j, v j • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : w • v = ∑ j, v j • T j := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, hT]
  rw [h1]
  funext i
  rw [Finset.sum_apply, kp_sum_four]
  simp [kpAct]

end Bridge

@[expose] def kpPairChar (k l : Fin Tag.F4.rank → ZMod 3) :
    Multiplicative (Fin Tag.F4.rank → ℤ) →* Z3 × Z3 :=
  (triChar k).prod (triChar l)

@[expose] def KpClosed (r : Fin Tag.F4.rank → ZMod 3) (L : List ℕ) : Prop :=
  ∀ c ∈ L, ∀ t ∈ kpTuples, kpPair r (kpOfCoords t) = 0 →
    kpTupN (kpCode fun j => kpRefl (kpOfCoords t) (kpTupN c j)) =
        (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∧
      kpCode (fun j => kpRefl (kpOfCoords t) (kpTupN c j)) ∈ L

@[expose] def KpOmega (r : Fin Tag.F4.rank → ZMod 3) (L : List ℕ) : Prop :=
  ∀ a b c d : ZMod 3, ∀ e ∈ L,
    (∀ j, kpPair (kpVec a b c d) (kpTupN e j) = kpVec a b c d j) →
    (∃ t ∈ kpTuples, kpPair r (kpOfCoords t) = 0 ∧ kpPair (kpVec a b c d) (kpOfCoords t) = 0) →
    (∀ t ∈ kpPosTuples, kpPair r (kpOfCoords t) = 0 →
      kpPair (kpVec a b c d) (kpOfCoords t) = 0 → 0 < kpHt (kpAct (kpTupN e) (kpOfCoords t))) →
    e = kpIdCode

theorem kpVec_eta (l : Fin Tag.F4.rank → ZMod 3) : kpVec (l 0) (l 1) (l 2) (l 3) = l := by
  funext i
  fin_cases i <;> rfl

theorem kpPairChar_apply (k l : Fin Tag.F4.rank → ZMod 3) (v : Fin Tag.F4.rank → ℤ) :
    kpPairChar k l (Multiplicative.ofAdd v) = (Z3.ofAdd (triPairing k v), Z3.ofAdd (triPairing l v)) :=
  rfl

section Glue


theorem mem_kernelRoots_kpPairChar {k l : Fin Tag.F4.rank → ZMod 3} {α : Fin Tag.F4.rank → ℤ} :
    α ∈ kernelRoots (kpPairChar k l) ↔ IsRoot .F4 α ∧ triPairing k α = 0 ∧ triPairing l α = 0 := by
  refine Iff.trans Iff.rfl (and_congr_right fun _ => ?_)
  rw [kpPairChar_apply, Prod.mk_eq_one, Z3.ofAdd_eq_one, Z3.ofAdd_eq_one]

theorem kpPairChar_stab {k l : Fin Tag.F4.rank → ZMod 3} {w : WeylGroup Tag.F4}
    (hw : w ∈ charStabilizer (kpPairChar k l)) (v : Fin Tag.F4.rank → ℤ) :
    triPairing k (w • v) = triPairing k v ∧ triPairing l (w • v) = triPairing l v := by
  have h := hw v
  rw [kpPairChar_apply, kpPairChar_apply, Prod.mk.injEq, Z3.ofAdd_eq_ofAdd_iff,
    Z3.ofAdd_eq_ofAdd_iff] at h
  exact h

theorem kp_exists_code {r : Fin Tag.F4.rank → ZMod 3} {L : List ℕ} (hid : kpIdCode ∈ L)
    (hcl : KpClosed r L) {y : WeylGroup Tag.F4} (hy : y ∈ kernelWeylGroup (triChar r)) :
    ∃ c ∈ L, ∀ j, kpTupN c j = y • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) := by
  have step : ∀ g ∈ {r' | ∃ (u : WeylGroup Tag.F4) (i : Fin Tag.F4.rank),
      u • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ kernelRoots (triChar r) ∧
        r' = u * simple Tag.F4 i * u⁻¹}, ∀ y : WeylGroup Tag.F4,
      (∃ c ∈ L, ∀ j, kpTupN c j = y • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) →
      ∃ c ∈ L, ∀ j, kpTupN c j = (g * y) • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) := by
    rintro _ ⟨u, i, hu, rfl⟩ y ⟨c, hc, hcy⟩
    set β := u • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) with hβdef
    obtain ⟨hβ, hβr⟩ := mem_kernelRoots_triChar.1 hu
    have hrefl : u * simple Tag.F4 i * u⁻¹ = rootReflection β := (rootReflection_eq_conj rfl).symm
    have ht := kp_isRoot_iff.1 hβ
    have hco := kpOfCoords_kpCoords β
    obtain ⟨h1, h2⟩ := hcl c hc (kpCoords β) ht (by rw [hco, ← kp_triPairing]; exact hβr)
    rw [hco] at h1 h2
    refine ⟨_, h2, fun j => ?_⟩
    rw [h1]
    show kpRefl β (kpTupN c j) = _
    rw [hcy, mul_smul, hrefl, kp_rootReflection_smul hβ]
  induction hy using Subgroup.closure_induction_left with
  | one => exact ⟨kpIdCode, hid, fun j => by rw [kpIdCode_spec, one_smul]⟩
  | mul_left g hg y _ ih => exact step g hg y ih
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨u, i, hu, rfl⟩ := hg
    have hinv : (u * simple Tag.F4 i * u⁻¹)⁻¹ = u * simple Tag.F4 i * u⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, (coxeterSystem Tag.F4).inv_simple, mul_assoc]
    rw [hinv]
    exact step _ ⟨u, i, hu, rfl⟩ y ih


theorem kp_kernelPosStabilizer_eq_bot {r : Fin Tag.F4.rank → ZMod 3} {L : List ℕ}
    (hid : kpIdCode ∈ L) (hcl : KpClosed r L) (hom : KpOmega r L) (l : Fin Tag.F4.rank → ZMod 3)
    (hne : (kernelRoots (kpPairChar r l)).Nonempty) :
    kernelPosStabilizer (kpPairChar r l) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun (w : WeylGroup Tag.F4) hw => ?_
  have hstab := kpPairChar_stab hw.1
  have hwr : w ∈ kernelWeylGroup (triChar r) := by
    rw [← charStabilizer_eq_kernelWeylGroup_F4_three]
    intro v
    rw [triChar_apply, triChar_apply, (hstab v).1]
  obtain ⟨c, hc, hcw⟩ := kp_exists_code hid hcl hwr
  have hact : ∀ v, w • v = kpAct (kpTupN c) v := kp_smul_eq fun j => (hcw j).symm
  have hcI := hom (l 0) (l 1) (l 2) (l 3) c hc ?_ ?_ ?_
  · refine ext_single fun i => ?_
    rw [one_smul, ← hcw i, hcI, kpIdCode_spec]
  · intro j
    rw [kpVec_eta, hcw, ← kp_triPairing, (hstab _).2]
    have := triPairing_zsmul_single l 1 j
    rwa [one_smul, Int.cast_one, mul_one] at this
  · obtain ⟨α, hα⟩ := hne
    obtain ⟨hαr, hαk, hαl⟩ := mem_kernelRoots_kpPairChar.1 hα
    refine ⟨kpCoords α, kp_isRoot_iff.1 hαr, ?_, ?_⟩
    · rw [kpOfCoords_kpCoords, ← kp_triPairing]; exact hαk
    · rw [kpOfCoords_kpCoords, kpVec_eta, ← kp_triPairing]; exact hαl
  · intro t ht h1 h2
    obtain ⟨htT, hth⟩ := kpPosTuples_sub t ht
    rw [kpVec_eta] at h2
    have hβ : kpOfCoords t ∈ posRoots (kernelRoots (kpPairChar r l)) := by
      refine ⟨mem_kernelRoots_kpPairChar.2 ⟨?_, ?_, ?_⟩, ?_⟩
      · exact mem_rootFinset.1 (kpTuples_isRoot t htT)
      · rw [kp_triPairing]; exact h1
      · rw [kp_triPairing]; exact h2
      · rw [kp_height]; exact hth
    have hwβ : w • kpOfCoords t ∈ posRoots (kernelRoots (kpPairChar r l)) := by
      rw [← hw.2]
      exact ⟨_, hβ, rfl⟩
    rw [← hact, ← kp_height]
    exact hwβ.2

end Glue

section Final


theorem kp_charStabilizer_eq {r : Fin Tag.F4.rank → ZMod 3} {L : List ℕ} (hid : kpIdCode ∈ L)
    (hcl : KpClosed r L) (hom : KpOmega r L) (l : Fin Tag.F4.rank → ZMod 3)
    (hne : (kernelRoots (kpPairChar r l)).Nonempty) :
    charStabilizer (kpPairChar r l) = kernelWeylGroup (kpPairChar r l) := by
  refine charStabilizer_eq_of_card_le_one (le_trans card_quotient_le_card_kernelPosStabilizer ?_)
  rw [kp_kernelPosStabilizer_eq_bot hid hcl hom l hne, Subgroup.card_bot]

theorem kp_triPairing_transport (l : Fin Tag.F4.rank → ZMod 3) (t : WeylGroup Tag.F4)
    (u : Fin Tag.F4.rank → ℤ) :
    triPairing (fun j => triPairing l (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))) u =
      triPairing l (t • u) := by
  have hu : u = ∑ j, u j • (Pi.single j 1 : Fin Tag.F4.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  let f : (Fin Tag.F4.rank → ℤ) →+ ZMod 3 :=
    { toFun := fun v => triPairing l v
      map_zero' := triPairing_zero l
      map_add' := triPairing_add l }
  have hfv : ∀ v, f v = triPairing l v := fun v => rfl
  have key : ∀ (n : ℤ) (v : Fin Tag.F4.rank → ℤ),
      triPairing l (n • v) = (n : ZMod 3) * triPairing l v := by
    intro n v
    simp only [triPairing, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc triPairing (fun j => triPairing l (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))) u
      = ∑ j, triPairing l (t • (u j • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm, key, mul_comm]
    _ = f (∑ j, t • (u j • (Pi.single j 1 : Fin Tag.F4.rank → ℤ))) := by
        rw [map_sum]
        rfl
    _ = triPairing l (t • u) := by
        rw [hfv, ← Finset.smul_sum, ← hu]

theorem kp_isCharConj {k k' l : Fin Tag.F4.rank → ZMod 3} {t : WeylGroup Tag.F4}
    (h : IsCharConj (triChar k') (triChar k) t) :
    IsCharConj (kpPairChar k' fun j => triPairing l (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)))
      (kpPairChar k l) t := by
  intro v
  rw [kpPairChar_apply, kpPairChar_apply, kp_triPairing_transport, smul_inv_smul]
  have h0 := h v
  rw [triChar_apply, triChar_apply] at h0
  rw [h0]

theorem kp_vec3_one : vec3 (τ := Tag.F4) (f4ThreeReps.getD 1 []) = kpVec 1 0 0 0 := by
  funext i; fin_cases i <;> rfl

theorem kp_vec3_two : vec3 (τ := Tag.F4) (f4ThreeReps.getD 2 []) = kpVec 0 1 0 0 := by
  funext i; fin_cases i <;> rfl

theorem kp_vec3_three : vec3 (τ := Tag.F4) (f4ThreeReps.getD 3 []) = kpVec 1 0 1 0 := by
  funext i; fin_cases i <;> rfl

theorem kp_vec3_zero : vec3 (τ := Tag.F4) (f4ThreeReps.getD 0 []) = 0 := by
  funext i; fin_cases i <;> rfl

theorem kp_charStabilizer_le (k l : Fin Tag.F4.rank → ZMod 3)
    (hne : (kernelRoots (kpPairChar k l)).Nonempty) :
    charStabilizer (kpPairChar k l) ≤ kernelWeylGroup (kpPairChar k l) := by
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 f4ThreeOrbit_check (triChar k)
  have hc := kp_isCharConj (l := l) ht
  rw [charStabilizer_eq_map hc, kernelWeylGroup_eq_map hc]
  refine Subgroup.map_mono ?_
  set l' : Fin Tag.F4.rank → ZMod 3 :=
    fun j => triPairing l (t • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) with hl'
  have hne' : (kernelRoots (kpPairChar (vec3 (τ := Tag.F4) (f4ThreeReps.getD ρ [])) l')).Nonempty := by
    obtain ⟨α, hα⟩ := hne
    exact ⟨t⁻¹ • α, (kernelRoots_iff_of_isCharConj hc).1 hα⟩
  have h4 : f4ThreeReps.length = 4 := rfl
  rw [h4] at hρ
  interval_cases ρ
  ·
    rw [kp_vec3_zero] at hne' ⊢
    have hker : ∀ x, kpPairChar 0 l' x = 1 ↔ triChar l' x = 1 := by
      intro x
      change (Z3.ofAdd (triPairing 0 (Multiplicative.toAdd x)), triChar l' x) = 1 ↔ _
      have h0 : triPairing (0 : Fin Tag.F4.rank → ZMod 3) (Multiplicative.toAdd x) = 0 := by
        simp [triPairing]
      rw [h0, Z3.ofAdd_zero, Prod.mk_eq_one]
      exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
    rw [charStabilizer_congr_ker hker, kernelWeylGroup_congr_ker hker,
      charStabilizer_eq_kernelWeylGroup_F4_three]
  · rw [kp_vec3_one] at hne' ⊢
    exact (kp_charStabilizer_eq (by decide) kpClosedOne kpOmegaOne l' hne').le
  · rw [kp_vec3_two] at hne' ⊢
    exact (kp_charStabilizer_eq (by decide) kpClosedTwo kpOmegaTwo l' hne').le
  · rw [kp_vec3_three] at hne' ⊢
    exact (kp_charStabilizer_eq (by decide) kpClosedThree kpOmegaThree l' hne').le

theorem kp_familyStab_le (L : Type) [Field L] (a : Fin 2 → Fin Tag.F4.rank → Lˣ)
    (ha : ∀ (s : Fin 2) (i : Fin Tag.F4.rank), a s i ^ 3 = 1)
    (hker : (familyKernel (τ := Tag.F4) a).Nonempty) (w : WeylGroup Tag.F4)
    (hw : ∀ s, w ∈ rootCharStabilizer (a s)) : w ∈ kernelWeylGroup (familyChar a) := by
  obtain ⟨χ₀, h₀⟩ :=
    exists_triChar_ker_eq (rootCharHom3 (a 0)) (rootCharHom3_pow_three (a 0) (ha 0))
  obtain ⟨χ₁, h₁⟩ :=
    exists_triChar_ker_eq (rootCharHom3 (a 1)) (rootCharHom3_pow_three (a 1) (ha 1))
  have hk0 := eq_triChar χ₀
  have hl1 := eq_triChar χ₁
  set k : Fin Tag.F4.rank → ZMod 3 := fun j => Z3.toAdd (χ₀ (Multiplicative.ofAdd (Pi.single j 1)))
  set l : Fin Tag.F4.rank → ZMod 3 := fun j => Z3.toAdd (χ₁ (Multiplicative.ofAdd (Pi.single j 1)))
  have hkerx : ∀ x, familyChar a x = 1 ↔ kpPairChar k l x = 1 := by
    intro x
    have e : familyChar a x = 1 ↔ rootCharHom3 (a 0) x = 1 ∧ rootCharHom3 (a 1) x = 1 := by
      rw [funext_iff, Fin.forall_fin_two]
      exact Iff.rfl
    rw [e, h₀, h₁, hk0, hl1]
    change _ ↔ ((triChar k) x, (triChar l) x) = 1
    rw [Prod.mk_eq_one]
  have hW : w ∈ charStabilizer (familyChar a) := by
    intro v
    funext s
    exact hw s v
  rw [charStabilizer_congr_ker hkerx] at hW
  have hne : (kernelRoots (kpPairChar k l)).Nonempty := by
    rw [← kernelRoots_congr_ker hkerx, kernelRoots_familyChar]
    exact hker
  rw [kernelWeylGroup_congr_ker hkerx]
  exact kp_charStabilizer_le k l hne hW

end Final


end SeitzExcOpenRest8bAux


theorem f4ThreeKilledPlaneWeyl_holds : F4ThreeKilledPlaneWeyl :=
  fun L _ a ha hker w hw => SeitzExcOpenRest8bAux.kp_familyStab_le L a ha hker w hw

end KilledPlaneWeyl

section Residual


@[expose] def E7NonToralTwoNormalizes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 → ThreeScope LieTypeIndex.E7 K →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      IsEmpty (LangPlaneData .E7 K E₀) → NormalizesRGroup (ringChar K) E₀

@[expose] def E8NonToralNormalizes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ 3 ∣ Nat.card K → ThreeScope LieTypeIndex.E8 K →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E₀ → Nat.card E₀ = 3 ^ 3 →
      IsEmpty (LangPlaneData .E8 K E₀) → NormalizesRGroup (ringChar K) E₀

@[expose] def SeitzNonToralResidual8 : Prop :=
  E7NonToralTwoNormalizes ∧ E8NonToralNormalizes

end Residual

section Reduction


theorem threeNonToralCubeRest_F4_of_regularPlane (h1 : F4NonToralRegularPlane) :
    ThreeNonToralCubeRest .F4 LieTypeIndex.F4 := by
  intro K _ _ hK3 hs E₀ hE₀ hc hN hD
  obtain ⟨P, hPE, hPc, D, hreg⟩ := h1 K hK3 hs E₀ hE₀ hc hN hD
  have hK : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
  rcases hK with h | h
  · exact hyperGen_F4_of_regularPlane h (card_ne_four_of_threeScope_F4 hs) hE₀ hc hPE hPc D hreg
  · exact hyperGen_F4_two_of_regularPlane h (three_le_card_of_threeScope_F4 hs) hE₀ hc hPE hPc D
      hreg

theorem threeNonToralCubeRest_F4_of_killedPlaneWeyl (hW : F4ThreeKilledPlaneWeyl) :
    ThreeNonToralCubeRest .F4 LieTypeIndex.F4 :=
  threeNonToralCubeRest_F4_of_regularPlane (f4NonToralRegularPlane_of_killedPlaneWeyl hW)

theorem threeNonToralCubeRest_F4_holds : ThreeNonToralCubeRest .F4 LieTypeIndex.F4 :=
  threeNonToralCubeRest_F4_of_killedPlaneWeyl f4ThreeKilledPlaneWeyl_holds

theorem not_kills_of_le_nonToral_F4 {K : Type} [Field K] [Finite K] (hK3 : ¬ 3 ∣ Nat.card K)
    {E₀ : Subgroup (adjointGroup .F4 K)} (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3)
    (hD : IsEmpty (LangPlaneData .F4 K E₀)) {P : Subgroup (adjointGroup .F4 K)} (hPE : P ≤ E₀)
    (hPc : Nat.card P = 3 ^ 2) (D : LangPlaneData .F4 K P) :
    ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → ¬ D.Kills α := by
  intro α hα hk
  obtain ⟨D₀⟩ := SeitzExcOpenRest8bAux.nonempty_langPlaneData_of_kills f4ThreeKilledPlaneWeyl_holds
    hK3 hE₀ hc hPE hPc D hα hk
  exact hD.false D₀

theorem e7NonToralTwoRest_of_normalizes (h : E7NonToralTwoNormalizes) :
    SeitzExcOpenRest5.E7NonToralTwoRest :=
  fun K _ _ hK hs E₀ hE₀ hc hN hD => (hN (h K hK hs E₀ hE₀ hc hD)).elim

theorem threeNonToralCubeRest_E8_of_normalizes (h : E8NonToralNormalizes) :
    ThreeNonToralCubeRest .E8 LieTypeIndex.E8 :=
  fun K _ _ hK hs E₀ hE₀ hc hN hD => (hN (h K hK hs E₀ hE₀ hc hD)).elim

theorem seitzNonToral_of_residual8 (h : SeitzNonToralResidual8) :
    ThreeNonToralCubeRest .F4 LieTypeIndex.F4 ∧ SeitzExcOpenRest5.E7NonToralTwoRest ∧
      ThreeNonToralCubeRest .E8 LieTypeIndex.E8 :=
  ⟨threeNonToralCubeRest_F4_holds, e7NonToralTwoRest_of_normalizes h.1,
    threeNonToralCubeRest_E8_of_normalizes h.2⟩

theorem seitzThreeResidual6_of_residual8 (h : SeitzNonToralResidual8)
    (hE6 : SeitzGoodInnerExcThreeE6) (hTw : SeitzGoodInnerExcThreeTwE6)
    (hE7 : SeitzExcOpenRest6.E7ToralNegCRest) (hE8 : SeitzExcOpenRest6.E8ToralNegTwistRest) :
    SeitzExcOpenRest6.SeitzThreeResidual6 :=
  ⟨threeNonToralCubeRest_F4_holds, hE6, hTw,
    ⟨hE7, e7NonToralTwoRest_of_normalizes h.1⟩, ⟨hE8, threeNonToralCubeRest_E8_of_normalizes h.2⟩⟩

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
