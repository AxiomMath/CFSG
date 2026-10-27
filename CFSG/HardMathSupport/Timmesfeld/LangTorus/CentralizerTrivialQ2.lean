module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PairFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallPerfect
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.F2WordsCert
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialQ3Comp
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.UntwistOuter
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.SimplyLacedCover PairFrame
open scoped commutatorElement
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Core

variable {τ : Tag} {L : Type} [Field L]

theorem canonicalRep_conj_pinnedX_two [CharP L 2] (w : WeylGroup τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (c : L) :
    canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c * (canonicalRep (coxeterSystem τ) L w)⁻¹ =
      pinnedX τ L (w • γ) c := by
  obtain ⟨ε, hε, hεc⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [hεc, hε1, one_mul]

theorem commute_conj_aux {G : Type*} [Group G] {z P : G} (n : G) (h : z * P = P * z) :
    (n⁻¹ * z * n) * (n⁻¹ * P * n) = (n⁻¹ * P * n) * (n⁻¹ * z * n) := by
  calc (n⁻¹ * z * n) * (n⁻¹ * P * n) = n⁻¹ * (z * P) * n := by group
    _ = n⁻¹ * (P * z) * n := by rw [h]
    _ = (n⁻¹ * P * n) * (n⁻¹ * z * n) := by group

theorem core_two_of_tableCheck [CharP L 2] (hsl : ∀ i, τ.symmetrizer i i = 1) (hinj : PairInjective τ)
    (hcheck : tableCheck τ = true)
    {j k : Fin τ.rank} (hjk : iform (Pi.single j 1 : Fin τ.rank → ℤ) (Pi.single k 1) = -1)
    (hcert : ∀ z : Module.End L (RootModule τ L), Commute z (xOp τ L j 1) →
      Commute z (yOp τ L j 1) → Commute z (xOp τ L k 1) → Commute z (yOp τ L k 1) →
      ∀ c : L, Commute z (xOp τ L j c))
    (z : ModGL τ L) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hab : iform α β = -1)
    (h1 : z * pinnedX τ L α 1 = pinnedX τ L α 1 * z)
    (h2 : z * pinnedX τ L (-α) 1 = pinnedX τ L (-α) 1 * z)
    (h3 : z * pinnedX τ L β 1 = pinnedX τ L β 1 * z)
    (h4 : z * pinnedX τ L (-β) 1 = pinnedX τ L (-β) 1 * z) (c : L) :
    z * pinnedX τ L α c = pinnedX τ L α c * z := by
  have hj := isRoot_single τ j
  have hk := isRoot_single τ k
  have hne : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ Pi.single k 1 := fun e => by
    rw [e, iform_self_eq_two hsl hk] at hjk
    exact absurd hjk (by decide)
  have hne' : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ -Pi.single k 1 := fun e => by
    rw [e, SimplyLacedCover.iform_neg_left, iform_self_eq_two hsl hk] at hjk
    exact absurd hjk (by decide)
  have hne₂ : α ≠ β := fun e => by
    rw [e, iform_self_eq_two hsl hβ] at hab
    exact absurd hab (by decide)
  have hne₂' : α ≠ -β := fun e => by
    rw [e, SimplyLacedCover.iform_neg_left, iform_self_eq_two hsl hβ] at hab
    exact absurd hab (by decide)
  obtain ⟨w, hwj, hwk⟩ := exists_weyl_pair_iform_of_tableCheck hcheck hinj hj hk hα hβ hne hne' hne₂ hne₂'
    (hjk.trans hab.symm)
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hconj : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → ∀ c : L,
      n * pinnedX τ L γ c * n⁻¹ = pinnedX τ L (w • γ) c := fun hγ c =>
    canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero w hγ c
  have hback : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → ∀ c : L,
      pinnedX τ L γ c = n⁻¹ * pinnedX τ L (w • γ) c * n := fun hγ c => by
    rw [← hconj hγ c]; group
  have hcomm : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → ∀ {δ : Fin τ.rank → ℤ}, w • γ = δ →
      z * pinnedX τ L δ 1 = pinnedX τ L δ 1 * z →
      (n⁻¹ * z * n) * pinnedX τ L γ 1 = pinnedX τ L γ 1 * (n⁻¹ * z * n) := by
    intro γ hγ δ hδ h
    rw [hback hγ 1, hδ]
    have hx := congrArg (fun x => n⁻¹ * x * n) h
    show (n⁻¹ * z * n) * (n⁻¹ * pinnedX τ L δ 1 * n) =
      (n⁻¹ * pinnedX τ L δ 1 * n) * (n⁻¹ * z * n)
    simpa only [mul_assoc, mul_inv_cancel_left] using hx
  have hnj : w • (-Pi.single j 1 : Fin τ.rank → ℤ) = -α := by rw [smul_neg, hwj]
  have hnk : w • (-Pi.single k 1 : Fin τ.rank → ℤ) = -β := by rw [smul_neg, hwk]
  have c1 := hcomm hj hwj h1
  have c2 := hcomm (IsRoot.neg hj) hnj h2
  have c3 := hcomm hk hwk h3
  have c4 := hcomm (IsRoot.neg hk) hnk h4
  rw [pinnedX_single] at c1 c3
  rw [pinnedX_neg_single] at c2 c4
  have e : ∀ (a b : ModGL τ L), a * b = b * a →
      Commute (a : Module.End L (RootModule τ L)) (b : Module.End L (RootModule τ L)) :=
    fun a b h => by
      have h' : (a : Module.End L (RootModule τ L)) * (b : Module.End L (RootModule τ L)) =
          (b : Module.End L (RootModule τ L)) * (a : Module.End L (RootModule τ L)) := by
        have := congrArg (fun m : ModGL τ L => (m : Module.End L (RootModule τ L))) h
        simpa only [Units.val_mul] using this
      exact h'
  have hx := hcert ((n⁻¹ * z * n : ModGL τ L) : Module.End L (RootModule τ L))
    (e _ _ c1) (e _ _ c2) (e _ _ c3) (e _ _ c4) c
  have hx' : (n⁻¹ * z * n) * xUnit τ L j c = xUnit τ L j c * (n⁻¹ * z * n) := Units.ext hx.eq
  rw [← pinnedX_single, hback hj c, hwj] at hx'
  calc z * pinnedX τ L α c = n * ((n⁻¹ * z * n) * (n⁻¹ * pinnedX τ L α c * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * pinnedX τ L α c * n) * (n⁻¹ * z * n)) * n⁻¹ := by rw [hx']
    _ = pinnedX τ L α c * z := by group

theorem symmetrizer_diag_one (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : ∀ i, τ.symmetrizer i i = 1 := by
  rcases hτ with rfl | rfl | rfl <;> intro i <;> simp [Tag.symmetrizer]

theorem core_two_tag_of_tableCheck [CharP L 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hcheck : tableCheck τ = true) (z : ModGL τ L) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hab : iform α β = -1)
    (h1 : z * pinnedX τ L α 1 = pinnedX τ L α 1 * z)
    (h2 : z * pinnedX τ L (-α) 1 = pinnedX τ L (-α) 1 * z)
    (h3 : z * pinnedX τ L β 1 = pinnedX τ L β 1 * z)
    (h4 : z * pinnedX τ L (-β) 1 = pinnedX τ L (-β) 1 * z) (c : L) :
    z * pinnedX τ L α c = pinnedX τ L α c * z := by
  have h2L : (2 : L) = 0 := CharTwo.two_eq_zero
  rcases hτ with rfl | rfl | rfl
  · exact core_two_of_tableCheck (by intro i; simp [Tag.symmetrizer])
      (pairInjective_of_exceptional (Or.inl rfl)) hcheck
      (j := ⟨0, by decide⟩) (k := ⟨2, by decide⟩) (by decide +kernel)
      (fun z a b c d e => (F2Words.commute_xOp_yOp_E6 h2L z a b c d e).1) z hα hβ hab h1 h2 h3 h4 c
  · exact core_two_of_tableCheck (by intro i; simp [Tag.symmetrizer])
      (pairInjective_of_exceptional (Or.inr (Or.inl rfl))) hcheck
      (j := ⟨0, by decide⟩) (k := ⟨2, by decide⟩) (by decide +kernel)
      (fun z a b c d e => (F2Words.commute_xOp_yOp_E7 h2L z a b c d e).1) z hα hβ hab h1 h2 h3 h4 c
  · exact core_two_of_tableCheck (by intro i; simp [Tag.symmetrizer])
      (pairInjective_of_exceptional (Or.inr (Or.inr rfl))) hcheck
      (j := ⟨0, by decide⟩) (k := ⟨2, by decide⟩) (by decide +kernel)
      (fun z a b c d e => (F2Words.commute_xOp_yOp_E8 h2L z a b c d e).1) z hα hβ hab h1 h2 h3 h4 c

theorem core_two_tag [CharP L 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (z : ModGL τ L) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hab : iform α β = -1)
    (h1 : z * pinnedX τ L α 1 = pinnedX τ L α 1 * z)
    (h2 : z * pinnedX τ L (-α) 1 = pinnedX τ L (-α) 1 * z)
    (h3 : z * pinnedX τ L β 1 = pinnedX τ L β 1 * z)
    (h4 : z * pinnedX τ L (-β) 1 = pinnedX τ L (-β) 1 * z) (c : L) :
    z * pinnedX τ L α c = pinnedX τ L α c * z :=
  core_two_tag_of_tableCheck hτ (tableCheck_eq τ) z hα hβ hab h1 h2 h3 h4 c

end Core

section Perfect

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem neg_mem_comp {i : KernelComponent χ} {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) :
    -α ∈ componentRoots χ i := by
  obtain ⟨hα', rfl⟩ := hα
  have hneg : -α ∈ kernelRoots χ := ⟨IsRoot.neg hα'.1, chi_neg hα'.2⟩
  refine ⟨hneg, (mk_eq_of_iform_ne_zero (α := ⟨α, hα'⟩) (β := ⟨-α, hneg⟩) ?_).symm⟩
  change iform α (-α) ≠ 0
  rw [SimplyLacedCover.iform_neg_right]
  exact neg_ne_zero.2 (iform_self_pos_of_isRoot hα'.1).ne'

theorem exists_adjacent_root (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) :
    ∃ δ ∈ componentRoots χ i, iform α δ = 1 := by
  have hsl := symmetrizer_diag_one hτ
  obtain ⟨β, hβ, n, hn, hnβ⟩ := exists_odd_witness_of_simplyLaced hsl i hi hα
  have hβr := isRoot_of_mem_componentRoots hβ
  have hαr := isRoot_of_mem_componentRoots hα
  rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, iform_self_eq_two hsl hβr] at hnβ
  have hn' : n = iform β α := by omega
  by_cases hba : β = α
  · subst hba
    rw [iform_self_eq_two hsl hβr] at hn'
    rw [hn'] at hn
    exact absurd hn (by decide)
  by_cases hbn : β = -α
  · subst hbn
    rw [SimplyLacedCover.iform_neg_left, iform_self_eq_two hsl hαr] at hn'
    rw [hn'] at hn
    exact absurd hn (by decide)
  rcases iform_mem hsl hβr hαr hba hbn with h | h | h
  · refine ⟨-β, neg_mem_comp hβ, ?_⟩
    rw [SimplyLacedCover.iform_neg_right, iform_comm, h]
    rfl
  · rw [h] at hn'
    rw [hn'] at hn
    exact absurd hn (by decide)
  · exact ⟨β, hβ, by rw [iform_comm]; exact h⟩

theorem isPerfect_componentRootSpan_two {K : Type} [Field K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hK : ∀ c : K, c = 0 ∨ c = 1) (i : KernelComponent χ)
    (hi : 2 < (componentRoots χ i).ncard) : Group.IsPerfect (componentRootSpan K χ i) := by
  have hsl := symmetrizer_diag_one hτ
  refine Subgroup.isPerfect_iff.2 (le_antisymm (Subgroup.commutator_le_self _) ?_)
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rcases hK c with rfl | rfl
  · rw [pinnedX_zero]
    exact one_mem _
  obtain ⟨δ, hδ, hαδ⟩ := exists_adjacent_root hτ i hi hα
  have hδr := isRoot_of_mem_componentRoots hδ
  have hαr := isRoot_of_mem_componentRoots hα
  have hγ : α - δ ∈ componentRoots χ i := by
    have := mem_componentRoots_of_nsmul_add hα (neg_mem_comp hδ) 1 1 (by
      rw [one_smul, one_smul, ← sub_eq_add_neg]
      have := SimplyLacedCover.isRoot_add hsl hαr (IsRoot.neg hδr) (by
        rw [SimplyLacedCover.iform_neg_right, hαδ])
      simpa [sub_eq_add_neg] using this)
    simpa [sub_eq_add_neg] using this
  have hγr := isRoot_of_mem_componentRoots hγ
  have hγδ : iform (α - δ) δ = -1 := by
    rw [iform_sub_left, hαδ, iform_self_eq_two hsl hδr]
    norm_num
  have hcomm := (SimplyLacedCover.adjointRoots (K := K) hτ).commutator (α - δ) δ hγr hδr hγδ
  have hS : ∀ γ ∈ componentRoots χ i, pinnedX τ K γ 1 ∈ componentRootSpan K χ i :=
    fun γ hγ => pinnedX_mem_rootSpan hγ 1
  have := Subgroup.commutator_mem_commutator (hS _ hγ) (hS _ hδ)
  have e : ⁅pinnedX τ K (α - δ) 1, pinnedX τ K δ 1⁆ = pinnedX τ K α 1 := by
    have h1 := congrArg (fun g : adjointGroup τ K => (g : ModGL τ K)) hcomm
    simp only [SimplyLacedCover.coe_commutatorElement_adjointGroup,
      SimplyLacedCover.adjointRoots_x] at h1
    rw [h1, sub_add_cancel]
  rwa [e] at this

end Perfect

section Assembly

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem commute_rootSpan_of_commute_component_two_of_tableCheck
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hcheck : tableCheck τ = true)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hq : S.D.q = 2) (hrk : 2 < (componentRoots (rootCharHom a) i).ncard) (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g := by
  classical
  have hTauAll : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := hτ
  have hsl : ∀ j : Fin τ.rank, τ.symmetrizer j j = 1 := by
    rcases hτ with rfl | rfl | rfl <;> intro j <;> simp [Tag.symmetrizer]
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  rw [hs1] at hs0 hs hmin hinner
  have : NeZero 1 := ⟨one_ne_zero⟩
  obtain ⟨w, hw, hwr⟩ := hinner
  obtain ⟨σ, zu, hσ, hnorm, hz⟩ := exists_untwist_outer_T S hT i hs0 (1 : ModGL τ L)
    (one_mem _) 1 (by
      have : weylQuotientHom τ L ⟨(1 : ModGL τ L), one_mem _⟩ = 1 := map_one _
      exact this)
    (fun γ hγ => by simpa using And.intro hγ hγ)
    ⟨w, hw, fun γ hγ => by simpa using hwr γ hγ⟩
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rw [hq] at h
    exact_mod_cast h
  have hCharL : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2L)
  have h2K : (2 : fixSubfield σ) = 0 := by
    have e : ((2 : fixSubfield σ) : L) = 2 := map_ofNat (fixSubfield σ).subtype 2
    exact Subtype.ext (by rw [e, h2L]; rfl)
  have hCharK : CharP (fixSubfield σ) 2 :=
    (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2K)
  have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ, hq, pow_one]
  have hBig : ∃ alpha ∈ componentRoots (rootCharHom a) i,
      ∃ delta ∈ componentRoots (rootCharHom a) i, delta ≠ alpha ∧ delta ≠ -alpha := by
    by_contra h
    push Not at h
    obtain ⟨root, hroot⟩ := Quotient.exists_rep i
    let alpha := root.val
    have ha : alpha ∈ componentRoots (rootCharHom a) i := ⟨root.property, hroot⟩
    have hsub : componentRoots (rootCharHom a) i ⊆ ({alpha, -alpha} : Set (Fin τ.rank → ℤ)) := by
      intro delta hd
      rcases eq_or_ne delta alpha with he | he
      · exact Set.mem_insert_iff.mpr (Or.inl he)
      · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (h alpha ha delta hd he)))
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have htwo : ({alpha, -alpha} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 := by
      calc
        _ ≤ ({-alpha} : Set (Fin τ.rank → ℤ)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  have hperfC := isPerfect_componentRootSpan_simplyLaced (K := fixSubfield σ)
    (Or.inr hTauAll) i hBig
  have hz1 : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step 1 (zu * g * zu⁻¹) = zu * frobGL σ g * zu⁻¹ := by
    intro g hg
    rw [hz g hg]
    simp
  have hmem : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ t : L, t ^ 2 = t →
      zu * pinnedX τ L γ t * zu⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro γ hγ t ht
    have hc : σ t = t := by rw [hσ2]; exact ht
    have hγ' : γ ∈ unionRoots (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) := by
      rw [unionRoots_singleton]
      exact hγ
    set P := outerOrbitFamily S hT i hs hmin with hP
    have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
      rw [hP, outerOrbitFamily_S, ZMod.val_zero]
      simp only [Function.iterate_zero, id_eq, Set.image_id']
    have hιC : ∀ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i,
        baseChangeGL (fixSubfield σ).subtype x ∈ CQ σ i := by
      intro x hx
      rw [CQ_eq_map]
      exact ⟨x, hx, rfl⟩
    have hιS : ∀ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i,
        baseChangeGL (fixSubfield σ).subtype x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      fun x hx => CQ_le_rootSpan σ i (hιC x hx)
    let θ₀ : componentRootSpan (fixSubfield σ) (rootCharHom a) i →* P.S 0 :=
      ((MulAut.conj zu).toMonoidHom.comp
        ((baseChangeGL (τ := τ) (fixSubfield σ).subtype).comp
          (componentRootSpan (fixSubfield σ) (rootCharHom a) i).subtype)).codRestrict (P.S 0)
        fun x => by
          rw [hP0]
          exact (hnorm i _).1 (hιS x.1 x.2)
    have hθ₀ : ∀ x, ((θ₀ x : P.S 0) : ModGL τ L) =
        zu * baseChangeGL (fixSubfield σ).subtype x.1 * zu⁻¹ := fun x => rfl
    have hfix : ∀ x, iterHom S.D.step 1 ((θ₀ x : P.S 0) : ModGL τ L) = θ₀ x := by
      intro x
      rw [hθ₀, hz1 _ (hιS x.1 x.2), frobGL_eq_self_of_mem_CQ σ i (hιC x.1 x.2)]
    obtain ⟨xt, hxt, hxι⟩ : ∃ x ∈ componentRootSpan (fixSubfield σ) (rootCharHom a) i,
        baseChangeGL (fixSubfield σ).subtype x = pinnedX τ L γ t := by
      have := pinnedX_mem_CQ hγ' hc
      rw [CQ_eq_map] at this
      exact this
    have hrt := outer_norm_mem_rationalComponent S hT i hs hmin hperfC θ₀ hfix ⟨xt, hxt⟩
    have hnormeq := norm_eq_list_prod P (θ₀ ⟨xt, hxt⟩)
    have hone : (P.norm (θ₀ ⟨xt, hxt⟩) : ModGL τ L) = zu * pinnedX τ L γ t * zu⁻¹ := by
      have hd : ∀ k : ZMod 1, k.val = 0 := fun k => by
        rw [Subsingleton.elim k 0, ZMod.val_zero]
      rw [hnormeq]
      simp [Finset.univ_unique, hd, iterHom_zero, hθ₀, hxι]
    rw [hone] at hrt
    exact hrt
  have hz' : ∀ γ ∈ componentRoots (rootCharHom a) i,
      (zu⁻¹ * z * zu) * pinnedX τ L γ 1 = pinnedX τ L γ 1 * (zu⁻¹ * z * zu) := by
    intro γ hγ
    have h := (hcomm _ (hmem γ hγ 1 (by simp))).eq
    have hx := congrArg (fun x => zu⁻¹ * x * zu) h
    have hzu : (zu⁻¹ * z * zu) * (zu⁻¹ * (zu * pinnedX τ L γ 1 * zu⁻¹) * zu) =
        (zu⁻¹ * (zu * pinnedX τ L γ 1 * zu⁻¹) * zu) * (zu⁻¹ * z * zu) := by
      simpa only [mul_assoc, mul_inv_cancel_left] using hx
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one] using hzu
  have hgen : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      z * (zu * pinnedX τ L γ c * zu⁻¹) = (zu * pinnedX τ L γ c * zu⁻¹) * z := by
    intro γ hγ c
    obtain ⟨δ, hδ, hne, hneg, hγδneg⟩ := exists_neg_partner
      (isRootComponent_componentRoots i) hBig hγ
    have hγδ : iform γ δ = -1 := by
      have hh := iform_mem hsl (isRoot_of_mem_componentRoots hγ) (isRoot_of_mem_componentRoots hδ)
        hne.symm (fun h => hneg (by rw [h, neg_neg]))
      rcases hh with h | h | h <;> omega
    have hδr := isRoot_of_mem_componentRoots hδ
    have hγr := isRoot_of_mem_componentRoots hγ
    have hab : iform γ δ = -1 := hγδ
    have key := core_two_tag_of_tableCheck hτ hcheck (zu⁻¹ * z * zu) hγr hδr hab (hz' γ hγ)
      (hz' _ ((isRootComponent_componentRoots i).neg_mem γ hγ)) (hz' δ hδ) (hz' _ ((isRootComponent_componentRoots i).neg_mem δ hδ)) c
    calc z * (zu * pinnedX τ L γ c * zu⁻¹)
        = zu * ((zu⁻¹ * z * zu) * pinnedX τ L γ c) * zu⁻¹ := by group
      _ = zu * (pinnedX τ L γ c * (zu⁻¹ * z * zu)) * zu⁻¹ := by rw [key]
      _ = (zu * pinnedX τ L γ c * zu⁻¹) * z := by group
  have hmap : (rootSpan τ L (componentRoots (rootCharHom a) i)).map (MulAut.conj zu).toMonoidHom ≤
      Subgroup.centralizer {z} := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hgen γ hγ c).symm
  intro g hg
  have hg' : zu⁻¹ * g * zu ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine (hnorm i _).2 ?_
    have : zu * (zu⁻¹ * g * zu) * zu⁻¹ = g := by group
    rw [this]
    exact hg
  have hcalc : (MulAut.conj zu).toMonoidHom (zu⁻¹ * g * zu) = g := by
    show zu * (zu⁻¹ * g * zu) * zu⁻¹ = g
    group
  have hmem' : g ∈ Subgroup.centralizer {z} := hmap (Subgroup.mem_map.2 ⟨_, hg', hcalc⟩)
  exact Commute.symm (Subgroup.mem_centralizer_singleton_iff.1 hmem')

theorem commute_rootSpan_of_commute_component_two (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hq : S.D.q = 2) (hrk : 2 < (componentRoots (rootCharHom a) i).ncard) (z : ModGL τ L)
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) :
    ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g :=
  commute_rootSpan_of_commute_component_two_of_tableCheck S hτ (tableCheck_eq τ)
    hT i hinner hs1 hq hrk z hcomm

end Assembly

section RootLine

variable {τ : Tag} {L : Type} [Field L]

theorem rootLineCommuteTwo [CharP L 2] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α γ : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hγ : IsRoot τ γ) (hab : iform α γ = -1)
    (g : ModGL τ L)
    (hg : ∀ β ∈ ({α, -α, γ, -γ} : Set (Fin τ.rank → ℤ)), g * pinnedX τ L β 1 = pinnedX τ L β 1 * g)
    (β : Fin τ.rank → ℤ) (hβ : β ∈ ({α, -α, γ, -γ} : Set (Fin τ.rank → ℤ))) (t : L) :
    g * pinnedX τ L β t = pinnedX τ L β t * g := by
  have hαg := hg α (by simp)
  have hnαg := hg (-α) (by simp)
  have hγg := hg γ (by simp)
  have hnγg := hg (-γ) (by simp)
  rcases hβ with rfl | rfl | rfl | rfl
  · exact core_two_tag hτ g hα hγ hab hαg hnαg hγg hnγg t
  · refine core_two_tag hτ g (IsRoot.neg hα) (IsRoot.neg hγ) ?_ hnαg (by simpa using hαg) hnγg
      (by simpa using hγg) t
    rw [SimplyLacedCover.iform_neg_left, SimplyLacedCover.iform_neg_right, neg_neg, hab]
  · refine core_two_tag hτ g hγ hα ?_ hγg hnγg hαg hnαg t
    rw [iform_comm, hab]
  · refine core_two_tag hτ g (IsRoot.neg hγ) (IsRoot.neg hα) ?_ hnγg (by simpa using hγg) hnαg
      (by simpa using hαg) t
    rw [SimplyLacedCover.iform_neg_left, SimplyLacedCover.iform_neg_right, neg_neg, iform_comm, hab]

@[expose] def E6RootLineCommuteTwo : Prop :=
  ∀ (L : Type) [Field L] [CharP L 2] (α γ : Fin Tag.E6.rank → ℤ),
    IsRoot Tag.E6 α → IsRoot Tag.E6 γ → iform α γ = -1 →
    ∀ g : ModGL Tag.E6 L,
      (∀ β ∈ ({α, -α, γ, -γ} : Set _), Commute g (pinnedX Tag.E6 L β 1)) →
      ∀ β ∈ ({α, -α, γ, -γ} : Set _), ∀ t : L, Commute g (pinnedX Tag.E6 L β t)

theorem e6RootLineCommuteTwo : E6RootLineCommuteTwo := by
  intro L _ _ α γ hα hγ hab g hg β hβ t
  exact rootLineCommuteTwo (Or.inl rfl) hα hγ hab g (fun β hβ => (hg β hβ).eq) β hβ t

end RootLine

end CFSG.HardMathSupport.Timmesfeld.LangTorus
