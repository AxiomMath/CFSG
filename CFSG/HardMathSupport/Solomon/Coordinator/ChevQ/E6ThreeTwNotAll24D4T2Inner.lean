module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnStr
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactD
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompFrames
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.Timmesfeld CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

@[expose] def d4t2inB (zl : List ℕ) : Bool :=
  zl.all fun x => (TwE6UniqAbs.szF zl x != 24) || (TwE6UniqAbs.cmpF zl x == TwE6InnerAbs.sD4)

theorem d4t2in_kc : ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
    (m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) →
    d4t2inB (TwE6UniqAbs.zlC m0 m1 m2 m3 m4 m5) = true := by
  decide +kernel

theorem d4t2in_cmpF_eq_sD4 {m0 m1 m2 m3 m4 m5 : Fin 4}
    (hsum : m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3) {x : ℕ}
    (hx : x ∈ TwE6UniqAbs.zlC m0 m1 m2 m3 m4 m5)
    (h24 : TwE6UniqAbs.szF (TwE6UniqAbs.zlC m0 m1 m2 m3 m4 m5) x = 24) :
    TwE6UniqAbs.cmpF (TwE6UniqAbs.zlC m0 m1 m2 m3 m4 m5) x = TwE6InnerAbs.sD4 := by
  have hx' := List.all_eq_true.1 (d4t2in_kc m0 m1 m2 m3 m4 m5 hsum) x hx
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hx'
  rcases hx' with h | h
  · exact absurd h24 h
  · exact h

section Class

set_option linter.unusedSectionVars false


theorem d4t2_class_of_card {L : Type} [Field L] [IsAlgClosed L] (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (hall : (kernelRoots (rootCharHom a)).ncard = 24) (i : KernelComponent (rootCharHom a)) :
    compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 24 := by
  classical
  have F := TwE6UniqAbs.kac_facts h3 hap
  have hfin := KSNotAll24.finite_kernelRoots_E6 (rootCharHom a)
  have hsub := KSNotAll24.componentRoots_subset_kernelRoots (rootCharHom a)
  have hn : (componentRoots (rootCharHom a) i).ncard = 24 := by
    by_cases hone : ∀ k : KernelComponent (rootCharHom a), k = i
    · have heq : kernelRoots (rootCharHom a) = componentRoots (rootCharHom a) i :=
        Set.Subset.antisymm (fun α hα => ⟨hα, hone _⟩) (hsub i)
      rw [← heq, hall]
    push Not at hone
    obtain ⟨j, hji⟩ := hone
    exfalso
    by_cases htwo : ∀ k : KernelComponent (rootCharHom a), k = i ∨ k = j
    · have heq : kernelRoots (rootCharHom a) =
          componentRoots (rootCharHom a) i ∪ componentRoots (rootCharHom a) j := by
        refine Set.Subset.antisymm (fun α hα => ?_) (Set.union_subset (hsub i) (hsub j))
        rcases htwo ⟦⟨α, hα⟩⟧ with h | h
        · exact Or.inl ⟨hα, h⟩
        · exact Or.inr ⟨hα, h⟩
      have hcard := Set.ncard_union_eq (KSNotAll24.disjoint_componentRoots (Ne.symm hji))
        (hfin.subset (hsub i)) (hfin.subset (hsub j))
      rw [← heq, hall] at hcard
      have h₁ := KSNotAll24.ncard_componentRoots_mem hap i
      have h₂ := KSNotAll24.ncard_componentRoots_mem hap j
      omega
    push Not at htwo
    obtain ⟨k, hki, hkj⟩ := htwo
    obtain ⟨hi6, hj6, hk6⟩ := F.three i j k (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj)
    have hcov : kernelRoots (rootCharHom a) ⊆ componentRoots (rootCharHom a) i ∪
        componentRoots (rootCharHom a) j ∪ componentRoots (rootCharHom a) k := by
      intro α hα
      by_cases hli : (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a)) = i
      · exact Or.inl (Or.inl ⟨hα, hli⟩)
      by_cases hlj : (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a)) = j
      · exact Or.inl (Or.inr ⟨hα, hlj⟩)
      by_cases hlk : (⟦⟨α, hα⟩⟧ : KernelComponent (rootCharHom a)) = k
      · exact Or.inr ⟨hα, hlk⟩
      exact (F.four i j k _ (Ne.symm hji) (Ne.symm hki) (Ne.symm hli) (Ne.symm hkj)
        (Ne.symm hlj) (Ne.symm hlk)).elim
    have hle := Set.ncard_le_ncard hcov
      (((hfin.subset (hsub i)).union (hfin.subset (hsub j))).union (hfin.subset (hsub k)))
    have hu₁ := Set.ncard_union_le
      (componentRoots (rootCharHom a) i ∪ componentRoots (rootCharHom a) j)
      (componentRoots (rootCharHom a) k)
    have hu₂ := Set.ncard_union_le (componentRoots (rootCharHom a) i)
      (componentRoots (rootCharHom a) j)
    omega
  refine ⟨?_, hn⟩
  obtain ⟨_, w, m0, m1, m2, m3, m4, m5, -, hsum, -, hcl⟩ := TwE6UniqAbs.kac_class_data h3 hap
  obtain ⟨x, hx, -, hncard, hrank, -⟩ := hcl i
  have h4 : TwE6InnerAbs.sD4.card = 4 := by decide
  rw [hrank, d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hn), h4]

end Class

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.CentralExt in
theorem d4t2in_not_three_dvd_card_center_spin (F : Type) [Field F] :
    ¬ 3 ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 4 F))) := by
  have hn : 3 ≤ 4 := by norm_num
  have hc : Subgroup.center (spinGroup (quadPlus 4 F)) = SpinPlusClosed.scalarSpin 4 F :=
    (spinToStatedProj_quadPlus (K := F) hn).2.2.symm.trans (spinToStatedProj_quadPlus hn).2.1
  rw [hc]
  by_cases h2 : (2 : F) = 0
  · rw [SpinPlusClosed.comap_statedScalars_quadPlus_eq_bot hn h2, Subgroup.card_bot]
    norm_num
  · rw [(SpinPlusClosed.isKleinFour_scalarSpin hn h2 (by decide)).card_four]
    norm_num

section Rat

set_option linter.unusedSectionVars false


theorem d4t2in_dModel_center {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {ta : Fin τ.rank → Lˣ}
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hT : rootDiagUnit τ ta ∈ S.D.torus) (i : KernelComponent (rootCharHom ta))
    (hinner : twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom ta) i)]))
    {n : ℕ} (hn : 4 ≤ n) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hroots : componentRoots (rootCharHom ta) i = rootsOfFam β (Set.range l))
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ {F : Type} [Field F] (i j : Fin n), edgeD n i j → ∃ θ : SL(3, F) →* ModGL τ F,
      θ.comp (blockSL F 3 2 0 (by omega)) = rootSL2 τ F (β (l i)) ∧
        θ.comp (blockSL F 3 2 1 (by omega)) = rootSL2 τ F (β (l j)))
    {r e : ℕ} (hr : r.Prime) (he : 0 < e) (hq : S.D.q = r ^ e) :
    StatedClassicalModel
        (↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i))
        .POmegaPlus n r (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) ∧
      ∃ (F : Type) (_ : Field F),
        Nat.card (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i)) ∣
          Nat.card (Subgroup.center (spinGroup (CFSG.LieType.Universal.Spin.quadPlus n F))) := by
  classical
  refine ⟨KSExact.rationalComponent_dModel S hτ hT i hinner hn β hroot l hroots hgram hframe hr he
    hq, ?_⟩
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  obtain ⟨σ, hfin, hcard, hrest⟩ := exists_inner_cover S hT i hinner
  haveI : Finite ↥(fixSubfield σ) := hfin
  have hcard' : Nat.card ↥(fixSubfield σ) = r ^ (e * s) := by rw [hcard, hq, ← pow_mul]
  have hcomp : componentRootSpan (fixSubfield σ) (rootCharHom ta) i =
      rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l)) := by
    show rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom ta) i) = _
    rw [hroots]
  rw [hcomp] at hrest
  obtain ⟨f, hf1, hker, hf2⟩ := hrest
  obtain ⟨U, ρ', hgen, hcomm, hρ', hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram
    (hframe (F := ↥(fixSubfield σ)))
  have hadm : StatedLieAdmissible .POmegaPlus n r (e * s) := ⟨hr, hes, hn⟩
  obtain ⟨Ψ, -, -, hqs, hcent, -⟩ := weakCT_spinPlus_of_frame hadm (by omega) hcard' U hgen hcomm
    hρ' hψ
  have hCperf : Group.IsPerfect ↥(rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l))) :=
    hqs.1
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hCperf)) hf1
  let g : ↥(rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l))) →*
      ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤
      Subgroup.center ↥(rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l))) := by
    intro c hc
    apply hker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  have hZ : Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom ta) i) =
      (Subgroup.center ↥(rootSpan τ (fixSubfield σ) (rootsOfFam β (Set.range l)))).map g := by
    rw [← comap_center_of_surjective hCperf.commutator_eq_top g hgsurj hgker,
      Subgroup.map_comap_eq_self_of_surjective hgsurj]
  refine ⟨↥(fixSubfield σ), inferInstance, ?_⟩
  rw [hZ, hcent]
  exact (Subgroup.card_map_dvd _ _).trans (Subgroup.card_map_dvd _ _)

theorem twE6ComponentType_rational_of_inner_d4
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .E6 L p₀)
    {l f : ℕ} (hl : l.Prime) (hf : 0 < f) (hq : S.D.q = l ^ f) (hl3 : l ≠ 3)
    (h3 : ((3 : ℕ) : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit .E6 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hall : (kernelRoots (rootCharHom a)).ncard = 24)
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hin : twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))) :
    TwE6ComponentType (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨_, w, m0, m1, m2, m3, m4, m5, -, hsum, -, hcl⟩ := TwE6UniqAbs.kac_class_data h3 hap
  obtain ⟨x, hx, hroots, hncard, -, -⟩ := hcl i
  have hD4 := d4t2in_cmpF_eq_sD4 hsum hx (hncard.symm.trans hc)
  have hfam : componentRoots (rootCharHom a) i =
      rootsOfFam (fun y => w⁻¹ • kacE6.extRoot y) (Set.range TwE6InnerAbs.lD4) := by
    rw [hroots, hD4, ← TwE6InnerAbs.range_lD4]
    exact TwE6InnerAbs.image_rootsOf_eq_rootsOfFam kacE6 w⁻¹ _
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1.1
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one hfin hρ
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    rw [hs1, Function.iterate_one]
    exact hin
  obtain ⟨hmodel, F, _, hZ⟩ := d4t2in_dModel_center S (Or.inr (Or.inl rfl)) hT i hinner
    (n := 4) le_rfl (fun y => w⁻¹ • kacE6.extRoot y)
    (fun y => IsRoot.smul (kacE6.isRoot_extRoot y) w⁻¹) TwE6InnerAbs.lD4 hfam
    (fun c d hcd h1 h2 => by
      show iform (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 c))
        (w⁻¹ • kacE6.extRoot (TwE6InnerAbs.lD4 d)) = 0
      rw [iform_smul, kacE6_extRoot]
      exact TwE6InnerAbs.d4_hgram c d hcd h1 h2)
    (fun {F} _ c d h => TwE6InnerAbs.d4_frames w⁻¹ c d h) hl hf hq
  rw [hs1, Nat.mul_one] at hmodel
  obtain ⟨q', hv, hqp, -, ⟨e⟩⟩ := KSExact.exists_D_of_statedClassicalModel_POmegaPlus hmodel
  refine Or.inl ⟨fun h3Z => d4t2in_not_three_dvd_card_center_spin F (h3Z.trans hZ),
    ⟨.D 4 q', hv⟩, e, ?_, ?_⟩
  · show 3 ≠ (TauCeti.LieTypeIndex.D 4 q').characteristic
    rw [TauCeti.LieTypeIndex.characteristic_D, hqp]
    exact fun h => hl3 h.symm
  · simp [AGLEmbeddingD2.IsD2SeitzException]

end Rat

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
