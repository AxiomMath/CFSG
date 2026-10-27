module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TreeGen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.ClassicalBridge
public import CFSG.ClassicalInvolution.WeakCT.Spin
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem weakCT_spinPlus_of_frame {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (hn3 : 3 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    {X : Type} [Group X] (U : Fin n → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin n → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin n, edgeD n i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : spinGroup (Spin.quadPlus n F) →* X, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (spinGroup (Spin.quadPlus n F))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .POmegaPlus n p f := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum n F hn3).isFiniteType
    (Dv := (Spin.plusDatum n F hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin n) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := F) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, -⟩ := weakCT_of_frame
    (CurtisTits.curtisTitsConclusion_spinPlus hadm hF hn3) (leviConePresented_spinPlus F hn3) hD
    (⟨0, by omega⟩ : Fin n) hgen hcomm hρ hψ
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel⟩


section Recog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint


theorem range_codRestrict_eq' {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Subgroup H)
    (h : ∀ x, f x ∈ S) : (f.codRestrict S h).range = f.range.subgroupOf S := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem weakCT_data {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b)) {n : ℕ}
    (l : Fin n → ι) (adj : Fin n → Fin n → Prop)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ adj i j → ¬ adj j i → iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, adj i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    ∃ (U : Fin n → Subgroup ↥(rootSpan τ K (rootsOfFam β (Set.range l))))
      (ρ : Fin n → SL(2, K) →* ↥(rootSpan τ K (rootsOfFam β (Set.range l)))),
      ⨆ k, U k = ⊤ ∧
      (∀ i j : Fin n, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a) ∧
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      (∀ i j : Fin n, adj i j → ∃ ψ : SL(3, K) →* ↥(rootSpan τ K (rootsOfFam β (Set.range l))),
        ψ.comp (blk K 0) = ρ i ∧ ψ.comp (blk K 1) = ρ j) := by
  classical
  set G : Subgroup (ModGL τ K) := rootSpan τ K (rootsOfFam β (Set.range l)) with hGdef
  have hmemΨ : ∀ k, β (l k) ∈ rootsOfFam β (Set.range l) ∧ -β (l k) ∈ rootsOfFam β (Set.range l) := by
    intro k
    have hsum : ∑ b, ((fun b => if b = l k then 1 else 0 : ι → ℕ) b : ℤ) • β b = β (l k) := by
      simp [ite_smul, Finset.sum_ite_eq']
    refine ⟨⟨hroot _, fun b => if b = l k then 1 else 0, fun b hb => ?_, Or.inl hsum.symm⟩,
      ⟨IsRoot.neg (hroot _), fun b => if b = l k then 1 else 0, fun b hb => ?_, Or.inr ?_⟩⟩
    · by_cases h : b = l k
      · exact ⟨k, h.symm⟩
      · exact absurd (by simp [h]) hb
    · by_cases h : b = l k
      · exact ⟨k, h.symm⟩
      · exact absurd (by simp [h]) hb
    · rw [hsum]
  have hGgen : G = ⨆ k, (rootSL2 τ K (β (l k))).range := by
    apply le_antisymm
    · calc G ≤ ⨆ b ∈ Set.range l, (rootSL2 τ K (β b)).range :=
          rootSpan_rootsOfFam_le hτ β hroot _
        _ = ⨆ k, (rootSL2 τ K (β (l k))).range := iSup_range
    · refine iSup_le fun k => ?_
      rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (hroot _)]
      exact sup_le (le_iSup₂ (f := fun γ (_ : γ ∈ rootsOfFam β (Set.range l)) =>
        rootSubgroup τ K γ) _ (hmemΨ k).1) (le_iSup₂ (f := fun γ
          (_ : γ ∈ rootsOfFam β (Set.range l)) => rootSubgroup τ K γ) _ (hmemΨ k).2)
  have hrangeG : ∀ k, (rootSL2 τ K (β (l k))).range ≤ G := fun k => by
    rw [hGgen]
    exact le_iSup (fun k => (rootSL2 τ K (β (l k))).range) k
  have hmem : ∀ k (A : SL(2, K)), rootSL2 τ K (β (l k)) A ∈ G := fun k A =>
    hrangeG k ⟨A, rfl⟩
  refine ⟨fun k => ((rootSL2 τ K (β (l k))).range).subgroupOf G,
    fun k => (rootSL2 τ K (β (l k))).codRestrict G (hmem k), ?_, ?_, ?_, ?_⟩
  · apply Subgroup.map_injective G.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    simp only [Subgroup.map_subgroupOf_eq_of_le (hrangeG _)]
    exact hGgen.symm
  · intro i j hij h1 h2 a ha b hb
    obtain ⟨A, hA⟩ := ha
    obtain ⟨B, hB⟩ := hb
    have := CFSG.HardMathSupport.Timmesfeld.CrossChar.commute_rootSL2_of_iform_eq_zero hτ
      (hroot (l i)) (hroot (l j)) (hgram i j hij h1 h2) A B
    have hA' : (a : ModGL τ K) = rootSL2 τ K (β (l i)) A := hA.symm
    have hB' : (b : ModGL τ K) = rootSL2 τ K (β (l j)) B := hB.symm
    refine Subtype.ext ?_
    show (a : ModGL τ K) * (b : ModGL τ K) = (b : ModGL τ K) * (a : ModGL τ K)
    rw [hA', hB']
    exact this.eq
  · intro k
    refine ⟨fun a b h => ?_, range_codRestrict_eq' _ G (hmem k)⟩
    exact CFSG.RankThree.Chevalley.rootSL2_injective_of_field (β (l k)) (congrArg Subtype.val h)
  · intro i j hij
    obtain ⟨θ, h0, h1⟩ := hframe i j hij
    have hθG : ∀ x, θ x ∈ G := by
      intro x
      have hx : x ∈ B12 K ⊔ B23 K := by rw [B12_sup_B23]; exact Subgroup.mem_top x
      have h2 : θ x ∈ (B12 K ⊔ B23 K).map θ := Subgroup.mem_map_of_mem θ hx
      rw [Subgroup.map_sup] at h2
      have e0 : (B12 K).map θ = (rootSL2 τ K (β (l i))).range := by
        rw [B12, ← MonoidHom.range_comp, h0]
      have e1 : (B23 K).map θ = (rootSL2 τ K (β (l j))).range := by
        rw [B23, ← MonoidHom.range_comp, h1]
      rw [e0, e1] at h2
      exact sup_le (hrangeG i) (hrangeG j) h2
    refine ⟨θ.codRestrict G hθG, ?_, ?_⟩
    · refine MonoidHom.ext fun A => Subtype.ext ?_
      exact congrArg (fun φ : SL(2, K) →* ModGL τ K => φ A) h0
    · refine MonoidHom.ext fun A => Subtype.ext ?_
      exact congrArg (fun φ : SL(2, K) →* ModGL τ K => φ A) h1

theorem innerRecog_D {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {n : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ)
    (hroot : ∀ b, IsRoot τ (β b)) (l : Fin n → ι)
    (hgram : ∀ i j : Fin n, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin n, edgeD n i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecog p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeD n) hgram hframe
  have hadm : StatedLieAdmissible .POmegaPlus n p f := ⟨hp, hf, hn⟩
  obtain ⟨Ψ', hsurj, hker, hqs, hcent, hmodel⟩ := weakCT_spinPlus_of_frame hadm (by omega) hK U
    hgen hcomm hρ hψ
  obtain ⟨hchev, hA6⟩ := lieModel_plus_chev hmodel
  refine ⟨_, inferInstance, ⟨hqs.1.commutator_eq_top, hchev, fun ⟨e⟩ => (hA6.false e).elim⟩,
    ⟨fun e => hA6.false e⟩, MonoidHom.id _, Function.surjective_id, ?_⟩
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact Subgroup.one_mem _

end Recog

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
