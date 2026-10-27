module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false


section TwoD

variable {τ : Tag}

private theorem excRec_lieModel_conj {G : Type} [Group G] {R₀ D₀ : Subgroup G} (z : G)
    (hRC : R₀.map (MulAut.conj z⁻¹).toMonoidHom = D₀) {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel (↥D₀ ⧸ Subgroup.center ↥D₀) t n p f) :
    CFSG.Blueprint.LieModel (↥R₀ ⧸ Subgroup.center ↥R₀) t n p f := by
  let eR : ↥R₀ ≃* ↥D₀ :=
    (R₀.equivMapOfInjective (MulAut.conj z⁻¹).toMonoidHom (MulAut.conj z⁻¹).injective).trans
      (MulEquiv.subgroupCongr hRC)
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (QuotientGroup.congr _ _ eR (Subgroup.map_center_eq eR)).symm h

private theorem excRec_twoD_aux (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : KacData τ)
    (hK : K.Facts) {E : List (ℕ × ℕ)} {tp : ℕ → ℕ → List ℕ}
    (hT : IsTreePaths (τ.rank + 1) E tp)
    (hadj : ∀ x y : Option (Fin τ.rank), K.Adj x y ↔ (nodeIdx x, nodeIdx y) ∈ E)
    {cands : List (List ℕ)}
    (hcheck : ((List.range (τ.rank + 1)).sublists.all fun zl =>
      !(fun _ : List ℕ => true) zl ||
        zl.all fun x => cands.any (sameSet (compIdx (τ.rank + 1) tp zl x))) = true)
    (hlt : ∀ c ∈ cands, ∀ w ∈ c, w < τ.rank + 1)
    (hcard : ∀ c ∈ cands, (c.map (idxNode (r := τ.rank))).toFinset.card = c.length)
    {trees : List (List (Option (Fin τ.rank)))}
    (hcount : ∀ c ∈ cands, 4 ≤ c.length →
      kacCount τ K.θ (c.map (idxNode (r := τ.rank))).toFinset = 2 * c.length * (c.length - 1) →
        ∃ P ∈ trees, sameSet c (P.map nodeIdx) = true)
    (htrees : ∀ P ∈ trees, P.Nodup ∧ 4 ≤ P.length ∧
      (∀ c d : Fin P.length, c ≠ d → ¬ edgeD P.length c d → ¬ edgeD P.length d c →
        iform (K.extRoot (P.get c)) (K.extRoot (P.get d)) = 0) ∧
      ∀ c d : Fin P.length, edgeD P.length c d →
        (nodeIdx (P.get c), nodeIdx (P.get d)) ∈ E)
    (hframes : ∀ {F : Type} [Field F] (x y : Option (Fin τ.rank)),
      (nodeIdx x, nodeIdx y) ∈ E →
        ∃ (ρ : SL(3, F) →* ModGL τ F) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ),
          CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ ∧ σ 0 1 = K.extRoot x ∧
            σ 1 2 = K.extRoot y)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ} (hTor : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD) :
    ∃ e : ℕ, ringChar L ^ e = S.D.q ∧
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus
        (compRank (componentRoots (rootCharHom a) i)) (ringChar L) e := by
  classical
  obtain ⟨r, e, m, hr, hchar, hm5, z, ε, D, hq, he, hDe, hRC, hDs, hCart, hfix, hswap⟩ :=
    CompsPTwoDExport.exists_twoD_export S hτ hTor i hkind h5
  haveI := hr
  haveI := hchar
  have hΨ : IsRootComponent (componentRoots (rootCharHom a) i) := isRootComponent_componentRoots i
  have hcardΔ : (simpleRoots (componentRoots (rootCharHom a) i)).card = m := by
    rw [← Fintype.card_coe, Fintype.card_congr ε, Fintype.card_fin]
  have hmrank : m = compRank (componentRoots (rootCharHom a) i) := by
    rw [compRank_eq_card hΨ, hcardΔ]
  have hR : CompsPTwoDDatumG.TwoDChainRecog r L D.e m := by
    rw [hDe]
    exact CompsPTwoDChainO.twoDChainRecog_all he (by omega)
  have hsl : ∀ β ∈ componentRoots (rootCharHom a) i, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  have hbroot : ∀ j : Fin m, IsRoot τ (ε.symm j : Fin τ.rank → ℤ) := fun j =>
    simpleRoots_isRoot (ε.symm j).2
  have hG : ∀ j k : Fin m, iform (ε.symm j : Fin τ.rank → ℤ) (ε.symm k) =
      CFSG.LieType.Universal.Spin.cartanD m j k := by
    intro j k
    have h := hCart (ε.symm j) (ε.symm k)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    rw [← h]
    exact (CompsPTwoDBase.corootPair_eq_iform (hbroot j)
      (hsl _ (simpleRoots_subset (ε.symm j).2)) _).symm
  have hrange : Set.range (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) =
      ((simpleRoots (componentRoots (rootCharHom a) i) : Finset (Fin τ.rank → ℤ)) :
        Set (Fin τ.rank → ℤ)) := by
    ext β
    exact ⟨by rintro ⟨j, rfl⟩; exact (ε.symm j).2, fun hβ => ⟨ε ⟨β, hβ⟩, by simp⟩⟩
  have hsw := hswap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)
  have hlie := KD264Lie.ExcUntw.lieModel_orbitGroup_of_datum_four_of_root_data hτ D (by omega) hR
    (fun j : Fin m => (ε.symm j : Fin τ.rank → ℤ)) hbroot
    (fun j k h => ε.symm.injective (Subtype.ext h)) hG (hDs.trans hrange.symm) hfix hsw.1 hsw.2
    (fun j k hjk => CompsPTwoDMain.exists_dFrames hτ K hK hT hadj hcheck hlt hcard hcount htrees
      hframes S hp hpL hTp i (by omega) hn ε hCart L j k hjk)
  have hmodel := excRec_lieModel_conj z hRC hlie
  rw [hDe] at hmodel
  rw [hmrank] at hmodel
  exact ⟨e, by rw [ringChar.eq L r, hq], by rw [ringChar.eq L r]; exact hmodel⟩

theorem excRec_twoD_of_root_data {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ}
    (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ e : ℕ, ringChar L ^ e = S.D.q ∧
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus
        (compRank (componentRoots (rootCharHom a) i)) (ringChar L) e := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap ha1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hkind : twistKind S.ρ (rootCharHom a) i = .twoD := by
    unfold twistKind
    rw [if_neg hout, if_neg, if_pos ⟨by omega, hn⟩]
    rintro (⟨h6, h72⟩ | ⟨h4', -, -⟩)
    · rw [hn, h6] at h72
      omega
    · omega
  have hr := compRank_le_rank (componentRoots (rootCharHom a) i)
  cases τ with
  | G2 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | F4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | D4 => exact absurd (le_trans h5 hr) (by simp [Tag.rank])
  | E6 =>
    exact excRec_twoD_aux (Or.inr (Or.inl rfl)) kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt
      e6_card e6_dcount e6_dtrees (fun {F} _ x y h => e6_frames x y h) S hp hpL hT hTp i h5 hn
      hkind
  | E7 =>
    exact excRec_twoD_aux (Or.inr (Or.inr (Or.inl rfl))) kacE7 facts_E7 e7_tree e7_adj e7_check
      e7_lt e7_card e7_dcount e7_dtrees (fun {F} _ x y h => e7_frames x y h) S hp hpL hT hTp i h5
      hn hkind
  | E8 =>
    exact excRec_twoD_aux (Or.inr (Or.inr (Or.inr rfl))) kacE8 facts_E8 e8_tree e8_adj e8_check
      e8_lt e8_card e8_dcount e8_dtrees (fun {F} _ x y h => e8_frames x y h) S hp hpL hT hTp i h5
      hn hkind


theorem excRec_twoD {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀) {p : ℕ}
    (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ m, a m ^ p = 1) (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)])) :
    ∃ e : ℕ, ringChar L ^ e = S.D.q ∧
      CFSG.Blueprint.LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus
        (compRank (componentRoots (rootCharHom a) i)) (ringChar L) e :=
  excRec_twoD_of_root_data S hp hT hap ha1 i h5 hn hout

end TwoD

end CFSG.LocalAnalysis.GLTheoremA.I167

end
