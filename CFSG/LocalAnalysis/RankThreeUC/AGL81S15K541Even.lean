module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeGN
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main
public import CFSG.Adapters.LinearCatalog
public import CFSG.LargeExtraspecial.A2ModSLd
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHPara
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.TwoLocalSylow
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding KFactsPair

@[expose] def K541Even : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ Ls : Subgroup (X ⧸ gnC T), CFSG.Open.IsComponentOf Ls ⊤ →
      ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls →
      ∀ n : ℕ, Even n → IsLThreeOfExp n (↥Ls ⧸ Subgroup.center ↥Ls) →
        Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))

namespace K541Proof

variable {X : Type} [Group X] [Finite X]

theorem odd_card_center_of_component {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : CFSG.Open.IsComponentOf Ls ⊤) :
    Odd (Nat.card (Subgroup.center ↥Ls)) :=
  Nat.not_even_iff_odd.mp fun h =>
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.not_two_dvd_card_center hX hLs
      (even_iff_two_dvd.mp h)

@[expose] noncomputable def equiv_of_center_card_one {S G : Type} [Group S] [Group G]
    (hc : Nat.card (Subgroup.center S) = 1) (e : (S ⧸ Subgroup.center S) ≃* G) : S ≃* G := by
  have hbot : Subgroup.center S = ⊥ := Subgroup.eq_bot_of_card_eq _ hc
  exact (QuotientGroup.quotientBot (G := S)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e)

theorem nonempty_equiv_sl3_of_catalog_A2 {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (Q : TauCeti.PrimePower) {n : ℕ} (hQ2 : Q.p = 2) (hQe : Q.exponent = n) (hn : Odd n)
    (hd : d.1 = .A 2 Q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  rcases Q with ⟨p, ex, hp, hex⟩
  simp only at hQ2 hQe
  subst hQ2
  subst hQe
  haveI : Fact (Nat.Prime 2) := ⟨hp⟩
  have hcard : Nat.card (GaloisField 2 ex) % 3 = 2 := by
    rw [GaloisField.card 2 ex hex.ne']
    obtain ⟨m, rfl⟩ := hn
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 _ hv)).trans
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.pslEquivSL3 hcard)⟩

theorem nonempty_equiv_sl3_two_of_catalog_A1 {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hq7 : q.card = 7) (hd : d.1 = .A 1 q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1)) := by
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hq7' : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans hq7
  rcases q with ⟨p, ex, hp, hex⟩
  simp only at hq7'
  have hp7 : p = 7 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 (hq7' ▸ dvd_pow_self p hex.ne')
  subst hp7
  have hex1 : ex = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 7) (hq7'.trans (pow_one 7).symm)
  subst hex1
  haveI : Fact (Nat.Prime 7) := ⟨hp⟩
  let φ : GaloisField 7 1 ≃+* ZMod 7 := (GaloisField.equivZmodP 7).toRingEquiv
  obtain ⟨e3⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e4 : GL (Fin 3) (ZMod 2) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (MulEquiv.ofBijective _
      CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two).symm
  exact ⟨((((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hv)).trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))).trans e3.symm).trans
    e4).trans (CFSG.LargeExtraspecial.A2Mod.slEquiv CFSG.LargeExtraspecial.A2Mod.galoisFieldTwoOneEquiv.symm)⟩

theorem k541_odd (hKSML3 : KSML3) {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : CFSG.Open.IsComponentOf Ls ⊤) {n : ℕ} (hn : Odd n)
    (h : IsLThreeOfExp n (↥Ls ⧸ Subgroup.center ↥Ls)) :
    Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
  have hodd := odd_card_center_of_component hX hLs
  have hqs : CFSG.Open.IsQuasisimple ↥Ls := hLs.2.2
  rcases h with ⟨h1, d, q, hq7, hd, ⟨e⟩⟩ | ⟨-, d, Q, hQ2, hQe, hd, ⟨e⟩⟩
  · subst h1
    have hZ := (hKSML3 ↥Ls hqs d ⟨e⟩ hodd).1 (Or.inr ⟨q, hq7, hd⟩)
    exact nonempty_equiv_sl3_two_of_catalog_A1 d q hq7 hd (equiv_of_center_card_one hZ e)
  · have hZ := (hKSML3 ↥Ls hqs d ⟨e⟩ hodd).1 (Or.inl ⟨Q, hQ2, hQe ▸ hn, hd⟩)
    exact nonempty_equiv_sl3_of_catalog_A2 d Q hQ2 hQe hn hd (equiv_of_center_card_one hZ e)

theorem k541_of_even (hKSML3 : KSML3) (h : K541Even) : K541 := by
  intro X _ _ T hX Ls hLs hcomm n hn
  rcases Nat.even_or_odd n with he | ho
  · exact h X T hX Ls hLs hcomm n he hn
  · exact k541_odd hKSML3 hX hLs ho hn

end K541Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
