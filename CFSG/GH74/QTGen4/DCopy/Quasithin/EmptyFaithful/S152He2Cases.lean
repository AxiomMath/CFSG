module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.Der6DMain
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithfulMultiple.Facts15420Proof
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise
open CFSG.Quasithin.C1Pack12
open CFSG.Quasithin.EmptyFaithfulMultiple

theorem cases15212_of_prop134He_F4
    (h134 : Prop134E9He) (hA3 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], A3Orbits G)
    (h1416 : StageLemma1416) (h15208 : StageLemma15208_F4) (h15209 : StageNotation15209_F4)
    (insp : Insp15212) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), Setting152 T Mc M →
      ∀ H : Subgroup G, IsHStar T M H →
        conjClosure (oTwoUpper H) Mc = oTwoUpper H ∨
        Case15212ii T Mc (conjClosure (oTwoUpper H) Mc) ∨
        Case15212iii T Mc (conjClosure (oTwoUpper H) Mc) ∨
        Case15212He T Mc (conjClosure (oTwoUpper H) Mc) := by
  intro G _ _ T Mc M hs H hH
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hn := h15209 G T Mc M hs H hH
  have hHMc : H ≤ Mc := hn.le_mc
  have hsyl : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hTsyl : quasithinIsSylowTwo T := hs.qtfe.sylow
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKMc : oTwoUpper H ≤ Mc := hKH.trans hHMc
  have hX : IsXi T (oTwoUpper H) := Der6D.xi_of_iso hsyl hH.1.2 φ
  have hi : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 :=
    C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hi]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge 3 (bot_le : ⊥ ≤ oTwoUpper H) IsPGroup.of_bot
  have hPc : Nat.card P = 9 := by rw [hX.card_sylow (by norm_num) h3 hP, hi]
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hPc
    omega
  have hPMc : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hs.qtfe.mc_max.1
  have := hs.qtfe.simple
  have hsq : CFSG.SectionRank.IsSQTKCat ↥Mc :=
    (qtkeCore_of_cat hs.qtfe.nonabelian hs.qtfe.qtke).1 Mc hPMc
  have hsylMc : IsSylowTwoOf T Mc := isSylowTwoOf_of_quasithinIsSylowTwo hTsyl hTMc
  have hSQ : IsSQTKIn Mc :=
    sqtkGroup_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian hPMc
  have hmax : ∀ L : Subgroup G, L ∈ cComp Mc → quasithinIsMaximalLocal T L := fun L hL =>
    ((h1416 G T Mc hs.qtfe).2.1 L).mpr hL
  rcases h134 G Mc T (oTwoUpper H) P hsq hPMc hsylMc hKMc hX hi hP.le hP.isPGroup hPc with
    hN | ⟨L, hL, hq, hXL, hcases⟩
  ·
    left
    exact le_antisymm (conjClosure_le fun g hg k hk =>
      (Subgroup.mem_normalizer_iff.mp (hN hg) k).mp hk) (le_conjClosure _ _)
  · right
    obtain ⟨horb, hcase⟩ := hA3 G Mc T L hSQ hsylMc hL

    have hinv : T ≤ Subgroup.normalizer (L : Set G) →
        Mc ≤ Subgroup.normalizer (L : Set G) ∧ oTwoUpper H ≤ L := by
      intro hTL
      refine ⟨fun g hg => ?_, ?_⟩
      · have hmem : conjByElt g L ∈ conjSubgroupsBy Mc L := ⟨g, hg, rfl⟩
        rw [horb] at hmem
        obtain ⟨t, ht, hgt⟩ := hmem
        have h1 : conjByElt t L = L := A38.map_conj_eq_iff.mpr (hTL ht)
        have h2 : conjByElt g L = L := by rw [hgt]; exact h1
        exact A38.map_conj_eq_iff.mp h2
      · exact (hXL.trans (conjClosure_le fun g hg l hl =>
          (Subgroup.mem_normalizer_iff.mp (hTL hg) l).mp hl))
    rcases hcases with ⟨⟨t, htSN, htL, hPeq, -⟩, htype⟩ | ⟨hTL, htype⟩ | ⟨hTL, -, hcyc⟩ |
        ⟨hTL, htype⟩ | ⟨hMcL, hHeL⟩
    ·
      rcases hcase with hnorm | ⟨t', ht'T, ht'N, hpair, hcomm', -, -⟩
      · exact absurd (hnorm t htSN.1) htL
      · have hY := Der6D.conjClosure_eq_sup_of_orbit (hTMc ht'T) (horb.trans hpair)
        have hPL : P ⊓ L ≠ ⊥ := by
          intro h
          apply hPne
          rw [hPeq, h]
          simp [conjByElt]
        have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
          rcases htype with ⟨n, -, hn'⟩ | ⟨q, -, -, hq'⟩
          · exact facts15420_centerPSL _ 2 2 n hn'
          · exact facts15420_centerPSL _ 2 q 1 hq'
        have hKc := Der6D.conjClosure_eq_sup_of_pair hL hTMc ht'T hY hXL hq hcenter hP.le
          hP.isPGroup hPL
        refine Or.inr (Or.inl ⟨L, t', hmax L hL, hL, ht'T, ht'N, hKc, hcomm', ?_⟩)
        rcases htype with ⟨n, hn2, hn'⟩ | ⟨q, hq', hq2, hmod⟩
        · refine Or.inl ⟨n, hn2, ?_⟩
          obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField
            _ 2 2 n hn'
          exact ⟨(Der6D.oTwoQuotEquiv L).trans e⟩
        · refine Or.inr ⟨q, hq', hq2, ?_⟩
          have : Fact q.Prime := ⟨hq'⟩
          obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField
            _ 2 q 1 hmod
          let _ : Fintype (GaloisField q 1) := Fintype.ofFinite _
          have hcard : Fintype.card (GaloisField q 1) = Fintype.card (ZMod q) := by
            rw [← Nat.card_eq_fintype_card, GaloisField.card q 1 (by norm_num), ZMod.card q]
            simp
          exact ⟨(Der6D.oTwoQuotEquiv L).trans (e.trans
            (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
              (FiniteField.ringEquivOfCardEq hcard)))⟩
    ·
      obtain ⟨hMcL, hKL⟩ := hinv hTL
      have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
        rcases htype with h | h
        · exact facts15420_centerPSL _ 3 3 1 h
        · exact facts15420_centerSL33M11 _ (Or.inl h)
      have hKc := Der6D.conjClosure_eq_of_invariant hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne
      obtain ⟨n, hn2, hAut⟩ := insp G T Mc M H L hs hH ⟨φ⟩ hL hMcL hKc
        (by rcases htype with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h))
      rw [hKc]
      exact Or.inl ⟨hmax L hL, hL, n, hn2, hAut⟩
    ·
      exact absurd hcyc (Der6D.not_autCyclic hTsyl hsyl φ hX hP hPc)
    ·
      obtain ⟨hMcL, hKL⟩ := hinv hTL
      have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
        rcases htype with h | h | h
        · exact facts15420_centerSL33M11 _ (Or.inr h)
        · exact facts15420_centerPSL _ 4 2 1 h
        · exact facts15420_centerPSL _ 5 2 1 h
      have hKc := Der6D.conjClosure_eq_of_invariant hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne
      obtain ⟨n, hn2, hAut⟩ := insp G T Mc M H L hs hH ⟨φ⟩ hL hMcL hKc
        (by rcases htype with h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
      rw [hKc]
      exact Or.inl ⟨hmax L hL, hL, n, hn2, hAut⟩
    ·
      have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTMc.trans hMcL
      have hKL : oTwoUpper H ≤ L := hXL.trans (conjClosure_le fun g hg l hl =>
        (Subgroup.mem_normalizer_iff.mp (hTL hg) l).mp hl)
      have hcenter : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
        facts15420_centerHe _ hHeL
      have hKc := Der6D.conjClosure_eq_of_invariant hL hMcL hKL hq hcenter hP.le hP.isPGroup hPne
      obtain ⟨e⟩ := hHeL
      rw [hKc]
      exact Or.inr (Or.inr ⟨hmax L hL, hL, ⟨(Der6D.oTwoQuotEquiv L).trans e⟩⟩)

end CFSG.Quasithin
