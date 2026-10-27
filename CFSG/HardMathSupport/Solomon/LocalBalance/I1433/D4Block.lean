module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.D4Field
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthIdent
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SL3Image
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddTop
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3Bridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294LayerLieQ
import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false


theorem d4BlockType_holds : D4BlockType := by
  intro F _ _ S _ _ hs hna ⟨e⟩ x hx J hJ hxJ q hq
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨n, hℓ, hcardF⟩ := FiniteField.card F (ringChar F)
  have hFcard : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcardF]
  have hmodel : StatedClassicalModel S .POmegaPlus 4 (ringChar F) (n : ℕ) :=
    ⟨⟨hℓ, n.pos, le_rfl⟩, F, inferInstance, inferInstance, hFcard, ⟨e⟩⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  by_cases h3 : ringChar F = 3
  · exfalso
    obtain ⟨d, hd, ⟨e'⟩⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_tauCeti_index_of_statedClassicalModel hmodel
        (by simp [CFSG.HardMathSupport.Dickson.Sec6.I1431.TauCetiDuplicate])
    have hchev : IsChevOfChar 3 S :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.isChevOfChar_of_characteristic
        (hd.trans h3) e'
    have hx3 : x ^ 3 = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hN := LieComp.noThreeComponents_of_conj YS08.LieQ.lieQConstrainedInner_three_holds hs hna
      hchev hx1 hx3
    apply hN J
    show GLAPComponent 3 (fixSubgroup (MulAut.conj x)) J
    rw [CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj]
    exact hJ
  · obtain ⟨K, E, _, _, _, _, m, hcardK, h3m, h2m, hcases⟩ :=
      orth_blockIdentification .POmegaPlus (Or.inr (Or.inl rfl)) S 4 (ringChar F) (n : ℕ) hmodel
        h3 x hx J hJ hxJ
    have hKF : Nat.card K = Nat.card F := by rw [hcardK, hFcard]
    have hm8 : 2 * m ≤ 8 := by simpa using h2m
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hx1
      rcases hcases with ⟨-, φ, ω, g, -, -, -, -, -, -, hφg⟩ |
        ⟨-, φ, ω, g, -, -, -, -, -, -, hφg⟩
      · have hg : g = 1 := Subsingleton.elim _ _
        rw [← hφg, hg, map_one]
        rfl
      · have hg : g = 1 := Subsingleton.elim _ _
        rw [← hφg, hg, map_one]
        rfl
    have hm3 : m = 3 := by
      obtain ⟨k, rfl⟩ := h3m
      omega
    subst hm3
    rcases hcases with ⟨hE, φ, ω, g, hsurj, hker, -, hω1, hω3, hg, hφg⟩ |
      ⟨hE, φ, ω, g, hsurj, hker, -, hω1, hω3, hg, hφg⟩
    · have hgx : φ g ≠ 1 := fun h => hx1 (by rw [← hφg, h]; rfl)
      have h := isSL3EpsOver_of_statedSL_image φ hsurj hker ω hω1 hω3 g hg hgx
      rwa [hE, hKF] at h
    · have hgx : φ g ≠ 1 := fun h => hx1 (by rw [← hφg, h]; rfl)
      have h := isSL3EpsOver_of_statedSU_image hE φ hsurj hker ω hω1 hω3 g hg hgx
      rwa [hKF] at h

theorem d4FieldSharp_holds : D4FieldSharp :=
  d4FieldSharp_of_blockType d4BlockType_holds

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
