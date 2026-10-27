module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma5Rank
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma5Red
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5Par

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem case1295Three_of_F4 (h1222 : Stmt12_2_2_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hPar : ParabolicFact1295) : Case1295Three_F4 := by
  intro G _ _ T L V hcx V₁ K₁ hV₁ hU hLK hK hHz hK5 hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : (4 : ℕ) ≠ 3 := by norm_num
  have hTK : T ≤ Subgroup.normalizer (K₁ : Set G) :=
    hV₁.2.2.trans (normalizer_le_of_lOne_le_F4 h1222 h37 h38 h hn hV₁ hLK hK)
  have hXK : K₁ ⊔ T ≤ Subgroup.normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hTK
  have hsyl : QuasithinUnique.IsSylowTwoOf T (K₁ ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow le_sup_right
  have hTL₁ : T ≤ Subgroup.normalizer (lOne L V₁ : Set G) :=
    le_normalizer_lOne hyp.normalizes hV₁.2.2
  have hidem : oTwoUpper (lOne L V₁) = lOne L V₁ := by
    refine le_antisymm (oTwoUpper_le _) ?_
    show oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G)) ≤
      oTwoUpper (oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G)))
    exact Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩
  obtain ⟨e⟩ := lOne_quotient_mulEquiv_F4 h1222 h hn hV₁
  obtain ⟨P, hTP, hPX, hmax, ⟨y, hyP, hy3⟩, hPL, hPc⟩ :=
    hPar G (K₁ ⊔ T) K₁ T (lOne L V₁) le_sup_left hXK hsyl rfl hK5 hLK hTL₁ hidem ⟨e⟩ hnot

  have hK₁G₁ : K₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
    le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
  have hPG₁ : P ≤ Subgroup.normalizer (V₁ : Set G) := hPX.trans (sup_le hK₁G₁ hV₁.2.2)
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  refine ⟨P, ⟨⟨hTP, ?_⟩, ?_, ?_⟩, hPX, hPL, hPc⟩
  ·
    have hVT : V ≤ T := (hyp.le_and_normalizes_F4 h1222).1
    have hV₁2 : IsPGroup 2 V₁ := hyp.sylow.1.to_le (hV₁.1.trans hVT)
    have hV₁P : V₁ ≤ pCoreOf 2 P :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((hV₁.1.trans hVT).trans hTP) hPG₁ hV₁2
    intro hb
    rw [hb, le_bot_iff] at hV₁P
    have h1 := hV₁.2.1
    rw [hV₁P, Subgroup.card_bot] at h1
    norm_num at h1
  ·
    intro hPM
    have hyO : y ∈ oTwoUpper P :=
      Subgroup.subset_closure ⟨hyP, by rw [hy3]; decide⟩
    refine L1295C.false_of_order_three_F4 h1222 hcx hV₁ (hPM hyP) (hPG₁ hyP) hy3 fun l hl => ?_
    have := hPc (Subgroup.commutator_mem_commutator hl hyO)
    rwa [commutatorElement_def] at this
  ·
    intro Y hY hYP hYM
    rcases hmax Y hY.1 hYP with rfl | rfl
    · exact absurd hTM hYM
    · rfl

end CFSG.Quasithin.H13
