module

public import CFSG.Quasithin.EmptyFaithful.S152Y30
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Y29

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType
open scoped commutatorElement

namespace S152Y

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M : Subgroup G}

theorem exists_Y1_three_F4 (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205_F4)
    (c3 : Lemma15203Concl T Mc M) (hOm : Om4IsoStatement)
    (hThree : Case1517Three M (V154 T Mc M) (mBar0 T Mc M))
    (hYb : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M))
    (hexp : ∀ x ∈ Ys T Mc M, x ^ 3 = 1) : ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  obtain ⟨⟨e⟩, sh⟩ := three_iso hOm hThree
  obtain ⟨A₀, hA₀Y, hcard, hinvT, hact⟩ := exists_Abar h c3 hThree e sh hYb
  have hA : autOn M (V154 T Mc M) = mBar0 T Mc M := hThree.2.1
  have hTb : autOn T (V154 T Mc M) ≤ mBar0 T Mc M := hA ▸ Tb_le h
  have hT2 : IsPGroup 2 (autOn T (V154 T Mc M)) := (isSylowTwoOf_Tb h).2.1
  have hRe : ∀ x ∈ autOn (rcOf Mc M) (V154 T Mc M), x * x = 1 := fun x hx => by
    have hxT := A4.autOn_mono h.rc_le_T hx
    obtain ⟨k, hk⟩ := hT2 ⟨x, hxT⟩
    exact sh.two_elements x (hTb hxT) ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact exists_Y1_of_line_F4 hs h h5 hexp hA₀Y hcard hinvT hact hRe

theorem exists_Y1_i_F4 (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205_F4)
    (c3 : Lemma15203Concl T Mc M) (hOm : Om4IsoStatement)
    (hThree : Case1517Three M (V154 T Mc M) (mBar0 T Mc M)) (hi : Case15203i T Mc M) :
    ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  obtain ⟨hYb, hcent, -⟩ := hi
  obtain ⟨-, sh⟩ := three_iso hOm hThree
  have hK : Ys T Mc M ⊓ (piStar h).ker = ⊥ := imageOTwoQuot_inf_ker_eq_bot h hcent
  have hexp : ∀ x ∈ Ys T Mc M, x ^ 3 = 1 := by
    intro x hx
    have h1 : x ^ 3 ∈ Ys T Mc M ⊓ (piStar h).ker := by
      refine ⟨(Ys T Mc M).pow_mem hx 3, ?_⟩
      show piStar h (x ^ 3) = 1
      rw [map_pow]
      exact sh.exp_O _ (Data.piStar_mem_of_mem_Ys h hx)
    rw [hK, Subgroup.mem_bot] at h1
    exact h1
  exact exists_Y1_three_F4 hs h h5 c3 hOm hThree hYb hexp

theorem exists_Y1_ii_F4 (hs : Setting152 T Mc M) (h : Data T Mc M) (h5 : StageLemma15205_F4)
    (c3 : Lemma15203Concl T Mc M) (hOm : Om4IsoStatement) (hii : Case15203ii T Mc M) :
    ∃ Y₁ : Subgroup G, IsY1 T Mc M Y₁ := by
  obtain ⟨hThree, -, -, h4, h5', hP, -⟩ := hii
  have hYb : autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M) :=
    h5'.symm.trans h4.symm
  have hexp : ∀ x ∈ Ys T Mc M, x ^ 3 = 1 := fun x hx => by
    have := hP.2.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  exact exists_Y1_three_F4 hs h h5 c3 hOm hThree hYb hexp

end S152Y

end CFSG.Quasithin
