module

public import CFSG.ClassicalInvolution.Phan.PhanQ34Std
public import CFSG.ClassicalInvolution.Phan.PhanQ21QuadThree
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.Phan.PhanQ7Dict

public section

namespace CFSG.ClassicalInvolution.PhanQ

open SimpleGraph CFSG.ClassicalInvolution.Phan

section Graph

variable {V : Type*} {G : SimpleGraph V}

theorem quadNull_of_resolved
    (h : ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      (∃ e, G.Adj e a ∧ G.Adj e b ∧ G.Adj e c ∧ G.Adj e d) ∨
      (∃ c', G.Adj c' b ∧ G.Adj c' c ∧ G.Adj c' d ∧
        ∃ e, G.Adj e a ∧ G.Adj e b ∧ G.Adj e c' ∧ G.Adj e d) ∨
      (∃ d', G.Adj d' a ∧ G.Adj d' c ∧ G.Adj d' d ∧
        ∃ e, G.Adj e a ∧ G.Adj e b ∧ G.Adj e c ∧ G.Adj e d')) : QuadNull G := by
  intro a b c d hab hbc hcd hda
  rcases h a b c d hab hbc hcd hda with ⟨e, hea, heb, hec, hed⟩ |
    ⟨c', hc'b, hc'c, hc'd, e, hea, heb, hec', hed⟩ |
    ⟨d', hd'a, hd'c, hd'd, e, hea, heb, hec, hed'⟩
  · exact cycleHomotopic_quad_common hab hbc hcd hda hea.symm heb.symm hec.symm hed.symm
  · have hs := cycleHomotopic_path_swap hbc hcd hc'b.symm hc'd hc'c.symm
    have h1 : CycleHomotopic (triWalks G)
        (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a)
        (.cons hab (.cons hc'b.symm (.cons hc'd (.cons hda .nil)))) := by
      have := (hs.append_right (.cons hda .nil)).append_left (.cons hab .nil)
      simpa using this
    exact h1.trans (cycleHomotopic_quad_common hab hc'b.symm hc'd hda hea.symm heb.symm
      hec'.symm hed.symm)
  · have hs := cycleHomotopic_path_swap hcd hda hd'c.symm hd'a hd'd.symm
    have h1 : CycleHomotopic (triWalks G)
        (.cons hab (.cons hbc (.cons hcd (.cons hda .nil))) : G.Walk a a)
        (.cons hab (.cons hbc (.cons hd'c.symm (.cons hd'a .nil)))) := by
      have := hs.append_left (.cons hab (.cons hbc .nil))
      simpa using this
    exact h1.trans (cycleHomotopic_quad_common hab hbc hd'c.symm hd'a hea.symm heb.symm
      hec.symm hed'.symm)

end Graph

section Std

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.PhanD4

variable {p e : ℕ} [Fact p.Prime]

theorem quadNull_std (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) :
    QuadNull (ptGraph M.S) := by
  have h2 := two_ne_zero_gf hp2 e
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  refine quadNull_of_resolved fun a b c d hab hbc hcd hda => ?_
  obtain ⟨ga, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨gb, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨gc, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨gd, rfl⟩ := QuotientGroup.mk_surjective d
  have pab := (adj_iff M hp2 hq ga gb).1 hab
  have pbc := (adj_iff M hp2 hq gb gc).1 hbc
  have pcd := (adj_iff M hp2 hq gc gd).1 hcd
  have pda := (adj_iff M hp2 hq gd ga).1 hda
  have adj : ∀ (g h : spinGroup (quadPlus 4 (GaloisField p e))),
      ColP M.ε (g • z0 M.ε) (h • z0 M.ε) →
      (ptGraph M.S).Adj (g : _ ⧸ parab M.S {1, 2, 3}) (h : _ ⧸ parab M.S {1, 2, 3}) :=
    fun g h => (adj_iff M hp2 hq g h).2
  have lift : ∀ z : NPair M.ε, ∃ g : spinGroup (quadPlus 4 (GaloisField p e)),
      g • z0 M.ε = z := fun z => exists_smul_z0 h2 hodd M.hε M.h4 z
  rcases resolved_std M hp2 hq pab pbc pcd pda with ⟨z, h1, h2', h3, h4⟩ |
    ⟨z, h1, h2', h3, z', h4, h5, h6, h7⟩ | ⟨z, h1, h2', h3, z', h4, h5, h6, h7⟩
  · obtain ⟨gx, rfl⟩ := lift z
    exact Or.inl ⟨(gx : _ ⧸ parab M.S {1, 2, 3}), adj _ _ h1, adj _ _ h2', adj _ _ h3,
      adj _ _ h4⟩
  · obtain ⟨gf, rfl⟩ := lift z
    obtain ⟨gg, rfl⟩ := lift z'
    exact Or.inr (Or.inl ⟨(gf : _ ⧸ parab M.S {1, 2, 3}), adj _ _ h1, adj _ _ h2', adj _ _ h3,
      (gg : _ ⧸ parab M.S {1, 2, 3}), adj _ _ h4, adj _ _ h5, adj _ _ h6, adj _ _ h7⟩)
  · obtain ⟨gf, rfl⟩ := lift z
    obtain ⟨gg, rfl⟩ := lift z'
    exact Or.inr (Or.inr ⟨(gf : _ ⧸ parab M.S {1, 2, 3}), adj _ _ h1, adj _ _ h2', adj _ _ h3,
      (gg : _ ⧸ parab M.S {1, 2, 3}), adj _ _ h4, adj _ _ h5, adj _ _ h6, adj _ _ h7⟩)

end Std

end CFSG.ClassicalInvolution.PhanQ
