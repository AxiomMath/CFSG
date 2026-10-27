module

public import CFSG.GH74.Uniqueness.Section122Struct
public import CFSG.GH74.Uniqueness.Section122Inv

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma122
    (S : ZDSetup X Z M) : Lemma122Stmt Z M := by
  intro c
  obtain ⟨n, i, hi, hn, hBL, ⟨Q, hQ⟩, hinv⟩ := S.lemma122a c
  have hZM := S.inter_eq_zHull_diff c hBL hQ hinv
  have hab := S.isElemAbelian_zHull c hBL hQ hinv
  have hcardM := S.card_zHull c hBL hQ hinv
  have hcomm : ∀ x ∈ zHull Z M, ∀ y ∈ zHull Z M, x * y = y * x := by
    intro x hx y hy
    have := hab.1
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥(zHull Z M))).comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h4 : 4 ≤ Nat.card ↥(zHull Z M) := by
    rw [hcardM]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hV : productInvolutions Z = Z :=
    S.prodDisc.productInvolutions_eq S.invariant hcomm hZM h4
  obtain ⟨hk1, hk2, hk3, hk4⟩ := S.lemma122f c hBL hQ hinv
  exact ⟨n, i,
    { hi := hi
      hn := hn
      bender := hBL
      borel := ⟨Q, hQ⟩
      invol := hinv
      m_abelian := hab
      m_card := hcardM
      m_le := (closure_le _).mpr (S.inter_subset_L c)
      m_normal := fun g hg x hx =>
        (mem_normalizer_iff.mp (le_normalizer_zHull S.invariant M hg) x).mp hx
      zM_eq := hZM
      prod_eq := hV
      normalizer_eq := S.normalizer_L_eq c hBL hQ
      centralizer_le := S.centralizer_L_le_D c
      nM_eq := S.nM_eq_L c hBL hQ
      dihedral := S.prodDisc.lemma122e S.invariant hV hab c.hz c.hzM
      k_eq := hk1
      k_eq' := hk2
      k_cyclic := hk3
      k_card := hk4 }⟩

end CFSG.GH74.Uniqueness
