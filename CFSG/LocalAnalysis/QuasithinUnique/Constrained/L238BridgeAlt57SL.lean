module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank

namespace Bridge

theorem injective_of_surjective_of_simple {Γ H : Type} [Group Γ] [Group H] [IsSimpleGroup Γ]
    [Nontrivial H] (π : Γ →* H) (hπ : Function.Surjective π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · have h1 : g ∈ π.ker := hg
    rw [h, Subgroup.mem_bot] at h1
    exact h1
  · exfalso
    obtain ⟨a, ha⟩ := exists_ne (1 : H)
    obtain ⟨x, rfl⟩ := hπ a
    exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x))

theorem card_sl_two_field (n : ℕ) [NeZero n] (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) K) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  let _ := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_SL_field, hK']
  simp

theorem center_sl_zmod2 (n : ℕ) [NeZero n] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  have hn : Fintype.card (Fin n) ≠ 0 := Fintype.card_pos.ne'
  have hr1 : r = 1 := by
    rcases h01 r with h0 | h1
    · rw [h0, zero_pow hn] at hr
      exact absurd hr (by decide)
    · exact h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have h2 : (Matrix.scalar (Fin n) r : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)) := by
    rw [hr1, map_one]
  exact hA'.symm.trans h2

theorem isSimple_sl_zmod2 (n : ℕ) (hn : 3 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  have : NeZero n := ⟨by omega⟩
  have h := (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := n) (by omega)
    (Or.inl hn)).2.1
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq (center_sl_zmod2 n)).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem card_sl4 : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [card_sl_two_field 4 (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]), Fin.prod_univ_four]
  norm_num

theorem card_sl5 : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [card_sl_two_field 5 (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card]), Fin.prod_univ_five]
  norm_num

theorem noAlt57Image_sl (n : ℕ) (hn : 3 ≤ n)
    (hc : ∀ m : ℕ, (m = 5 ∨ m = 7) →
      Nat.card (alternatingGroup (Fin m)) ≠ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    NoAlt57Image ↥(StatedSL n (ZMod 2)) := by
  intro H _ π hπ L hL _hsq m hm ⟨e⟩
  have hSL := isSimple_sl_zmod2 n hn
  have hS : IsSimpleGroup ↥(StatedSL n (ZMod 2)) :=
    (specialLinearGroupEquivStatedSL n (ZMod 2)).symm.isSimpleGroup
  have hAm : 5 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have : IsSimpleGroup (alternatingGroup (Fin m)) := alt_isSimple hAm
  have : Nontrivial (alternatingGroup (Fin m)) := IsSimpleGroup.toNontrivial
  have : Nontrivial ↥L := e.toEquiv.nontrivial
  obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
  have : Nontrivial H := ⟨⟨l, 1, fun h => hl (Subtype.ext h)⟩⟩
  have hinj : Function.Injective π := injective_of_surjective_of_simple π hπ
  let eπ : ↥(StatedSL n (ZMod 2)) ≃* H := MulEquiv.ofBijective π ⟨hinj, hπ⟩
  have : IsSimpleGroup H := eπ.symm.isSimpleGroup
  have := hL
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with h | h
  · have h1 : (l : H) ∈ (⊥ : Subgroup H) := by rw [← h]; exact l.2
    exact hl (Subtype.ext (Subgroup.mem_bot.1 h1))
  · have h1 : Nat.card ↥L = Nat.card H := by rw [h]; exact Subgroup.card_top
    have h2 : Nat.card ↥L = Nat.card (alternatingGroup (Fin m)) := Nat.card_congr e.toEquiv
    have h3 : Nat.card H = Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
      (Nat.card_congr eπ.toEquiv).symm.trans
        (Nat.card_congr (specialLinearGroupEquivStatedSL n (ZMod 2)).toEquiv).symm
    exact hc m hm (h2.symm.trans (h1.trans h3))

theorem noAlt57Image_sl4 : NoAlt57Image ↥(StatedSL 4 (ZMod 2)) :=
  noAlt57Image_sl 4 (by norm_num) fun m hm => by
    rw [card_sl4]
    rcases hm with rfl | rfl
    · rw [card_alt_five]; norm_num
    · rw [card_alt_seven]; norm_num

theorem noAlt57Image_sl5 : NoAlt57Image ↥(StatedSL 5 (ZMod 2)) :=
  noAlt57Image_sl 5 (by norm_num) fun m hm => by
    rw [card_sl5]
    rcases hm with rfl | rfl
    · rw [card_alt_five]; norm_num
    · rw [card_alt_seven]; norm_num

end Bridge

end CFSG.QuasithinUnique
