module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndCfg
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.FourFive

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Types

variable {V : Type} [CommGroup V] [Finite V]

theorem types_of_classX (hV : ∀ v : V, v ^ 2 = 1) {Y : Subgroup (MulAut V)} (hperf : ⁅Y, Y⁆ = Y)
    (hc : Subgroup.center ↥Y = ⊥) (hX : InClassX ↥(yuHol Y)) :
    (∃ f : ℕ, 2 ≤ f ∧ YSL Y f) ∨ ∃ m : ℕ, 7 ≤ m ∧ Odd m ∧ YAlt Y m := by
  classical
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  obtain ⟨hshort, halt | hsl⟩ := hX
  ·
    obtain ⟨n, hn1, φ, ψ, hsum, hsurj, hker, hequiv⟩ := halt
    have hθs := yuTheta_surjective Y φ hV
    have hRc := yuTheta_ker_le_center Y φ hV hshort
    have hker1 : (yuTheta Y φ).ker = ⊥ := by
      rw [eq_bot_iff]
      exact hRc.trans hc.le
    have hθi : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hker1
    let θ : ↥Y ≃* alternatingGroup (Fin (2 * n + 1)) :=
      MulEquiv.ofBijective (yuTheta Y φ) ⟨hθi, hθs⟩
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn : n = 1 := by omega
      subst hn
      have hcard : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      have : Nontrivial (alternatingGroup (Fin (2 * 1 + 1))) :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega)
      exact false_of_perfect_small (Γ := ↥Y) (A := alternatingGroup (Fin (2 * 1 + 1)))
        (by omega) (yuTheta Y φ) hθs
    by_cases hn3 : 3 ≤ n
    · right
      exact ⟨2 * n + 1, by omega, odd_two_mul_add_one n, ⟨θ⟩⟩
    · left
      have hn : n = 2 := by omega
      subst hn
      obtain ⟨e⟩ := sl2_four_equiv_alt5
      exact ⟨2, le_rfl, ⟨θ.trans e.symm⟩⟩
  ·
    obtain ⟨n, hn1, φ, ψ, hsurj, hker, hequiv⟩ := hsl
    have hθs := yuTheta_surjective Y φ hV
    have hRc := yuTheta_ker_le_center Y φ hV hshort
    have hker1 : (yuTheta Y φ).ker = ⊥ := by
      rw [eq_bot_iff]
      exact hRc.trans hc.le
    have hθi : Function.Injective (yuTheta Y φ) := (MonoidHom.ker_eq_bot_iff _).mp hker1
    let θ : ↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n) :=
      MulEquiv.ofBijective (yuTheta Y φ) ⟨hθi, hθs⟩
    have hn2 : 2 ≤ n := by
      by_contra h
      have hn : n = 1 := by omega
      subst hn
      have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
          GaloisField.card 2 1 (by norm_num)]
        norm_num
      have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega)
      exact false_of_perfect_small (Γ := ↥Y) (by omega) (yuTheta Y φ) hθs
    exact Or.inl ⟨n, hn2, ⟨θ⟩⟩

variable {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.types (hM4 : SchurMultL2Two) (hV : ∀ v : V, v ^ 2 = 1) (h : EndCfg4 G T Y) :
    (∃ f : ℕ, 2 ≤ f ∧ YSL Y f) ∨ YSL5 Y ∨ ∃ m : ℕ, 7 ≤ m ∧ Odd m ∧ YAlt Y m := by
  have hperf : ⁅Y, Y⁆ = Y := h.adm.hperf
  rcases h.hcls2 with hX | ⟨n, hn, hΩ⟩
  · rcases emb_four_five_core Y hM4 hV hperf hX with hc | ⟨hiso, -, -, -⟩
    · rcases types_of_classX hV hperf hc hX with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl hiso)
  · obtain ⟨-, θ, -⟩ := hΩ
    exact Or.inl ⟨2 * n, by omega, ⟨θ⟩⟩

end Types

end CFSG.CGT.PushingUpLit.CGT6
