module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem statedClassicalModel_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : LieModel G t n p f) : StatedClassicalModel G t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h ht

theorem ringChar_ne_two_of_card_eq_pow {K : Type*} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) : ringChar K ≠ 2 := by
  intro h2
  have : Fintype K := Fintype.ofFinite K
  have hdvd : ringChar K ∣ Nat.card K :=
    ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero K)
  rw [h2, hK] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
    (Nat.prime_two.dvd_of_dvd_pow hdvd)).symm

theorem isCyclic_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    IsCyclic G := by
  rcases Nat.lt_or_ge (Nat.card G) 2 with h1 | h1
  · have : Subsingleton G := Finite.card_le_one_iff_subsingleton.1 (by omega)
    exact isCyclic_of_subsingleton
  · exact isCyclic_of_prime_card (p := 2) (le_antisymm h h1)

theorem card_le_two_of_forall_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*}
    [Field K] {G : Type*} [Group G] {φ : G →* GL ι K} (hφ : Function.Injective φ)
    (h : ∀ g, ∃ u : K, u ^ 2 = 1 ∧ ((φ g : GL ι K) : Matrix ι ι K) = Matrix.scalar ι u) :
    Nat.card G ≤ 2 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · have : Subsingleton G := ⟨fun a b => hφ (Matrix.GeneralLinearGroup.ext fun j => hι.elim j)⟩
    exact (Finite.card_le_one_iff_subsingleton.2 this).trans (by norm_num)
  ·
    have key : ∀ g, ((φ g : GL ι K) : Matrix ι ι K) =
        Matrix.scalar ι (((φ g : GL ι K) : Matrix ι ι K) i i) ∧
        (((φ g : GL ι K) : Matrix ι ι K) i i = 1 ∨
          ((φ g : GL ι K) : Matrix ι ι K) i i = -1) := fun g => by
      obtain ⟨u, hu, hg⟩ := h g
      have hii : ((φ g : GL ι K) : Matrix ι ι K) i i = u := by
        rw [hg, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      rw [hii]
      exact ⟨hg, mul_self_eq_one_iff.1 (by rw [← pow_two]; exact hu)⟩
    have hF : Function.Injective fun g : G =>
        decide (((φ g : GL ι K) : Matrix ι ι K) i i = 1) := by
      intro a b hab
      have hiff := decide_eq_decide.1 hab
      have hab' : ((φ a : GL ι K) : Matrix ι ι K) i i = ((φ b : GL ι K) : Matrix ι ι K) i i := by
        by_cases hx : ((φ a : GL ι K) : Matrix ι ι K) i i = 1
        · rw [hx, hiff.1 hx]
        · have hy : ¬((φ b : GL ι K) : Matrix ι ι K) i i = 1 := fun hy => hx (hiff.2 hy)
          rw [(key a).2.resolve_left hx, (key b).2.resolve_left hy]
      apply hφ
      exact Units.ext ((key a).1.trans (hab' ▸ (key b).1.symm))
    calc Nat.card G ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hF
      _ = 2 := by simp

theorem ker_comp_mk' {H Q : Type*} [Group H] [Group Q] (N : Subgroup H) [N.Normal]
    (e : H ⧸ N ≃* Q) : (e.toMonoidHom.comp (QuotientGroup.mk' N)).ker = N := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_eq_one_iff _
    e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end CFSG.LieType.Steinberg
