module

public import CFSG.GH74.GLS.C3.Layer1.EvenSE413
public import CFSG.GH74.GLS.C3.Statements
public import CFSG.GH74.GLS.Stage4.LocalSE

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG Equiv Equiv.Perm

section Alt

theorem exists_orderOf_four_alt (m : ℕ) (hm : m = 9 ∨ m = 10) :
    ∃ y : alternatingGroup (Fin m), orderOf y = 4 := by
  rcases hm with rfl | rfl
  · let σ : Perm (Fin 9) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5
    have hσ : σ ∈ alternatingGroup (Fin 9) := by
      rw [mem_alternatingGroup]
      simp [σ, Perm.sign_mul]
    refine ⟨⟨σ, hσ⟩, ?_⟩
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · intro h
      have h' : σ ^ 2 = 1 := by simpa using congrArg Subtype.val h
      revert h'
      decide
    · apply Subtype.ext
      show σ ^ 4 = 1
      decide
  · let σ : Perm (Fin 10) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5
    have hσ : σ ∈ alternatingGroup (Fin 10) := by
      rw [mem_alternatingGroup]
      simp [σ, Perm.sign_mul]
    refine ⟨⟨σ, hσ⟩, ?_⟩
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · intro h
      have h' : σ ^ 2 = 1 := by simpa using congrArg Subtype.val h
      revert h'
      decide
    · apply Subtype.ext
      show σ ^ 4 = 1
      decide

theorem three_dvd_card_alt (m : ℕ) (hm : m = 9 ∨ m = 10) :
    3 ∣ Nat.card (alternatingGroup (Fin m)) := by
  rcases hm with rfl | rfl <;>
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide

end Alt

section SE

theorem isStronglyEmbeddedOrder_of_isStronglyEmbedded' {X : Type*} [Group X] {M : Subgroup X}
    (h : IsStronglyEmbedded M) : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  have := h.2.2 g⁻¹ (fun hginv => hg (M.inv_mem_iff.mp hginv))
  simpa only [CFSG.conjugate, inv_inv] using this

theorem no_orderOf_four_psl2Model {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* CFSG.Theory.Comparator.PSL2Model n) {g : X} (hg : orderOf g = 4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have : Finite (CFSG.Theory.Comparator.PSL2Model n) := Finite.of_equiv X e.toEquiv
  have hg' : orderOf (e g) = 4 := by
    rw [← hg]
    exact orderOf_injective e.toMonoidHom e.injective g
  have hp : IsPGroup 2 (Subgroup.zpowers (e g)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg']; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨f⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  have hgQ : e g ∈ (Q : Subgroup (CFSG.Theory.Comparator.PSL2Model n)) := hQ (Subgroup.mem_zpowers _)
  obtain ⟨a, ha⟩ := f.surjective ⟨e g, hgQ⟩
  have ha2 : a ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  have hsq : (⟨e g, hgQ⟩ : ↥Q) ^ 2 = 1 := by
    rw [← ha, ← map_pow, ha2, map_one]
  have h2 : (e g) ^ 2 = 1 := congrArg Subtype.val hsq
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hg'] at this
  omega

variable {G : Type} [Group G] [Finite G]

theorem false_of_isStronglyEmbedded_alt
    (hG : C3Hyp G) {N : Subgroup G} (hN : IsStronglyEmbedded N)
    {m : ℕ} (hm : m = 9 ∨ m = 10) (e : ↥N ≃* alternatingGroup (Fin m)) : False := by
  have : IsSimpleGroup G := hG.kproper.1
  obtain ⟨y, hy⟩ := exists_orderOf_four_alt m hm
  have hy' : orderOf (e.symm y) = 4 := by
    rw [← hy]
    exact orderOf_injective e.symm.toMonoidHom e.symm.injective y
  have hg : orderOf ((e.symm y : ↥N) : G) = 4 := by
    rw [Subgroup.orderOf_coe]
    exact hy'
  have h3 : 3 ∣ Nat.card G := by
    have h1 : 3 ∣ Nat.card ↥N := by
      rw [Nat.card_congr e.toEquiv]
      exact three_dvd_card_alt m hm
    exact h1.trans (Subgroup.card_subgroup_dvd_card N)
  rcases CFSG.Milestones.bender_suzuki N (isStronglyEmbeddedOrder_of_isStronglyEmbedded' hN) with
    ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩ | ⟨n, hn, e'⟩
  · exact no_orderOf_four_psl2Model (by omega) e' hg
  · exact Stage4.three_not_dvd_card_of_szModel hn e' h3
  · have hrank : 3 ≤ CFSG.Open.twoRank G := by
      rw [← pRank_two_eq_twoRank, hG.pRank_eq_four]
      norm_num
    exact Bender.false_of_mulEquiv_psu3Model hn e' hrank hG.gen4

theorem false_of_samePattern_alt
    (hG : C3Hyp G) {N : Subgroup G} (hN : N ≠ ⊤)
    (heven : Even (Nat.card G)) {m : ℕ} (hm : m = 9 ∨ m = 10) (e : ↥N ≃* alternatingGroup (Fin m))
    (hpat : SameCentralizerOfInvolutionPattern G ↥N) : False := by
  rcases eq_top_or_isStronglyEmbedded_of_samePattern heven N hpat with h | h
  · exact hN h
  · exact false_of_isStronglyEmbedded_alt hG h hm e

end SE

end CFSG.GH74.GLS
