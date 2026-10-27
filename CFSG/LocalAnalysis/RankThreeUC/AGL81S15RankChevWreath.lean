module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevProd

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevProof

open CFSG.Open CFSG.SectionRank RegularWreathProduct

section Wreath

variable {P : Type*} [Group P] {Q : Type*} [Group Q] {p : ℕ}

@[expose] def wreathBase (P : Type*) [Group P] (Q : Type*) [Group Q] : (Q → P) →* P ≀ᵣ Q where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp [RegularWreathProduct.mul_def]

theorem wreathBase_injective (P : Type*) [Group P] (Q : Type*) [Group Q] :
    Function.Injective (wreathBase P Q) := fun _ _ h => congrArg RegularWreathProduct.left h

theorem left_eq_one_of_commute [Fact p.Prime] [Finite Q] (hQ : Nat.card Q = p) {x c : P ≀ᵣ Q}
    (hx : x.right ≠ 1) (hc : c.right = 1) (hcx : c * x = x * c) (h1 : c.left 1 = 1) :
    c.left = 1 := by
  have key : ∀ y, c.left y * x.left y = x.left y * c.left (x.right⁻¹ * y) := by
    intro y
    have h := congrArg (fun w : P ≀ᵣ Q => w.left y) hcx
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply, hc, inv_one, one_mul] at h
    exact h
  have hn : ∀ n : ℕ, c.left (x.right ^ n) = 1 := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      have h := key (x.right ^ (n + 1))
      have e : x.right⁻¹ * x.right ^ (n + 1) = x.right ^ n := by
        rw [pow_succ']
        exact inv_mul_cancel_left _ _
      rw [e, ih, mul_one] at h
      exact mul_right_cancel (h.trans (one_mul _).symm)
  funext y
  obtain ⟨n, hy⟩ := (Submonoid.mem_powers_iff y x.right).1 (mem_powers_of_prime_card hQ hx)
  rw [← hy]
  exact hn n

variable [Finite P] [Fintype Q] [Fact p.Prime]

theorem pow_succ_le_pow_mul {m : ℕ} (hm : 1 ≤ m) : p ^ (m + 1) ≤ p ^ (p * m) :=
  Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by
    have h2 := (Fact.out : p.Prime).two_le
    nlinarith)

theorem card_le_of_isElemAbelian_wreath (hQ : Fintype.card Q = p)
    (hm : 1 ≤ pRank p (⊤ : Subgroup P)) {E : Subgroup (P ≀ᵣ Q)} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (p * pRank p (⊤ : Subgroup P)) := by
  have hcardQ : Nat.card Q = p := by rw [Nat.card_eq_fintype_card, hQ]
  let ρ : E →* Q := (rightHom (D := P) (Q := Q)).comp E.subtype
  have hρ : ∀ x : E, ρ x = (x : P ≀ᵣ Q).right := fun x => rfl
  have hcomm : ∀ a b : ρ.ker, a * b = b * a := fun a b =>
    Subtype.ext (hE.1.is_comm.comm a.1 b.1)
  have hpow : ∀ a : ρ.ker, a ^ p = 1 := fun a =>
    Subtype.ext (Subtype.ext (by simpa using hE.2 _ a.1.2))
  have hkr : ∀ k : ρ.ker, ((k.1 : E) : P ≀ᵣ Q).right = 1 := fun k => (hρ k.1).symm.trans k.2
  have hidx : Nat.card ρ.ker * ρ.ker.index = Nat.card E := Subgroup.card_mul_index ρ.ker
  have hpm : pRank p (⊤ : Subgroup (Q → P)) = p * pRank p (⊤ : Subgroup P) := by
    rw [pRank_pi, Finset.sum_const, Finset.card_univ, hQ, smul_eq_mul]
  by_cases hA : ∀ x : E, (x : P ≀ᵣ Q).right = 1
  ·
    have hindex : ρ.ker.index = 1 := by
      rw [Subgroup.index_ker]
      have : ρ.range = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        rintro _ ⟨x, rfl⟩
        exact (hρ x).trans (hA x)
      rw [this, Subgroup.card_bot]
    let χ : ρ.ker →* (Q → P) :=
      { toFun := fun k => ((k.1 : E) : P ≀ᵣ Q).left
        map_one' := rfl
        map_mul' := fun k k' => by
          ext y
          have h1 := hkr k
          simp only [Subgroup.coe_mul, RegularWreathProduct.mul_left, Pi.mul_apply, h1, inv_one,
            one_mul] }
    have hχ : Function.Injective χ := by
      intro k k' h
      apply Subtype.ext
      apply Subtype.ext
      apply RegularWreathProduct.ext
      · exact h
      · rw [hkr k, hkr k']
    have hle := card_le_pow_pRank_of_injective hcomm hpow χ hχ
    rw [hpm] at hle
    rw [← hidx, hindex, mul_one]
    exact hle
  ·
    push Not at hA
    obtain ⟨x, hx⟩ := hA
    let χ : ρ.ker →* P :=
      { toFun := fun k => ((k.1 : E) : P ≀ᵣ Q).left 1
        map_one' := rfl
        map_mul' := fun k k' => by
          have h1 := hkr k
          simp only [Subgroup.coe_mul, RegularWreathProduct.mul_left, Pi.mul_apply, h1, inv_one,
            one_mul] }
    have hχ : Function.Injective χ := by
      rw [injective_iff_map_eq_one]
      intro k hk
      have hcx : ((k.1 : E) : P ≀ᵣ Q) * (x : P ≀ᵣ Q) = (x : P ≀ᵣ Q) * ((k.1 : E) : P ≀ᵣ Q) :=
        congrArg Subtype.val (hE.1.is_comm.comm k.1 x)
      have hl := left_eq_one_of_commute hcardQ hx (hkr k) hcx hk
      apply Subtype.ext
      apply Subtype.ext
      apply RegularWreathProduct.ext
      · exact hl
      · exact hkr k
    have hle := card_le_pow_pRank_of_injective hcomm hpow χ hχ
    have hind : ρ.ker.index ≤ p := by
      rw [Subgroup.index_ker]
      calc Nat.card ρ.range ≤ Nat.card Q := Subgroup.card_le_card_group _
        _ = p := hcardQ
    calc Nat.card E = Nat.card ρ.ker * ρ.ker.index := hidx.symm
      _ ≤ p ^ pRank p (⊤ : Subgroup P) * p := Nat.mul_le_mul hle hind
      _ = p ^ (pRank p (⊤ : Subgroup P) + 1) := (pow_succ _ _).symm
      _ ≤ p ^ (p * pRank p (⊤ : Subgroup P)) := pow_succ_le_pow_mul hm

theorem pRank_wreath (hQ : Fintype.card Q = p) (hm : 1 ≤ pRank p (⊤ : Subgroup P)) :
    pRank p (⊤ : Subgroup (P ≀ᵣ Q)) = p * pRank p (⊤ : Subgroup P) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  apply le_antisymm
  · exact pRank_le hp1 (fun E _ hE => card_le_of_isElemAbelian_wreath hQ hm hE)
  · have hpm : pRank p (⊤ : Subgroup (Q → P)) = p * pRank p (⊤ : Subgroup P) := by
      rw [pRank_pi, Finset.sum_const, Finset.card_univ, hQ, smul_eq_mul]
    rw [← hpm]
    exact pRank_top_le_of_injective hp1 _ (wreathBase_injective P Q)

end Wreath

end RankChevProof

end CFSG.LocalAnalysis.RankThreeUC.S15
