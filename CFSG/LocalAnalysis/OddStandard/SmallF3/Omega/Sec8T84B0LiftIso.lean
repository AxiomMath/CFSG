module

public import Mathlib.GroupTheory.FiniteAbelian.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

theorem exists_mulEquiv_zmod4 {A : Type*} [CommGroup A] [Finite A] (h4 : ∀ x : A, x ^ 4 = 1)
    (hcard : Nat.card A = 256) (hsq : Nat.card (powMonoidHom 2 : A →* A).range = 16) :
    Nonempty (A ≃* Multiplicative (Fin 4 → ZMod 4)) := by
  classical
  obtain ⟨ι, hι, n, hn_gt, ⟨φ⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  haveI : Fintype ι := hι
  let P := (i : ι) → Multiplicative (ZMod (n i))
  have hdvd : ∀ i, n i ∣ 4 := by
    intro i
    let y : P := Pi.mulSingle (M := fun j => Multiplicative (ZMod (n j))) i
      (Multiplicative.ofAdd (1 : ZMod (n i)))
    have hy : y ^ 4 = 1 := by
      have hx : (φ.symm y) ^ 4 = 1 := h4 (φ.symm y)
      calc y ^ 4 = (φ (φ.symm y)) ^ 4 := by rw [φ.apply_symm_apply]
        _ = φ ((φ.symm y) ^ 4) := (map_pow (φ.toMonoidHom) (φ.symm y) 4).symm
        _ = φ 1 := by rw [hx]
        _ = 1 := map_one (φ.toMonoidHom)
    have hcoord : (Multiplicative.ofAdd (1 : ZMod (n i))) ^ 4 = 1 := by
      have h := congrArg (Pi.evalMonoidHom (f := fun j => Multiplicative (ZMod (n j))) i) hy
      rw [map_pow, map_one] at h
      rwa [show (Pi.evalMonoidHom (f := fun j => Multiplicative (ZMod (n j))) i) y
        = Multiplicative.ofAdd (1 : ZMod (n i)) from Pi.mulSingle_eq_same i _] at h
    rw [← ZMod.addOrderOf_one (n i), ← orderOf_ofAdd_eq_addOrderOf (1 : ZMod (n i))]
    exact orderOf_dvd_iff_pow_eq_one.mpr hcoord
  have hn24 : ∀ i, n i = 2 ∨ n i = 4 := by
    intro i
    have hdvd' : n i ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact hdvd i
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hdvd'
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hgt := hn_gt i
      rw [pow_zero] at hk'
      omega
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with h | h
    · left; rw [hk', h]; norm_num
    · right; rw [hk', h]; norm_num
  let K : Subgroup A := (powMonoidHom 2 : A →* A).ker
  have hKpow : Nat.card K = 2 ^ Nat.card ι := by
    have hfactor : ∀ m : ℕ, (m = 2 ∨ m = 4) →
        Nat.card {b : Multiplicative (ZMod m) // b ^ 2 = 1} = 2 := by
      rintro m (rfl | rfl) <;> rw [Nat.card_eq_fintype_card] <;> decide
    have hmem : ∀ x : A, x ∈ K ↔ x ^ 2 = 1 := by
      intro x
      show x ∈ (powMonoidHom 2 : A →* A).ker ↔ x ^ 2 = 1
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
    calc
      Nat.card K = Nat.card {x : A // x ^ 2 = 1} :=
        Nat.card_congr (Equiv.subtypeEquivRight hmem)
      _ = Nat.card {y : P // y ^ 2 = 1} := by
        apply Nat.card_congr
        refine
          { toFun := fun x => ⟨φ x, ?_⟩
            invFun := fun y => ⟨φ.symm y, ?_⟩
            left_inv := fun x => Subtype.ext (φ.left_inv x)
            right_inv := fun y => Subtype.ext (φ.right_inv y) }
        · change (φ.toMonoidHom x) ^ 2 = 1
          rw [← map_pow (φ.toMonoidHom), x.2, map_one (φ.toMonoidHom)]
        · change (φ.symm.toMonoidHom y) ^ 2 = 1
          rw [← map_pow (φ.symm.toMonoidHom), y.2, map_one (φ.symm.toMonoidHom)]
      _ = Nat.card ((i : ι) → {b : Multiplicative (ZMod (n i)) // b ^ 2 = 1}) := by
        apply Nat.card_congr
        refine (Equiv.subtypeEquivRight ?_).trans Equiv.subtypePiEquivPi
        intro y
        constructor
        · intro h i; exact congr_fun h i
        · intro h; funext i; exact h i
      _ = ∏ i, Nat.card {b : Multiplicative (ZMod (n i)) // b ^ 2 = 1} := Nat.card_pi
      _ = ∏ i, 2 := Finset.prod_congr rfl fun i _ => hfactor (n i) (hn24 i)
      _ = 2 ^ Nat.card ι := by
        rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hK16 : Nat.card K = 16 := by
    have h := Subgroup.card_ker_mul_card_range (powMonoidHom 2 : A →* A)
    rw [hsq, hcard] at h
    have h' : Nat.card K * 16 = 16 * 16 := by rw [h]
    exact mul_right_cancel₀ (by norm_num : (16 : ℕ) ≠ 0) h'
  have hιcard : Nat.card ι = 4 := by
    have hpow : 2 ^ Nat.card ι = 2 ^ 4 := by
      have : 2 ^ Nat.card ι = 16 := hKpow.symm.trans hK16
      rw [this]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hprod_n : ∏ i, n i = 256 := by
    have h1 : Nat.card P = ∏ i, n i := by
      rw [Nat.card_pi]
      exact Finset.prod_congr rfl fun i _ =>
        (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod (n i))
    have h2 : Nat.card P = Nat.card A := (Nat.card_congr φ.toEquiv).symm
    rw [h2, hcard] at h1
    exact h1.symm
  have hn4 : ∀ i, n i = 4 := by
    let e : ι → ℕ := fun i => if n i = 4 then 2 else 1
    have he_le : ∀ i, e i ≤ 2 := by
      intro i; dsimp [e]; split <;> omega
    have hne : ∀ i, n i = 2 ^ e i := by
      intro i
      rcases hn24 i with h | h
      · dsimp [e]; rw [if_neg (by rw [h]; norm_num), h]; norm_num
      · dsimp [e]; rw [if_pos h, h]; norm_num
    have hprod_pow : ∏ i, n i = 2 ^ (∑ i, e i) := by
      rw [show n = (fun i => 2 ^ e i) from funext fun i => hne i,
        Finset.prod_pow_eq_pow_sum]
    have hsum : ∑ i, e i = 8 := by
      have h8 : 2 ^ (∑ i, e i) = 2 ^ 8 := by rw [← hprod_pow, hprod_n]; norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h8
    have hall : ∀ i, e i = 2 := by
      have h8 : ∑ i, e i = ∑ i : ι, 2 := by
        rw [hsum, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hιcard]
        norm_num
      simpa using (Finset.sum_eq_sum_iff_of_le (fun i _ => he_le i)).mp h8
    intro i
    rw [hne i, hall i]; norm_num
  have hcardι : Fintype.card ι = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hιcard
  let e : ι ≃ Fin 4 := Fintype.equivFinOfCardEq hcardι
  let ψ : P ≃* ((i : ι) → Multiplicative (ZMod 4)) :=
    MulEquiv.piCongrRight
      (fun i => AddEquiv.toMultiplicative (ZMod.ringEquivCongr (hn4 i)).toAddEquiv)
  let ρ : ((i : ι) → Multiplicative (ZMod 4)) ≃*
      ((j : Fin 4) → Multiplicative (ZMod 4)) :=
    { toFun := fun f j => f (e.symm j)
      invFun := fun g i => g (e i)
      left_inv := fun f => by funext i; simp
      right_inv := fun g => by funext j; simp
      map_mul' := fun f g => rfl }
  let τ : ((j : Fin 4) → Multiplicative (ZMod 4)) ≃*
      Multiplicative (Fin 4 → ZMod 4) :=
    (MulEquiv.piMultiplicative (fun _ : Fin 4 => ZMod 4)).symm
  exact ⟨φ.trans (ψ.trans (ρ.trans τ))⟩

end T84Co

end CFSG.OddStandard.SmallF3.Omega
