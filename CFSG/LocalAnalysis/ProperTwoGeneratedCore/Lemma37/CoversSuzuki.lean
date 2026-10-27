module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzuki

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open Polynomial

namespace CoverSuzuki

variable (m : ℕ)

local notation "F" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

theorem exists_suzukiTitsNorm_ne (hm : 2 ≤ m) : ∃ x : F, x ≠ 0 ∧ x ≠ 1 ∧
    x * suzukiCoverTits m x + (x + 1) * suzukiCoverTits m (x + 1) +
      x * suzukiCoverTits m x * ((x + 1) * suzukiCoverTits m (x + 1)) ≠ 0 := by
  classical
  set T := 2 ^ (m + 1) with hT
  let p : F[X] := X * X ^ T + (X + 1) * (X + 1) ^ T + X * X ^ T * ((X + 1) * (X + 1) ^ T)
  have heval : ∀ x : F, p.eval x = x * suzukiCoverTits m x + (x + 1) * suzukiCoverTits m (x + 1) +
      x * suzukiCoverTits m x * ((x + 1) * suzukiCoverTits m (x + 1)) := fun x => by
    simp [p, suzukiCoverTits_apply, T]
  have hp0 : p ≠ 0 := by
    intro h
    have h0 := heval 0
    rw [h, eval_zero] at h0
    simp at h0
  have hdeg : p.natDegree ≤ 2 * T + 2 := by
    have hX1 : (X + 1 : F[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
    have hA : (X * X ^ T : F[X]).natDegree ≤ T + 1 := by
      rw [← pow_succ', natDegree_X_pow]
    have hB : ((X + 1) * (X + 1) ^ T : F[X]).natDegree ≤ T + 1 := by
      rw [← pow_succ']
      exact (natDegree_pow_le_of_le _ hX1).trans (by rw [mul_one])
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (hA.trans (by omega))
      (hB.trans (by omega))) ((natDegree_mul_le_of_le hA hB).trans (by omega))
  let bad : Finset F := insert 0 (insert 1 p.roots.toFinset)
  have hbad : bad.card ≤ 2 * T + 4 := by
    have hroot := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
    have h1 := Finset.card_insert_le (1 : F) p.roots.toFinset
    have h0 := Finset.card_insert_le (0 : F) (insert 1 p.roots.toFinset)
    dsimp only [bad]
    omega
  have hcard : Nat.card F = 2 ^ (2 * m + 1) := GaloisField.card 2 (2 * m + 1) (by omega)
  have hlt : bad.card < Nat.card F := by
    rw [hcard]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    have h1 : 2 ^ (2 * (k + 2) + 1) = 2 ^ (k + 3) * 2 ^ (k + 2) := by
      rw [← pow_add]; congr 1; omega
    have h2 : T = 2 ^ (k + 3) := by rw [hT]
    have h3 : 4 ≤ 2 ^ (k + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 8 ≤ 2 ^ (k + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h1]
    nlinarith
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := bad) (t := Finset.univ) (by rwa [Finset.card_univ, ← Nat.card_eq_fintype_card])
  simp only [bad, Finset.mem_insert, Multiset.mem_toFinset, not_or] at hx
  obtain ⟨hx0, hx1, hxr⟩ := hx
  refine ⟨x, hx0, hx1, fun h => hxr ((mem_roots hp0).mpr ?_)⟩
  rw [IsRoot, heval, h]

theorem suzuki_pairing_eq_zero (hm : 2 ≤ m) (f : F → F → ZMod 2)
    (hl : ∀ a a' c, f (a + a') c = f a c + f a' c)
    (hr : ∀ a c c', f a (c + c') = f a c + f a c')
    (hinv : ∀ x : F, x ≠ 0 → ∀ a c, f (x * a) (x * suzukiCoverTits m x * c) = f a c)
    (a c : F) : f a c = 0 := by
  obtain ⟨x, hx0, hx1, hx⟩ := exists_suzukiTitsNorm_ne m hm
  have hN0 : ∀ y : F, y ≠ 0 → y * suzukiCoverTits m y ≠ 0 := fun y hy =>
    mul_ne_zero hy ((_root_.map_ne_zero _).mpr hy)
  have hmove : ∀ y : F, y ≠ 0 → ∀ a c, f (y * a) c = f a ((y * suzukiCoverTits m y)⁻¹ * c) := by
    intro y hy a c
    have h := hinv y hy a ((y * suzukiCoverTits m y)⁻¹ * c)
    rwa [mul_inv_cancel_left₀ (hN0 y hy)] at h
  have hx1' : x + 1 ≠ 0 := fun h => hx1 (CharTwo.add_eq_zero.mp h)
  set t : F := (((x + 1) * suzukiCoverTits m (x + 1))⁻¹ + (x * suzukiCoverTits m x)⁻¹ + 1)
  have hkill : ∀ a c, f a (t * c) = 0 := by
    intro a c
    have h := hl (x * a) a c
    rw [← add_one_mul, hmove _ hx1', hmove _ hx0] at h
    have h2 : ∀ u : ZMod 2, u + u = 0 := by decide
    rw [add_mul, add_mul, one_mul, hr, hr, h]
    calc f a ((x * suzukiCoverTits m x)⁻¹ * c) + f a c +
          f a ((x * suzukiCoverTits m x)⁻¹ * c) + f a c =
        (f a ((x * suzukiCoverTits m x)⁻¹ * c) + f a ((x * suzukiCoverTits m x)⁻¹ * c)) +
          (f a c + f a c) := by ring
      _ = 0 := by rw [h2, h2, add_zero]
  have ht : t ≠ 0 := by
    intro ht
    apply hx
    have hA := hN0 x hx0
    have hB := hN0 _ hx1'
    calc x * suzukiCoverTits m x + (x + 1) * suzukiCoverTits m (x + 1) +
          x * suzukiCoverTits m x * ((x + 1) * suzukiCoverTits m (x + 1)) =
        t * (x * suzukiCoverTits m x * ((x + 1) * suzukiCoverTits m (x + 1))) := by
          simp only [t]
          field_simp
      _ = 0 := by rw [ht, zero_mul]
  have h := hkill a (t⁻¹ * c)
  rwa [mul_inv_cancel_left₀ ht] at h

theorem coverPairingVanishes_suzukiCoverRoot (hm : 2 ≤ m) :
    CoverPairingVanishes G (suzukiCoverRoot m) := by
  intro P h₁ h₂ h₃ h₄ a ha b hb
  have hm0 : 0 < m := by omega
  let S : F → F → G := fun a b => suzukiCoverRootElement m a b
  have hS : ∀ a b, S a b ∈ suzukiCoverRoot m := fun a b => (suzukiCoverRootElement m a b).2
  have hZ : ∀ c, InCenterOf (suzukiCoverRoot m) (S 0 c) := BorelSuzuki.inCenterOf_root_zero m hm0
  have hred : ∀ x y c, P (S x y) (S 0 c) = P (S x 0) (S 0 c) := by
    intro x y c
    change P (suzukiCoverRootElement m x y : G) (S 0 c) = _
    rw [BorelSuzuki.root_eq_mul m hm0 x y, h₁ _ (hS x 0) _ (hS 0 y) _ (hZ c),
      h₃ _ _ (hZ y) (hZ c), add_zero]
  have hmul : ∀ x x', S x 0 * S x' 0 = S (x + x') (x * suzukiCoverTits m x') := by
    intro x x'
    change (suzukiCoverRootElement m x 0 : G) * suzukiCoverRootElement m x' 0 = _
    rw [BorelSuzuki.root_mul m hm0, zero_add, zero_add]
  have hmul0 : ∀ c c', S 0 c * S 0 c' = S 0 (c + c') := by
    intro c c'
    change (suzukiCoverRootElement m 0 c : G) * suzukiCoverRootElement m 0 c' = _
    rw [BorelSuzuki.root_mul m hm0, zero_add, zero_mul, add_zero]
  have hf := CoverSuzuki.suzuki_pairing_eq_zero m hm (fun x c => P (S x 0) (S 0 c))
    (fun x x' c => by
      rw [← h₁ _ (hS x 0) _ (hS x' 0) _ (hZ c), hmul, hred (x + x') (x * suzukiCoverTits m x')])
    (fun x c c' => by
      rw [← h₂ _ (hS x 0) _ _ (hZ c) (hZ c'), hmul0])
    (fun y hy x c => by
      have ht : ((suzukiCoverTorusHom m (Units.mk0 y hy) : suzukiCoverTorus m) : G) ∈
          Subgroup.normalizer (suzukiCoverRoot m : Set G) :=
        suzukiCoverTorus_le_normalizer m (suzukiCoverTorusHom m (Units.mk0 y hy)).2
      have h := h₄ _ ht _ (hS x 0) _ (hZ c)
      rwa [BorelSuzuki.torus_conj_root, BorelSuzuki.torus_conj_root, Units.val_mk0, mul_zero,
        mul_zero] at h)
  obtain ⟨x, y, rfl⟩ := BorelSuzuki.exists_eq_root m ha
  obtain ⟨c, rfl⟩ := (BorelSuzuki.inCenterOf_iff m hm0 b).mp hb
  exact (hred x y c).trans (hf x c)

theorem benderCoverFacts_suzukiCoverRoot (hm : 2 ≤ m) :
    BenderCoverFacts G (suzukiCoverRoot m) where
  center := Or.inl (by
    rw [BorelSuzuki.card_inCenterOf m (by omega)]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
  pairing := coverPairingVanishes_suzukiCoverRoot m hm

end CoverSuzuki

theorem suzukiCoverFacts {n : ℕ} (hn : 2 ≤ n) :
    ∃ Q : Sylow 2 ↥(CFSG.Theory.Comparator.SzModel n),
      BenderCoverFacts ↥(CFSG.Theory.Comparator.SzModel n) (Q : Subgroup _) := by
  rw [show CFSG.Theory.Comparator.SzModel n = SuzukiMatrixGroup n from
    CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n]
  exact ⟨suzukiCoverSylow n (by omega), CoverSuzuki.benderCoverFacts_suzukiCoverRoot n hn⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
