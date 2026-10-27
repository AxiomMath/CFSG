module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowCount

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

abbrev W (n : ℕ) := IteratedWreathProduct Z2 n

noncomputable def repW (n : ℕ) : W n →* Equiv.Perm (Fin n → Z2) := iteratedWreathToPermHom Z2 n

theorem repW_injective (n : ℕ) : Function.Injective (repW n) :=
  iteratedWreathToPermHomInj Z2 n

noncomputable def sgW (n : ℕ) : W n →* ℤˣ := Equiv.Perm.sign.comp (repW n)

theorem sgW_apply (n : ℕ) (x : W n) : sgW n x = Equiv.Perm.sign (repW n x) := by
  unfold sgW
  rfl

theorem repW_succ (n : ℕ) (x : W n ≀ᵣ Z2) :
    repW (n + 1) x = (Fin.succFunEquiv Z2 n).symm.permCongr
      (letI := MulAction.compHom (Fin n → Z2) (repW n)
       (RegularWreathProduct.toPerm (W n) Z2 (Fin n → Z2)) x) := by
  unfold repW
  rw [iteratedWreathToPermHom]
  rfl

theorem sign_mulLeft (r : Z2) :
    Equiv.Perm.sign (Equiv.mulLeft r) = if r = 1 then 1 else -1 := by
  rcases z2_cases r with rfl | rfl
  · simp
  · have : Equiv.mulLeft z2 = Equiv.swap (1 : Z2) z2 := by
      ext x; revert x; decide
    rw [this, Equiv.Perm.sign_swap (by decide)]
    simp [z2_ne_one]

theorem sgW_succ (n : ℕ) (x : W n ≀ᵣ Z2) :
    sgW (n + 1) x = sgW n (x.left 1) * sgW n (x.left z2) *
      (if x.right = 1 then 1 else (-1) ^ (2 ^ n)) := by
  let _ := MulAction.compHom (Fin n → Z2) (repW n)
  have h1 : (RegularWreathProduct.toPerm (W n) Z2 (Fin n → Z2)) x =
      Equiv.prodCongrLeft (fun q : Z2 => repW n (x.left q)) *
        Equiv.prodCongr (Equiv.refl _) (Equiv.mulLeft x.right) := by
    ext p
    · simp [RegularWreathProduct.toPerm]
      rfl
    · simp [RegularWreathProduct.toPerm]
  have h2 : Equiv.prodCongr (Equiv.refl (Fin n → Z2)) (Equiv.mulLeft x.right) =
      Equiv.prodCongrRight (fun _ => Equiv.mulLeft x.right) := rfl
  show Equiv.Perm.sign (repW (n + 1) x) = _
  rw [repW_succ, Equiv.Perm.sign_permCongr]
  rw [h1, map_mul, h2, Equiv.Perm.sign_prodCongrLeft, Equiv.Perm.sign_prodCongrRight,
    sign_mulLeft]
  have hcard : Fintype.card (Fin n → Z2) = 2 ^ n := by
    simp
  have hU : (Finset.univ : Finset Z2) = {1, z2} := by decide
  rw [Finset.prod_const, Finset.card_univ, hcard, hU, Finset.prod_pair z2_ne_one.symm]
  split_ifs <;> simp [sgW]

instance : Subsingleton (W 0) := inferInstanceAs (Subsingleton PUnit)

theorem sgW_zero (x : W 0) : sgW 0 x = 1 := by
  have : x = 1 := Subsingleton.elim _ _
  rw [this, map_one]

noncomputable def cc : (n : ℕ) → W n
  | 0 => 1
  | n + 1 => (⟨fun _ => cc n, if n = 0 then z2 else 1⟩ : W n ≀ᵣ Z2)

theorem cc_succ (n : ℕ) (hn : 1 ≤ n) : cc (n + 1) = (diag (cc n) : W n ≀ᵣ Z2) := by
  have : n ≠ 0 := by omega
  simp [cc, diag, this]

theorem cc_one : cc 1 = (⟨fun _ => 1, z2⟩ : W 0 ≀ᵣ Z2) := by
  simp [cc]

theorem cc_ne_one : ∀ n : ℕ, 1 ≤ n → cc n ≠ 1
  | 0, h => by omega
  | 1, _ => by
    rw [cc_one]
    intro h
    have := congrArg RegularWreathProduct.right h
    exact z2_ne_one this
  | n + 2, _ => by
    rw [cc_succ (n + 1) (by omega)]
    intro h
    exact cc_ne_one (n + 1) (by omega) (diag_injective (h.trans diag_one.symm))

theorem W_one_comm (x y : W 1) : x * y = y * x := by
  rcases x with ⟨f, q⟩
  rcases y with ⟨f', q'⟩
  show (⟨f, q⟩ : W 0 ≀ᵣ Z2) * ⟨f', q'⟩ = ⟨f', q'⟩ * ⟨f, q⟩
  rw [RegularWreathProduct.mul_def, RegularWreathProduct.mul_def]
  ext z
  · exact Subsingleton.elim _ _
  · exact mul_comm q q'

theorem cc_central : ∀ n : ℕ, 1 ≤ n → ∀ a : W n, a * cc n = cc n * a
  | 0, h => by omega
  | 1, _ => fun a => W_one_comm a (cc 1)
  | n + 2, _ => fun a => by
    rw [cc_succ (n + 1) (by omega)]
    exact diag_central (cc_central (n + 1) (by omega)) a

theorem eq_one_or_cc : ∀ n : ℕ, 1 ≤ n → ∀ y : W n, (∀ a : W n, a * y = y * a) → y * y = 1 →
    y = 1 ∨ y = cc n
  | 0, h => by omega
  | 1, _ => fun y _ _ => by
    rcases y with ⟨f, q⟩
    rcases z2_cases q with rfl | rfl
    · left
      exact RegularWreathProduct.ext (funext fun _ => Subsingleton.elim _ _) rfl
    · right
      rw [cc_one]
      exact RegularWreathProduct.ext (funext fun _ => Subsingleton.elim _ _) rfl
  | n + 2, _ => fun y hc hy => by
    obtain ⟨d, hd, rfl⟩ := central_wreath (cc (n + 1)) (cc_ne_one (n + 1) (by omega)) y hc
    have hdd : d * d = 1 := diag_injective ((diag_mul_self d).symm.trans hy)
    rcases eq_one_or_cc (n + 1) (by omega) d hd hdd with rfl | rfl
    · left
      rfl
    · right
      exact (cc_succ (n + 1) (by omega)).symm

theorem sgW_cc_one : sgW 1 (cc 1) = -1 := by
  rw [cc_one]
  show sgW (0 + 1) _ = -1
  rw [sgW_succ]
  simp [z2_ne_one]

theorem sgW_cc_succ (n : ℕ) (hn : 1 ≤ n) : sgW (n + 1) (cc (n + 1)) = 1 := by
  rw [cc_succ n hn, sgW_succ]
  simp [diag]

theorem card_W : ∀ n : ℕ, Nat.card (W n) = 2 ^ (2 ^ n - 1)
  | 0 => by
    have : Subsingleton (W 0) := inferInstance
    simp
  | n + 1 => by
    have h := RegularWreathProduct.card (D := W n) (Q := Z2)
    have hZ : Nat.card Z2 = 2 := by simp
    rw [hZ, card_W n] at h
    rw [show Nat.card (W (n + 1)) = Nat.card (W n ≀ᵣ Z2) from rfl, h, ← pow_mul]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [← pow_succ]
    congr 1
    rw [pow_succ]
    omega

end CFSG.OddStandard.AltStdSec.SylowSn
