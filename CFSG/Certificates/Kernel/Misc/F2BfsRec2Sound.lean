
module

public import CFSG.Certificates.Kernel.Misc.F2MatGroup
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import Certificates.Data.Kernel.Misc.F2BfsRec2
import CFSG.Certificates.Kernel.Spor.PK.MiscBase

public section

namespace CFSG.KC.F2BfsRec

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.F2Mat CFSG.KC.Misc.Spec
open CFSG.KC.Misc.G24 (mulF2)

private theorem andB_tt' {a b : Bool} (h : CFSG.KLie.CT.andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem allN_tt' {m : ℕ} {f : ℕ → Bool} (h : allN m f = true) : ∀ i < m, f i = true := by
  induction m with
  | zero => exact fun i hi => absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    obtain ⟨h1, h2⟩ := andB_tt' (h : CFSG.KLie.CT.andB (f m) (allN m f) = true)
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

private theorem strictB_eq3 (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem matOfF_eq_pkMat (d M : ℕ) : CFSG.KC.WordPts.matOfF d M = pkMat d M := by
  ext r c
  rw [matOfF_apply]
  rfl

theorem testBit_foldF2_ge {n : ℕ} (hn : 0 < n) (A B : ℕ) {q : ℕ} (hq : n * n ≤ q) :
    ∀ m, (foldF2 n A B m).testBit q = false
  | 0 => by simp [foldF2]
  | m + 1 => by
    obtain ⟨i, j, hj, e⟩ : ∃ i j, j < n ∧ q = n * i + j :=
      ⟨q / n, q % n, Nat.mod_lt _ hn, (Nat.div_add_mod q n).symm⟩
    have hi : ¬ i < n := fun hi => by
      have h1 : n * (i + 1) ≤ n * n := Nat.mul_le_mul_left _ hi
      rw [Nat.mul_succ] at h1
      omega
    rw [foldF2, Nat.testBit_xor, testBit_foldF2_ge hn A B hq m, e, testBit_stepF2 hn A B m hj]
    simp [hi]

theorem mulF2_lt (d A B : ℕ) : mulF2 d A B < 2 ^ (d * d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · unfold mulF2
    simp only [CFSG.KS.PK.letN_eq]
    exact Nat.zero_lt_one
  rw [mulF2_eq_fold hd]
  exact Nat.lt_pow_two_of_testBit _ fun q hq => testBit_foldF2_ge hd A B hq d

theorem mulF_lt (d A B : ℕ) : mulF d A B < 2 ^ (d * d) := by
  apply Nat.lt_pow_two_of_testBit
  intro q hq
  apply Bool.eq_false_iff.mpr
  intro h
  change (CFSG.KC.Loop.strictN A fun A => CFSG.KC.Loop.strictN B fun B =>
    orN d fun i => (vmF d B (rowF d A i)) <<< (d * i)).testBit q = true at h
  simp only [strictN_eq] at h
  rw [testBit_orN] at h
  obtain ⟨i, hi, h⟩ := h
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨_, h⟩ := h
  have h1 : d * (i + 1) ≤ d * d := Nat.mul_le_mul_left _ hi
  rw [Nat.mul_succ] at h1
  rw [testBit_vmF_ge (by omega)] at h
  exact Bool.false_ne_true h

theorem mulF2_eq_mulF (d A B : ℕ) : mulF2 d A B = mulF d A B := by
  apply matOfF_inj (mulF2_lt d A B) (mulF_lt d A B)
  rw [matOfF_mulF, matOfF_eq_pkMat, matOfF_eq_pkMat, matOfF_eq_pkMat, pkMat_mulF2]

theorem edgesK2_eq (d w lb ng : ℕ) (CF G : ℕ → ℕ) (N r X : ℕ) :
    edgesK2 d w lb ng CF G N r X = edgesK d w lb ng CF G N r X := by
  simp only [edgesK2, edgesK, mulF2_eq_mulF]

theorem recK2_eq_recK (d w lb ng : ℕ) (CF G : ℕ → ℕ) (N k : ℕ) :
    recK2 d w lb ng CF G N k = recK d w lb ng CF G N k := by
  simp only [recK2, recK, edgesK2_eq]

variable {d w lb ng N : ℕ} {CF G : ℕ → ℕ}

theorem recK2_sound (hN : 0 < N) (hNw : N < 2 ^ w)
    (hh : headK d w lb ng CF = true) (h : ∀ k < N, recK2 d w lb ng CF G N k = true) :
    elemAt d w lb ng CF 0 = idF d ∧
      (∀ k < N, ∀ k' < N, elemAt d w lb ng CF k = elemAt d w lb ng CF k' → k = k') ∧
      (∀ k < N, ∀ j < ng, ∃ t < N, elemAt d w lb ng CF t = mulF d (elemAt d w lb ng CF k) (G j)) ∧
      ∀ P : ℕ → Prop, P (idF d) → (∀ X j, j < ng → P X → P (mulF d X (G j))) →
        ∀ k < N, P (elemAt d w lb ng CF k) :=
  recK_sound hN hNw hh fun k hk => (recK2_eq_recK _ _ _ _ _ _ _ _).symm.trans (h k hk)

theorem card_range_of_recK2 {K : Type*} [Group K]
    (ψ : K →* Matrix (Fin d) (Fin d) (ZMod 2)) (g : Fin ng → K)
    (hg : ∀ j : Fin ng, ψ (g j) = CFSG.KC.WordPts.matOfF d (G j))
    (hgen : Subgroup.closure {x | (∃ j, g j = x) ∨ ψ x = 1} = ⊤)
    (hN : 0 < N) (hNw : N < 2 ^ w) (hh : headK d w lb ng CF = true)
    (h : ∀ k < N, recK2 d w lb ng CF G N k = true) :
    Nat.card (Set.range ψ) = N :=
  card_range_of_recK ψ g hg hgen hN hNw hh fun k hk =>
    (recK2_eq_recK _ _ _ _ _ _ _ _).symm.trans (h k hk)

theorem exists_entry_of_recK2 {K : Type*} [Group K]
    (ψ : K →* Matrix (Fin d) (Fin d) (ZMod 2)) (g : Fin ng → K)
    (hg : ∀ j : Fin ng, ψ (g j) = CFSG.KC.WordPts.matOfF d (G j))
    (hgen : Subgroup.closure {x | (∃ j, g j = x) ∨ ψ x = 1} = ⊤)
    (hN : 0 < N) (hNw : N < 2 ^ w) (hh : headK d w lb ng CF = true)
    (h : ∀ k < N, recK2 d w lb ng CF G N k = true) (x : K) :
    ∃ t < N, ψ x = CFSG.KC.WordPts.matOfF d (elemAt d w lb ng CF t) := by
  obtain ⟨h0, -, hcl, -⟩ := recK2_sound hN hNw hh h
  set S : Set (Matrix (Fin d) (Fin d) (ZMod 2)) :=
    (fun t => CFSG.KC.WordPts.matOfF d (elemAt d w lb ng CF t)) '' Set.Iio N with hS
  have hxx : ∀ x : K, ψ x * ψ x⁻¹ = 1 := fun x => by rw [← map_mul, mul_inv_cancel, map_one]
  have key : ∀ x : K, ∀ X ∈ S, X * ψ x ∈ S := by
    intro x
    have hx : x ∈ Subgroup.closure {x | (∃ j, g j = x) ∨ ψ x = 1} := by
      rw [hgen]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨j, rfl⟩ | h1
      · rintro _ ⟨t, ht, rfl⟩
        obtain ⟨t', ht', he⟩ := hcl t ht j j.2
        exact ⟨t', ht', by simp only [he, matOfF_mulF, hg]⟩
      · intro X hX
        rwa [h1, mul_one]
    | one =>
      intro X hX
      rwa [map_one, mul_one]
    | mul x y _ _ ihx ihy =>
      intro X hX
      rw [map_mul, ← mul_assoc]
      exact ihy _ (ihx _ hX)
    | inv x _ ihx =>
      intro X hX
      have hfin : S.Finite := (Set.finite_Iio N).image _
      have hinjOn : Set.InjOn (fun Y => Y * ψ x) S := fun Y _ Z _ hYZ => by
        have hYZ' : Y * ψ x = Z * ψ x := hYZ
        calc Y = Y * ψ x * ψ x⁻¹ := by rw [mul_assoc, hxx, mul_one]
          _ = Z * ψ x * ψ x⁻¹ := by rw [hYZ']
          _ = Z := by rw [mul_assoc, hxx, mul_one]
      obtain ⟨Y, hY, hYX⟩ :=
        ((hfin.injOn_iff_bijOn_of_mapsTo fun Y hY => ihx Y hY).mp hinjOn).surjOn hX
      have hYX' : Y * ψ x = X := hYX
      rw [← hYX', mul_assoc, hxx, mul_one]
      exact hY
  have h1 : (1 : Matrix (Fin d) (Fin d) (ZMod 2)) ∈ S := ⟨0, hN, by simp only [h0, matOfF_idF]⟩
  obtain ⟨t, ht, he⟩ := key x 1 h1
  have he' : CFSG.KC.WordPts.matOfF d (elemAt d w lb ng CF t) = 1 * ψ x := he
  exact ⟨t, ht, by rw [he', one_mul]⟩

theorem exists_of_entry_recK2 {K : Type*} [Group K]
    (ψ : K →* Matrix (Fin d) (Fin d) (ZMod 2)) (g : Fin ng → K)
    (hg : ∀ j : Fin ng, ψ (g j) = CFSG.KC.WordPts.matOfF d (G j))
    (hN : 0 < N) (hNw : N < 2 ^ w) (hh : headK d w lb ng CF = true)
    (h : ∀ k < N, recK2 d w lb ng CF G N k = true) {t : ℕ} (ht : t < N) :
    ∃ x : K, ψ x = CFSG.KC.WordPts.matOfF d (elemAt d w lb ng CF t) := by
  obtain ⟨-, -, -, hmin⟩ := recK2_sound hN hNw hh h
  exact hmin (fun X => ∃ x, ψ x = CFSG.KC.WordPts.matOfF d X) ⟨1, by rw [map_one, matOfF_idF]⟩
    (fun X j hj ⟨x, hx⟩ => ⟨x * g ⟨j, hj⟩, by rw [map_mul, hx, hg, matOfF_mulF]⟩) t ht

theorem mulF_idF {X : ℕ} (hX : X < 2 ^ (d * d)) : mulF d (idF d) X = X :=
  matOfF_inj (mulF_lt d _ _) hX (by rw [matOfF_mulF, matOfF_idF, one_mul])

theorem genR_eq (hh : headK d w lb ng CF = true) (h0 : recK2 d w lb ng CF G N 0 = true)
    {j : ℕ} (hj : j < ng) (hG : G j < 2 ^ (d * d)) : genR d w lb ng CF j = G j := by
  have hE : elemAt d w lb ng CF 0 = idF d := by
    unfold headK at hh
    rw [strictB_eq3] at hh
    exact Nat.eq_of_beq_eq_true (andB_tt' hh).1
  unfold recK2 at h0
  simp only [strictB_eq3] at h0
  have h1 := allN_tt' (andB_tt' h0).1 j hj
  rw [strictB_eq3] at h1
  have h2 := Nat.eq_of_beq_eq_true (andB_tt' h1).2
  change elemAt d w lb ng CF (fldOf d w (recAt d w lb ng CF 0) j) = G j
  rw [h2, mulF2_eq_mulF]
  change mulF d (elemAt d w lb ng CF 0) (G j) = G j
  rw [hE, mulF_idF hG]

theorem memK_spec {t X : ℕ} (h : memK d w lb ng CF N t X = true) :
    t < N ∧ elemAt d w lb ng CF t = X := by
  obtain ⟨h1, h2⟩ := andB_tt' h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

private theorem sort_of_recK2 {k : ℕ} (h : recK2 d w lb ng CF G N k = true) :
    fldOf d w (recAt d w lb ng CF k) (Nat.succ ng) < N ∧ (k + 1 < N →
      sortedAt d w lb ng CF k < sortedAt d w lb ng CF (k + 1)) := by
  unfold recK2 at h
  simp only [strictB_eq3] at h
  have hs := (andB_tt' (andB_tt' (andB_tt' h).2).2).2
  obtain ⟨h1, h2⟩ := andB_tt' hs
  refine ⟨Nat.le_of_ble_eq_true h1, fun hk => ?_⟩
  have e : Nat.blt (Nat.succ k) N = true := Nat.ble_eq_true_of_le hk
  rw [e] at h2
  exact Nat.le_of_ble_eq_true h2

theorem sortedAt_entry (h : ∀ k < N, recK2 d w lb ng CF G N k = true) {s : ℕ} (hs : s < N) :
    ∃ t < N, sortedAt d w lb ng CF s = elemAt d w lb ng CF t :=
  ⟨_, (sort_of_recK2 (h s hs)).1, rfl⟩

private theorem le_of_succ_lt {N : ℕ} {e : ℕ → ℕ} (h : ∀ k, k + 1 < N → e k < e (k + 1)) :
    ∀ {a b : ℕ}, a ≤ b → b < N → e a ≤ e b
  | a, 0, hab, _ => by
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | a, b + 1, hab, hb => by
    rcases Nat.lt_or_eq_of_le hab with h1 | rfl
    · exact le_trans (le_of_succ_lt h (by omega) (by omega)) (le_of_lt (h b hb))
    · exact le_rfl

theorem ne_of_gapK (h : ∀ k < N, recK2 d w lb ng CF G N k = true) {p X : ℕ}
    (hg : gapK d w lb ng CF N p X = true) : ∀ t < N, elemAt d w lb ng CF t ≠ X := by
  have hS := fun k hk => sort_of_recK2 (h k hk)
  have hmono : ∀ k, k + 1 < N → sortedAt d w lb ng CF k < sortedAt d w lb ng CF (k + 1) :=
    fun k hk => (hS k (by omega)).2 hk
  have hle : ∀ {a b : ℕ}, a ≤ b → b < N →
      sortedAt d w lb ng CF a ≤ sortedAt d w lb ng CF b := le_of_succ_lt hmono
  let σ : Fin N → Fin N := fun k => ⟨_, (hS k k.2).1⟩
  have hσ : Function.Injective σ := by
    intro a b hab
    have e : sortedAt d w lb ng CF a = sortedAt d w lb ng CF b :=
      congrArg (elemAt d w lb ng CF) (congrArg Fin.val hab)
    rcases Nat.lt_trichotomy (a : ℕ) b with h' | h' | h'
    · have := lt_of_lt_of_le (hmono a (by omega)) (hle (Nat.succ_le_of_lt h') b.2)
      omega
    · exact Fin.ext h'
    · have := lt_of_lt_of_le (hmono b (by omega)) (hle (Nat.succ_le_of_lt h') a.2)
      omega
  intro t ht hE
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hσ ⟨t, ht⟩
  have ek : sortedAt d w lb ng CF k = X := by
    have e1 : ((σ k : Fin N) : ℕ) = t := congrArg Fin.val hk
    change elemAt d w lb ng CF ((σ k : Fin N) : ℕ) = X
    rw [e1, hE]
  unfold gapK at hg
  cases hpN : Nat.beq p N
  · rw [hpN] at hg
    obtain ⟨h1, h2⟩ := andB_tt' hg
    obtain ⟨h3, h4⟩ := andB_tt' h2
    have hp : p < N := Nat.le_of_ble_eq_true h1
    have hpX : sortedAt d w lb ng CF p < X := Nat.le_of_ble_eq_true h3
    by_cases hkp : (k : ℕ) ≤ p
    · have := hle hkp hp
      omega
    · have hp1 : p + 1 < N := by omega
      have e : Nat.blt (Nat.succ p) N = true := Nat.ble_eq_true_of_le hp1
      rw [e] at h4
      have hX : X < sortedAt d w lb ng CF (p + 1) := Nat.le_of_ble_eq_true h4
      have := hle (by omega : p + 1 ≤ k) k.2
      omega
  · rw [hpN] at hg
    have hX : X < sortedAt d w lb ng CF 0 := Nat.le_of_ble_eq_true hg
    have := hle (Nat.zero_le k) k.2
    omega

theorem exists_sorted_of_entry (h : ∀ k < N, recK2 d w lb ng CF G N k = true) {t : ℕ}
    (ht : t < N) : ∃ s < N, sortedAt d w lb ng CF s = elemAt d w lb ng CF t := by
  have hS := fun k hk => sort_of_recK2 (h k hk)
  have hmono : ∀ k, k + 1 < N → sortedAt d w lb ng CF k < sortedAt d w lb ng CF (k + 1) :=
    fun k hk => (hS k (by omega)).2 hk
  have hle : ∀ {a b : ℕ}, a ≤ b → b < N →
      sortedAt d w lb ng CF a ≤ sortedAt d w lb ng CF b := le_of_succ_lt hmono
  let σ : Fin N → Fin N := fun k => ⟨_, (hS k k.2).1⟩
  have hσ : Function.Injective σ := by
    intro a b hab
    have e : sortedAt d w lb ng CF a = sortedAt d w lb ng CF b :=
      congrArg (elemAt d w lb ng CF) (congrArg Fin.val hab)
    rcases Nat.lt_trichotomy (a : ℕ) b with h' | h' | h'
    · have := lt_of_lt_of_le (hmono a (by omega)) (hle (Nat.succ_le_of_lt h') b.2)
      omega
    · exact Fin.ext h'
    · have := lt_of_lt_of_le (hmono b (by omega)) (hle (Nat.succ_le_of_lt h') a.2)
      omega
  obtain ⟨k, hk⟩ := Finite.surjective_of_injective hσ ⟨t, ht⟩
  have e1 : ((σ k : Fin N) : ℕ) = t := congrArg Fin.val hk
  refine ⟨k, k.2, ?_⟩
  change elemAt d w lb ng CF ((σ k : Fin N) : ℕ) = _
  rw [e1]

end CFSG.KC.F2BfsRec

end
