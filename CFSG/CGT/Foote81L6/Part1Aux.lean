module

public import CFSG.CGT.Foote81L6.Rigid

public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

section E4

theorem e4_sq {b : ℕ} (hb : b = 1) (g : DihedralGroup (2 ^ b)) : g * g = 1 := by
  subst hb; revert g; decide

theorem e4_card {b : ℕ} (hb : b = 1) : Nat.card (DihedralGroup (2 ^ b)) = 4 := by
  subst hb; simp [DihedralGroup.nat_card]

theorem e4_enum {b : ℕ} (hb : b = 1) (u v : DihedralGroup (2 ^ b)) (hu : u ≠ 1) (hv : v ≠ 1)
    (huv : u ≠ v) (s : DihedralGroup (2 ^ b)) : s = 1 ∨ s = u ∨ s = v ∨ s = u * v := by
  subst hb; revert u v s; decide

end E4

variable {a : Fin 3 → ℕ}

theorem central_apply_cases' {i : Fin 3} (hi : 2 ≤ a i) {c : PX a} (hc : ∀ x, x * c = c * x) :
    c i = 1 ∨ c i = zc (a i) :=
  eq_one_or_zc_of_comm hi fun g =>
    ((comm_mulSingle_iff c).mp (fun i h => (hc _).symm) i g).symm

theorem central_sq' (hcase : ∀ i, a i = 1 ∨ 2 ≤ a i) {c : PX a} (hc : ∀ x, x * c = c * x) :
    c * c = 1 := by
  ext i
  rcases hcase i with h | h
  · exact e4_sq h (c i)
  · rcases central_apply_cases' h hc with h' | h'
    · simp [h']
    · simp [h', zc_mul_self (a := a i) (by omega)]

theorem central_pow_odd' (hcase : ∀ i, a i = 1 ∨ 2 ≤ a i) {c : PX a} (hc : ∀ x, x * c = c * x)
    {N : ℕ} (hN : Odd N) : c ^ N = c := by
  obtain ⟨k, rfl⟩ := hN
  rw [pow_succ, pow_mul, sq, central_sq' hcase hc, one_pow, one_mul]

theorem map_central {y : MulAut (PX a)} {c : PX a} (hc : ∀ x, x * c = c * x) :
    ∀ x, x * y c = y c * x := by
  intro x
  apply y.symm.injective
  simp [hc]

theorem p1 (h0 : a 0 = 1) (h1 : 2 ≤ a 1) (h2 : 2 ≤ a 2) (y : MulAut (PX a)) {N : ℕ} (hN : Odd N)
    (hyN : y ^ N = 1) (j : Fin 3) (hj : j ≠ 0) :
    y (zz a j) = zz a j ∧ ∀ k, k ≠ j → ∀ (d : DihedralGroup (2 ^ a j)) (h : DihedralGroup (2 ^ a k)),
      y (Pi.mulSingle j d) * Pi.mulSingle k h = Pi.mulSingle k h * y (Pi.mulSingle j d) := by
  obtain ⟨i1, hi1, -, hz1, hc1⟩ := sig h1 y
  obtain ⟨i2, hi2, -, hz2, hc2⟩ := sig h2 y
  have hne0 : ∀ i, 2 ≤ a i → i ≠ 0 := fun i hi h => by rw [h, h0] at hi; omega
  have hdist : i1 ≠ i2 := by
    intro h
    subst h
    have : zz a 1 = zz a 2 := y.injective (hz1.trans hz2.symm)
    have := zz_injective (a := a) (by omega) (by omega) this
    exact absurd this (by decide)
  have hcases : (i1 = 1 ∧ i2 = 2) ∨ (i1 = 2 ∧ i2 = 1) := by
    have := hne0 i1 hi1
    have := hne0 i2 hi2
    omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · fin_cases j
    · exact absurd rfl hj
    · exact ⟨hz1, hc1⟩
    · exact ⟨hz2, hc2⟩
  · exfalso
    obtain ⟨k, rfl⟩ := hN
    have key : ∀ m, (y ^ (2 * m)) (zz a 1) = zz a 1 ∧ (y ^ (2 * m)) (zz a 2) = zz a 2 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        refine ⟨?_, ?_⟩ <;>
          rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, mulAut_pow_apply_succ',
            mulAut_pow_apply_succ'] <;> simp [hz1, hz2, ih.1, ih.2]
    have h3 := (key k).2
    have h4 : (y ^ (2 * k + 1)) (zz a 1) = zz a 1 := by rw [hyN]; rfl
    rw [mulAut_pow_apply_succ', hz1, h3] at h4
    exact absurd (zz_injective (a := a) (by omega) (by omega) h4) (by decide)


abbrev PY (a : Fin 3 → ℕ) := PX (fun i : Fin 2 => a i.succ)

def ιY (a : Fin 3 → ℕ) : PY a →* PX a where
  toFun g := Fin.cons (α := fun i : Fin 3 => DihedralGroup (2 ^ a i)) 1 g
  map_one' := by
    ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  map_mul' g h := by
    ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp

theorem ιY_zero (g : PY a) : ιY a g 0 = 1 := by simp [ιY]

theorem ιY_succ (g : PY a) (i : Fin 2) : ιY a g i.succ = g i := by simp [ιY]

theorem ιY_injective : Function.Injective (ιY a) := by
  intro g h hgh
  ext i
  have := congrFun hgh i.succ
  rwa [ιY_succ, ιY_succ] at this

theorem ιY_mulSingle (j : Fin 2) (d : DihedralGroup (2 ^ a j.succ)) :
    ιY a (Pi.mulSingle j d) = Pi.mulSingle j.succ d := by
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [ιY_zero, Pi.mulSingle_eq_of_ne (Fin.succ_ne_zero j).symm]
  · by_cases h : i = j
    · subst h; simp [ιY_succ]
    · rw [ιY_succ, Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne (fun h' => h (Fin.succ_injective _ h'))]

theorem exists_ιY (x : PX a) (hx : x 0 = 1) : ∃ g, x = ιY a g := by
  refine ⟨fun i => x i.succ, ?_⟩
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [ιY_zero, hx]
  · simp [ιY_succ]


theorem twist (h0 : a 0 = 1) (h1 : 2 ≤ a 1) (h2 : 2 ≤ a 2) (y : MulAut (PX a)) {N : ℕ}
    (hN : Odd N) (hyN : y ^ N = 1) (K : Subgroup (PX a)) (hKc : K ≤ Subgroup.center (PX a))
    (hKy : ∀ k ∈ K, y k ∈ K) (π : PX a →* PY a) (hπι : ∀ g, π (ιY a g) = g)
    (hπK : ∀ k ∈ K, π k = 1) (hker : ∀ x, π x = 1 → x ∈ K) :
    ∀ x, x⁻¹ * y x ∈ K := by
  have hdec : ∀ x, ∃ k ∈ K, x = k * ιY a (π x) := by
    intro x
    refine ⟨x * (ιY a (π x))⁻¹, hker _ (by simp [hπι]), by simp⟩
  have hπy : ∀ x, π (y x) = π (y (ιY a (π x))) := by
    intro x
    obtain ⟨k, hk, hx⟩ := hdec x
    have h1' : y x = y k * y (ιY a (π x)) := by rw [← map_mul, ← hx]
    rw [h1', map_mul, hπK _ (hKy k hk), one_mul]
  let y' : PY a →* PY a := π.comp (y.toMonoidHom.comp (ιY a))
  have hy' : ∀ g, y' g = π (y (ιY a g)) := fun _ => rfl
  have iter : ∀ m g, y'^[m] g = π ((y ^ m) (ιY a g)) := by
    intro m g
    induction m with
    | zero => simp [hπι]
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, hy', ← hπy, mulAut_pow_apply_succ]
  have hy'N : ∀ g, y'^[N] g = g := by
    intro g
    rw [iter, hyN, MulAut.one_apply, hπι]
  obtain ⟨ψ, hψ, hψN⟩ := exists_mulAut_of_iterate y' hN.pos hy'N
  have hcase : ∀ i : Fin 2, 2 ≤ a i.succ := by
    intro i; fin_cases i
    · exact h1
    · exact h2
  have hCent : Cent ψ := by
    refine fun j k hjk d h => ?_
    have hc := (p1 h0 h1 h2 y hN hyN j.succ (Fin.succ_ne_zero j)).2 k.succ
      (fun h' => hjk (Fin.succ_injective _ h')) d h
    have hc' : y (ιY a (Pi.mulSingle j d)) * ιY a (Pi.mulSingle k h) =
        ιY a (Pi.mulSingle k h) * y (ιY a (Pi.mulSingle j d)) := by
      rwa [ιY_mulSingle, ιY_mulSingle]
    have := congrArg π hc'
    rw [map_mul, map_mul, hπι] at this
    rw [hψ, hy']
    exact this
  have hψ1 : ψ = 1 := kl hcase ψ hN hψN hCent
  have hyid : ∀ g, y' g = g := fun g => by rw [← hψ, hψ1]; rfl
  have hker1 : ∀ g, (ιY a g)⁻¹ * y (ιY a g) ∈ K := by
    intro g
    refine hker _ ?_
    rw [map_mul, map_inv, hπι, ← hy', hyid, inv_mul_cancel]
  intro x
  obtain ⟨k, hk, hx⟩ := hdec x
  set g := π x with hg
  have hkc : k⁻¹ * y k ∈ K := K.mul_mem (K.inv_mem hk) (hKy k hk)
  have hcomm := Subgroup.mem_center_iff.mp (hKc hkc)
  have : x⁻¹ * y x = (k⁻¹ * y k) * ((ιY a g)⁻¹ * y (ιY a g)) := by
    conv_lhs => rw [hx]
    rw [map_mul, mul_inv_rev]
    calc (ιY a g)⁻¹ * k⁻¹ * (y k * y (ιY a g))
        = (ιY a g)⁻¹ * (k⁻¹ * y k) * y (ιY a g) := by group
      _ = (k⁻¹ * y k) * (ιY a g)⁻¹ * y (ιY a g) := by rw [← hcomm]
      _ = _ := by group
  rw [this]
  exact K.mul_mem hkc (hker1 g)

end CFSG.CGT.Foote81L6
