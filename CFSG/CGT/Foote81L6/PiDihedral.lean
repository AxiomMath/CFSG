module

public import CFSG.CGT.Foote81L6.Dihedral

public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

variable {ι : Type*} [DecidableEq ι] (a : ι → ℕ)

abbrev PX := ∀ i, DihedralGroup (2 ^ a i)

def zz (j : ι) : PX a := Pi.mulSingle j (zc (a j))

variable {a}

theorem conj_mulSingle (x : PX a) (j : ι) (d : DihedralGroup (2 ^ a j)) :
    x * Pi.mulSingle j d * x⁻¹ = Pi.mulSingle j (x j * d * (x j)⁻¹) := by
  ext i
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h]

theorem zz_apply_same (j : ι) : zz a j j = zc (a j) := by simp [zz]

theorem zz_apply_ne {i j : ι} (h : i ≠ j) : zz a j i = 1 := by
  simp [zz, Pi.mulSingle_eq_of_ne h]

theorem zz_ne_one (j : ι) (hj : 1 ≤ a j) : zz a j ≠ 1 := by
  intro h
  have := congrFun h j
  rw [zz_apply_same] at this
  exact zc_ne_one hj this

theorem zz_injective {i j : ι} (hi : 1 ≤ a i) (hj : 1 ≤ a j) (h : zz a i = zz a j) : i = j := by
  by_contra hij
  have := congrFun h i
  rw [zz_apply_same, zz_apply_ne hij] at this
  exact zc_ne_one hi this

theorem zz_comm (j : ι) (hj : 1 ≤ a j) (x : PX a) : x * zz a j = zz a j * x := by
  ext i
  by_cases h : i = j
  · subst h; simp [zz_apply_same, zc_comm hj]
  · simp [zz_apply_ne h]

theorem zz_eq_pow (j : ι) (hj : 1 ≤ a j) :
    zz a j = (Pi.mulSingle j (r 1 : DihedralGroup (2 ^ a j)) : PX a) ^ (2 ^ (a j - 1)) := by
  rw [← Pi.mulSingle_pow, rho_pow hj]; rfl

theorem comm_mulSingle_iff (u : PX a) :
    (∀ i (h : DihedralGroup (2 ^ a i)), u * Pi.mulSingle i h = Pi.mulSingle i h * u) ↔
      ∀ i (h : DihedralGroup (2 ^ a i)), u i * h = h * u i := by
  constructor
  · intro H i h
    have := congrFun (H i h) i
    simpa using this
  · intro H i h
    ext k
    by_cases hk : k = i
    · subst hk; simpa using H k h
    · simp [Pi.mulSingle_eq_of_ne hk]

def Kj (y : MulAut (PX a)) (j i : ι) : Subgroup (DihedralGroup (2 ^ a j)) where
  carrier := {e | ∀ k, k ≠ i → y (Pi.mulSingle j e) k = 1}
  mul_mem' := by
    intro e f he hf k hk
    simp [Pi.mulSingle_mul, he k hk, hf k hk]
  one_mem' := by intro k _; simp
  inv_mem' := by
    intro e he k hk
    rw [Pi.mulSingle_inv, map_inv, Pi.inv_apply, he k hk, inv_one]

instance (y : MulAut (PX a)) (j i : ι) : (Kj y j i).Normal where
  conj_mem e he g k hk := by
    have : Pi.mulSingle j (g * e * g⁻¹) =
        (Pi.mulSingle j g : PX a) * Pi.mulSingle j e * (Pi.mulSingle j g)⁻¹ := by
      rw [Pi.mulSingle_mul, Pi.mulSingle_mul, Pi.mulSingle_inv]
    show y (Pi.mulSingle j (g * e * g⁻¹)) k = 1
    rw [this, map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, he k hk]
    simp

theorem sig1 {j i : ι} (hj : 2 ≤ a j) (y : MulAut (PX a)) (d : DihedralGroup (2 ^ a j))
    (h : DihedralGroup (2 ^ a i))
    (hne : y (Pi.mulSingle j d) * Pi.mulSingle i h ≠ Pi.mulSingle i h * y (Pi.mulSingle j d)) :
    2 ≤ a i ∧ y (zz a j) = zz a i := by
  set u := y (Pi.mulSingle j d) with hu
  set w : PX a := Pi.mulSingle i h with hw
  have hc1 : u⁻¹ * w⁻¹ * u * w ≠ 1 := by
    intro hc
    apply hne
    have h3 : w⁻¹ * u * w = u := by
      calc w⁻¹ * u * w = u * (u⁻¹ * w⁻¹ * u * w) := by group
        _ = u := by rw [hc, mul_one]
    calc u * w = w * (w⁻¹ * u * w) := by group
      _ = w * u := by rw [h3]
  obtain ⟨d', hd'⟩ : ∃ d', w⁻¹ * u * w = y (Pi.mulSingle j d') := by
    refine ⟨(y.symm w)⁻¹ j * d * ((y.symm w)⁻¹ j)⁻¹, ?_⟩
    rw [← conj_mulSingle]
    simp [hu]
  have hce : y (Pi.mulSingle j (d⁻¹ * d')) = u⁻¹ * w⁻¹ * u * w := by
    rw [Pi.mulSingle_mul, Pi.mulSingle_inv, map_mul, map_inv, mul_assoc, mul_assoc, ← mul_assoc w⁻¹,
      hd']
  have hmem : d⁻¹ * d' ∈ Kj y j i := by
    intro k hk
    rw [hce]
    simp [hw, Pi.mulSingle_eq_of_ne hk]
  have hne1 : d⁻¹ * d' ≠ 1 := by
    intro h1
    rw [h1] at hce
    simp at hce
    exact hc1 hce.symm
  have hz := zc_mem_of_normal hj (Kj y j i) hmem hne1
  have hz' : ∀ k, k ≠ i → y (zz a j) k = 1 := hz
  have hcen : ∀ x, x * y (zz a j) = y (zz a j) * x := by
    intro x
    apply y.symm.injective
    simp [zz_comm j (by omega) (y.symm x)]
  have hi2 : 2 ≤ a i := by
    by_contra hlt
    apply hne
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hw, mul_comm_of_le_one (by omega : a k ≤ 1)]
    · simp [hw, Pi.mulSingle_eq_of_ne hk]
  refine ⟨hi2, ?_⟩
  have hcent := (comm_mulSingle_iff (y (zz a j))).mp (fun i h => (hcen _).symm) i
  rcases eq_one_or_zc_of_comm hi2 (fun g => (hcent g).symm) with h1 | h1
  · exfalso
    have : y (zz a j) = 1 := by
      ext k
      by_cases hk : k = i
      · subst hk; simpa using h1
      · simpa using hz' k hk
    rw [← map_one y] at this
    exact zz_ne_one j (by omega) (y.injective this)
  · ext k
    by_cases hk : k = i
    · subst hk; rw [zz_apply_same]; exact h1
    · rw [zz_apply_ne hk]; exact hz' k hk

theorem sig_le {j i : ι} (hj : 1 ≤ a j) (hi : 1 ≤ a i) (y : MulAut (PX a))
    (h : y (zz a j) = zz a i) : a j ≤ a i := by
  by_contra hlt
  push_neg at hlt
  have h1 := congrFun h i
  rw [zz_eq_pow j hj, map_pow, Pi.pow_apply, zz_apply_same] at h1
  have := pow_two_pow_eq_one hi (Nat.le_sub_one_of_lt hlt)
    (y (Pi.mulSingle j (r 1 : DihedralGroup (2 ^ a j))) i)
  rw [this] at h1
  exact zc_ne_one hi h1.symm

theorem sig2 {j : ι} (hj : 2 ≤ a j) (y : MulAut (PX a)) :
    ∃ i, ∃ (d : DihedralGroup (2 ^ a j)) (h : DihedralGroup (2 ^ a i)),
      y (Pi.mulSingle j d) * Pi.mulSingle i h ≠ Pi.mulSingle i h * y (Pi.mulSingle j d) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨g, g', hgg⟩ := not_comm_of_two_le hj
  have hg := (comm_mulSingle_iff (y (Pi.mulSingle j g))).mp (fun i h => hcon i g h)
  apply hgg
  apply (Pi.mulSingle_injective j)
  apply y.injective
  rw [Pi.mulSingle_mul, Pi.mulSingle_mul, map_mul, map_mul]
  ext k
  simp [hg k]

theorem sig {j : ι} (hj : 2 ≤ a j) (y : MulAut (PX a)) :
    ∃ i, 2 ≤ a i ∧ a j ≤ a i ∧ y (zz a j) = zz a i ∧
      ∀ k, k ≠ i → ∀ (d : DihedralGroup (2 ^ a j)) (h : DihedralGroup (2 ^ a k)),
        y (Pi.mulSingle j d) * Pi.mulSingle k h = Pi.mulSingle k h * y (Pi.mulSingle j d) := by
  obtain ⟨i, d, h, hne⟩ := sig2 hj y
  obtain ⟨hi2, hz⟩ := sig1 hj y d h hne
  refine ⟨i, hi2, sig_le (by omega) (by omega) y hz, hz, ?_⟩
  intro k hk d' h'
  by_contra hne'
  obtain ⟨hk2, hz'⟩ := sig1 hj y d' h' hne'
  exact hk (zz_injective (by omega) (by omega) (hz.symm.trans hz')).symm

end CFSG.CGT.Foote81L6
