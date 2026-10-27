module

public import CFSG.GH74.Generic.BProg.B2.WeakSigCaseBAux

public section

namespace CFSG.GH74.Generic.BProg.B2.WeakSigCaseB

open CFSG Subgroup

section N

variable {Y : Type} [Group Y]

theorem mem_zpowers_of_odd_mul [Finite Y] {a u : Y} (hcomm : a * u = u * a)
    (hu : ∃ n : ℕ, u ^ (2 ^ n) = 1) (hodd : Odd (orderOf (a * u))) : u ∈ Subgroup.zpowers a := by
  obtain ⟨n, hn⟩ := hu
  set m : ℕ := orderOf (a * u) with hm
  have hmu : (a * u) ^ m = 1 := pow_orderOf_eq_one _
  have hc : Commute a u := hcomm
  rw [hc.mul_pow] at hmu
  have hum : u ^ m = (a ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hmu
  have hord : orderOf u ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (orderOf u) m :=
    Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd))
  obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := u) (n := m) hcop.symm
  rw [← hk, hum, inv_pow, ← pow_mul, ← zpow_natCast, ← zpow_neg]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) _

theorem false_of_odd_centralizing [Finite Y] {C : Subgroup Y} {c a : Y} (hcC : c ∈ C)
    (hc2 : ∃ n : ℕ, c ^ (2 ^ n) = 1) (hcn : ∃ y ∈ C, y * c ≠ c * y)
    (ha : ∀ y ∈ C, y * a = a * y) (hodd : Odd (orderOf (a * c⁻¹))) : False := by
  have hu2 : ∃ n : ℕ, c⁻¹ ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hc2
    exact ⟨n, by rw [inv_pow, hn, inv_one]⟩
  have hac : a * c⁻¹ = c⁻¹ * a := ((ha c hcC).symm : a * c = c * a) |> fun h => by
    exact (Commute.inv_right (show Commute a c from h)).eq
  have hmem := mem_zpowers_of_odd_mul hac hu2 hodd
  obtain ⟨y, hyC, hy⟩ := hcn
  apply hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hya : Commute y a := ha y hyC
  have hyc : Commute y c⁻¹ := by rw [← hk]; exact hya.zpow_right k
  exact (inv_inv c ▸ hyc.inv_right).eq

theorem mem_of_sq_mem_of_odd {N : Subgroup Y} {w : Y} (h : w * w ∈ N) (hodd : Odd (orderOf w)) :
    w ∈ N := by
  obtain ⟨j, hj⟩ := hodd
  have h1 : w ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one w
  have h3 : w ^ (2 * j + 1) = (w * w) ^ j * w := by rw [pow_succ, pow_mul, sq]
  rw [h3] at h1
  have h2 : w = ((w * w) ^ j)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact N.inv_mem (N.pow_mem h j)

theorem normalizes_of_diag [Finite Y] {L W : Subgroup Y} {s c : Y} (hL : IsComponent L)
    (hW : Odd (Nat.card ↥W)) (hss : s * s = 1) (hs : s ∉ normalizer (L : Set Y)) (hcL : c ∈ L)
    (hc2 : ∃ n : ℕ, c ^ (2 ^ n) = 1) (hcn : ∃ y ∈ L, y * c ≠ c * y)
    (hx : c * (s * c * s⁻¹) ∈ normalizer (W : Set Y)) : W ≤ normalizer (L : Set Y) := by
  intro w hw
  obtain ⟨v, hv⟩ : ∃ v : Y, v = s * c * s⁻¹ := ⟨_, rfl⟩
  rw [← hv] at hx
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hL₂ : IsComponent (conjugate L s) := isComponent_conjugate hL s
  have hne12 : L ≠ conjugate L s := fun h => hs (conjugate_eq_self_iff.mp h.symm)
  have hsss : ∀ z : Y, s * (s * z * s⁻¹) * s⁻¹ = z := fun z => by
    calc s * (s * z * s⁻¹) * s⁻¹ = (s * s) * z * (s * s)⁻¹ := by group
      _ = z := by rw [hss]; simp
  have hvL₂ : v ∈ conjugate L s := by
    rw [mem_conjugate_iff, hv, hsss]; exact hcL
  have hcv : c * v = v * c := commute_of_ne hL hL₂ hne12 c hcL v hvL₂
  have hodd_w : Odd (orderOf w) := Odd.of_dvd_nat hW (Subgroup.orderOf_dvd_natCard W hw)
  have hL₃ : IsComponent (conjugate L w⁻¹) := isComponent_conjugate hL w⁻¹
  have hL₄ : IsComponent (conjugate (conjugate L s) w⁻¹) :=
    isComponent_conjugate hL₂ w⁻¹
  have hc'm : w * c * w⁻¹ ∈ conjugate L w⁻¹ := by
    rw [mem_conjugate_iff]
    have e : w⁻¹ * (w * c * w⁻¹) * w⁻¹⁻¹ = c := by group
    rw [e]; exact hcL
  have hv'm : w * v * w⁻¹ ∈ conjugate (conjugate L s) w⁻¹ := by
    rw [mem_conjugate_iff]
    have e : w⁻¹ * (w * v * w⁻¹) * w⁻¹⁻¹ = v := by group
    rw [e]; exact hvL₂
  have ht : (w * (c * v) * w⁻¹) * (c * v)⁻¹ ∈ W := by
    have h1 : (c * v) * w⁻¹ * (c * v)⁻¹ ∈ W := (mem_normalizer_iff.mp hx w⁻¹).mp (W.inv_mem hw)
    have h2 : w * ((c * v) * w⁻¹ * (c * v)⁻¹) ∈ W := W.mul_mem hw h1
    simpa [mul_assoc] using h2
  have hodd_t : Odd (orderOf ((w * (c * v) * w⁻¹) * (c * v)⁻¹)) :=
    Odd.of_dvd_nat hW (Subgroup.orderOf_dvd_natCard W ht)
  have hxx' : w * (c * v) * w⁻¹ = (w * c * w⁻¹) * (w * v * w⁻¹) := by group
  have hA : L = conjugate L w⁻¹ ∨ L = conjugate (conjugate L s) w⁻¹ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hy3 := commute_of_ne hL hL₃ h1
    have hy4 := commute_of_ne hL hL₄ h2
    have hy2 := commute_of_ne hL hL₂ hne12
    have ha : ∀ y ∈ L, y * ((w * c * w⁻¹) * (w * v * w⁻¹) * v⁻¹) =
        ((w * c * w⁻¹) * (w * v * w⁻¹) * v⁻¹) * y := by
      intro y hy
      have e1 : Commute y (w * c * w⁻¹) := hy3 y hy _ hc'm
      have e2 : Commute y (w * v * w⁻¹) := hy4 y hy _ hv'm
      have e3 : Commute y v⁻¹ := (show Commute y v from hy2 y hy v hvL₂).inv_right
      exact ((e1.mul_right e2).mul_right e3).eq
    have hteq : (w * (c * v) * w⁻¹) * (c * v)⁻¹ =
        ((w * c * w⁻¹) * (w * v * w⁻¹) * v⁻¹) * c⁻¹ := by
      rw [hxx', mul_inv_rev]; group
    rw [hteq] at hodd_t
    exact false_of_odd_centralizing hcL hc2 hcn ha hodd_t
  have hB : conjugate L s = conjugate L w⁻¹ ∨
      conjugate L s = conjugate (conjugate L s) w⁻¹ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hy3 := commute_of_ne hL₂ hL₃ h1
    have hy4 := commute_of_ne hL₂ hL₄ h2
    have hy1 := commute_of_ne hL₂ hL hne12.symm
    have ha : ∀ y ∈ conjugate L s, y * ((w * c * w⁻¹) * (w * v * w⁻¹) * c⁻¹) =
        ((w * c * w⁻¹) * (w * v * w⁻¹) * c⁻¹) * y := by
      intro y hy
      have e1 : Commute y (w * c * w⁻¹) := hy3 y hy _ hc'm
      have e2 : Commute y (w * v * w⁻¹) := hy4 y hy _ hv'm
      have e3 : Commute y c⁻¹ := (show Commute y c from hy1 y hy c hcL).inv_right
      exact ((e1.mul_right e2).mul_right e3).eq
    have hteq : (w * (c * v) * w⁻¹) * (c * v)⁻¹ =
        ((w * c * w⁻¹) * (w * v * w⁻¹) * c⁻¹) * v⁻¹ := by
      rw [hxx', hcv, mul_inv_rev]; group
    rw [hteq] at hodd_t
    have hv2 : ∃ n : ℕ, v ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := hc2
      exact ⟨n, by rw [hv, conj_pow, hn]; simp⟩
    have hvn : ∃ y ∈ conjugate L s, y * v ≠ v * y := by
      obtain ⟨y₀, hy₀L, hy₀⟩ := hcn
      refine ⟨s * y₀ * s⁻¹, ?_, fun h => hy₀ ?_⟩
      · rw [mem_conjugate_iff, hsss]; exact hy₀L
      · have e1 : y₀ * c = s⁻¹ * ((s * y₀ * s⁻¹) * v) * s := by rw [hv]; group
        have e2 : c * y₀ = s⁻¹ * (v * (s * y₀ * s⁻¹)) * s := by rw [hv]; group
        rw [e1, e2, h]
    exact false_of_odd_centralizing hvL₂ hv2 hvn ha hodd_t
  rcases hA with hA | hA
  · exact by simpa using inv_mem (conjugate_eq_self_iff.mp hA.symm)
  · rcases hB with hB | hB
    · have h1 : conjugate L (w⁻¹ * w⁻¹) = L := by
        rw [← conjugate_conjugate, ← hB]; exact hA.symm
      have hsq : w * w ∈ normalizer (L : Set Y) := by
        have := inv_mem (conjugate_eq_self_iff.mp h1)
        simpa [mul_inv_rev] using this
      exact mem_of_sq_mem_of_odd hsq hodd_w
    · exact absurd (hA.trans hB.symm) hne12

end N

end CFSG.GH74.Generic.BProg.B2.WeakSigCaseB
