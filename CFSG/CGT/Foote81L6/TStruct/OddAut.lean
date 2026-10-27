module

public import CFSG.CGT.Foote81L6.Part2

public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

private theorem mulAut_pow_apply_eq_iterate {G : Type*} [Group G] (Ψ : MulAut G) (f : G →* G)
    (h : ∀ x, Ψ x = f x) (m : ℕ) (x : G) : (Ψ ^ m) x = f^[m] x := by
  induction m with
  | zero => simp
  | succ m ih => rw [mulAut_pow_apply_succ, ih, h, Function.iterate_succ_apply']

section Pi

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {a : ι → ℕ}

theorem comm_central_mulSingle (y : MulAut (PX a)) {N : ℕ} (hN : Odd N) (hyN : y ^ N = 1)
    {j : ι} (hj : 2 ≤ a j) (hfix : y (zz a j) = zz a j) (g : DihedralGroup (2 ^ a j))
    (z : PX a) :
    z * ((Pi.mulSingle j g : PX a)⁻¹ * y (Pi.mulSingle j g)) =
      ((Pi.mulSingle j g : PX a)⁻¹ * y (Pi.mulSingle j g)) * z := by
  obtain ⟨i, hi2, -, hz, hcomm⟩ := sig hj y
  have hij : i = j := zz_injective (by omega) (by omega) (hz.symm.trans hfix)
  have hcomp : ∀ k, k ≠ j → ∀ (d : DihedralGroup (2 ^ a j)) (h : DihedralGroup (2 ^ a k)),
      (y (Pi.mulSingle j d)) k * h = h * (y (Pi.mulSingle j d)) k := fun k hk d h => by
    have := congrFun (hcomm k (by rwa [hij]) d h) k
    simpa using this
  let ψ : DihedralGroup (2 ^ a j) →* DihedralGroup (2 ^ a j) :=
    (Pi.evalMonoidHom (fun k => DihedralGroup (2 ^ a k)) j).comp
      (y.toMonoidHom.comp (MonoidHom.mulSingle (fun k => DihedralGroup (2 ^ a k)) j))
  have hψ : ∀ g, ψ g = y (Pi.mulSingle j g) j := fun _ => rfl
  have step : ∀ g : DihedralGroup (2 ^ a j), ∃ c : PX a, (∀ x, x * c = c * x) ∧
      y (Pi.mulSingle j g) = Pi.mulSingle j (ψ g) * c := by
    intro g
    refine ⟨(Pi.mulSingle j (ψ g))⁻¹ * y (Pi.mulSingle j g), ?_, by simp⟩
    refine central_of_comp fun k h => ?_
    by_cases hk : k = j
    · subst hk; simp [hψ]
    · simpa [Pi.mulSingle_eq_of_ne hk] using hcomp k hk g h
  have hyc : ∀ {c : PX a}, (∀ x, x * c = c * x) → ∀ x, x * y c = y c * x := by
    intro c hc x
    apply y.symm.injective
    simp [hc]
  have iter : ∀ m (g : DihedralGroup (2 ^ a j)), ∃ c : PX a, (∀ x, x * c = c * x) ∧
      (y ^ m) (Pi.mulSingle j g) = Pi.mulSingle j (ψ^[m] g) * c := by
    intro m
    induction m with
    | zero => intro g; exact ⟨1, fun x => by simp, by simp⟩
    | succ m ih =>
      intro g
      obtain ⟨c, hc1, hc3⟩ := ih g
      obtain ⟨c₁, hd1, hd3⟩ := step (ψ^[m] g)
      refine ⟨c₁ * y c, central_mul hd1 (hyc hc1), ?_⟩
      rw [mulAut_pow_apply_succ, hc3, map_mul, hd3, mul_assoc, Function.iterate_succ_apply']
  have hmodN : ∀ g : DihedralGroup (2 ^ a j), ∃ w, (∀ h, h * w = w * h) ∧ ψ^[N] g = g * w := by
    intro g
    obtain ⟨c, hc1, hc3⟩ := iter N g
    rw [hyN, MulAut.one_apply] at hc3
    have h1 : g = ψ^[N] g * c j := by
      have := congrFun hc3 j
      simpa using this
    refine ⟨(c j)⁻¹, fun h => ?_, eq_mul_inv_of_mul_eq h1.symm⟩
    have hcj : c j * h = h * c j := (comm_mulSingle_iff c).mp (fun k h' => (hc1 _).symm) j h
    calc h * (c j)⁻¹ = (c j)⁻¹ * (c j * h) * (c j)⁻¹ := by group
      _ = (c j)⁻¹ * (h * c j) * (c j)⁻¹ := by rw [hcj]
      _ = (c j)⁻¹ * h := by group
  have hzc : ψ (zc (a j)) = zc (a j) := by
    have e : (Pi.mulSingle j (zc (a j)) : PX a) = zz a j := by
      ext k
      by_cases hk : k = j
      · subst hk; rw [Pi.mulSingle_eq_same, zz_apply_same]
      · rw [Pi.mulSingle_eq_of_ne hk, zz_apply_ne hk]
    rw [hψ, e, hfix, zz_apply_same]
  have hcen : ∀ w : DihedralGroup (2 ^ a j), (∀ h, h * w = w * h) →
      ψ^[N] w = w ∧ w * w = 1 := by
    intro w hw
    rcases eq_one_or_zc_of_comm hj hw with rfl | rfl
    · exact ⟨iterate_map_one ψ N, one_mul 1⟩
    · exact ⟨Function.iterate_fixed hzc N, zc_mul_self (by omega)⟩
  have h2N : ∀ g, ψ^[2 * N] g = g := by
    intro g
    obtain ⟨w, hw, hgw⟩ := hmodN g
    rw [two_mul, Function.iterate_add_apply, hgw, iterate_map_mul, hgw, (hcen w hw).1, mul_assoc,
      (hcen w hw).2, mul_one]
  obtain ⟨Ψ, hΨ, hΨN⟩ := exists_mulAut_of_iterate ψ (by have := hN.pos; omega) h2N
  have hΨ2 : Ψ ^ 2 = 1 :=
    CFSG.ComponentClassification.HarrisLit.dihedral_mulAut_eq_one_of_odd hj (Ψ ^ 2) hN
      (by rw [← pow_mul]; exact hΨN)
  have hΨN' : Ψ ^ N = Ψ := by
    obtain ⟨k, hk⟩ := hN
    rw [hk, pow_succ, pow_mul, hΨ2, one_pow, one_mul]
  obtain ⟨c, hc1, hc3⟩ := step g
  obtain ⟨w, hw, hgw⟩ := hmodN g
  have hψw : ψ g = g * w := by
    rw [← hΨ, ← hΨN', mulAut_pow_apply_eq_iterate Ψ ψ hΨ, hgw]
  have e : (Pi.mulSingle j g : PX a)⁻¹ * y (Pi.mulSingle j g) = Pi.mulSingle j w * c := by
    rw [hc3, hψw, Pi.mulSingle_mul, mul_assoc, inv_mul_cancel_left]
  rw [e]
  have hwc : ∀ x : PX a, x * Pi.mulSingle j w = Pi.mulSingle j w * x := by
    refine central_of_comp fun k h => ?_
    by_cases hk : k = j
    · subst hk; simpa using (hw h).symm
    · simp [Pi.mulSingle_eq_of_ne hk]
  exact central_mul hwc hc1 z

theorem comm_central_of_fix (y : MulAut (PX a)) {N : ℕ} (hN : Odd N) (hyN : y ^ N = 1)
    (hfix : ∀ j, 2 ≤ a j → y (zz a j) = zz a j) (x z : PX a) :
    z * (x⁻¹ * y x) = (x⁻¹ * y x) * z := by
  revert z
  refine pi_induction (P := fun x => ∀ z : PX a, z * (x⁻¹ * y x) = (x⁻¹ * y x) * z)
    (fun z => by simp) (fun x w hx hw z => ?_) (fun j g => ?_) x
  · have e : (x * w)⁻¹ * y (x * w) = (x⁻¹ * y x) * (w⁻¹ * y w) := by
      rw [map_mul, mul_inv_rev]
      calc w⁻¹ * x⁻¹ * (y x * y w) = w⁻¹ * (x⁻¹ * y x) * y w := by simp only [mul_assoc]
        _ = (x⁻¹ * y x) * w⁻¹ * y w := by rw [hx w⁻¹]
        _ = (x⁻¹ * y x) * (w⁻¹ * y w) := by simp only [mul_assoc]
    rw [e]
    calc z * ((x⁻¹ * y x) * (w⁻¹ * y w)) = (z * (x⁻¹ * y x)) * (w⁻¹ * y w) :=
          (mul_assoc ..).symm
      _ = ((x⁻¹ * y x) * z) * (w⁻¹ * y w) := by rw [hx z]
      _ = (x⁻¹ * y x) * (z * (w⁻¹ * y w)) := mul_assoc ..
      _ = (x⁻¹ * y x) * ((w⁻¹ * y w) * z) := by rw [hw z]
      _ = ((x⁻¹ * y x) * (w⁻¹ * y w)) * z := (mul_assoc ..).symm
  · by_cases hj : 2 ≤ a j
    · exact comm_central_mulSingle y hN hyN hj (hfix j hj) g
    · have hc : ∀ x : PX a, x * Pi.mulSingle j g = Pi.mulSingle j g * x := by
        refine central_of_comp fun k h => ?_
        by_cases hk : k = j
        · subst hk; simp [mul_comm_of_le_one (by omega : a k ≤ 1)]
        · simp [Pi.mulSingle_eq_of_ne hk]
      have hyc : ∀ x : PX a, x * y (Pi.mulSingle j g) = y (Pi.mulSingle j g) * x := by
        intro x
        apply y.symm.injective
        simp [hc]
      have hci : ∀ x : PX a, x * (Pi.mulSingle j g)⁻¹ = (Pi.mulSingle j g)⁻¹ * x := fun x =>
        (show Commute x (Pi.mulSingle j g) from hc x).inv_right.eq
      exact central_mul hci hyc

end Pi

variable {a : Fin 3 → ℕ}

theorem fix_zz_of_le_one {i₀ : Fin 3} (hi₀ : a i₀ ≤ 1) (y : MulAut (PX a)) {N : ℕ} (hN : Odd N)
    (hyN : y ^ N = 1) (j : Fin 3) (hj : 2 ≤ a j) : y (zz a j) = zz a j := by
  obtain ⟨i, hi, -, hz, -⟩ := sig hj y
  by_cases hij : i = j
  · rw [hz, hij]
  exfalso
  obtain ⟨i', hi', -, hz', -⟩ := sig hi y
  have hii' : i' ≠ i := by
    rintro rfl
    exact hij (zz_injective (by omega) (by omega) (y.injective (hz.trans hz'.symm))).symm
  have h0i : i₀ ≠ i := fun h => by rw [h] at hi₀; omega
  have h0i' : i₀ ≠ i' := fun h => by rw [h] at hi₀; omega
  have h0j : i₀ ≠ j := fun h => by rw [h] at hi₀; omega
  have hi'j : i' = j := by omega
  rw [hi'j] at hz'
  obtain ⟨k, rfl⟩ := hN
  have key : ∀ m, (y ^ (2 * m)) (zz a j) = zz a j := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, mulAut_pow_apply_succ, mulAut_pow_apply_succ,
        ih, hz, hz']
  have h5 : (y ^ (2 * k + 1)) (zz a j) = zz a i := by rw [mulAut_pow_apply_succ, key, hz]
  rw [hyN, MulAut.one_apply] at h5
  exact hij (zz_injective (by omega) (by omega) h5).symm

theorem comm_central_or_transitive (y : MulAut (PX a)) {N : ℕ} (hN : Odd N) (hyN : y ^ N = 1) :
    (∀ x z : PX a, z * (x⁻¹ * y x) = (x⁻¹ * y x) * z) ∨
      ((∀ i, 2 ≤ a i) ∧ ∀ i j, ∃ m : ℕ, (y ^ m) (zz a i) = zz a j) := by
  by_cases hall : ∀ i, 2 ≤ a i
  · by_cases hy : y = 1
    · left
      intro x z
      simp [hy]
    · right
      obtain ⟨-, -, σ, hσ, htr⟩ := part2 a hall y hy hN hyN
      refine ⟨hall, fun i j => ?_⟩
      obtain ⟨m, hm⟩ := htr i j
      exact ⟨m, by rw [pow_zz y σ hσ m i, hm]⟩
  · push_neg at hall
    obtain ⟨i₀, hi₀⟩ := hall
    exact Or.inl (comm_central_of_fix y hN hyN fun j hj =>
      fix_zz_of_le_one (by omega : a i₀ ≤ 1) y hN hyN j hj)

end CFSG.CGT.Foote81L6
