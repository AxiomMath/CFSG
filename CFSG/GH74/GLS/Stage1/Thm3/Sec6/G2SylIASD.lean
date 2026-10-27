module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo
public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl

namespace SDQ

open CFSG.Semidihedral CFSG.Open

theorem rpow_mul_s (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    r n ^ k * s n = element n hn (k : ZMod (modulus n)) 1 := by
  rw [r_pow_eq_element n hn, s_eq_element n hn, element_rotation_mul, add_zero]

theorem rs_eq (n : ℕ) (hn : 3 ≤ n) : r n * s n = element n hn 1 1 := by
  simpa using rpow_mul_s n hn 1

theorem w_conj_c (n : ℕ) (hn : 3 ≤ n) :
    (r n * s n) * r n ^ 2 * (r n * s n)⁻¹ = (r n ^ 2)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
  rw [rs_eq n hn, r_pow_eq_element n hn 2, element_reflection_mul, element_rotation_mul,
    element_eq_iff]
  have hh := two_mul_half_residue n hn
  refine ⟨?_, by decide⟩
  simp only [twist]
  push_cast
  linear_combination hh

theorem w_sq (n : ℕ) (hn : 3 ≤ n) : (r n * s n) * (r n * s n) = z n := by
  simpa [sq] using reflection_square_nat n hn 1

theorem c_pow_quarter (n : ℕ) (hn : 3 ≤ n) : (r n ^ 2) ^ (2 ^ (n - 3)) = z n := by
  rw [← pow_mul, z, half_eq_two_mul_quarter hn]

theorem c_pow_half (n : ℕ) (hn : 3 ≤ n) : (r n ^ 2) ^ (2 ^ (n - 2)) = 1 := by
  have : 2 ^ (n - 2) = 2 ^ (n - 3) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [this, pow_mul, c_pow_quarter n hn, z_sq n hn]

theorem y_sq (n : ℕ) (hn : 3 ≤ n) (j : ℕ) :
    (r n ^ (2 * j) * s n) * (r n ^ (2 * j) * s n) = 1 := by
  have h := reflection_square_nat n hn (2 * j)
  rw [sq] at h
  rw [h, pow_mul, z_sq n hn, one_pow]

theorem y_conj_c (n : ℕ) (hn : 3 ≤ n) (j : ℕ) :
    (r n ^ (2 * j) * s n) * r n ^ 2 * (r n ^ (2 * j) * s n)⁻¹ = (r n ^ 2)⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, eq_inv_mul_iff_mul_eq]
  rw [rpow_mul_s n hn, r_pow_eq_element n hn 2, element_reflection_mul, element_rotation_mul,
    element_eq_iff]
  have hh := two_mul_half_residue n hn
  refine ⟨?_, by decide⟩
  simp only [twist]
  push_cast
  linear_combination hh

theorem y_conj_w (n : ℕ) (hn : 4 ≤ n) (j : ℕ) :
    (r n ^ (2 * j) * s n) * (r n * s n) * (r n ^ (2 * j) * s n)⁻¹ =
      (r n ^ 2) ^ (2 * j + 2 ^ (n - 3) - 1) * (r n * s n) := by
  have hn3 : 3 ≤ n := by omega
  rw [mul_inv_eq_iff_eq_mul]
  rw [← pow_mul, rpow_mul_s n hn3, rs_eq n hn3, r_pow_eq_element n hn3,
    element_reflection_mul, element_rotation_mul, element_reflection_mul, element_eq_iff]
  have hh := two_mul_half_residue n hn3
  have hq : (half n : ZMod (modulus n)) = 2 * ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) := by
    rw [half_eq_two_mul_quarter hn3]; push_cast; ring
  have hpos : 1 ≤ 2 * j + 2 ^ (n - 3) := by
    have := Nat.one_le_two_pow (n := n - 3); omega
  have hk : ((2 * (2 * j + 2 ^ (n - 3) - 1) : ℕ) : ZMod (modulus n)) =
      2 * (2 * (j : ZMod (modulus n)) + ((2 ^ (n - 3) : ℕ) : ZMod (modulus n)) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hpos]; push_cast; ring
  refine ⟨?_, by decide⟩
  simp only [twist]
  rw [hk]
  push_cast at hq ⊢
  linear_combination hq - (j : ZMod (modulus n)) * hh

theorem r_sq_ne_one (n : ℕ) (hn : 3 ≤ n) : r n ^ 2 ≠ 1 := by
  intro h
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_r n hn] at h1
  have h2 := Nat.le_of_dvd (by norm_num) h1
  have h3 : 4 ≤ 2 ^ (n - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [modulus] at h2
  omega

theorem s_sq_eq (n : ℕ) : s n * s n = 1 := by
  rw [← sq]; exact s_sq n

theorem s_ne_one (n : ℕ) (hn : 3 ≤ n) : s n ≠ 1 := by
  intro h
  have := orderOf_s n hn
  rw [h, orderOf_one] at this
  omega

section Quat

open QuaternionGroup

theorem natCast_ne_zero_two_mul (N : ℕ) [NeZero N] : ((N : ℕ) : ZMod (2 * N)) ≠ 0 := by
  intro h
  have h1 := (ZMod.natCast_eq_zero_iff N (2 * N)).1 h
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h2 := Nat.le_of_dvd hpos h1
  omega

theorem zmod_add_self_eq_zero (N : ℕ) [NeZero N] (j : ZMod (2 * N)) (h : j + j = 0) :
    j = 0 ∨ j = (N : ZMod (2 * N)) := by
  have h1 : ((2 * j.val : ℕ) : ZMod (2 * N)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination h
  have h2 := (ZMod.natCast_eq_zero_iff (2 * j.val) (2 * N)).1 h1
  have h3 : N ∣ j.val := by
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [hc]; ring)⟩
  have hv : j.val < 2 * N := ZMod.val_lt j
  obtain ⟨c, hc⟩ := h3
  have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc2 : c = 0 ∨ c = 1 := by
    have : c < 2 := by
      by_contra hcon
      push Not at hcon
      have : N * 2 ≤ N * c := Nat.mul_le_mul_left N hcon
      omega
    omega
  rcases hc2 with rfl | rfl
  · left
    have : j.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val j, this]
    simp
  · right
    have : j.val = N := by omega
    rw [← ZMod.natCast_zmod_val j, this]

theorem quat_sq_eq_one {N : ℕ} [NeZero N] (g : QuaternionGroup N) (hg : g * g = 1) :
    g = 1 ∨ g = a (N : ZMod (2 * N)) := by
  cases g with
  | a i =>
    rw [a_mul_a, one_def] at hg
    have h := QuaternionGroup.a.inj hg
    rcases zmod_add_self_eq_zero N i h with h0 | h0
    · left; rw [h0, one_def]
    · right; rw [h0]
  | xa i =>
    rw [xa_mul_xa, one_def] at hg
    have h := QuaternionGroup.a.inj hg
    exfalso
    apply natCast_ne_zero_two_mul N
    linear_combination h

theorem quat_central {N : ℕ} [NeZero N] (hN : 2 ≤ N) (g : QuaternionGroup N)
    (hg : ∀ h : QuaternionGroup N, h * g = g * h) :
    g = 1 ∨ g = a (N : ZMod (2 * N)) := by
  cases g with
  | a i =>
    have h := hg (xa 0)
    rw [xa_mul_a, a_mul_xa] at h
    have h' := QuaternionGroup.xa.inj h
    rcases zmod_add_self_eq_zero N i (by linear_combination h') with h0 | h0
    · left; rw [h0, one_def]
    · right; rw [h0]
  | xa i =>
    exfalso
    have h := hg (a 1)
    rw [a_mul_xa, xa_mul_a] at h
    have h' := QuaternionGroup.xa.inj h
    have h2 : ((2 : ℕ) : ZMod (2 * N)) = 0 := by
      push_cast
      linear_combination -h'
    have hdvd := (ZMod.natCast_eq_zero_iff 2 (2 * N)).mp h2
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    omega

theorem quat_mul_ne {N : ℕ} (hN : 2 ≤ N) : (a 1 : QuaternionGroup N) * xa 0 ≠ xa 0 * a 1 := by
  rw [a_mul_xa, xa_mul_a]
  intro h
  have h' : (0 : ZMod (2 * N)) - 1 = 0 + 1 := QuaternionGroup.xa.inj h
  have h2 : ((2 : ℕ) : ZMod (2 * N)) = 0 := by
    push_cast
    linear_combination -h'
  have hdvd := (ZMod.natCast_eq_zero_iff 2 (2 * N)).mp h2
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

variable {X : Type} [Group X]

theorem quat_facts {P : Subgroup X} {z : X} {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (θ : ↥P ≃* QuaternionGroup N) (hzP : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    (∀ x ∈ P, x * x = 1 → x ≠ 1 → x = z) ∧
    (∀ x ∈ P, (∀ p ∈ P, p * x = x * p) → x = 1 ∨ x = z) ∧
    ¬ ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  have key : ∀ (x : X) (hx : x ∈ P), x * x = 1 → x ≠ 1 →
      θ ⟨x, hx⟩ = QuaternionGroup.a (N : ZMod (2 * N)) := by
    intro x hx hx2 hx1
    have h : θ ⟨x, hx⟩ * θ ⟨x, hx⟩ = 1 := by
      rw [← map_mul, ← map_one θ]
      congr 1
      exact Subtype.ext hx2
    rcases quat_sq_eq_one _ h with h1 | h1
    · exfalso
      apply hx1
      have := θ.injective (h1.trans (map_one θ).symm)
      simpa using congrArg Subtype.val this
    · exact h1
  have hzθ := key z hzP hz2 hz1
  refine ⟨fun x hx hx2 hx1 => ?_, fun x hx hc => ?_, fun hc => ?_⟩
  · have h1 := key x hx hx2 hx1
    exact congrArg Subtype.val (θ.injective (h1.trans hzθ.symm))
  · rcases quat_central hN (θ ⟨x, hx⟩) (fun h => by
        obtain ⟨p, rfl⟩ := θ.surjective h
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hc p.1 p.2)) with h | h
    · left
      have := θ.injective (h.trans (map_one θ).symm)
      simpa using congrArg Subtype.val this
    · right
      exact congrArg Subtype.val (θ.injective (h.trans hzθ.symm))
  · apply quat_mul_ne hN
    have h1 : θ.symm (QuaternionGroup.a 1) * θ.symm (QuaternionGroup.xa 0) =
        θ.symm (QuaternionGroup.xa 0) * θ.symm (QuaternionGroup.a 1) :=
      Subtype.ext (hc _ (θ.symm (QuaternionGroup.a 1)).2 _ (θ.symm (QuaternionGroup.xa 0)).2)
    simpa using congrArg θ h1

end Quat

section Decomp

variable {X : Type} [Group X]

theorem mem_sup_cases {P : Subgroup X} {y : X} (hyy : y * y = 1)
    (hnorm : ∀ x ∈ P, y * x * y⁻¹ ∈ P) {h : X} (hh : h ∈ P ⊔ Subgroup.zpowers y) :
    h ∈ P ∨ h * y ∈ P := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  let Wd : Subgroup X :=
    { carrier := {g | g ∈ P ∨ g * y ∈ P}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (P.mul_mem ha hb)
        · refine Or.inr ?_
          rw [mul_assoc]
          exact P.mul_mem ha hb
        · refine Or.inr ?_
          have e : a * b * y = (a * y) * (y * b * y⁻¹) := by
            rw [hyinv]
            calc a * b * y = a * (y * y) * b * y := by rw [hyy, mul_one]
              _ = a * y * (y * b * y) := by simp only [mul_assoc]
          rw [e]
          exact P.mul_mem ha (hnorm b hb)
        · refine Or.inl ?_
          have e : a * b = (a * y) * (y * (b * y) * y⁻¹) := by
            rw [hyinv]
            calc a * b = a * (y * y) * b * (y * y) := by rw [hyy]; simp
              _ = a * y * (y * (b * y) * y) := by simp only [mul_assoc]
          rw [e]
          exact P.mul_mem ha (hnorm _ hb)
      one_mem' := Or.inl P.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (P.inv_mem ha)
        · refine Or.inr ?_
          have h1 : y * a⁻¹ ∈ P := by
            have := P.inv_mem ha
            rwa [mul_inv_rev, hyinv] at this
          have e : a⁻¹ * y = y * (y * a⁻¹) * y⁻¹ := by
            rw [hyinv]
            calc a⁻¹ * y = (y * y) * a⁻¹ * y := by rw [hyy, one_mul]
              _ = y * (y * a⁻¹) * y := by simp only [mul_assoc]
          rw [e]
          exact hnorm _ h1 }
  have hle : P ⊔ Subgroup.zpowers y ≤ Wd :=
    sup_le (fun x hx => Or.inl hx)
      (Subgroup.zpowers_le.2 (Or.inr (by rw [hyy]; exact P.one_mem)))
  exact hle hh

end Decomp

section Core

variable {X : Type} [Group X]

theorem sdq_core {P : Subgroup X} {y ze : X} {nP mP : ℕ}
    (ψ : SemidihedralGroup mP →* X) (hψ : Function.Injective ψ)
    (hyy : y * y = 1) (hyP : y ∉ P) (hzP : ze ∈ P) (hz2 : ze * ze = 1) (hz1 : ze ≠ 1)
    (hdec : ∀ g, ψ g ∈ P ∨ ψ g * y ∈ P) (hPr : ∀ x ∈ P, ∃ g, ψ g = x)
    (hyr : ∃ g, ψ g = y)
    (θ : ↥P ≃* QuaternionGroup (2 ^ (nP - 2))) (hn3P : 3 ≤ nP) (hm4 : 4 ≤ mP) :
    ∃ (c w : X) (k : ℕ), c ∈ P ∧ w ∈ P ∧ P = Subgroup.closure {c, w} ∧ Odd k ∧
      c ^ (2 ^ (nP - 1)) = 1 ∧ c ^ (2 ^ (nP - 2)) = ze ∧ w * w = ze ∧ w * c * w⁻¹ = c⁻¹ ∧
      y * c * y⁻¹ = c⁻¹ ∧ y * w * y⁻¹ = c ^ k * w ∧
      (∀ x ∈ P, (∀ p ∈ P, p * x = x * p) → x = 1 ∨ x = ze) := by
  have hm3 : 3 ≤ mP := by omega
  set E : Subgroup (SemidihedralGroup mP) := P.comap ψ with hEdef
  have hmem : ∀ g, g ∈ E ↔ ψ g ∈ P := fun g => Iff.rfl
  obtain ⟨gy, hgy⟩ := hyr
  have hgyE : gy ∉ E := fun h => hyP (hgy ▸ (hmem gy).1 h)
  have hEidx : E.index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨gy, hgyE, fun b => ?_⟩
    rcases hdec b with h | h
    · exact Or.inr ((hmem b).2 h)
    · exact Or.inl ((hmem _).2 (by rw [map_mul, hgy]; exact h))
  have : NeZero (2 ^ (nP - 2)) := ⟨by positivity⟩
  have hN2 : 2 ≤ 2 ^ (nP - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (nP - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hinvP, hcenter, hnc⟩ := quat_facts hN2 θ hzP hz2 hz1
  have hinvψ : ∀ g : SemidihedralGroup mP, g ∈ E → g * g = 1 → g ≠ 1 → ψ g = ze := by
    intro g hg hg2 hg1
    apply hinvP (ψ g) ((hmem g).1 hg)
    · rw [← map_mul, hg2, map_one]
    · intro h
      apply hg1
      exact hψ (by rw [h, map_one])
  have hEcard : Nat.card E = modulus mP := indexTwo_natCard mP hm3 E hEidx
  have hPcard : Nat.card P = 4 * 2 ^ (nP - 2) := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hEP : Nat.card E = Nat.card P := by
    refine Nat.card_congr (Equiv.ofBijective (fun e : E => (⟨ψ e, (hmem e).1 e.2⟩ : P)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (hψ (congrArg Subtype.val hab))
    · intro x
      obtain ⟨g, hg⟩ := hPr x.1 x.2
      exact ⟨⟨g, (hmem g).2 (hg ▸ x.2)⟩, Subtype.ext hg⟩
  have h4 : 4 * 2 ^ (nP - 2) = 2 ^ nP := by
    have : nP = (nP - 2) + 2 := by omega
    conv_rhs => rw [this, pow_add]
    ring
  have hmn : mP = nP + 1 := by
    have h1 : 2 ^ (mP - 1) = 2 ^ nP := by
      rw [← h4, ← hPcard, ← hEP, hEcard]
      rfl
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  rcases (index_eq_two_iff mP hm3 E).1 hEidx with hE | hE | hE
  ·
    exfalso
    apply hnc
    intro a ha b hb
    obtain ⟨g1, rfl⟩ := hPr a ha
    obtain ⟨g2, rfl⟩ := hPr b hb
    have h1 : g1 ∈ Subgroup.zpowers (r mP) := by
      have h := (hmem g1).2 ha
      rw [hE] at h
      exact h
    have h2 : g2 ∈ Subgroup.zpowers (r mP) := by
      have h := (hmem g2).2 hb
      rw [hE] at h
      exact h
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 h1
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 h2
    rw [← map_mul, ← map_mul, ← zpow_add, ← zpow_add, add_comm]
  ·
    exfalso
    have hsE : s mP ∈ E := hE ▸ s_mem_dihedralSubgroup mP
    have hr2E : r mP ^ 2 ∈ E := hE ▸ r_sq_mem_dihedralSubgroup mP
    have h1 := hinvψ (s mP) hsE (s_sq_eq mP) (s_ne_one mP hm3)
    have h2 := hinvψ (r mP ^ 2 * s mP) (E.mul_mem hr2E hsE)
      (by simpa using y_sq mP hm3 1)
      (by
        rw [rpow_mul_s mP hm3 2]
        simp)
    have h3 : s mP = r mP ^ 2 * s mP := hψ (h1.trans h2.symm)
    apply r_sq_ne_one mP hm3
    have h4 : r mP ^ 2 * s mP = 1 * s mP := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel h4
  ·
    have hr2E : r mP ^ 2 ∈ E := hE ▸ r_sq_mem_quaternionSubgroup mP
    have hrsE : r mP * s mP ∈ E := hE ▸ rs_mem_quaternionSubgroup mP
    have hzE : z mP ∈ E := by
      rw [← c_pow_quarter mP hm3]
      exact E.pow_mem hr2E _
    have hzψ : ψ (z mP) = ze :=
      hinvψ (z mP) hzE (by simpa [sq] using z_sq mP hm3) (z_ne_one mP hm3)
    have hgy2 : gy * gy = 1 := hψ (by rw [map_mul, hgy, hyy, map_one])
    have hgy1 : gy ≠ 1 := fun h => hyP (by rw [← hgy, h, map_one]; exact P.one_mem)
    have hgyord : orderOf gy = 2 := orderOf_eq_prime (by rw [sq]; exact hgy2) hgy1
    obtain ⟨j, hj⟩ : ∃ j : ℕ, gy = r mP ^ (2 * j) * s mP := by
      rcases (involution_iff mP hm3 gy).1 hgyord with h | ⟨j, hj⟩
      · exact absurd (h ▸ hzE) hgyE
      · exact ⟨j.val, hj⟩
    have hy' : y = ψ (r mP ^ (2 * j) * s mP) := by rw [← hgy, hj]
    have hq1 : 2 ^ (mP - 3) = 2 * 2 ^ (mP - 4) := by
      rw [← pow_succ']; congr 1; omega
    have hq2 : 0 < 2 ^ (mP - 4) := by positivity
    refine ⟨ψ (r mP ^ 2), ψ (r mP * s mP), 2 * j + 2 ^ (mP - 3) - 1, (hmem _).1 hr2E,
      (hmem _).1 hrsE, ?_, ⟨j + 2 ^ (mP - 4) - 1, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, hcenter⟩
    · apply le_antisymm
      · intro x hx
        obtain ⟨g, rfl⟩ := hPr x hx
        have hg : g ∈ Subgroup.closure {r mP ^ 2, r mP * s mP} := by
          have h := (hmem g).2 hx
          rw [hE] at h
          exact h
        have h1 : ψ g ∈ (Subgroup.closure {r mP ^ 2, r mP * s mP}).map ψ :=
          Subgroup.mem_map_of_mem ψ hg
        rwa [MonoidHom.map_closure, Set.image_pair] at h1
      · rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact (hmem _).1 hr2E
        · exact (hmem _).1 hrsE
    · rw [← map_pow, show nP - 1 = mP - 2 by omega, c_pow_half mP hm3, map_one]
    · rw [← map_pow, show nP - 2 = mP - 3 by omega, c_pow_quarter mP hm3, hzψ]
    · rw [← map_mul, w_sq mP hm3, hzψ]
    · have := congrArg ψ (w_conj_c mP hm3)
      simpa only [map_mul, map_inv] using this
    · rw [hy']
      have := congrArg ψ (y_conj_c mP hm3 j)
      simpa only [map_mul, map_inv] using this
    · rw [hy']
      have := congrArg ψ (y_conj_w mP hm4 j)
      simpa only [map_mul, map_inv, map_pow] using this

end Core

end SDQ

theorem sdq_data {X : Type} [Group X] {P : Subgroup X} {y z : X} {nP mP : ℕ}
    (hyy : y * y = 1) (hyP : y ∉ P) (hnorm : ∀ x ∈ P, y * x * y⁻¹ ∈ P)
    (hzP : z ∈ P) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hPq : CFSG.GH74.GLS.IVK.IsQuaternionTwoGroup ↥P nP)
    (hsd : CFSG.GH74.GLS.IVK.IsSemidihedralTwoGroup ↥(P ⊔ Subgroup.zpowers y) mP) :
    ∃ (c w : X) (k : ℕ), c ∈ P ∧ w ∈ P ∧ P = Subgroup.closure {c, w} ∧ Odd k ∧
      c ^ (2 ^ (nP - 1)) = 1 ∧ c ^ (2 ^ (nP - 2)) = z ∧ w * w = z ∧ w * c * w⁻¹ = c⁻¹ ∧
      y * c * y⁻¹ = c⁻¹ ∧ y * w * y⁻¹ = c ^ k * w ∧
      (∀ x ∈ P, (∀ p ∈ P, p * x = x * p) → x = 1 ∨ x = z) := by
  obtain ⟨hn3P, ⟨θ⟩⟩ := hPq
  obtain ⟨hm4, ⟨φ⟩⟩ := hsd
  have hyH : y ∈ P ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  let ψ : CFSG.Open.SemidihedralGroup mP →* X :=
    (P ⊔ Subgroup.zpowers y).subtype.comp φ.symm.toMonoidHom
  refine SDQ.sdq_core ψ ?_ hyy hyP hzP hz2 hz1 ?_ ?_ ?_ θ hn3P hm4
  · exact Subtype.val_injective.comp φ.symm.injective
  · intro g
    exact SDQ.mem_sup_cases hyy hnorm (φ.symm g).2
  · intro x hx
    exact ⟨φ ⟨x, Subgroup.mem_sup_left hx⟩, by simp [ψ]⟩
  · exact ⟨φ ⟨y, hyH⟩, by simp [ψ]⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl
