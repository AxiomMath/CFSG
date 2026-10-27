module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.CharacterTheory.Semidihedral.DerivedAndIndexTwo
public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem t2OA_modEq_one_of_pow_odd {s N j : ℕ} (hN : Odd N) (h : j ^ N ≡ 1 [MOD 2 ^ s]) :
    j ≡ 1 [MOD 2 ^ s] := by
  rcases s with _ | s
  · exact Nat.modEq_one
  · have hu : (j : ZMod (2 ^ (s + 1))) ^ N = 1 := by
      have := (ZMod.natCast_eq_natCast_iff (j ^ N) 1 (2 ^ (s + 1))).mpr h
      simpa using this
    obtain ⟨u, hu'⟩ := IsUnit.of_pow_eq_one hu hN.pos.ne'
    have h1 : u ^ N = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hu', hu, Units.val_one]
    have h2 : u ^ Nat.totient (2 ^ (s + 1)) = 1 := ZMod.pow_totient u
    have h3 : Nat.Coprime N (Nat.totient (2 ^ (s + 1))) := by
      rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simpa using (Nat.Coprime.pow_right s (Nat.coprime_two_right.mpr hN))
    have h4 : u = 1 := (pow_eq_one_iff_of_coprime h3).mp ⟨h1, h2⟩
    have h5 : (j : ZMod (2 ^ (s + 1))) = ((1 : ℕ) : ZMod (2 ^ (s + 1))) := by
      rw [← hu', h4]
      simp
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h5

theorem t2C_oddAut_of_cyc2 {M : Type} [Group M] [Finite M] (hM : IsPGroup 2 M) (A : Subgroup M)
    (hAc : IsCyclic ↥A) (hAidx : A.index = 2) (hbig : ∀ x : M, x ∉ A → orderOf x < Nat.card ↥A)
    (θ : MulAut M) (hθ : Odd (orderOf θ)) : θ = 1 := by
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top A).mp hAc
  have hcard : Nat.card ↥A = orderOf g := by rw [← hg, Nat.card_zpowers]
  have hfin : IsOfFinOrder g := isOfFinOrder_of_finite g
  have hpow : ∀ a ∈ A, ∃ k : ℕ, g ^ k = a := by
    intro a ha
    rw [← hg] at ha
    exact (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr ha)
  have hθg : θ g ∈ A := by
    by_contra hnot
    have h1 := hbig _ hnot
    rw [hcard, MulEquiv.orderOf_eq] at h1
    exact lt_irrefl _ h1
  obtain ⟨j, hj⟩ := hpow _ hθg
  have hiter : ∀ k : ℕ, (θ ^ k) g = g ^ (j ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, ← hj, map_pow, ih, ← pow_mul, pow_succ]
  have hN : (θ ^ orderOf θ) = 1 := pow_orderOf_eq_one θ
  have hmod : j ^ orderOf θ ≡ 1 [MOD orderOf g] := by
    have : g ^ (j ^ orderOf θ) = g ^ 1 := by
      rw [← hiter, hN, pow_one]
      rfl
    exact pow_eq_pow_iff_modEq.mp this
  obtain ⟨s, hs⟩ : ∃ s : ℕ, orderOf g = 2 ^ s := by
    obtain ⟨k, hk⟩ := hM g
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨s, hs⟩
  have hj1 : j ≡ 1 [MOD orderOf g] := by
    rw [hs] at hmod ⊢
    exact t2OA_modEq_one_of_pow_odd hθ hmod
  have hθgg : θ g = g := by
    have : g ^ j = g ^ 1 := pow_eq_pow_iff_modEq.mpr hj1
    rw [← hj, this, pow_one]
  have hfixA : ∀ a ∈ A, θ a = a := by
    intro a ha
    obtain ⟨k, rfl⟩ := hpow a ha
    rw [map_pow, hθgg]
  have hnotA : ∀ x, x ∉ A → θ x ∉ A := by
    intro x hx hθx
    apply hx
    have h1 : θ x = x := θ.injective (hfixA _ hθx)
    rwa [h1] at hθx
  have hquot : ∀ x, x ∉ A → x⁻¹ * θ x ∈ A := by
    intro x hx
    rw [Subgroup.mul_mem_iff_of_index_two hAidx]
    simp [hx, hnotA x hx]
  ext x
  by_cases hx : x ∈ A
  · rw [hfixA x hx]
    rfl
  · have ha := hquot x hx
    have hit : ∀ k : ℕ, (θ ^ k) x = x * (x⁻¹ * θ x) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfixA _ ha, pow_succ',
          ← mul_assoc, mul_inv_cancel_left]
    have h1 : (x⁻¹ * θ x) ^ orderOf θ = 1 := by
      have := hit (orderOf θ)
      rw [hN] at this
      have h2 : x = x * (x⁻¹ * θ x) ^ orderOf θ := this
      exact mul_eq_left.mp h2.symm
    obtain ⟨k, hk⟩ := hM (x⁻¹ * θ x)
    have h2 : orderOf (x⁻¹ * θ x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf (x⁻¹ * θ x) ∣ orderOf θ := orderOf_dvd_of_pow_eq_one h1
    have h4 : Nat.Coprime (orderOf (x⁻¹ * θ x)) (orderOf θ) :=
      Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hθ))
    have h5 : orderOf (x⁻¹ * θ x) = 1 := Nat.Coprime.eq_one_of_dvd h4 h3
    have h6 : x⁻¹ * θ x = 1 := orderOf_eq_one_iff.mp h5
    have h7 : θ x = x := by
      have := congrArg (x * ·) h6
      simpa using this
    rw [h7]
    rfl

theorem t2OA_congr {M M' : Type} [Group M] [Group M'] (e : M ≃* M')
    (h : ∀ θ' : MulAut M', Odd (orderOf θ') → θ' = 1) (θ : MulAut M)
    (hθ : Odd (orderOf θ)) : θ = 1 := by
  have h1 : MulAut.congr e θ = 1 := h _ (by rwa [MulEquiv.orderOf_eq])
  exact (MulAut.congr e).injective (by rw [h1, map_one])

theorem t2OA_dihedralGroup {k m : ℕ} (hk : k = 2 ^ m) (hk4 : 4 ≤ k)
    (θ : MulAut (DihedralGroup k)) (hθ : Odd (orderOf θ)) : θ = 1 := by
  have : NeZero k := ⟨by omega⟩
  have hcardG : Nat.card (DihedralGroup k) = 2 ^ (m + 1) := by
    rw [DihedralGroup.nat_card, hk, pow_succ]
    ring
  have hP : IsPGroup 2 (DihedralGroup k) := IsPGroup.of_card hcardG
  have hAcard : Nat.card (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup k)) = k := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  refine t2C_oddAut_of_cyc2 hP (Subgroup.zpowers (DihedralGroup.r 1)) inferInstance ?_ ?_ θ hθ
  · have h := Subgroup.card_mul_index (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup k))
    rw [hAcard, DihedralGroup.nat_card] at h
    have hkpos : 0 < k := by omega
    exact Nat.eq_of_mul_eq_mul_left hkpos (by rw [h]; ring)
  · intro x hx
    rw [hAcard]
    rcases x with i | i
    · exfalso
      apply hx
      have : (DihedralGroup.r i : DihedralGroup k) = (DihedralGroup.r 1) ^ (i.val) := by
        rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    · rw [DihedralGroup.orderOf_sr]
      omega

theorem t2OA_semidihedralGroup {n : ℕ} (hn : 4 ≤ n)
    (θ : MulAut (CFSG.Open.SemidihedralGroup n)) (hθ : Odd (orderOf θ)) : θ = 1 := by
  have hn3 : 3 ≤ n := by omega
  have : Finite (CFSG.Open.SemidihedralGroup n) := CFSG.Semidihedral.presentation_finite n hn3
  refine t2C_oddAut_of_cyc2 (CFSG.Semidihedral.isTwoGroup n hn3)
    (CFSG.Semidihedral.rotationSubgroup n) (CFSG.Semidihedral.rotationSubgroup_cyclic n)
    (CFSG.Semidihedral.rotationSubgroup_index n hn3) ?_ θ hθ
  intro x hx
  rw [CFSG.Semidihedral.rotationSubgroup_natCard n hn3]
  obtain ⟨⟨i, e⟩, rfl⟩ := (CFSG.Semidihedral.coordinateEquiv n hn3).symm.surjective x
  change CFSG.Semidihedral.element n hn3 i e ∉ CFSG.Semidihedral.rotationSubgroup n at hx
  rw [CFSG.Semidihedral.element_mem_rotationSubgroup_iff n hn3] at hx
  change orderOf (CFSG.Semidihedral.element n hn3 i e) < CFSG.Semidihedral.modulus n
  rcases CFSG.Semidihedral.exponent_cases e with rfl | rfl
  · exact absurd rfl hx
  · have hmod : 8 ≤ CFSG.Semidihedral.modulus n := by
      unfold CFSG.Semidihedral.modulus
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h
    · rw [(CFSG.Semidihedral.outside_involution_iff n hn3 i).mpr h]
      omega
    · rw [(CFSG.Semidihedral.outside_order_four_iff n hn3 i).mpr h]
      omega

theorem t2C_oddAut_dihedral {M : Type} [Group M] {n : ℕ} (hn : 3 ≤ n)
    (h : CFSG.GH74.GLS.IVK.IsDihedralTwoGroup M n) (θ : MulAut M) (hθ : Odd (orderOf θ)) :
    θ = 1 := by
  obtain ⟨-, k, hk, -, ⟨e⟩⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hkm : k = 2 ^ m := by
    rw [pow_succ] at hk
    omega
  have hk4 : 4 ≤ k := by
    rw [hkm]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact t2OA_congr e (fun θ' hθ' => t2OA_dihedralGroup hkm hk4 θ' hθ') θ hθ

theorem t2C_oddAut_semidihedral {M : Type} [Group M] {n : ℕ}
    (h : CFSG.GH74.GLS.IVK.IsSemidihedralTwoGroup M n) (θ : MulAut M) (hθ : Odd (orderOf θ)) :
    θ = 1 := by
  obtain ⟨hn, ⟨e⟩⟩ := h
  exact t2OA_congr e (fun θ' hθ' => t2OA_semidihedralGroup hn θ' hθ') θ hθ

end CFSG.GH74.GLS.Stage4.Rest
