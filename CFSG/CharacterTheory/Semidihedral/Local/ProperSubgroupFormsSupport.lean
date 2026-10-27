module

public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

section Dihedral

variable {H : Type*} [Group H] {h : ℕ} [NeZero h] {u x : H}

@[expose] def dihedralFormFun (u x : H) : DihedralGroup h → H
  | DihedralGroup.r i => u ^ i.val
  | DihedralGroup.sr i => x * u ^ i.val

theorem pow_val_add_of_pow_eq_one' (hu : u ^ h = 1) (i j : ZMod h) :
    u ^ (i + j).val = u ^ i.val * u ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hu, pow_add]

theorem pow_val_sub_of_pow_eq_one' (hu : u ^ h = 1) (i j : ZMod h) :
    u ^ (j - i).val = u ^ j.val * (u ^ i.val)⁻¹ := by
  have hneg : u ^ (-i).val = (u ^ i.val)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_val_add_of_pow_eq_one' hu, neg_add_cancel, ZMod.val_zero,
      pow_zero]
  rw [sub_eq_add_neg, pow_val_add_of_pow_eq_one' hu, hneg]

theorem dihedralFormFun_mul (hu : u ^ h = 1) (hx2 : x ^ 2 = 1) (hxu : x * u * x⁻¹ = u⁻¹)
    (g g' : DihedralGroup h) :
    dihedralFormFun u x (g * g') = dihedralFormFun u x g * dihedralFormFun u x g' := by
  have hxu' : x⁻¹ * u * x = u⁻¹ := by
    rw [← inv_inj, show (x⁻¹ * u * x)⁻¹ = x⁻¹ * u⁻¹ * x by group, inv_inv, ← hxu]
    group
  have hux : ∀ k : ℕ, u ^ k * x = x * (u ^ k)⁻¹ := fun k => by
    have hk : x⁻¹ * u ^ k * x = (u ^ k)⁻¹ := by
      have := conj_pow (a := x⁻¹) (b := u) (i := k)
      rw [inv_inv] at this
      rw [← this, hxu', inv_pow]
    calc u ^ k * x = x * (x⁻¹ * u ^ k * x) := by group
      _ = x * (u ^ k)⁻¹ := by rw [hk]
  have hcomm : ∀ p q : ℕ, (u ^ p)⁻¹ * u ^ q = u ^ q * (u ^ p)⁻¹ := fun p q =>
    ((Commute.pow_pow_self u p q).inv_left).eq
  rcases g with i | i <;> rcases g' with j | j
  · show u ^ (i + j).val = u ^ i.val * u ^ j.val
    exact pow_val_add_of_pow_eq_one' hu i j
  · show x * u ^ (j - i).val = u ^ i.val * (x * u ^ j.val)
    rw [pow_val_sub_of_pow_eq_one' hu, ← mul_assoc (u ^ i.val), hux, mul_assoc, hcomm]
  · show x * u ^ (i + j).val = x * u ^ i.val * u ^ j.val
    rw [pow_val_add_of_pow_eq_one' hu, mul_assoc]
  · show u ^ (j - i).val = x * u ^ i.val * (x * u ^ j.val)
    rw [pow_val_sub_of_pow_eq_one' hu]
    calc u ^ j.val * (u ^ i.val)⁻¹ = x ^ 2 * ((u ^ i.val)⁻¹ * u ^ j.val) := by
          rw [hx2, one_mul, hcomm]
      _ = x * (x * (u ^ i.val)⁻¹) * u ^ j.val := by rw [pow_two]; group
      _ = x * (u ^ i.val * x) * u ^ j.val := by rw [hux]
      _ = x * u ^ i.val * (x * u ^ j.val) := by group

@[expose] noncomputable def dihedralFormHom (hu : u ^ h = 1) (hx2 : x ^ 2 = 1)
    (hxu : x * u * x⁻¹ = u⁻¹) : DihedralGroup h →* H where
  toFun := dihedralFormFun u x
  map_one' := by
    show u ^ (0 : ZMod h).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := dihedralFormFun_mul hu hx2 hxu

theorem dihedral_normal_form (hgen : Subgroup.closure ({u, x} : Set H) = ⊤)
    (hu : orderOf u = h) (hx : x ∉ Subgroup.zpowers u) (hx2 : x ^ 2 = 1)
    (hxu : x * u * x⁻¹ = u⁻¹) :
    ∃ e : DihedralGroup h ≃* H, e (DihedralGroup.r 1) = u ∧ e (DihedralGroup.sr 0) = x := by
  have huh : u ^ h = 1 := by rw [← hu, pow_orderOf_eq_one]
  set φ := dihedralFormHom huh hx2 hxu with hφdef
  have hφr : ∀ i, φ (DihedralGroup.r i) = u ^ i.val := fun i => rfl
  have hφsr : ∀ i, φ (DihedralGroup.sr i) = x * u ^ i.val := fun i => rfl
  have hφ1 : φ (DihedralGroup.r 1) = u := by
    rw [hφr]
    by_cases h1 : h = 1
    · subst h1
      have : u = 1 := orderOf_eq_one_iff.mp hu
      rw [this, one_pow]
    · rw [ZMod.val_one'' h1, pow_one]
  have hφ0 : φ (DihedralGroup.sr 0) = x := by rw [hφsr, ZMod.val_zero, pow_zero, mul_one]
  have hpowinj : ∀ i j : ZMod h, u ^ i.val = u ^ j.val → i = j := by
    intro i j hij
    rw [pow_inj_mod, hu, Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)]
      at hij
    exact ZMod.val_injective _ hij
  have hmem : ∀ k : ℕ, u ^ k ∈ Subgroup.zpowers u := fun k =>
    Subgroup.pow_mem _ (Subgroup.mem_zpowers u) k
  have hinj : Function.Injective φ := by
    intro g g' hgg'
    rcases g with i | i <;> rcases g' with j | j
    · rw [hφr, hφr] at hgg'
      rw [hpowinj i j hgg']
    · rw [hφr, hφsr] at hgg'
      exfalso
      apply hx
      have : x = u ^ i.val * (u ^ j.val)⁻¹ := by rw [hgg']; group
      rw [this]
      exact Subgroup.mul_mem _ (hmem _) (Subgroup.inv_mem _ (hmem _))
    · rw [hφsr, hφr] at hgg'
      exfalso
      apply hx
      have : x = u ^ j.val * (u ^ i.val)⁻¹ := by rw [← hgg']; group
      rw [this]
      exact Subgroup.mul_mem _ (hmem _) (Subgroup.inv_mem _ (hmem _))
    · rw [hφsr, hφsr, mul_right_inj] at hgg'
      rw [hpowinj i j hgg']
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact ⟨DihedralGroup.r 1, hφ1⟩
    · exact ⟨DihedralGroup.sr 0, hφ0⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, hφ1, hφ0⟩

end Dihedral

section Coordinates

variable {S : Type*} [Group S] {n : ℕ}

theorem sd_orderOf_r (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    orderOf (f (r n)) = 2 ^ (n - 1) := by
  rw [equiv_orderOf, orderOf_r n (by omega), modulus]

theorem sd_conj_r (f : SemidihedralGroup n ≃* S) :
    f (s n) * f (r n) * (f (s n))⁻¹ = f (r n) ^ (2 ^ (n - 2) - 1) := by
  rw [← map_mul, ← map_inv, ← map_mul, s_conj_r, map_pow]

theorem sd_s_notMem (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    f (s n) ∉ Subgroup.zpowers (f (r n)) := by
  have h := image_element_mem_zpowers_r_iff (by omega : 3 ≤ n) f 0 1
  rw [element_eq, ZMod.val_zero, pow_zero, one_mul, ZMod.val_one, pow_one] at h
  rw [h]
  decide

theorem sd_index_two (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) :
    (Subgroup.zpowers (f (r n))).index = 2 := by
  rw [← map_rotationSubgroup n f, Subgroup.index_map_equiv]
  exact rotation_index n (by omega)

theorem sd_sq (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) (i : ℤ) :
    (f (r n) ^ i * f (s n)) ^ 2 = (f (r n) ^ (2 ^ (n - 1) / 2)) ^ i :=
  supplied_square_formula n hn f i

theorem sd_eq_of_notMem (hn : 4 ≤ n) (f : SemidihedralGroup n ≃* S) {g : S}
    (hg : g ∉ Subgroup.zpowers (f (r n))) : ∃ i < 2 ^ (n - 1), g = f (r n) ^ i * f (s n) := by
  obtain ⟨c, hc, -⟩ := (normal_form n hn).1 (f.symm g)
  have hg' : g = f (r n) ^ c.1.val * f (s n) ^ c.2.val := by
    rw [← map_pow, ← map_pow, ← map_mul, ← hc, MulEquiv.apply_symm_apply]
  have hc2 : c.2.val = 1 := by
    by_contra h
    have h0 : c.2.val = 0 := by omega
    apply hg
    rw [hg', h0, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  exact ⟨c.1.val, c.1.isLt, by rw [hg', hc2, pow_one]⟩

theorem sd_conj_rotation (f : SemidihedralGroup n ≃* S) (i : ℤ) (j : ℕ) :
    (f (r n) ^ i * f (s n)) * f (r n) ^ j * (f (r n) ^ i * f (s n))⁻¹ =
      f (r n) ^ ((2 ^ (n - 2) - 1) * j) := by
  set ρ := f (r n) with hρ
  set σ := f (s n) with hσ
  have h1 : σ * ρ ^ j * σ⁻¹ = ρ ^ ((2 ^ (n - 2) - 1) * j) := by
    rw [← conj_pow, hρ, hσ, sd_conj_r f, ← pow_mul]
  calc (ρ ^ i * σ) * ρ ^ j * (ρ ^ i * σ)⁻¹ = ρ ^ i * (σ * ρ ^ j * σ⁻¹) * (ρ ^ i)⁻¹ := by group
    _ = ρ ^ i * ρ ^ ((2 ^ (n - 2) - 1) * j) * (ρ ^ i)⁻¹ := by rw [h1]
    _ = ρ ^ ((2 ^ (n - 2) - 1) * j) := by
      rw [(((Commute.refl ρ).zpow_left i).pow_right ((2 ^ (n - 2) - 1) * j)).eq]
      group

end Coordinates

section CyclicTwo

variable {G : Type*} [Group G]

theorem eq_zpowers_of_le_zpowers {r : G} {B : Subgroup G} (hB : B ≤ Subgroup.zpowers r) :
    ∃ b ∈ B, B = Subgroup.zpowers b := by
  have : IsCyclic B := Subgroup.isCyclic_of_le hB
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := B)
  refine ⟨b, b.2, le_antisymm ?_ (Subgroup.zpowers_le.mpr b.2)⟩
  intro x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hb ⟨x, hx⟩)
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩

theorem eq_zpowers_two_pow_of_le {r : G} {N : ℕ} (hr : orderOf r = 2 ^ N) {B : Subgroup G}
    (hB : B ≤ Subgroup.zpowers r) : ∃ k ≤ N, B = Subgroup.zpowers (r ^ (2 ^ k)) := by
  obtain ⟨b, hbB, hBb⟩ := eq_zpowers_of_le_zpowers hB
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hB hbB)
  have hd : orderOf b ∣ 2 ^ N := by
    rw [← hr, ← hj]
    exact orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow])
  obtain ⟨c, hc, hdc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  refine ⟨N - c, by omega, ?_⟩
  rw [hBb]
  have hrk : orderOf (r ^ (2 ^ (N - c))) = 2 ^ c := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hr]; exact Nat.pow_dvd_pow 2 (by omega)), hr,
      Nat.pow_div (by omega) (by norm_num)]
    congr 1
    omega
  have : Finite (Subgroup.zpowers (r ^ 2 ^ (N - c))) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hrk]; positivity)
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    have h1 : b ^ (2 ^ c) = 1 := by rw [← hdc, pow_orderOf_eq_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul] at h1
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hr] at h2
    have h3 : ((2 : ℤ) ^ (N - c)) ∣ j := by
      have e : ((2 ^ N : ℕ) : ℤ) = (2 : ℤ) ^ (N - c) * 2 ^ c := by
        push_cast
        rw [← pow_add]
        congr 1
        omega
      rw [e] at h2
      push_cast at h2
      exact Int.dvd_of_mul_dvd_mul_right (by positivity) h2
    obtain ⟨t, ht⟩ := h3
    rw [← hj, ht, zpow_mul]
    have : r ^ ((2 : ℤ) ^ (N - c)) = r ^ (2 ^ (N - c)) := by
      rw [← zpow_natCast]
      push_cast
      rfl
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) t
  · rw [Nat.card_zpowers, Nat.card_zpowers, hdc, hrk]

end CyclicTwo

end CFSG.Semidihedral.Local
