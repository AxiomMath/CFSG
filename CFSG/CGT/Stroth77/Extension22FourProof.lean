module

public import CFSG.CGT.Stroth77.Extension22Four
public import CFSG.CGT.Stroth77.Extension22Final

public section

namespace CFSG.CGT.Stroth77

open Matrix

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

def fourT (k : Fin 3 → ℕ) : AddSubgroup (Torus k) where
  carrier := {x | ∃ z : Torus k, 4 • z = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨zx, rfl⟩ ⟨zy, rfl⟩
    exact ⟨zx + zy, by rw [smul_add]⟩
  neg_mem' := by
    rintro x ⟨zx, rfl⟩
    exact ⟨-zx, by rw [smul_neg]⟩

theorem mem_fourT_iff {k : Fin 3 → ℕ} {x : Torus k} :
    x ∈ fourT k ↔ ∃ z : Torus k, 4 • z = x := Iff.rfl

theorem four_dvd_two_pow_succ {m : ℕ} (hm : 1 ≤ m) : (4 : ℤ) ∣ 2 ^ (m + 1) :=
  ⟨2 ^ (m - 1), by rw [two_pow_succ_eq_four hm]⟩

theorem dvd_four_of_eq_four_smul_coord {k : Fin 3 → ℕ} {a b c : ℤ} {z : Torus k} (j : Fin 3)
    (h : a • gen k 0 + b • gen k 1 + c • gen k 2 = 4 • z)
    (h4 : (4 : ℤ) ∣ 2 ^ k j) :
    (4 : ℤ) ∣ (if j = 0 then a else if j = 1 then b else c) := by
  have h' := congrFun h j
  have hleft : (a • gen k 0 + b • gen k 1 + c • gen k 2 : Torus k) j =
      (if j = 0 then a else if j = 1 then b else c : ℤ) := by
    fin_cases j <;> simp [gen, Pi.single_apply, zsmul_eq_mul]
  have hright : (4 • z : Torus k) j = 4 * (z j).val := by
    rw [Pi.smul_apply, nsmul_eq_mul]
    congr 1
    exact (ZMod.natCast_zmod_val (z j)).symm
  rw [hleft, hright] at h'
  have h'' : ((if j = 0 then a else if j = 1 then b else c : ℤ) : ZMod (2 ^ k j)) =
      ((4 * (z j).val : ℤ) : ZMod (2 ^ k j)) := by
    rw [h']
    push_cast
    ring
  have hdvd : ((2 : ℤ) ^ k j) ∣
      ((if j = 0 then a else if j = 1 then b else c) - 4 * (z j).val) := by
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h''
    have := dvd_neg.mpr h
    rwa [neg_sub] at this
  have h4' : (4 : ℤ) ∣ 4 * (z j).val := dvd_mul_right 4 _
  have h4'' : (4 : ℤ) ∣
      ((if j = 0 then a else if j = 1 then b else c) - 4 * (z j).val) :=
    dvd_trans h4 hdvd
  have heq : (if j = 0 then a else if j = 1 then b else c) =
      ((if j = 0 then a else if j = 1 then b else c) - 4 * (z j).val) + 4 * (z j).val := by
    ring
  rw [heq]
  exact dvd_add h4'' h4'

theorem type100_rho_apply_gens (m : ℕ) (a b c : ℤ) :
    (Type100.action m).φρ (a • gen (Type100.k m) 0 + b • gen (Type100.k m) 1 +
        c • gen (Type100.k m) 2) =
      (a - 2 * c) • gen (Type100.k m) 0 + (-c) • gen (Type100.k m) 1 +
        (b - c) • gen (Type100.k m) 2 := by
  rw [show (Type100.action m).φρ =
      matAct (Type100.k m) Type100.ρM (Type100.compat_rho m) from rfl, matAct_zsmul_gens]
  have hr00 : Type100.ρM 0 0 = 1 := by decide
  have hr01 : Type100.ρM 0 1 = 0 := by decide
  have hr02 : Type100.ρM 0 2 = -2 := by decide
  have hr10 : Type100.ρM 1 0 = 0 := by decide
  have hr11 : Type100.ρM 1 1 = 0 := by decide
  have hr12 : Type100.ρM 1 2 = -1 := by decide
  have hr20 : Type100.ρM 2 0 = 0 := by decide
  have hr21 : Type100.ρM 2 1 = 1 := by decide
  have hr22 : Type100.ρM 2 2 = -1 := by decide
  rw [hr00, hr01, hr02, hr10, hr11, hr12, hr20, hr21, hr22]
  simp only [zero_mul, one_mul, zero_add, add_zero]
  congr 1 <;> ring

theorem type100_t_apply_gens (m : ℕ) (a b c : ℤ) :
    (Type100.action m).φt (a • gen (Type100.k m) 0 + b • gen (Type100.k m) 1 +
        c • gen (Type100.k m) 2) =
      (a - 2 * c) • gen (Type100.k m) 0 +
        (2 * a - b - 2 * c) • gen (Type100.k m) 1 +
        (-c) • gen (Type100.k m) 2 := by
  rw [show (Type100.action m).φt =
      matAct (Type100.k m) Type100.tM (Type100.compat_t m) from rfl, matAct_zsmul_gens]
  have ht00 : Type100.tM 0 0 = 1 := by decide
  have ht01 : Type100.tM 0 1 = 0 := by decide
  have ht02 : Type100.tM 0 2 = -2 := by decide
  have ht10 : Type100.tM 1 0 = 2 := by decide
  have ht11 : Type100.tM 1 1 = -1 := by decide
  have ht12 : Type100.tM 1 2 = -2 := by decide
  have ht20 : Type100.tM 2 0 = 0 := by decide
  have ht21 : Type100.tM 2 1 = 0 := by decide
  have ht22 : Type100.tM 2 2 = -1 := by decide
  rw [ht00, ht01, ht02, ht10, ht11, ht12, ht20, ht21, ht22]
  simp only [zero_mul, one_mul, zero_add, add_zero]
  congr 1 <;> ring

theorem t100_fixed_rho_t_mod_four (m : ℕ) (hm : 1 ≤ m) {y : Torus (Type100.k m)}
    (hρ : (Type100.action m).φρ y - y ∈ fourT (Type100.k m))
    (ht : (Type100.action m).φt y - y ∈ fourT (Type100.k m)) :
    y ∈ fourT (Type100.k m) ∨ y - 2 • Torus.c ∈ fourT (Type100.k m) := by
  classical
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (Type100.k m) y
  obtain ⟨zρ, hzρ⟩ := mem_fourT_iff.mp hρ
  obtain ⟨zt, hzt⟩ := mem_fourT_iff.mp ht
  have hzρ' : (-2 * l) • gen (Type100.k m) 0 + (-l - j) • gen (Type100.k m) 1 +
      (j - 2 * l) • gen (Type100.k m) 2 = 4 • zρ := by
    rw [hzρ, hy, type100_rho_apply_gens]
    simp only [sub_eq_add_neg, neg_gens, gens_add]
    congr 1 <;> ring
  have hzt' : (-2 * l) • gen (Type100.k m) 0 + (2 * i - 2 * j - 2 * l) •
      gen (Type100.k m) 1 + (-2 * l) • gen (Type100.k m) 2 = 4 • zt := by
    rw [hzt, hy, type100_t_apply_gens]
    simp only [sub_eq_add_neg, neg_gens, gens_add]
    congr 1 <;> ring
  have h4m1 : (4 : ℤ) ∣ 2 ^ (Type100.k m) 1 := by
    rw [k100_one]; exact four_dvd_two_pow_succ hm
  have h4m2 : (4 : ℤ) ∣ 2 ^ (Type100.k m) 2 := by
    rw [k100_two]; exact four_dvd_two_pow_succ hm
  have hρ1 : (4 : ℤ) ∣ (-l - j) := by
    simpa using dvd_four_of_eq_four_smul_coord (k := Type100.k m) 1 hzρ' h4m1
  have hρ2 : (4 : ℤ) ∣ (j - 2 * l) := by
    simpa using dvd_four_of_eq_four_smul_coord (k := Type100.k m) 2 hzρ' h4m2
  have hj1 : (j : ZMod 4) = -(l : ZMod 4) := by
    have h : (((-l - j : ℤ)) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hρ1
    rw [Int.cast_sub, Int.cast_neg] at h
    have h' : (j : ZMod 4) + (l : ZMod 4) = 0 := by linear_combination -h
    linear_combination h'
  have hj2 : (j : ZMod 4) = 2 * (l : ZMod 4) := by
    have h : (((j - 2 * l : ℤ)) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hρ2
    rw [Int.cast_sub, Int.cast_mul] at h
    norm_num at h
    linear_combination h
  have hl3 : (3 : ZMod 4) * (l : ZMod 4) = 0 := by
    linear_combination hj1 - hj2
  have h3unit : IsUnit (3 : ZMod 4) := (ZMod.isUnit_iff_coprime 3 4).2 (by decide)
  have hl : (l : ZMod 4) = 0 := by
    have hl3' : (l : ZMod 4) * 3 = 0 := by rw [mul_comm]; exact hl3
    exact (h3unit.mul_left_eq_zero).mp hl3'
  have hj : (j : ZMod 4) = 0 := by rw [hj1, hl, neg_zero]
  have hdl : (4 : ℤ) ∣ l := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hl
  have hdj : (4 : ℤ) ∣ j := by
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
  have ht2 : (4 : ℤ) ∣ (2 * i - 2 * j - 2 * l) := by
    simpa using dvd_four_of_eq_four_smul_coord (k := Type100.k m) 1 hzt' h4m1
  have h2i : (4 : ℤ) ∣ 2 * i := by
    have h2j : (4 : ℤ) ∣ 2 * j := by
      obtain ⟨t, ht⟩ := hdj; exact ⟨2 * t, by rw [ht]; ring⟩
    have h2l : (4 : ℤ) ∣ 2 * l := by
      obtain ⟨t, ht⟩ := hdl; exact ⟨2 * t, by rw [ht]; ring⟩
    have heq : 2 * i = (2 * i - 2 * j - 2 * l) + 2 * j + 2 * l := by ring
    rw [heq]
    exact dvd_add (dvd_add ht2 h2j) h2l
  have h2dvd : (2 : ℤ) ∣ i := by
    obtain ⟨t, ht⟩ := h2i
    exact ⟨t, by linarith⟩
  obtain ⟨i', hi'⟩ := h2dvd
  obtain ⟨j', hj'⟩ := hdj
  obtain ⟨l', hl'⟩ := hdl
  rcases Int.even_or_odd i' with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    refine mem_fourT_iff.2 ⟨k • gen (Type100.k m) 0 + j' • gen (Type100.k m) 1 +
      l' • gen (Type100.k m) 2, ?_⟩
    rw [hy, hi', hj', hl', hk]
    module
  · right
    refine mem_fourT_iff.2 ⟨k • gen (Type100.k m) 0 + j' • gen (Type100.k m) 1 +
      l' • gen (Type100.k m) 2, ?_⟩
    rw [hy, hi', hj', hl', hk]
    module

theorem t100_fixed_rho_t_mod_four' (m : ℕ) (hm : 1 ≤ m) {y : Torus (StrothTypeIndex.t100 m).k}
    (hρ : (StrothTypeIndex.t100 m).action.φρ y - y ∈ fourT (StrothTypeIndex.t100 m).k)
    (ht : (StrothTypeIndex.t100 m).action.φt y - y ∈ fourT (StrothTypeIndex.t100 m).k) :
    y ∈ fourT (StrothTypeIndex.t100 m).k ∨
      y - 2 • Torus.c ∈ fourT (StrothTypeIndex.t100 m).k :=
  t100_fixed_rho_t_mod_four m hm hρ ht

variable {τ : StrothTypeIndex}

def fourB (D : StrothTypeData B τ) : Subgroup B where
  carrier := {x | D.ec x ∈ fourT τ.k}
  one_mem' := by simp [D.ec_one]
  mul_mem' := by
    intro x y hx hy
    change D.ec (x * y) ∈ fourT τ.k
    rw [D.ec_mul]
    exact (fourT τ.k).add_mem hx hy
  inv_mem' := by
    intro x hx
    change D.ec x⁻¹ ∈ fourT τ.k
    rw [D.ec_inv]
    exact (fourT τ.k).neg_mem hx

theorem mem_fourB_iff (D : StrothTypeData B τ) {x : B} :
    x ∈ fourB D ↔ ∃ z : Torus τ.k, 4 • z = D.ec x :=
  mem_fourT_iff

@[simp]
theorem ec_pow (D : StrothTypeData B τ) (x : B) (n : ℕ) :
    D.ec (x ^ n) = n • D.ec x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, D.ec_mul, ih, add_smul, one_smul]

theorem exists_pow_four_of_mem_fourB (D : StrothTypeData B τ) {y : B}
    (hy : y ∈ fourB D) : ∃ s : B, s ^ 4 = y := by
  obtain ⟨z, hz⟩ := (mem_fourB_iff D).mp hy
  refine ⟨Additive.toMul (D.e.symm z), ?_⟩
  apply D.ec_injective
  rw [ec_pow]
  have hs : D.ec (Additive.toMul (D.e.symm z)) = z := by
    show D.e (Additive.ofMul (Additive.toMul (D.e.symm z))) = z
    rw [show Additive.ofMul (Additive.toMul (D.e.symm z)) = D.e.symm z from rfl]
    exact D.e.apply_symm_apply z
  rw [hs]
  exact hz

theorem t100_fixed_rho_t_mod_four_of_mem {D : StrothTypeData B (StrothTypeIndex.t100 m)}
    (hm : 1 ≤ m) {y : B}
    (hρ : conjBy D.ρ_mem y * y⁻¹ ∈ fourB D)
    (ht : conjBy D.t_mem y * y⁻¹ ∈ fourB D) :
    y ∈ fourB D ∨ y * D.c ^ (-2 : ℤ) ∈ fourB D := by
  have hρ' : (StrothTypeIndex.t100 m).action.φρ (D.ec y) - D.ec y ∈
      fourT (StrothTypeIndex.t100 m).k := by
    rw [mem_fourT_iff, sub_eq_add_neg]
    have h := (mem_fourB_iff D).mp hρ
    rw [D.ec_mul, D.ec_inv, ec_conj_ρ] at h
    simpa [Φρ] using h
  have ht' : (StrothTypeIndex.t100 m).action.φt (D.ec y) - D.ec y ∈
      fourT (StrothTypeIndex.t100 m).k := by
    rw [mem_fourT_iff, sub_eq_add_neg]
    have h := (mem_fourB_iff D).mp ht
    rw [D.ec_mul, D.ec_inv, ec_conj_t] at h
    simpa [Φt] using h
  rcases t100_fixed_rho_t_mod_four' m hm hρ' ht' with h | h
  · exact Or.inl ((mem_fourB_iff D).mpr h)
  · right
    have hc : D.ec (y * D.c ^ (-2 : ℤ)) = D.ec y + -(2 • Torus.c) := by
      rw [D.ec_mul, D.ec_zpow, D.ec_c, neg_zsmul]
      norm_num
    rw [mem_fourB_iff, hc]
    rw [mem_fourT_iff] at h
    simpa [sub_eq_add_neg] using h

theorem subgroupOf_le_center (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) :
    B.subgroupOf C ≤ Subgroup.center C := by
  intro b hb
  rw [Subgroup.mem_center_iff]
  intro g
  have hbB : (b : S) ∈ B := Subgroup.mem_subgroupOf.mp hb
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hC g.2) (b : S) hbB).symm

theorem comm_of_le_centralizer_of_cyclic_quotient [hN : (B.subgroupOf C).Normal]
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hcyc : IsCyclic (C ⧸ B.subgroupOf C)) (x y : C) : x * y = y * x := by
  let H := B.subgroupOf C
  have hker : (QuotientGroup.mk' H).ker ≤ Subgroup.center C := by
    rw [QuotientGroup.ker_mk']
    exact subgroupOf_le_center hBC hC
  haveI : IsCyclic (C ⧸ H) := hcyc
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' H) hker x y

theorem card_quotient_four [hN : (B.subgroupOf C).Normal]
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) :
    Nat.card (C ⧸ B.subgroupOf C) = 4 := by
  rw [← Subgroup.index_eq_card, index_four_of_relIndex hBC hrel]

theorem cyclic_or_sq_eq_one {Q : Type*} [Group Q] [Finite Q] (hcard : Nat.card Q = 4) :
    IsCyclic Q ∨ ∀ x : Q, x * x = 1 := by
  by_cases hcyc : IsCyclic Q
  · exact Or.inl hcyc
  · right
    intro x
    by_contra hx
    have hx2 : x ^ 2 ≠ 1 := by simpa [pow_two] using hx
    have hx4 : x ^ 4 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hcard]
      exact orderOf_dvd_natCard x
    have hord4 : orderOf x ∣ 4 := (orderOf_dvd_iff_pow_eq_one).mpr hx4
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two (p := 2) (m := 2)).mp (by simpa using hord4)
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp at hk
        rw [hk] at hx2
        simp at hx2
      · exact hpos
    have hk2' : k = 1 ∨ k = 2 := by omega
    rcases hk2' with rfl | rfl
    · have hx2' : x ^ 2 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hk]
        norm_num
      exact hx2 hx2'
    · have hord : orderOf x = Nat.card Q := by rw [hk, hcard]; norm_num
      exact hcyc (isCyclic_of_orderOf_eq_card x hord)

noncomputable def conjOnSubgroup (g : S) (hg : g ∈ Subgroup.normalizer C) : C →* C where
  toFun x := ⟨g * (x : S) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : S)).mp x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mk, Subgroup.coe_mul]
    group

section QuotientAction

variable [hN : (B.subgroupOf C).Normal]

noncomputable def conjQuotientMap (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    (C ⧸ B.subgroupOf C) →* (C ⧸ B.subgroupOf C) :=
  QuotientGroup.map (B.subgroupOf C) (B.subgroupOf C) (conjOnSubgroup g hgC) (by
    intro x hx
    change g * (x : S) * g⁻¹ ∈ B
    exact (Subgroup.mem_normalizer_iff.mp hgB (x : S)).mp (Subgroup.mem_subgroupOf.mp hx))

@[simp]
theorem conjQuotientMap_mk (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjQuotientMap g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjOnSubgroup g hgC x) := by
  rw [conjQuotientMap]
  exact QuotientGroup.map_mk _ _ _ _ x

theorem conjQuotientMap_left_inv (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.LeftInverse
      (conjQuotientMap g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjQuotientMap g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotientMap_mk, conjQuotientMap_mk]
    congr 1
    ext
    simp only [conjOnSubgroup, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
    group

theorem conjQuotientMap_right_inv (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.RightInverse
      (conjQuotientMap g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjQuotientMap g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotientMap_mk, conjQuotientMap_mk]
    congr 1
    ext
    simp only [conjOnSubgroup, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
    group

noncomputable def conjAutQuotient (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) : MulAut (C ⧸ B.subgroupOf C) :=
  MulEquiv.ofBijective (conjQuotientMap g hgC hgB)
    ⟨(conjQuotientMap_left_inv g hgC hgB).injective,
     (conjQuotientMap_right_inv g hgC hgB).surjective⟩

@[simp]
theorem conjAutQuotient_apply_mk (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjAutQuotient g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjOnSubgroup g hgC x) := by
  show conjQuotientMap g hgC hgB (QuotientGroup.mk x) = _
  exact conjQuotientMap_mk g hgC hgB x

end QuotientAction

end CFSG.CGT.Stroth77
