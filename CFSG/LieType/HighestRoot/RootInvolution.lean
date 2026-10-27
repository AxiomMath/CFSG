module

public import CFSG.LieType.HighestRoot.GenBasic
public import CFSG.ClassicalInvolution.ModelFacts.WeylTransitive
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Conjugacy
public import CFSG.Timmesfeld.Defs
public import CFSG.Mathlib.GroupTheory.CardTwo
public import Mathlib

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.ModelFacts (IsIrreducible)
open CFSG.GroupTheory (eq_of_mem_of_card_eq_two eq_one_or_eq_of_mem_of_card_eq_two
  orderOf_eq_two_of_mem_of_card_eq_two)
open scoped commutatorElement

theorem odd_orderOf_mul_of_conj_eq {G : Type*} [Group G] {x y m : G} (hx : x * x = 1)
    (hy : y * y = 1) (hm : m ∈ Subgroup.closure ({x, y} : Set G)) (hmxy : m * x * m⁻¹ = y) :
    Odd (orderOf (x * y)) := by
  let t : G := x * y
  have hxy : x * t = y := by
    change x * (x * y) = y
    rw [← mul_assoc, hx, one_mul]
  have hxconj : x * t * x⁻¹ = t⁻¹ := by
    change x * (x * y) * x⁻¹ = (x * y)⁻¹
    rw [← mul_assoc x x y, hx, one_mul, mul_inv_rev,
      inv_eq_of_mul_eq_one_right hy, inv_eq_of_mul_eq_one_right hx]
  have hzx (i : ℤ) : t ^ i * x = x * t ^ (-i) := by
    have hconj : x * t ^ i * x⁻¹ = t ^ (-i) := by
      rw [← conj_zpow, hxconj, inv_zpow']
    have h2 : x * t ^ i = t ^ (-i) * x := by
      calc x * t ^ i = x * t ^ i * x⁻¹ * x := by group
        _ = t ^ (-i) * x := by rw [hconj]
    calc t ^ i * x = x * (x * t ^ i) * x := by rw [← mul_assoc x x (t ^ i), hx, one_mul]
      _ = x * (t ^ (-i) * x) * x := by rw [h2]
      _ = x * t ^ (-i) := by rw [← mul_assoc x (t ^ (-i)) x, mul_assoc, hx, mul_one]
  have hmul1 (i j : ℤ) : t ^ i * (x * t ^ j) = x * t ^ (j - i) := by
    calc t ^ i * (x * t ^ j) = (t ^ i * x) * t ^ j := by group
      _ = (x * t ^ (-i)) * t ^ j := by rw [hzx i]
      _ = x * t ^ (j - i) := by
        rw [mul_assoc, ← zpow_add, show -i + j = j - i by ring]
  have hmul2 (i j : ℤ) : (x * t ^ i) * t ^ j = x * t ^ (i + j) := by
    rw [mul_assoc, ← zpow_add]
  have hmul3 (i j : ℤ) : (x * t ^ i) * (x * t ^ j) = t ^ (j - i) := by
    calc (x * t ^ i) * (x * t ^ j) = x * t ^ i * x * t ^ j := by group
      _ = x * (t ^ i * x) * t ^ j := by group
      _ = x * (x * t ^ (-i)) * t ^ j := by rw [hzx i]
      _ = (x * x) * t ^ (-i) * t ^ j := by group
      _ = t ^ (j - i) := by
        rw [hx, one_mul, ← zpow_add, show -i + j = j - i by ring]
  let S : Subgroup G :=
    { carrier := {g | ∃ i : ℤ, g = t ^ i ∨ g = x * t ^ i}
      one_mem' := ⟨0, Or.inl (zpow_zero t).symm⟩
      mul_mem' := by
        rintro a b ⟨i, hi | hi⟩ ⟨j, hj | hj⟩
        · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
        · exact ⟨j - i, Or.inr (by rw [hi, hj, hmul1])⟩
        · exact ⟨i + j, Or.inr (by rw [hi, hj, hmul2])⟩
        · exact ⟨j - i, Or.inl (by rw [hi, hj, hmul3])⟩
      inv_mem' := by
        rintro a ⟨i, hi | hi⟩
        · exact ⟨-i, Or.inl (by rw [hi, ← zpow_neg])⟩
        · exact ⟨i, Or.inr (by
            rw [hi, mul_inv_rev, ← zpow_neg, inv_eq_of_mul_eq_one_right hx]
            simpa using hzx (-i))⟩ }
  have hxS : x ∈ S := ⟨0, Or.inr (by simp)⟩
  have hyS : y ∈ S := ⟨1, Or.inr (by rw [zpow_one]; exact hxy.symm)⟩
  have hcl : Subgroup.closure ({x, y} : Set G) ≤ S :=
    (Subgroup.closure_le S).2 (by
      rintro z (rfl | rfl)
      · exact hxS
      · exact hyS)
  have hodd_of_dvd {k : ℤ} (hk : t ^ k = 1) (hko : Odd k) : Odd (orderOf t) :=
    Odd.of_dvd_nat (Int.natAbs_odd.mpr hko)
      (Int.natCast_dvd.1 (orderOf_dvd_iff_zpow_eq_one.2 hk))
  obtain ⟨i, hi | hi⟩ := hcl hm
  · have h := hmxy
    rw [hi] at h
    have h1 : t ^ i * x * (t ^ i)⁻¹ = x * t ^ (-2 * i) := by
      calc t ^ i * x * (t ^ i)⁻¹ = t ^ i * x * t ^ (-i) := by rw [← zpow_neg]
        _ = (x * t ^ (-i)) * t ^ (-i) := by rw [hzx i]
        _ = x * t ^ (-i + -i) := by rw [mul_assoc, ← zpow_add]
        _ = x * t ^ (-2 * i) := by
          rw [show -i + -i = -2 * i by ring]
    have h2 : t ^ (-2 * i) = t :=
      mul_left_cancel (h1.symm.trans (h.trans hxy.symm))
    have hk : t ^ (-2 * i - 1) = 1 := by
      rw [show -2 * i - 1 = -2 * i + (-1) by ring, zpow_add, h2, zpow_neg_one,
        mul_inv_cancel]
    exact hodd_of_dvd hk (by rw [Int.odd_iff]; omega)
  · have h := hmxy
    rw [hi] at h
    have hinv : (x * t ^ i)⁻¹ = x * t ^ i := by
      rw [mul_inv_rev, ← zpow_neg, inv_eq_of_mul_eq_one_right hx]
      simpa using hzx (-i)
    have h1 : (x * t ^ i) * x * (x * t ^ i)⁻¹ = x * t ^ (2 * i) := by
      calc (x * t ^ i) * x * (x * t ^ i)⁻¹ = (x * t ^ i) * x * (x * t ^ i) := by
            rw [hinv]
        _ = x * (t ^ i * x) * (x * t ^ i) := by group
        _ = x * (x * t ^ (-i)) * (x * t ^ i) := by rw [hzx i]
        _ = (x * x) * t ^ (-i) * (x * t ^ i) := by group
        _ = t ^ (-i) * (x * t ^ i) := by rw [hx, one_mul]
        _ = x * t ^ (2 * i) := by
          rw [hmul1 (-i) i, show i - -i = 2 * i by ring]
    have h2 : t ^ (2 * i) = t :=
      mul_left_cancel (h1.symm.trans (h.trans hxy.symm))
    have hk : t ^ (2 * i - 1) = 1 := by
      rw [show 2 * i - 1 = 2 * i + (-1) by ring, zpow_add, h2, zpow_neg_one,
        mul_inv_cancel]
    exact hodd_of_dvd hk (by rw [Int.odd_iff]; omega)

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

private theorem rootForm_symm (x y : Fin D.rank → ℤ) :
    rootForm D x y = rootForm D y x :=
  form_comm D.isFiniteType _ _

private theorem rootForm_zsmul_add_zsmul (a b : ℤ) (x y z : Fin D.rank → ℤ) :
    rootForm D (a • x + b • y) z =
      (a : ℚ) * rootForm D x z + (b : ℚ) * rootForm D y z := by
  simp only [rootForm, map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [zsmul_eq_mul]

private theorem rootForm_add_self (x y : Fin D.rank → ℤ) :
    rootForm D (x + y) (x + y) =
      rootForm D x x + 2 * rootForm D x y + rootForm D y y := by
  simp only [rootForm, map_add, LinearMap.add_apply]
  rw [form_comm D.isFiniteType (toRat y) (toRat x)]
  ring

private theorem rootForm_sub_self (x y : Fin D.rank → ℤ) :
    rootForm D (x - y) (x - y) =
      rootForm D x x - 2 * rootForm D x y + rootForm D y y := by
  simp only [rootForm, map_sub, LinearMap.sub_apply]
  rw [form_comm D.isFiniteType (toRat y) (toRat x)]
  ring

private theorem rootForm_nsmul_add_self (a b : ℕ) (x y : Fin D.rank → ℤ) :
    rootForm D (a • x + b • y) (a • x + b • y) =
      (a : ℚ) ^ 2 * rootForm D x x + 2 * (a : ℚ) * (b : ℚ) * rootForm D x y +
        (b : ℚ) ^ 2 * rootForm D y y := by
  simp only [rootForm, map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [nsmul_eq_mul]
  rw [form_comm D.isFiniteType (toRat y) (toRat x)]
  ring

theorem odd_orderOf_mul_of_card_rootGroup_eq_two
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (hW : DivisibleWeylMem D n)
    {r : Fin D.rank → ℤ} (hr : r ∈ D.roots) (h2 : Nat.card (D.rootGroup r) = 2) {x y : K}
    (hx : x ∈ D.rootGroup r) (hx1 : x ≠ 1) (hy : y ∈ D.rootGroup (-r)) (hy1 : y ≠ 1) :
    Odd (orderOf (x * y)) := by
  obtain ⟨m, hm, s, hs, hsr⟩ := exists_mem_rankOneGroup_actsAs hct hW hr
  have hmap : (D.rootGroup r).map (MulAut.conj m).toMonoidHom = D.rootGroup (-r) := by
    have h := hs r hr
    rwa [hsr] at h
  have h2neg : Nat.card (D.rootGroup (-r)) = 2 := by
    rw [← hmap, Subgroup.card_map_of_injective (K := D.rootGroup r)
      (MulAut.conj m).injective, h2]
  have hXr : ∀ z ∈ D.rootGroup r, z = 1 ∨ z = x := fun z hz =>
    eq_one_or_eq_of_mem_of_card_eq_two h2 hx hx1 hz
  have hXnr : ∀ z ∈ D.rootGroup (-r), z = 1 ∨ z = y := fun z hz =>
    eq_one_or_eq_of_mem_of_card_eq_two h2neg hy hy1 hz
  have hmx : m * x * m⁻¹ ∈ D.rootGroup (-r) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (MulAut.conj m).toMonoidHom hx
  have hmx1 : m * x * m⁻¹ ≠ 1 := by
    intro h
    apply hx1
    apply (MulAut.conj m).injective
    simpa [MulAut.conj_apply] using h
  have hmxy : m * x * m⁻¹ = y := eq_of_mem_of_card_eq_two h2neg hmx hy hmx1 hy1
  have hx2 : x * x = 1 := by
    rw [← pow_two, ← orderOf_eq_two_of_mem_of_card_eq_two h2 hx hx1, pow_orderOf_eq_one]
  have hy2 : y * y = 1 := by
    rw [← pow_two, ← orderOf_eq_two_of_mem_of_card_eq_two h2neg hy hy1, pow_orderOf_eq_one]
  have hm_closure : m ∈ Subgroup.closure ({x, y} : Set K) := by
    have hle : D.rootGroup r ⊔ D.rootGroup (-r) ≤ Subgroup.closure ({x, y} : Set K) := by
      apply sup_le
      · intro z hz
        rcases hXr z hz with h | h
        · rw [h]; exact (Subgroup.closure ({x, y} : Set K)).one_mem
        · rw [h]; exact Subgroup.subset_closure (by simp)
      · intro z hz
        rcases hXnr z hz with h | h
        · rw [h]; exact (Subgroup.closure ({x, y} : Set K)).one_mem
        · rw [h]; exact Subgroup.subset_closure (by simp)
    exact hle hm
  exact odd_orderOf_mul_of_conj_eq hx2 hy2 hm_closure hmxy

theorem openCone_subset_of_rootForm_eq (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {r δ : Fin D.rank → ℤ} (hr : r ∈ D.roots)
    (hl : ∀ γ ∈ D.roots, rootForm D γ γ ≤ rootForm D r r) (hδ : δ ∈ D.roots)
    (hlen : rootForm D δ δ = rootForm D r r) (hne : δ ≠ r) (hne' : δ ≠ -r) :
    LinIndepPair r δ ∧ (∀ ε ∈ openCone D.roots r δ, ε = r + δ) ∧
      (r + δ ∈ D.roots → ∃ w : W, ρ w r = r + δ) := by
  have hδ' : δ ∈ roots D.isFiniteType ∅ := by
    simpa only [UniversalRootDatum.roots, hdiv] using hδ
  have hLpos : 0 < rootForm D r r :=
    CFSG.ClassicalInvolution.ModelFacts.lenSq_pos D.isFiniteType
      (ne_zero_of_mem_roots D.isFiniteType D.divisible hr)
  obtain ⟨s, hs⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_reflection D.isFiniteType hδ'
  obtain ⟨m, hm, -⟩ := hs r
  have hmL : (m : ℚ) * rootForm D r r = 2 * rootForm D δ r := by
    have hm' : (m : ℚ) * rootForm D δ δ = 2 * rootForm D δ r := hm
    rw [hlen] at hm'
    exact hm'
  have hsub : rootForm D (r - δ) (r - δ) =
      (2 - (m : ℚ)) * rootForm D r r := by
    rw [rootForm_sub_self, rootForm_symm r δ, hlen]
    linear_combination (1 : ℚ) * hmL
  have hadd : rootForm D (r + δ) (r + δ) =
      (2 + (m : ℚ)) * rootForm D r r := by
    rw [rootForm_add_self, rootForm_symm r δ, hlen]
    linear_combination (-1 : ℚ) * hmL
  have hmle : m ≤ 1 := by
    by_contra h
    push Not at h
    have hm2 : (2 : ℤ) ≤ m := by omega
    have hm2q : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm2
    have hle : rootForm D (r - δ) (r - δ) ≤ 0 := by
      rw [hsub]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le
    have hne0 : r - δ ≠ 0 := sub_ne_zero.2 fun h' => hne h'.symm
    have hpos : 0 < rootForm D (r - δ) (r - δ) :=
      CFSG.ClassicalInvolution.ModelFacts.lenSq_pos D.isFiniteType hne0
    linarith
  have hmge : -1 ≤ m := by
    by_contra h
    push Not at h
    have hm2 : m ≤ -2 := by omega
    have hm2q : (m : ℚ) ≤ -2 := by exact_mod_cast hm2
    have hle : rootForm D (r + δ) (r + δ) ≤ 0 := by
      rw [hadd]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hLpos.le
    have hne0 : r + δ ≠ 0 := by
      intro h0
      exact hne' (by linear_combination h0)
    have hpos : 0 < rootForm D (r + δ) (r + δ) :=
      CFSG.ClassicalInvolution.ModelFacts.lenSq_pos D.isFiniteType hne0
    linarith
  have hm_cases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  have hLin : LinIndepPair r δ := by
    intro a b hab
    have h1 : (a : ℚ) * rootForm D r r + (b : ℚ) * rootForm D δ r = 0 := by
      have h := congrArg (fun v => rootForm D v r) hab
      rw [rootForm_zsmul_add_zsmul] at h
      have h0 : rootForm D (0 : Fin D.rank → ℤ) r = 0 := by simp [rootForm]
      rwa [h0] at h
    have h2 : (a : ℚ) * rootForm D δ r + (b : ℚ) * rootForm D r r = 0 := by
      have h := congrArg (fun v => rootForm D v δ) hab
      rw [rootForm_zsmul_add_zsmul, rootForm_symm r δ, hlen] at h
      have h0 : rootForm D (0 : Fin D.rank → ℤ) δ = 0 := by simp [rootForm]
      rwa [h0] at h
    have hb : b = 0 := by
      have hbq : (b : ℚ) = 0 := by
        rcases hm_cases with hm | hm | hm
        · subst hm
          norm_num at hmL
          have hX : rootForm D δ r = -(rootForm D r r / 2) := by linarith [hmL]
          rw [hX] at h1 h2
          ring_nf at h1 h2
          have hbL : (b : ℚ) * rootForm D r r = 0 := by linarith
          exact (mul_eq_zero.1 hbL).resolve_right hLpos.ne'
        · subst hm
          norm_num at hmL
          have hX : rootForm D δ r = 0 := by linarith [hmL]
          rw [hX] at h2
          simp only [mul_zero, zero_add] at h2
          exact (mul_eq_zero.1 h2).resolve_right hLpos.ne'
        · subst hm
          norm_num at hmL
          have hX : rootForm D δ r = rootForm D r r / 2 := by linarith [hmL]
          rw [hX] at h1 h2
          ring_nf at h1 h2
          have hbL : (b : ℚ) * rootForm D r r = 0 := by linarith
          exact (mul_eq_zero.1 hbL).resolve_right hLpos.ne'
      exact_mod_cast hbq
    have haL : (a : ℚ) * rootForm D r r = 0 := by
      rw [hb] at h1
      simpa only [Int.cast_zero, zero_mul, add_zero] using h1
    have haq : (a : ℚ) = 0 := (mul_eq_zero.1 haL).resolve_right hLpos.ne'
    exact ⟨by exact_mod_cast haq, hb⟩
  have hcone : ∀ ε ∈ openCone D.roots r δ, ε = r + δ := by
    intro ε hε
    obtain ⟨hεR, a, b, ha, hb, rfl⟩ := hε
    have hεsq : rootForm D (a • r + b • δ) (a • r + b • δ) =
        ((a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) * (m : ℚ) + (b : ℚ) ^ 2) *
          rootForm D r r := by
      rw [rootForm_nsmul_add_self, rootForm_symm r δ, hlen]
      linear_combination (-((a : ℚ) * (b : ℚ))) * hmL
    have hcoef :
        (a : ℚ) ^ 2 + (a : ℚ) * (b : ℚ) * (m : ℚ) + (b : ℚ) ^ 2 ≤ 1 := by
      have h := hl _ hεR
      rw [hεsq] at h
      nlinarith [hLpos, h]
    rcases hm_cases with hm | hm | hm
    · subst hm
      norm_num at hcoef
      have haq : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
      have hbq : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
      have h1 : ((a : ℚ) - (b : ℚ)) ^ 2 + (a : ℚ) * (b : ℚ) ≤ 1 := by nlinarith
      have hab : 1 ≤ (a : ℚ) * (b : ℚ) := by nlinarith
      have hd : ((a : ℚ) - (b : ℚ)) ^ 2 = 0 := by nlinarith
      have heq : (a : ℚ) = (b : ℚ) := by nlinarith
      have ha1le : (a : ℚ) ≤ 1 := by
        nlinarith [sq_nonneg ((a : ℚ) - 1)]
      have ha1 : (a : ℚ) = 1 := le_antisymm ha1le haq
      have hb1 : (b : ℚ) = 1 := by
        rw [← heq]
        exact ha1
      have ha1' : a = 1 := by exact_mod_cast ha1
      have hb1' : b = 1 := by exact_mod_cast hb1
      subst ha1'
      subst hb1'
      simp
    · subst hm
      norm_num at hcoef
      have haq : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
      have hbq : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
      exfalso
      nlinarith
    · subst hm
      norm_num at hcoef
      have haq : (1 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
      have hbq : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
      exfalso
      nlinarith
  have hsum : r + δ ∈ D.roots → ∃ w : W, ρ w r = r + δ := by
    intro hrd
    have hrdle : rootForm D (r + δ) (r + δ) ≤ rootForm D r r := hl _ hrd
    have hm_le : (m : ℚ) ≤ -1 := by
      have h2 : (2 : ℚ) + (m : ℚ) ≤ 1 := by nlinarith [hLpos, hadd ▸ hrdle]
      linarith
    have hm_eq : m = -1 := by
      have : m ≤ -1 := by exact_mod_cast hm_le
      omega
    have hlenr : rootForm D r r = rootForm D (r + δ) (r + δ) := by
      rw [hadd, hm_eq]
      norm_num
    have hr' : r ∈ roots D.isFiniteType ∅ := by
      simpa only [UniversalRootDatum.roots, hdiv] using hr
    have hrd' : r + δ ∈ roots D.isFiniteType ∅ := by
      simpa only [UniversalRootDatum.roots, hdiv] using hrd
    obtain ⟨w, hw⟩ :=
      CFSG.ClassicalInvolution.ModelFacts.exists_weylAction_eq_of_lenSq_eq
        D.isFiniteType hirr hr' hrd' hlenr
    exact ⟨w, hw⟩
  exact ⟨hLin, hcone, hsum⟩

theorem isHighestRoot_of_forall_ht_le (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {γ₀ : Fin D.rank → ℤ} (hγ₀ : γ₀ ∈ D.roots) (hmax : ∀ δ ∈ D.roots, ht δ ≤ ht γ₀) :
    IsHighestRoot D γ₀ := by
  have hrank : 0 < D.rank := by
    rcases (show γ₀ ∈ roots D.isFiniteType D.divisible from hγ₀) with
      ⟨w, i, -⟩ | ⟨w, i, hi, -⟩
    · exact Fin.pos i
    · rw [hdiv] at hi
      exact absurd hi (Set.notMem_empty i)
  obtain ⟨r₀, hr₀⟩ := exists_isHighestRoot D hirr hdiv hrank
  have hht_eq : ht γ₀ = ht r₀ :=
    le_antisymm (hr₀.height_le γ₀ hγ₀) (hmax r₀ hr₀.mem_roots)
  have hγ₀_nonneg : 0 ≤ γ₀ := by
    rcases nonneg_or_nonpos D.isFiniteType D.divisible hγ₀ with h | h
    · exact h
    · exfalso
      have hle0 : ht γ₀ ≤ 0 := by
        simp only [ht]
        exact Finset.sum_nonpos fun j _ => h j
      have hpos : 0 < ht γ₀ := by
        rw [hht_eq]
        exact hr₀.ht_pos
      linarith
  obtain ⟨w, i, hrw⟩ : ∃ (w : W) (i : Fin D.rank),
      r₀ = ρ w (Pi.single i 1) := by
    rcases (show r₀ ∈ roots D.isFiniteType D.divisible from hr₀.mem_roots) with
      ⟨w, i, h⟩ | ⟨w, i, hi, h⟩
    · exact ⟨w, i, h⟩
    · rw [hdiv] at hi
      exact absurd hi (Set.notMem_empty i)
  have hle : γ₀ ≤ r₀ :=
    le_of_nonneg D.isFiniteType hirr hrw hr₀.longest hr₀.dominant hγ₀ hγ₀_nonneg
  have hsum_eq : ∑ j, γ₀ j = ∑ j, r₀ j := by
    simpa only [ht] using hht_eq
  have heq : γ₀ = r₀ := by
    funext j
    exact (Finset.sum_eq_sum_iff_of_le fun j _ => hle j).1 hsum_eq j (Finset.mem_univ j)
  rw [heq]
  exact hr₀

private theorem rootInvolution_conj {G : Type*} [Group G] {x₀ a c : G}
    (h : (orderOf a = 2 ∨ orderOf a = 4 ∨ Odd (orderOf a)) ∧
      (orderOf a = 4 → IsConj x₀ (a ^ 2))) :
    (orderOf (c * a * c⁻¹) = 2 ∨ orderOf (c * a * c⁻¹) = 4 ∨
        Odd (orderOf (c * a * c⁻¹))) ∧
      (orderOf (c * a * c⁻¹) = 4 → IsConj x₀ ((c * a * c⁻¹) ^ 2)) := by
  have hord : orderOf (c * a * c⁻¹) = orderOf a :=
    (IsConj.orderOf_eq (isConj_iff.2 ⟨c, rfl⟩)).symm
  refine ⟨?_, ?_⟩
  · rw [hord]
    exact h.1
  · intro h4
    have h4a : orderOf a = 4 := by rwa [hord] at h4
    have hsq := h.2 h4a
    have hsqeq : (c * a * c⁻¹) ^ 2 = c * a ^ 2 * c⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [hsqeq]
    exact hsq.trans (isConj_iff.2 ⟨c, rfl⟩)

theorem mem_borel_conj_eq (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hN : DivisibleNormalizes D) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) (h2 : Nat.card (D.rootGroup r) = 2) {x₀ : K}
    (hx₀ : x₀ ∈ D.rootGroup r) {b : K} (hb : b ∈ borel D H) : b * x₀ * b⁻¹ = x₀ := by
  by_cases hx1 : x₀ = 1
  · simp [hx1]
  have hmem : b * x₀ * b⁻¹ ∈ D.rootGroup r :=
    (Subgroup.mem_normalizer_iff.1 (borel_le_normalizer_rootGroup hct hext hN hr hb) x₀).1 hx₀
  have hmem1 : b * x₀ * b⁻¹ ≠ 1 := by
    intro hv
    apply hx1
    calc x₀ = b⁻¹ * (b * x₀ * b⁻¹) * b := by group
      _ = 1 := by rw [hv, mul_one, inv_mul_cancel]
  exact eq_of_mem_of_card_eq_two h2 hmem hx₀ hmem1 hx1

theorem exists_mem_borel_conj_eq (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hN : DivisibleNormalizes D) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) (h2 : Nat.card (D.rootGroup r) = 2) {x₀ : K}
    (hx₀ : x₀ ∈ D.rootGroup r) (g : K) :
    ∃ b ∈ borel D H, ∃ w : W,
      g * x₀ * g⁻¹ = b * (nrep hct w * x₀ * (nrep hct w)⁻¹) * b⁻¹ := by
  obtain ⟨w, hw⟩ := exists_mem_bruhatCell hct hext g
  obtain ⟨b, hb, u, hu, hgu⟩ := exists_eq_mul_nrep_mul hct hext hw
  refine ⟨b, hb, w, ?_⟩
  have huB : u ∈ borel D H := posUnipotent_le_borel (inversionUnipotent_le_posUnipotent w hu)
  have hux : u * x₀ * u⁻¹ = x₀ := mem_borel_conj_eq hct hext hN hr h2 hx₀ huB
  rw [hgu]
  calc b * nrep hct w * u * x₀ * (b * nrep hct w * u)⁻¹ =
      b * nrep hct w * (u * x₀ * u⁻¹) * (nrep hct w)⁻¹ * b⁻¹ := by group
    _ = b * (nrep hct w * x₀ * (nrep hct w)⁻¹) * b⁻¹ := by rw [hux]; group


private theorem key_weyl (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) (h2 : Nat.card (D.rootGroup r) = 2)
    {x₀ : K} (hx₀ : x₀ ∈ D.rootGroup r) (hx₀1 : x₀ ≠ 1) (w : W) :
    (orderOf (x₀ * (nrep hct w * x₀ * (nrep hct w)⁻¹)) = 2 ∨
        orderOf (x₀ * (nrep hct w * x₀ * (nrep hct w)⁻¹)) = 4 ∨
        Odd (orderOf (x₀ * (nrep hct w * x₀ * (nrep hct w)⁻¹)))) ∧
      (orderOf (x₀ * (nrep hct w * x₀ * (nrep hct w)⁻¹)) = 4 →
        IsConj x₀ ((x₀ * (nrep hct w * x₀ * (nrep hct w)⁻¹)) ^ 2)) := by
  set δ : Fin D.rank → ℤ := ρ w r with hδdef
  set z : K := nrep hct w * x₀ * (nrep hct w)⁻¹ with hzdef
  have hδmem : δ ∈ D.roots := weylAction_mem_roots D.isFiniteType w hr.mem_roots
  have hδlen : rootForm D δ δ = rootForm D r r := by
    rw [hδdef]
    exact rootForm_weylAction w r r
  have hzmem : z ∈ D.rootGroup δ := by
    rw [hδdef, hzdef]
    exact (actsAs_nrep hct w).conj_mem hr.mem_roots hx₀
  have hxord : orderOf x₀ = 2 := orderOf_eq_two_of_mem_of_card_eq_two h2 hx₀ hx₀1
  have hx2 : x₀ * x₀ = 1 := by
    have h := pow_orderOf_eq_one x₀
    rwa [hxord, pow_two] at h
  have hzo : orderOf z = 2 := by
    have hconj : IsConj x₀ z := by
      rw [hzdef]
      exact isConj_iff.2 ⟨nrep hct w, rfl⟩
    rw [(IsConj.orderOf_eq hconj).symm]
    exact hxord
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    omega
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hzo, pow_two] at h
  have hδcard : Nat.card (D.rootGroup δ) = 2 := by
    have hmap : Subgroup.map (MulAut.conj (nrep hct w)).toMonoidHom (D.rootGroup r) =
        D.rootGroup δ := by
      rw [hδdef]
      exact (actsAs_nrep hct w) r hr.mem_roots
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj (nrep hct w)).injective, h2]
  by_cases hδr : δ = r
  · have hzx : z = x₀ := eq_of_mem_of_card_eq_two h2 (hδr ▸ hzmem) hx₀ hz1 hx₀1
    have h1 : x₀ * z = 1 := by rw [hzx, hx2]
    refine ⟨Or.inr (Or.inr ?_), ?_⟩
    · rw [h1, orderOf_one]
      norm_num
    · intro h4
      rw [h1, orderOf_one] at h4
      omega
  by_cases hδnr : δ = -r
  · have hzmem' : z ∈ D.rootGroup (-r) := hδnr ▸ hzmem
    have hodd : Odd (orderOf (x₀ * z)) :=
      odd_orderOf_mul_of_card_rootGroup_eq_two hct
        (divisibleWeylMem_of_divisible_eq_empty hdiv) hr.mem_roots h2 hx₀ hx₀1 hzmem' hz1
    refine ⟨Or.inr (Or.inr hodd), ?_⟩
    intro h4
    rw [h4] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  · obtain ⟨hlin, hcone, hroot⟩ :=
      openCone_subset_of_rootForm_eq hirr hdiv hr.mem_roots hr.longest hδmem hδlen hδr hδnr
    have hxinv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hx2
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hcomm := hext.commutator_mem r hr.mem_roots δ hδmem hlin x₀ hx₀ z hzmem
    have hcomm_eq : ⁅x₀, z⁆ = (x₀ * z) ^ 2 := by
      rw [commutatorElement_def, hxinv, hzinv, pow_two]
      group
    by_cases hrs : r + δ ∈ D.roots
    · obtain ⟨w', hw'⟩ := hroot hrs
      have hle : (⨆ ε ∈ openCone D.roots r δ, D.rootGroup ε) ≤ D.rootGroup (r + δ) := by
        refine iSup₂_le fun ε hε => ?_
        rw [hcone ε hε]
      have hsqmem : (x₀ * z) ^ 2 ∈ D.rootGroup (r + δ) := by
        rw [← hcomm_eq]
        exact hle hcomm
      set x' : K := nrep hct w' * x₀ * (nrep hct w')⁻¹ with hx'def
      have hx'mem : x' ∈ D.rootGroup (r + δ) := by
        rw [hx'def]
        have h := (actsAs_nrep hct w').conj_mem hr.mem_roots hx₀
        rwa [hw'] at h
      have hx'card : Nat.card (D.rootGroup (r + δ)) = 2 := by
        have hmap : Subgroup.map (MulAut.conj (nrep hct w')).toMonoidHom (D.rootGroup r) =
            D.rootGroup (r + δ) := by
          have h := (actsAs_nrep hct w') r hr.mem_roots
          rwa [hw'] at h
        rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj (nrep hct w')).injective, h2]
      have hx'ord : orderOf x' = 2 := by
        have hconj : IsConj x₀ x' := by
          rw [hx'def]
          exact isConj_iff.2 ⟨nrep hct w', rfl⟩
        rw [(IsConj.orderOf_eq hconj).symm]
        exact hxord
      have hx'1 : x' ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hx'ord
        omega
      have hx'2 : x' * x' = 1 := by
        have h := pow_orderOf_eq_one x'
        rwa [hx'ord, pow_two] at h
      have hsq : (x₀ * z) ^ 2 = 1 ∨ (x₀ * z) ^ 2 = x' :=
        eq_one_or_eq_of_mem_of_card_eq_two hx'card hx'mem hx'1 hsqmem
      have h4 : (x₀ * z) ^ 4 = 1 := by
        have hsquare : ((x₀ * z) ^ 2) ^ 2 = 1 := by
          rcases hsq with h | h
          · rw [h, one_pow]
          · rw [h, pow_two]
            exact hx'2
        calc (x₀ * z) ^ 4 = ((x₀ * z) ^ 2) ^ 2 := by
              rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
          _ = 1 := hsquare
      have hdvd : orderOf (x₀ * z) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      refine ⟨?_, ?_⟩
      · have hdvd' : orderOf (x₀ * z) ∣ 2 ^ 2 := by simpa using hdvd
        obtain ⟨k, hk4, hk⟩ := (Nat.dvd_prime_pow (m := 2) Nat.prime_two).1 hdvd'
        interval_cases k
        · right
          right
          rw [hk]
          norm_num
        · left
          rw [hk]
          norm_num
        · right
          left
          rw [hk]
          norm_num
      · intro h4ord
        have hsqne : (x₀ * z) ^ 2 ≠ 1 := by
          intro hs
          have hdvd2 : orderOf (x₀ * z) ∣ 2 := orderOf_dvd_of_pow_eq_one hs
          rw [h4ord] at hdvd2
          exact absurd hdvd2 (by norm_num)
        have hsqx' : (x₀ * z) ^ 2 = x' := by
          rcases hsq with h | h
          · exact absurd h hsqne
          · exact h
        rw [hsqx']
        exact isConj_iff.2 ⟨nrep hct w', hx'def.symm⟩
    · have hbot : (⨆ ε ∈ openCone D.roots r δ, D.rootGroup ε) = ⊥ := by
        refine iSup₂_eq_bot.2 fun ε hε => ?_
        exfalso
        exact hrs ((hcone ε hε) ▸ hε.1)
      have hcomm1 : ⁅x₀, z⁆ = 1 := by
        rw [hbot] at hcomm
        exact Subgroup.mem_bot.1 hcomm
      have hsq1 : (x₀ * z) ^ 2 = 1 := by
        rw [← hcomm_eq, hcomm1]
      have hdvd : orderOf (x₀ * z) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq1
      refine ⟨?_, ?_⟩
      · rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
        · right
          right
          rw [h1]
          norm_num
        · left
          exact h2
      · intro h4
        rw [h4] at hdvd
        exact absurd hdvd (by norm_num)

private theorem key_borel (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hN : DivisibleNormalizes D) (hirr : IsIrreducible D.cartan)
    (hdiv : D.divisible = ∅) {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r)
    (h2 : Nat.card (D.rootGroup r) = 2) {x₀ : K} (hx₀ : x₀ ∈ D.rootGroup r)
    (hx₀1 : x₀ ≠ 1) (k : K) :
    (orderOf (x₀ * (k * x₀ * k⁻¹)) = 2 ∨ orderOf (x₀ * (k * x₀ * k⁻¹)) = 4 ∨
        Odd (orderOf (x₀ * (k * x₀ * k⁻¹)))) ∧
      (orderOf (x₀ * (k * x₀ * k⁻¹)) = 4 →
        IsConj x₀ ((x₀ * (k * x₀ * k⁻¹)) ^ 2)) := by
  obtain ⟨b, hb, w, hkw⟩ := exists_mem_borel_conj_eq hct hext hN hr h2 hx₀ k
  set z : K := nrep hct w * x₀ * (nrep hct w)⁻¹ with hzdef
  have hb' : b⁻¹ ∈ borel D H := inv_mem hb
  have hbx : b⁻¹ * x₀ * b = x₀ := by
    simpa using mem_borel_conj_eq hct hext hN hr h2 hx₀ hb'
  have hconj : x₀ * (k * x₀ * k⁻¹) = b * (x₀ * z) * b⁻¹ := by
    rw [hkw]
    calc x₀ * (b * z * b⁻¹) = b * (b⁻¹ * x₀ * b) * z * b⁻¹ := by group
      _ = b * (x₀ * z) * b⁻¹ := by rw [hbx]; group
  have hprop := rootInvolution_conj (x₀ := x₀) (a := x₀ * z) (c := b)
    (key_weyl hct hext hirr hdiv hr h2 hx₀ hx₀1 w)
  constructor
  · rw [hconj]
    exact hprop.1
  · intro h4
    rw [hconj] at h4
    rw [hconj]
    exact hprop.2 h4

theorem isRootInvolutionSet_conj_rootGroup (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) (h2 : Nat.card (D.rootGroup r) = 2)
    {x₀ : K} (hx₀ : x₀ ∈ D.rootGroup r) (hx₀1 : x₀ ≠ 1) :
    CFSG.Timmesfeld.IsRootInvolutionSet {g : K | IsConj x₀ g} := by
  have hxord : orderOf x₀ = 2 := orderOf_eq_two_of_mem_of_card_eq_two h2 hx₀ hx₀1
  have hN : DivisibleNormalizes D := divisibleNormalizes_of_divisible_eq_empty hdiv
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    exact (IsConj.orderOf_eq hd).symm.trans hxord
  · intro d hd e he
    obtain ⟨g, hg⟩ := isConj_iff.1 hd
    obtain ⟨h, hh⟩ := isConj_iff.1 he
    let k : K := g⁻¹ * h
    have hprod : d * e = g * (x₀ * (k * x₀ * k⁻¹)) * g⁻¹ := by
      rw [← hg, ← hh]
      dsimp [k]
      group
    rw [hprod]
    exact (rootInvolution_conj (x₀ := x₀) (a := x₀ * (k * x₀ * k⁻¹)) (c := g)
      (key_borel hct hext hN hirr hdiv hr h2 hx₀ hx₀1 k)).1
  · intro d hd e he h4
    obtain ⟨g, hg⟩ := isConj_iff.1 hd
    obtain ⟨h, hh⟩ := isConj_iff.1 he
    let k : K := g⁻¹ * h
    have hprod : d * e = g * (x₀ * (k * x₀ * k⁻¹)) * g⁻¹ := by
      rw [← hg, ← hh]
      dsimp [k]
      group
    have h4' : orderOf (g * (x₀ * (k * x₀ * k⁻¹)) * g⁻¹) = 4 := by
      rwa [← hprod]
    have hprop := (rootInvolution_conj (x₀ := x₀) (a := x₀ * (k * x₀ * k⁻¹)) (c := g)
      (key_borel hct hext hN hirr hdiv hr h2 hx₀ hx₀1 k)).2 h4'
    change IsConj x₀ ((d * e) ^ 2)
    rw [hprod]
    exact hprop

end CFSG.LieType.HighestRoot
