module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Witness
public import CFSG.ClassicalInvolution.AschTight.Sec6GenL62
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym
public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI2
public import CFSG.ClassicalInvolution.AschTight.Sec7L76A
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

namespace Wr

variable {G : Type*} [Group G]

theorem wr_conj_a {a c b : G} (hba : b * a * b⁻¹ = c) (k : ℤ) : b * a ^ k * b⁻¹ = c ^ k := by
  rw [← hba, conj_zpow]

theorem wr_conj_c {a c b : G} (hbc : b * c * b⁻¹ = a) (k : ℤ) : b * c ^ k * b⁻¹ = a ^ k := by
  rw [← hbc, conj_zpow]

theorem wr_hcomm {a c : G} (hac : a * c = c * a) (m n : ℤ) : a ^ m * c ^ n = c ^ n * a ^ m :=
  ((Commute.zpow_zpow (show Commute a c from hac) m n)).eq

theorem wr_swap_a {a c b : G} (hb : b * b = 1) (hba : b * a * b⁻¹ = c) (k : ℤ) :
    b * a ^ k = c ^ k * b := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have := wr_conj_a hba k
  rw [hbinv] at this
  calc b * a ^ k = b * a ^ k * b * b := by rw [mul_assoc (b * a ^ k), hb, mul_one]
    _ = c ^ k * b := by rw [this]

theorem wr_swap_c {a c b : G} (hb : b * b = 1) (hbc : b * c * b⁻¹ = a) (k : ℤ) :
    b * c ^ k = a ^ k * b := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have := wr_conj_c hbc k
  rw [hbinv] at this
  calc b * c ^ k = b * c ^ k * b * b := by rw [mul_assoc (b * c ^ k), hb, mul_one]
    _ = a ^ k * b := by rw [this]

def wrForm (a c b : G) (g : G) : Prop :=
  ∃ i j : ℤ, g = a ^ i * c ^ j ∨ g = a ^ i * c ^ j * b

theorem wr_form_mul {a c b : G} (hac : a * c = c * a) (hb : b * b = 1) (hba : b * a * b⁻¹ = c)
    (hbc : b * c * b⁻¹ = a) {g h : G} (hg : wrForm a c b g) (hh : wrForm a c b h) :
    wrForm a c b (g * h) := by
  have hcomm := wr_hcomm hac
  have hswapa := wr_swap_a hb hba
  have hswapc := wr_swap_c hb hbc
  obtain ⟨i, j, hg | hg⟩ := hg <;> obtain ⟨k, l, hh | hh⟩ := hh <;> subst hg <;> subst hh
  · refine ⟨i + k, j + l, Or.inl ?_⟩
    calc a ^ i * c ^ j * (a ^ k * c ^ l) = a ^ i * (c ^ j * a ^ k) * c ^ l := by group
      _ = a ^ i * (a ^ k * c ^ j) * c ^ l := by rw [← hcomm k j]
      _ = a ^ (i + k) * c ^ (j + l) := by rw [zpow_add, zpow_add]; group
  · refine ⟨i + k, j + l, Or.inr ?_⟩
    calc a ^ i * c ^ j * (a ^ k * c ^ l * b) = a ^ i * (c ^ j * a ^ k) * c ^ l * b := by group
      _ = a ^ i * (a ^ k * c ^ j) * c ^ l * b := by rw [← hcomm k j]
      _ = a ^ (i + k) * c ^ (j + l) * b := by rw [zpow_add, zpow_add]; group
  · refine ⟨i + l, j + k, Or.inr ?_⟩
    calc a ^ i * c ^ j * b * (a ^ k * c ^ l) = a ^ i * c ^ j * (b * a ^ k) * c ^ l := by group
      _ = a ^ i * c ^ j * (c ^ k * b) * c ^ l := by rw [hswapa]
      _ = a ^ i * c ^ j * c ^ k * (b * c ^ l) := by group
      _ = a ^ i * c ^ j * c ^ k * (a ^ l * b) := by rw [hswapc]
      _ = a ^ i * (c ^ (j + k) * a ^ l) * b := by rw [zpow_add]; group
      _ = a ^ i * (a ^ l * c ^ (j + k)) * b := by rw [← hcomm l (j + k)]
      _ = a ^ (i + l) * c ^ (j + k) * b := by rw [zpow_add]; group
  · refine ⟨i + l, j + k, Or.inl ?_⟩
    calc a ^ i * c ^ j * b * (a ^ k * c ^ l * b)
        = a ^ i * c ^ j * (b * a ^ k) * c ^ l * b := by group
      _ = a ^ i * c ^ j * (c ^ k * b) * c ^ l * b := by rw [hswapa]
      _ = a ^ i * c ^ j * c ^ k * (b * c ^ l) * b := by group
      _ = a ^ i * c ^ j * c ^ k * (a ^ l * b) * b := by rw [hswapc]
      _ = a ^ i * (c ^ (j + k) * a ^ l) * (b * b) := by rw [zpow_add]; group
      _ = a ^ i * (a ^ l * c ^ (j + k)) := by rw [← hcomm l (j + k), hb, mul_one]
      _ = a ^ (i + l) * c ^ (j + k) := by rw [zpow_add]; group

theorem wr_form_inv {a c b : G} (hac : a * c = c * a) (hb : b * b = 1) (hba : b * a * b⁻¹ = c)
    (hbc : b * c * b⁻¹ = a) {g : G} (hg : wrForm a c b g) : wrForm a c b g⁻¹ := by
  have hcomm := wr_hcomm hac
  have hswapa := wr_swap_a hb hba
  have hswapc := wr_swap_c hb hbc
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  obtain ⟨i, j, hg | hg⟩ := hg <;> subst hg
  · refine ⟨-i, -j, Or.inl ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (hcomm (-i) (-j)).symm
  · refine ⟨-j, -i, Or.inr ?_⟩
    have e1 : (a ^ i * c ^ j * b)⁻¹ = b * (c ^ (-j) * a ^ (-i)) := by
      simp only [mul_inv_rev, hbinv, zpow_neg, mul_assoc]
    rw [e1]
    calc b * (c ^ (-j) * a ^ (-i)) = (b * c ^ (-j)) * a ^ (-i) := by group
      _ = (a ^ (-j) * b) * a ^ (-i) := by rw [hswapc]
      _ = a ^ (-j) * (b * a ^ (-i)) := by group
      _ = a ^ (-j) * (c ^ (-i) * b) := by rw [hswapa]
      _ = a ^ (-j) * c ^ (-i) * b := by group

theorem wr_closure_form {a c b : G} (hac : a * c = c * a) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = c) (hbc : b * c * b⁻¹ = a) {x : G}
    (hx : x ∈ Subgroup.closure ({a, c, b} : Set G)) : wrForm a c b x := by
  let S : Subgroup G :=
    { carrier := {g | wrForm a c b g}
      one_mem' := ⟨0, 0, Or.inl (by simp)⟩
      mul_mem' := fun hg hh => wr_form_mul hac hb hba hbc hg hh
      inv_mem' := fun hg => wr_form_inv hac hb hba hbc hg }
  have hle : Subgroup.closure ({a, c, b} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨1, 0, Or.inl (by simp)⟩
    · exact ⟨0, 1, Or.inl (by simp)⟩
    · exact ⟨0, 0, Or.inr (by simp)⟩
  exact hle hx

theorem wr_finite_zpowers {a : G} (ha : 0 < orderOf a) : (Subgroup.zpowers a : Set G).Finite := by
  have h : Finite (Subgroup.zpowers a) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zpowers]
    exact ha.ne'
  exact Set.toFinite _

theorem wr_ne {a c b : G} (hac : a * c = c * a) (hb : b * b = 1) (hba : b * a * b⁻¹ = c)
    (hbc : b * c * b⁻¹ = a) {P : Subgroup G} (hcl : Subgroup.closure ({a, c, b} : Set G) = P)
    (ha : 4 ≤ orderOf a) (hP : Nat.card P = 2 * orderOf a ^ 2) : a ≠ c := by
  intro hae
  subst hae
  have hpos : 0 < orderOf a := by omega
  have hfin := wr_finite_zpowers (a := a) hpos
  set A : Set G := (Subgroup.zpowers a : Set G) with hA
  have hsub : (P : Set G) ⊆ A ∪ (fun g => g * b) '' A := by
    intro g hg
    rw [← hcl] at hg
    obtain ⟨i, j, h | h⟩ := wr_closure_form hac hb hba hbc hg
    · left
      rw [h, ← zpow_add]
      exact Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩
    · right
      refine ⟨a ^ (i + j), Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩, ?_⟩
      simp only
      rw [h, zpow_add]
  have hfinT : (A ∪ (fun g => g * b) '' A).Finite := hfin.union (hfin.image _)
  have h1 := Set.ncard_le_ncard hsub hfinT
  have h2 := Set.ncard_union_le A ((fun g => g * b) '' A)
  have h3 : ((fun g => g * b) '' A).ncard ≤ A.ncard := Set.ncard_image_le hfin
  have h4 : A.ncard = orderOf a := by
    rw [hA, ← Nat.card_coe_set_eq]
    exact Nat.card_zpowers a
  have h5 : (P : Set G).ncard = Nat.card P := (Nat.card_coe_set_eq _).symm
  rw [h5, hP] at h1
  nlinarith

theorem wr_pow_eq {a : G} (hn : 0 < orderOf a) (k : ℤ) :
    ∃ r : ℕ, r < orderOf a ∧ a ^ k = a ^ r := by
  have h0 : (orderOf a : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 := Int.emod_nonneg k h0
  have h2 := Int.emod_lt_of_pos k (show (0 : ℤ) < orderOf a by exact_mod_cast hn)
  refine ⟨(k % (orderOf a : ℤ)).toNat, by omega, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg h1, zpow_mod_orderOf]

theorem wr_inj {a c b : G} (hac : a * c = c * a) (hb : b * b = 1) (hba : b * a * b⁻¹ = c)
    (hbc : b * c * b⁻¹ = a) {P : Subgroup G} (hcl : Subgroup.closure ({a, c, b} : Set G) = P)
    (ha : 4 ≤ orderOf a) (hc : orderOf c = orderOf a) (hP : Nat.card P = 2 * orderOf a ^ 2) :
    Function.Injective
      (fun p : Fin (orderOf a) × Fin (orderOf a) => a ^ (p.1 : ℕ) * c ^ (p.2 : ℕ)) := by
  classical
  have hpos : 0 < orderOf a := by omega
  have hposc : 0 < orderOf c := by omega
  set F : Fin (orderOf a) × Fin (orderOf a) → G :=
    fun p => a ^ (p.1 : ℕ) * c ^ (p.2 : ℕ) with hF
  set Fs : Finset G := Finset.univ.image F with hFs
  have hmem : ∀ i j : ℤ, a ^ i * c ^ j ∈ Fs := by
    intro i j
    obtain ⟨r, hr, hri⟩ := wr_pow_eq hpos i
    obtain ⟨s, hs, hsj⟩ := wr_pow_eq hposc j
    rw [hc] at hs
    refine Finset.mem_image.mpr ⟨(⟨r, hr⟩, ⟨s, hs⟩), Finset.mem_univ _, ?_⟩
    simp only [hF]
    rw [hri, hsj]
  have hsub : (P : Set G) ⊆ (Fs : Set G) ∪ (fun g => g * b) '' (Fs : Set G) := by
    intro g hg
    rw [← hcl] at hg
    obtain ⟨i, j, h | h⟩ := wr_closure_form hac hb hba hbc hg
    · left
      rw [h]
      exact Finset.mem_coe.mpr (hmem i j)
    · right
      exact ⟨a ^ i * c ^ j, Finset.mem_coe.mpr (hmem i j), by simp only; rw [h]⟩
  have hfinT : ((Fs : Set G) ∪ (fun g => g * b) '' (Fs : Set G)).Finite :=
    (Fs.finite_toSet).union ((Fs.finite_toSet).image _)
  have h1 := Set.ncard_le_ncard hsub hfinT
  have h2 := Set.ncard_union_le (Fs : Set G) ((fun g => g * b) '' (Fs : Set G))
  have h3 : ((fun g => g * b) '' (Fs : Set G)).ncard ≤ (Fs : Set G).ncard :=
    Set.ncard_image_le Fs.finite_toSet
  have h4 : (Fs : Set G).ncard = Fs.card := Set.ncard_coe_finset Fs
  have h5 : (P : Set G).ncard = Nat.card P := (Nat.card_coe_set_eq _).symm
  rw [h5, hP] at h1
  have h6 : Fs.card ≤ orderOf a * orderOf a := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin (orderOf a) × Fin (orderOf a))))
      (f := F)
    simpa [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using this
  have h7 : Fs.card = (Finset.univ : Finset (Fin (orderOf a) × Fin (orderOf a))).card := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    nlinarith
  have h8 := Finset.card_image_iff.mp h7
  intro p q hpq
  exact h8 (Finset.mem_coe.mpr (Finset.mem_univ p)) (Finset.mem_coe.mpr (Finset.mem_univ q)) hpq

theorem wr_inter {a c b : G} (hac : a * c = c * a) (hb : b * b = 1) (hba : b * a * b⁻¹ = c)
    (hbc : b * c * b⁻¹ = a) {P : Subgroup G} (hcl : Subgroup.closure ({a, c, b} : Set G) = P)
    (ha : 4 ≤ orderOf a) (hc : orderOf c = orderOf a) (hP : Nat.card P = 2 * orderOf a ^ 2)
    (k l : ℤ) (h : a ^ k = c ^ l) : a ^ k = 1 := by
  have hinj := wr_inj hac hb hba hbc hcl ha hc hP
  have hpos : 0 < orderOf a := by omega
  have hposc : 0 < orderOf c := by omega
  obtain ⟨r, hr, hrk⟩ := wr_pow_eq hpos k
  obtain ⟨s, hs, hsl⟩ := wr_pow_eq hposc (-l)
  rw [hc] at hs
  have h1 : a ^ r * c ^ s = 1 := by
    rw [← hrk, ← hsl, h, ← zpow_add]
    simp
  have h2 : ((⟨r, hr⟩, ⟨s, hs⟩) : Fin (orderOf a) × Fin (orderOf a)) =
      (⟨0, hpos⟩, ⟨0, hpos⟩) := by
    apply hinj
    simp only [pow_zero, mul_one]
    exact h1
  have h3 : r = 0 := by
    have := congrArg (fun p : Fin (orderOf a) × Fin (orderOf a) => (p.1 : ℕ)) h2
    simpa using this
  rw [hrk, h3]
  simp

theorem wr_half {n : ℕ} {i : ℤ} (hn : 0 < n) (h2 : (n : ℤ) ∣ 2 * i) (h1 : ¬ (n : ℤ) ∣ i) :
    ∃ m : ℤ, i = n * m + ((n / 2 : ℕ) : ℤ) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hdiv := Int.mul_ediv_add_emod i n
  have hr1 := Int.emod_nonneg i (show (n : ℤ) ≠ 0 by omega)
  have hr2 := Int.emod_lt_of_pos i hn'
  have h3 : (n : ℤ) ∣ 2 * (i % n) := by
    have : 2 * (i % n) = 2 * i - n * (2 * (i / n)) := by linarith
    rw [this]
    exact dvd_sub h2 (dvd_mul_right _ _)
  obtain ⟨s, hs⟩ := h3
  have hs0 : 0 ≤ s := by
    by_contra h
    push Not at h
    nlinarith
  have hs2 : s < 2 := by
    by_contra h
    push Not at h
    nlinarith
  have hs' : s = 0 ∨ s = 1 := by omega
  rcases hs' with rfl | rfl
  · exfalso
    apply h1
    have : i % n = 0 := by omega
    exact Int.dvd_of_emod_eq_zero this
  · refine ⟨i / n, ?_⟩
    have : ((n / 2 : ℕ) : ℤ) = i % n := by omega
    rw [this]
    linarith

theorem wr_zpow_shift {x : G} {n : ℕ} (hx : orderOf x = n) (m h : ℤ) :
    x ^ ((n : ℤ) * m + h) = x ^ h := by
  rw [zpow_add, zpow_mul, ← hx, zpow_natCast, pow_orderOf_eq_one, one_zpow, one_mul]

theorem wr_central_form {a c b : G} (hac : a * c = c * a) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = c) (hbc : b * c * b⁻¹ = a) {P : Subgroup G}
    (hcl : Subgroup.closure ({a, c, b} : Set G) = P) (ha : 4 ≤ orderOf a)
    (hc : orderOf c = orderOf a) (hP : Nat.card P = 2 * orderOf a ^ 2)
    {z : G} (hz : z ∈ P) (hzc : ∀ p ∈ P, p * z = z * p) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    z = a ^ ((orderOf a / 2 : ℕ) : ℤ) * c ^ ((orderOf a / 2 : ℕ) : ℤ) := by
  have hne := wr_ne hac hb hba hbc hcl ha hP
  have hcomm := wr_hcomm hac
  have haP : a ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hbP : b ∈ P := hcl ▸ Subgroup.subset_closure (by simp)
  have hpos : 0 < orderOf a := by omega
  obtain ⟨i, j, h | h⟩ := wr_closure_form hac hb hba hbc (hcl ▸ hz)
  swap
  · exfalso
    apply hne
    have hac' : Commute a c := hac
    have hwc : Commute (a ^ i * c ^ j) c :=
      (hac'.zpow_left i).mul_left ((Commute.refl c).zpow_left j)
    have h1 : z * a * z⁻¹ = c := by
      rw [h]
      calc a ^ i * c ^ j * b * a * (a ^ i * c ^ j * b)⁻¹
          = (a ^ i * c ^ j) * (b * a * b⁻¹) * (a ^ i * c ^ j)⁻¹ := by group
        _ = (a ^ i * c ^ j) * c * (a ^ i * c ^ j)⁻¹ := by rw [hba]
        _ = c := by rw [hwc.eq, mul_inv_cancel_right]
    have h2 : z * a * z⁻¹ = a := by rw [← hzc a haP, mul_inv_cancel_right]
    rw [← h1, h2]
  · have hbz : b * z = z * b := hzc b hbP
    have e1 : b * z * b⁻¹ = c ^ i * a ^ j := by
      rw [h]
      calc b * (a ^ i * c ^ j) * b⁻¹ = (b * a ^ i * b⁻¹) * (b * c ^ j * b⁻¹) := by group
        _ = c ^ i * a ^ j := by rw [wr_conj_a hba, wr_conj_c hbc]
    have e2 : b * z * b⁻¹ = z := by rw [hbz, mul_inv_cancel_right]
    have e3 : a ^ j * c ^ i = a ^ i * c ^ j := by
      calc a ^ j * c ^ i = c ^ i * a ^ j := hcomm j i
        _ = b * z * b⁻¹ := e1.symm
        _ = z := e2
        _ = a ^ i * c ^ j := h
    have e4 : a ^ (j - i) = c ^ (j - i) := by
      calc a ^ (j - i) = a ^ (-i) * (a ^ j * c ^ i) * c ^ (-i) := by group
        _ = a ^ (-i) * (a ^ i * c ^ j) * c ^ (-i) := by rw [e3]
        _ = c ^ (j - i) := by group
    have hinter := fun k l (hkl : a ^ k = c ^ l) => wr_inter hac hb hba hbc hcl ha hc hP k l hkl
    have e5 : a ^ (j - i) = 1 := hinter _ _ e4
    have e6 : c ^ (j - i) = 1 := e4 ▸ e5
    have e7 : z = a ^ i * c ^ i := by
      calc z = a ^ i * c ^ j := h
        _ = a ^ i * (c ^ i * c ^ (j - i)) := by group
        _ = a ^ i * c ^ i := by rw [e6, mul_one]
    have e8 : a ^ (2 * i) = 1 := by
      have h1 : a ^ (2 * i) * c ^ (2 * i) = 1 := by
        calc a ^ (2 * i) * c ^ (2 * i) = a ^ i * a ^ i * (c ^ i * c ^ i) := by
              rw [two_mul, zpow_add, zpow_add]
          _ = a ^ i * (a ^ i * c ^ i) * c ^ i := by group
          _ = a ^ i * (c ^ i * a ^ i) * c ^ i := by rw [hcomm i i]
          _ = (a ^ i * c ^ i) * (a ^ i * c ^ i) := by group
          _ = 1 := by rw [← e7]; exact hz2
      apply hinter (2 * i) (-(2 * i))
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_left h1
    have e9 : (orderOf a : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.mpr e8
    have e10 : ¬ (orderOf a : ℤ) ∣ i := by
      intro hd
      apply hz1
      have h1 : a ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.mp hd
      have h2 : c ^ i = 1 := orderOf_dvd_iff_zpow_eq_one.mp (hc ▸ hd)
      rw [e7, h1, h2, one_mul]
    obtain ⟨m, hm⟩ := wr_half hpos e9 e10
    rw [e7, hm, wr_zpow_shift rfl, wr_zpow_shift hc]

theorem wreathed_central_involutions_eq {G : Type*} [Group G] (P : Subgroup G) (a c b : G)
    (ha : 4 ≤ orderOf a) (hc : orderOf c = orderOf a) (hac : a * c = c * a)
    (hP : Nat.card P = 2 * orderOf a ^ 2) (hb : b * b = 1) (hba : b * a * b⁻¹ = c)
    (hbc : b * c * b⁻¹ = a) (hcl : Subgroup.closure {a, c, b} = P)
    {x y : G} (hx : x ∈ P) (hy : y ∈ P)
    (hxc : ∀ p ∈ P, p * x = x * p) (hyc : ∀ p ∈ P, p * y = y * p)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  rw [wr_central_form hac hb hba hbc hcl ha hc hP hx hxc hx2 hx1,
    wr_central_form hac hb hba hbc hcl ha hc hP hy hyc hy2 hy1]

theorem isWreathed_eq_of_central_involutions {G : Type} [Group G] {P : Subgroup G}
    (hP : IsWreathed P) {x y : G} (hx : x ∈ P) (hy : y ∈ P)
    (hxc : ∀ p ∈ P, p * x = x * p) (hyc : ∀ p ∈ P, p * y = y * p)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  obtain ⟨a, c, b, ha, hc, hac, hcard, hb, hba, hbc, hcl⟩ := hP
  exact wreathed_central_involutions_eq P a c b ha hc hac hcard hb hba hbc hcl hx hy hxc hyc
    hx2 hy2 hx1 hy1

end Wr

section Graph

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_subset_omegaStarNbr_gen (hΩ : HypOmegaGen Ω) (K : Subgroup G) :
    omegaNbr Ω K ⊆ omegaStarNbr Ω K := by
  rintro J ⟨hJ, hJK, R, hR, hRJ, hRN⟩
  obtain ⟨U, hUR, hUc, hcard⟩ := (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR).exists_cyclic_index_two
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    have hU0 : 0 < Nat.card U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hU0 h1
  exact ⟨hJ, hJK, U, ⟨R, hR, hUR, hUc, hrel⟩, hUR.trans hRJ, hUR.trans hRN⟩

theorem commutator_mem_oddCore_of_action_eq_one {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G))
    (h : Hat2A7.oddQuotAut K (Hat2A7.conjOn K g hg) = 1) (k : ↥K) :
    k⁻¹ * Hat2A7.conjOn K g hg k ∈ classicalInvolutionOddCore ↥K := by
  have h1 : Hat2A7.oddQuotAut K (Hat2A7.conjOn K g hg) (k : Hat2A7.OddQuot K) =
      (k : Hat2A7.OddQuot K) := by
    rw [h]
    rfl
  rw [Hat2A7.oddQuotAut_mk] at h1
  exact QuotientGroup.eq.mp h1.symm

end Graph

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem omegaNbr_of_omegaStarNbr (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    (h16 : ∀ J ∈ Ω, ∀ R : Subgroup G, IsSylow2In R J → 16 ≤ Nat.card R)
    {K J : Subgroup G} (hK : K ∈ Ω) {z t : G} (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (hzt : z ≠ t) (hJ : J ∈ omegaStarNbr Ω K) :
    J ∈ omegaNbr Ω K := by
  obtain ⟨hJΩ, hJK, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R₀, hR₀, J₀, hJ₀, hR₀J₀, hUR₀, hUc, hcardR₀, hU4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hJ₀J : J₀ = J := Sec6Gen.eq_of_mem_USet hΩ hU hJ₀ hJΩ (hUR₀.trans hR₀J₀.1) hUJ
  subst hJ₀J
  have hU8 : 8 ≤ Nat.card U := by
    have := h16 J₀ hJ₀ R₀ hR₀J₀
    omega
  have hU2 : IsPGroup 2 U := hR₀J₀.2.1.to_le hUR₀
  have htU : t ∈ U := T3.mem_of_isPGroup ht hUJ hU2 (by omega)
  have hUz : U ≤ Subgroup.centralizer ({z} : Set G) :=
    T3.le_centralizer_of_le_normalizer' hz hUN
  obtain ⟨V, hV, hUV⟩ := IsSylow2In.exists_ge hU2 (le_inf hUJ hUz)
  have htV : t ∈ V := hUV htU
  have hVJ : V ≤ J₀ := hV.1.trans inf_le_left
  have hVz : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  have hV2 : IsPGroup 2 V := hV.2.1
  have hVcard : 8 ≤ Nat.card V := hU8.trans (Subgroup.card_le_of_le hUV)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht.sq) ht.ne_one
  have hpair : Sec6Gen.Pair Ω K J₀ z t := ⟨hK, hJΩ, hz, ht, hzt⟩
  rcases Sec6Gen.Pair.six_two hΩ hpair hV htV with
    ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, hVN, R, hR, hRK, hVR, hW⟩ | ⟨hV4, hcomm⟩
  · exfalso
    have : Nat.card V = 2 := by rw [hV1, Nat.card_zpowers, ht2]
    omega
  · exfalso
    have : Nat.card V = 2 := by rw [hV1, Nat.card_zpowers, ht2]
    omega
  · exfalso
    have hR2 : IsPGroup 2 R := Sec7.isPGroup_of_mem_RSet hR
    have hVunique : ∀ x ∈ V, orderOf x = 2 → x = t := fun x hx hx2 => by
      have hxx : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hx2, pow_two] at this
      rcases ht.unique x (hVJ hx) hxx with h | h
      · exfalso
        rw [h, orderOf_one] at hx2
        omega
      · exact h
    have hgt : t ∈ Subgroup.normalizer (K : Set G) := hVN htV
    have htriv := Hat2A7.oddQuotAut_conjOn_eq_one_of_card (hw K hK) hVN hV2 htV hVunique
      (by omega)
    have htR : ∀ r ∈ R, t * r = r * t := by
      intro r hr
      have hrK : r ∈ K := hRK hr
      have hmem := commutator_mem_oddCore_of_action_eq_one hgt htriv ⟨r, hrK⟩
      have hmemG : r⁻¹ * (t * r * t⁻¹) ∈ oddCoreOf K :=
        ⟨_, hmem, rfl⟩
      have htrR : t * r * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hVR htV) r).mp hr
      have hxR : r⁻¹ * (t * r * t⁻¹) ∈ R := R.mul_mem (R.inv_mem hr) htrR
      have h1 : r⁻¹ * (t * r * t⁻¹) = 1 :=
        eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmemG
          (hR2.to_le (Subgroup.zpowers_le.mpr hxR))
      have h2 : t * r * t⁻¹ = r := by
        have := congrArg (fun y => r * y) h1
        simpa using this
      calc t * r = t * r * t⁻¹ * t := by group
        _ = r * t := by rw [h2]
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
    have hzR : z ∈ R := T3.mem_of_isPGroup hz hRK hR2 (by omega)
    have hzc : ∀ p ∈ R ⊔ V, p * z = z * p := by
      have hle : R ⊔ V ≤ Subgroup.centralizer ({z} : Set G) := by
        refine sup_le (fun r hr => ?_) hVz
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := hz.conj_eq (n := r)
          (mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer (hRK hr)))
        calc r * z = r * z * r⁻¹ * r := by group
          _ = z * r := by rw [this]
      intro p hp
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hp)
    have htc : ∀ p ∈ R ⊔ V, p * t = t * p := by
      have hle : R ⊔ V ≤ Subgroup.centralizer ({t} : Set G) := by
        refine sup_le (fun r hr => ?_) (fun v hv => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (htR r hr).symm
        · rw [Subgroup.mem_centralizer_singleton_iff]
          obtain ⟨R', -, -, hcyc, -⟩ := hV3
          have hcomm : (⟨v, hv⟩ : ↥V) * ⟨t, htV⟩ = ⟨t, htV⟩ * ⟨v, hv⟩ := by
            let : CommGroup ↥V := IsCyclic.commGroup
            exact mul_comm _ _
          exact congrArg Subtype.val hcomm
      intro p hp
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hp)
    exact hzt (Wr.isWreathed_eq_of_central_involutions hW (Subgroup.mem_sup_left hzR)
      (Subgroup.mem_sup_right htV) hzc htc hz.sq ht.sq hz.ne_one ht.ne_one)
  · have hVN : V ≤ Subgroup.normalizer (K : Set G) := by
      intro v hv
      rw [mem_normalizer_iff_conjSub_eq]
      apply Sec7.conjSub_eq_of_le_self
      intro y hy
      rw [mem_conjSub_iff] at hy
      have hcm : ⁅v, v⁻¹ * y * v⁆ ∈ K :=
        oddCoreOf_le_self K (hcomm (Subgroup.commutator_mem_commutator hv hy))
      have e : y = ⁅v, v⁻¹ * y * v⁆ * (v⁻¹ * y * v) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact K.mul_mem hcm hy
    exact ⟨hJΩ, hJK, V, hV4, hVJ, hVN⟩

theorem omegaStarNbr_subset_omegaNbr (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    (h16 : ∀ J ∈ Ω, ∀ R : Subgroup G, IsSylow2In R J → 16 ≤ Nat.card R)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K : Subgroup G} (hK : K ∈ Ω) :
    omegaStarNbr Ω K ⊆ omegaNbr Ω K := by
  intro J hJ
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  by_cases hzt : z = t
  · exfalso
    have hJt : J ∈ twinSet Ω K := ⟨hJ.1, z, hz, by rw [hzt]; exact ht⟩
    exact hJ.2.1 (hnt K hK J hJt)
  · exact omegaNbr_of_omegaStarNbr hΩ hw h16 hK hz ht hzt hJ

theorem dComp_eq_dstarComp (hΩ : HypOmegaGen Ω) (hw : ∀ L ∈ Ω, A7Witness L)
    (h16 : ∀ J ∈ Ω, ∀ R : Subgroup G, IsSylow2In R J → 16 ≤ Nat.card R)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K : Subgroup G} (hK : K ∈ Ω) :
    dComp Ω K = dstarComp Ω K := by
  ext J
  constructor
  · intro h
    have h' : Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J := h
    show Relation.ReflTransGen (dstarAdj Ω) K J
    refine Relation.ReflTransGen.mono (fun M N hMN => ?_) K J h'
    obtain ⟨hN, hadj⟩ := hMN
    refine ⟨hN, ?_⟩
    rcases hadj with h1 | h1
    · exact Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩ M h1)
    · exact Or.inr (omegaNbr_subset_omegaStarNbr_gen hΩ N h1)
  · intro h0
    have h : Relation.ReflTransGen (dstarAdj Ω) K J := h0
    clear h0
    have key : J ∈ Ω ∧ Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K J := by
      induction h with
      | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        rename_i b c
        obtain ⟨hbΩ, hbr⟩ := ih
        refine ⟨hbc.1, hbr.tail ⟨hbc.1, ?_⟩⟩
        rcases hbc.2 with h1 | h1
        · exact Or.inl (omegaStarNbr_subset_omegaNbr hΩ hw h16 hnt hbΩ h1)
        · exact Or.inr (omegaStarNbr_subset_omegaNbr hΩ hw h16 hnt hbc.1 h1)
    exact key.2

end Main

end CFSG.ClassicalInvolution.Hat2A7S8
