module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Diagonal
public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic

public section

namespace CFSG.HardMathSupport.Dickson.ElementCaseBp

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.LocalCores
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {Y : Type*} [Group Y]

theorem conjSub_eq_self_of_mem_center {c : Y} (hc : c ∈ Subgroup.center Y) (L : Subgroup Y) :
    conjSub c L = L := by
  ext y
  rw [mem_conjSub_iff]
  have h := Subgroup.mem_center_iff.mp hc y
  have hcy : c⁻¹ * y * c = y := by
    rw [mul_assoc, h, inv_mul_cancel_left]
  rw [hcy]

private theorem conjSub_mul_of_mem_center {c : Y} (hc : c ∈ Subgroup.center Y) (g : Y)
    (K : Subgroup Y) : conjSub (c * g) K = conjSub g K := by
  rw [← conjSub_conjSub, conjSub_eq_self_of_mem_center hc]

private theorem conjSub_pow_eq_conjSub_pow_mod {p : ℕ} {f : Y} (hf : f ^ p ∈ Subgroup.center Y)
    (L : Subgroup Y) (n : ℕ) : conjSub (f ^ n) L = conjSub (f ^ (n % p)) L := by
  have h : f ^ n = (f ^ p) ^ (n / p) * f ^ (n % p) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [h]
  exact conjSub_mul_of_mem_center (pow_mem hf (n / p)) _ _

private theorem dvd_of_conjSub_pow_eq_of_pow_mem_center {p : ℕ} (hp : p.Prime) {L : Subgroup Y}
    {f : Y} (hf : f ^ p ∈ Subgroup.center Y) (hmoved : conjSub f L ≠ L) {n : ℕ}
    (h : conjSub (f ^ n) L = L) : p ∣ n := by
  by_contra hn
  have hcop : Nat.Coprime n p := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  apply hmoved
  have h1 : conjSub (f ^ (n * k)) L = L := by
    rw [pow_mul]
    exact conjSub_pow_eq h k
  have h2 := conjSub_pow_eq_conjSub_pow_mod hf L (n * k)
  rw [hk, pow_one] at h2
  exact h2.symm.trans h1

theorem conjSub_pow_ne_self_of_pow_mem_center {p : ℕ} (hp : p.Prime) {L : Subgroup Y} {f : Y}
    (hf : f ^ p ∈ Subgroup.center Y) (hmoved : conjSub f L ≠ L) {i : ℕ} (hi0 : 0 < i)
    (hip : i < p) : conjSub (f ^ i) L ≠ L := fun h =>
  absurd (Nat.le_of_dvd hi0 (dvd_of_conjSub_pow_eq_of_pow_mem_center hp hf hmoved h))
    (not_le.2 hip)

theorem diagProd_conj_comm_of_pow_mem_center {n : ℕ} {f : Y}
    (hf : f ^ (n + 1) ∈ Subgroup.center Y) {L : Subgroup Y} (hc : PairComm n f L) {x : Y}
    (hx : x ∈ L) : f * diagProd n f x * f⁻¹ = diagProd n f x := by
  unfold diagProd
  refine conj_ofFn_prod_rotate f (fun i : ℕ => f ^ i * x * (f ^ i)⁻¹) ?_ ?_ ?_
  · intro i
    simp only [pow_succ']
    group
  · have hcomm : f ^ (n + 1) * x = x * f ^ (n + 1) :=
      (Subgroup.mem_center_iff.mp hf x).symm
    show f ^ (n + 1) * x * (f ^ (n + 1))⁻¹ = f ^ 0 * x * (f ^ 0)⁻¹
    rw [hcomm, mul_inv_cancel_right, pow_zero, one_mul, inv_one, mul_one]
  · exact fun i j hi hj hij => hc i j hi hj hij x hx x hx

theorem pairComm_of_isComponent_of_pow_mem_center [Finite Y] {n : ℕ} (hp : (n + 1).Prime)
    {L : Subgroup Y} (hL : IsComponent L) {f : Y} (hf : f ^ (n + 1) ∈ Subgroup.center Y)
    (hmoved : conjSub f L ≠ L) : PairComm n f L := by
  have key : ∀ i j : ℕ, i < j → j < n + 1 → conjSub (f ^ i) L ≠ conjSub (f ^ j) L := by
    intro i j hij hj heq
    have h1 : conjSub (f ^ (n + 1 - i)) (conjSub (f ^ i) L) = L := by
      have hi : i ≤ n + 1 := by omega
      rw [conjSub_conjSub, ← pow_add, Nat.sub_add_cancel hi]
      exact conjSub_eq_self_of_mem_center hf L
    have h2 : conjSub (f ^ (n + 1 - i)) (conjSub (f ^ j) L) = conjSub (f ^ (j - i)) L := by
      rw [conjSub_conjSub, ← pow_add]
      have : n + 1 - i + j = (n + 1) + (j - i) := by omega
      rw [this, pow_add, conjSub_mul_of_mem_center hf]
    have hm : conjSub (f ^ (j - i)) L = L := by rw [← h2, ← heq, h1]
    have hm0 : 0 < j - i := by omega
    have hmp : j - i < n + 1 := by omega
    have hcop : Nat.Coprime (j - i) (n + 1) :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hm0 hmp))
    obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    have hft : conjSub ((f ^ (j - i)) ^ t) L = L := conjSub_pow_eq hm t
    apply hmoved
    have h3 := conjSub_pow_eq_conjSub_pow_mod hf L ((j - i) * t)
    rw [ht, pow_one] at h3
    rw [← pow_mul] at hft
    exact h3.symm.trans hft
  have hcomp : ∀ i : ℕ, IsComponent (conjSub (f ^ i) L) := fun i =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (f ^ i)) hL
  intro i j hi hj hij x hx y hy
  rcases lt_or_gt_of_ne hij with h | h
  · exact commute_of_isComponent_of_ne (hcomp i) (hcomp j) (key i j h hj) _
      (conj_mem_conjSub hx) _ (conj_mem_conjSub hy)
  · exact (commute_of_isComponent_of_ne (hcomp j) (hcomp i) (key j i h hi) _
      (conj_mem_conjSub hy) _ (conj_mem_conjSub hx)).symm

theorem exists_diagonal_component_of_pow_mem_center [Finite Y] {p : ℕ} (hp : p.Prime)
    {L : Subgroup Y} (hL : IsComponent L) {f : Y} (hf : f ^ p ∈ Subgroup.center Y)
    (hmoved : conjSub f L ≠ L) :
    ∃ Δ : Subgroup Y, Δ ≤ Subgroup.centralizer ({f} : Set Y) ∧
      IsComponent (Δ.subgroupOf (Subgroup.centralizer ({f} : Set Y))) ∧
      Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card Δ ∧
      ∀ x ∈ L, (List.ofFn fun i : Fin p => f ^ (i : ℕ) * x * (f ^ (i : ℕ))⁻¹).prod ∈ Δ := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hc : PairComm n f L := pairComm_of_isComponent_of_pow_mem_center hp hL hf hmoved
  let ψ : L →* Y :=
    MonoidHom.mk' (fun x : L => diagProd n f (x : Y)) (fun x y => diagProd_mul hc x.2 y.2)
  have hψ : ∀ x : L, ψ x = diagProd n f (x : Y) := fun x => rfl
  set Δ : Subgroup Y := ψ.range with hΔ
  set C : Subgroup Y := Subgroup.centralizer ({f} : Set Y) with hC
  have hΔC : Δ ≤ C := by
    rintro _ ⟨x, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff, hψ]
    exact ((mul_inv_eq_iff_eq_mul).mp (diagProd_conj_comm_of_pow_mem_center hf hc x.2)).symm
  have hker : ψ.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (comm_of_diagProd_eq_one hc x.2 hx g g.2)
  refine ⟨Δ, hΔC, ⟨?_, ?_⟩, ?_, fun x hx => ⟨⟨x, hx⟩, rfl⟩⟩
  ·
    have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center L := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker
    have hq := isQuasisimple_of_surjective hL.1 ψ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ψ) hker'
    exact isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΔC).symm hq
  ·
    set E : Subgroup Y := layer Y with hE
    have hEnorm : E.Normal := by
      have : (layer Y).Characteristic := layer_characteristic
      infer_instance
    have hLE : L ≤ E := component_le_layer hL
    have hΔE : Δ ≤ E := by
      rintro _ ⟨x, rfl⟩
      exact diagProd_mem_of_normal hEnorm (hLE x.2)
    have hEn : E ≤ Subgroup.normalizer (L : Set Y) := layer_le_normalizer hL
    have hN1 : (Δ.subgroupOf (E ⊓ C)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (le_inf hΔE hΔC)]
      rintro _ k ⟨w, rfl⟩ ⟨hkE, hkC⟩
      have hkf : k * f = f * k := Subgroup.mem_centralizer_singleton_iff.mp hkC
      have hkL : k * (w : Y) * k⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hEn hkE) w).mp w.2
      rw [hψ, diagProd_conj_of_commute hkf]
      exact ⟨⟨_, hkL⟩, rfl⟩
    have hN3 : ((E ⊓ C).subgroupOf C).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      rintro h k ⟨hhE, hhC⟩ hkC
      exact ⟨hEnorm.conj_mem h hhE k, C.mul_mem (C.mul_mem hkC hhC) (C.inv_mem hkC)⟩
    have hchain : IsSubnormal Δ C :=
      IsSubnormal.step (le_inf hΔE hΔC) hN1
        (IsSubnormal.step inf_le_right hN3 (IsSubnormal.refl C))
    have h1 : IsSubnormal (Δ.subgroupOf C) ⊤ :=
      (CFSG.ComponentClassification.LBalance.subnormal_subgroupOf_iff hΔC).mpr hchain
    exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h1
      Subgroup.IsSubnormal.top
  ·
    have h1 : Nat.card Δ = ψ.ker.index := by
      rw [Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv).symm
    rw [h1, ← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_of_le hker

end CFSG.HardMathSupport.Dickson.ElementCaseBp
