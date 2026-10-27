module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47P4Ft
public import CFSG.GroupTheory.ABGDGroups.LinearSemidihedral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_normalizer_of_isSylowOf {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {y : G}
    (hy : y ∈ normalizer (S : Set G)) (hy2 : IsPGroup 2 (zpowers y)) : y ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(S ⊔ zpowers y) :=
    hS.isPGroup.to_sup_of_normal_left' hy2 (zpowers_le.mpr hy)
  rw [← hS.eq_of_le le_sup_left le_top hp]
  exact mem_sup_right (mem_zpowers y)

theorem exists_odd_mul_of_mem_normalizer {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) {n : G}
    (hn : n ∈ normalizer (S : Set G)) :
    ∃ x₁ ∈ zpowers n, ∃ x₂ ∈ zpowers n, n = x₁ * x₂ ∧ Odd (orderOf x₁) ∧ x₂ ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hbez : (1 : ℤ) = ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m + (m : ℤ) * Nat.gcdB (2 ^ a) m := by
    have h := Nat.gcd_eq_gcd_ab (2 ^ a) m
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h
  set e₁ : ℤ := ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m with he₁
  set e₂ : ℤ := (m : ℤ) * Nat.gcdB (2 ^ a) m with he₂
  have hord : n ^ ((orderOf n : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_orderOf_eq_one]
  refine ⟨n ^ e₁, zpow_mem (mem_zpowers n) _, n ^ e₂, zpow_mem (mem_zpowers n) _, ?_, ?_, ?_⟩
  · rw [← zpow_add, ← hbez, zpow_one]
  · have h1 : (n ^ e₁) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show e₁ * (m : ℤ) =
        ((orderOf n : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m by rw [hnm, he₁]; push_cast; ring,
        zpow_mul, hord, one_zpow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  · refine mem_of_mem_normalizer_of_isSylowOf hS (zpow_mem hn _) ?_
    have h1 : (n ^ e₂) ^ (2 ^ a) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, show e₂ * ((2 ^ a : ℕ) : ℤ) =
        ((orderOf n : ℕ) : ℤ) * Nat.gcdB (2 ^ a) m by rw [hnm, he₂]; push_cast; ring,
        zpow_mul, hord, one_zpow]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

theorem exists_conj_of_involutions {A W : Subgroup G} [IsSimpleGroup (A ⧸ pPrimeCore 2 A)]
    (hna : ∃ a b : A ⧸ pPrimeCore 2 A, a * b ≠ b * a)
    (hdih : GorensteinWalter.HasDihedralSylowTwo (A ⧸ pPrimeCore 2 A)) (hW : IsPGroup 2 W)
    (hWC : W ≤ coreActionKernel A) {r t : G} (hrA : r ∈ A) (htA : t ∈ A) (hr : orderOf r = 2)
    (ht : orderOf t = 2) (hrW : r ∈ centralizer (W : Set G))
    (htW : t ∈ centralizer (W : Set G)) :
    ∃ k ∈ A, k ∈ centralizer (W : Set G) ∧ k⁻¹ * r * k = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := A ⧸ pPrimeCore 2 A with hX
  have himg : ∀ {u : G} (huA : u ∈ A), orderOf u = 2 → orderOf ((⟨u, huA⟩ : A) : X) = 2 := by
    intro u huA hu
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← QuotientGroup.mk_pow]
      have h2 : (⟨u, huA⟩ : A) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hu]
        exact pow_orderOf_eq_one u)
      rw [h2, QuotientGroup.mk_one]
    · rw [QuotientGroup.eq_one_iff, mem_pPrimeCore_iff_mem_oddCoreIn] at h1
      have hup : IsPGroup 2 (zpowers u) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
      have h3 := eq_one_of_mem_of_odd hup (odd_card_oddCoreIn A) (mem_zpowers u) h1
      rw [h3, orderOf_one] at hu
      omega
  obtain ⟨ybar, hy⟩ :=
    Foote47.isConj_of_simple_of_hasDihedralSylowTwo hdih hna (himg htA ht) (himg hrA hr)
  obtain ⟨⟨y₀, hy₀A⟩, rfl⟩ := QuotientGroup.mk_surjective ybar
  have hWN : W ≤ normalizer ((oddCoreIn A : Subgroup G) : Set G) := fun w hw =>
    mem_normalizer_oddCoreIn (hWC hw).1
  have hm : ∀ w ∈ W, y₀⁻¹ * (w * y₀ * w⁻¹) ∈ oddCoreIn A := by
    intro w hw
    have h1 := (inv_mem (hWC hw)).2 y₀ hy₀A
    rw [inv_inv] at h1
    rw [show y₀⁻¹ * (w * y₀ * w⁻¹) = y₀⁻¹ * w * y₀ * w⁻¹ by group]
    exact h1
  obtain ⟨o, hoO, hy₁⟩ :=
    Foote47.exists_mem_centralizer_of_isPGroup hW hWN (odd_card_oddCoreIn A) hm
  have hoA : o ∈ A := map_subtype_le _ hoO
  set y₁ := y₀ * o with hy₁def
  have hy₁A : y₁ ∈ A := mul_mem hy₀A hoA
  set b := y₁ * t * y₁⁻¹ with hb
  have hbA : b ∈ A := mul_mem (mul_mem hy₁A htA) (inv_mem hy₁A)
  have hrb : r⁻¹ * b ∈ oddCoreIn A := by
    have h1 : ((⟨r, hrA⟩ : A) : X) = ((⟨b, hbA⟩ : A) : X) := by
      rw [← hy]
      have ho1 : ((⟨o, hoA⟩ : A) : X) = 1 := by
        rw [QuotientGroup.eq_one_iff, mem_pPrimeCore_iff_mem_oddCoreIn]
        exact hoO
      have h2 : (⟨b, hbA⟩ : A) = ⟨y₀, hy₀A⟩ * ⟨o, hoA⟩ * ⟨t, htA⟩ * (⟨y₀, hy₀A⟩ * ⟨o, hoA⟩)⁻¹ :=
        Subtype.ext (by simp [hb, hy₁def])
      rw [h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_mul, ho1, mul_one]
    rw [QuotientGroup.eq, mem_pPrimeCore_iff_mem_oddCoreIn] at h1
    simpa using h1
  have hr2 : r * r = 1 := by rw [← sq, ← hr]; exact pow_orderOf_eq_one r
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hb2 : b * b = 1 := by
    rw [hb]
    calc y₁ * t * y₁⁻¹ * (y₁ * t * y₁⁻¹) = y₁ * (t * t) * y₁⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have hodd : Odd (orderOf (r * b)) := by
    rw [← hri]
    exact odd_orderOf_of_mem_of_odd (odd_card_oddCoreIn A) hrb
  obtain ⟨u, hu, hbu⟩ := Foote47.exists_conj_of_odd_orderOf_mul hr2 hb2 hodd
  have hbW : b ∈ centralizer (W : Set G) := mul_mem (mul_mem hy₁ htW) (inv_mem hy₁)
  have huW : u ∈ centralizer (W : Set G) := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    exact zpow_mem (mul_mem hrW hbW) k
  have huA : u ∈ A := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    refine zpow_mem ?_ k
    rw [← hri]
    exact map_subtype_le _ hrb
  refine ⟨u * y₁, mul_mem huA hy₁A, mul_mem huW hy₁, ?_⟩
  rw [show (u * y₁)⁻¹ * r * (u * y₁) = y₁⁻¹ * (u⁻¹ * r * u) * y₁ by group, ← hbu, hb]
  group

theorem exists_mul_of_dihedral {X : Type*} [Group X] {P : Subgroup X} {n : ℕ}
    (e : P ≃* DihedralGroup n) {p : X} (hp : p ∈ P) :
    ∃ a ∈ P, ∃ b ∈ P, a * a = 1 ∧ b * b = 1 ∧ p = a * b := by
  have hd : e.symm (e ⟨p, hp⟩) = ⟨p, hp⟩ := e.symm_apply_apply _
  have hsr : ∀ i : ZMod n, (e.symm (DihedralGroup.sr i) : X) * e.symm (DihedralGroup.sr i) = 1 :=
    fun i => by rw [← coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one, coe_one]
  rcases hde : e ⟨p, hp⟩ with i | i
  · refine ⟨e.symm (DihedralGroup.sr 0), (e.symm _).2, e.symm (DihedralGroup.sr i), (e.symm _).2,
      hsr 0, hsr i, ?_⟩
    rw [← coe_mul, ← map_mul, DihedralGroup.sr_mul_sr, sub_zero, ← hde, hd]
  · refine ⟨e.symm (DihedralGroup.sr i), (e.symm _).2, 1, one_mem _, hsr i, mul_one 1, ?_⟩
    rw [mul_one, ← hde, hd]

theorem exists_center_of_dihedral {X : Type*} [Group X] {P : Subgroup X} {m : ℕ}
    (e : P ≃* DihedralGroup (2 ^ m)) (hna : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) :
    ∃ c ∈ P, ∀ d ∈ P, (∀ p ∈ P, d * p = p * d) → d = 1 ∨ d = c := by
  have hm : 2 ≤ m := by
    by_contra hm
    have hcomm : IsMulCommutative (DihedralGroup (2 ^ m)) :=
      DihedralGroup.commutative_iff.mpr (by interval_cases m <;> simp)
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    apply hab
    have h1 := hcomm.is_comm.comm (e ⟨a, ha⟩) (e ⟨b, hb⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  set k : ℕ := 2 ^ m / 2 with hk
  have hkk : k + k = 2 ^ m := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    rw [hk, this, Nat.mul_div_cancel_left _ two_pos]
    ring
  have hrk : (DihedralGroup.r (k : ZMod (2 ^ m))) ^ 2 = 1 := by
    rw [sq, DihedralGroup.r_mul_r, ← Nat.cast_add, hkk, ZMod.natCast_self, DihedralGroup.r_zero]
  refine ⟨e.symm (DihedralGroup.r (k : ZMod (2 ^ m))), (e.symm _).2, fun d hd hdc => ?_⟩
  have hcen : e ⟨d, hd⟩ ∈ center (DihedralGroup (2 ^ m)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨p, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hdc p p.2).symm)
  have h2 : 2 ^ m ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right two_pos hm
    omega
  rw [DihedralGroup.center_eq_closure_of_even_ne_two
    (Nat.even_pow.mpr ⟨even_two, by omega⟩) h2] at hcen
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hcen
  rcases Int.even_or_odd' j with ⟨l, rfl | rfl⟩
  · left
    rw [zpow_mul, show (DihedralGroup.r (k : ZMod (2 ^ m))) ^ (2 : ℤ) = 1 by
      exact_mod_cast hrk, one_zpow] at hj
    have h3 := congrArg e.symm hj
    rw [map_one, e.symm_apply_apply] at h3
    exact congrArg Subtype.val h3.symm
  · right
    rw [zpow_add, zpow_mul, show (DihedralGroup.r (k : ZMod (2 ^ m))) ^ (2 : ℤ) = 1 by
      exact_mod_cast hrk, one_zpow, one_mul, zpow_one] at hj
    have h3 := congrArg e.symm hj
    rw [e.symm_apply_apply] at h3
    exact congrArg Subtype.val h3.symm

theorem card_le_four_of_dihedral_or_semidihedral {X : Type} [Group X] {P E : Subgroup X}
    (hP : AschbacherTheorem3.IsDihedralTwoGroup P ∨ AschbacherTheorem3.IsSemidihedralTwoGroup P)
    (hEP : E ≤ P) (hE : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have hcard : ∀ {Y : Type} [Group Y] (e : P ≃* Y),
      Nat.card ((E.subgroupOf P).map e.toMonoidHom) = Nat.card E := by
    intro Y _ e
    rw [card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv
  have hsq : ∀ {Y : Type} [Group Y] (e : P ≃* Y), ∀ y ∈ (E.subgroupOf P).map e.toMonoidHom,
      y * y = 1 := by
    intro Y _ e y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    rw [← map_mul]
    have h1 : x * x = 1 := Subtype.ext (by rw [coe_mul, coe_one]; exact hE _ hx)
    rw [h1, map_one]
  rcases hP with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h2 : 2 ^ (k + 2 - 1) = 2 * 2 ^ k := by
      rw [show k + 2 - 1 = k + 1 by omega, pow_succ']
    rw [h2] at e
    have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
    rw [← hcard e]
    exact SmallLocal.dihedral_card_le_four_of_mul_self_eq_one _ (hsq e)
  · rw [← hcard e]
    exact ABGDGroups.semidihedral_card_le_four hn _ fun x hx => by rw [sq]; exact hsq e x hx

omit [Finite G] in
theorem exists_finset_closure_of_ker {N : Subgroup G} {H : Type*} [Group H] (φ : N →* H)
    {U : Subgroup G} (hUN : U ≤ N) {a b : ℕ}
    (h1 : ∃ s : Finset G, s.card ≤ a ∧ closure (s : Set G) = U ⊓ φ.ker.map N.subtype)
    (h2 : ∃ s : Finset H, s.card ≤ b ∧ closure (s : Set H) = (U.subgroupOf N).map φ) :
    ∃ s : Finset G, s.card ≤ a + b ∧ closure (s : Set G) = U := by
  classical
  obtain ⟨s₁, hs₁, hs₁U⟩ := h1
  obtain ⟨s₂, hs₂, hs₂U⟩ := h2
  have hlift : ∀ α ∈ s₂, ∃ u : N, (u : G) ∈ U ∧ φ u = α := by
    intro α hα
    have h3 : α ∈ (U.subgroupOf N).map φ := hs₂U ▸ subset_closure hα
    obtain ⟨u, hu, rfl⟩ := mem_map.mp h3
    exact ⟨u, mem_subgroupOf.mp hu, rfl⟩
  choose! f hfU hfφ using hlift
  set s₃ : Finset G := s₂.image (fun α => (f α : G)) with hs₃
  have hs₃U : ∀ x ∈ s₃, x ∈ U := by
    intro x hx
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp hx
    exact hfU α hα
  refine ⟨s₁ ∪ s₃, (Finset.card_union_le _ _).trans
    (add_le_add hs₁ (Finset.card_image_le.trans hs₂)), le_antisymm ?_ ?_⟩
  · rw [closure_le]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have h3 : x ∈ U ⊓ φ.ker.map N.subtype := hs₁U ▸ subset_closure hx
      exact h3.1
    · exact hs₃U x hx
  · intro u hu
    set C : Subgroup G := Subgroup.closure (s₃ : Set G) with hC
    have hCs : C ≤ closure ((s₁ ∪ s₃ : Finset G) : Set G) :=
      closure_mono (by rw [Finset.coe_union]; exact Set.subset_union_right)
    have hCU : C ≤ U := by
      rw [hC, closure_le]
      exact fun x hx => hs₃U x hx
    have h3 : (U.subgroupOf N).map φ ≤ (C.subgroupOf N).map φ := by
      rw [← hs₂U, closure_le]
      intro α hα
      refine mem_map.mpr ⟨f α, mem_subgroupOf.mpr (subset_closure ?_), hfφ α hα⟩
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hα)
    obtain ⟨c, hc, hcu⟩ := mem_map.mp (h3 (mem_map_of_mem φ (mem_subgroupOf.mpr hu :
      (⟨u, hUN hu⟩ : N) ∈ U.subgroupOf N)))
    have hker : (c : G)⁻¹ * u ∈ U ⊓ φ.ker.map N.subtype := by
      refine mem_inf.mpr ⟨mul_mem (inv_mem (hCU (mem_subgroupOf.mp hc))) hu, ?_⟩
      refine mem_map.mpr ⟨c⁻¹ * ⟨u, hUN hu⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcu, inv_mul_cancel]
    rw [← hs₁U] at hker
    rw [show u = (c : G) * ((c : G)⁻¹ * u) by group]
    refine mul_mem (hCs (mem_subgroupOf.mp hc)) (closure_mono ?_ hker)
    rw [Finset.coe_union]
    exact Set.subset_union_left

end CFSG.ComponentClassification.Foote5
