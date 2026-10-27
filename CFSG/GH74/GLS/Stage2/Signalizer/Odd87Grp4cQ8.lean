module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpQ8
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

theorem card_center_eq_two_of_card_eight {M : Type*} [Group M] [Finite M]
    (h8 : Nat.card M = 8) (hnc : ¬ ∀ a b : M, a * b = b * a) :
    Nat.card (Subgroup.center M) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hcard⟩ := IsPGroup.card_center_eq_prime_pow (p := 2) (n := 3)
    (by rw [h8]; norm_num) (by norm_num)
  have hdvd : Nat.card (Subgroup.center M) ∣ 8 := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center M)
    rwa [h8] at this
  rw [hcard] at hdvd ⊢
  have hk3 : k ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 hcon
    have := (this.trans hdvd)
    omega
  have hidx := Subgroup.index_mul_card (Subgroup.center M)
  rw [hcard, h8] at hidx
  interval_cases k
  · rfl
  · exfalso
    have hi : (Subgroup.center M).index = 2 := by omega
    have hcyc : IsCyclic (M ⧸ Subgroup.center M) :=
      isCyclic_of_prime_card (p := 2) (by
        have : Nat.card (M ⧸ Subgroup.center M) = 2 := hi
        exact this)
    exact hnc (fun a b => (isMulCommutative_of_isCyclic_quotient_center_self
      (G := M)).is_comm.comm a b)
  · exfalso
    have hi : (Subgroup.center M).index = 1 := by omega
    have htop : Subgroup.center M = ⊤ := Subgroup.index_eq_one.mp hi
    apply hnc
    intro a b
    have : b ∈ Subgroup.center M := by rw [htop]; trivial
    exact Subgroup.mem_center_iff.mp this a

theorem map_center_eq_inf_centralizer' {A : Type} [Group A] (V : Subgroup A) :
    (Subgroup.center ↥V).map V.subtype = V ⊓ centralizer (V : Set A) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨h, hh⟩
    exact congrArg Subtype.val this
  · rintro ⟨hx, hxc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 hxc) g g.2

section Q8Setting

variable {A : Type} [Group A] [Finite A] {p : ℕ} {V X : Subgroup A} {z : A}

theorem card_Z_eq_two (hC : Core412 V X z) (hV8 : Nat.card ↥V = 8) :
    Nat.card ↥(V ⊓ centralizer (V : Set A)) = 2 := by
  have hnc : ¬ ∀ a b : ↥V, a * b = b * a := by
    intro h
    apply hC.nonab
    intro a ha b hb
    have := h ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have h2 := card_center_eq_two_of_card_eight hV8 hnc
  rw [← map_center_eq_inf_centralizer', Subgroup.card_map_of_injective V.subtype_injective]
  exact h2


omit [Finite A] in
theorem conj_eq_of_mem_Z (hC : Core412 V X z) {x u : A} (hx : x ∈ X)
    (hu : u ∈ V ⊓ centralizer (V : Set A)) : x * u * x⁻¹ = u := by
  have h1 : u * x = x * u := mem_centralizer_iff.mp (hC.X_cent_Z hx) u hu
  calc x * u * x⁻¹ = (u * x) * x⁻¹ := by rw [h1]
    _ = u := by group

theorem exists_quaternion_data (h : Setup412 p V X z) (hV : ⁅V, X⁆ = V) (hne : V ≠ ⊥)
    (hcz : Nat.card ↥(V ⊓ centralizer (V : Set A) ⊓ centralizer ({z} : Set A)) = 2) :
    ∃ (s u v : A), s ≠ 1 ∧ s ∈ V ⊓ centralizer (V : Set A) ∧
      (∀ g ∈ V ⊓ centralizer (V : Set A), g = 1 ∨ g = s) ∧ u ∈ V ∧ v ∈ V ∧ orderOf u = 4 ∧
      orderOf v = 4 ∧ u * v ≠ v * u ∧ Nonempty (↥V ≃* QuaternionGroup 2) := by
  have hC : Core412 V X z := core412_of_setup h hV hne
  have hV8 : Nat.card ↥V = 8 := hC.card8 hcz
  have hZ2 := card_Z_eq_two hC hV8
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs1, hsZ, hZ⟩ : ∃ s : A, s ≠ 1 ∧ s ∈ V ⊓ centralizer (V : Set A) ∧
      ∀ g ∈ V ⊓ centralizer (V : Set A), g = 1 ∨ g = s := by
    obtain ⟨s', hs'1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(V ⊓ centralizer (V : Set A)))).mp hZ2
    refine ⟨(s' : A), fun he => hs'1 (Subtype.ext he), s'.2, fun g hg => ?_⟩
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · refine Or.inr ?_
      have := huniq ⟨g, hg⟩ (fun he => hg1 (congrArg Subtype.val he))
      exact congrArg Subtype.val this
  have hss : s * s = 1 := hC.Z_exp2 s hsZ
  have hsc : ∀ w ∈ V, w * s = s * w := fun w hw => (mem_centralizer_iff.mp hsZ.2 w hw)
  obtain ⟨hfirst, y, hyV, hyy, hzy⟩ := q8_data h hV hne hs1 hsZ hZ
  have hy1 : y ≠ 1 := fun he => hs1 (by rw [← hyy, he, one_mul])
  have hys : y ≠ s := by
    intro he
    apply hs1
    have h1 : y * y = 1 := by rw [he]; exact hss
    rw [← hyy]; exact h1
  obtain ⟨x, hxX, hx1, hxs⟩ : ∃ x ∈ X, ⁅x, y⁆ ≠ 1 ∧ ⁅x, y⁆ ≠ s := by
    by_contra hcon
    push Not at hcon
    rcases hfirst y hyV (fun x hx => by
      by_cases h1 : ⁅x, y⁆ = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)) with he | he
    · exact hy1 he
    · exact hys he
  set v : A := x * y * x⁻¹ with hv
  have hvV : v ∈ V := (mem_normalizer_iff.mp (h.XW hxX) y).mp hyV
  have hxs' : x * s * x⁻¹ = s := conj_eq_of_mem_Z hC hxX hsZ
  have hvv : v * v = s := by
    calc v * v = x * (y * y) * x⁻¹ := by rw [hv]; group
      _ = s := by rw [hyy, hxs']
  have hy4 : orderOf y = 2 * 2 := by
    have h4 : y ^ 4 = 1 := by
      calc y ^ 4 = (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := by rw [hyy, hss]
    have : orderOf y = 2 ^ (1 + 1) := orderOf_eq_prime_pow (p := 2) (n := 1)
      (by rw [pow_one, pow_two, hyy]; exact hs1)
      (by norm_num; exact h4)
    rw [this]; norm_num
  have hv4 : orderOf v = 2 * 2 := by
    have : orderOf v = orderOf y :=
      orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective y
    rw [this, hy4]
  set x' : ↥V := ⟨y, hyV⟩ with hx'
  set y' : ↥V := ⟨v, hvV⟩ with hy'
  have hx'ord : orderOf x' = 2 * 2 := by rw [hx', Subgroup.orderOf_mk]; exact hy4
  have hnot : y' ∉ Subgroup.zpowers x' := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : y ^ k = v := by simpa [hx', hy'] using congrArg Subtype.val hk
    have h1 : y ^ (k + k) = y ^ (2 : ℤ) := by
      rw [zpow_add, hk', hvv, zpow_two, hyy]
    have h2 : y ^ (k + k - 2) = 1 := by
      rw [zpow_sub, h1, mul_inv_cancel]
    have h3 : ((orderOf y : ℕ) : ℤ) ∣ k + k - 2 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hy4] at h3
    obtain ⟨c, hc⟩ := h3
    have hk2 : k = 2 * c + 1 := by push_cast at hc; omega
    have hcomm : ⁅x, y⁆ = s ^ c := by
      have e1 : ⁅x, y⁆ = v * y⁻¹ := by rw [hv, commutatorElement_def]
      rw [e1, ← hk', hk2, zpow_add, zpow_one, mul_inv_cancel_right, zpow_mul, zpow_two, hyy]
    rcases Int.even_or_odd' c with ⟨n, hn | hn⟩
    · apply hx1
      rw [hcomm, hn, zpow_mul, zpow_two, hss, one_zpow]
    · apply hxs
      rw [hcomm, hn, zpow_add, zpow_mul, zpow_two, hss, one_zpow, one_mul, zpow_one]
  have hgen : Subgroup.closure ({x', y'} : Set ↥V) = ⊤ := by
    set K := Subgroup.closure ({x', y'} : Set ↥V) with hK
    have hxK : Subgroup.zpowers x' ≤ K :=
      (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (by simp))
    have hyK : y' ∈ K := Subgroup.subset_closure (by simp)
    have hcard4 : Nat.card (Subgroup.zpowers x') = 4 := by rw [Nat.card_zpowers, hx'ord]
    have hgt : 4 < Nat.card K := by
      by_contra hle
      push Not at hle
      have := Subgroup.eq_of_le_of_card_ge hxK (by rw [hcard4]; exact hle)
      exact hnot (this ▸ hyK)
    have hdvd : Nat.card K ∣ Nat.card ↥V := Subgroup.card_subgroup_dvd_card K
    rw [hV8] at hdvd
    have hle8 : Nat.card K ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    have h8 : Nat.card K = 8 := by
      interval_cases (Nat.card K) <;> omega
    exact Subgroup.eq_top_of_card_eq K (by rw [h8, hV8])
  have hnc : x' * y' ≠ y' * x' := by
    intro hcomm
    have hpair : ({x', y'} : Set ↥V).Pairwise Commute := by
      intro a ha b hb hab
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact hcomm
      · exact hcomm.symm
      · exact absurd rfl hab
    have := Subgroup.isMulCommutative_closure hpair
    apply hC.nonab
    intro a ha b hb
    have hmem : ∀ c : ↥V, c ∈ Subgroup.closure ({x', y'} : Set ↥V) := by
      intro c; rw [hgen]; trivial
    have h1 := (inferInstance : IsMulCommutative ↥(Subgroup.closure ({x', y'} : Set ↥V))).is_comm.comm
      ⟨⟨a, ha⟩, hmem _⟩ ⟨⟨b, hb⟩, hmem _⟩
    have h2 := congrArg (fun t : ↥(Subgroup.closure ({x', y'} : Set ↥V)) => ((t : ↥V) : A)) h1
    simpa using h2
  have hyv : y * v ≠ v * y := fun he => hnc (Subtype.ext (by simpa [hx', hy'] using he))
  have hcomm_mem : v * y * v⁻¹ * y⁻¹ ∈ V ⊓ centralizer (V : Set A) := by
    rw [hC.Z_eq_derived]
    have : ⁅v, y⁆ ∈ ⁅V, V⁆ := Subgroup.commutator_mem_commutator hvV hyV
    simpa [commutatorElement_def] using this
  have hcs : v * y * v⁻¹ * y⁻¹ = s := by
    rcases hZ _ hcomm_mem with he | he
    · exfalso
      apply hyv
      have h1 : v * y * v⁻¹ = y := by
        calc v * y * v⁻¹ = (v * y * v⁻¹ * y⁻¹) * y := by group
          _ = y := by rw [he, one_mul]
      calc y * v = (v * y * v⁻¹) * v := by rw [h1]
        _ = v * y := by group
    · exact he
  have hyinv : s * y = y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hyy, hss])
  have hyx_A : v * y * v⁻¹ = y⁻¹ := by
    calc v * y * v⁻¹ = (v * y * v⁻¹ * y⁻¹) * y := by group
      _ = s * y := by rw [hcs]
      _ = y⁻¹ := hyinv
  have hyx : y' * x' * y'⁻¹ = x'⁻¹ := Subtype.ext (by simpa [hx', hy'] using hyx_A)
  have hy2 : y' ^ 2 = x' ^ 2 := Subtype.ext (by simp [hx', hy', pow_two, hvv, hyy])
  obtain ⟨⟨e, -⟩, -⟩ := CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism (m := 2)
    (by norm_num) hgen hx'ord hnot hy2 hyx
  exact ⟨s, y, v, hs1, hsZ, hZ, hyV, hvV, by rw [hy4], by rw [hv4], hyv, ⟨e.symm⟩⟩

end Q8Setting

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
