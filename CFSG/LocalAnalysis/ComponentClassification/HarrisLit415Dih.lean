module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open Subgroup DihedralGroup

namespace L415

variable {G : Type*} [Group G] {D : Subgroup G}

theorem comm_of_r_double {n : ℕ} (e : ↥D ≃* DihedralGroup n) {j : ZMod n} (hj : j + j = 0)
    (d : ↥D) : e.symm (r j) * d = d * e.symm (r j) := by
  apply e.injective
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
  rcases e d with i | i
  · rw [r_mul_r, r_mul_r, add_comm]
  · rw [r_mul_sr, sr_mul_r]
    congr 1
    linear_combination -hj

theorem symm_r_eq_pow {m : ℕ} (e : ↥D ≃* DihedralGroup (2 ^ m)) (i : ZMod (2 ^ m)) :
    e.symm (r i) = e.symm (r 1) ^ i.val := by
  rw [← map_pow, r_one_pow, ZMod.natCast_zmod_val]

theorem exists_involution_not_mem [Finite G] {m : ℕ} (e : ↥D ≃* DihedralGroup (2 ^ m))
    {Ds : Subgroup G} (hDs : Ds ≤ D) (hcard : 2 * Nat.card Ds = Nat.card D)
    (hnab : ∃ a ∈ Ds, ∃ b ∈ Ds, a * b ≠ b * a)
    (hZ : ∀ c ∈ D, (∀ d ∈ D, c * d = d * c) → c ∈ Ds) :
    ∃ x ∈ D, x ∉ Ds ∧ x * x = 1 ∧ ∀ d ∈ Ds, d * x = x * d → ∀ d' ∈ D, d * d' = d' * d := by
  set ρ : ↥D := e.symm (r 1) with hρ
  obtain ⟨σ, hσ, i, hσi⟩ : ∃ σ, ∃ hσ : σ ∈ Ds, ∃ i, e ⟨σ, hDs hσ⟩ = sr i := by
    by_contra hno
    push Not at hno
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    apply hab
    have h1 : ∀ c (hc : c ∈ Ds), ∃ j, e ⟨c, hDs hc⟩ = r j := by
      intro c hc
      rcases h : e ⟨c, hDs hc⟩ with j | j
      · exact ⟨j, rfl⟩
      · exact absurd h (hno c hc j)
    obtain ⟨j, hj⟩ := h1 a ha
    obtain ⟨k, hk⟩ := h1 b hb
    have h2 : (⟨a, hDs ha⟩ : ↥D) * ⟨b, hDs hb⟩ = ⟨b, hDs hb⟩ * ⟨a, hDs ha⟩ := by
      apply e.injective
      rw [map_mul, map_mul, hj, hk, r_mul_r, r_mul_r, add_comm]
    exact congrArg Subtype.val h2
  have hρDs : (ρ : G) ∉ Ds := by
    intro hρ'
    have hDle : D ≤ Ds := by
      intro d hd
      have hpow : ∀ j : ZMod (2 ^ m), ((e.symm (r j) : ↥D) : G) ∈ Ds := by
        intro j
        rw [symm_r_eq_pow, Subgroup.coe_pow]
        exact pow_mem hρ' _
      rcases h : e ⟨d, hd⟩ with j | j
      · have : (⟨d, hd⟩ : ↥D) = e.symm (r j) := by rw [← h, MulEquiv.symm_apply_apply]
        rw [show d = ((⟨d, hd⟩ : ↥D) : G) from rfl, this]
        exact hpow j
      · have : (⟨d, hd⟩ : ↥D) = ⟨σ, hDs hσ⟩ * e.symm (r (j - i)) := by
          apply e.injective
          rw [map_mul, MulEquiv.apply_symm_apply, h, hσi, sr_mul_r]
          congr 1
          ring
        rw [show d = ((⟨d, hd⟩ : ↥D) : G) from rfl, this, Subgroup.coe_mul]
        exact mul_mem hσ (hpow _)
    have h1 := Subgroup.card_le_of_le hDle
    have h2 : 0 < Nat.card Ds := Nat.card_pos
    omega
  obtain ⟨x, hx⟩ : ∃ x : ↥D, x = ⟨σ, hDs hσ⟩ * ρ := ⟨_, rfl⟩
  have hex : e x = sr (i + 1) := by rw [hx, map_mul, hσi, hρ, MulEquiv.apply_symm_apply, sr_mul_r]
  refine ⟨x, x.2, fun hxDs => hρDs ?_, ?_, fun d hd hdx d' hd' => ?_⟩
  · have : (ρ : G) = σ⁻¹ * x := by rw [hx, Subgroup.coe_mul]; group
    rw [this]
    exact mul_mem (inv_mem hσ) hxDs
  · have : x * x = 1 := by
      apply e.injective
      rw [map_mul, hex, sr_mul_self, map_one]
    exact congrArg Subtype.val this
  · have hdx' : (⟨d, hDs hd⟩ : ↥D) * x = x * ⟨d, hDs hd⟩ := Subtype.ext hdx
    rcases h : e ⟨d, hDs hd⟩ with j | j
    ·
      have h1 := congrArg e hdx'
      rw [map_mul, map_mul, h, hex, r_mul_sr, sr_mul_r, sr.injEq] at h1
      have hj : j + j = 0 := by linear_combination -h1
      have h2 := comm_of_r_double e hj ⟨d', hd'⟩
      have h3 : (⟨d, hDs hd⟩ : ↥D) = e.symm (r j) := by rw [← h, MulEquiv.symm_apply_apply]
      rw [← h3] at h2
      exact congrArg Subtype.val h2
    ·
      exfalso
      have h1 := congrArg e hdx'
      rw [map_mul, map_mul, h, hex, sr_mul_sr, sr_mul_sr, r.injEq] at h1
      set k : ZMod (2 ^ m) := i + 1 - j with hk
      have hkk : k + k = 0 := by rw [hk]; linear_combination h1
      have hcZ : ((e.symm (r k) : ↥D) : G) ∈ Ds :=
        hZ _ (e.symm (r k)).2 fun d'' hd'' =>
          congrArg Subtype.val (comm_of_r_double e hkk ⟨d'', hd''⟩)
      have h2 : (⟨d, hDs hd⟩ : ↥D) = x * (e.symm (r k))⁻¹ := by
        apply e.injective
        rw [map_mul, map_inv, MulEquiv.apply_symm_apply, h, hex, inv_r, sr_mul_r]
        congr 1
        rw [hk]
        ring
      have h3 : (x : G) = d * (e.symm (r k) : ↥D) := by
        have := congrArg Subtype.val h2
        rw [Subgroup.coe_mul, Subgroup.coe_inv] at this
        rw [show (d : G) = ((⟨d, hDs hd⟩ : ↥D) : G) from rfl, this]
        group
      apply hρDs
      have : (ρ : G) = σ⁻¹ * x := by rw [hx, Subgroup.coe_mul]; group
      rw [this, h3]
      exact mul_mem (inv_mem hσ) (mul_mem hd hcZ)

theorem exists_commutator_eq_pow [Finite G] {m : ℕ} (e : ↥D ≃* DihedralGroup (2 ^ m))
    (hm : 2 ≤ m) {x : G} (hx2 : x * x = 1) (hxD : ∀ d ∈ D, x * d * x⁻¹ ∈ D) {z : G}
    (hC : ∀ d ∈ D, d * x = x * d → d = 1 ∨ d = z) (k : ℕ) :
    ∃ d ∈ D, d * x * d⁻¹ * x⁻¹ = ((e.symm (r 1) : ↥D) : G) ^ k := by
  classical
  have : Fintype ↥D := Fintype.ofFinite _
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  let φ : ↥D → ↥D := fun d => ⟨x * d * x⁻¹, hxD d d.2⟩
  have hφφ : ∀ d, φ (φ d) = d := fun d => Subtype.ext (by
    show x * (x * (d : G) * x⁻¹) * x⁻¹ = d
    rw [hxi, show x * (x * (d : G) * x) * x = (x * x) * d * (x * x) by group, hx2]
    group)
  have hφmul : ∀ a b, φ (a * b) = φ a * φ b := fun a b => Subtype.ext (by
    show x * ((a : G) * b) * x⁻¹ = x * a * x⁻¹ * (x * b * x⁻¹)
    group)
  have hφpow : ∀ (a : ↥D) (n : ℕ), φ (a ^ n) = φ a ^ n := by
    intro a n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact Subtype.ext (by show x * 1 * x⁻¹ = 1; group)
    | succ n ih => rw [pow_succ, hφmul, ih, pow_succ]
  have hrot : ∀ d : ↥D, (∃ j, e d = r j) → ∃ j, e (φ d) = r j := by
    have hρ : ∃ j, e (φ (e.symm (r 1))) = r j := by
      rcases h : e (φ (e.symm (r 1))) with j | j
      · exact ⟨j, rfl⟩
      · exfalso
        have h1 : orderOf (φ (e.symm (r 1))) = orderOf (e.symm (r 1) : ↥D) := by
          have := MulEquiv.orderOf_eq (MulAut.conj x) ((e.symm (r 1) : ↥D) : G)
          simp only [MulAut.conj_apply] at this
          rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
          exact this
        rw [← MulEquiv.orderOf_eq e, h, orderOf_sr, ← MulEquiv.orderOf_eq e,
          MulEquiv.apply_symm_apply, orderOf_r_one] at h1
        omega
    rintro d ⟨j, hj⟩
    obtain ⟨j₀, hj₀⟩ := hρ
    have hd : d = e.symm (r 1) ^ j.val := by rw [← symm_r_eq_pow, ← hj, MulEquiv.symm_apply_apply]
    refine ⟨j₀ * j.val, ?_⟩
    rw [hd, hφpow, map_pow, hj₀]
    induction j.val with
    | zero => rw [pow_zero, Nat.cast_zero, mul_zero, one_def]
    | succ n ih => rw [pow_succ, ih, r_mul_r, Nat.cast_succ]; ring_nf
  have hrefl : ∀ d : ↥D, (∃ j, e d = sr j) → ∃ j, e (φ d) = sr j := by
    rintro d ⟨j, hj⟩
    rcases h : e (φ d) with j' | j'
    · exfalso
      obtain ⟨j'', hj''⟩ := hrot (φ d) ⟨j', h⟩
      rw [hφφ, hj] at hj''
      exact absurd hj'' (by intro h; cases h)
    · exact ⟨j', rfl⟩
  let f : ↥D → ↥D := fun d => d * φ d⁻¹
  have hf : ∀ d : ↥D, ((f d : ↥D) : G) = (d : G) * x * (d : G)⁻¹ * x⁻¹ := fun d => by
    show (d : G) * (x * (d⁻¹ : ↥D) * x⁻¹) = d * x * d⁻¹ * x⁻¹
    rw [Subgroup.coe_inv]
    group
  have hfrot : ∀ d, ∃ j, e (f d) = r j := by
    intro d
    rcases h : e d with j | j
    · obtain ⟨j', hj'⟩ := hrot d⁻¹ ⟨-j, by rw [map_inv, h, inv_r]⟩
      exact ⟨j + j', by rw [map_mul, h, hj', r_mul_r]⟩
    · obtain ⟨j', hj'⟩ := hrefl d⁻¹ ⟨j, by rw [map_inv, h, inv_sr]⟩
      exact ⟨j' - j, by rw [map_mul, h, hj', sr_mul_sr]⟩
  set R : Subgroup ↥D := (zpowers (r 1 : DihedralGroup (2 ^ m))).map e.symm.toMonoidHom with hR
  have hmemR : ∀ d : ↥D, d ∈ R ↔ ∃ j, e d = r j := by
    intro d
    rw [hR, Subgroup.mem_map_equiv, MulEquiv.symm_symm, mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, r_one_zpow]⟩
    · rintro ⟨j, hj⟩
      exact ⟨j.val, by rw [hj, zpow_natCast, r_one_pow, ZMod.natCast_zmod_val]⟩
  have hcardR : Nat.card R = 2 ^ m := by
    rw [hR, Subgroup.card_map_of_injective e.symm.injective, Nat.card_zpowers, orderOf_r_one]
  have hfib : ∀ b ∈ (Finset.univ : Finset ↥D).image f,
      ((Finset.univ : Finset ↥D).filter fun a => f a = b).card ≤ 2 := by
    intro b hb
    obtain ⟨a₀, -, ha₀⟩ := Finset.mem_image.mp hb
    have hsub : Set.MapsTo (fun a : ↥D => (a : G)) ↑((Finset.univ : Finset ↥D).filter
        fun a => f a = b) ↑({(a₀ : G), a₀ * z} : Finset G) := by
      intro a ha
      have ha' : f a = f a₀ := by
        rw [ha₀]
        exact (Finset.mem_filter.mp ha).2
      have h1 : ((f a : ↥D) : G) = f a₀ := by rw [ha']
      rw [hf, hf] at h1
      have h2 : ((a₀ : G)⁻¹ * a) * x = x * ((a₀ : G)⁻¹ * a) := by
        have h3 : (a : G) * x * (a : G)⁻¹ = a₀ * x * (a₀ : G)⁻¹ := by
          calc (a : G) * x * (a : G)⁻¹ = (a * x * (a : G)⁻¹ * x⁻¹) * x := by group
            _ = (a₀ * x * (a₀ : G)⁻¹ * x⁻¹) * x := by rw [h1]
            _ = a₀ * x * (a₀ : G)⁻¹ := by group
        calc ((a₀ : G)⁻¹ * a) * x = (a₀ : G)⁻¹ * (a * x * (a : G)⁻¹) * a := by group
          _ = (a₀ : G)⁻¹ * (a₀ * x * (a₀ : G)⁻¹) * a := by rw [h3]
          _ = x * ((a₀ : G)⁻¹ * a) := by group
      rcases hC _ (mul_mem (inv_mem a₀.2) a.2) h2 with h4 | h4
      · have : (a : G) = a₀ := by
          calc (a : G) = a₀ * ((a₀ : G)⁻¹ * a) := by group
            _ = a₀ := by rw [h4, mul_one]
        simp [this]
      · have : (a : G) = a₀ * z := by
          calc (a : G) = a₀ * ((a₀ : G)⁻¹ * a) := by group
            _ = a₀ * z := by rw [h4]
        simp [this]
    exact (Finset.card_le_card_of_injOn _ hsub (fun a _ b _ hab => Subtype.ext hab)).trans
      Finset.card_le_two
  have h1 := Finset.card_le_mul_card_image (Finset.univ : Finset ↥D) 2 hfib
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_congr e.toEquiv,
    DihedralGroup.nat_card] at h1
  have hsubR : (Finset.univ : Finset ↥D).image f ⊆ (R : Set ↥D).toFinset := by
    intro a ha
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp ha
    rw [Set.mem_toFinset, SetLike.mem_coe, hmemR]
    exact hfrot d
  have hcardR' : ((R : Set ↥D).toFinset).card = 2 ^ m := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, ← hcardR]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsubR (by omega)
  have hmem : e.symm (r 1) ^ k ∈ (R : Set ↥D).toFinset := by
    rw [Set.mem_toFinset, SetLike.mem_coe, hmemR]
    exact ⟨k, by rw [map_pow, MulEquiv.apply_symm_apply, r_one_pow]⟩
  rw [← heq] at hmem
  obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hmem
  refine ⟨d, d.2, ?_⟩
  rw [← hf, hd, Subgroup.coe_pow]

end L415

end CFSG.ComponentClassification.HarrisLit
