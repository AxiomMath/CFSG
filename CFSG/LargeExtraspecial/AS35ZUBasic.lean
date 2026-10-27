module

public import CFSG.LargeExtraspecial.AS35LMain
public import CFSG.LargeExtraspecial.AS35ZUFive

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Fischer.Classification.Unitary

namespace AS35Z

variable {L : Type} [Group L] {D : Set L} {k : ℕ}

theorem mem_DG_of_le_four (hk : 2 ≤ k) (ψ : L ⧸ center L ≃* PG (k + 2))
    (hinv : ∀ d ∈ D, d * d = 1) (hconj : ∀ g : L, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hfour : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ))
    {d : L} (hd : d ∈ D) (hdZ : d ∉ center L) : ψ (QuotientGroup.mk d) ∈ DG (k + 2) := by
  set f : L →* PG (k + 2) := ψ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hf
  have hfx : ∀ x, f x = ψ (QuotientGroup.mk x) := fun _ => rfl
  refine mem_DG_of_orderOf_mul_conj_le_four (by omega) ?_ fun c => ?_
  · refine orderOf_eq_prime ?_ fun h1 => hdZ ?_
    · rw [sq, ← hfx, ← map_mul, hinv d hd, map_one]
    · rw [← QuotientGroup.eq_one_iff]
      exact ψ.injective (by rw [h1, map_one])
  · obtain ⟨g, rfl⟩ := AS35L.exists_mk_eq ψ c
    rw [show ψ (QuotientGroup.mk d) * (ψ (QuotientGroup.mk g) * ψ (QuotientGroup.mk d) *
        (ψ (QuotientGroup.mk g))⁻¹) = f (d * (g * d * g⁻¹)) by
      rw [map_mul, map_mul, map_mul, map_inv]; rfl]
    have hdvd := orderOf_map_dvd f (d * (g * d * g⁻¹))
    have h4 := hfour d hd _ (hconj g d hd)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h4 ⊢
    have hm0 : 0 < orderOf (d * (g * d * g⁻¹)) := by omega
    have hpos := Nat.pos_of_dvd_of_pos hdvd hm0
    have hle := Nat.le_of_dvd hm0 hdvd
    omega

theorem three_of_le_four (ψ : L ⧸ center L ≃* PG (k + 2))
    (hDG : ∀ d ∈ D, ψ (QuotientGroup.mk d) ∈ DG (k + 2))
    (hfour : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ))
    (hZ : ∀ u ∈ center L, u * u = 1 → u = 1) {a b : L} (ha : a ∈ D) (hb : b ∈ D) :
    orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ) := by
  set f : L →* PG (k + 2) := ψ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hf
  obtain ⟨v, -, hv, hva⟩ := hDG a ha
  obtain ⟨w, -, hw, hwb⟩ := hDG b hb
  have h3 : orderOf (f (a * b)) ∈ ({1, 2, 3} : Set ℕ) := by
    rw [map_mul]
    change orderOf (ψ (QuotientGroup.mk a) * ψ (QuotientGroup.mk b)) ∈ _
    rw [← hva, ← hwb]
    exact orderOf_tq_mul_tq_mem hv hw
  have h4 := hfour a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3 h4 ⊢
  rcases h4 with h4 | h4 | h4 | h4
  · exact Or.inl h4
  · exact Or.inr (Or.inl h4)
  · exact Or.inr (Or.inr h4)
  · exfalso
    have hdvd : orderOf (f (a * b)) ∣ 4 := h4 ▸ orderOf_map_dvd f (a * b)
    have h2 : f ((a * b) ^ 2) = 1 := by
      rw [map_pow]
      rcases h3 with h3 | h3 | h3
      · rw [orderOf_eq_one_iff.1 h3, one_pow]
      · have := pow_orderOf_eq_one (f (a * b))
        rwa [h3] at this
      · rw [h3] at hdvd
        norm_num at hdvd
    have hcen : (a * b) ^ 2 ∈ center L := by
      rw [← QuotientGroup.eq_one_iff]
      exact ψ.injective (by rw [map_one]; exact h2)
    have hu := hZ _ hcen (by
      rw [← pow_add, show 2 + 2 = orderOf (a * b) from h4.symm, pow_orderOf_eq_one])
    have h22 := orderOf_dvd_of_pow_eq_one hu
    rw [h4] at h22
    norm_num at h22

end AS35Z

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

abbrev DbarL : Set (closure S.DbarAsc) := Subtype.val ⁻¹' S.DbarAsc

structure ZUHyp (k : ℕ) : Prop where
  two_le : 2 ≤ k
  width_eq : S.width = k + 2
  weak : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  sixFour : S.SixFourConcl
  normal : ∀ m ∈ S.Mbar, ∀ x ∈ closure S.DbarAsc, m * x * m⁻¹ ∈ closure S.DbarAsc
  cls : ∀ a ∈ S.DbarAsc, ∀ b ∈ S.DbarAsc, ∃ g ∈ closure S.DbarAsc, g * a * g⁻¹ = b
  psu : Nonempty (closure S.DbarAsc ⧸ center (closure S.DbarAsc) ≃* PG (k + 2))

namespace ZUHyp

variable {S} {k : ℕ} (h : S.ZUHyp k)
include h

omit h in
theorem sub : S.DbarAsc ⊆ S.Mbar := by
  rintro _ ⟨t, -, htM, rfl⟩
  exact ⟨⟨t, htM⟩, rfl⟩

omit h in
theorem closure_le : closure S.DbarAsc ≤ S.Mbar := (Subgroup.closure_le _).2 sub

theorem isTypeA {d : S.O} (hd : d ∈ S.DbarAsc) :
    IsTypeA S.q (d : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact (S.fiveOne_two h.sixFour h.weak ht htM).1

omit h in
theorem mul_self {d : S.O} (hd : d ∈ S.DbarAsc) : d * d = 1 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))

omit h in
theorem conj_mem {m : S.O} (hm : m ∈ S.Mbar) {d : S.O} (hd : d ∈ S.DbarAsc) :
    m * d * m⁻¹ ∈ S.DbarAsc :=
  S.conj_mem_DbarAsc_L hm hd

theorem eq_one_of_central {u : S.O} (hu : u ∈ closure S.DbarAsc)
    (hc : ∀ x ∈ closure S.DbarAsc, u * x = x * u) {j : ℕ} (hj : u ^ 2 ^ j = 1) : u = 1 := by
  set L := closure S.DbarAsc with hL
  set N : Subgroup S.O :=
    { carrier := {v | v ∈ L ∧ (∀ x ∈ L, v * x = x * v) ∧ ∃ i : ℕ, v ^ 2 ^ i = 1}
      mul_mem' := by
        rintro a b ⟨haL, hac, i, hi⟩ ⟨hbL, hbc, i', hi'⟩
        refine ⟨L.mul_mem haL hbL, fun x hx => ?_, i + i', ?_⟩
        · rw [mul_assoc, hbc x hx, ← mul_assoc, hac x hx, mul_assoc]
        · rw [(Commute.mul_pow (hac b hbL) _), pow_add, pow_mul, hi, one_pow, one_mul,
            mul_comm (2 ^ i), pow_mul, hi', one_pow]
      one_mem' := ⟨L.one_mem, fun x _ => by rw [one_mul, mul_one], 0, by rw [one_pow]⟩
      inv_mem' := by
        rintro a ⟨haL, hac, i, hi⟩
        refine ⟨L.inv_mem haL, fun x hx => ?_, i, by rw [inv_pow, hi, inv_one]⟩
        have := hac x hx
        calc a⁻¹ * x = a⁻¹ * (x * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * x) * a⁻¹ := by rw [this]
          _ = x * a⁻¹ := by group } with hN
  have hNM : N ≤ S.Mbar := fun v hv => closure_le hv.1
  have hN2 : IsPGroup 2 N := by
    rintro ⟨v, -, -, i, hi⟩
    exact ⟨i, Subtype.ext hi⟩
  have hnorm : S.Mbar ≤ normalizer (N : Set S.O) := by
    have key : ∀ m ∈ S.Mbar, ∀ v ∈ N, m * v * m⁻¹ ∈ N := by
      rintro m hm v ⟨hvL, hvc, i, hi⟩
      refine ⟨h.normal m hm v hvL, fun x hx => ?_, i, ?_⟩
      · have hx' : m⁻¹ * x * m ∈ L := by
          have := h.normal m⁻¹ (S.Mbar.inv_mem hm) x hx
          rwa [inv_inv] at this
        have e := hvc _ hx'
        calc m * v * m⁻¹ * x = m * (v * (m⁻¹ * x * m)) * m⁻¹ := by group
          _ = m * ((m⁻¹ * x * m) * v) * m⁻¹ := by rw [e]
          _ = x * (m * v * m⁻¹) := by group
      · rw [conj_pow, hi, mul_one, mul_inv_cancel]
    intro m hm
    rw [mem_normalizer_iff]
    intro v
    refine ⟨key m hm v, fun hv => ?_⟩
    have := key m⁻¹ (S.Mbar.inv_mem hm) _ hv
    rwa [inv_inv, show m⁻¹ * (m * v * m⁻¹) * m = v by group] at this
  have hbot := S.eq_bot_of_normalized_L hNM hnorm hN2
  have huN : u ∈ N := ⟨hu, hc, j, hj⟩
  rw [hbot] at huN
  exact huN

omit h in
theorem mem_center_iff' {x : closure S.DbarAsc} :
    x ∈ center (closure S.DbarAsc) ↔ ∀ y ∈ closure S.DbarAsc, (x : S.O) * y = y * x := by
  rw [mem_center_iff]
  constructor
  · intro hx y hy
    exact congrArg Subtype.val (hx ⟨y, hy⟩).symm
  · intro hx y
    exact Subtype.ext (hx y y.2).symm

theorem orderOf_mul_mem_le_four {a b : S.O} (ha : a ∈ S.DbarAsc) (hb : b ∈ S.DbarAsc) :
    orderOf (a * b) ∈ ({1, 2, 3, 4} : Finset ℕ) ∧
      (orderOf (a * b) = 4 →
        IsTypeA S.q (((a * b) ^ 2 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) := by
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have h37 := aschbacher_3_7 S.q_nondegenerate (h.isTypeA ha) (h.isTypeA hb)
  rw [← Subgroup.coe_mul, Subgroup.orderOf_coe] at h37
  refine ⟨h37.1, fun h4 => ?_⟩
  have := h37.2 h4
  rwa [← Subgroup.coe_pow] at this

abbrev mkL {d : S.O} (hd : d ∈ S.DbarAsc) : closure S.DbarAsc := ⟨d, subset_closure hd⟩

theorem center_inv {u : closure S.DbarAsc} (hu : u ∈ center (closure S.DbarAsc))
    (huu : u * u = 1) : u = 1 :=
  Subtype.ext (h.eq_one_of_central u.2 (mem_center_iff'.1 hu) (j := 1)
    (by rw [pow_one, sq]; exact congrArg Subtype.val huu))

theorem not_mem_center {d : closure S.DbarAsc} (hd : d ∈ S.DbarL) :
    d ∉ center (closure S.DbarAsc) := fun hZ =>
  (h.isTypeA hd).2.1 (by
    rw [h.center_inv hZ (Subtype.ext (mul_self hd))]
    rfl)

theorem four_L {a b : closure S.DbarAsc} (ha : a ∈ S.DbarL) (hb : b ∈ S.DbarL) :
    orderOf (a * b) ∈ ({1, 2, 3, 4} : Set ℕ) := by
  have h4 := (h.orderOf_mul_mem_le_four ha hb).1
  rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  simpa using h4

theorem mem_DG (ψ : closure S.DbarAsc ⧸ center (closure S.DbarAsc) ≃* PG (k + 2))
    {d : closure S.DbarAsc} (hd : d ∈ S.DbarL) : ψ (QuotientGroup.mk d) ∈ DG (k + 2) :=
  AS35Z.mem_DG_of_le_four h.two_le ψ (fun _ hd => Subtype.ext (mul_self hd))
    (fun g _ hd => conj_mem (closure_le g.2) hd) (fun _ ha _ hb => h.four_L ha hb) hd
    (h.not_mem_center hd)

theorem three {a b : S.O} (ha : a ∈ S.DbarAsc) (hb : b ∈ S.DbarAsc) :
    orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨ψ⟩ := h.psu
  have := AS35Z.three_of_le_four ψ (fun d hd => h.mem_DG ψ hd)
    (fun _ ha _ hb => h.four_L ha hb) (fun u hu huu => h.center_inv hu huu)
    (a := mkL ha) (b := mkL hb) ha hb
  rwa [← Subgroup.orderOf_coe, Subgroup.coe_mul] at this

theorem hyp : AS35L.Hyp S.Mbar S.DbarAsc k where
  finite := inferInstance
  two_le := h.two_le
  sub := sub
  conj _ hm _ hd := conj_mem hm hd
  cls := h.cls
  inv _ hd := mul_self hd
  three _ ha _ hb := h.three ha hb
  psu := h.psu
  core _ hNM hN h2 := S.eq_bot_of_normalized_L hNM hN h2

end ZUHyp

end Setting

end CFSG.LargeExtraspecial
