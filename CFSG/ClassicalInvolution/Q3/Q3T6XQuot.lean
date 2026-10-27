module

public import CFSG.ClassicalInvolution.Uniform.U4Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Uniform.U4

section Defs

variable {F : Type} [Group F] [Finite F]

abbrev Cz (z : F) : Subgroup F := Subgroup.centralizer ({z} : Set F)

abbrev Qz (z : F) : Type := ↥(Cz z) ⧸ classicalInvolutionOddCore ↥(Cz z)

omit [Finite F] in
theorem self_mem_Cz (z : F) : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.mpr rfl

@[expose] def piz (z : F) : ↥(Cz z) →* Qz z := QuotientGroup.mk' _

@[expose] def zb (z : F) : Qz z := piz z ⟨z, self_mem_Cz z⟩

@[expose] def imgz (z : F) (K : Subgroup F) : Subgroup (Qz z) := (K.subgroupOf (Cz z)).map (piz z)

theorem piz_surjective (z : F) : Function.Surjective (piz z) := QuotientGroup.mk'_surjective _

theorem piz_eq_iff (z : F) {a b : ↥(Cz z)} :
    piz z a = piz z b ↔ a⁻¹ * b ∈ classicalInvolutionOddCore ↥(Cz z) :=
  QuotientGroup.eq

theorem piz_eq_one_iff (z : F) {a : ↥(Cz z)} :
    piz z a = 1 ↔ a ∈ classicalInvolutionOddCore ↥(Cz z) :=
  QuotientGroup.eq_one_iff a

theorem mem_imgz_iff (z : F) {K : Subgroup F} {x : Qz z} :
    x ∈ imgz z K ↔ ∃ (k : F) (hC : k ∈ Cz z), k ∈ K ∧ piz z ⟨k, hC⟩ = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, y.2, hy, rfl⟩
  · rintro ⟨k, hC, hk, rfl⟩
    exact ⟨⟨k, hC⟩, hk, rfl⟩

theorem piz_mem_imgz {z : F} {K : Subgroup F} {k : F} (hC : k ∈ Cz z) (hk : k ∈ K) :
    piz z ⟨k, hC⟩ ∈ imgz z K :=
  (mem_imgz_iff z).mpr ⟨k, hC, hk, rfl⟩

theorem imgz_mono (z : F) {K L : Subgroup F} (h : K ≤ L) : imgz z K ≤ imgz z L := by
  intro x hx
  obtain ⟨k, hC, hk, rfl⟩ := (mem_imgz_iff z).mp hx
  exact piz_mem_imgz hC (h hk)

theorem zb_mul_self (z : F) (hz : z * z = 1) : zb z * zb z = 1 := by
  unfold zb
  rw [← map_mul]
  have : (⟨z, self_mem_Cz z⟩ * ⟨z, self_mem_Cz z⟩ : ↥(Cz z)) = 1 := Subtype.ext hz
  rw [this, map_one]

end Defs

section Odd

variable {F : Type} [Group F] [Finite F]

theorem oddCore_Qz_eq_bot (z : F) : componentClassificationOddCore (Qz z) = ⊥ :=
  CFSG.ComponentClassification.OddCore.quotient_corefree (↥(Cz z))

theorem oddCoreIn_top_Qz (z : F) : Balance.oddCoreIn (⊤ : Subgroup (Qz z)) = ⊥ := by
  have h := CFSG.ComponentClassification.OddCore.equiv_invariant (Subgroup.topEquiv (G := Qz z))
  rw [oddCore_Qz_eq_bot] at h
  exact h

theorem centralizer_zb (z : F) : Subgroup.centralizer ({zb z} : Set (Qz z)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [Subgroup.mem_centralizer_singleton_iff]
    show piz z g * piz z ⟨z, self_mem_Cz z⟩ = piz z ⟨z, self_mem_Cz z⟩ * piz z g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

theorem exAt_zb (z : F) :
    Balance.oddCoreIn (Subgroup.centralizer ({zb z} : Set (Qz z))) = ⊥ := by
  rw [centralizer_zb]
  exact oddCoreIn_top_Qz z

theorem Mem3.imgz {K : Subgroup F} {z : F} (h : Mem3 K z) : Mem3 (imgz z K) (zb z) where
  member := (h.member.subgroupOf h.le_centralizer).map_oddQuotient
  intrinsic := by
    intro _
    rw [centralizer_zb, oddCoreIn_top_Qz]
    exact bot_le

end Odd

section Conj

variable {F : Type} [Group F] [Finite F]

theorem mem_imgz_iff' (z : F) {K : Subgroup F} {x : Qz z} :
    x ∈ imgz z K ↔ ∃ w : ↥(Cz z), (w : F) ∈ K ∧ piz z w = x :=
  Iff.rfl

theorem mem_oddCoreOf_Cz_iff (z : F) {c : F} :
    c ∈ oddCoreOf (Cz z) ↔ ∃ hc : c ∈ Cz z, piz z ⟨c, hc⟩ = 1 := by
  rw [mem_oddCoreOf_iff]
  refine exists_congr fun hc => ?_
  exact (piz_eq_one_iff z).symm

theorem imgz_conjSub (z : F) (K : Subgroup F) (a : ↥(Cz z)) :
    conjSub (piz z a) (imgz z K) = imgz z (conjSub (a : F) K) := by
  ext x
  obtain ⟨y, rfl⟩ := piz_surjective z x
  rw [mem_conjSub_iff, mem_imgz_iff', mem_imgz_iff']
  constructor
  · rintro ⟨w, hw, hwy⟩
    refine ⟨a * w * a⁻¹, ?_, ?_⟩
    · have := conj_mem_conjSub (n := (a : F)) hw
      simpa using this
    · rw [map_mul, map_mul, map_inv, hwy]
      group
  · rintro ⟨w, hw, hwy⟩
    refine ⟨a⁻¹ * w * a, ?_, ?_⟩
    · have := mem_conjSub_iff.mp hw
      simpa using this
    · rw [map_mul, map_mul, map_inv, hwy]

theorem oddCoreOf_Cz_conj (z : F) (a : ↥(Cz z)) {o : F} (ho : o ∈ oddCoreOf (Cz z)) :
    a * o * (a : F)⁻¹ ∈ oddCoreOf (Cz z) := by
  obtain ⟨hC, h1⟩ := (mem_oddCoreOf_Cz_iff z).mp ho
  refine (mem_oddCoreOf_Cz_iff z).mpr ⟨(Cz z).mul_mem ((Cz z).mul_mem a.2 hC)
    ((Cz z).inv_mem a.2), ?_⟩
  have : (⟨a * o * (a : F)⁻¹, (Cz z).mul_mem ((Cz z).mul_mem a.2 hC) ((Cz z).inv_mem a.2)⟩ :
      ↥(Cz z)) = a * ⟨o, hC⟩ * a⁻¹ := rfl
  rw [this, map_mul, map_mul, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]

theorem le_of_imgz_le (z : F) {K K' : Subgroup F} (hK : K ≤ Cz z)
    (hOK' : oddCoreOf (Cz z) ≤ K') (h : imgz z K ≤ imgz z K') : K ≤ K' := by
  intro k hk
  obtain ⟨w, hw, hwk⟩ := (mem_imgz_iff' z).mp (h (piz_mem_imgz (hK hk) hk))
  have h1 : w⁻¹ * ⟨k, hK hk⟩ ∈ classicalInvolutionOddCore ↥(Cz z) := (piz_eq_iff z).mp hwk
  have h2 : (w : F)⁻¹ * k ∈ oddCoreOf (Cz z) := ⟨_, h1, rfl⟩
  have h3 : (w : F) * ((w : F)⁻¹ * k) ∈ K' := K'.mul_mem hw (hOK' h2)
  simpa using h3

theorem eq_of_imgz_eq (z : F) {K K' : Subgroup F} (hK : K ≤ Cz z) (hK' : K' ≤ Cz z)
    (hOK : oddCoreOf (Cz z) ≤ K) (hOK' : oddCoreOf (Cz z) ≤ K') (h : imgz z K = imgz z K') :
    K = K' :=
  le_antisymm (le_of_imgz_le z hK hOK' h.le) (le_of_imgz_le z hK' hOK h.ge)

theorem conjSub_le_Cz {K : Subgroup F} {z : F} (hK : K ≤ Cz z) (a : ↥(Cz z)) :
    conjSub (a : F) K ≤ Cz z := by
  intro x hx
  have h1 : (a : F)⁻¹ * x * a ∈ K := mem_conjSub_iff.mp hx
  have h2 := (Cz z).mul_mem ((Cz z).mul_mem a.2 (hK h1)) ((Cz z).inv_mem a.2)
  simpa [mul_assoc] using h2

theorem oddCoreOf_Cz_le_conjSub {K : Subgroup F} {z : F} (hO : oddCoreOf (Cz z) ≤ K)
    (a : ↥(Cz z)) : oddCoreOf (Cz z) ≤ conjSub (a : F) K := by
  intro o ho
  rw [mem_conjSub_iff]
  have := oddCoreOf_Cz_conj z a⁻¹ ho
  simp only [Subgroup.coe_inv, inv_inv] at this
  exact hO this

theorem conjSub_eq_iff_imgz (z : F) {K : Subgroup F} (hK : K ≤ Cz z)
    (hO : oddCoreOf (Cz z) ≤ K) (a : ↥(Cz z)) :
    conjSub (a : F) K = K ↔ conjSub (piz z a) (imgz z K) = imgz z K := by
  rw [imgz_conjSub]
  constructor
  · intro h
    rw [h]
  · intro h
    exact eq_of_imgz_eq z (conjSub_le_Cz hK a) hK (oddCoreOf_Cz_le_conjSub hO a) hO h

theorem isSubnormal_imgz (z : F) {A B : Subgroup F} (h : IsSubnormal A B) :
    IsSubnormal (imgz z A) (imgz z B) :=
  CFSG.ComponentClassification.Components.chain_map (piz z) (isSubnormal_subgroupOf h (Cz z))

theorem centralizer_piz (z : F) {u : F} (hu : u ∈ Cz z) (hu2 : orderOf u = 2) :
    Subgroup.centralizer ({piz z ⟨u, hu⟩} : Set (Qz z)) = imgz z (Cz z ⊓ Cz u) := by
  have h2 : orderOf (⟨u, hu⟩ : ↥(Cz z)) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have h := centralizer_map_oddCore (Y := ↥(Cz z)) h2
  change _ = Subgroup.centralizer ({piz z ⟨u, hu⟩} : Set (Qz z)) at h
  rw [← h]
  unfold imgz
  congr 1
  ext w
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hw
    refine ⟨w.2, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
  · intro hw
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hw.2))

theorem exists_lift_involution_of_mem (z : F) {H : Subgroup F} {x : Qz z} (hxH : x ∈ imgz z H)
    (hx : x * x = 1) : ∃ (w : F) (hC : w ∈ Cz z), w ∈ H ∧ w * w = 1 ∧ piz z ⟨w, hC⟩ = x := by
  obtain ⟨a₀, ha₀H, rfl⟩ := (mem_imgz_iff' z).mp hxH
  have h1 : piz z (a₀ * a₀) = 1 := by rw [map_mul]; exact hx
  have h2 : a₀ * a₀ ∈ classicalInvolutionOddCore ↥(Cz z) := (piz_eq_one_iff z).mp h1
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥(Cz z))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have h3 : (a₀ * a₀) ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ h2)
  refine ⟨((a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) : ↥(Cz z)) : F),
    (a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z))).2, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact H.pow_mem ha₀H _
  · rw [← Subgroup.coe_mul]
    have : a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) *
        a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) = 1 := by
      calc a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) *
            a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z))
          = a₀ ^ (Nat.card (classicalInvolutionOddCore ↥(Cz z)) +
              Nat.card (classicalInvolutionOddCore ↥(Cz z))) := (pow_add _ _ _).symm
        _ = (a₀ * a₀) ^ Nat.card (classicalInvolutionOddCore ↥(Cz z)) := by
            rw [← two_mul, pow_mul, pow_two]
        _ = 1 := h3
    rw [this]
    rfl
  · obtain ⟨k, hk⟩ := hN
    show piz z (a₀ ^ Nat.card (classicalInvolutionOddCore ↥(Cz z))) = piz z a₀
    rw [map_pow, hk, pow_succ, pow_mul, pow_two, hx, one_pow, one_mul]

theorem piz_ne_one_of_orderOf_eq_two (z : F) {u : F} (hu : u ∈ Cz z) (hu2 : orderOf u = 2) :
    piz z ⟨u, hu⟩ ≠ 1 := by
  intro h
  have h1 : (⟨u, hu⟩ : ↥(Cz z)) ∈ classicalInvolutionOddCore ↥(Cz z) := (piz_eq_one_iff z).mp h
  have h2 := Subgroup.orderOf_dvd_natCard _ h1
  have h3 : orderOf (⟨u, hu⟩ : ↥(Cz z)) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  rw [h3] at h2
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥(Cz z))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h2)

end Conj

section OddFixedVars

variable {F : Type} [Group F] [Finite F]

theorem exists_fixed_of_involutive_of_odd {α : Type*} [Finite α] (hodd : Odd (Nat.card α))
    {f : α → α} (hf : Function.Involutive f) : ∃ a, f a = a := by
  classical
  have := Fintype.ofFinite α
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : Function.End α := f
  have hsq : g ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext a
    exact hf a
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := g) (p := 2) (n := 1) hsq
  by_contra hne
  push Not at hne
  have hempty : IsEmpty (Function.fixedPoints g) := ⟨fun ⟨a, ha⟩ => hne a ha⟩
  have h0 : Fintype.card (Function.fixedPoints g) = 0 := Fintype.card_eq_zero_iff.mpr hempty
  rw [h0, Fintype.card_eq_nat_card] at hmod
  have h2 : Nat.card α % 2 = 0 := by
    have := hmod
    unfold Nat.ModEq at this
    simpa using this
  obtain ⟨k, hk⟩ := hodd
  omega

variable {F : Type} [Group F] [Finite F]

theorem exists_fixed_mul_of_odd {δ : F} (hδ2 : δ * δ = 1) {P : Subgroup F}
    (hP : Odd (Nat.card P)) (hPδ : ∀ p ∈ P, δ * p * δ⁻¹ ∈ P) {x : F}
    (hx : x⁻¹ * (δ * x * δ⁻¹) ∈ P) : ∃ p ∈ P, (x * p) * δ = δ * (x * p) := by
  have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  set c : F := x⁻¹ * (δ * x * δ⁻¹) with hc
  let σ : P → P := fun p => ⟨c * (δ * (p : F) * δ⁻¹), P.mul_mem hx (hPδ p p.2)⟩
  have hσ : Function.Involutive σ := by
    intro p
    apply Subtype.ext
    show c * (δ * (c * (δ * (p : F) * δ⁻¹)) * δ⁻¹) = p
    have e : c * (δ * c * δ⁻¹) = 1 := by
      rw [hc, hδi]
      calc x⁻¹ * (δ * x * δ) * (δ * (x⁻¹ * (δ * x * δ)) * δ) =
          x⁻¹ * δ * x * (δ * δ) * x⁻¹ * δ * x * (δ * δ) := by group
        _ = x⁻¹ * δ * x * x⁻¹ * δ * x := by rw [hδ2]; group
        _ = x⁻¹ * (δ * δ) * x := by group
        _ = 1 := by rw [hδ2]; group
    calc c * (δ * (c * (δ * (p : F) * δ⁻¹)) * δ⁻¹)
        = (c * (δ * c * δ⁻¹)) * ((δ * δ) * (p : F) * (δ * δ)⁻¹) := by group
      _ = p := by rw [e, hδ2]; group
  obtain ⟨p, hp⟩ := exists_fixed_of_involutive_of_odd hP hσ
  refine ⟨p, p.2, ?_⟩
  have h1 : c * (δ * (p : F) * δ⁻¹) = p := congrArg Subtype.val hp
  rw [hc] at h1
  have h2 : δ * (x * p) * δ⁻¹ = x * p := by
    calc δ * (x * p) * δ⁻¹ = δ * x * δ⁻¹ * (δ * p * δ⁻¹) := by group
      _ = x * (x⁻¹ * (δ * x * δ⁻¹) * (δ * p * δ⁻¹)) := by group
      _ = x * p := by rw [h1]
  calc (x * p) * δ = (δ * (x * p) * δ⁻¹) * δ := by rw [h2]
    _ = δ * (x * p) := by group

end OddFixedVars

end CFSG.ClassicalInvolution.Q3.Q3T6X
