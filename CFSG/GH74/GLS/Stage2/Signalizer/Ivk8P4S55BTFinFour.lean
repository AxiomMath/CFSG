module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinGlue
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCycB
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCyc

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74.GLS FinGen FinGlue FinCyc

@[expose] def NoFourPerfIn {G : Type} [Group G] (R : Subgroup G) : Prop :=
  ∀ U Q I : Subgroup G, U ≤ R → I ≤ R → IVK.IsFourSubgroup U → IVK.IsFourSubgroup Q → Q ≤ I →
    ⁅I, I⁆ = I → I ≤ centralizer (U : Set G) → False

namespace FinFour

variable {G : Type} [Group G]

theorem isFourSubgroup_map_of_injective {H : Type} [Group H] {f : H →* G}
    (hf : Function.Injective f) {U : Subgroup H} (hU : IVK.IsFourSubgroup U) :
    IVK.IsFourSubgroup (U.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hU.1
  exact ⟨IsElementaryAbelian.map f, by rw [Subgroup.card_map_of_injective hf, hU.2]⟩

end FinFour

open FinFour in
theorem NoFourPerf.of_in {G : Type} [Group G] {R : Subgroup G} (h : NoFourPerfIn R) :
    NoFourPerf ↥R := by
  intro U Q I hU hQ hQI hI hIU
  have hinj : Function.Injective R.subtype := Subtype.val_injective
  refine h (U.map R.subtype) (Q.map R.subtype) (I.map R.subtype) (map_subtype_le U)
    (map_subtype_le I) (isFourSubgroup_map_of_injective hinj hU)
    (isFourSubgroup_map_of_injective hinj hQ) (Subgroup.map_mono hQI)
    (by rw [← Subgroup.map_commutator, hI]) ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨u, hu, rfl⟩
  exact congrArg Subtype.val (mem_centralizer_iff.mp (hIU hg) u hu)

namespace FinFour

variable {G : Type} [Group G]

theorem isSolvable_of_card_dvd {H : Type*} [Group H] [Finite H] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card H ∣ p ^ a * q ^ b) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hq).1 hk₂
  exact isSolvable_of_card_eq_pow_mul_pow hp hq hpq hk.symm

theorem mul_mem_of_not_mem {P R : Subgroup G} {c : G} (hR : ∀ x ∈ R, x ∈ P ∨ x * c ∈ P)
    (hc : c * c = 1) (hcP : ∀ x ∈ P, c * x * c⁻¹ ∈ P) {x y : G} (hx : x ∈ R) (hy : y ∈ R)
    (hxP : x ∉ P) (hyP : y ∉ P) : x * y ∈ P := by
  have hx' := (hR x hx).resolve_left hxP
  have hy' := (hR y hy).resolve_left hyP
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have : x * y = (x * c) * (c * (y * c) * c⁻¹) := by
    rw [hci]
    calc x * y = x * (c * c) * y * (c * c) := by rw [hc]; group
      _ = (x * c) * (c * (y * c) * c) := by group
  rw [this]
  exact P.mul_mem hx' (hcP _ hy')

theorem perfect_le {P R : Subgroup G} {c : G} (hR : ∀ x ∈ R, x ∈ P ∨ x * c ∈ P)
    (hc : c * c = 1) (hcP : ∀ x ∈ P, c * x * c⁻¹ ∈ P) {I : Subgroup G} (hIR : I ≤ R)
    (hI : ⁅I, I⁆ = I) : I ≤ P :=
  perfect_le_of_two hI fun _ hg _ hh hgP hhP =>
    mul_mem_of_not_mem hR hc hcP (hIR hg) (hIR hh) hgP hhP

theorem exists_pair {P R : Subgroup G} {c : G} (hR : ∀ x ∈ R, x ∈ P ∨ x * c ∈ P)
    (hc : c * c = 1) (hcP : ∀ x ∈ P, c * x * c⁻¹ ∈ P) {U : Subgroup G} (hUR : U ≤ R)
    (hU : IVK.IsFourSubgroup U) : ∃ t ∈ U, ∃ w ∈ U, t ≠ 1 ∧ w ≠ 1 ∧ w ≠ t ∧ w ∈ P := by
  obtain ⟨u, huU, v, hvU, hu1, hv1, hvu⟩ := exists_two_of_four hU
  have := hU.1
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
  by_cases huP : u ∈ P
  · exact ⟨v, hvU, u, huU, hv1, hu1, hvu.symm, huP⟩
  by_cases hvP : v ∈ P
  · exact ⟨u, huU, v, hvU, hu1, hv1, hvu, hvP⟩
  refine ⟨u, huU, u * v, U.mul_mem huU hvU, hu1, fun h => hvu ?_, fun h => hv1 ?_,
    mul_mem_of_not_mem hR hc hcP (hUR huU) (hUR hvU) huP hvP⟩
  · have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u huU)
    rw [← huinv]
    exact eq_inv_of_mul_eq_one_right h
  · calc v = u * (u * v) := by rw [← mul_assoc, hsq u huU, one_mul]
      _ = 1 := by rw [h, hsq u huU]

variable [Finite G]

theorem isSolvable_of_reps {P R : Subgroup G} (reps : List G) {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q)
    (hcov : ∀ t ∈ R, t * t = 1 → t ≠ 1 → ∃ r ∈ reps, ∃ g ∈ P, t = g * r * g⁻¹)
    (hcnt : ∀ r ∈ reps, ∀ w ∈ P ⊓ centralizer ({r} : Set G), w * w = 1 → w ≠ 1 → w ≠ r →
      Nat.card ↥((P ⊓ centralizer ({r} : Set G)) ⊓ centralizer ({w} : Set G)) ∣ p ^ a * q ^ b)
    {t w : G} (ht : t ∈ R) (htt : t * t = 1) (ht1 : t ≠ 1) (hwP : w ∈ P) (hww : w * w = 1)
    (hw1 : w ≠ 1) (hwt : w ≠ t) (hc : t * w = w * t) :
    Group.IsSolvable ↥(P ⊓ centralizer ({t} : Set G) ⊓ centralizer ({w} : Set G)) := by
  obtain ⟨r, hr, g, hg, rfl⟩ := hcov t ht htt ht1
  set w' := g⁻¹ * w * g with hw'
  have hw'P : w' ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hg) hwP) hg
  have hw'r : w' * r = r * w' := by
    have h1 : w * (g * r * g⁻¹) = (g * r * g⁻¹) * w := hc.symm
    calc w' * r = g⁻¹ * (w * (g * r * g⁻¹)) * g := by rw [hw']; group
      _ = g⁻¹ * ((g * r * g⁻¹) * w) * g := by rw [h1]
      _ = r * w' := by rw [hw']; group
  have hw'w' : w' * w' = 1 := by
    calc w' * w' = g⁻¹ * (w * w) * g := by rw [hw']; group
      _ = 1 := by rw [hww]; group
  have hw'1 : w' ≠ 1 := fun h => hw1 (by
    calc w = g * w' * g⁻¹ := by rw [hw']; group
      _ = 1 := by rw [h]; group)
  have hw'ne : w' ≠ r := fun h => hwt (by
    calc w = g * w' * g⁻¹ := by rw [hw']; group
      _ = g * r * g⁻¹ := by rw [h])
  have hsol := isSolvable_of_card_dvd hp hq hpq
    (hcnt r hr w' ⟨hw'P, mem_centralizer_singleton_iff.mpr hw'r⟩ hw'w' hw'1 hw'ne)
  set T := (P ⊓ centralizer ({r} : Set G)) ⊓ centralizer ({w'} : Set G)
  let f : ↥(P ⊓ centralizer ({g * r * g⁻¹} : Set G) ⊓ centralizer ({w} : Set G)) →* ↥T :=
    { toFun := fun x => ⟨g⁻¹ * x * g, by
        have hxP : (x : G) ∈ P := x.2.1.1
        have hxt : (x : G) * (g * r * g⁻¹) = (g * r * g⁻¹) * x :=
          mem_centralizer_singleton_iff.mp x.2.1.2
        have hxw : (x : G) * w = w * x := mem_centralizer_singleton_iff.mp x.2.2
        have h1 : g⁻¹ * (x : G) * g * r = r * (g⁻¹ * x * g) := by
          calc g⁻¹ * (x : G) * g * r = g⁻¹ * (↑x * (g * r * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * r * g⁻¹) * ↑x) * g := by rw [hxt]
            _ = r * (g⁻¹ * ↑x * g) := by group
        have h2 : g⁻¹ * (x : G) * g * w' = w' * (g⁻¹ * x * g) := by
          rw [hw']
          calc g⁻¹ * (x : G) * g * (g⁻¹ * w * g) = g⁻¹ * (↑x * w) * g := by group
            _ = g⁻¹ * (w * ↑x) * g := by rw [hxw]
            _ = g⁻¹ * w * g * (g⁻¹ * ↑x * g) := by group
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
          ⟨P.mul_mem (P.mul_mem (P.inv_mem hg) hxP) hg, mem_centralizer_singleton_iff.mpr h1⟩,
          mem_centralizer_singleton_iff.mpr h2⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp only [coe_mul]; group }
  have hf : Function.Injective f := fun x y h => by
    have h1 : g⁻¹ * (x : G) * g = g⁻¹ * (y : G) * g := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  exact Group.isSolvable_of_isSolvable_injective hf

theorem noFourPerfIn_of_reps {P R : Subgroup G} {c : G} (hR : ∀ x ∈ R, x ∈ P ∨ x * c ∈ P)
    (hcc : c * c = 1) (hcP : ∀ x ∈ P, c * x * c⁻¹ ∈ P) (reps : List G) {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcov : ∀ t ∈ R, t * t = 1 → t ≠ 1 → ∃ r ∈ reps, ∃ g ∈ P, t = g * r * g⁻¹)
    (hcnt : ∀ r ∈ reps, ∀ w ∈ P ⊓ centralizer ({r} : Set G), w * w = 1 → w ≠ 1 → w ≠ r →
      Nat.card ↥((P ⊓ centralizer ({r} : Set G)) ⊓ centralizer ({w} : Set G)) ∣ p ^ a * q ^ b) :
    NoFourPerfIn R := by
  intro U Q I hUR hIR hU hQ hQI hI hIU
  have := hU.1
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥U)).comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨t, htU, w, hwU, ht1, hw1, hwt, hwP⟩ := exists_pair hR hcc hcP hUR hU
  have hsol := isSolvable_of_reps reps hp hq hpq hcov hcnt (hUR htU) (hsq t htU) ht1 hwP
    (hsq w hwU) hw1 hwt (hcomm t htU w hwU)
  have hIle : I ≤ P ⊓ centralizer ({t} : Set G) ⊓ centralizer ({w} : Set G) := by
    intro x hx
    have hxU := mem_centralizer_iff.mp (hIU hx)
    refine ⟨⟨perfect_le hR hcc hcP hIR hI hx, ?_⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.mpr (hxU t htU).symm
    · exact mem_centralizer_singleton_iff.mpr (hxU w hwU).symm
  have hbot := eq_bot_of_perfect_of_le hIle hsol hI
  have hQ1 : Q = ⊥ := le_bot_iff.mp (by rw [← hbot]; exact hQI)
  have h4 := hQ.2
  rw [hQ1, card_bot] at h4
  omega

end FinFour

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
