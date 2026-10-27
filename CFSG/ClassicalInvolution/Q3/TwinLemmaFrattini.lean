module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.ClassicalInvolution.Q3.GL4Two

public section

namespace CFSG.ClassicalInvolution.Q3.Twin

open CFSG.OrderReductions.FrattiniAutomorphisms

variable {Y : Type*} [Group Y] [Finite Y]

private theorem displaced_key {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {P : Subgroup Y} (hP : IsPGroup 3 P) {a b : Y}
    (ha : a ∈ P) (hb : b ∈ P) (S : Finset Y) (hSU : ∀ x ∈ S, x ∈ U)
    (hda : ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ Subgroup.closure (S : Set Y))
    (hdb : ∀ u ∈ U, b * u * b⁻¹ * u⁻¹ ∈ Subgroup.closure (S : Set Y)) :
    (S.card ≤ 4 → a * b = b * a) ∧ (S.card ≤ 2 → a ≠ 1 → b ∈ Subgroup.zpowers a) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcomm, hexp, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hU
  let ι : ↥U →* ↥U ⧸ frattini ↥U := QuotientGroup.mk' (frattini ↥U)
  let σ : Y →* MulAut (↥U ⧸ frattini ↥U) :=
    quotientAction (frattini ↥U) (MulAut.conjNormal (H := U))
  let φ : ↥P →* MulAut (↥U ⧸ frattini ↥U) := σ.comp P.subtype
  have hσ : ∀ (g : Y) (u : ↥U),
      σ g (ι u) = ι ⟨g * u * g⁻¹, Subgroup.Normal.conj_mem ‹U.Normal› _ u.2 g⟩ := by
    intro g u
    exact (quotientAction_apply (frattini ↥U) (MulAut.conjNormal (H := U)) g u).trans
      (congrArg ι (Subtype.ext (MulAut.conjNormal_apply g u)))
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hker : MulAut.conjNormal (H := U) (p : Y) ∈ (quotientAutomorphism (frattini ↥U)).ker :=
      hp
    have hkerP := frattini_automorphism_kernel_isPGroup 2 hU
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hkerP ⟨_, hker⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hP p
    have hord : orderOf (MulAut.conjNormal (H := U) (p : Y)) ∣ 3 ^ m := by
      rw [← hm, ← Subgroup.orderOf_coe p]
      exact orderOf_map_dvd (MulAut.conjNormal (H := U)) (p : Y)
    have hk' : orderOf (MulAut.conjNormal (H := U) (p : Y)) = 2 ^ k := by
      rw [← hk]
      exact Subgroup.orderOf_coe (⟨_, hker⟩ : (quotientAutomorphism (frattini ↥U)).ker)
    have hk0 : k = 0 := by
      by_contra hne
      have h2 : 2 ∣ 3 ^ m := by
        have : 2 ∣ 2 ^ k := dvd_pow_self 2 hne
        exact this.trans (hk' ▸ hord)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
      omega
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
    have hpC : (p : Y) ∈ Subgroup.centralizer (U : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := congrArg (fun f : MulAut ↥U => (f ⟨u, hu⟩ : Y)) hk'
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hpU : (p : Y) ∈ U := hC hpC
    obtain ⟨l, hl⟩ := IsPGroup.iff_orderOf.mp hU ⟨(p : Y), hpU⟩
    have h2l : orderOf (p : Y) = 2 ^ l := by
      rw [← Subgroup.orderOf_coe ⟨(p : Y), hpU⟩] at hl
      exact hl
    have h3m : orderOf (p : Y) = 3 ^ m := by rw [← hm]; exact Subgroup.orderOf_coe p
    have hl0 : l = 0 := by
      by_contra hne
      have h2 : 2 ∣ 3 ^ m := by
        have : 2 ∣ 2 ^ l := dvd_pow_self 2 hne
        rw [← h2l, h3m] at this
        exact this
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
      omega
    rw [hl0, pow_zero, orderOf_eq_one_iff] at h2l
    exact Subtype.ext h2l
  let S' : Finset (↥U ⧸ frattini ↥U) := S.attach.image fun x => ι ⟨x.1, hSU x.1 x.2⟩
  have hS' : S'.card ≤ S.card := (Finset.card_image_le).trans (by simp)
  have hSle : Subgroup.closure (S : Set Y) ≤ U := (Subgroup.closure_le U).mpr fun x hx => hSU x hx
  have hmk : ∀ c (hc : c ∈ Subgroup.closure (S : Set Y)),
      ι ⟨c, hSle hc⟩ ∈ Subgroup.closure (S' : Set (↥U ⧸ frattini ↥U)) := by
    intro c hc
    refine Subgroup.closure_induction
      (p := fun c hc => ι ⟨c, hSle hc⟩ ∈ Subgroup.closure (S' : Set (↥U ⧸ frattini ↥U)))
      ?_ ?_ ?_ ?_ hc
    · intro x hx
      refine Subgroup.subset_closure ?_
      simp only [S', Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach, true_and,
        Subtype.exists]
      exact ⟨x, hx, rfl⟩
    · have : (⟨1, hSle (one_mem _)⟩ : ↥U) = 1 := rfl
      simp [this]
    · intro x y hx hy hxm hym
      have : (⟨x * y, hSle (mul_mem hx hy)⟩ : ↥U) = ⟨x, hSle hx⟩ * ⟨y, hSle hy⟩ := rfl
      rw [this, map_mul]
      exact mul_mem hxm hym
    · intro x hx hxm
      have : (⟨x⁻¹, hSle (inv_mem hx)⟩ : ↥U) = (⟨x, hSle hx⟩)⁻¹ := rfl
      rw [this, map_inv]
      exact inv_mem hxm
  have hdisp : ∀ g : ↥P, (∀ u ∈ U, (g : Y) * u * (g : Y)⁻¹ * u⁻¹ ∈ Subgroup.closure (S : Set Y)) →
      ∀ x : ↥U ⧸ frattini ↥U, φ g x * x⁻¹ ∈ Subgroup.closure (S' : Set (↥U ⧸ frattini ↥U)) := by
    intro g hg x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥U) x
    have := hmk _ (hg u u.2)
    have e : φ g (ι u) * (ι u)⁻¹ = ι ⟨(g : Y) * u * (g : Y)⁻¹ * (u : Y)⁻¹, hSle (hg u u.2)⟩ := by
      change σ g (ι u) * (ι u)⁻¹ = _
      rw [hσ, ← map_inv, ← map_mul]
      rfl
    rw [e]
    exact this
  have hcomm' : ∀ x y : ↥U ⧸ frattini ↥U, x * y = y * x := fun x y => mul_comm' x y
  refine ⟨fun hS4 => ?_, fun hS2 ha1 => ?_⟩
  · have := GL4Two.mul_comm_of_displaced hcomm' hexp hP φ hφinj ⟨a, ha⟩ ⟨b, hb⟩ S'
      (hS'.trans hS4) (hdisp ⟨a, ha⟩ hda) (hdisp ⟨b, hb⟩ hdb)
    exact congrArg Subtype.val this
  · have := GL4Two.mem_zpowers_of_displaced hcomm' hexp hP φ hφinj (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
      S' (hS'.trans hS2) (hdisp ⟨a, ha⟩ hda) (hdisp ⟨b, hb⟩ hdb)
      (fun h => ha1 (congrArg Subtype.val h))
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp this
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem mul_comm_of_displaced_into_closure {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {P : Subgroup Y} (hP : IsPGroup 3 P) {a b : Y}
    (ha : a ∈ P) (hb : b ∈ P) (S : Finset Y) (hSU : ∀ x ∈ S, x ∈ U) (hS : S.card ≤ 4)
    (hda : ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ Subgroup.closure (S : Set Y))
    (hdb : ∀ u ∈ U, b * u * b⁻¹ * u⁻¹ ∈ Subgroup.closure (S : Set Y)) : a * b = b * a :=
  (displaced_key hU hC hP ha hb S hSU hda hdb).1 hS

theorem mem_zpowers_of_displaced_into_closure {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {P : Subgroup Y} (hP : IsPGroup 3 P) {a b : Y}
    (ha : a ∈ P) (hb : b ∈ P) (S : Finset Y) (hSU : ∀ x ∈ S, x ∈ U) (hS : S.card ≤ 2)
    (hda : ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ Subgroup.closure (S : Set Y))
    (hdb : ∀ u ∈ U, b * u * b⁻¹ * u⁻¹ ∈ Subgroup.closure (S : Set Y)) (ha1 : a ≠ 1) :
    b ∈ Subgroup.zpowers a :=
  (displaced_key hU hC hP ha hb S hSU hda hdb).2 hS ha1

end CFSG.ClassicalInvolution.Q3.Twin
