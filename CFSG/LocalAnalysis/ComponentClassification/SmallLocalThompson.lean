module

public import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.ComponentClassification.SmallLocal

open Subgroup

variable {G : Type*} [Group G]

theorem thompson_subgroup [Finite G] {p : ℕ} [hp : Fact p.Prime] {P A B : Subgroup G}
    [P.Normal] (hP : IsPGroup p P) (hA : Nat.Coprime p (Nat.card A)) (hB : IsPGroup p B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hfix : ∀ a ∈ A, ∀ x ∈ P, (∀ b ∈ B, b * x = x * b) → a * x = x * a) :
    ∀ a ∈ A, ∀ x ∈ P, a * x = x * a := by
  let α : A →* MulAut P := MulAut.conjNormal.comp A.subtype
  let β : B →* MulAut P := MulAut.conjNormal.comp B.subtype
  have hα : ∀ (a : A) (x : P), ((α a x : P) : G) = a * x * (a : G)⁻¹ := fun a x =>
    MulAut.conjNormal_apply _ x
  have hβ : ∀ (b : B) (x : P), ((β b x : P) : G) = b * x * (b : G)⁻¹ := fun b x =>
    MulAut.conjNormal_apply _ x
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    change MulAut.conjNormal (a : G) * MulAut.conjNormal (b : G) =
      MulAut.conjNormal (b : G) * MulAut.conjNormal (a : G)
    rw [← map_mul, ← map_mul, hAB a a.2 b b.2]
  have hfix' : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    intro a r hr
    have hrB : ∀ b ∈ B, b * (r : G) = r * b := fun b hb => by
      have h := congrArg Subtype.val (hr ⟨b, hb⟩)
      rw [hβ] at h
      calc b * (r : G) = b * r * b⁻¹ * b := by group
        _ = r * b := by rw [h]
    apply Subtype.ext
    rw [hα, hfix a a.2 r r.2 hrB, mul_inv_cancel_right]
  have hA' : ¬ p ∣ Nat.card A := (Nat.Prime.coprime_iff_not_dvd hp.out).mp hA
  have h := CFSG.GroupTheory.thompson_A_times_B hP hA' hB α β hcomm hfix'
  intro a ha x hx
  have hconj : a * x * a⁻¹ = x := by
    have := congrArg (fun f : MulAut P => ((f ⟨x, hx⟩ : P) : G)) (h ⟨a, ha⟩)
    simpa [hα] using this
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [hconj]

theorem normal_coprime_centralizer_centralizes_prime_core {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) {T D : Subgroup H} (hT : IsPGroup p T)
    (hDC : D ≤ centralizer (T : Set H)) (hDn : (D.subgroupOf (centralizer (T : Set H))).Normal)
    (hD : Nat.Coprime p (Nat.card D)) : ⁅D, pCore p H⁆ = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hQn : (pCore p H).Normal := pCore_normal
  have hQp : IsPGroup p (pCore p H) := pCore_isPGroup
  have hdisj : Disjoint D (pCore p H) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact (hD.pow_left n).symm
  have key := thompson_subgroup hQp hD hT
    (fun a ha b hb => ((mem_centralizer_iff.mp (hDC ha)) b hb).symm) (by
      intro d hd x hx hxT
      have hxC : x ∈ centralizer (T : Set H) := mem_centralizer_iff.mpr hxT
      have h1 : x * d⁻¹ * x⁻¹ ∈ D := by
        have := hDn.conj_mem ⟨d⁻¹, hDC (inv_mem hd)⟩ (mem_subgroupOf.mpr (inv_mem hd)) ⟨x, hxC⟩
        exact mem_subgroupOf.mp this
      have hcD : d * x * d⁻¹ * x⁻¹ ∈ D := by
        have := mul_mem hd h1
        simpa only [mul_assoc] using this
      have hcQ : d * x * d⁻¹ * x⁻¹ ∈ pCore p H := mul_mem (hQn.conj_mem x hx d) (inv_mem hx)
      have hc1 : d * x * d⁻¹ * x⁻¹ = 1 := disjoint_def.mp hdisj hcD hcQ
      calc d * x = d * x * d⁻¹ * x⁻¹ * (x * d) := by group
        _ = x * d := by rw [hc1, one_mul])
  rw [commutator_eq_bot_iff_le_centralizer]
  intro d hd
  rw [mem_centralizer_iff]
  intro x hx
  exact (key d hd x hx).symm

end CFSG.ComponentClassification.SmallLocal
