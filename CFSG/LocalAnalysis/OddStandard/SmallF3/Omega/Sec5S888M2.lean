module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

private def s888SupportTwo (V : Subgroup X) (W : Fin 4 → Subgroup X) (c d : Fin 4) : Set X :=
  {v | ∃ a ∈ W c, ∃ b ∈ W d, a ≠ 1 ∧ b ≠ 1 ∧ v = a * b}

private theorem s888SupportTwo_subset_V (hS : PlaneSys V W) {c d : Fin 4} :
    s888SupportTwo V W c d ⊆ V := by
  rintro v ⟨a, ha, b, hb, _, _, rfl⟩
  exact V.mul_mem (hS.le c ha) (hS.le d hb)

private theorem s888_card_subtype_ne_one (hS : PlaneSys V W) (i : Fin 4) :
    Nat.card {a : W i // a ≠ 1} = 3 := by
  classical
  haveI : Finite (W i) := Nat.finite_of_card_ne_zero (by rw [hS.card i]; decide)
  haveI : Fintype (W i) := Fintype.ofFinite (W i)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun a : W i => a = 1),
    Fintype.card_subtype_eq (1 : W i), Fintype.card_eq_nat_card, hS.card i]

private theorem s888SupportTwo_card (hS : PlaneSys V W) {c d : Fin 4} (hcd : c ≠ d) :
    Nat.card (s888SupportTwo V W c d) = 9 := by
  classical
  let T := {a : W c // a ≠ 1} × {b : W d // b ≠ 1}
  let f : T → s888SupportTwo V W c d := fun x =>
    ⟨(x.1.1 : X) * (x.2.1 : X),
      ⟨(x.1.1 : X), x.1.1.2, (x.2.1 : X), x.2.1.2,
        (fun h => x.1.2 (Subtype.ext h)), (fun h => x.2.2 (Subtype.ext h)), rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ h
      have hval : (a1 : X) * (b1 : X) = (a2 : X) * (b2 : X) := congrArg Subtype.val h
      have h1 : (a2 : X)⁻¹ * (a1 : X) = (b2 : X) * (b1 : X)⁻¹ := by
        have h2 : ((a2 : X)⁻¹ * (a1 : X)) * (b1 : X) = (b2 : X) := by
          calc ((a2 : X)⁻¹ * (a1 : X)) * (b1 : X)
              = (a2 : X)⁻¹ * ((a1 : X) * (b1 : X)) := by group
            _ = (a2 : X)⁻¹ * ((a2 : X) * (b2 : X)) := by rw [hval]
            _ = (b2 : X) := by group
        calc (a2 : X)⁻¹ * (a1 : X)
            = ((a2 : X)⁻¹ * (a1 : X)) * (b1 : X) * (b1 : X)⁻¹ := by group
          _ = (b2 : X) * (b1 : X)⁻¹ := by rw [h2]
      have hmem : (a2 : X)⁻¹ * (a1 : X) ∈ W c ⊓ W d :=
        ⟨(W c).mul_mem ((W c).inv_mem a2.2) a1.2, by
          rw [h1]
          exact (W d).mul_mem b2.2 ((W d).inv_mem b1.2)⟩
      rw [hS.inf_eq_bot hcd] at hmem
      have hone : (a2 : X)⁻¹ * (a1 : X) = 1 := Subgroup.mem_bot.mp hmem
      have haeq : (a1 : X) = (a2 : X) := by
        have h2 := congrArg (fun t : X => (a2 : X) * t) hone
        simp only [mul_one] at h2
        rw [← mul_assoc, mul_inv_cancel, one_mul] at h2
        exact h2
      have hbeq : (b1 : X) = (b2 : X) := by
        have hone_b : (b2 : X) * (b1 : X)⁻¹ = 1 := by rw [← h1]; exact hone
        have h2 : (b2 : X) = (b1 : X) := by
          calc (b2 : X) = ((b2 : X) * (b1 : X)⁻¹) * (b1 : X) := by group
            _ = 1 * (b1 : X) := by rw [hone_b]
            _ = (b1 : X) := one_mul _
        exact h2.symm
      exact Prod.ext (Subtype.ext (Subtype.ext haeq)) (Subtype.ext (Subtype.ext hbeq))
    · rintro ⟨v, hv⟩
      obtain ⟨a, ha, b, hb, ha1, hb1, rfl⟩ := hv
      refine ⟨(⟨⟨a, ha⟩, fun h => ha1 (Subtype.ext_iff.mp h)⟩,
        ⟨⟨b, hb⟩, fun h => hb1 (Subtype.ext_iff.mp h)⟩), Subtype.ext rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f hf)
  rw [← hcard, Nat.card_prod, s888_card_subtype_ne_one hS c, s888_card_subtype_ne_one hS d]

private theorem s888SupportTwo_conj_mem (hS : PlaneSys V W) {c d : Fin 4}
    {R : Subgroup X} (hR : ActsElemAb V R)
    (hpres : ∀ y : normalizer (V : Set X), (y : X) ∈ R →
      (planeHom hS y c = c ∧ planeHom hS y d = d) ∨
        (planeHom hS y c = d ∧ planeHom hS y d = c))
    {y : X} (hy : y ∈ R) {v : X} (hv : v ∈ s888SupportTwo V W c d) :
    y * v * y⁻¹ ∈ s888SupportTwo V W c d := by
  rcases hv with ⟨a, ha, b, hb, ha1, hb1, rfl⟩
  have hyN : y ∈ normalizer (V : Set X) := hR.le_normalizer hy
  let y' : normalizer (V : Set X) := ⟨y, hyN⟩
  have hspec_a := planeHom_spec hS y' c a ha
  have hspec_b := planeHom_spec hS y' d b hb
  have hne_a : y * a * y⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have hconj : y⁻¹ * (y * a * y⁻¹) * y = a := by group
    have h1 : y⁻¹ * (y * a * y⁻¹) * y = 1 := by rw [h]; group
    rw [hconj] at h1
    exact h1
  have hne_b : y * b * y⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have hconj : y⁻¹ * (y * b * y⁻¹) * y = b := by group
    have h1 : y⁻¹ * (y * b * y⁻¹) * y = 1 := by rw [h]; group
    rw [hconj] at h1
    exact h1
  rcases hpres y' hy with ⟨hcc, hdd⟩ | ⟨hcd', hdc'⟩
  · exact ⟨y * a * y⁻¹, by rwa [hcc] at hspec_a,
      y * b * y⁻¹, by rwa [hdd] at hspec_b, hne_a, hne_b, by group⟩
  · refine ⟨y * b * y⁻¹, by rwa [hdc'] at hspec_b,
      y * a * y⁻¹, by rwa [hcd'] at hspec_a, hne_b, hne_a, ?_⟩
    have hcomm : (y * a * y⁻¹) * (y * b * y⁻¹) = (y * b * y⁻¹) * (y * a * y⁻¹) :=
      hS.comm _ (hS.le d (by rwa [hcd'] at hspec_a)) _
        (hS.le c (by rwa [hdc'] at hspec_b))
    rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group, hcomm]

theorem exists_fixed_support_two [Finite X] (hS : PlaneSys V W) {c d : Fin 4} (hcd : c ≠ d)
    {R : Subgroup X} (hR : ActsElemAb V R)
    (hpres : ∀ y : normalizer (V : Set X), (y : X) ∈ R →
      (planeHom hS y c = c ∧ planeHom hS y d = d) ∨
        (planeHom hS y c = d ∧ planeHom hS y d = c)) :
    ∃ a ∈ W c, ∃ b ∈ W d, a ≠ 1 ∧ b ≠ 1 ∧ ∀ y ∈ R, y * (a * b) * y⁻¹ = a * b := by
  classical
  let S := s888SupportTwo V W c d
  have hcardS : Nat.card S = 9 := s888SupportTwo_card hS hcd
  have hnotdvd : ¬ 2 ∣ Nat.card S := by rw [hcardS]; decide
  have hstab : ∀ (y : R) (v : S), (y : X) * (v : X) * (y : X)⁻¹ ∈ S :=
    fun y v => s888SupportTwo_conj_mem hS hR hpres y.2 v.2
  let actR : R → S → S := fun y v => ⟨(y : X) * (v : X) * (y : X)⁻¹, hstab y v⟩
  have hact_one : actR 1 = id := by
    funext v
    apply Subtype.ext
    change (1 : X) * (v : X) * (1 : X)⁻¹ = (v : X)
    group
  have hact_mul : ∀ y z : R, actR (y * z) = actR y ∘ actR z := by
    intro y z
    funext v
    apply Subtype.ext
    change ((y * z : R) : X) * (v : X) * ((y * z : R) : X)⁻¹ =
      (y : X) * ((z : X) * (v : X) * (z : X)⁻¹) * (y : X)⁻¹
    simp only [Subgroup.coe_mul]
    group
  let endR : R →* Function.End S :=
    { toFun := actR
      map_one' := hact_one
      map_mul' := fun y z => hact_mul y z }
  letI : MulAction R S := MulAction.ofEndHom endR
  let φ : R →* Equiv.Perm S := MulAction.toPermHom R S
  let P : Subgroup (Equiv.Perm S) := φ.range
  have hP2 : IsPGroup 2 P := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro g
    refine ⟨1, ?_⟩
    have hsq : g ^ 2 = 1 := by
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp g.2
      apply Subtype.ext
      change (g : Equiv.Perm S) ^ 2 = (1 : Equiv.Perm S)
      rw [pow_two, ← hy, ← map_mul]
      apply Equiv.ext
      intro s
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
      show ((y * y : R) • s : S) = s
      apply Subtype.ext
      change ((y * y : R) : X) * (s : X) * ((y * y : R) : X)⁻¹ = (s : X)
      simpa using hR.sq (y : X) y.2 (s : X) (s888SupportTwo_subset_V hS s.2)
    simpa using hsq
  obtain ⟨s, hs⟩ := hP2.nonempty_fixed_point_of_prime_not_dvd_card S hnotdvd
  rw [MulAction.mem_fixedPoints] at hs
  rcases s.2 with ⟨a, ha, b, hb, ha1, hb1, hsv⟩
  refine ⟨a, ha, b, hb, ha1, hb1, fun y hy => ?_⟩
  have hfix : (⟨φ ⟨y, hy⟩, MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩⟩ : P) • s = s := hs _
  have hfix' : (y : X) * (s : X) * (y : X)⁻¹ = (s : X) := by
    have h1 : actR ⟨y, hy⟩ s = s := hfix
    exact congrArg Subtype.val h1
  rw [hsv] at hfix'
  exact hfix'

end CFSG.OddStandard.SmallF3.Omega
