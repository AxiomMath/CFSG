module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModuleLines
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open scoped IsMulCommutative commutatorElement

section ecp

variable {D : Type*} [Group D]

lemma ecp_comm_mul_left (hcl : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D) (a b c : D) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.mp (hcl b c) a,
    mul_inv_cancel_right]
  exact Subgroup.mem_center_iff.mp (hcl a c) _

lemma ecp_comm_mul_right (hcl : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D) (a b c : D) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have h := Subgroup.mem_center_iff.mp (hcl a c) b
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ := by simp only [mul_assoc]
    _ = ⁅a, b⁆ * (⁅a, c⁆ * b) * b⁻¹ := by rw [h]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by simp only [mul_assoc, mul_inv_cancel, mul_one]

lemma ecp_comm_center_left {z : D} (hz : z ∈ Subgroup.center D) (b : D) : ⁅z, b⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz b).symm

lemma ecp_comm_center_right (a : D) {z : D} (hz : z ∈ Subgroup.center D) : ⁅a, z⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a)

lemma ecp_exists_pairing (hcl : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D) :
    ∃ B : D ⧸ Subgroup.center D → D ⧸ Subgroup.center D → Subgroup.center D,
      (∀ x y : D, B x y = ⟨⁅x, y⁆, hcl x y⟩) ∧
      (∀ u u' v, B (u * u') v = B u v * B u' v) ∧
      (∀ u v v', B u (v * v') = B u v * B u v') := by
  let B : D ⧸ Subgroup.center D → D ⧸ Subgroup.center D → Subgroup.center D := fun u v =>
    Quotient.liftOn₂' u v (fun x y => (⟨⁅x, y⁆, hcl x y⟩ : Subgroup.center D)) (by
      intro a b a' b' ha hb
      have ha' : a⁻¹ * a' ∈ Subgroup.center D := QuotientGroup.leftRel_apply.mp ha
      have hb' : b⁻¹ * b' ∈ Subgroup.center D := QuotientGroup.leftRel_apply.mp hb
      have e1 : a' = a * (a⁻¹ * a') := by rw [mul_inv_cancel_left]
      have e2 : b' = b * (b⁻¹ * b') := by rw [mul_inv_cancel_left]
      apply Subtype.ext
      show ⁅a, b⁆ = ⁅a', b'⁆
      rw [e1, e2, ecp_comm_mul_left hcl, ecp_comm_center_left ha', mul_one,
        ecp_comm_mul_right hcl, ecp_comm_center_right _ hb', mul_one])
  refine ⟨B, fun x y => rfl, ?_, ?_⟩
  · intro u u' v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective u'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    apply Subtype.ext
    exact ecp_comm_mul_left hcl x x' y
  · intro u v v'
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective v'
    apply Subtype.ext
    exact ecp_comm_mul_right hcl x y y'

end ecp

theorem exists_comm_pairing {D : Type*} [Group D] (q : ℕ) [Fact q.Prime]
    (hcl : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D)
    [IsElementaryAbelian q (D ⧸ Subgroup.center D)] [IsElementaryAbelian q (Subgroup.center D)] :
    ∃ β : Additive (D ⧸ Subgroup.center D) →ₗ[ZMod q]
        Additive (D ⧸ Subgroup.center D) →ₗ[ZMod q] Additive (Subgroup.center D),
      ∀ x y : D, β (Additive.ofMul (x : D ⧸ Subgroup.center D))
        (Additive.ofMul (y : D ⧸ Subgroup.center D)) =
          Additive.ofMul (⟨⁅x, y⁆, hcl x y⟩ : Subgroup.center D) := by
  obtain ⟨B, hB, hB1, hB2⟩ := ecp_exists_pairing hcl
  let f1 : (D ⧸ Subgroup.center D) →
      Additive (D ⧸ Subgroup.center D) →ₗ[ZMod q] Additive (Subgroup.center D) := fun u =>
    AddMonoidHom.toZModLinearMap q
      (AddMonoidHom.mk' (fun v : Additive (D ⧸ Subgroup.center D) => Additive.ofMul (B u v.toMul))
        (fun v v' => congrArg Additive.ofMul (hB2 u v.toMul v'.toMul)))
  let f2 : Additive (D ⧸ Subgroup.center D) →+
      (Additive (D ⧸ Subgroup.center D) →ₗ[ZMod q] Additive (Subgroup.center D)) :=
    AddMonoidHom.mk' (fun u : Additive (D ⧸ Subgroup.center D) => f1 u.toMul) (fun u u' =>
      LinearMap.ext fun v => congrArg Additive.ofMul (hB1 u.toMul u'.toMul v.toMul))
  refine ⟨AddMonoidHom.toZModLinearMap q f2, fun x y => ?_⟩
  exact congrArg Additive.ofMul (hB x y)

section Actions

variable {J : Type} [Group J] [Finite J]


theorem four_le_card_of_action {A : Type} [Group A] [Finite A] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hpq : p ≠ q) (hp5 : 5 ≤ p) [IsElementaryAbelian q A] [MulDistribMulAction J A]
    {U : Subgroup J} (hU : Nat.card U = p ^ 2) (hexp : ∀ u ∈ U, u ^ p = 1)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {τ σ : J}
    (hτ : τ ∈ Subgroup.normalizer (U : Set J)) (hτinv : ∀ u ∈ U, τ * u * τ⁻¹ = u⁻¹)
    (hσ : σ ∈ Subgroup.normalizer (U : Set J))
    (hσ1 : ∀ H : Subgroup J, H ≤ U → Nat.card H = p → ∃ h ∈ H, σ * h * σ⁻¹ ∉ H)
    (hσ2 : ∀ H : Subgroup J, H ≤ U → Nat.card H = p →
      ∃ h ∈ H, σ * (σ * h * σ⁻¹) * σ⁻¹ ∉ H)
    (hnt : ∃ u ∈ U, ∃ a : A, u • a ≠ a) : q ^ 4 ≤ Nat.card A := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  have hpF : ((p : ℕ) : ZMod q) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  let ρ : J →* Module.End (ZMod q) (Additive A) :=
    Theory.Representation.ofElementaryAbelianAction (p := q) (A := J) (G := A)
  have hnt' : ∃ u ∈ U, ρ u ≠ 1 := by
    obtain ⟨u, hu, a, ha⟩ := hnt
    refine ⟨u, hu, fun h => ha ?_⟩
    have h1 := congrArg (fun T : Module.End (ZMod q) (Additive A) => T (Additive.ofMul a)) h
    have h2 : ρ u (Additive.ofMul a) = Additive.ofMul (u • a) :=
      Theory.Representation.ofElementaryAbelianAction_apply_ofMul u a
    simp only [h2, Module.End.one_apply] at h1
    exact Additive.ofMul.injective h1
  have hp2 : p ≠ 2 := by omega
  have h4 := PlaneModule.four_le_finrank hpF ρ hp2 hU hexp hcomm hτ hτinv hσ hσ1 hσ2 hnt'
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod q) (V := Additive A)
  rw [Nat.card_zmod] at hcard
  have : Nat.card (Additive A) = Nat.card A := Nat.card_congr Additive.toMul
  rw [this] at hcard
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : q.Prime).pos h4


omit [Finite J] in
theorem smul_commutator {D : Type*} [Group D] [MulDistribMulAction J D] (g : J) (x y : D) :
    ⁅g • x, g • y⁆ = g • ⁅x, y⁆ := by
  simp only [commutatorElement_def, smul_mul', smul_inv']

theorem exists_abelian_of_action {D : Type} [Group D] [Finite D] {p q : ℕ} [Fact p.Prime]
    [Fact q.Prime] (hpq : p ≠ q) (hcl : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D)
    [IsElementaryAbelian q (D ⧸ Subgroup.center D)] [IsElementaryAbelian q (Subgroup.center D)]
    [MulDistribMulAction J D] [MulDistribMulAction J (D ⧸ Subgroup.center D)]
    (hcompat : ∀ (g : J) (x : D),
      g • (x : D ⧸ Subgroup.center D) = ((g • x : D) : D ⧸ Subgroup.center D))
    {U : Subgroup J} (hU : Nat.card U = p ^ 2) (hUexp : ∀ u ∈ U, u ^ p = 1)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {σ : J}
    (hσ : σ ∈ Subgroup.normalizer (U : Set J))
    (hσ1 : ∀ H : Subgroup J, H ≤ U → Nat.card H = p → ∃ h ∈ H, σ * h * σ⁻¹ ∉ H)
    (hσ2 : ∀ H : Subgroup J, H ≤ U → Nat.card H = p →
      ∃ h ∈ H, σ * (σ * h * σ⁻¹) * σ⁻¹ ∉ H)
    (hUZ : ∀ u ∈ U, ∀ z ∈ Subgroup.center D, u • z = z)
    (hnt : ∃ u ∈ U, ∃ x : D,
      u • (x : D ⧸ Subgroup.center D) ≠ (x : D ⧸ Subgroup.center D)) :
    ∃ E : Subgroup D, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ Subgroup.center D ≤ E ∧
      q ^ 3 * Nat.card (Subgroup.center D) ≤ Nat.card E := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  have hpF : ((p : ℕ) : ZMod q) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  let ρ : J →* Module.End (ZMod q) (Additive (D ⧸ Subgroup.center D)) :=
    Theory.Representation.ofElementaryAbelianAction (p := q) (A := J)
      (G := D ⧸ Subgroup.center D)
  obtain ⟨β, hβ⟩ := exists_comm_pairing q hcl
  have hρ : ∀ (g : J) (x : D), ρ g (Additive.ofMul (x : D ⧸ Subgroup.center D)) =
      Additive.ofMul ((g • x : D) : D ⧸ Subgroup.center D) := fun g x => by
    rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul, hcompat]
  have hsurj : ∀ v : Additive (D ⧸ Subgroup.center D),
      ∃ x : D, Additive.ofMul (x : D ⧸ Subgroup.center D) = v := fun v => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, by rw [hx]; rfl⟩
  have hinv : ∀ u ∈ U, ∀ v w, β (ρ u v) (ρ u w) = β v w := by
    intro u hu v w
    obtain ⟨x, rfl⟩ := hsurj v
    obtain ⟨y, rfl⟩ := hsurj w
    rw [hρ, hρ, hβ, hβ]
    congr 2
    rw [smul_commutator, hUZ u hu _ (hcl x y)]
  have halt : ∀ v, β v v = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := hsurj v
    rw [hβ]
    have : (⟨⁅x, x⁆, hcl x x⟩ : Subgroup.center D) = 1 := Subtype.ext (by simp)
    rw [this]
    rfl
  have hnt' : ∃ u ∈ U, ρ u ≠ 1 := by
    obtain ⟨u, hu, x, hx⟩ := hnt
    refine ⟨u, hu, fun h => hx ?_⟩
    have h1 := congrArg (fun T : Module.End (ZMod q) (Additive (D ⧸ Subgroup.center D)) =>
      T (Additive.ofMul (x : D ⧸ Subgroup.center D))) h
    have h2 : ρ u (Additive.ofMul (x : D ⧸ Subgroup.center D)) =
        Additive.ofMul (u • (x : D ⧸ Subgroup.center D)) :=
      Theory.Representation.ofElementaryAbelianAction_apply_ofMul u _
    simp only [h2, Module.End.one_apply] at h1
    exact Additive.ofMul.injective h1
  obtain ⟨S, hS3, hSiso⟩ := PlaneModule.exists_isotropic_three hpF ρ β hinv halt hU hUexp hcomm
    hσ hσ1 hσ2 hnt'
  let Ssub : Subgroup (D ⧸ Subgroup.center D) :=
    { carrier := {x | Additive.ofMul x ∈ S}
      mul_mem' := fun {a b} ha hb => S.add_mem ha hb
      one_mem' := S.zero_mem
      inv_mem' := fun {a} ha => S.neg_mem ha }
  refine ⟨Ssub.comap (QuotientGroup.mk' (Subgroup.center D)), ?_, ?_, ?_⟩
  · intro x hx y hy
    have h1 : β (Additive.ofMul (x : D ⧸ Subgroup.center D))
        (Additive.ofMul (y : D ⧸ Subgroup.center D)) = 0 := hSiso _ hx _ hy
    rw [hβ] at h1
    have h2 : ⁅x, y⁆ = 1 := congrArg (fun z : Additive (Subgroup.center D) => (z.toMul : D)) h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2)
  · intro z hz
    show Additive.ofMul (QuotientGroup.mk' (Subgroup.center D) z) ∈ S
    have h : (QuotientGroup.mk' (Subgroup.center D)) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [h]
    exact S.zero_mem
  · have h1 := QuotientGroup.card_preimage_mk (Subgroup.center D)
      (Ssub : Set (D ⧸ Subgroup.center D))
    have h2 : Nat.card (Ssub : Set (D ⧸ Subgroup.center D)) = q ^ 3 := by
      have h3 := Module.natCard_eq_pow_finrank (K := ZMod q) (V := S)
      rw [Nat.card_zmod, hS3] at h3
      rw [← h3]
      exact Nat.card_congr
        { toFun := fun x => ⟨Additive.ofMul x.1, x.2⟩
          invFun := fun s => ⟨Additive.toMul s.1, s.2⟩
          left_inv := fun x => rfl
          right_inv := fun s => rfl }
    have h4 : Nat.card (Ssub.comap (QuotientGroup.mk' (Subgroup.center D))) =
        Nat.card (QuotientGroup.mk ⁻¹' (Ssub : Set (D ⧸ Subgroup.center D))) := rfl
    rw [h4, h1, h2, mul_comm]

end Actions

end CFSG.LocalAnalysis.RankThreeTheoremC
