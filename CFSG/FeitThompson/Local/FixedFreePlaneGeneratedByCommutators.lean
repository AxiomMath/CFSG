module

public import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
public import CFSG.FeitThompson.Local.CoprimeDisplacementFixedInDerived

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

section Additive

variable {A V : Type*} [Group A] [AddCommGroup V] [DistribMulAction A V] {A₁ A₂ : Subgroup A}

theorem smul_mem_displacementAddSubgroup_of_commute
    (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y) {a : A} (ha : a ∈ A₁) {v : V}
    (hv : v ∈ displacementAddSubgroup A₂ V) : a • v ∈ displacementAddSubgroup A₂ V := by
  have h : displacementAddSubgroup A₂ V
      ≤ (displacementAddSubgroup A₂ V).comap (DistribSMul.toAddMonoidHom V a) := by
    refine displacementAddSubgroup_le fun b w => ?_
    have hb : a • ((b : A) • w) = (b : A) • (a • w) := by
      rw [smul_smul, smul_smul, ((hcomm a ha b b.2).symm).eq]
    simp only [AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply, smul_sub,
      Subgroup.smul_def, hb]
    exact sub_mem_displacementAddSubgroup b (a • w)
  exact h hv

theorem smul_mem_fixedPoints_addSubgroup_of_commute
    (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y) {a : A} (ha : a ∈ A₁) {v : V}
    (hv : v ∈ FixedPoints.addSubgroup A₂ V) : a • v ∈ FixedPoints.addSubgroup A₂ V := by
  simp only [FixedPoints.mem_addSubgroup, Subgroup.smul_def] at hv ⊢
  intro b
  rw [smul_smul, ((hcomm a ha b b.2).symm).eq, ← smul_smul, hv b]

theorem inf_fixedPoints_addSubgroup_eq (hgen : A₁ ⊔ A₂ = ⊤) :
    FixedPoints.addSubgroup A₁ V ⊓ FixedPoints.addSubgroup A₂ V
      = FixedPoints.addSubgroup A V := by
  refine le_antisymm (fun v hv => ?_) fun v hv => ?_
  · rw [AddSubgroup.mem_inf] at hv
    obtain ⟨h₁, h₂⟩ := hv
    simp only [FixedPoints.mem_addSubgroup, Subgroup.smul_def] at h₁ h₂
    have hle : A₁ ⊔ A₂ ≤ MulAction.stabilizer A v :=
      sup_le (fun x hx => MulAction.mem_stabilizer_iff.2 (h₁ ⟨x, hx⟩))
        fun y hy => MulAction.mem_stabilizer_iff.2 (h₂ ⟨y, hy⟩)
    rw [hgen, top_le_iff] at hle
    exact (FixedPoints.mem_addSubgroup A V v).2 fun a =>
      MulAction.mem_stabilizer_iff.1 (hle ▸ Subgroup.mem_top a)
  · rw [FixedPoints.mem_addSubgroup] at hv
    exact AddSubgroup.mem_inf.2
      ⟨(FixedPoints.mem_addSubgroup _ _ _).2 fun a => hv (a : A),
        (FixedPoints.mem_addSubgroup _ _ _).2 fun a => hv (a : A)⟩

private theorem eq_of_isCompl_of_add_eq_add {C D : AddSubgroup V} (h : IsCompl C D)
    {x x' y y' : V} (hx : x ∈ C) (hx' : x' ∈ C) (hy : y ∈ D) (hy' : y' ∈ D)
    (hsum : x + y = x' + y') : x = x' := by
  have hd : x - x' ∈ C := AddSubgroup.sub_mem C hx hx'
  have hd' : x - x' = y' - y := by linear_combination (norm := abel) hsum
  have hmem : x - x' ∈ C ⊓ D :=
    AddSubgroup.mem_inf.2 ⟨hd, hd' ▸ AddSubgroup.sub_mem D hy' hy⟩
  rw [h.inf_eq_bot, AddSubgroup.mem_bot, sub_eq_zero] at hmem
  exact hmem

theorem fixedPoints_addSubgroup_le_displacementAddSubgroup [Finite V] [Finite A₂]
    (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (hcop : (Nat.card A₂).Coprime (Nat.card V))
    (hfix : FixedPoints.addSubgroup A₁ V ⊓ FixedPoints.addSubgroup A₂ V = ⊥) :
    FixedPoints.addSubgroup A₁ V ≤ displacementAddSubgroup A₂ V := by
  intro c hc
  have hcfix : ∀ a ∈ A₁, a • c = c := fun a ha => by
    simpa [Subgroup.smul_def] using (FixedPoints.mem_addSubgroup _ _ _).1 hc ⟨a, ha⟩
  have h2 := isCompl_fixedPoints_displacementAddSubgroup (B := A₂) (V := V) hcop
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    AddSubgroup.mem_sup.1 (h2.sup_eq_top ▸ AddSubgroup.mem_top c)
  have hx1 : x ∈ FixedPoints.addSubgroup A₁ V := by
    rw [FixedPoints.mem_addSubgroup]
    intro a
    rw [Subgroup.smul_def]
    refine eq_of_isCompl_of_add_eq_add h2
      (smul_mem_fixedPoints_addSubgroup_of_commute hcomm a.2 hx) hx
      (smul_mem_displacementAddSubgroup_of_commute hcomm a.2 hy) hy ?_
    rw [← smul_add, hxy, hcfix _ a.2]
  have hx0 : x = 0 := by
    have h := hfix ▸ AddSubgroup.mem_inf.2 ⟨hx1, hx⟩
    simpa using h
  rw [← hxy, hx0, zero_add]
  exact hy

theorem sup_displacementAddSubgroup_eq_top [Finite V] [Finite A₁] [Finite A₂]
    (hgen : A₁ ⊔ A₂ = ⊤) (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (hcop₁ : (Nat.card A₁).Coprime (Nat.card V))
    (hcop₂ : (Nat.card A₂).Coprime (Nat.card V))
    (hfix : FixedPoints.addSubgroup A V = ⊥) :
    displacementAddSubgroup A₁ V ⊔ displacementAddSubgroup A₂ V = ⊤ := by
  have hle : FixedPoints.addSubgroup A₁ V ≤ displacementAddSubgroup A₂ V :=
    fixedPoints_addSubgroup_le_displacementAddSubgroup hcomm hcop₂
      (by rw [inf_fixedPoints_addSubgroup_eq hgen, hfix])
  rw [eq_top_iff, ← sup_fixedPoints_displacementAddSubgroup_eq_top (B := A₁) (V := V) hcop₁]
  exact sup_le (hle.trans le_sup_right) le_sup_left

end Additive

section Multiplicative

open Pointwise

variable {A V : Type*} [Group A] [CommGroup V] [MulDistribMulAction A V] {A₁ A₂ : Subgroup A}
  {p : ℕ}

private instance distribMulActionAdditive {M N : Type*} [Monoid M] [CommGroup N]
    [MulDistribMulAction M N] : DistribMulAction M (Additive N) where
  smul m x := Additive.ofMul (m • x.toMul)
  one_smul x := by
    change Additive.ofMul ((1 : M) • x.toMul) = x
    rw [one_smul, ofMul_toMul]
  mul_smul m n x := by
    change Additive.ofMul ((m * n) • x.toMul)
      = Additive.ofMul (m • (Additive.ofMul (n • x.toMul)).toMul)
    rw [mul_smul, toMul_ofMul]
  smul_zero m := by
    change Additive.ofMul (m • (1 : N)) = 0
    rw [smul_one]; rfl
  smul_add m x y := by
    change Additive.ofMul (m • (x.toMul * y.toMul)) = _
    rw [smul_mul']; rfl

private theorem ofMul_smul {M N : Type*} [Monoid M] [CommGroup N] [MulDistribMulAction M N]
    (m : M) (v : N) : Additive.ofMul (m • v) = m • Additive.ofMul v := rfl

private theorem toMul_smul {M N : Type*} [Monoid M] [CommGroup N] [MulDistribMulAction M N]
    (m : M) (x : Additive N) : (m • x).toMul = m • x.toMul := rfl

private theorem toAddSubgroup_fixedPoints (B : Type*) [Monoid B] [MulDistribMulAction B V] :
    (FixedPoints.subgroup B V).toAddSubgroup = FixedPoints.addSubgroup B (Additive V) := by
  ext x
  rw [show (x ∈ (FixedPoints.subgroup B V).toAddSubgroup) ↔ x.toMul ∈ FixedPoints.subgroup B V
    from Iff.rfl, FixedPoints.mem_subgroup, FixedPoints.mem_addSubgroup]
  exact ⟨fun h m => Additive.toMul.injective (by rw [toMul_smul, h m]),
    fun h m => by rw [← toMul_smul, h m]⟩

private theorem ofMul_inv_mul_smul (a : A) (v : V) :
    Additive.ofMul (v⁻¹ * a • v) = a • Additive.ofMul v - Additive.ofMul v := by
  rw [mul_comm, ← div_eq_mul_inv, ofMul_div, ofMul_smul]

private theorem toAddSubgroup_smulDisplacementSubgroup (A₁ : Subgroup A) :
    (smulDisplacementSubgroup A₁ V).toAddSubgroup
      = displacementAddSubgroup A₁ (Additive V) := by
  rw [smulDisplacementSubgroup_eq_closure, Subgroup.toAddSubgroup_closure,
    displacementAddSubgroup_eq_closure]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, v, hv⟩
    exact ⟨a, Additive.ofMul v, by rw [← ofMul_inv_mul_smul, hv, ofMul_toMul]⟩
  · rintro ⟨a, v, hv⟩
    refine ⟨a, v.toMul, ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_inv_mul_smul, ofMul_toMul, hv, ofMul_toMul]

theorem sup_smulDisplacementSubgroup_eq_top [Finite V] [Finite A₁] [Finite A₂]
    (hgen : A₁ ⊔ A₂ = ⊤) (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (hcop₁ : (Nat.card A₁).Coprime (Nat.card V))
    (hcop₂ : (Nat.card A₂).Coprime (Nat.card V))
    (hfix : FixedPoints.subgroup A V = ⊥) :
    smulDisplacementSubgroup A₁ V ⊔ smulDisplacementSubgroup A₂ V = ⊤ := by
  have hcard : Nat.card (Additive V) = Nat.card V := Nat.card_congr Additive.toMul
  have hfix' : FixedPoints.addSubgroup A (Additive V) = ⊥ := by
    rw [← toAddSubgroup_fixedPoints, hfix, map_bot]
  have h := sup_displacementAddSubgroup_eq_top (A₁ := A₁) (A₂ := A₂) (V := Additive V)
    hgen hcomm (by rwa [hcard]) (by rwa [hcard]) hfix'
  rw [← toAddSubgroup_smulDisplacementSubgroup, ← toAddSubgroup_smulDisplacementSubgroup,
    ← map_sup] at h
  rw [← (Subgroup.toAddSubgroup (G := V)).injective.eq_iff, h, map_top]

theorem coe_mul_coe_smulDisplacementSubgroup [Finite V] [Finite A₁] [Finite A₂]
    (hgen : A₁ ⊔ A₂ = ⊤) (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (hcop₁ : (Nat.card A₁).Coprime (Nat.card V))
    (hcop₂ : (Nat.card A₂).Coprime (Nat.card V))
    (hfix : FixedPoints.subgroup A V = ⊥) :
    (smulDisplacementSubgroup A₁ V : Set V) * (smulDisplacementSubgroup A₂ V : Set V)
      = Set.univ := by
  rw [← Subgroup.mul_normal (smulDisplacementSubgroup A₁ V) (smulDisplacementSubgroup A₂ V),
    sup_smulDisplacementSubgroup_eq_top hgen hcomm hcop₁ hcop₂ hfix]
  exact Subgroup.coe_top

theorem sup_smulDisplacementSubgroup_eq_top_of_card_eq_prime [Finite V] (hp : p.Prime)
    (h₁ : Nat.card A₁ = p) (h₂ : Nat.card A₂ = p)
    (hgen : A₁ ⊔ A₂ = ⊤) (_hdisj : A₁ ⊓ A₂ = ⊥)
    (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y)
    (hdvd : ¬ p ∣ Nat.card V) (hfix : FixedPoints.subgroup A V = ⊥) :
    smulDisplacementSubgroup A₁ V ⊔ smulDisplacementSubgroup A₂ V = ⊤ := by
  have hf₁ : Finite A₁ := Nat.finite_of_card_ne_zero (by rw [h₁]; exact hp.ne_zero)
  have hf₂ : Finite A₂ := Nat.finite_of_card_ne_zero (by rw [h₂]; exact hp.ne_zero)
  exact sup_smulDisplacementSubgroup_eq_top hgen hcomm
    (h₁ ▸ hp.coprime_iff_not_dvd.2 hdvd) (h₂ ▸ hp.coprime_iff_not_dvd.2 hdvd) hfix

end Multiplicative

section MonoidHomVersion

variable {A V : Type*} [Group A] [CommGroup V] {A₁ A₂ : Subgroup A} {p : ℕ}

theorem sup_closure_inv_mul_smul_eq_top_of_card_eq_prime [Finite V] (ρ : A →* MulAut V)
    (hp : p.Prime) (h₁ : Nat.card A₁ = p) (h₂ : Nat.card A₂ = p)
    (hgen : A₁ ⊔ A₂ = ⊤) (_hdisj : A₁ ⊓ A₂ = ⊥)
    (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, Commute x y) (hdvd : ¬ p ∣ Nat.card V)
    (hfix : ∀ v : V, (∀ a : A, ρ a v = v) → v = 1) :
    Subgroup.closure {x : V | ∃ a ∈ A₁, ∃ v : V, v⁻¹ * ρ a v = x}
      ⊔ Subgroup.closure {x : V | ∃ a ∈ A₂, ∃ v : V, v⁻¹ * ρ a v = x} = ⊤ := by
  let inst : MulDistribMulAction A V := MulDistribMulAction.compHom V ρ
  have hgens : ∀ B : Subgroup A, smulDisplacementSubgroup B V
      = Subgroup.closure {x : V | ∃ a ∈ B, ∃ v : V, v⁻¹ * ρ a v = x} := by
    intro B
    rw [smulDisplacementSubgroup_eq_closure]
    congr 1
    ext x
    exact ⟨fun ⟨a, v, hv⟩ => ⟨a, a.2, v, hv⟩, fun ⟨a, ha, v, hv⟩ => ⟨⟨a, ha⟩, v, hv⟩⟩
  have hbot : FixedPoints.subgroup A V = ⊥ := by
    rw [eq_bot_iff]
    exact fun v hv => Subgroup.mem_bot.2 (hfix v ((FixedPoints.mem_subgroup A V v).1 hv))
  rw [← hgens, ← hgens]
  exact sup_smulDisplacementSubgroup_eq_top_of_card_eq_prime hp h₁ h₂ hgen _hdisj hcomm hdvd hbot

end MonoidHomVersion

end
end CFSG.FeitThompson
