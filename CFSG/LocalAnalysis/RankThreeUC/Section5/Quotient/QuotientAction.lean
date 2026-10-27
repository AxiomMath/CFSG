module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialBinaryActionCounterexample

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace Quotient

open scoped commutatorElement

variable {G : Type} [Group G]

abbrev Pbar (P : Subgroup G) : Type := ↥P ⧸ Subgroup.center ↥P

theorem mem_centerP {P : Subgroup G} {x : G} :
    x ∈ centerP P ↔ ∃ h : x ∈ P, (⟨x, h⟩ : P) ∈ Subgroup.center ↥P := by
  unfold centerP
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem commutator_mem_center {P : Subgroup G} (h : ⁅⁅P, P⁆, P⁆ = ⊥) (x y : P) :
    ⁅x, y⁆ ∈ Subgroup.center ↥P := by
  rw [Subgroup.mem_center_iff]
  intro z
  have hxy : ((⁅x, y⁆ : P) : G) ∈ ⁅P, P⁆ :=
    Subgroup.commutator_mem_commutator x.2 y.2
  have : ⁅((⁅x, y⁆ : P) : G), (z : G)⁆ ∈ ⁅⁅P, P⁆, P⁆ :=
    Subgroup.commutator_mem_commutator hxy z.2
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact Subtype.ext (by simpa using this.symm)

instance instCommGroupPbar (P : Subgroup G) [Fact (⁅⁅P, P⁆, P⁆ = ⊥)] : CommGroup (Pbar P) :=
  { (inferInstance : Group (Pbar P)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | _ x => ?_
      induction b using QuotientGroup.induction_on with | _ y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h3 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [h3]
      exact commutator_mem_center (Fact.out : ⁅⁅P, P⁆, P⁆ = ⊥) _ _ }

instance instModulePbar (P : Subgroup G) (p : ℕ) [Fact p.Prime] [Fact (⁅⁅P, P⁆, P⁆ = ⊥)]
    [Fact (Monoid.exponent ↥P = p)] : Module (ZMod p) (Additive (Pbar P)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    induction x using Additive.rec with | _ x => ?_
    induction x using QuotientGroup.induction_on with | _ g => ?_
    show Additive.ofMul ((QuotientGroup.mk g) ^ p) = 0
    rw [← QuotientGroup.mk_pow]
    have : g ^ p = 1 := by
      have := Monoid.pow_exponent_eq_one g
      rwa [Fact.out (p := Monoid.exponent ↥P = p)] at this
    rw [this]; rfl

section Action

variable {P B : Subgroup G}

@[expose] def conjAut (hB : B ≤ Subgroup.normalizer (P : Set G)) (b : B) : P ≃* P :=
  P.normalizerMonoidHom ⟨b, hB b.2⟩

theorem conjAut_apply (hB : B ≤ Subgroup.normalizer (P : Set G)) (b : B) (x : P) :
    ((conjAut hB b x : P) : G) = b * x * b⁻¹ := rfl

@[expose] def actionMul (hB : B ≤ Subgroup.normalizer (P : Set G)) : B →* MulAut (Pbar P) where
  toFun b := QuotientGroup.congr (Subgroup.center ↥P) (Subgroup.center ↥P) (conjAut hB b)
    (Subgroup.map_center_eq _)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | _ x => ?_
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simp [conjAut_apply]
  map_mul' b c := by
    ext x
    induction x using QuotientGroup.induction_on with | _ x => ?_
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simp [conjAut_apply, mul_assoc]

theorem actionMul_mk (hB : B ≤ Subgroup.normalizer (P : Set G)) (b : B) (x : P) :
    actionMul hB b (QuotientGroup.mk x) = QuotientGroup.mk (conjAut hB b x) := rfl

variable {p : ℕ} [Fact p.Prime] [Fact (⁅⁅P, P⁆, P⁆ = ⊥)] [Fact (Monoid.exponent ↥P = p)]

@[expose] def linearOfMulAut (f : MulAut (Pbar P)) :
    Additive (Pbar P) ≃ₗ[ZMod p] Additive (Pbar P) :=
  { MulEquiv.toAdditive f with
    map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive f).toAddMonoidHom c x }

@[expose] def action (p : ℕ) [Fact p.Prime] [Fact (⁅⁅P, P⁆, P⁆ = ⊥)] [Fact (Monoid.exponent ↥P = p)]
    (hB : B ≤ Subgroup.normalizer (P : Set G)) :
    B →* (Additive (Pbar P) ≃ₗ[ZMod p] Additive (Pbar P)) where
  toFun b := linearOfMulAut (actionMul hB b)
  map_one' := by rw [map_one]; exact LinearEquiv.ext fun x => rfl
  map_mul' b c := by rw [map_mul]; exact LinearEquiv.ext fun x => rfl

theorem action_apply (hB : B ≤ Subgroup.normalizer (P : Set G)) (b : B) (x : Pbar P) :
    action p hB b (Additive.ofMul x) = Additive.ofMul (actionMul hB b x) := by
  simp [action, linearOfMulAut]

theorem fixed_iff_commutator_mem_center (hB : B ≤ Subgroup.normalizer (P : Set G)) (b : B)
    {g : G} (hg : g ∈ P) :
    action p hB b (Additive.ofMul (QuotientGroup.mk ⟨g, hg⟩)) =
        Additive.ofMul (QuotientGroup.mk ⟨g, hg⟩) ↔
      (b : G) * g * (b : G)⁻¹ * g⁻¹ ∈ centerP P := by
  have h1 : (b : G) * g * (b : G)⁻¹ * g⁻¹ ∈ P :=
    P.mul_mem (((Subgroup.mem_normalizer_iff.mp (hB b.2)) g).mp hg) (P.inv_mem hg)
  have h2 : conjAut hB b ⟨g, hg⟩ / ⟨g, hg⟩ = (⟨_, h1⟩ : P) :=
    Subtype.ext (by simp [conjAut_apply, div_eq_mul_inv])
  rw [action_apply, actionMul_mk, Equiv.apply_eq_iff_eq, QuotientGroup.eq_iff_div_mem, h2,
    mem_centerP]
  exact ⟨fun h => ⟨h1, h⟩, fun ⟨_, h⟩ => h⟩

theorem nontrivial_Pbar_of_extraspecial (hP : CFSG.IsExtraspecialPGroup p ↥P) :
    Nontrivial (Pbar P) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hc : Subgroup.center ↥P = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have h1 : commutator ↥P = ⊥ := (_root_.commutator_eq_bot_iff_center_eq_top ↥P).mpr hc
  have h2 : Subgroup.center ↥P = ⊥ := by rw [← hP.2.1, h1]
  have h3 := hP.2.2.2
  rw [h2, Subgroup.card_bot] at h3
  exact (Fact.out : p.Prime).one_lt.ne h3

end Action
end Quotient
end Section5
end CFSG.LocalAnalysis.RankThreeUC
