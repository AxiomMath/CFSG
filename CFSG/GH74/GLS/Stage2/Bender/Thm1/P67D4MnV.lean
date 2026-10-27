module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4VNormal
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4WeylCases
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.RankThree.PartOne.KGD.D4QFrame
public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

section Abstract

variable {Y : Type} [Group Y]

theorem mulAut_pow_apply_mem_of_stable {N : Subgroup Y} {δ : MulAut Y}
    (hN : ∀ n ∈ N, δ n ∈ N) (j : ℕ) : ∀ n ∈ N, (δ ^ j) n ∈ N := by
  induction j with
  | zero => intro n hn; simpa using hn
  | succ j ih => intro n hn; rw [pow_succ, MulAut.mul_apply]; exact ih _ (hN n hn)

theorem conj_mul_pow_mul_conj_mul_pow (δ : MulAut Y) (g h : Y) (j k : ℕ) :
    (MulAut.conj g * δ ^ j) * (MulAut.conj h * δ ^ k) =
      MulAut.conj (g * (δ ^ j) h) * δ ^ (j + k) := by
  calc (MulAut.conj g * δ ^ j) * (MulAut.conj h * δ ^ k)
      = MulAut.conj g * (δ ^ j * MulAut.conj h) * δ ^ k := by simp only [mul_assoc]
    _ = MulAut.conj g * (MulAut.conj ((δ ^ j) h) * δ ^ j) * δ ^ k := by
        rw [CFSG.LieType.Chevalley.mulAut_mul_conj]
    _ = MulAut.conj (g * (δ ^ j) h) * δ ^ (j + k) := by
        rw [map_mul, pow_add]; simp only [mul_assoc]

@[expose] def conjPowSubgroup (δ : MulAut Y) (hδ : δ ^ 3 = 1) (N : Subgroup Y)
    (hN : ∀ n ∈ N, δ n ∈ N) : Subgroup (MulAut Y) where
  carrier := {α | ∃ g ∈ N, ∃ j : ℕ, α = MulAut.conj g * δ ^ j}
  mul_mem' := by
    rintro _ _ ⟨g, hg, j, rfl⟩ ⟨g', hg', k, rfl⟩
    exact ⟨g * (δ ^ j) g', mul_mem hg (mulAut_pow_apply_mem_of_stable hN j g' hg'), j + k,
      conj_mul_pow_mul_conj_mul_pow δ g g' j k⟩
  one_mem' := ⟨1, one_mem _, 0, by rw [map_one, pow_zero, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨g, hg, j, rfl⟩
    have hinv : (δ ^ j)⁻¹ = δ ^ (2 * j) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hδ, one_pow]
    refine ⟨(δ ^ (2 * j)) g⁻¹, mulAut_pow_apply_mem_of_stable hN _ _ (inv_mem hg), 2 * j, ?_⟩
    rw [mul_inv_rev, ← map_inv, hinv]
    exact CFSG.LieType.Chevalley.mulAut_mul_conj _ _

@[expose] def innPowSubgroup (δ : MulAut Y) (hδ : δ ^ 3 = 1) : Subgroup (MulAut Y) :=
  conjPowSubgroup δ hδ ⊤ (fun _ _ => Subgroup.mem_top _)

theorem relIndex_conjPowSubgroup {δ : MulAut Y} (hδ : δ ^ 3 = 1)
    (hinn : ∀ (h : Y) (j : ℕ), MulAut.conj h = δ ^ j → h = 1)
    {N : Subgroup Y} (hN : ∀ n ∈ N, δ n ∈ N) :
    (conjPowSubgroup δ hδ N hN).relIndex (innPowSubgroup δ hδ) = N.index := by
  set A := innPowSubgroup δ hδ
  set B := conjPowSubgroup δ hδ N hN
  have hconjA : ∀ y : Y, MulAut.conj y ∈ A := fun y =>
    ⟨y, Subgroup.mem_top _, 0, by rw [pow_zero, mul_one]⟩
  let Φ : Y ⧸ N → A ⧸ B.subgroupOf A :=
    Quotient.lift (fun y => (QuotientGroup.mk ⟨MulAut.conj y, hconjA y⟩ : A ⧸ B.subgroupOf A))
      (fun a b hab => QuotientGroup.eq.2 (by
        have h := QuotientGroup.leftRel_apply.1 hab
        rw [Subgroup.mem_subgroupOf]
        exact ⟨a⁻¹ * b, h, 0, by simp⟩))
  have hinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
    refine QuotientGroup.eq.2 ?_
    have h := QuotientGroup.eq.1 hab
    rw [Subgroup.mem_subgroupOf] at h
    obtain ⟨g, hg, j, hgj⟩ := h
    have h1 : MulAut.conj (g⁻¹ * (y⁻¹ * y')) = δ ^ j := by
      rw [map_mul, map_mul, map_inv, map_inv]
      have hgj' : (MulAut.conj y)⁻¹ * MulAut.conj y' = MulAut.conj g * δ ^ j := hgj
      rw [hgj', inv_mul_cancel_left]
    have h2 := hinn _ _ h1
    have h3 : y⁻¹ * y' = g := by
      have := congrArg (g * ·) h2
      simpa using this
    rw [h3]
    exact hg
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨α, hα⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, -, j, rfl⟩ := hα
    refine ⟨QuotientGroup.mk y, QuotientGroup.eq.2 ?_⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨1, one_mem _, j, by simp⟩
  show (B.subgroupOf A).index = N.index
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

theorem exists_mem_conj_mem_of_relIndex {G : Type} [Group G] (A B V : Subgroup G) [Finite A]
    (hB : ¬ 3 ∣ B.relIndex A) (hVA : V ≤ A) (hV : ∀ x ∈ V, x ^ 3 = 1) :
    ∃ β ∈ A, ∀ x ∈ V, β⁻¹ * x * β ∈ B := by
  have hP : IsPGroup 3 (V.subgroupOf A) := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    have := hV _ (Subgroup.mem_subgroupOf.1 x.2)
    simpa using this
  obtain ⟨β, hβ⟩ := exists_conj_mem_of_isPGroup_three (B.subgroupOf A) hB (V.subgroupOf A) hP
  refine ⟨β.1, β.2, fun x hx => ?_⟩
  have := hβ ⟨x, hVA hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  exact Subgroup.mem_subgroupOf.1 this

theorem exists_conj_mem_conjPowSubgroup [Finite Y] {δ : MulAut Y} (hδ : δ ^ 3 = 1)
    (hinn : ∀ (h : Y) (j : ℕ), MulAut.conj h = δ ^ j → h = 1)
    {N : Subgroup Y} (hidx : ¬ 3 ∣ N.index) (hN : ∀ n ∈ N, δ n ∈ N)
    {V : Subgroup (MulAut Y)} (hVA : V ≤ innPowSubgroup δ hδ) (hV : ∀ x ∈ V, x ^ 3 = 1) :
    ∃ β : MulAut Y, ∀ x ∈ V, ∃ g ∈ N, ∃ j : ℕ, β⁻¹ * x * β = MulAut.conj g * δ ^ j := by
  have hidx' : ¬ 3 ∣ (conjPowSubgroup δ hδ N hN).relIndex (innPowSubgroup δ hδ) := by
    rw [relIndex_conjPowSubgroup hδ hinn hN]
    exact hidx
  obtain ⟨β, -, hβ⟩ := exists_mem_conj_mem_of_relIndex (innPowSubgroup δ hδ)
    (conjPowSubgroup δ hδ N hN) V hidx' hVA hV
  exact ⟨β, hβ⟩

end Abstract

section Cube

variable {G : Type*} [Group G] {σ : G}

theorem pow_eq_one_or_eq_or_eq_inv_of_pow_three_eq_one (hσ : σ ^ 3 = 1) (j : ℕ) :
    σ ^ j = 1 ∨ σ ^ j = σ ∨ σ ^ j = σ⁻¹ := by
  have hinv : σ⁻¹ = σ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hσ)
  have h : σ ^ j = σ ^ (j % 3) := by
    conv_lhs => rw [← Nat.div_add_mod j 3, pow_add, pow_mul, hσ, one_pow, one_mul]
  rw [h, hinv]
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h0 | h0
  · left; rw [h0, pow_zero]
  · right; left; rw [h0, pow_one]
  · right; right; rw [h0]

theorem exists_pow_eq_of_eq_one_or_eq_or_eq_inv {δ : G} (hσ : σ ^ 3 = 1)
    (h : δ = 1 ∨ δ = σ ∨ δ = σ⁻¹) : ∃ j : ℕ, δ = σ ^ j := by
  have hinv : σ⁻¹ = σ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hσ)
  rcases h with h | h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩
  · exact ⟨2, by rw [h, hinv]⟩

end Cube

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem d4_exists_conj_le_Bδ {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hidx : ¬ 3 ∣ N.index)
    (hstab : ∀ n ∈ N, fieldActor (t := TwistTag.D4) σ σ n ∈ N)
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hV : ∀ x ∈ V, x ^ 3 = 1) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∀ x ∈ V,
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K), g ∈ N ∧
        (δ = 1 ∨ δ = σ ∨ δ = σ⁻¹) ∧
        β⁻¹ * x * β = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
  classical
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -, -⟩, hcyc, hcard, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hδ3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := d4_fieldActor_pow_three K hK σ hσ
  have hσ3 : σ ^ 3 = 1 := RingEquiv.ext fun c => by
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 :=
    ringEquiv_ne_one_of_pow (Nat.one_lt_pow (by omega) hp.one_lt) hK σ hσ
  have hpow : ∀ j : ℕ, fieldActor (t := TwistTag.D4) σ σ ^ j = fieldActor σ (σ ^ j) := fun j =>
    (map_pow (fieldActorHom (t := TwistTag.D4) σ) σ j).symm
  have hinn : ∀ (h : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (j : ℕ),
      MulAut.conj h = fieldActor (t := TwistTag.D4) σ σ ^ j → h = 1 := by
    intro h j hj
    have h1 : MulAut.conj h = MulAut.conj h * fieldActor (t := TwistTag.D4) σ 1 := by
      rw [fieldActor_one, mul_one]
    have h2 : MulAut.conj h = MulAut.conj 1 * fieldActor (t := TwistTag.D4) σ (σ ^ j) := by
      rw [hj, hpow, map_one, one_mul]
    exact congrArg Prod.fst ((hNF (MulAut.conj h)).unique
      (y₁ := (h, 1)) (y₂ := (1, σ ^ j)) h1 h2)
  have hVA : V ≤ innPowSubgroup (fieldActor (t := TwistTag.D4) σ σ) hδ3 := by
    intro x hx
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF x
    have hΘx : Θ x = δ := hΘ x g δ hgδ
    have hδ3' : δ ^ 3 = 1 := by rw [← hΘx, ← map_pow, hV x hx, map_one]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, δ = σ ^ j := by
      by_cases hδ1 : δ = 1
      · exact ⟨0, by rw [hδ1, pow_zero]⟩
      · exact exists_pow_eq_of_eq_one_or_eq_or_eq_inv hσ3
          (Or.inr (eq_or_eq_inv_of_pow_three_eq_one hσ1 hσ3 hδ1 hδ3'))
    exact ⟨g, Subgroup.mem_top _, j, by rw [hgδ, hj, hpow]⟩
  obtain ⟨β, hβ⟩ := exists_conj_mem_conjPowSubgroup hδ3 hinn hidx hstab hVA hV
  refine ⟨β, fun x hx => ?_⟩
  obtain ⟨g, hg, j, hgj⟩ := hβ x hx
  exact ⟨g, σ ^ j, hg, pow_eq_one_or_eq_or_eq_inv_of_pow_three_eq_one hσ3 j, by
    rw [hgj, hpow]⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
