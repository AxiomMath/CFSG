module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4F
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SympU4Surv
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTExcl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

variable {p f : ℕ} {K : Type} [Field K]

theorem card_statedProj_three_three [Fact (3 : ℕ).Prime] (hK : Nat.card K = (3 ^ 1) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (3 ^ 1) K)) = 6048 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 3) Fact.out
    le_rfl hK (by norm_num)]
  decide

theorem not_kindFactorAll_psu3 {k : Kind} (hk : IsClassicalKind k) [Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2) :
    ¬ KindFactorAll k (StatedProj (StatedSU 3 (p ^ f) K)) := by
  have hp : p.Prime := Fact.out
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  have hfin : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
  rcases (show 5 ≤ p ^ f ∨ p ^ f = 3 by
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have := Nat.le_self_pow (by omega : f ≠ 0) p
    omega) with h5 | h3
  · exact not_kindFactorAll hp2 (involved_qdSL_statedProj_three hK)
      (not_card_dvd_factorial_statedProj_three_odd hf hK hodd h5)
  · have hp3 : p = 3 := by
      rcases Nat.lt_or_ge 1 f with h1 | h1
      · have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos h1
        have := hp.two_le
        nlinarith
      · obtain rfl : f = 1 := by omega
        simpa using h3
    subst hp3
    have hf1 : f = 1 := by
      rcases Nat.lt_or_ge 1 f with h1 | h1
      · have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) h1
        omega
      · omega
    subst hf1
    exact not_kindFactorAll_of_card_btw hk (card_statedProj_three_three hK) 22 (by norm_num)
      (by norm_num) (by norm_num)

theorem not_admAut_of_su3 {k : Kind} (hk : IsClassicalKind k) (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {α : MulAut (hypPSU h 2 0)} (θ : ↥(StatedSU 3 (p ^ f) K) →* hypPSU h 2 0)
    (hθ : Function.Injective θ) (hfix : ∀ s ∈ θ.range, α s = s) : ¬ AdmAut k α := by
  intro hadm
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  let ψ : ↥(StatedSU 3 (p ^ f) K) →* ↥(fixSub α) :=
    θ.codRestrict _ fun g => hfix _ ⟨g, rfl⟩
  have hψ : Function.Injective ψ := fun a b hab => hθ (congrArg Subtype.val hab)
  have hq2 : p ^ f ≠ 2 := by
    have := Nat.le_self_pow (by have := h.one_le; omega : f ≠ 0) p
    have := h.prime.two_le
    have : p ≠ 2 := hp2
    omega
  have hs := isSimpleGroup_statedProj_three_odd (K := K) hK hq2
  have hP3 := isPerfect_statedSU_three_odd (K := K) hK hp2
  have : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have : Nontrivial (StatedProj (StatedSU 3 (p ^ f) K)) := IsSimpleGroup.toNontrivial
  exact not_kindFactorAll_psu3 hk hp2 h.one_le hK (hadm _ (Group.IsPerfect.not_isSolvable _)
    ⟨ψ.range, (QuotientGroup.mk' _).comp (MonoidHom.ofInjective hψ).symm.toMonoidHom,
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hψ).symm.surjective⟩)

theorem not_admAut_symp_bar {k : Kind} (hk : IsClassicalKind k) (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {A : GL (HypIndex 2 0) K} {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hA : A ∈ hypUnitary h 2 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = (-1 : K) • 1) :
    ¬ AdmAut k (semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩) := by
  intro hadm
  have := h.finite
  obtain ⟨ψ, hψc, hψs⟩ := exists_sp4_comm_of_bar h hp2 hA hAA
  have hfix := fixed_of_comm_bar h (by norm_num) (by norm_num) hσ hx ψ hψc
  obtain ⟨hsimple, hns, hbad⟩ := BS4.psp4_bad hk h.prime hp2 h.one_le h.card_fixedField
  let φ : ↥(StatedSp 2 h.fixedField) →*
      ↥(fixSub (semilinearAutHom h (by norm_num) (by norm_num) ⟨_, hx⟩)) :=
    ((hypProj h 2 0).comp ψ).codRestrict _ fun x => hfix _ ⟨x, rfl⟩
  have hle : φ.ker ≤ ((StatedScalars (Fin 2 ⊕ Fin 2) h.fixedField).subgroupOf
      (StatedSp 2 h.fixedField)).comap (MonoidHom.id (StatedSp 2 h.fixedField)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hψs x (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  let c : ↥φ.range →* StatedProj (StatedSp 2 h.fixedField) :=
    (QuotientGroup.map φ.ker _ (MonoidHom.id (StatedSp 2 h.fixedField)) hle).comp
      (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
  have hc : Function.Surjective c :=
    (QuotientGroup.map_surjective_of_surjective φ.ker
      ((StatedScalars (Fin 2 ⊕ Fin 2) h.fixedField).subgroupOf (StatedSp 2 h.fixedField))
      (MonoidHom.id (StatedSp 2 h.fixedField)) (fun t => QuotientGroup.mk_surjective t) hle).comp
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  exact hbad (hadm _ hns ⟨φ.range, c, hc⟩)

theorem survU4Orth_of_admAut {k : Kind} (hk : IsClassicalKind k) (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {u : MulAut (hypPSU h 2 0)} (hu2 : u * u = 1) (hadm : AdmAut k u) :
    SurvU4Orth h u := by
  rcases unitary4_involution_cases h hp2 u (by rw [sq]; exact hu2) with ⟨ψ, hψ, hfix⟩ | hS
  · exact absurd hadm (not_admAut_of_su3 hk h hp2 _ hψ hfix)
  · rcases hS with hS | hS | ⟨A, σ, hx, hA, hσ, c, hc, hAA, rfl⟩
    · exact Or.inl hS
    · exact Or.inr (Or.inl hS)
    · rcases eq_one_or_neg_one_of_bar h hp2 hA hc hAA with rfl | rfl
      · exact Or.inr (Or.inr ⟨A, σ, hx, hA, hσ, by rw [hAA, one_smul], rfl⟩)
      · exact absurd hadm (not_admAut_symp_bar hk h hp2 hσ hx hA hAA)

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
