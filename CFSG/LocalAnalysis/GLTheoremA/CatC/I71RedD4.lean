module

public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Lift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Gates

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem no_E9_of_orthogonalGates (Q : QuadraticForm K (Fin d → K)) {f : ℕ}
    (hG : OrthogonalGates Q f) (X : Subgroup (MulAut (matrixProjectiveDerived Q)))
    (hX : IsElemAbelian 3 X) (hXc : Nat.card X = 3 ^ 2) (hXE : X ≤ matrixProjectiveImage Q)
    (hXI : X ⊓ Inn (matrixProjectiveDerived Q) = ⊥) : False := by
  classical
  obtain ⟨-, ⟨ψ, -, hker, hcyc⟩, ⟨hInn, k, hrel⟩, -⟩ := hG
  have hXD : X ⊓ (linearConjugationHom Q).range = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxD⟩
    have hx3 : x ^ 3 = 1 := hX.2 x hxX
    set Dl := (linearConjugationHom Q).range with hDl
    set N : Subgroup ↥Dl := (Inn (matrixProjectiveDerived Q)).subgroupOf Dl with hN
    have hcard : Nat.card (↥Dl ⧸ N) = 2 ^ k := by
      rw [← Subgroup.index_eq_card]
      exact hrel
    set q : ↥Dl ⧸ N := QuotientGroup.mk ⟨x, hxD⟩ with hq
    have hq3 : q ^ 3 = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have h1 : (⟨x, hxD⟩ : ↥Dl) ^ 3 = 1 := Subtype.ext hx3
      rw [h1]
      rfl
    have hord3 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
    have hord2 : orderOf q ∣ 2 ^ k := hcard ▸ orderOf_dvd_natCard q
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have hone : orderOf q = 1 := by
      have h := Nat.dvd_gcd hord3 hord2
      rw [Nat.Coprime.gcd_eq_one hcop] at h
      exact Nat.dvd_one.1 h
    have hq1 : q = 1 := orderOf_eq_one_iff.1 hone
    have hxN : (⟨x, hxD⟩ : ↥Dl) ∈ N := (QuotientGroup.eq_one_iff _).1 hq1
    have hxI : x ∈ Inn (matrixProjectiveDerived Q) := Subgroup.mem_subgroupOf.1 hxN
    have h2 : x ∈ X ⊓ Inn (matrixProjectiveDerived Q) := ⟨hxX, hxI⟩
    rw [hXI, Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    exact h2
  set χ : X →* ψ.range :=
    (ψ.comp (Subgroup.inclusion hXE)).codRestrict ψ.range
      (fun x => ⟨Subgroup.inclusion hXE x, rfl⟩) with hχ
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ψ (Subgroup.inclusion hXE x) = 1 := congrArg Subtype.val hx
    have h2 : Subgroup.inclusion hXE x ∈ ψ.ker := MonoidHom.mem_ker.2 h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    have h3 : (x : MulAut (matrixProjectiveDerived Q)) ∈ X ⊓ (linearConjugationHom Q).range :=
      ⟨x.2, h2⟩
    rw [hXD, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  haveI : IsCyclic ψ.range := hcyc
  have hXcyc : IsCyclic ↥X := isCyclic_of_injective χ hχinj
  have hexp : Monoid.exponent ↥X ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => Subtype.ext (hX.2 x.1 x.2))
  rw [IsCyclic.exponent_eq_card, hXc] at hexp
  have hle := Nat.le_of_dvd (by norm_num) hexp
  omega

end Gates

section Transport

theorem no_E9_of_noTrialityAt {S : Type} [Group S] [Finite S] {P D : Subgroup (MulAut S)}
    (hNT : NoTrialityAt S P) (hDP : D ≤ P) (hD : IsElemAbelian 3 D) (hc : Nat.card D = 3 ^ 2)
    (hDI : D ⊓ Inn S = ⊥) : False := by
  obtain ⟨K, _, _, r, f, e, hr, -, hf, hK, hP⟩ := hNT
  have hXE : D.map (MulAut.congr e).toMonoidHom ≤
      matrixProjectiveImage (coordinateQuadPlus 4 K) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hP (hDP hx)
  have hXI : D.map (MulAut.congr e).toMonoidHom ⊓
      Inn (matrixProjectiveDerived (coordinateQuadPlus 4 K)) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e,
      ← Subgroup.map_inf D (Inn S) (MulAut.congr e).toMonoidHom (MulAut.congr e).injective, hDI,
      Subgroup.map_bot]
  have hXA : IsElemAbelian 3 (D.map (MulAut.congr e).toMonoidHom) :=
    isElemAbelian_map_equiv (MulAut.congr e) hD
  have hXc : Nat.card (D.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]
  have eS : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    e.trans (statedProjectiveReindexEquiv (plusIndexEquiv 4)
      (CFSG.LieType.Universal.Spin.quadPlus 4 K) (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K)).symm
  have hmodel : StatedClassicalModel S .POmegaPlus 4 r f :=
    ⟨⟨hr, hf, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨eS⟩⟩
  have hG := orthogonal_large_prime_semilinear_field_and_diagonal_gates S .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 r f hmodel K hK eS
  exact no_E9_of_orthogonalGates (coordinateQuadPlus 4 K) hG _ hXA hXc hXE hXI

end Transport

end CFSG.LocalAnalysis.GLTheoremA
