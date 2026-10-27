module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81CLin
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YGIso
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCorePlanes
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.E81C

open CFSG.Open Matrix Module CFSG.Assembly.LowTwoRank
open CFSG.StandardType CFSG.StandardType.Triality
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} [Field K]

private theorem eq_zero_or_one [Finite K] (hK : Nat.card K = 2) (x : K) : x = 0 ∨ x = 1 := by
  classical
  haveI := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hK] at h
  have h0 : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (sub_eq_zero.1 h1)

private theorem ringEquiv_eq_one [Finite K] (hK : Nat.card K = 2) (σ : K ≃+* K) : σ = 1 :=
  RingEquiv.ext fun x => by
    rcases eq_zero_or_one hK x with rfl | rfl
    · exact map_zero σ
    · exact map_one σ

private theorem isElemAbelian_map {G N : Type*} [Group G] [Group N] {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (f : G →* N) : IsElemAbelian 3 (E.map f) := by
  obtain ⟨hc', hp'⟩ := hE
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', hae⟩ := a.2
    obtain ⟨b', hb', hbe⟩ := b.2
    have h1 := congrArg Subtype.val (hc'.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩)
    change (a : N) * b = b * a
    rw [← hae, ← hbe, ← map_mul, ← map_mul]
    exact congrArg f h1
  · obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_pow, hp' x' hx', map_one]

theorem false_of_conjAct [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (g : similarityPairs (coordinateQuadPlus 4 K)) (E : Subgroup (Om8 K))
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4)
    (ht : conjAct (coordinateQuadPlus 4 K) g ^ 2 = 1) (ht1 : conjAct (coordinateQuadPlus 4 K) g ≠ 1)
    (hfix : ∀ e ∈ E, conjAct (coordinateQuadPlus 4 K) g e = e) : False := by
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t := conjAct (coordinateQuadPlus 4 K) g with htdef
  set L : GL (Fin (2 * 4)) K := g.val.left with hL
  have hσ : g.val.right = 1 := ringEquiv_eq_one hK _
  have hconj : ∀ A : Om8 K,
      ((t A : Om8 K) : GL (Fin (2 * 4)) K) = L * (A : GL (Fin (2 * 4)) K) * L⁻¹ := by
    intro A
    rw [htdef, conjAct_apply, matrixDerivedConjugation_val, hσ, map_one, MulAut.one_apply, ← hL]
  have hpow : ∀ (j : ℕ) (A : Om8 K),
      (((t ^ j) A : Om8 K) : GL (Fin (2 * 4)) K) =
        L ^ j * (A : GL (Fin (2 * 4)) K) * (L ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro A; simp
    | succ j ih =>
      intro A
      rw [pow_succ', MulAut.mul_apply, hconj, ih, pow_succ' L j]
      group
  have hLpos : 0 < orderOf L := orderOf_pos L
  have heven : Even (orderOf L) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨r, hr⟩ := hodd
    have htm : t ^ orderOf L = 1 := by
      refine MulEquiv.ext fun A => Subtype.ext ?_
      rw [hpow, pow_orderOf_eq_one, inv_one, one_mul, mul_one, MulAut.one_apply]
    rw [hr, pow_succ, pow_mul, ht, one_pow, one_mul] at htm
    exact ht1 htm
  obtain ⟨r, hr⟩ := heven
  have hr0 : r ≠ 0 := by
    rintro rfl
    omega
  have hB2 : L ^ r * L ^ r = 1 := by rw [← pow_add, ← hr, pow_orderOf_eq_one]
  have hB1 : L ^ r ≠ 1 := pow_ne_one_of_lt_orderOf hr0 (by omega)
  have hcommL : ∀ A ∈ E, (A : GL (Fin (2 * 4)) K) * L = L * A := by
    intro A hA
    have h1 := congrArg (fun x : Om8 K => (x : GL (Fin (2 * 4)) K)) (hfix A hA)
    rw [hconj] at h1
    calc (A : GL (Fin (2 * 4)) K) * L = (L * (A : GL (Fin (2 * 4)) K) * L⁻¹) * L := by rw [h1]
      _ = L * A := by group
  set G : Subgroup (GL (Fin (2 * 4)) K) :=
    E.map (matrixDerived (coordinateQuadPlus 4 K)).subtype with hGdef
  have hcomm : ∀ x ∈ G, x * L ^ r = L ^ r * x := by
    rintro _ ⟨A, hA, rfl⟩
    exact (Commute.pow_right (hcommL A hA) r).eq
  have hGab : IsElemAbelian 3 G := isElemAbelian_map hE _
  have hGcard : Nat.card G = 3 ^ 4 := by
    rw [hGdef, Subgroup.card_map_of_injective
      (matrixDerived (coordinateQuadPlus 4 K)).subtype_injective, hcard]
  have hbound := card_le_of_commute_involution G hGab hB2 hB1 hcomm
  have hdim : finrank (ZMod 2) (Fin (2 * 4) → K) = 2 * 4 := by
    have h1 := FiniteField.pow_finrank_eq_natCard 2 (Fin (2 * 4) → K)
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card (α := Fin (2 * 4)), Fintype.card_fin] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  rw [hGcard, hdim] at hbound
  norm_num at hbound

theorem innerOfFix_om8 [Finite K] [CharP K 2] (hK : Nat.card K = 2) : InnerOfFix (Om8 K) := by
  intro E hE hcard t ht hfix
  by_cases ht1 : t = 1
  · exact ⟨1, by rw [ht1, map_one]⟩
  exfalso
  obtain ⟨ι, hι, k, c, hc, rfl⟩ := exists_inner_mul_theta_pow_mul t
  obtain ⟨σ, hcσ | hcσ⟩ := AutOm.mem_plusCompl.1 hc
  ·
    rw [ringEquiv_eq_one hK σ, map_one] at hcσ
    subst hcσ
    simp only [mul_one] at ht ht1 hfix
    have h2 : ι * theta ^ k * (ι * theta ^ k) = 1 := by rw [← pow_two]; exact ht
    have e : (theta : MulAut (Om8 K)) ^ (2 * k) =
        (theta ^ k * ι * (theta ^ k)⁻¹)⁻¹ * ι⁻¹ := by
      rw [two_mul k, pow_add]
      calc (theta : MulAut (Om8 K)) ^ k * theta ^ k =
          theta ^ k * ι⁻¹ * (theta ^ k)⁻¹ * ι⁻¹ * (ι * theta ^ k * (ι * theta ^ k)) := by group
        _ = (theta ^ k * ι * (theta ^ k)⁻¹)⁻¹ * ι⁻¹ := by rw [h2, mul_one]; group
    have hinn : (theta : MulAut (Om8 K)) ^ (2 * k) * 1 ∈ inner (Om8 K) := by
      rw [mul_one, e]
      exact mul_mem (inv_mem ((inner_normal _).conj_mem ι hι _)) (inv_mem hι)
    have h2k := (theta_pow_mul_mem_inner (2 * k) (one_mem _) hinn).1
    have hk : (theta : MulAut (Om8 K)) ^ k = 1 := by
      have h3 : (theta : MulAut (Om8 K)) ^ (3 * k) = 1 := by rw [pow_mul, theta_cube, one_pow]
      have h32 : (theta : MulAut (Om8 K)) ^ (3 * k) = theta ^ k * theta ^ (2 * k) := by
        rw [← pow_add, show k + 2 * k = 3 * k by ring]
      rw [h32, h2k, mul_one] at h3
      exact h3
    rw [hk, mul_one] at ht ht1 hfix
    obtain ⟨g, hg⟩ := exists_pair_of_mem_inner hι
    rw [← hg] at ht ht1 hfix
    exact false_of_conjAct hK g E hE hcard ht ht1 hfix
  ·
    rw [ringEquiv_eq_one hK σ, map_one, mul_one] at hcσ
    subst hcσ
    set ρ : MulAut (Om8 K) := AutOm.plusRefl (K := K) one_le_four with hρ
    set s : MulAut (Om8 K) := theta ^ (2 * k) with hs
    have hρρ : ρ * ρ = 1 := AutOm.plusRefl_mul_self one_le_four
    have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρρ
    have hρs : ρ * s * ρ = s⁻¹ := by
      have e1 : ρ * theta * ρ⁻¹ = theta⁻¹ := by rw [hρinv]; exact plusRefl_theta_plusRefl
      calc ρ * s * ρ = ρ * s * ρ⁻¹ := by rw [hρinv]
        _ = (ρ * theta * ρ⁻¹) ^ (2 * k) := by rw [hs, conj_pow]
        _ = s⁻¹ := by rw [e1, inv_pow, hs]
    have hks : (theta : MulAut (Om8 K)) ^ k * s⁻¹ = s := by
      rw [mul_inv_eq_iff_eq_mul, hs, ← pow_add]
      have e2 : 2 * k + 2 * k = k + 3 * k := by ring
      rw [e2, pow_add, pow_mul, theta_cube, one_pow, mul_one]
    have hrel : (theta : MulAut (Om8 K)) ^ k * ρ * s = s * ρ := by
      calc (theta : MulAut (Om8 K)) ^ k * ρ * s = theta ^ k * (ρ * s * ρ) * ρ := by
            simp only [mul_assoc, hρρ, mul_one]
        _ = theta ^ k * s⁻¹ * ρ := by rw [hρs]
        _ = s * ρ := by rw [hks]
    set t := ι * (theta ^ k * ρ) with htdef
    have ht' : s⁻¹ * t * s = (s⁻¹ * ι * s) * ρ := by
      calc s⁻¹ * t * s = s⁻¹ * ι * (theta ^ k * ρ * s) := by
            simp only [htdef, mul_assoc]
        _ = s⁻¹ * ι * (s * ρ) := by rw [hrel]
        _ = (s⁻¹ * ι * s) * ρ := by simp only [mul_assoc]
    have hι' : s⁻¹ * ι * s ∈ inner (Om8 K) := by
      have h1 := (inner_normal (Om8 K)).conj_mem ι hι s⁻¹
      rwa [inv_inv] at h1
    obtain ⟨g₁, hg₁⟩ := exists_pair_of_mem_inner hι'
    obtain ⟨g₂, hg₂⟩ := exists_pair_of_mem_plusCompl hc
    have hconj : conjAct (coordinateQuadPlus 4 K) (g₁ * g₂) = s⁻¹ * t * s := by
      rw [map_mul, hg₁, hg₂, ht']
    set E' : Subgroup (Om8 K) := E.map (s⁻¹ : MulAut (Om8 K)).toMonoidHom with hE'
    have hE'ab : IsElemAbelian 3 E' := isElemAbelian_map hE _
    have hE'card : Nat.card E' = 3 ^ 4 := by
      rw [hE', Subgroup.card_map_of_injective (f := (s⁻¹ : MulAut (Om8 K)).toMonoidHom)
        (s⁻¹ : MulAut (Om8 K)).injective, hcard]
    have ht2 : conjAct (coordinateQuadPlus 4 K) (g₁ * g₂) ^ 2 = 1 := by
      rw [hconj, pow_two]
      calc s⁻¹ * t * s * (s⁻¹ * t * s) = s⁻¹ * (t * t) * s := by group
        _ = 1 := by rw [← pow_two t, ht, mul_one, inv_mul_cancel]
    have ht21 : conjAct (coordinateQuadPlus 4 K) (g₁ * g₂) ≠ 1 := by
      rw [hconj]
      intro h1
      apply ht1
      calc t = s * (s⁻¹ * t * s) * s⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    have hfix' : ∀ e ∈ E', conjAct (coordinateQuadPlus 4 K) (g₁ * g₂) e = e := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hconj]
      change s⁻¹ (t (s (s⁻¹ x))) = s⁻¹ x
      exact congrArg (fun y => (s⁻¹ : MulAut (Om8 K)) y)
        ((congrArg t (MulAut.apply_inv_self _ s x)).trans (hfix x hx))
    exact false_of_conjAct hK (g₁ * g₂) E' hE'ab hE'card ht2 ht21 hfix'

theorem exists_om8_of_isD4two {S : Type} [Group S]
    (h : CFSG.Yardstones.Md0ec50421ce4.catalogIs S S9.isD4two) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ 2), Nat.card K₀ = 2 ∧
      Nonempty (S ≃* Om8 K₀) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isD4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := CFSG.Models.lieModel_D 4 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K₀, _, _, hK₀, ⟨eK⟩⟩ := hm.statedClassicalModel (by decide)
  have hK₀' : Nat.card K₀ = 2 := hK₀.trans (by norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK₀])
  have hS := CFSG.LocalAnalysis.GLTheoremA.D4Y.matrixDerivedScalars_eq_bot_charTwo
    (coordinateQuadPlus 4 K₀)
    ⟨CFSG.RankThree.PartOne.KCOrthogonalSubfield.stdU K₀, by
      rw [CFSG.RankThree.PartOne.KCOrthogonalSubfield.coordinateQuadPlus_stdU]
      exact one_ne_zero⟩
  exact ⟨K₀, inferInstance, inferInstance, inferInstance, hK₀',
    ⟨(coordinatePlusWitnessEquiv K₀ eK).trans
      ((QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot)⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat.E81C

end
