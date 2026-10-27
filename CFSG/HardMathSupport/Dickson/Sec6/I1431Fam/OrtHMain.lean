module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHBlock
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PspHMain
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHShell

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Module CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

section Setting

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem t6orth_center_eq_bot_of_simple {T : Type*} [Group T] [IsSimpleGroup T]
    (h : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hb : b ∈ Subgroup.center T := h1 ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem t6orth_data_orth (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hpK : (3 : K) ≠ 0) {q : ℕ} (hq : 10 ≤ q)
    (a : ↥(orthDerived Q)) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ∃ (ι : Type) (_ : Finite ι) (N : ι → Subgroup ↥(orthDerived Q)),
      (∀ i, N i ≤ Subgroup.centralizer ({a} : Set ↥(orthDerived Q))) ∧
      (∀ i, ((N i).subgroupOf (Subgroup.centralizer ({a} : Set ↥(orthDerived Q)))).IsSubnormal) ∧
      (∀ i, CFSG.IsQuasisimple (N i)) ∧
      (∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set ↥(orthDerived Q))) k,
        (g : ↥(orthDerived Q)) ∈ ⨆ i, N i) ∧
      (∀ i, IsTypeL2 q (N i) → ∀ b ∈ Subgroup.centralizer ({a} : Set ↥(orthDerived Q)),
        b ^ 3 = 1 → ∃ s ∈ N i, ∀ m ∈ N i, b * m * b⁻¹ = s * m * s⁻¹) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hpl : (3 : ℕ) ≠ ringChar K := by
    intro h
    apply hpK
    have h0 := CharP.cast_eq_zero K (ringChar K)
    rw [← h] at h0
    exact_mod_cast h0
  have hx : OddOrderIsometry Q 3 (a : V ≃ₗ[K] V) :=
    oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ a hao
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  have hcomm := hx.blocks_commute hRep
  refine t6orth_blocks_data (orthDerived Q) q a
    (fun r : ↥Rep => supportedBlock Q (a : V ≃ₗ[K] V) r.1)
    (fun i j hij x hx' y hy' => hcomm hij x y hx' hy') (hx.blocks_iSupIndep hRep) ?_ ?_ ?_
  · intro g
    rw [hx.blocks_iSup_eq hRep, isometryCentralizer, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨orthDerived_le_orthogonalGroup g.2, congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  · intro r
    have hle : supportedBlock Q (a : V ≃ₗ[K] V) r.1 ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
      fun g hg => (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer _ hg)).1
    exact Subgroup.commutator_mono hle hle
  · intro r
    by_cases hr : r.1 = X - 1
    · have := t6orth_factorOK_fixed hx q
      rw [← hr] at this
      exact this
    · exact t6orth_factorOK_block hO hx Nat.prime_three (by norm_num) hq (hRep.1 r.2) hr

end Setting

theorem s1431_false_orth {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hpK : (3 : K) ≠ 0)
    {A : Subgroup (MulAut (ProjOrthDerived Q))} {ψ : MulAut (ProjOrthDerived Q)}
    {J : Subgroup (ProjOrthDerived Q)} {q : ℕ} (c : S1431Cfg (ProjOrthDerived Q) A ψ J q)
    (hq : 10 ≤ q) (hA : ∀ a ∈ A, IsInnerAut a) : False := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, hcenter, hZcard, hsimple, hnonab, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  set π : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hπ
  have hker : π.ker ≤ Subgroup.center ↥(orthDerived Q) := by
    rw [hπ, QuotientGroup.ker_mk', hcenter]
  have hZ3 : ∀ z ∈ π.ker, z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    rw [hπ, QuotientGroup.ker_mk'] at hz
    have h1 : orderOf z ∣ Nat.card ((scalars K V).subgroupOf (orthDerived Q)) :=
      Subgroup.orderOf_dvd_natCard _ hz
    have h2 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    have h3 : orderOf z ≤ 2 := (Nat.le_of_dvd Nat.card_pos h1).trans hZcard
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · omega
  haveI := hsimple
  have hZ : Subgroup.center (ProjOrthDerived Q) = ⊥ := t6orth_center_eq_bot_of_simple hnonab
  exact t6orth_s1431_false_of_lift_blocks_sn π (QuotientGroup.mk'_surjective _) hker hZ3
    (t6psph_conj_injective_of_center hZ) c hA
    fun a ha3 hπa => t6orth_data_orth hO hQ hpK hq a ha3 (fun h => hπa (by rw [h, map_one]))

end CFSG.HardMathSupport.Dickson.Sec6.I1431
