module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOutL
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace OutLU4

theorem sq_conj_mem_of_cyclic {X : Type} [Group X] {D I : Subgroup X} [D.Normal] [hI : I.Normal]
    (hcyc : IsCyclic (↥D ⧸ I.subgroupOf D)) (h4 : Nat.card (↥D ⧸ I.subgroupOf D) ∣ 4)
    (α : X) {δ : X} (hδ : δ ∈ D) : α ^ 2 * δ * (α ^ 2)⁻¹ * δ⁻¹ ∈ I := by
  let τ : ↥D →* ↥D := (MulAut.conjNormal α).toMonoidHom
  have hτ : ∀ x : ↥D, (τ x : X) = α * x * α⁻¹ := fun x => MulAut.conjNormal_apply α x
  have hle : I.subgroupOf D ≤ (I.subgroupOf D).comap τ := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hτ]
    exact hI.conj_mem _ (Subgroup.mem_subgroupOf.mp hx) α
  let τb : ↥D ⧸ I.subgroupOf D →* ↥D ⧸ I.subgroupOf D := QuotientGroup.map _ _ τ hle
  have hτb : ∀ x : ↥D, τb (x : ↥D ⧸ I.subgroupOf D) = ((τ x : ↥D) : ↥D ⧸ I.subgroupOf D) :=
    fun x => rfl
  have hinj : ∀ q : ↥D ⧸ I.subgroupOf D, τb q = 1 → q = 1 := by
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hτb, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hτ] at hq
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have h1 := hI.conj_mem _ hq α⁻¹
      rwa [show α⁻¹ * (α * (x : X) * α⁻¹) * α⁻¹⁻¹ = x by group] at h1
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic τb
  have hq4 : ∀ (q : ↥D ⧸ I.subgroupOf D) (k : ℤ), q ^ (4 * k) = 1 := by
    intro q k
    have h1 : q ^ (4 : ℕ) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard q).trans h4)
    rw [zpow_mul, show q ^ (4 : ℤ) = q ^ (4 : ℕ) from zpow_natCast q 4, h1, one_zpow]
  have hinv : ∀ q, τb (τb q) = q := by
    rcases Int.even_or_odd m with ⟨s, hs⟩ | ⟨s, hs⟩
    · have h2 : ∀ q : ↥D ⧸ I.subgroupOf D, q ^ (2 : ℤ) = 1 := fun q => hinj _ (by
        rw [hm, ← zpow_mul, hs, show (2 : ℤ) * (s + s) = 4 * s by ring, hq4])
      have h1 : ∀ q : ↥D ⧸ I.subgroupOf D, q = 1 := fun q => hinj _ (by
        rw [hm, hs, ← two_mul, zpow_mul, h2, one_zpow])
      intro q
      rw [h1 q, map_one, map_one]
    · intro q
      rw [hm, hm, ← zpow_mul, hs,
        show (2 * s + 1) * (2 * s + 1) = 4 * (s * (s + 1)) + 1 by ring, zpow_add, hq4, one_mul,
        zpow_one]
  have h1 := hinv (⟨δ, hδ⟩ : ↥D)
  rw [hτb, hτb, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have h2 := hI.conj_mem _ (inv_mem h1) δ
  have key : δ * (((τ (τ ⟨δ, hδ⟩))⁻¹ * ⟨δ, hδ⟩ : ↥D) : X)⁻¹ * δ⁻¹ =
      α ^ 2 * δ * (α ^ 2)⁻¹ * δ⁻¹ := by
    have hy : α * (α * δ * α⁻¹) * α⁻¹ = α ^ 2 * δ * (α ^ 2)⁻¹ := by
      rw [pow_two, _root_.mul_inv_rev]
      simp only [mul_assoc]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hτ, hτ]
    show δ * ((α * (α * δ * α⁻¹) * α⁻¹)⁻¹ * δ)⁻¹ * δ⁻¹ = _
    rw [hy]
    generalize α ^ 2 = b
    group
  rwa [key] at h2

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem outTwoNilp_u4 :
    OutTwoNilp (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
  have : Finite K := h.finite
  have hq : ¬(4 = 3 ∧ p ^ f = 2) := fun h3 => absurd h3.1 (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, hFker, hDn, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h isPrimeFormGram_one (by norm_num) hq
  obtain ⟨-, hcyc, hcard, -⟩ := unitary_full_diagonal_outer_order h (by norm_num) hq
  set T := primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hT
  set D := primeFormD h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hD
  set F := primeFormFieldFactor h (isPrimeFormGram_one (n := 4) (K := K)) (by norm_num) hq
    with hF
  have : Finite T := Finite.of_equiv _
    (CFSG.ComponentClassification.Burgoyne.U.uTransport h (by norm_num)).toEquiv
  have hI : (inner T).Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal T
  have h4 : Nat.card (↥D ⧸ (inner T).subgroupOf D) ∣ 4 := hcard ▸ Nat.gcd_dvd_left 4 _
  refine OutL.outTwoNilp_of_diag D (fun δ hδ => ⟨2, ?_⟩) (fun α β => ?_)
    (fun α δ hδ => sq_conj_mem_of_cyclic hcyc h4 α hδ)
  · have h1 : ((⟨δ, hδ⟩ : ↥D) : ↥D ⧸ (inner T).subgroupOf D) ^ 4 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans h4)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · rw [← hFker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [CFSG.RankThree.PartOne.OutStructure.ringAut_comm K (F α) (F β)]
    group

end OutLU4

open OutLU4 in
theorem outCell_fu4 : OutCell FU4 := by
  intro Y _ _ _ hY
  obtain ⟨p, f, hp, hf, -, -, hLie⟩ := hY
  obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hLie
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  exact OutL.outTwoNilp_of_equiv
    (e.trans (CFSG.ComponentClassification.Burgoyne.U.uTransport h (by norm_num))) (outTwoNilp_u4 h)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
