module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private def conjN' {N : Subgroup G} {t : G}
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (n : ↥N) : ↥N :=
  ⟨t * n.1 * t⁻¹, htN n.1 n.2⟩

private def cosetConj' {E N : Subgroup G} {t : G}
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    (↥N ⧸ E.subgroupOf N) → (↥N ⧸ E.subgroupOf N) :=
  Quotient.map' (conjN' htN) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    apply Subgroup.mem_subgroupOf.mpr
    have hmem : (a : G)⁻¹ * (b : G) ∈ E := Subgroup.mem_subgroupOf.mp hab
    have hconj : t * ((a : G)⁻¹ * (b : G)) * t⁻¹ ∈ E := htE _ hmem
    have hEq : ((conjN' htN a : G)⁻¹ * (conjN' htN b : G)) =
        t * ((a : G)⁻¹ * (b : G)) * t⁻¹ := by
      simp only [conjN', Subtype.coe_mk]
      push_cast
      group
    change ((conjN' htN a : G)⁻¹ * (conjN' htN b : G)) ∈ E
    rw [hEq]
    exact hconj

private lemma conjN'_involutive {N : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (n : ↥N) :
    conjN' htN (conjN' htN n) = n := by
  have htinv : t⁻¹ = t := by
    calc t⁻¹ = t⁻¹ * 1 := (mul_one _).symm
      _ = t⁻¹ * (t * t) := by rw [ht2]
      _ = (t⁻¹ * t) * t := by rw [mul_assoc]
      _ = t := by rw [inv_mul_cancel, one_mul]
  apply Subtype.ext
  simp only [conjN', Subtype.coe_mk]
  calc t * (t * n.1 * t⁻¹) * t⁻¹ = (t * t) * n.1 * (t⁻¹ * t⁻¹) := by group
    _ = n.1 := by rw [ht2, htinv, ht2]; group

private lemma cosetConj'_involutive {E N : Subgroup G} {t : G} (ht2 : t * t = 1)
    (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    Function.Involutive (cosetConj' htN htE) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h n =>
    simp only [cosetConj', Quotient.map'_mk'']
    rw [conjN'_involutive ht2 htN n]

theorem exists_fixed_coset_of_even_index {E N : Subgroup G} (hidx : 2 ∣ (E.subgroupOf N).index)
    {t : G} (ht2 : t * t = 1) (htN : ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) :
    ∃ n ∈ N, n ∉ E ∧ n⁻¹ * (t * n * t⁻¹) ∈ E := by
  classical
  let X := ↥N ⧸ E.subgroupOf N
  haveI : Fintype ↥N := Fintype.ofFinite ↥N
  haveI : Fintype X :=
    Fintype.ofSurjective (Quotient.mk'' : ↥N → X) Quotient.mk''_surjective
  have hcardX : Fintype.card X = (E.subgroupOf N).index := by
    rw [Fintype.card_eq_nat_card, Subgroup.index_eq_card]
  have hα : 2 ∣ Fintype.card X := by
    rw [hcardX]
    exact hidx
  let s : Equiv.Perm X := (cosetConj'_involutive ht2 htN htE).toPerm (cosetConj' htN htE)
  have hs : (s : X → X) = cosetConj' htN htE := Function.Involutive.coe_toPerm _
  have hpow : s ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    rw [hs]
    exact cosetConj'_involutive ht2 htN htE x
  let oneN : ↥N := ⟨1, N.one_mem⟩
  let a : X := Quotient.mk'' oneN
  have hone : conjN' htN oneN = oneN := by
    ext
    simp [conjN', oneN, ht2]
  have hfixa : s a = a := by
    rw [hs]
    change cosetConj' htN htE (Quotient.mk'' oneN) = Quotient.mk'' oneN
    simp only [cosetConj', Quotient.map'_mk'']
    rw [hone]
  obtain ⟨b, hbfix, hbne⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime' (p := 2) (n := 1) hα hpow hfixa
  obtain ⟨x, hxb⟩ : ∃ x : ↥N, (Quotient.mk'' x : X) = b :=
    ⟨b.out, Quotient.out_eq' b⟩
  have hbfix' : s (Quotient.mk'' x) = Quotient.mk'' x := by
    rw [hxb]
    exact hbfix
  have hbne' : (Quotient.mk'' x : X) ≠ a := by
    rw [hxb]
    exact hbne
  have hfixq : cosetConj' htN htE (Quotient.mk'' x) = Quotient.mk'' x := by
    rw [← hs]
    exact hbfix'
  have hmemQ : (conjN' htN x)⁻¹ * x ∈ E.subgroupOf N := by
    apply QuotientGroup.eq.mp
    simpa only [cosetConj', Quotient.map'_mk''] using hfixq
  have hmemE : (conjN' htN x : G)⁻¹ * x.1 ∈ E :=
    Subgroup.mem_subgroupOf.mp hmemQ
  refine ⟨x.1, x.2, ?_, ?_⟩
  · intro hxe
    apply hbne'
    rw [QuotientGroup.eq]
    apply Subgroup.mem_subgroupOf.mpr
    simpa [oneN] using E.inv_mem hxe
  · have hfin : ((conjN' htN x : G)⁻¹ * x.1)⁻¹ ∈ E := E.inv_mem hmemE
    simpa [conjN', mul_inv_rev, inv_inv] using hfin

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem t_conj_ctxCQ {c : G} (hc : c ∈ ctxCQ t tau x₁ x₂ rho) :
    t * c * t⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := by
  refine mem_centralizer_iff.mpr ?_
  intro q hq
  have htq : t⁻¹ * q * t ∈ ctxQ t tau x₁ x₂ rho := by
    simpa using hz.normal_Q.2 t⁻¹ ((ctxM t tau x₁ x₂).inv_mem hz.t_mem_M) q hq
  have hcomm := mem_centralizer_iff.mp hc (t⁻¹ * q * t) htq
  calc q * (t * c * t⁻¹)
      = t * ((t⁻¹ * q * t) * c) * t⁻¹ := by group
    _ = t * (c * (t⁻¹ * q * t)) * t⁻¹ := by rw [hcomm]
    _ = (t * c * t⁻¹) * q := by group

theorem Q_lt_ctxWN (hn : ¬ IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho)) :
    ctxQ t tau x₁ x₂ rho < ctxWN t tau x₁ x₂ rho := by
  have hQC : ctxQ t tau x₁ x₂ rho ≤ ctxCQ t tau x₁ x₂ rho := by
    intro q hq
    refine mem_centralizer_iff.mpr ?_
    intro p hp
    exact hz.Q_comm p hp q hq
  have hQ2 : IsPGroup 2 (ctxQ t tau x₁ x₂ rho) :=
    IsPGroup.of_card (p := 2) (n := 6) hz.card_Q
  have hrel : 2 ∣ (ctxQ t tau x₁ x₂ rho).relIndex (ctxCQ t tau x₁ x₂ rho) := by
    by_contra h
    exact hn ⟨hQC, hQ2, h⟩
  obtain ⟨n, hnN, hnE, hnQ⟩ :=
    exists_fixed_coset_of_even_index (E := ctxQ t tau x₁ x₂ rho)
      (N := ctxCQ t tau x₁ x₂ rho) hrel hz.t_mul_self
      (fun c hc => hz.t_conj_ctxCQ hc) (fun e he => hz.normal_Q.2 t hz.t_mem_M e he)
  refine lt_of_le_of_ne hz.Q_le_ctxWN ?_
  intro hEq
  have hwN : n⁻¹ ∈ ctxCQ t tau x₁ x₂ rho := (ctxCQ t tau x₁ x₂ rho).inv_mem hnN
  have hwt : n⁻¹ * t * (n⁻¹)⁻¹ * t⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    have heq : n⁻¹ * t * (n⁻¹)⁻¹ * t⁻¹ = n⁻¹ * (t * n * t⁻¹) := by group
    rw [heq]
    exact hnQ
  have hwW : n⁻¹ ∈ ctxWN t tau x₁ x₂ rho := hz.mem_ctxWN_iff.mpr ⟨hwN, hwt⟩
  have hwQ : n⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [← hEq] at hwW
    exact hwW
  exact hnE (by simpa using (ctxQ t tau x₁ x₂ rho).inv_mem hwQ)

theorem znw (hn : ¬ IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho)) :
    ZNW t L S x₁ x₂ lam rho tau :=
  ⟨hz, hz.Q_lt_ctxWN hn⟩

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
