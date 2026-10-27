module

public import CFSG.RankThree.PartOne.K1214.CycAlg

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

@[expose, instance_reducible] noncomputable def subConjAction (G : Type) [Group G] :
    MulAction G (Subgroup G) :=
  MulAction.compHom (Subgroup G) (MulAut.conj : G →* MulAut G)

theorem mem_conj_subgroup_iff (n : G) (H : Subgroup G) (x : G) :
    letI := subConjAction G
    x ∈ n • H ↔ n⁻¹ * x * n ∈ H := by
  letI := subConjAction G
  change x ∈ (MulAut.conj n) • H ↔ _
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, MulAut.conj_inv_apply]

theorem comm_le_of_normalized [Finite G] {P J B : Subgroup G} (hP : IsPGroup 5 P) (hJP : J ≤ P)
    (hBJ : B ≤ J) (hJn : ∀ p ∈ P, ∀ j ∈ J, p * j * p⁻¹ ∈ J)
    (hBn : ∀ p ∈ P, ∀ b ∈ B, p * b * p⁻¹ ∈ B) (hcard : Nat.card J = 5 * Nat.card B) :
    ⁅J, P⁆ ≤ B := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let Bs : Subgroup P := B.subgroupOf P
  let Js : Subgroup P := J.subgroupOf P
  have hBsn : Bs.Normal := ⟨fun b hb p => hBn p p.2 b hb⟩
  have hBsJs : Bs ≤ Js := fun x hx => hBJ hx
  let π : P →* P ⧸ Bs := QuotientGroup.mk' Bs
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Bs
  have hQ : IsPGroup 5 (P ⧸ Bs) := hP.of_surjective π hπs
  let D : Subgroup (P ⧸ Bs) := Js.map π
  have hJs : Nat.card Js = Nat.card J := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJP).toEquiv]
  have hBs : Nat.card Bs = Nat.card B := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBJ.trans hJP)).toEquiv]
  have hDcard : Nat.card D = 5 := by
    have h1 := Subgroup.card_mul_index D
    have h2 := Subgroup.card_mul_index Js
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup Bs
    have hDi : D.index = Js.index :=
      Subgroup.index_map_eq Js hπs (by rw [QuotientGroup.ker_mk']; exact hBsJs)
    have hBpos : 0 < Nat.card Bs := Nat.card_pos
    have hipos : 0 < Js.index := Nat.pos_of_ne_zero (by
      intro h
      rw [h, mul_zero] at h2
      exact (Nat.card_pos (α := P)).ne h2)
    rw [hDi] at h1
    have h4 : Nat.card D * Js.index * Nat.card Bs = Nat.card Js * Js.index := by
      rw [h1, ← h3, h2]
    rw [hJs, hcard, ← hBs] at h4
    have h5 : Nat.card D * (Js.index * Nat.card Bs) = 5 * (Js.index * Nat.card Bs) := by
      linarith
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hipos hBpos) h5
  rw [Subgroup.commutator_le]
  intro j hj p hp
  have hjP : j ∈ P := hJP hj
  have hjinv : (⟨j⁻¹, P.inv_mem hjP⟩ : P) ∈ Js := J.inv_mem hj
  obtain ⟨m, hm⟩ := hQ (π ⟨p, hp⟩)
  have hcD : ∀ d ∈ D, π ⟨p, hp⟩ * d * (π ⟨p, hp⟩)⁻¹ ∈ D := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨p, hp⟩ * x * ⟨p, hp⟩⁻¹, ?_, by simp⟩
    exact hJn p hp x hx
  have hconj := CFSG.RankThree.PartOne.K1214.conj_eq_of_card_prime Nat.prime_five hDcard hcD hm
    (π ⟨j⁻¹, P.inv_mem hjP⟩) ⟨_, hjinv, rfl⟩
  have h6 : π (⟨p, hp⟩ * ⟨j⁻¹, P.inv_mem hjP⟩ * ⟨p, hp⟩⁻¹) = π ⟨j⁻¹, P.inv_mem hjP⟩ := by
    rw [map_mul, map_mul, map_inv]
    exact hconj
  have h7 := QuotientGroup.eq.mp h6
  have h8 : ((⟨p, hp⟩ * ⟨j⁻¹, P.inv_mem hjP⟩ * ⟨p, hp⟩⁻¹ : P)⁻¹ * ⟨j⁻¹, P.inv_mem hjP⟩ : P) ∈ Bs :=
    h7
  have h9 : (p * j⁻¹ * p⁻¹)⁻¹ * j⁻¹ ∈ B := h8
  have h10 := B.inv_mem h9
  convert h10 using 1
  rw [commutatorElement_def]
  group

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
