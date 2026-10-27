module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocDefs
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Aut
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.GH74.Generic.S3.L3Class

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)
open scoped commutatorElement

theorem socleInvConj_of_singleInv {F : Type} [Group F]
    (h : CFSG.GH74.Generic.S3.SingleInv F) : SocleInvConj F := by
  have key : ∀ x : F, orderOf x = 2 → x * x = 1 ∧ x ≠ 1 := by
    intro x hx
    refine ⟨?_, fun h1 => ?_⟩
    · have := pow_orderOf_eq_one x
      rw [hx, sq] at this
      exact this
    · rw [h1, orderOf_one] at hx
      norm_num at hx
  intro s t hs ht
  exact h s t (key s hs).1 (key s hs).2 (key t ht).1 (key t ht).2

theorem socleInvConj_l3 {F : Type} [Group F] [Finite F] (h : SmallL3Ne3 F) : SocleInvConj F := by
  obtain ⟨p, f, hp, hp2, -, -, hm⟩ := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have h2 : (2 : K) ≠ 0 :=
    Ring.two_ne_zero (CFSG.GH74.Generic.S3.ringChar_ne_two_of_card_pow hp hp2 hK)
  exact socleInvConj_of_singleInv
    (CFSG.GH74.Generic.S3.SingleInv.of_mulEquiv e.symm (CFSG.GH74.Generic.S3.singleInv_psl h2))

theorem socleInvConj_u3 {F : Type} [Group F] [Finite F] (h : SmallU3Ne3 F) : SocleInvConj F := by
  obtain ⟨p, f, hp, hp2, hf, -, hm⟩ := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  exact socleInvConj_of_singleInv
    (CFSG.GH74.Generic.S3.SingleInv.of_mulEquiv e.symm
      (CFSG.GH74.Generic.S3.singleInv_psu hU hp2))

theorem soc_outer_comm_of_pow {K : Type} [Field K] [Finite K] (a b : Outer (projectiveSL 3 K))
    (k : ℕ) (hk : (⁅a, b⁆) ^ 2 ^ k = 1) : a * b = b * a := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective b
  have hq : ⁅(QuotientGroup.mk α : Outer (projectiveSL 3 K)),
      (QuotientGroup.mk β : Outer (projectiveSL 3 K))⁆ =
        (QuotientGroup.mk ⁅α, β⁆ : Outer (projectiveSL 3 K)) :=
    (map_commutatorElement (QuotientGroup.mk' (inner (projectiveSL 3 K))) α β).symm
  rw [hq, ← QuotientGroup.mk_pow] at hk
  have hI : ⁅α, β⁆ ^ 2 ^ k ∈ inner (projectiveSL 3 K) := (QuotientGroup.eq_one_iff _).mp hk
  have hδ : ⁅α, β⁆ ∈ linearAutGroup 3 K :=
    CFSG.ClassicalInvolution.Q3.TA3.Q5L3.commutator_mem_linearAutGroup le_rfl α β
  have hdiag : ¬ 2 ∣ Nat.gcd 3 (Nat.card K - 1) := fun h => by
    have := h.trans (Nat.gcd_dvd_left 3 _)
    omega
  have hin : ⁅α, β⁆ ∈ inner (projectiveSL 3 K) :=
    CFSG.RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl hdiag _ hδ k hI
  have h1 : ⁅(QuotientGroup.mk α : Outer (projectiveSL 3 K)),
      (QuotientGroup.mk β : Outer (projectiveSL 3 K))⁆ = 1 := by
    rw [hq]
    exact (QuotientGroup.eq_one_iff _).mpr hin
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem socleOutAbelian_u3 {F : Type} [Group F] [Finite F] (h : SmallU3Ne3 F) :
    SocleOutAbelian F := by
  obtain ⟨p, f, -, -, -, -, hm⟩ := h
  have hodd : Odd (Nat.gcd 3 (p ^ f + 1)) :=
    (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  have hcyc := CFSG.ClassicalInvolution.Q3.TA3.outTwoCyclic_PSU hm hodd
  intro P hP
  haveI := hcyc P hP
  exact IsCyclic.isMulCommutative

theorem socleOutAbelian_l3 {F : Type} [Group F] [Finite F] (h : SmallL3Ne3 F) :
    SocleOutAbelian F := by
  obtain ⟨p, f, -, -, -, -, hm⟩ := h
  obtain ⟨K, _, _, -, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (Or.inl ⟨by decide, hm⟩ : CFSG.Blueprint.LieModel F .PSL 3 p f)
  refine SocleOutAbelian.of_mulEquiv e ?_
  intro Pg hPg
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨k, hk⟩ := hPg ⟨⁅a.1, b.1⁆,
    Pg.mul_mem (Pg.mul_mem (Pg.mul_mem a.2 b.2) (Pg.inv_mem a.2)) (Pg.inv_mem b.2)⟩
  have hk' : (⁅a.1, b.1⁆) ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_pow] at h1
    exact h1
  exact soc_outer_comm_of_pow a.1 b.1 k hk'

end CFSG.CGT.PushingUpLit.SolKNA.R4
