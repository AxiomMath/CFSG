module

public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.GH74.Filter.ElemAbelian
public import CFSG.GH74.Filter.Statements
public import Certificates.Data.CFSGNative.Filter.TitsElem
public meta import Certificates.Data.CFSGNative.Filter.TitsElem
public import Certificates.Certificate5022
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.SectionRank CFSG.SectionRank.TitsGen CFSG.SectionRank.TitsOrder
  CFSG.SectionRank.Native.Tits CFSG.SectionRank.TitsLocal CFSG.Sporadic.Th CFSG.Perm
  CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap invT invOK idT compT powT Table allIn wordT)

attribute [local instance] idxAction

theorem hker_of_digits {G : Type*} [Group G] (u : Fin 5 → G)
    (h : ∀ n : ℕ, 1 ≤ n → n < 32 →
      u 0 ^ (n % 2) * u 1 ^ (n / 2 % 2) * u 2 ^ (n / 4 % 2) * u 3 ^ (n / 8 % 2) *
        u 4 ^ (n / 16 % 2) ≠ 1) :
    ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1 := by
  intro a ha
  have h0 : (a 0 : ℕ) + 2 * a 1 + 4 * a 2 + 8 * a 3 + 16 * a 4 ≠ 0 := by
    intro h0
    apply ha
    funext i
    fin_cases i <;> simp <;> omega
  have a0 := (a 0).2
  have a1 := (a 1).2
  have a2 := (a 2).2
  have a3 := (a 3).2
  have a4 := (a 4).2
  have key := h ((a 0 : ℕ) + 2 * a 1 + 4 * a 2 + 8 * a 3 + 16 * a 4) (by omega) (by omega)
  have d0 : ((a 0 : ℕ) + 2 * a 1 + 4 * a 2 + 8 * a 3 + 16 * a 4) % 2 = a 0 := by omega
  have d1 : ((a 0 : ℕ) + 2 * a 1 + 4 * a 2 + 8 * a 3 + 16 * a 4) / 2 % 2 = a 1 := by omega
  have d2 : ((a 0 : ℕ) + 2 * a 1 + 4 * a 2 + 8 * a 3 + 16 * a 4) / 4 % 2 = a 2 := by omega
  have d3 : ((a 0 : ℕ) + 2 * a 1 + 4 * a 2 + 8 * a 3 + 16 * a 4) / 8 % 2 = a 3 := by omega
  have d4 : ((a 0 : ℕ) + 2 * a 1 + 4 * a 2 + 8 * a 3 + 16 * a 4) / 16 % 2 = a 4 := by omega
  rw [d0, d1, d2, d3, d4] at key
  simpa [List.ofFn_succ, mul_assoc] using key

theorem commute_fin_five {G : Type*} [Group G] (u : Fin 5 → G) (k01 : Commute (u 0) (u 1))
    (k02 : Commute (u 0) (u 2)) (k03 : Commute (u 0) (u 3)) (k04 : Commute (u 0) (u 4))
    (k12 : Commute (u 1) (u 2)) (k13 : Commute (u 1) (u 3)) (k14 : Commute (u 1) (u 4))
    (k23 : Commute (u 2) (u 3)) (k24 : Commute (u 2) (u 4)) (k34 : Commute (u 3) (u 4)) :
    ∀ i j, Commute (u i) (u j) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)

theorem tits_elem_check :
    elemOK [0] [2, 26] [5, 6, 5] [16, 2, 5] [24, 2, 18] = true :=
  Certificates.certificate5022

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem Tits_commuting_involutions
    (hK : Nat.card K = 2) :
    ∃ u : Fin 5 → commutator (reeFixed ReeTag.F4 K 0), (∀ i, u i ^ 2 = 1) ∧
      (∀ i j, Commute (u i) (u j)) ∧
      ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1 := by
  have : Fact (Nat.card K = 2) := ⟨hK⟩
  have h := tits_elem_check
  unfold elemOK at h
  simp only [Bool.and_eq_true, List.all_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hT, ⟨⟨⟨⟨hw0, hw1⟩, hw2⟩, hw3⟩, hw4⟩⟩, hs0⟩, hs1⟩, hs2⟩, hs3⟩, hs4⟩,
    c01⟩, c02⟩, c03⟩, c04⟩, c12⟩, c13⟩, c14⟩, c23⟩, c24⟩, c34⟩, hall⟩ := h
  obtain ⟨u0, r0⟩ : ∃ u : commutator (reeFixed ReeTag.F4 K 0),
      Rep nPts (wT (texpand [0])) (u : reeFixed ReeTag.F4 K 0) :=
    ⟨⟨tword K [0], tword_mem hT hw0⟩, rep_tword [0]⟩
  obtain ⟨u1, r1⟩ : ∃ u : commutator (reeFixed ReeTag.F4 K 0),
      Rep nPts (wT (texpand [2, 26])) (u : reeFixed ReeTag.F4 K 0) :=
    ⟨⟨tword K [2, 26], tword_mem hT hw1⟩, rep_tword [2, 26]⟩
  obtain ⟨u2, r2⟩ : ∃ u : commutator (reeFixed ReeTag.F4 K 0),
      Rep nPts (wT (texpand [5, 6, 5])) (u : reeFixed ReeTag.F4 K 0) :=
    ⟨⟨tword K [5, 6, 5], tword_mem hT hw2⟩, rep_tword [5, 6, 5]⟩
  obtain ⟨u3, r3⟩ : ∃ u : commutator (reeFixed ReeTag.F4 K 0),
      Rep nPts (wT (texpand [16, 2, 5])) (u : reeFixed ReeTag.F4 K 0) :=
    ⟨⟨tword K [16, 2, 5], tword_mem hT hw3⟩, rep_tword [16, 2, 5]⟩
  obtain ⟨u4, r4⟩ : ∃ u : commutator (reeFixed ReeTag.F4 K 0),
      Rep nPts (wT (texpand [24, 2, 18])) (u : reeFixed ReeTag.F4 K 0) :=
    ⟨⟨tword K [24, 2, 18], tword_mem hT hw4⟩, rep_tword [24, 2, 18]⟩
  have q0 : u0 ^ 2 = 1 := eqD (repD_pow r0 2) repD_one hs0
  have q1 : u1 ^ 2 = 1 := eqD (repD_pow r1 2) repD_one hs1
  have q2 : u2 ^ 2 = 1 := eqD (repD_pow r2 2) repD_one hs2
  have q3 : u3 ^ 2 = 1 := eqD (repD_pow r3 2) repD_one hs3
  have q4 : u4 ^ 2 = 1 := eqD (repD_pow r4 2) repD_one hs4
  have k01 : Commute u0 u1 := eqD (repD_mul r0 r1) (repD_mul r1 r0) c01
  have k02 : Commute u0 u2 := eqD (repD_mul r0 r2) (repD_mul r2 r0) c02
  have k03 : Commute u0 u3 := eqD (repD_mul r0 r3) (repD_mul r3 r0) c03
  have k04 : Commute u0 u4 := eqD (repD_mul r0 r4) (repD_mul r4 r0) c04
  have k12 : Commute u1 u2 := eqD (repD_mul r1 r2) (repD_mul r2 r1) c12
  have k13 : Commute u1 u3 := eqD (repD_mul r1 r3) (repD_mul r3 r1) c13
  have k14 : Commute u1 u4 := eqD (repD_mul r1 r4) (repD_mul r4 r1) c14
  have k23 : Commute u2 u3 := eqD (repD_mul r2 r3) (repD_mul r3 r2) c23
  have k24 : Commute u2 u4 := eqD (repD_mul r2 r4) (repD_mul r4 r2) c24
  have k34 : Commute u3 u4 := eqD (repD_mul r3 r4) (repD_mul r4 r3) c34
  have hprod : ∀ n : ℕ, 1 ≤ n → n < 32 →
      u0 ^ (n % 2) * u1 ^ (n / 2 % 2) * u2 ^ (n / 4 % 2) * u3 ^ (n / 8 % 2) *
        u4 ^ (n / 16 % 2) ≠ 1 := by
    intro n hn1 hn2
    have h1 := (allIn_eq_true.1 hall) (n - 1) (Nat.zero_le _) (by omega)
    rw [Nat.sub_add_cancel hn1, Bool.not_eq_true'] at h1
    exact neD (repD_mul (repD_mul (repD_mul (repD_mul (repD_pow r0 _) (repD_pow r1 _))
      (repD_pow r2 _)) (repD_pow r3 _)) (repD_pow r4 _)) repD_one h1
  refine ⟨![u0, u1, u2, u3, u4], ?_, commute_fin_five _ k01 k02 k03 k04 k12 k13 k14 k23 k24 k34,
    hker_of_digits _ (by simpa using hprod)⟩
  intro i
  fin_cases i
  exacts [q0, q1, q2, q3, q4]

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.SectionRank CFSG.SectionRank.TitsGen CFSG.SectionRank.TitsOrder
  CFSG.SectionRank.Native.Tits CFSG.SectionRank.TitsLocal CFSG.Sporadic.Th CFSG.Perm
  CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap invT invOK idT compT powT Table allIn wordT)

theorem t_Tits :
    S_Tits := by
  intro G _ _ h
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_titsGroup_of_model h
  obtain ⟨u, hsq, hcomm, hker⟩ := Tits_commuting_involutions hK
  exact not_gen4_of_mulEquiv e.symm (not_gen4_of_commuting_involutions le_rfl u hsq hcomm hker)

end CFSG.GH74.Filter
