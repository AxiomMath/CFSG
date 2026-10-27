module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycle
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryEmbed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT Matrix
open scoped MatrixGroups

section H1Conj

variable {k : Type} [Field k]

theorem conj_rootSL2_of_mem_h1F4 {v : ModGL .F4 k} (hv : v ∈ h1F4 k) (A : SL2 k) :
    ∃ A' : SL2 k, v⁻¹ * rootSL2 .F4 k thetaF4 A * v = rootSL2 .F4 k thetaF4 A' := by
  obtain ⟨n, hn, B, rfl⟩ := hv
  obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_F4 (inv_mem hn) A
  rw [inv_inv] at hA'
  refine ⟨B⁻¹ * A' * B, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hA']
  group

end H1Conj

section Final

variable {p e : ℕ} [Fact p.Prime]

theorem a2Pairing_F4 : A2Pairing thetaF4 deltaF4 :=
  ⟨by rw [iform_thetaF4_self, isPartnerF4_deltaF4.2.1], by rw [iform_thetaF4_self]; norm_num,
    by rw [isPartnerF4_deltaF4.2.2, iform_thetaF4_self]; norm_num⟩

theorem a2UnitaryF4 : A2UnitaryF4 p e := by
  intro hadm hp2 hq R₂ c₂ hR₂ hc₂ ho _ _ ⟨v, hv, hd, m, hm, hcoc⟩
  have hne : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hk2 : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  have hcardE : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  obtain ⟨Em⟩ := nonempty_a2Embedding_F4 (GaloisField p (2 * e))
  have hcocycle := cocycle_conj_pinnedX p hk2 e
    (entrywiseFrobGL_baseChangeGL_algebraMap (c₂ : ModGL .F4 (GaloisField p e))) hd hm hcoc
  have hv' : ∀ t ∈ torusGroup .F4 (AlgClosGF p e), t * v ∈ h1F4 (AlgClosGF p e) :=
    fun t ht => mul_mem (levi_le_h1F4 (torusGroup_le_parabolicLevi JF4 ht)) hv
  obtain ⟨θ, hinj, hB12', hneg⟩ := exists_unitary_hom hp2 hq isRoot_thetaF4
    isPartnerF4_deltaF4.1 a2Pairing_F4 Em hd hcocycle
    (fun t ht => rootDiagUnit_mul_comm_of_mem_torusGroup (corootDiagF4 deltaF4 (-1)) ht)
    (fun t ht => h1F4_le_adjointGroup (hv' t ht))
    (fun t ht A => conj_rootSL2_of_mem_h1F4 (hv' t ht) A)
    (fun j => by
      rw [rootTorusSL2_corootDiagF4 isPartnerF4_deltaF4.1 isPartnerF4_deltaF4.2.1,
        baseChangeGL_rootDiagUnit_corootDiagF4 j deltaF4]
      rfl)
  have hB12eq : (Phan.B12 (GaloisField p (2 * e)) p e).map θ =
      stdRankOne (f4Datum (GaloisField p e)) thetaF4 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
      obtain ⟨A₀, hA₀⟩ := hB12' A
      exact (mem_stdRankOne_f4_iff' isRoot_thetaF4 _).2 ⟨A₀, hA₀⟩
    · rw [natCard_rankOne hp2 (stdRankOne (f4Datum (GaloisField p e)) thetaF4)
        (fun g => mem_stdRankOne_f4_iff' isRoot_thetaF4 g),
        Subgroup.card_map_of_injective hinj, natCard_B12 hcardE]
  have hB23eq : (Phan.B23 (GaloisField p (2 * e)) p e).map θ = R₂ := by
    have h1 : (Phan.B23 (GaloisField p (2 * e)) p e).map θ =
        (stdRankOne (f4Datum (GaloisField p e)) thetaF4).map
          (MulAut.conj (θ (swapElt (GaloisField p (2 * e)) p e))).toMonoidHom := by
      rw [← map_conj_swapElt_B12 (GaloisField p (2 * e)) p e, Subgroup.map_map, ← hB12eq,
        Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
    have hR' := map_conj_mem_longestFundamental (θ (swapElt (GaloisField p (2 * e)) p e))
      (stdRankOne_mem_longestFundamental (p := p) (e := e) isRoot_thetaF4 iform_thetaF4_self)
    have hc : c₂ ∈ (Phan.B23 (GaloisField p (2 * e)) p e).map θ :=
      ⟨_, ⟨suNegOne (GaloisField p (2 * e)) p e, rfl⟩, hneg⟩
    rw [h1] at hc ⊢
    exact eq_of_mem_longestFundamental_F4 hp2 hadm hR' hR₂ hc hc₂ ho
  exact ⟨θ.range, unitaryBlockStandardPair_of_normalized
    (by rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]; exact bot_le) rfl hB12eq hB23eq⟩

end Final

end CFSG.ClassicalInvolution.ModelFacts.Levi
