module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE7Embed
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryE7Cocycle
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Pair
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2InterfaceE7
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Rational
public import CFSG.ClassicalInvolution.Models.SymplecticPairs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT Matrix
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open scoped MatrixGroups

section H1Conj

variable {k : Type} [Field k]

theorem conj_rootSL2_of_mem_h1E7 {v : ModGL .E7 k} (hv : v ∈ h1E7 k) (A : SL2 k) :
    ∃ A' : SL2 k, v⁻¹ * rootSL2 .E7 k thetaE7 A * v = rootSL2 .E7 k thetaE7 A' := by
  obtain ⟨n, hn, B, rfl⟩ := hv
  obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E7 (inv_mem hn) A
  rw [inv_inv] at hA'
  refine ⟨B⁻¹ * A' * B, ?_⟩
  rw [map_mul, map_mul, map_inv, ← hA']
  group

end H1Conj

section Final

variable {p e : ℕ} [Fact p.Prime]

local notation "ψ" => e7Isogeny (GaloisField p e)

theorem a2Pairing_E7 : A2Pairing thetaE7 deltaE7 := by
  have h1 := iform_self_isRoot_E7 isRoot_thetaE7
  have h2 := iform_self_isRoot_E7 isPartnerE7_deltaE7.1
  exact ⟨by rw [h1, h2], by rw [h1]; norm_num, by rw [isPartnerE7_deltaE7.2, h1]; norm_num⟩

theorem a2UnitaryImageE7 (hadm : StatedLieAdmissible .E7 0 p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    {R₂ : Subgroup (E7sc p e)} {c₂ : E7sc p e}
    (hR₂ : R₂ ∈ longestFundamental (e7Datum (GaloisField p e))) (hc₂ : c₂ ∈ R₂)
    (ho : orderOf c₂ = 2)
    (hv : ∃ v ∈ h1E7 (AlgClosGF p e),
      v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
          ((e7Isogeny (GaloisField p e) c₂ : ↥(adjointGroup .E7 (GaloisField p e))) :
            ModGL .E7 (GaloisField p e)) * v⁻¹ = signDiagE7 (AlgClosGF p e) deltaE7 ∧
      ∃ m ∈ parabolicLevi .E7 (AlgClosGF p e) JE7,
        entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹ =
          m * rootSL2 .E7 (AlgClosGF p e) thetaE7 WSL) :
    ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * e)) p e W
      ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map ψ) (R₂.map ψ) := by
  obtain ⟨v, hv, hd, m, hm, hcoc⟩ := hv
  have hne : NeZero e := ⟨by rintro rfl; simp at hq⟩
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hk2 : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  have hcardE : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  obtain ⟨Em⟩ := nonempty_a2Embedding_E7 (GaloisField p (2 * e))
  have hcocycle := cocycle_conj_pinnedX_E7 p hk2 e
    (entrywiseFrobGL_baseChangeGL_algebraMap
      ((ψ c₂ : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e))) hd hm hcoc
  have hv' : ∀ t ∈ torusGroup .E7 (AlgClosGF p e), t * v ∈ h1E7 (AlgClosGF p e) :=
    fun t ht => mul_mem (levi_le_h1E7 (torusGroup_le_parabolicLevi JE7 ht)) hv
  obtain ⟨θ, hinj, hB12', hneg⟩ := exists_unitary_hom hp2 hq isRoot_thetaE7
    isPartnerE7_deltaE7.1 a2Pairing_E7 Em hd hcocycle
    (fun t ht => rootDiagUnit_mul_comm_of_mem_torusGroup (thetaDiag deltaE7 (-1)) ht)
    (fun t ht => h1E7_le_adjointGroup (hv' t ht))
    (fun t ht A => conj_rootSL2_of_mem_h1E7 (hv' t ht) A)
    (fun j => by
      rw [rootSL2_HSL_eq_thetaDiag_E7 isPartnerE7_deltaE7.1,
        baseChangeGL_rootDiagUnit_thetaDiag_E7 j deltaE7]
      rfl)
  have hR₁ := stdRankOne_mem_longestFundamental_E7 (p := p) (e := e) hadm isRoot_thetaE7
  have hmap := map_stdRankOne_e7_root (p := p) (e := e) isRoot_thetaE7
  have hB12eq : (Phan.B12 (GaloisField p (2 * e)) p e).map θ =
      (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map ψ := by
    rw [hmap]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, ⟨A, rfl⟩, rfl⟩
      obtain ⟨A₀, hA₀⟩ := hB12' A
      exact (mem_stdRankOne_e7_iff' isRoot_thetaE7 _).2 ⟨A₀, hA₀⟩
    · rw [natCard_rankOne hp2 (stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7)
        (fun g => mem_stdRankOne_e7_iff' isRoot_thetaE7 g),
        Subgroup.card_map_of_injective hinj, natCard_B12 hcardE]
  obtain ⟨g, hg⟩ := e7Isogeny_surjective (GaloisField p e)
    (θ (swapElt (GaloisField p (2 * e)) p e))
  have hB23eq : (Phan.B23 (GaloisField p (2 * e)) p e).map θ =
      ((stdRankOne (e7Datum (GaloisField p e)) thetaE7).map (MulAut.conj g).toMonoidHom).map ψ := by
    rw [map_conj_map_e7, hg, ← map_conj_swapElt_B12 (GaloisField p (2 * e)) p e,
      Subgroup.map_map, ← hB12eq, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hR₃ := map_conj_mem_longestFundamental g hR₁
  set R₃ := (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map (MulAut.conj g).toMonoidHom
    with hR₃def
  have hc : ψ c₂ ∈ R₃.map ψ := by
    rw [← hB23eq, ← hneg]
    exact ⟨_, ⟨suNegOne (GaloisField p (2 * e)) p e, rfl⟩, rfl⟩
  obtain ⟨c₃, hc₃, hc₃ψ⟩ := hc
  have hinjR₃ : ∀ x ∈ R₃, ψ x = 1 → x = 1 := by
    intro x hx hx1
    obtain ⟨y, hy, rfl⟩ := hx
    have : ψ y = 1 := by
      have h : ψ g * ψ y * (ψ g)⁻¹ = 1 := by simpa using hx1
      calc ψ y = (ψ g)⁻¹ * (ψ g * ψ y * (ψ g)⁻¹) * ψ g := by group
        _ = 1 := by rw [h]; group
    simp [injOn_e7Isogeny_stdRankOne hp2 hadm isRoot_thetaE7 y hy this]
  have hc₂ne : ψ c₂ ≠ 1 := by
    rw [← hneg]
    intro h1
    have := hinj (h1.trans (map_one θ).symm)
    have h2 := embSUid_injective (unitaryInvolution (GaloisField p (2 * e)) p e) 0
      (this.trans (map_one _).symm)
    have h3 := congrArg
      (fun s : Su (GaloisField p (2 * e)) p e 2 => suMat s 0 0) h2
    have h4 : (-1 : GaloisField p (2 * e)) = 1 := by
      simpa [suNegOne, suMat, Units.val_neg] using h3
    have h5 : ((2 : ℕ) : GaloisField p (2 * e)) = 0 := by
      push_cast
      linear_combination -h4
    have h6 := (CharP.cast_eq_zero_iff (GaloisField p (2 * e)) p 2).1 h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h6)
  have ho₃ : orderOf c₃ = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h2 : ψ (c₃ ^ 2) = 1 := by
        have ho_sq : c₂ ^ 2 = 1 := by
          have := pow_orderOf_eq_one c₂
          rwa [ho] at this
        rw [map_pow, hc₃ψ, ← map_pow, ho_sq, map_one]
      exact hinjR₃ _ (R₃.pow_mem hc₃ 2) h2
    · intro h1
      exact hc₂ne (by rw [← hc₃ψ, h1, map_one])
  have hRR : R₃ = R₂ := eq_of_mem_longestFundamental_E7 hp2 hq hadm hR₃ hR₂ hc₃ hc₂ ho₃ ho
    (by exact_mod_cast congrArg Subtype.val hc₃ψ)
  have hker : θ.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e 3) := by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]
    exact bot_le
  refine ⟨θ.range, unitaryBlockStandardPair_of_normalized hker rfl hB12eq ?_⟩
  rw [hB23eq, hRR]

end Final

end CFSG.ClassicalInvolution.ModelFacts.Levi
