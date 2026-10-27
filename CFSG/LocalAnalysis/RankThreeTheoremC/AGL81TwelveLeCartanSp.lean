module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

theorem centralizes_of_idxBTwo (hZ : OddCenterRest) {A : Type} [Group A] [Finite A]
    {Y P : Subgroup A} (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hB2 : IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P) {β : A}
    (hβ : Odd (orderOf β)) (hβY : β ∈ normalizer (Y : Set A))
    (hβP : β ∈ normalizer (P : Set A)) (hW : ParabComm.WCent P β) :
    ∀ y ∈ Y, β * y = y * β := by
  obtain ⟨y, hyP, hyodd, hconj⟩ :=
    ParabCensus.exists_mem_of_normalizer_spTwo hZ hY hO hB2 hP hβ hβY hβP
  have hPY : P ≤ Y := hP.1
  have hprod : ParabCensus.IsSpTwoLeviProduct ↥P :=
    ParabCensus.isSpTwoLeviProduct_of_parabolic hZ hY hO hB2 hP
  let q := QuotientGroup.mk' (CFSG.pCore 2 ↥P)
  let ŷ : ↥P ⧸ CFSG.pCore 2 ↥P := q ⟨y, hyP⟩
  have hcen : ŷ ∈ centralizer (wSup (↥P ⧸ CFSG.pCore 2 ↥P) : Set (↥P ⧸ CFSG.pCore 2 ↥P)) := by
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥P) w
    have hpP : (p : A) ∈ P := p.2
    have hz : y * (p : A) * y⁻¹ * (p : A)⁻¹ ∈ pCoreOf 2 P := by
      have h := hW (p : A) hpP (by simpa [q, QuotientGroup.mk'_apply] using hw)
      rwa [hconj (p : A) (hPY hpP)] at h
    have hzP : (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P) ∈ CFSG.pCore 2 ↥P := by
      rw [← CFSG.mem_openPCoreOf_iff (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P)]
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hz
    have h1 : ŷ * q p * ŷ⁻¹ * (q p)⁻¹ = 1 := by
      have h := (QuotientGroup.eq_one_iff
        (⟨y, hyP⟩ * p * ⟨y, hyP⟩⁻¹ * p⁻¹ : ↥P)).mpr hzP
      simpa [ŷ, q, map_mul, map_inv, QuotientGroup.mk'_apply] using h
    have h2 : q p * ŷ = ŷ * q p := by
      have h2' : ŷ * q p * ŷ⁻¹ = q p := by
        have := congrArg (fun t => t * q p) h1
        simpa [mul_assoc] using this
      have := congrArg (fun t => t * ŷ) h2'
      simpa [mul_assoc] using this.symm
    exact h2
  have hŷ1 : ŷ = 1 := by
    have hmem := hcen
    rw [hprod.centralizer_wSup_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hy1 : y = 1 := ParabCensus.eq_one_of_odd_of_pCore_quotient_eq_one hyP hyodd hŷ1
  intro y' hy'
  have h := hconj y' hy'
  rw [hy1] at h
  have h' : β * y' * β⁻¹ = y' := by simpa using h
  have h'' := congrArg (fun t => t * β) h'
  simpa [mul_assoc] using h''

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
