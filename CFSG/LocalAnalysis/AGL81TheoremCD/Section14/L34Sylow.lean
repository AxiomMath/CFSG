module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Cases
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.KFacts.L34Max
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem nonempty_mulEquiv_projSL_of_lie_A2_four (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d.1 = .A 2 Q) :
    Nonempty ((TauCeti.CFSGIndex.lie d).Group ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 2)) := by
  obtain ⟨Q, hQ, hd⟩ := hd
  have hv : (TauCeti.LieTypeIndex.A 2 Q).Valid := hd ▸ d.2
  have hd' : d = ⟨.A 2 Q, hv⟩ := Subtype.ext hd
  have hLie := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 2 Q hv
  have hStated : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group .PSL 3 Q.p Q.exponent := by
    rcases hLie.2 with hc | hexc
    · exact hc
    · exact absurd hexc.1 (by norm_num)
  have hLieB : CFSG.Blueprint.LieModel
      (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group .PSL 3 Q.p Q.exponent :=
    Or.inl ⟨by decide, hStated⟩
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eK⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLieB
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard4 : Nat.card K = 2 ^ 2 := by
    rw [hKcard, ← TauCeti.PrimePower.card_def, hQ]
    norm_num
  let φ : K ≃+* GaloisField 2 2 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 2 (by norm_num) hcard4
  let eField : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 K).symm.trans
      ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3)).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          3 (GaloisField 2 2)))
  have eFull : (TauCeti.CFSGIndex.lie ⟨.A 2 Q, hv⟩).Group ≃*
      projSL 3 (GaloisField 2 2) :=
    eK.trans (eField.trans
      (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3
        (GaloisField 2 2)).symm)
  exact ⟨by rw [hd']; exact eFull⟩

theorem nonempty_mulEquiv_projSL_quotient_center_of_isL34Type {L : Type*} [Group L]
    (hL : IsL34Type L) :
    Nonempty ((L ⧸ Subgroup.center L) ≃* CFSG.PGLModel.projSL 3 (GaloisField 2 2)) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hL
  exact ⟨e.trans (nonempty_mulEquiv_projSL_of_lie_A2_four d hd).some⟩

theorem nonempty_mulEquiv_projSL_of_isL34Type {L : Type*} [Group L] (hL : IsL34Type L)
    (hZ : Nat.card (Subgroup.center L) = 1) :
    Nonempty (L ≃* projSL 3 (GaloisField 2 2)) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hL
  obtain ⟨eFull⟩ := nonempty_mulEquiv_projSL_of_lie_A2_four d hd
  have hcenter : Subgroup.center L = ⊥ :=
    Subgroup.eq_bot_of_card_eq (Subgroup.center L) hZ
  let eBot : L ⧸ Subgroup.center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq (G := L) (M := Subgroup.center L) (N := ⊥)
      hcenter).trans (QuotientGroup.quotientBot (G := L))
  exact ⟨eBot.symm.trans (e.trans eFull)⟩


theorem eq_top_of_normalizer_le_of_dvd {X : Type*} [Group X]
    (e : X ≃* projSL 3 (GaloisField 2 2)) {E Y : Subgroup X}
    (hE : Nat.card E = 9) (hEY : Subgroup.normalizer (E : Set X) ≤ Y)
    (h64 : 64 ∣ Nat.card Y) : Y = ⊤ := by
  by_contra hY
  have hY72 : Nat.card Y = 72 := by
    rw [eq_normalizer_of_normalizer_le e hE hEY hY,
      card_normalizer_of_card_eq_nine e hE]
  rw [hY72] at h64
  have hnot : ¬ (64 ∣ 72) := by norm_num
  exact hnot h64

theorem not_le_of_isSylowOf_two {K M A S : Subgroup G}
    (hK : Nonempty ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃*
      projSL 3 (GaloisField 2 2)))
    (hO : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ M) (hKM : ¬ K ≤ M)
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ K ≤ M)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K) : ¬ S ≤ M := by
  classical
  rintro hSM
  set N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K with hNdef
  set π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N with hπdef
  set A' : Subgroup ↥K := A.subgroupOf K with hA'def
  set Abar : Subgroup (↥K ⧸ N) := A'.map π with hAbardef
  set Y : Subgroup (↥K ⧸ N) := ((K ⊓ M).subgroupOf K).map π with hYdef
  have hNnormal : N.Normal := hNdef ▸ CFSG.pPrimeCore_normal (p := 3) (G := ↥K)
  haveI : N.Normal := hNnormal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA'p : IsPGroup 3 ↥A' := hA'def ▸ hA.isPGroup.comap_subtype
  haveI : Fact (IsPGroup 3 ↥A') := ⟨hA'p⟩
  have hnorm : Subgroup.normalizer Abar = (Subgroup.normalizer A').map π := by
    rw [hAbardef]
    exact normalizer_map_quotient_eq_map_normalizer 3 A' N
      (CFSG.pPrimeCore_normal (p := 3) (G := ↥K))
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
  have hnormA : (Subgroup.normalizer A').map K.subtype =
      Subgroup.normalizer (A : Set G) ⊓ K := by
    rw [normalizer_subgroupOf_eq_subgroupOf_inf_normalizer K A hA.le,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left, inf_comm]
  have hNKA_le : Subgroup.normalizer A' ≤ (K ⊓ M).subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxG : (x : G) ∈ Subgroup.normalizer (A : Set G) := by
      have hxmap : (x : G) ∈ (Subgroup.normalizer A').map K.subtype :=
        Subgroup.mem_map_of_mem K.subtype hx
      rw [hnormA] at hxmap
      exact hxmap.1
    exact ⟨x.2, hNA ⟨hxG, x.2⟩⟩
  have hEY : Subgroup.normalizer Abar ≤ Y := by
    rw [hnorm, hYdef]
    exact Subgroup.map_mono hNKA_le
  have hcardQuot : Nat.card (↥K ⧸ N) = 20160 := by
    obtain ⟨eK⟩ := hK
    rw [Nat.card_congr eK.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_projSL
  have hf3 : (20160 : ℕ).factorization 3 = 2 := by
    rw [show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hf2 : (20160 : ℕ).factorization 2 = 6 := by
    rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨Q3, hQ3⟩ := hA.exists_sylow_eq_subgroupOf
  set Qbar3 : Sylow 3 (↥K ⧸ N) :=
    Q3.mapSurjective (f := π) (QuotientGroup.mk'_surjective N) with hQbar3def
  have hE : Nat.card Abar = 9 := by
    have h1 : Abar = (Qbar3 : Subgroup (↥K ⧸ N)) := by
      rw [hAbardef, hQbar3def,
        Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective N), hQ3]
    rw [h1, Sylow.card_eq_multiplicity, hcardQuot, hf3]
    norm_num
  obtain ⟨Q2, hQ2⟩ := hS.exists_sylow_eq_subgroupOf
  set Sbar : Sylow 2 (↥K ⧸ N) :=
    Q2.mapSurjective (f := π) (QuotientGroup.mk'_surjective N) with hSbardef
  have h64 : 64 ∣ Nat.card Y := by
    have hSbar_le : (Sbar : Subgroup (↥K ⧸ N)) ≤ Y := by
      intro x hx
      rw [hSbardef,
        Sylow.coe_mapSurjective (f := π) (QuotientGroup.mk'_surjective N), hQ2,
        Subgroup.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [Subgroup.mem_subgroupOf] at hs
      exact Subgroup.mem_map_of_mem π
        (Subgroup.mem_subgroupOf.mpr ⟨s.2, hSM hs⟩)
    have hcardS : Nat.card (Sbar : Subgroup (↥K ⧸ N)) = 64 := by
      rw [Sylow.card_eq_multiplicity, hcardQuot, hf2]
      norm_num
    rw [← hcardS]
    exact Subgroup.card_dvd_of_le hSbar_le
  have hYtop : Y = ⊤ := by
    obtain ⟨eK⟩ := hK
    exact eq_top_of_normalizer_le_of_dvd eK hE hEY h64
  have hKM' : K ≤ M := by
    intro k hk
    have hkY : π ⟨k, hk⟩ ∈ Y := by
      rw [hYtop]
      exact Subgroup.mem_top _
    rw [hYdef, Subgroup.mem_map] at hkY
    obtain ⟨m, hm, hπm⟩ := hkY
    rw [Subgroup.mem_subgroupOf] at hm
    have hker : m⁻¹ * (⟨k, hk⟩ : ↥K) ∈ N := by
      have h1 : π (m⁻¹ * ⟨k, hk⟩) = 1 := by
        rw [map_mul, map_inv, hπm, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (N := N) _).mp h1
    have hGM : ((m⁻¹ * (⟨k, hk⟩ : ↥K) : ↥K) : G) ∈ M :=
      hO (Subgroup.mem_map_of_mem K.subtype hker)
    have hk_eq : (k : G) = (m : G) * ((m⁻¹ * (⟨k, hk⟩ : ↥K) : ↥K) : G) := by
      simp [mul_assoc]
    rw [hk_eq]
    exact M.mul_mem hm.2 hGM
  exact hKM hKM'

namespace IsL34Star

theorem not_le_of_isSylowOf_two {K M A S : Subgroup G}
    (hK : IsL34Star K) (hO : (CFSG.pPrimeCore 3 ↥K).map K.subtype ≤ M)
    (hKM : ¬ K ≤ M) (hA : CFSG.ABGLocalTools.IsSylowOf 3 A K)
    (hNA : Subgroup.normalizer (A : Set G) ⊓ K ≤ M)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K) : ¬ S ≤ M := by
  refine CFSG.LocalAnalysis.AGL81TheoremCD.Section14.not_le_of_isSylowOf_two
    (K := K) (M := M) (A := A) (S := S) ?_ hO hKM hA hNA hS
  exact nonempty_mulEquiv_projSL_of_isL34Type hK.1 hK.2

end IsL34Star

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
