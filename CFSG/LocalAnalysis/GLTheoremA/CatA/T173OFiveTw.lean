module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwTheta
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwBig
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwMult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveAltIV
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OTwSU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveStd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDModel2
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TwE6RootKill
open CFSG.SeitzReduction.TwistedE6Pilot CFSG.LieType.Chevalley.E6GraphLevi

local notation "Γ₂" F => ModGL TwistTag.E6.tag F



variable {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}

private theorem exists_std_and_conj_levi_twE6 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hcfg : Cfg173 3 S B N D K x) (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (M : S172DModel S B (twistedE6RootGroup F σ) (twistedE6InndiagGL F σ)) :
    ∃ d ∈ M.barB, d ≠ 1 ∧ d ^ 3 = 1 ∧
      M.piImg K = stdLayerD (twistedE6RootGroup F σ) d ∧
      IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
        (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F))) ∧
      M.barB ⊓ Subgroup.centralizer
        (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) = Subgroup.zpowers d ∧
      ∃ g ∈ twistedE6RootGroup F σ, ∃ J : Set (Fin TwistTag.E6.foldedTag.rank), J ≠ Set.univ ∧
        M.barB.map (MulAut.conj g).toMonoidHom ≤
          graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ∧
        (stdLayerD (twistedE6RootGroup F σ) d).map (MulAut.conj g).toMonoidHom ≤
          graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
  classical
  obtain ⟨d, hdbar, hd1, hd3, -, hdK, hcomp, hcent⟩ := S172DModel.exists_stdD hcfg M
  have hAel : IsElemAbelian 3 M.barB := S172DModel.isElemAbelian_barB hcfg M
  have hA3 : IsPGroup 3 M.barB := hAel.isPGroup
  have hAG : M.barB ≤ twistedE6InndiagGL F σ :=
    Subgroup.map_subtype_le (H := twistedE6InndiagGL F σ) M.β.range
  obtain ⟨R, hRne, hR2, hRG, hRnorm⟩ :=
    S172DModel.exists_twoGroup_normalized_by_piImg_sup_barB hcfg M
  have hAN : M.barB ≤ Subgroup.normalizer (R : Set (Γ₂ F)) := le_trans le_sup_right hRnorm
  have hLN : M.piImg K ≤ Subgroup.normalizer (R : Set (Γ₂ F)) :=
    le_trans (Subgroup.map_mono (Subgroup.map_mono
      (Subgroup.subgroupOf_mono S (le_closureIn_self K N)))) (le_trans le_sup_left hRnorm)
  obtain ⟨g, hgC, J, hJ, hAg, hKg⟩ :=
    exists_conj_levi_twE6 hF σ hσ hRne hR2 hRG hA3 hAG hAN hLN hdbar
      (le_of_eq hdK.symm) hcomp
  have hcent' : M.barB ⊓ Subgroup.centralizer
      (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) = Subgroup.zpowers d := by
    rw [← hdK]
    exact hcent
  exact ⟨d, hdbar, hd1, hd3, hdK, hcomp, hcent', g, hgC, J, hJ, hAg, hKg⟩

private theorem exists_conj_std_data_twE6 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hcfg : Cfg173 3 S B N D K x) (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    (M : S172DModel S B (twistedE6RootGroup F σ) (twistedE6InndiagGL F σ)) :
    ∃ (J : Set (Fin TwistTag.E6.foldedTag.rank))
      (M' : S172DModel S B (twistedE6RootGroup F σ) (twistedE6InndiagGL F σ)) (d' : Γ₂ F),
      J ≠ Set.univ ∧
      M'.barB ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ ∧
      3 ^ 4 ≤ Nat.card M'.barB ∧ IsElemAbelian 3 M'.barB ∧
      d' ∈ M'.barB ∧ d' ≠ 1 ∧ d' ^ 3 = 1 ∧
      M'.piImg K = stdLayerD (twistedE6RootGroup F σ) d' ∧
      IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d')
        (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d'} : Set (Γ₂ F))) ∧
      M'.barB ⊓ Subgroup.centralizer
        (stdLayerD (twistedE6RootGroup F σ) d' : Set (Γ₂ F)) = Subgroup.zpowers d' ∧
      stdLayerD (twistedE6RootGroup F σ) d' ≤
        graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
  classical
  obtain ⟨d, hdbar, hd1, hd3, hdK, hcomp, hcent, g, hgC, J, hJ, hAg, hKg⟩ :=
    exists_std_and_conj_levi_twE6 hcfg hF σ hσ M
  have hgG : g ∈ twistedE6InndiagGL F σ := M.le hgC
  have hgN : g ∈ Subgroup.normalizer (twistedE6RootGroup F σ : Set (Γ₂ F)) :=
    twistedE6InndiagGL_le_normalizer F σ hgG
  obtain ⟨M', hbar', hpi', -⟩ := S172DModel.exists_conj M hgG hgN
  obtain ⟨d', hd'bar, hd'1, hd'3, -, hd'K, hcomp', hcent'⟩ := S172DModel.exists_stdD hcfg M'
  have hcent'' : M'.barB ⊓ Subgroup.centralizer
      (stdLayerD (twistedE6RootGroup F σ) d' : Set (Γ₂ F)) = Subgroup.zpowers d' := by
    rw [← hd'K]
    exact hcent'
  have hA'L : M'.barB ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ := by
    rw [hbar']
    exact hAg
  have hK'L : stdLayerD (twistedE6RootGroup F σ) d' ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
    rw [← hd'K, hpi' K, hdK]
    exact hKg
  have hbar4 : 3 ^ 4 ≤ Nat.card M'.barB := by
    rw [hbar', Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact three_pow_four_le_card_barB_twE6 hcfg hF σ hσ h3 M
  exact ⟨J, M', d', hJ, hA'L, hbar4,
    S172DModel.isElemAbelian_barB hcfg M', hd'bar, hd'1, hd'3, hd'K, hcomp', hcent'', hK'L⟩

private theorem two_dvd_card_stdLayerD_su_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 2) {σ : F ≃+* F} {d : Γ₂ F} {n : ℕ} (hn : 3 ≤ n)
    (hn3 : Nat.Coprime n 3)
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →*
      ↥(stdLayerD (twistedE6RootGroup F σ) d))
    (hρ : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2)) :
    2 ∣ Nat.card (stdLayerD (twistedE6RootGroup F σ) d) := by
  have hker : ρ.ker = ⊥ := le_bot_iff.mp (hρk.trans (center_su_two_eq_bot hF hn hn3).le)
  let e : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) ≃*
      ↥(stdLayerD (twistedE6RootGroup F σ) d) :=
    MulEquiv.ofBijective ρ ⟨(MonoidHom.ker_eq_bot_iff ρ).1 hker, hρ⟩
  rw [← Nat.card_congr e.toEquiv]
  have htp : CFSG.LocalAnalysis.GLTheoremA.S10.twoPart
      (Nat.card ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2)) = 2 ^ (1 * (n * (n - 1) / 2)) :=
    CFSG.LocalAnalysis.GLTheoremA.FQ.twoPart_card_SU (n := n) (g := 1) hn le_rfl
      (by simpa using hF)
  have hdvd : CFSG.LocalAnalysis.GLTheoremA.S10.twoPart
      (Nat.card ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2)) ∣
      Nat.card ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) := Nat.ordProj_dvd _ _
  rw [htp] at hdvd
  have hexp : 1 * (n * (n - 1) / 2) ≠ 0 := by
    have : 6 ≤ n * (n - 1) := by
      calc 6 = 3 * 2 := by norm_num
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    omega
  exact (dvd_pow_self 2 hexp).trans hdvd

private theorem su_layer_data_twE6 {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    (hcfg : Cfg173 3 S B N D K x)
    (M : S172DModel S B (twistedE6RootGroup F σ) (twistedE6InndiagGL F σ))
    (hF : Nat.card F = 2 ^ 2) {d : Γ₂ F}
    (hdK : M.piImg K = stdLayerD (twistedE6RootGroup F σ) d) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →*
      ↥(stdLayerD (twistedE6RootGroup F σ) d))
    (hρ : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2)) :
    (∀ k ∈ K, k ∈ Subgroup.centralizer (S : Set Ω) → k ^ 3 = 1 → k = 1) ∧
      2 ∣ Nat.card (M.piImg K) := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hcop : Nat.Coprime n 3 := by rcases hn with rfl | rfl <;> norm_num
  let e : ↥(stdLayerD (twistedE6RootGroup F σ) d) ≃* ↥(M.piImg K) :=
    MulEquiv.subgroupCongr hdK.symm
  let ρM : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →* ↥(M.piImg K) :=
    e.toMonoidHom.comp ρ
  have hρM : Function.Surjective ρM := e.surjective.comp hρ
  have hkerM : ρM.ker = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact e.map_eq_one_iff
  have hKZ := eq_one_of_mem_inf_centralizer_of_su_two hcfg M hF hn ρM hρM
    (by rw [hkerM]; exact hρk)
  have h2 := two_dvd_card_stdLayerD_su_two hF hn3 hcop ρ hρ hρk
  exact ⟨hKZ, by rw [hdK]; exact h2⟩

private theorem exists_inner_pair_twE6 {F : Type} [Field F] [Finite F] {f : ℕ} {k : Type}
    [Field k] [Algebra k F] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hF : Nat.card F = (2 ^ f) ^ 2) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (h3 : 3 ∣ 2 ^ f + 1) {A L : Subgroup (Γ₂ F)}
    (hA : A ≤ Subgroup.centralizer
      (E6GraphLevi.thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F)))
    (hL : L ≤ CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ) :
    ∃ t ∈ twistedE6RootGroup F σ, ∃ s ∈ twistedE6RootGroup F σ, t ^ 2 = 1 ∧ s ^ 2 = 1 ∧
      t ∈ Subgroup.centralizer ((A ⊔ L : Subgroup (Γ₂ F)) : Set (Γ₂ F)) ∧
      s ∈ Subgroup.centralizer ((A ⊔ L : Subgroup (Γ₂ F)) : Set (Γ₂ F)) ∧
      (t * s) ^ 3 = 1 ∧ t * s ∉ A := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨t, htJ, s, hsJ, ht2, hs2, hts3, htsnot⟩ :=
    exists_involution_pair_thetaRankOneGroup hf hk hF hσ h3
  have hJle : E6GraphLevi.thetaRankOneGroup (algebraMap k F) ≤
      twistedE6RootGroup F σ :=
    CFSG.SeitzReduction.TwistedE6Pilot.thetaRankOneGroup_le_C0 hf hk hF hσ
  have hsu6C : CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom ≤
      Subgroup.centralizer (E6GraphLevi.thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F)) :=
    (CFSG.SeitzReduction.TwistedE6Pilot.su6Levi_facts hf hk hF hσ).1
  have hJA : E6GraphLevi.thetaRankOneGroup (algebraMap k F) ≤
      Subgroup.centralizer (A : Set (Γ₂ F)) := Subgroup.le_centralizer_iff.mp hA
  have hJL : E6GraphLevi.thetaRankOneGroup (algebraMap k F) ≤
      Subgroup.centralizer (L : Set (Γ₂ F)) :=
    Subgroup.le_centralizer_iff.mp (hL.trans hsu6C)
  have hmem : ∀ u ∈ E6GraphLevi.thetaRankOneGroup (algebraMap k F),
      u ∈ Subgroup.centralizer ((A ⊔ L : Subgroup (Γ₂ F)) : Set (Γ₂ F)) := by
    intro u hu
    have hzu : Subgroup.zpowers u ≤
        Subgroup.centralizer ((A ⊔ L : Subgroup (Γ₂ F)) : Set (Γ₂ F)) :=
      CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
        (Subgroup.zpowers_le.2 (hJA hu)) (Subgroup.zpowers_le.2 (hJL hu))
    exact hzu (Subgroup.mem_zpowers u)
  refine ⟨t, hJle htJ, s, hJle hsJ, ht2, hs2, hmem t htJ, hmem s hsJ, hts3, ?_⟩
  intro htsA
  exact htsnot (hAL htsA)

private theorem inner_action_data_su_twE6 {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    {d : Γ₂ F} (hF : Nat.card F = 2 ^ 2) {A L : Subgroup (Γ₂ F)}
    (hAel : IsElemAbelian 3 A)
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ)
    (hdA : d ∈ A)
    (hcomp : IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
      (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F))))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (ρ : ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2) →*
      ↥(stdLayerD (twistedE6RootGroup F σ) d))
    (hρ : Function.Surjective ρ)
    (hρk : ρ.ker ≤ Subgroup.center ↥(CFSG.Assembly.LargeEvenSUGroup (Fin n) F 2))
    (hdL : L = stdLayerD (twistedE6RootGroup F σ) d) :
    ∀ a ∈ A, ∃ y ∈ L, y ^ 3 = 1 ∧ y ∈ Subgroup.centralizer (A : Set (Γ₂ F)) ∧
      a * y⁻¹ ∈ Subgroup.centralizer (L : Set (Γ₂ F)) := by
  haveI : Finite (Γ₂ F) := finite_modGL
  haveI : Group.IsPerfect ↥(stdLayerD (twistedE6RootGroup F σ) d) :=
    Group.isPerfect_def.mpr hcomp.2.2.1
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hcop : Nat.Coprime n 3 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨hout, hcenter⟩ :=
    card_outer_dvd_two_and_center_eq_bot_of_su_two hF hn3 hcop ρ hρ hρk
  intro a ha
  obtain ⟨y, hyL, hy3, hyC, hyCK⟩ :=
    inner_of_card_outer_dvd_two hAel hAL hdA hout hcenter a ha
  exact ⟨y, hdL.symm ▸ hyL, hy3, hyC, hdL.symm ▸ hyCK⟩

private theorem concl_of_small_twE6
    {F k : Type} [Field F] [Finite F] [Field k] [Algebra k F]
    {n : ℕ} {σ : F ≃+* F}
    {M' : S172DModel S B (twistedE6RootGroup F σ) (twistedE6InndiagGL F σ)} {d' : Γ₂ F}
    (hcfg : Cfg173 3 S B N D K x)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    (hn : n = 1) (hkcard : Nat.card k = 2 ^ n)
    (hA'el : IsElemAbelian 3 M'.barB) (hbar4 : 3 ^ 4 ≤ Nat.card M'.barB)
    (hA'A5 : M'.barB ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ)
    (hd'bar : d' ∈ M'.barB) (hd'1 : d' ≠ 1)
    (hcomp' : IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d')
      (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d'} : Set (Γ₂ F))))
    (hd'K : M'.piImg K = stdLayerD (twistedE6RootGroup F σ) d')
    (hKLevi : stdLayerD (twistedE6RootGroup F σ) d' ≤
      CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom)
    (hbarC : M'.barB ≤ Subgroup.centralizer
      (E6GraphLevi.thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F))) :
    T173Concl 3 S B K N := by
  have hn1 : 1 ≤ n := by omega
  have hF2 : Nat.card F = 2 ^ 2 := by simpa [hn] using hF
  have hσ2 : ∀ c, σ c = c ^ 2 := by simpa [hn] using hσ
  have hk2 : Nat.card k = 2 := by simpa [hn] using hkcard
  obtain ⟨m, hm, ρ, hρ, hρk⟩ :=
    exists_su_of_le_levi_A5_two hk2 hF2 hσ2 hA'el hbar4 hA'A5 hd'bar hd'1 hKLevi hcomp'
  obtain ⟨hKZ3, h2⟩ := su_layer_data_twE6 hcfg M' hF2 hd'K hm ρ hρ hρk
  obtain ⟨t, htG, s, hsG, ht2, hs2, htC, hsC, hts3, htsnot⟩ :=
    exists_inner_pair_twE6 (A := M'.barB) (L := M'.piImg K) hn1 hkcard hF hσ h3 hbarC
      (by rw [hd'K]; exact hKLevi) hA'A5
  have hinner := inner_action_data_su_twE6 hF2 hA'el hA'A5 hd'bar hcomp' hm ρ hρ hρk hd'K
  exact S172DModel.concl_of_inner hcfg M' hKZ3 h2 hinner
    ⟨t, htG, s, hsG, ht2, hs2, htC, hsC, hts3, htsnot⟩

private theorem su6Levi_and_thetaRankOne_data
    {F k : Type} [Field F] [Finite F] [Field k] [Algebra k F]
    {n : ℕ} {σ : F ≃+* F} {J : Set (Fin TwistTag.E6.foldedTag.rank)} {A : Subgroup (Γ₂ F)}
    {d : Γ₂ F}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    (hn1 : 1 ≤ n) (hkcard : Nat.card k = 2 ^ n)
    (hAel : IsElemAbelian 3 A)
    (hA : A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ)
    (hJsub : J ⊆ twE6MaxA5)
    (hKL : stdLayerD (twistedE6RootGroup F σ) d ≤
      graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J)
    (hcomp : IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
      (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F)))) :
    (stdLayerD (twistedE6RootGroup F σ) d ≤
        CFSG.SeitzReduction.TwistedE6Pilot.su6Levi σ.toRingHom) ∧
      A ≤ Subgroup.centralizer
        (E6GraphLevi.thetaRankOneGroup (algebraMap k F) : Set (Γ₂ F)) := by
  have hA5le : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ≤
      parabolicLevi TwistTag.E6.tag F setA ⊓ graphFixedRootGroup TwistTag.E6 F σ.toRingHom := by
    rw [graphFixedParabolicLevi, twE6MaxA5_eq_foldedSetA, orbitUnion_foldedSetA]
  have hq' : CFSG.IsQuasisimple ↥(stdLayerD (twistedE6RootGroup F σ) d) :=
    ⟨⟨hcomp.2.2.1⟩, hcomp.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hcomp.2.2⟩
  exact ⟨le_su6Levi_of_isQuasisimple hn1 hkcard hF hσ
      (hKL.trans ((graphFixedParabolicLevi_mono hJsub).trans hA5le)) hq',
    le_centralizer_thetaRankOneGroup hn1 hkcard hF hσ h3 hAel.isPGroup hA⟩

theorem concl_of_famFive_twE6_of_subset
    (hT4 : ∀ {F : Type} [Field F] [Finite F] {n : ℕ}, Nat.card F = (2 ^ n) ^ 2 →
      ∀ (σ : F ≃+* F), (∀ c, σ c = c ^ 2 ^ n) → 3 ∣ 2 ^ n + 1 →
      ∀ {J : Set (Fin TwistTag.E6.foldedTag.rank)}, J ≠ Set.univ →
      ∀ {A : Subgroup (Γ₂ F)}, IsElemAbelian 3 A → 3 ^ 4 ≤ Nat.card A →
      A ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ →
      ∀ {d : Γ₂ F}, d ∈ A →
      stdLayerD (twistedE6RootGroup F σ) d ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J →
      IsComponentOf (stdLayerD (twistedE6RootGroup F σ) d)
        (twistedE6RootGroup F σ ⊓ Subgroup.centralizer ({d} : Set (Γ₂ F))) →
      A ⊓ Subgroup.centralizer (stdLayerD (twistedE6RootGroup F σ) d : Set (Γ₂ F)) =
        Subgroup.zpowers d →
      J ⊆ twE6MaxA5)
    {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 3 S B N D K x) {lab : GLALabel} (hlab : GLAInLambda2 lab)
    (htag : lab.tag = .twE6)
    (hmark : GLAMarking S (fun lab' _ _ I _ θ => lab' = lab ∧ GLASplit16 3 lab' ∧
      B ≤ Subgroup.normalizer (S : Set Ω) ∧
      ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : Ω) = b⁻¹ * l * b) φ)) :
    T173Concl 3 S B K N := by
  obtain ⟨F, hFld, hFinF, σ, hF, hσ, h3, ⟨M⟩⟩ := exists_dmodel_twE6 hcfg hlab htag hmark
  letI : Field F := hFld
  letI : Finite F := hFinF
  obtain ⟨J, M', d', hJ, hA'L, hbar4, hA'el, hd'bar, hd'1, hd'3, hd'K, hcomp', hcent', hK'L⟩ :=
    exists_conj_std_data_twE6 hcfg hF σ hσ h3 M
  have hJsub : J ⊆ twE6MaxA5 :=
    hT4 hF σ hσ h3 hJ hA'el hbar4 hA'L hd'bar hK'L hcomp' hcent'
  have hA'A5 : M'.barB ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 ⊔
      twistedE6DiagGL F σ :=
    hA'L.trans (sup_le_sup_right (graphFixedParabolicLevi_mono hJsub) _)
  obtain ⟨k, hkFld, hkAlg, hkcard⟩ := exists_subfield_twE6 hlab.1 hF
  letI : Field k := hkFld
  letI : Algebra k F := hkAlg
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hkcard]; positivity)
  obtain ⟨hKLevi, hbarC⟩ := su6Levi_and_thetaRankOne_data hF hσ h3 hlab.1 hkcard hA'el
    hA'A5 hJsub hK'L hcomp'
  rcases Nat.lt_or_ge lab.n 2 with hnlt | hnge
  · have hn_eq : lab.n = 1 := by have h := hlab.1; omega
    exact concl_of_small_twE6 hcfg hF hσ h3 hn_eq hkcard hA'el hbar4 hA'A5 hd'bar hd'1
      hcomp' hd'K hKLevi hbarC
  · exact (false_of_le_su6Levi hnge hkcard hF hσ
      (Subgroup.map_subtype_le (H := twistedE6InndiagGL F σ) M'.β.range hd'bar)
      hd'1 hd'3 (hbarC hd'bar) hKLevi).elim


end CFSG.LocalAnalysis.GLTheoremA.T173O

end
