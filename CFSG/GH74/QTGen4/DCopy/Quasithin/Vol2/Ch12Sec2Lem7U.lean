module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7Nat1238NQBase
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Lem7Stmts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.H13.NQBlockRadicalR2
public import CFSG.Quasithin.H13.NQBlockResidualUniqueM
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7NQ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Lem7NQ

theorem lem1227NotQuasisimple_of_unique_F4
    (h331 : Stmt3_3_1_F4) (h3214 : Stmt3_2_14_F4) : Lem1227NotQuasisimple_F4 := by
  intro G _ _ T L V H X Y hH hCZ hHs hns hXc hHX hXq hXY hYmax hYf
  by_contra hYq
  have hs := hH.simple
  have hnab := hH.nonabelian
  have hQ := hH.qtke
  have hT := hH.sylow
  set M := Subgroup.normalizer (L : Set G) with hMdef

  have hTY : T ≤ Subgroup.normalizer (Y : Set G) :=
    NQBlock.le_normalizer_of_not_isQuasisimple hs hnab hQ hYmax.1 hYq

  have hO2 : pCoreOf 2 Y ≠ ⊥ := NQCore.pCoreOf_ne_bot_of_quasithinV2_ne_bot hYf.2.2.2
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥Y := (NQCore.qt_positive_two_core_SQTK hnab hQ hO2).2
  have hYc : Y ∈ cComp (Y ⊔ T) := cComp_of_isLocal hYmax.1
  have hYself : Y ∈ cComp Y := cComp_mem_of_le hYc le_rfl le_sup_left
  have hYtop : CFSG.IsCComponent (⊤ : Subgroup ↥Y) := by
    have h3 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hYself)
    rwa [Subgroup.subgroupOf_self] at h3
  obtain ⟨p, hp, hp5, D₀, -, hD₀, hshape, -⟩ :=
    NQBlock.nq_characteristic_radical_odd_residual_witness hsqtk.1 hYtop hYq
  have : Fact p.Prime := ⟨hp⟩
  have hCp : CFSG.pCore p (↥Y ⧸ CFSG.pCore 2 ↥Y) ≠ ⊥ := by
    intro hbot
    have hD₀b : D₀ = ⊥ := le_bot_iff.mp (hbot ▸ hD₀)
    have hcard : Nat.card D₀ = 1 := by rw [hD₀b, Subgroup.card_bot]
    rcases hshape with ⟨-, h2⟩ | ⟨-, h3, -⟩
    · rw [hcard] at h2
      have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
      omega
    · rw [hcard] at h3
      have : 1 < p ^ 3 := Nat.one_lt_pow three_ne_zero hp.one_lt
      omega

  set Q : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := CFSG.pCore p (↥Y ⧸ CFSG.pCore 2 ↥Y) with hQdef
  set B : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := Subgroup.closure {a | a ∈ Q ∧ a ^ p = 1} with hBdef
  set E : Subgroup ↥Y := B.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) with hEdef
  set X' : Subgroup ↥Y := Subgroup.closure {e | e ∈ E ∧ Odd (orderOf e)} with hX'def
  obtain ⟨-, hX'c, -, hX'solv, -⟩ := NQBlock.canonical_prime_witness hsqtk.1 hYtop hYq
    (NQCore.mem_primeFactors_fitting hCp) Q B E X' rfl rfl rfl rfl
  have hX₀ : nqPrimeResidualX Y p = X'.map Y.subtype := rfl
  have : X'.Normal := inferInstance

  have hU := NQCore.isUniqueM_canonical_residual hs hnab hQ hT hYmax hYf hTY hYq hp hp5 hCp

  have hX'rad : X' ≤ CFSG.solvableRadical ↥Y := le_sSup ⟨inferInstance, hX'solv⟩
  have hRad := A7.solvableRadical_le_centralizer_conjClosure_F4 h3214 hs hnab hQ hT hYmax.1 hYq
  have hX₀M : nqPrimeResidualX Y p ≤ M := by
    rw [hX₀]
    refine (Subgroup.map_mono hX'rad).trans (hRad.trans ((Subgroup.centralizer_le ?_).trans hCZ))
    exact le_conjClosure _ _

  have hMmax : quasithinIsMaxTwoLocal M := by
    obtain ⟨⟨hmax2, -, -⟩, -⟩ := (h331 G T hs hnab hQ hT).2 L hH.maximal hH.quasisimple
    rwa [hH.conjClosure_eq] at hmax2
  have hMeq : M = Subgroup.normalizer ((nqPrimeResidualX Y p : Subgroup G) : Set G) :=
    hU.2 M ⟨hMmax, sup_le hX₀M hH.normalizes⟩

  have hYM : Y ≤ M := by
    rw [hMeq, hX₀]
    exact le_normalizer_map X'
  apply hHs.2.1
  rw [hHX]
  exact sup_le (hXY.trans hYM) hH.normalizes

end CFSG.Quasithin.H13
