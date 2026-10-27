module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcEndNode
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Mult
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.KRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2EUp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerExcTorus
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyOdd
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.SeitzReduction.EPilot CFSG.StandardType CFSG.StandardType.TableBExc
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem lieModel_adjointGroup_E7 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    CFSG.Blueprint.LieModel (adjointGroup .E7 F) .E7 0 2 n := by
  refine Or.inr (Or.inl ⟨rfl, by decide, ?_⟩)
  refine ⟨?_, CFSG.SignalizerFunctorTheorem.CatalogBridge.untwistedChevalleyModel_adjointGroup
    (τ := .E7) hF⟩
  exact ⟨Nat.prime_two, hn, rfl⟩

theorem hasLabel_adjointGroup_E7 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    HasLabel (adjointGroup .E7 F) (· = ⟨.E7, 0, n⟩) := by
  have hLie := lieModel_adjointGroup_E7 hF hn
  have hZ : Subgroup.center (adjointGroup .E7 F) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨lab, hlab, htag, hrank, _, hdeg, hraw⟩ :=
    CFSG.StandardType.exists_label_rawDatum_of_lieModel (S := adjointGroup .E7 F) hZ hLie
  have hlab' : lab = ⟨.E7, 0, n⟩ := by
    obtain ⟨t, r, k⟩ := lab
    have ht : t = .E7 := by
      cases t <;> simp only [CFSG.StandardType.markTag] at htag ⊢
      all_goals try rfl
      all_goals try split_ifs at htag
      all_goals simp_all
    subst ht
    have hr : r = 0 := hlab.2
    subst hr
    have hk : k = n := by simpa [CFSG.StandardType.markDeg] using hdeg
    subst hk
    rfl
  subst hlab'
  have hq : CFSG.IsQuasisimple (adjointGroup .E7 F) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 F
  refine hasLabel_of_quasisimple_rawDatum hq hlab ?_
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
  rintro R _ I F' ⟨e⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot |>.trans e⟩

theorem evenRank_adjointGroup_E7 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    evenRank (adjointGroup .E7 F) = 7 := by
  have hlab := hasLabel_adjointGroup_E7 hF (by omega)
  obtain ⟨p, hp, hp2, hpd⟩ := CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hn
  have hpq : p ∣ Nat.card F - 1 := by rw [hF]; exact hpd
  have hlow : 7 ≤ evenRank (adjointGroup .E7 F) :=
    le_evenRank_adjointGroup_of_torusPow (τ := .E7) hp hp2 (isRoot_single .E7 0)
      (card_torusPow_E7 hp hpq)
  have hup : evenRank (adjointGroup .E7 F) ≤ 7 :=
    (rk2_eUpAt_of_tables rk2KRank rk2Upper_holds hlab).e7 rfl hn
  omega

theorem hasLabel_perpLevi_E7 {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) :
    HasLabel ↥(perpLevi .E7 F) (· = ⟨.D, 6, n⟩) := by
  have hJ : CFSG.IsQuasisimple ↥(perpLevi .E7 F) :=
    CFSG.SeitzReduction.E7Pilot.isQuasisimple_perpLevi_E7
  have hM := CFSG.SeitzReduction.E7Pilot.lieModel_perpLevi_E7_quotient_center (K := F) hF
  have hSC : CFSG.Open.StatedClassicalModel
      (↥(perpLevi .E7 F) ⧸ Subgroup.center ↥(perpLevi .E7 F)) .POmegaPlus 6 2 n :=
    hM.statedClassicalModel (by decide)
  exact hasLabel_of_statedClassicalModel_POmegaPlus hJ hSC

private theorem endNodeElt_mem_torusPow {F : Type} [Field F] [Finite F] [CharP F 2]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {ζ : Fˣ} (hζ : orderOf ζ = q) :
    endNodeElt (τ := .E7) (Or.inr (Or.inl rfl)) ζ ∈ torusPow .E7 F q := by
  have hfull : ∀ a : Fin Tag.E7.rank → Fˣ, rootDiagUnit .E7 a ∈ torusGroup .E7 F :=
    full_of_E7_E8 (Or.inl rfl)
  exact (endNodeAt_torusPow (τ := .E7) (Or.inr (Or.inl rfl)) (ringChar.eq F 2) hfull
    hq hq2 hζ (CFSG.SeitzReduction.E7Pilot.isQuasisimple_perpLevi_E7)).1

private theorem perpLevi_le_centralizer_endNodeElt {F : Type} [Field F] [Finite F]
    {ζ : Fˣ} :
    perpLevi .E7 F ≤ Subgroup.centralizer
      ({endNodeElt (τ := .E7) (Or.inr (Or.inl rfl)) ζ} : Set (adjointGroup .E7 F)) := by
  intro g hg
  rw [mem_centralizer_endNodeElt_iff, toralCentralizer]
  exact Subgroup.mem_inf.mpr
    ⟨rootSpan_le_adjointGroup' _ (Subgroup.mem_subgroupOf.mp hg),
      rootSpan_le_centralizer _ (perpRoots_subset_rootCharKernel ζ)
        (Subgroup.mem_subgroupOf.mp hg)⟩

private theorem commutator_mem_perpLevi {F : Type} [Field F] [Finite F] [CharP F 2]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {ζ : Fˣ} (hζ : orderOf ζ = q)
    {g h : adjointGroup .E7 F}
    (hg : g ∈ Subgroup.centralizer
      ({endNodeElt (τ := .E7) (Or.inr (Or.inl rfl)) ζ} : Set (adjointGroup .E7 F)))
    (hh : h ∈ Subgroup.centralizer
      ({endNodeElt (τ := .E7) (Or.inr (Or.inl rfl)) ζ} : Set (adjointGroup .E7 F))) :
    g * h * g⁻¹ * h⁻¹ ∈ perpLevi .E7 F := by
  have hζ3 : 3 ≤ orderOf ζ := by
    rw [hζ]
    exact lt_of_le_of_ne hq.two_le (Ne.symm hq2)
  obtain ⟨hTD, -, hcomm⟩ :=
    toralCentralizer_highDiag_eq_sup (τ := .E7) (Or.inr (Or.inl rfl)) (ringChar.eq F 2) hζ3
  have hg' : (g : ModGL .E7 F) ∈ toralCentralizer .E7 F (highDiag .E7 ζ) :=
    (mem_centralizer_endNodeElt_iff (Or.inr (Or.inl rfl))).1 hg
  have hh' : (h : ModGL .E7 F) ∈ toralCentralizer .E7 F (highDiag .E7 ζ) :=
    (mem_centralizer_endNodeElt_iff (Or.inr (Or.inl rfl))).1 hh
  rw [hTD] at hg' hh'
  have h1 : (g : ModGL .E7 F) * (h : ModGL .E7 F) * (g : ModGL .E7 F)⁻¹ *
      (h : ModGL .E7 F)⁻¹ ∈ rootSpan .E7 F (perpRoots .E7) :=
    commutator_mem_of_mem_sup
      (fun t ht t' ht' => mul_comm_of_mem_highTorusLine (Or.inr (Or.inl rfl)) ht ht')
      (fun t ht d hd => (hcomm t ht d hd).eq) hg' hh'
  exact Subgroup.mem_subgroupOf.mpr h1

private theorem omegaPlusSix_mult {J : Type} [Group J] [Finite J] {n p q : ℕ}
    (hn : 2 ≤ n) (hq : q.Prime) (hq2 : q ≠ 2) (hqD : q ∣ 2 ^ n - 1)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpD : p ∣ 2 ^ n + 1)
    (hJ : HasLabel J (· = ⟨.D, 6, n⟩)) :
    (Subgroup.center J = ⊥ ∧ TrivialMultiplierT J) ∧ Odd (Nat.card (Subgroup.center J)) ∧
      (9 ≤ twoRank J) ∧
      (p * q ∣ Nat.card (J ⧸ Subgroup.center J)) := by
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  obtain ⟨⟨hZ, hTM⟩, hodd, hm2, hdvd⟩ :=
    omegaPlus_mult (m := 6) (n := n) (by norm_num) hn hJ hGA
  refine ⟨⟨hZ, hTM⟩, hodd, ?_, ?_⟩
  · have hm2' : 15 * n ≤ twoRank J := by
      simpa [show 6 * (6 - 1) / 2 = 15 by norm_num, Nat.mul_comm] using hm2
    omega
  · have hfac : 2 ^ (2 * n) - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      rw [show 2 * n = n + n by omega, pow_add, ← pow_two (2 ^ n)]
      simpa using Nat.sq_sub_sq (2 ^ n) 1
    have hpD' : p ∣ 2 ^ (2 * n) - 1 := by
      rw [hfac]
      exact dvd_trans hpD (dvd_mul_right _ _)
    have hqD' : q ∣ 2 ^ (2 * n) - 1 := by
      rw [hfac]
      exact dvd_trans hqD (dvd_mul_left _ _)
    have hpq : p ≠ q := by
      intro hpq
      subst hpq
      have hdvd2 : p ∣ 2 := by
        have hle : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
        have hsub : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpD hqD
        rwa [show (2 ^ n + 1) - (2 ^ n - 1) = 2 by omega] at hsub
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd2)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
      ((Nat.coprime_primes hp hq).2 hpq)
      (hdvd p hp hp2 hpD') (hdvd q hq hq2 hqD')

private theorem e7_JShape {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {lab : GLALabel}
    (hlab : HasLabel (adjointGroup .E7 F) (fun l : GLALabel => l = lab)) :
    JShape lab (3 ∣ Nat.card (Subgroup.center (adjointGroup .E7 F))) ⟨.D, 6, n⟩ := by
  have hlabE7 : HasLabel (adjointGroup .E7 F) (fun l : GLALabel => l = ⟨.E7, 0, n⟩) :=
    hasLabel_adjointGroup_E7 hF (by omega)
  have hcenter : Subgroup.center (adjointGroup .E7 F) = ⊥ := center_adjointGroup_eq_bot
  have hz : ¬ 3 ∣ Nat.card (Subgroup.center (adjointGroup .E7 F)) := by
    rw [hcenter]
    simp
  have he : 4 ≤ evenRank (adjointGroup .E7 F) := by
    rw [evenRank_adjointGroup_E7 hF hn]
    norm_num
  rcases label_eq_or_BC he hlab hlabE7 with hEq | ⟨ht, ht', -, -⟩
  · subst hEq
    refine ⟨rfl, ?_⟩
    simp [JShape]
  · exact absurd ht' (by simp)

theorem concl166S_E7_model_of_layerData {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ 2 ^ n + 1)
    (hD6 : LayerData166At ⟨.D, 6, n⟩) :
    ∃ (q' : ℕ) (B' : Subgroup (adjointGroup .E7 F)) (x' : adjointGroup .E7 F)
      (J : Subgroup (adjointGroup .E7 F)), Concl166S (adjointGroup .E7 F) p q' B' x' J := by
  obtain ⟨q, hq, hq2, hqD⟩ := CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hn
  haveI : Fact q.Prime := ⟨hq⟩
  have hqF : q ∣ Nat.card F - 1 := by rwa [hF]
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := F) hqF
  let R := adjointGroup .E7 F
  let J : Subgroup R := perpLevi .E7 F
  let x : R := endNodeElt (τ := .E7) (Or.inr (Or.inl rfl)) ζ
  have hfull : ∀ a : Fin Tag.E7.rank → Fˣ, rootDiagUnit .E7 a ∈ torusGroup .E7 F :=
    full_of_E7_E8 (Or.inl rfl)
  have hxmem : x ∈ torusPow .E7 F q := endNodeElt_mem_torusPow hq hq2 hζ
  have hxq : x ^ q = 1 := (mem_torusPow.mp hxmem).2
  have hx1 : x ≠ 1 := by
    exact (endNodeAt_torusPow (τ := .E7) (Or.inr (Or.inl rfl)) (ringChar.eq F 2) hfull
      hq hq2 hζ (CFSG.SeitzReduction.E7Pilot.isQuasisimple_perpLevi_E7)).2.1
  have hJx : J ≤ Subgroup.centralizer ({x} : Set R) := perpLevi_le_centralizer_endNodeElt
  have hJq : CFSG.IsQuasisimple ↥J := CFSG.SeitzReduction.E7Pilot.isQuasisimple_perpLevi_E7
  have hJlab : HasLabel ↥J (· = ⟨.D, 6, n⟩) := hasLabel_perpLevi_E7 hF (by omega)
  have hmul := omegaPlusSix_mult (J := ↥J) hn hq hq2 hqD hp hp2 hpF hJlab
  have he : 4 ≤ evenRank R := by
    rw [evenRank_adjointGroup_E7 hF hn]
    norm_num
  have hshape : ∀ lab : GLALabel, HasLabel R (fun l : GLALabel => l = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center R)) ⟨.D, 6, n⟩ :=
    fun lab hlab => e7_JShape hn hF hlab
  have hm2 : evenRank R + 2 ≤ twoRank ↥J := by
    change evenRank (adjointGroup .E7 F) + 2 ≤ twoRank ↥J
    rw [evenRank_adjointGroup_E7 hF hn]
    norm_num
    exact hmul.2.2.1
  have hcomm : ∀ g ∈ Subgroup.centralizer ({x} : Set R),
      ∀ h ∈ Subgroup.centralizer ({x} : Set R), g * h * g⁻¹ * h⁻¹ ∈ J :=
    fun g hg h hh => commutator_mem_perpLevi hq hq2 hζ hg hh
  have hqn : q ∣ 2 ^ (⟨.D, 6, n⟩ : GLALabel).n - 1 := by simpa using hqD
  have hrank : (⟨.D, 6, n⟩ : GLALabel).rank = evenRank R - 1 := by
    rw [evenRank_adjointGroup_E7 hF hn]
  obtain ⟨B', hConcl⟩ := exists_concl166S_of_layerData166At (K := R) hq hq2 hxq hx1
    (center_adjointGroup_eq_bot (τ := .E7) (K := F)) he hJx hJq hcomm ⟨.D, 6, n⟩ hJlab
    hshape hm2 hmul.2.2.2 hmul.1.1 hmul.1.2 hD6 hqn hrank
  exact ⟨q, B', x, J, hConcl⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F
