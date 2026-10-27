module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormW
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvU42Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21HU42
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import Certificates.Certificate2012
public import Certificates.Certificate26121
public import Certificates.Certificate26122
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SpTwo
import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutU42Aut
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW

open CFSG.Open CFSG.AGLEmbedding Subgroup

namespace U42

open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.EvenSporadicStandard.M22Std CFSG.EvenSporadicStandard.M22Std.P21H

theorem lieModel_of_twistedA {Y : Type} [Group Y] (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : CFSG.Blueprint.LieModel Y .PSU 4 2 1 := by
  obtain ⟨q, hq, hdq⟩ := hd
  obtain ⟨i, hv⟩ := d
  simp only at hdq
  subst hdq
  have h2 : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  obtain ⟨hp, hf⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 h2
  have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
  rw [hp, hf] at hM
  exact Or.inl ⟨by decide, hM⟩

theorem not_orderOf_fifteen_u42
    {E : Type} [Group E] (h : CFSG.Blueprint.LieModel E .PSU 4 2 1) (y : E) :
    orderOf y ≠ 15 := by
  obtain ⟨e⟩ := equiv_of_lieModel (lieModel_PSp_two_three_of_lieModel_PSU_four_two h)
  intro hy
  refine noElemOrder_of_check QP45_ok (by norm_num : 0 < 15) Certificates.certificate26122
    (e y).2 ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact hy

theorem exists_conj_of_odd_u42 {E : Type} [Group E]
    (h : CFSG.Blueprint.LieModel E .PSU 4 2 1) {α : MulAut E} (hα : Odd (orderOf α)) :
    ∃ g : E, MulAut.conj g = α ∧ Odd (orderOf g) := by
  obtain ⟨hAut, hcard⟩ := card_mulAut_of_lieModel_psu42 h
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  haveI : IsSimpleGroup E :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  obtain ⟨a, b, hab⟩ := not_commutative_of_lieModel_psu42 h
  have hZ : Subgroup.center E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center E) with h0 | h1
    · exact h0
    · exact absurd (Subgroup.mem_center_iff.1 (h1 ▸ Subgroup.mem_top b) a) hab
  have hinj : Function.Injective (MulAut.conj : E →* MulAut E) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hzc : z ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun σ : MulAut E => σ x) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * z = (z * x * z⁻¹) * z := by rw [h1]
        _ = z * x := by group
    rwa [hZ, Subgroup.mem_bot] at hzc
  set Inn : Subgroup (MulAut E) := (MulAut.conj : E →* MulAut E).range with hInn
  have hInnCard : Nat.card Inn = 25920 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : Inn.index = 2 := by
    have h1 := Subgroup.index_mul_card Inn
    rw [hInnCard, hAut] at h1
    omega
  have hαmem : α ∈ Inn := by
    obtain ⟨m, hm⟩ := hα
    have h1 : α = (α ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, ← hm,
        pow_orderOf_eq_one, one_mul]
    rw [h1]
    exact Inn.pow_mem (Subgroup.sq_mem_of_index_two hidx α) _
  obtain ⟨g, hg⟩ := hαmem
  refine ⟨g, hg, ?_⟩
  rw [← orderOf_injective (MulAut.conj : E →* MulAut E) hinj g, hg]
  exact hα

theorem eq_one_of_commute_two_five_u42
    {E : Type} [Group E]
    (h : CFSG.Blueprint.LieModel E .PSU 4 2 1) {g s u : E} (hg : Odd (orderOf g))
    (hs : orderOf s = 2) (hu : orderOf u = 5) (hgs : g * s = s * g) (hgu : g * u = u * g) :
    g = 1 := by
  by_contra hg1
  obtain ⟨-, hcard⟩ := card_mulAut_of_lieModel_psu42 h
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hk1 : orderOf g ≠ 1 := fun h1 => hg1 (orderOf_eq_one_iff.1 h1)
  have hr : (orderOf g).minFac.Prime := Nat.minFac_prime hk1
  have hrk : (orderOf g).minFac ∣ orderOf g := Nat.minFac_dvd _
  set r := (orderOf g).minFac with hr_def
  have hr2 : r ≠ 2 := by
    intro h2
    rw [h2] at hrk
    exact (Nat.not_even_iff_odd.2 hg) (even_iff_two_dvd.2 hrk)
  set z := g ^ (orderOf g / r) with hz_def
  have hz : orderOf z = r := orderOf_pow_orderOf_div (orderOf_pos g).ne' hrk
  have hzs : z * s = s * z := ((show Commute g s from hgs).pow_left (orderOf g / r)).eq
  have hzu : z * u = u * z := ((show Commute g u from hgu).pow_left (orderOf g / r)).eq
  have hrcard : r ∣ 2 ^ 6 * 3 ^ 4 * 5 := by
    have h1 : r ∣ Nat.card E := hrk.trans (orderOf_dvd_natCard g)
    rwa [hcard, show (25920 : ℕ) = 2 ^ 6 * 3 ^ 4 * 5 by norm_num] at h1
  rcases (Nat.Prime.dvd_mul hr).1 hrcard with h23 | h5
  · rcases (Nat.Prime.dvd_mul hr).1 h23 with h2 | h3
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2))
    ·
      have h3' : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
        (hr.dvd_of_dvd_pow h3)
      have hcop : Nat.Coprime (orderOf z) (orderOf u) := by rw [hz, hu, h3']; norm_num
      have h15 : orderOf (z * u) = 15 := by
        rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (show Commute z u from hzu) hcop, hz,
          hu, h3']
      exact not_orderOf_fifteen_u42 h (z * u) h15
  ·
    have h5' : r = 5 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h5
    have hs2 : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hs, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hs
      omega
    exact no_commuting_five_u42 h s z hs2 hs1 (hz.trans h5') hzs.symm

end U42

theorem centralizes_u42 {A : Type} [Group A] [Finite A]
    {Y P : Subgroup A}
    (hPY : P ≤ Y) (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q)
    (eY : ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group) (eP : ↥P ≃* Equiv.Perm (Fin 6))
    {b : A} (hbo : Odd (orderOf b)) (hbY : b ∈ normalizer (Y : Set A))
    (hbP : b ∈ normalizer (P : Set A))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Y, b * y = y * b := by
  classical
  have hL := U42.lieModel_of_twistedA d hd eY
  let α : MulAut ↥Y := Y.normalizerMonoidHom ⟨b, hbY⟩
  have hαcoe : ∀ y : ↥Y, (α y : A) = b * (y : A) * b⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨b, hbY⟩ y
  have hαodd : Odd (orderOf α) := by
    refine hbo.of_dvd_nat ?_
    have h := orderOf_map_dvd Y.normalizerMonoidHom (⟨b, hbY⟩ : ↥(normalizer (Y : Set A)))
    rwa [Subgroup.orderOf_mk] at h
  obtain ⟨g, hg, hgodd⟩ := U42.exists_conj_of_odd_u42 hL hαodd
  have hconj : ∀ w ∈ Y, b * w * b⁻¹ = (g : A) * w * (g : A)⁻¹ := by
    intro w hw
    have h1 : α ⟨w, hw⟩ = MulAut.conj g ⟨w, hw⟩ := by rw [hg]
    have h2 : ((α ⟨w, hw⟩ : ↥Y) : A) = b * w * b⁻¹ := hαcoe ⟨w, hw⟩
    rw [← h2, h1, MulAut.conj_apply]
    rfl
  have hPbot : CFSG.pCore 2 ↥P = ⊥ := by
    have h := CFSG.pCore_map_iso 2 eP
    rw [pCore_perm_six_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ eP.injective).1 h
  have hO : pCoreOf 2 P = ⊥ := by rw [pCoreOf, hPbot, Subgroup.map_bot]
  let φ : ↥P ⧸ CFSG.pCore 2 ↥P ≃* Equiv.Perm (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hPbot).trans QuotientGroup.quotientBot).trans eP
  have hA6 : alternatingGroup (Fin 6) ≤ wSup (Equiv.Perm (Fin 6)) :=
    le_wSup_of_normal_of_isQuasisimple inferInstance
      CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.isQuasisimple_alternatingGroup_six
  have hcomm : ∀ x ∈ alternatingGroup (Fin 6),
      (g : A) * ((eP.symm x : ↥P) : A) = ((eP.symm x : ↥P) : A) * (g : A) := by
    intro x hx
    set w : ↥P := eP.symm x with hw
    have hmkx : QuotientGroup.mk' (CFSG.pCore 2 ↥P) w = φ.symm x := by
      apply φ.injective
      rw [MulEquiv.apply_symm_apply]
      show eP w = x
      rw [hw, MulEquiv.apply_symm_apply]
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥P) w ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
      rw [hmkx, ← map_wSup_eq φ.symm]
      exact ⟨x, hA6 hx, rfl⟩
    have h1 := hW (w : A) w.2 hmem
    rw [hO, Subgroup.mem_bot, hconj (w : A) (hPY w.2)] at h1
    have h2 : (g : A) * w * (g : A)⁻¹ = w := mul_inv_eq_one.1 h1
    calc (g : A) * w = ((g : A) * w * (g : A)⁻¹) * (g : A) := by group
      _ = w * g := by rw [h2]
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have h : 2 * Nat.card (alternatingGroup (Fin 6)) = 720 := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    omega
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨s₀, hs₀⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 6)) 2
    (by rw [hA6card]; norm_num)
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 6)) 5
    (by rw [hA6card]; norm_num)
  let ι : Equiv.Perm (Fin 6) →* ↥Y := (Subgroup.inclusion hPY).comp eP.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hPY).comp eP.symm.injective
  have hg1 : g = 1 := by
    refine U42.eq_one_of_commute_two_five_u42 hL hgodd (s := ι (s₀ : Equiv.Perm (Fin 6)))
      (u := ι (u₀ : Equiv.Perm (Fin 6))) ?_ ?_ ?_ ?_
    · rw [orderOf_injective ι hι, Subgroup.orderOf_coe, hs₀]
    · rw [orderOf_injective ι hι, Subgroup.orderOf_coe, hu₀]
    · exact Subtype.ext (hcomm _ s₀.2)
    · exact Subtype.ext (hcomm _ u₀.2)
  intro y hy
  have h1 := hconj y hy
  rw [hg1] at h1
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
  calc b * y = b * y * b⁻¹ * b := by group
    _ = y * b := by rw [h1]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW
