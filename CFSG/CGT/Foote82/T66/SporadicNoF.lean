module

public import CFSG.CGT.Foote82.T66.CitedMC2
import CFSG.CGT.Foote82.T66.MC2Arith
import CFSG.CGT.Foote82.T66.MC2Spor
import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8He
import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Suz
import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ2
import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRu
import CFSG.Sporadic.Co1Block.Thirteen
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public import CFSG.Sporadic.Schreier.RuIso

public section

namespace CFSG.CGT.Foote82

namespace SporNoF

open CFSG.RankThree.PartTwo CFSG.Blueprint.NativeSporadic

private theorem nine_dvd_factorial_div_two {n : ℕ} (hn : 6 ≤ n) : 9 ∣ n.factorial / 2 := by
  obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hn
  rw [hk, show Nat.factorial 6 = 720 by decide, show 720 * k / 2 = 360 * k by omega]
  exact Dvd.dvd.mul_right (by norm_num) k

private theorem eq_eight_of_factorial_div_two {n : ℕ} (h : n.factorial / 2 = 20160) : n = 8 := by
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp_all [Nat.factorial]
  · have h1 := Nat.factorial_le hn
    have h9 : Nat.factorial 9 = 362880 := by decide
    omega

private theorem factorial_div_two_ne_G24 (n : ℕ) : n.factorial / 2 ≠ 251596800 := by
  rcases Nat.lt_or_ge n 13 with h | h
  · have h1 := Nat.factorial_le (show n ≤ 12 by omega)
    have h12 : Nat.factorial 12 = 479001600 := by decide
    omega
  · have h1 := Nat.factorial_le h
    have h13 : Nat.factorial 13 = 6227020800 := by decide
    omega

private theorem nontrivial_of_card_ne_one {T : Type*} [Group T] (h : Nat.card T ≠ 1) :
    Nontrivial T := by
  by_contra hT
  have := not_nontrivial_iff_subsingleton.1 hT
  exact h Nat.card_unique

private theorem nonempty_quot_equiv {Q T : Type} [Group Q] [Group T] [Nontrivial T]
    (hQ : CFSG.IsQuasisimple Q) (hT : Subgroup.center T = ⊥) (α : Q →* T)
    (hα : Function.Surjective α) : Nonempty (Q ⧸ Subgroup.center Q ≃* T) := by
  obtain ⟨β, hβ⟩ := MC2.exists_surjective_lift (QuotientGroup.mk' (Subgroup.center Q))
    (QuotientGroup.mk'_surjective _) (le_of_eq (QuotientGroup.ker_mk' _)) α hα hT
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  have hinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal β.ker with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : T)
      obtain ⟨q, rfl⟩ := hβ x
      exact hx (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top q))
  exact ⟨MulEquiv.ofBijective β ⟨hinj, hβ⟩⟩

private theorem master {Q : Type} [Group Q] (hQ : CFSG.IsQuasisimple Q) (h : MC2.FSurj Q) :
    9 ∣ Nat.card (Q ⧸ Subgroup.center Q) ∧ Nat.card (Q ⧸ Subgroup.center Q) ≠ 251596800 ∧
      (Nat.card (Q ⧸ Subgroup.center Q) = 20160 →
        Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 8))) := by
  rcases h with ⟨n, hn, α, hα⟩ | ⟨α, hα⟩ | ⟨α, hα⟩
  · have h4 : 4 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    haveI : Nontrivial (alternatingGroup (Fin n)) :=
      alternatingGroup.nontrivial_of_three_le_card (by omega)
    obtain ⟨e⟩ := nonempty_quot_equiv hQ (alternatingGroup.center_eq_bot h4) α hα
    have hc : Nat.card (Q ⧸ Subgroup.center Q) = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    refine ⟨?_, ?_, fun h20160 => ?_⟩
    · rw [hc]
      exact nine_dvd_factorial_div_two hn
    · rw [hc]
      exact factorial_div_two_ne_G24 n
    · rw [hc] at h20160
      obtain rfl := eq_eight_of_factorial_div_two h20160
      exact ⟨e⟩
  · haveI : Nontrivial ↥(omegaMinusTwo 2) :=
      nontrivial_of_card_ne_one (by rw [MC2.card_omegaMinusTwo_two]; norm_num)
    obtain ⟨e⟩ := nonempty_quot_equiv hQ (MC2.center_omegaMinusTwo le_rfl) α hα
    have hc : Nat.card (Q ⧸ Subgroup.center Q) = 25920 := by
      rw [Nat.card_congr e.toEquiv, MC2.card_omegaMinusTwo_two]
    refine ⟨?_, ?_, fun h20160 => ?_⟩
    · rw [hc]
      norm_num
    · rw [hc]
      norm_num
    · rw [hc] at h20160
      exact absurd h20160 (by norm_num)
  · haveI : Nontrivial ↥(omegaMinusTwo 3) :=
      nontrivial_of_card_ne_one (by rw [MC2.card_omegaMinusTwo_three]; norm_num)
    obtain ⟨e⟩ := nonempty_quot_equiv hQ (MC2.center_omegaMinusTwo (by norm_num)) α hα
    have hc : Nat.card (Q ⧸ Subgroup.center Q) = 197406720 := by
      rw [Nat.card_congr e.toEquiv, MC2.card_omegaMinusTwo_three]
    refine ⟨?_, ?_, fun h20160 => ?_⟩
    · rw [hc]
      norm_num
    · rw [hc]
      norm_num
    · rw [hc] at h20160
      exact absurd h20160 (by norm_num)

private theorem j2_false
    {X : Type} [Group X] (hX : IsSporadic X .J2) {t : X} (ht : orderOf t = 2)
    {B : Subgroup ↥(Subgroup.centralizer ({t} : Set X))}
    (h9 : 9 ∣ Nat.card (↥B ⧸ Subgroup.center ↥B)) : False := by
  have h1 : Nat.card (↥B ⧸ Subgroup.center ↥B) ∣ 1920 :=
    ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card B)).trans
      (CFSG.ComponentClassification.FooteLit.KG.card_centralizer_dvd_of_J2 hX t ht)
  have h2 := h9.trans h1
  omega

private theorem suz_false
    {X : Type} [Group X] (hX : IsSporadic X .Suz) {t : X} (ht : orderOf t = 2)
    {B : Subgroup ↥(Subgroup.centralizer ({t} : Set X))} (hB : CFSG.IsComponent B)
    (h8 : Nat.card (↥B ⧸ Subgroup.center ↥B) = 20160 →
      Nonempty (↥B ⧸ Subgroup.center ↥B ≃* alternatingGroup (Fin 8))) : False := by
  obtain ⟨e⟩ := hX
  exact CFSG.ComponentClassification.CatFC.ResidualA8.noAltEightComponent_suz_centralizer e t ht
    B hB (h8 (CFSG.Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order
      e t ht B hB))

private theorem he_false
    {X : Type} [Group X] (hX : IsSporadic X .He) {t : X} (ht : orderOf t = 2) {Y : Subgroup X}
    (hY : CFSG.Assembly.IsComponentOf Y (Subgroup.centralizer ({t} : Set X)))
    {B : Subgroup ↥(Subgroup.centralizer ({t} : Set X))} (hB : CFSG.IsComponent B)
    (eBY : ↥B ≃* ↥Y)
    (h8 : Nat.card (↥B ⧸ Subgroup.center ↥B) = 20160 →
      Nonempty (↥B ⧸ Subgroup.center ↥B ≃* alternatingGroup (Fin 8))) : False := by
  have hcard : Nat.card (↥B ⧸ Subgroup.center ↥B) = 20160 := by
    rw [CFSG.Sporadic.SuzOddCore.card_quotient_center_equiv eBY]
    exact CFSG.Sporadic.SmallOddCore.cti_he_involution_local_components_simple_quotient_order
      hX ht hY
  obtain ⟨e⟩ := hX
  have hno : CFSG.ComponentClassification.CatFC.ResidualA8.NoAltEightComponent
      ↥(Subgroup.centralizer ({t} : Set X)) :=
    CFSG.ComponentClassification.CatFC.ResidualA8.NoAltEightComponent.of_mulEquiv
      (MulEquiv.subgroupCongr
        (CFSG.SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf t).symm)
      (CFSG.ComponentClassification.CatFC.ResidualA8.noAltEightComponent_he_fixed e ht)
  exact hno B hB (h8 hcard)

private theorem ru_false
    {X : Type} [Group X] (hX : IsSporadic X .Ru) {t : X} (ht : orderOf t = 2)
    {B : Subgroup ↥(Subgroup.centralizer ({t} : Set X))} (hB : CFSG.IsComponent B)
    (h9 : 9 ∣ Nat.card (↥B ⧸ Subgroup.center ↥B)) : False := by
  obtain ⟨e⟩ := hX
  have h3 : 3 ∣ Nat.card ↥B :=
    ((by norm_num : 3 ∣ 9).trans h9).trans (Subgroup.card_quotient_dvd_card _)
  exact CFSG.ComponentClassification.RestrictedStd.Spor.compsSatisfy_centralizer_of_mulEquiv _
    CFSG.ComponentClassification.RestrictedStd.Spor.isoInvariant_not_three_dvd
    CFSG.ComponentClassification.RestrictedStd.Spor.ru_centralizerIn_comps
    (e.trans CFSG.Sporadic.RuSchreier.ruEquivP) t ht B hB h3

private theorem co1_false
    {X : Type} [Group X] (hX : IsSporadic X .Co1) {t : X} (ht : orderOf t = 2)
    {B : Subgroup ↥(Subgroup.centralizer ({t} : Set X))} (hB : CFSG.IsComponent B)
    (h13 : Nat.card (↥B ⧸ Subgroup.center ↥B) ≠ 251596800) : False := by
  open CFSG.Sporadic.Co1Block in
  exact h13 (cti_co1_involution_local_components_simple_quotient_divisible_by_thirteen
    hX ht B hB).1

end SporNoF

theorem sporadicNoFComponent_holds
    : SporadicNoFComponent := by
  intro X _ _ hX t ht Y hY
  have hYC : Y ≤ Subgroup.centralizer ({t} : Set X) := hY.1
  have hYa : CFSG.Assembly.IsComponentOf Y (Subgroup.centralizer ({t} : Set X)) :=
    CFSG.Assembly.isComponentOf_iff_open.2 hY
  have hB : CFSG.IsComponent (Y.subgroupOf (Subgroup.centralizer ({t} : Set X))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hYC).1 hYa
  have key : ¬ MC2.FSurj ↥Y := by
    intro hS
    obtain ⟨h9, h13, h8⟩ := SporNoF.master hB.1
      (MC2.fSurj_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYC) hS)
    rcases hX with hJ2 | hSuz | hHe | hRu | hCo1
    · exact SporNoF.j2_false hJ2 ht h9
    · exact SporNoF.suz_false hSuz ht hB h8
    · exact SporNoF.he_false hHe ht hYa hB (Subgroup.subgroupOfEquivOfLe hYC) h8
    · exact SporNoF.ru_false hRu ht hB h9
    · exact SporNoF.co1_false hCo1 ht hB h13
  exact ⟨fun n hn α hα => key (Or.inl ⟨n, hn, α, hα⟩),
    fun α hα => key (Or.inr (Or.inl ⟨α, hα⟩)), fun α hα => key (Or.inr (Or.inr ⟨α, hα⟩))⟩

end CFSG.CGT.Foote82
