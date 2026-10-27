module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourGN
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7KleinUnique
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B1Red CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)

theorem orderOf_perm7_ne_nine (σ : Equiv.Perm (Fin 7)) : orderOf σ ≠ 9 := by
  intro h
  have hmem : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have h1 : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : n ≤ σ.cycleType.sum := Multiset.le_sum_of_mem hn
    rw [Equiv.Perm.sum_cycleType] at h2
    have h2' : σ.support.card ≤ 7 := by
      have := Finset.card_le_univ σ.support
      simpa using this
    have h3 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    rw [h] at h1
    have : n ≤ 7 := h2.trans h2'
    interval_cases n <;> simp_all <;> omega
  have : orderOf σ ∣ 3 := by
    rw [← Equiv.Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.mpr (fun n hn => (hmem n hn) ▸ dvd_refl _)
  rw [h] at this
  omega

theorem orderOf_alt7_ne_nine (g : alternatingGroup (Fin 7)) : orderOf g ≠ 9 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_perm7_ne_nine _

theorem isElemAbelian_three_of_card_nine {Y : Type*} [Group Y] {E : Subgroup Y}
    (hE : Nat.card E = 9) (hno : ∀ g ∈ E, orderOf g ≠ 9) : IsElemAbelian 3 E := by
  have hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hE' : Nat.card E = 3 ^ 2 := by rw [hE]; norm_num
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hE', fun x hx => ?_⟩
  have hd : orderOf x ∣ 3 ^ 2 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : E)
    rwa [hE', Subgroup.orderOf_mk] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 hd
  have hk2 : k ≤ 1 := by
    by_contra hk2
    have : k = 2 := by omega
    exact hno x hx (by rw [hk', this]; norm_num)
  have : orderOf x ∣ 3 := by
    rw [hk']
    interval_cases k <;> norm_num
  exact orderOf_dvd_iff_pow_eq_one.1 this

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem one_lt_pRank_three_gnA_of_nine {C₂ : Subgroup X} (h2 : C₂ ≤ baum T)
    (h2c : (C₂.subgroupOf (baum T)).Characteristic) {L : Subgroup (X ⧸ gnC T)}
    (eL : ↥L ≃* alternatingGroup (Fin 7)) {E : Subgroup (X ⧸ gnC T)} (hEL : E ≤ L)
    (hE9 : Nat.card E = 9) (hEN : E ≤ gnImg T (Subgroup.normalizer (baum T : Set X))) :
    1 < Open.pRank 3 (gnA T C₂ L) := by
  have hno : ∀ g ∈ E, orderOf g ≠ 9 := by
    intro g hg
    have : orderOf g = orderOf (eL ⟨g, hEL hg⟩) := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    rw [this]
    exact orderOf_alt7_ne_nine _
  have hEA := isElemAbelian_three_of_card_nine hE9 hno
  have hEA' : E ≤ gnA T C₂ L :=
    le_inf (hEN.trans (Subgroup.map_mono (normalizer_le_normalizer_of_characteristic_subgroupOf h2 h2c)))
      hEL
  have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEA' hEA (k := 2) (by rw [hE9]; norm_num)
  omega

@[expose] def A7NaturalCase (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Prop :=
  ∃ (g : ↥L →* alternatingGroup (Fin 7)) (W : Subgroup X)
    (π : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆ →* Multiplicative (altHeart 7)),
    Function.Surjective g ∧ W ≤ gnV T ∧ omegaOneCenterOf T ≤ W ∧
    (∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ w ∈ W, k * w * k⁻¹ ∈ W) ∧
    (∀ u, π u = 1 → ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)),
      (k : X) * u * (k : X)⁻¹ = u) ∧
    ∀ (l : X) (hl : QuotientGroup.mk' (gnC T) l ∈ L)
      (u u' : ↥⁅W, L.comap (QuotientGroup.mk' (gnC T))⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight 7,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart 7) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨QuotientGroup.mk' (gnC T) l, hl⟩ : Equiv.Perm (Fin 7)) x) :
            altHeart 7)

theorem gnAltSevenThreeRank_of_natural (hGF : GF2EightFive)
    (hNat : ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
      ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
        ∀ L : Subgroup (X ⧸ gnC T), GNYComponent T C₁ C₂ L →
          ∀ _ : ↥L ≃* alternatingGroup (Fin 7), gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) →
            A7NaturalCase T L →
              1 < Open.pRank 3 (gnA T C₁ L) ∨ 1 < Open.pRank 3 (gnA T C₂ L)) :
    GNAltSevenThreeRank := by
  intro X _ _ T hX hT C₁ C₂ hP L hY he hTL
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_alt_seven hX hY.1 hJ he
  obtain ⟨e⟩ := he
  let eL : ↥L ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientBot (G := ↥L)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e)
  rcases exists_naturalOn_or_four_of_gf2EightFive hGF hX hY.1 hJ eL with hn | ⟨W, U, hWV, hZW, hWK,
      hWU, hUV, hUK, hU16⟩
  · exact hNat X T hX hT C₁ C₂ hP L hY eL hTL hn
  · obtain ⟨E, hEL, hE9, hEN⟩ := exists_nine_le_normalizer_baum_of_four hX h1Z hY.1 hJ hY.2.1 eL
      alt7Hyp hTL hWV hZW hWK hWU hUV hUK hU16
    exact Or.inr (one_lt_pRank_three_gnA_of_nine h2B h2c eL hEL hE9 hEN)

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
