module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Camp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620FStarMain
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem pCoreOf_le_primeCore' {H : Subgroup G}
    (hH : H ≤ normalizer (pCoreOf 2 H : Set G)) : pCoreOf 2 H ≤ rankThreePrimeCore 3 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_sSup ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 H,
    (normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr hH, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H)
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem exists_data620 (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {H S K : Subgroup G} {b : G}
    (hext : Prop614Extremal M (zpowers x ⊔ zpowers z) H S)
    (hHN : H = normalizer (pCoreOf 2 H : Set G))
    (hmax : IsMaxTwoInvariantIn (zpowers x ⊔ zpowers z) H S) (hOS : pCoreOf 2 H ≤ S)
    (hS1 : ∀ S₀ : Subgroup G, pCoreOf 2 H < S₀ → S₀ ≤ S →
      S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M)
    (hS2 : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
      normalizer (S₀ : Set G) ≤ M)
    (hvi : rankThreePrimeCore 3 H ≤ pCoreOf 2 H)
    (h3 : ¬ 3 ∣ (zpowers x ⊔ zpowers z).relIndex H)
    (hK : Prop614Component M H K x z) (hb : Prop614Layer P M H K x z b)
    (hSK : S ≤ K ⊔ pCoreOf 2 H) (hSi : (pCoreOf 2 H).relIndex S = 4) :
    ∃ f : ↥K →* GL32, Data620 M (zpowers x ⊔ zpowers z) H S K z b f := by
  have hOeq : rankThreePrimeCore 3 H = pCoreOf 2 H :=
    le_antisymm hvi (pCoreOf_le_primeCore' hHN.le)
  obtain ⟨f₀, hf₀s, hf₀k⟩ := hb.kbar
  let f : ↥K →* GL32 := (L32Insp.pslEquiv : PSL(3, ZMod 2) ≃* GL32).toMonoidHom.comp f₀
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hplane := SmallRankPlane.of_situation hS hsit hx hz
  have hb3 : b ^ 3 = 1 := hplane.isElemAbelian.2 b hb.mem
  have hb1 : b ≠ 1 := fun h => hb.not_mem (h ▸ one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hB9 : Nat.card ↥(zpowers x ⊔ zpowers z) = 9 := by
    rw [hplane.card_eq]
    norm_num
  have hBeq : zpowers x ⊔ zpowers z = zpowers z ⊔ zpowers b := by
    have hle : zpowers z ⊔ zpowers b ≤ zpowers x ⊔ zpowers z :=
      sup_le (Subgroup.mem_sup_right (mem_zpowers z) |> zpowers_le.2)
        (zpowers_le.2 hb.mem)
    have hz3 : Nat.card (zpowers z) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hz.pow_eq_one hz.ne_one
    have hlt : zpowers z < zpowers z ⊔ zpowers b :=
      lt_of_le_of_ne le_sup_left fun e =>
        hb.not_mem (e ▸ (le_sup_right : zpowers b ≤ zpowers z ⊔ zpowers b) (mem_zpowers b))
    have hd1 : 3 ∣ Nat.card ↥(zpowers z ⊔ zpowers b) := hz3 ▸ Subgroup.card_dvd_of_le le_sup_left
    have hd2 : Nat.card ↥(zpowers z ⊔ zpowers b) ∣ 9 :=
      hB9 ▸ Subgroup.card_dvd_of_le hle
    have hne : Nat.card ↥(zpowers z ⊔ zpowers b) ≠ 3 := fun e => by
      have := Subgroup.eq_of_le_of_card_ge (le_sup_left : zpowers z ≤ zpowers z ⊔ zpowers b)
        (by rw [e, hz3])
      exact hlt.ne this
    have h9 : Nat.card ↥(zpowers z ⊔ zpowers b) = 9 := by
      obtain ⟨c, hc⟩ := hd1
      have hc9 : c ∣ 3 := by
        rw [hc] at hd2
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (by simpa [mul_comm] using hd2)
      rcases (Nat.dvd_prime Nat.prime_three).1 hc9 with rfl | rfl
      · exact (hne (by simpa using hc)).elim
      · omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hB9])).symm
  refine ⟨f, ?_⟩
  exact
    { charTwo := hS.charTwo
      twoLocal := hext.pair.isTwoLocal
      eq_normalizer := hHN
      B_le := hext.pair.le
      maxInv := hmax
      core_le := hOS
      S_ne_bot := hext.pair.ne_bot
      norm_le := hS1
      char_le := hS2
      K_le := hK.le
      K_normal := hK.normal
      K_not_le := hK.not_le
      K_simple := fun N hNK hN hle => by
        rw [← hOeq] at hle ⊢
        exact hK.maximal N hNK hN hle
      f_surj := (L32Insp.pslEquiv : PSL(3, ZMod 2) ≃* GL32).surjective.comp hf₀s
      f_ker := fun k => by
        rw [← hOeq, ← hf₀k k]
        exact map_eq_one_iff _ (L32Insp.pslEquiv : PSL(3, ZMod 2) ≃* GL32).injective
      z_mem_K := hK.mem (mem_zpowers z)
      z_mem_B := Subgroup.mem_sup_right (mem_zpowers z)
      z_order := orderOf_eq_prime hz.pow_eq_one hz.ne_one
      M_solvable := hsolv
      primeCore_le := fun N hNH hHN' hcop => by
        refine le_trans ?_ hvi
        exact le_sSup ⟨hNH, (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN', hcop⟩
      B_card := hB9
      B_sylow := h3
      b_mem := hb.mem
      b_order := hbo
      b_not_mem := hb.not_mem
      B_eq := hBeq
      b_cent := by
        rw [← hOeq]
        exact hb.centralizes
      b_fpf := fun o ho h => hb.fixed_point_free o (hOeq ▸ ho) h
      K_perfect := hK.perfect
      S_le := hSK
      S_index := hSi }

theorem prop614Core21_of_core22 (hS : Setting G) (h : GL83SmallRankProp614Core22 G) :
    GL83SmallRankProp614Core21 G := by
  intro P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hvi hex
  obtain ⟨K, b, hK, hb, hSK, hSi⟩ := hex
  obtain ⟨f, hD⟩ := exists_data620 hS hsit hsolv hx hz hext hHN hmax hOS hS1 hS2 hvi h3 hK hb hSK
    hSi
  exact h P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hvi
    ⟨K, b, hK, hb, hSK, hSi, hD.fStarEq⟩

private theorem exists_sylow_two_le {X S : Subgroup G} (hSX : S ≤ X) (hS : IsPGroup 2 S) :
    ∃ R : Subgroup G, S ≤ R ∧ R ≤ X ∧ IsPGroup 2 R ∧ ¬ 2 ∣ (R.subgroupOf X).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := (hS.comap_subtype (K := X)).exists_le_sylow
  refine ⟨(Q : Subgroup X).map X.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro s hs
    exact ⟨⟨s, hSX hs⟩, hQ hs, rfl⟩
  · exact Q.isPGroup'.map X.subtype
  · change ¬ 2 ∣ (comap X.subtype (map X.subtype (Q : Subgroup X))).index
    rw [comap_map_eq_self_of_injective X.subtype_injective]
    exact Q.not_dvd_index

theorem prop614Core22_of_core23 (hS : Setting G) (hCamp : KFactCampbell)
    (h : GL83SmallRankProp614Core23 G) : GL83SmallRankProp614Core22 G := by
  intro P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hvi hex
  obtain ⟨K, b, hK, hb, hSK, hSi, hF⟩ := hex
  by_cases hfail : CampbellFails H S K
  · exact h P M hsit hsolv he x z hx hz H S hext h3 hHN hmax hOS hS1 hS2 hOM hvi
      ⟨K, b, hK, hb, hSK, hSi, hF, hfail⟩
  · obtain ⟨f, hD⟩ := exists_data620 hS hsit hsolv hx hz hext hHN hmax hOS hS1 hS2 hvi h3 hK hb hSK
      hSi
    obtain ⟨R, hSR, hRX, hR2, hRi⟩ := exists_sylow_two_le hSK hmax.1.2.1
    refine hD.false_of_campbell hCamp hSR hRX hR2 hRi ?_
    by_contra hC
    exact hfail ⟨R, hSR, hRX, hR2, hRi, hC⟩

theorem prop614_of_core23 (hS : Setting G) (hU0 : FullCoreLocal G) (hD2 : TheoremD2 G)
    (hK : KFactBlockFactorThreePrime) (hKF1 : KFactSylowNormalizerIrreducible)
    (hKF2 : KFactOutThreePrimeSimple) (hK1 : KFactRankTwoUniqueness)
    (hK2 : KFactRankThreeStructure) (h627 : GL83SmallRankProp627 G)
    (h632 : GL83SmallRankProp632 G) (hCamp : KFactCampbell)
    (h : GL83SmallRankProp614Core23 G) : GL83SmallRankProp614 G :=
  prop614_of_core21 hS hU0 hD2 hK hKF1 hKF2 hK1 hK2 h627 h632
    (prop614Core21_of_core22 hS (prop614Core22_of_core23 hS hCamp h))

end CFSG.LocalAnalysis.RankThreeTheoremC
