module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PUBlock
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactL34NotOrthogonal : Prop :=
  ∀ (K : Type) [Group K], IsLinThreeFour K → ¬ IsOrthogonalTwo K

variable {G : Type} [Group G] [Finite G] {M H L : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
  {φ : (↥H ⧸ CFSG.pCore 2 ↥H) →* (↥H ⧸ primeComplementCore (G := H) 3)}

namespace L34BlockFacts

omit [Finite G] in
theorem injective (hB : L34BlockFacts M H L K φ) (hZ : Subgroup.center (barM H L) = ⊥) :
    Function.Injective (φ.comp (barM H L).subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  exact hZ ▸ hB.ker_le

omit [Finite G] in
theorem range_eq (_hB : L34BlockFacts M H L K φ) :
    (φ.comp (barM H L).subtype).range = (barM H L).map φ := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

noncomputable def equivK (hB : L34BlockFacts M H L K φ) (hZ : Subgroup.center (barM H L) = ⊥) :
    barM H L ≃* K :=
  (MonoidHom.ofInjective (hB.injective hZ)).trans
    (MulEquiv.subgroupCongr (by rw [hB.range_eq, hB.map_eq]))

omit [Finite G] in
theorem card_eq (hB : L34BlockFacts M H L K φ) (hZ : Subgroup.center (barM H L) = ⊥) :
    Nat.card (barM H L) = 20160 := by
  rw [Nat.card_congr (hB.equivK hZ).toEquiv, ← hB.map_eq, hB.card_map]

omit [Finite G] in
theorem card_map_eq (hB : L34BlockFacts M H L K φ) (hZ : Subgroup.center (barM H L) = ⊥)
    {X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hX : X ≤ barM H L) :
    Nat.card (X.map φ) = Nat.card X := by
  have e : X.map φ = (X.subgroupOf (barM H L)).map (φ.comp (barM H L).subtype) := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hX]
  rw [e, Subgroup.card_map_of_injective (hB.injective hZ),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv]

omit [Finite G] in
theorem card_quotient_center (hB : L34BlockFacts M H L K φ) :
    Nat.card (barM H L ⧸ Subgroup.center (barM H L)) = 20160 := by
  have hker : (φ.comp (barM H L).subtype).ker = Subgroup.center (barM H L) :=
    le_antisymm hB.ker_le hB.le_ker
  have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange (φ.comp (barM H L).subtype))
  rw [Nat.card_congr e.toEquiv, hB.range_eq, hB.card_map]

theorem not_nineThreeTwo (hB : L34BlockFacts M H L K φ)
    (h72 : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) 3), Y ≤ d1X0 3 M H ⊓ K →
      Nat.card Y ∣ 72) : ¬ NineThreeTwo H (pCoreOf 2 (H ⊓ M)) L := by
  rintro ⟨-, ⟨-, T, hT, hTN⟩, -⟩
  have hTJ : T ≤ barM H (Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ⊓ L) :=
    fun t ht => hTN ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
  have hdvd := h72 (T.map φ) ((Subgroup.map_mono hTJ).trans hB.map_J)
  rw [card_map_of_isSylowTwoOf φ hT hB.card_map] at hdvd
  norm_num at hdvd

omit [Finite G] in
theorem not_nineThreeThree (hB : L34BlockFacts M H L K φ) (hNO : KFactL34NotOrthogonal)
    (hL : IsLinThreeFour K) : ¬ NineThreeThree H (pCoreOf 2 (H ⊓ M)) L := by
  rintro ⟨-, hO2, -⟩
  have hZ := center_eq_bot_of_isOrthogonalTwo ⟨hB.quasisimple.1⟩
    (exists_ne_comm_of_isQuasisimple hB.quasisimple) hO2
  exact hNO K hL (IsOrthogonalTwo.of_mulEquiv (hB.equivK hZ).symm hO2)

theorem not_nineThreeFour (hB : L34BlockFacts M H L K φ) :
    ¬ NineThreeFour H (pCoreOf 2 (H ⊓ M)) L := by
  rintro ⟨-, h3, -⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (barM H L)) 3
    (by rw [h3])
  have hxk := hB.le_ker x.2
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at hxk
  have hc := hB.ker_coprime _ hxk
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx] at hc
  norm_num at hc

omit [Finite G] in
theorem not_nineThreeFive (hB : L34BlockFacts M H L K φ) : ¬ NineThreeFive H L := by
  rintro ⟨-, ⟨e⟩, -⟩
  have h1 : Nat.card (barM H L) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have h2 := Subgroup.card_map_dvd (barM H L) φ
  rw [hB.card_map, h1] at h2
  norm_num at h2

omit [Finite G] in
theorem not_nineThreeSix (hB : L34BlockFacts M H L K φ) :
    ¬ NineThreeSix H (pCoreOf 2 (H ⊓ M)) L := by
  rintro ⟨-, n, ⟨e₁⟩, ⟨e₂⟩⟩
  have h1 := hB.card_quotient_center
  rw [Nat.card_congr e₁.toEquiv] at h1
  have h8 := eq_eight_of_card_alternatingGroup h1
  obtain rfl : n = 4 := by omega
  obtain ⟨V, hVn, hVp, hV1⟩ := exists_normal_two_perm_four
  exact not_nonempty_quotient_pCore_equiv hVn hVp hV1 ⟨e₂⟩

omit [Finite G] in
theorem not_nineThreeSeven (hB : L34BlockFacts M H L K φ) :
    ¬ NineThreeSeven H (pCoreOf 2 (H ⊓ M)) L := by
  rintro ⟨-, n, ⟨e₁⟩, ⟨e₂⟩⟩
  have hZ := center_eq_bot_of_mulEquiv_alternating
    (exists_ne_comm_of_isQuasisimple hB.quasisimple) e₁
  have h1 := hB.card_eq hZ
  rw [Nat.card_congr e₁.toEquiv] at h1
  have h8 := eq_eight_of_card_alternatingGroup h1
  obtain rfl : n = 2 := by omega
  obtain ⟨V, hVn, hVp, hV1⟩ := exists_normal_two_perm_two
  exact not_nonempty_quotient_pCore_equiv hVn hVp hV1 ⟨e₂⟩

theorem not_nineThreeEight (hB : L34BlockFacts M H L K φ)
    (h72 : ∀ Y : Subgroup (H ⧸ primeComplementCore (G := H) 3), Y ≤ d1X0 3 M H ⊓ K →
      Nat.card Y ∣ 72) : ¬ NineThreeEight H (pCoreOf 2 (H ⊓ M)) L := by
  rintro ⟨-, N, r, -, h2r, h0, h2, h4, ⟨e₁⟩, φ₂, -, -⟩
  have hZ := center_eq_bot_of_mulEquiv_alternating
    (exists_ne_comm_of_isQuasisimple hB.quasisimple) e₁
  have h1 := hB.card_eq hZ
  rw [Nat.card_congr e₁.toEquiv] at h1
  obtain rfl := eq_eight_of_card_alternatingGroup h1
  set J := barM H (Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ⊓ L) with hJ
  have hJ72 : Nat.card J ≤ 72 := by
    have := h72 (J.map φ) hB.map_J
    rw [hB.card_map_eq hZ hB.J_le] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hq : Nat.card (J ⧸ CFSG.pCore 2 J) ≤ Nat.card J :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  rw [Nat.card_congr φ₂.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_perm, Nat.card_fin,
    Nat.card_fin] at hq
  have hr : r = 0 ∨ r = 1 := by omega
  rcases hr with rfl | rfl <;> norm_num [Nat.factorial] at hq <;> omega

end L34BlockFacts

end CFSG.AGLEmbedding
