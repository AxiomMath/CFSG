module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley Subgroup
open scoped commutatorElement


theorem odd_card_of_pow_eq_one {G : Type*} [Group G] [Finite G] {M : ℕ} (hM : Odd M)
    (h : ∀ g : G, g ^ M = 1) : Odd (Nat.card G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hodd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hodd
  exact hM.not_two_dvd_nat (hg ▸ orderOf_dvd_of_pow_eq_one (h g))

theorem not_two_dvd_relIndex_pi_oneBlock {Q : Type*} [Group Q] (U Λ : Subgroup Q) [U.Normal]
    (h : ¬ 2 ∣ (Λ ⊔ U).index) :
    ¬ 2 ∣ (Subgroup.pi Set.univ (fun _ : Fin 1 => Λ.map (QuotientGroup.mk' U))).relIndex
      (MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).range := by
  classical
  have hrange : (MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U).range = ⊤ := by
    rw [eq_top_iff]
    rintro g -
    choose x hx using fun j => QuotientGroup.mk'_surjective U (g j)
    exact ⟨x 0, funext fun j => by
      rw [MonoidHom.pi_apply, Fin.fin_one_eq_zero j]
      exact hx 0⟩
  have hev : Function.Surjective (Pi.evalMonoidHom (fun _ : Fin 1 => Q ⧸ U) 0) :=
    fun y => ⟨fun _ => y, rfl⟩
  have hpi : Subgroup.pi Set.univ (fun _ : Fin 1 => Λ.map (QuotientGroup.mk' U)) =
      (Λ.map (QuotientGroup.mk' U)).comap (Pi.evalMonoidHom (fun _ : Fin 1 => Q ⧸ U) 0) := by
    ext g
    simp only [Subgroup.mem_pi, Subgroup.mem_comap, Pi.evalMonoidHom_apply, Set.mem_univ,
      true_implies]
    exact Fin.forall_fin_one
  have hmap : (Λ.map (QuotientGroup.mk' U)).comap (QuotientGroup.mk' U) = Λ ⊔ U := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hidx : (Λ.map (QuotientGroup.mk' U)).index = (Λ ⊔ U).index := by
    rw [← hmap]
    exact (Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)).symm
  rw [hrange, Subgroup.relIndex_top_right, hpi,
    Subgroup.index_comap_of_surjective _ hev, hidx]
  exact h

theorem hasLeviCensus_idxG2 (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] {L J : Subgroup X} (hCP : CompParab L J) (h : IsLieOf IdxG2 (↥L ⧸ center ↥L)) :
    HasLeviCensus ↥J IsWBlock := by
  classical
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2 hGA hCP h
  obtain ⟨T, hNT, hne, htop⟩ := exists_sylow_le_subgroupOf_of_compParab hCP
  obtain ⟨π', hQ, hBA, i, hI⟩ := exists_single_node_g2 e T hNT hne htop
  haveI : Finite ↥(adjointGroup .G2 (GaloisField 2 f)) := generated_group_finite .G2 _
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := GaloisField 2 f) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    sl2_isSimpleGroup h4
  have : IsSimpleGroup ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i) :=
    eL.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i), a * b ≠ b * a :=
    ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
      sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩
  have hLU : rankOne (g2Datum (GaloisField 2 f)).rootGroup i ⊓
      posUnipotentExcept (g2Datum (GaloisField 2 f)) i = ⊥ :=
    rankOne_inf_posUnipotentExcept_eq_bot hQ i hnc
  set A : Subgroup ↥(adjointGroup .G2 (GaloisField 2 f)) := (J.subgroupOf L).comap π' with hA
  have hUA : posUnipotentExcept (g2Datum (GaloisField 2 f)) i ≤ A := by
    rw [hA]
    exact posUnipotentExcept_le_of_borel_le hBA i
  have hLA : rankOne (g2Datum (GaloisField 2 f)).rootGroup i ≤ A := by
    rw [hA]
    exact rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  set U : Subgroup ↥A := (posUnipotentExcept (g2Datum (GaloisField 2 f)) i).subgroupOf A with hU
  set Λ : Subgroup ↥A := (rankOne (g2Datum (GaloisField 2 f)).rootGroup i).subgroupOf A with hΛ
  have hUn : U.Normal := by
    rw [hU]
    exact (normal_subgroupOf_iff_le_normalizer hUA).mpr
      (le_normalizer_posUnipotentExcept_of_negIndices_eq hQ hBA hI)
  haveI := hUn
  have hU2 : IsPGroup 2 U := by
    rw [hU]
    exact (isPGroup_posUnipotentExcept hQ i).comap_subtype
  have hΛU : Λ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx : (x : ↥(adjointGroup .G2 (GaloisField 2 f))) ∈
        rankOne (g2Datum (GaloisField 2 f)).rootGroup i ⊓
          posUnipotentExcept (g2Datum (GaloisField 2 f)) i :=
      ⟨Subgroup.mem_subgroupOf.mp hx1, Subgroup.mem_subgroupOf.mp hx2⟩
    rw [hLU, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.2 (Subtype.ext hx)
  obtain ⟨eΛ⟩ := nonempty_mulEquiv_oneBlock U Λ hΛU
  have eSL : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) ≃*
      ↥(Λ.map (QuotientGroup.mk' U)) :=
    eL.trans ((Subgroup.subgroupOfEquivOfLe hLA).symm.trans eΛ)
  obtain ⟨hqsS, hZS, -⟩ := sl2Block_facts h4 eSL
  have hWblock : IsWBlock ↥(Λ.map (QuotientGroup.mk' U)) := by
    refine Or.inl ⟨hqsS, ?_⟩
    rw [hZS, Subgroup.card_bot]
    exact odd_one
  let S : ∀ _ : Fin 1, Subgroup (↥A ⧸ U) := fun _ => Λ.map (QuotientGroup.mk' U)
  let β : ↥A →* ∀ _ : Fin 1, ↥A ⧸ U := MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U
  have hβ : IsPGroup 2 β.ker := isPGroup_ker_oneBlock U hU2
  have hle : Subgroup.pi Set.univ S ≤ β.range := pi_le_range_oneBlock U Λ
  have hc : ∀ a b : ↥A, ⁅a, b⁆ ∈ Λ ⊔ U := by
    intro a b
    have hsup : Λ ⊔ U =
        (rankOne (g2Datum (GaloisField 2 f)).rootGroup i ⊔
          posUnipotentExcept (g2Datum (GaloisField 2 f)) i).subgroupOf A := by
      rw [hΛ, hU, Subgroup.subgroupOf_sup hLA hUA]
    rw [hsup]
    exact Subgroup.mem_subgroupOf.2 (commutator_mem_of_negIndices_eq hQ hBA hI a.2 b.2)
  have hn : β.range ≤
      Subgroup.normalizer (Subgroup.pi Set.univ S : Set (∀ _ : Fin 1, ↥A ⧸ U)) :=
    le_normalizer_of_commutator_le hle (commutator_range_oneBlock_le U Λ hc)
  have hUplus : posUnipotent (g2Datum (GaloisField 2 f)) ≤ A := by
    rw [hA]
    exact (posUnipotent_le_borel (D := g2Datum (GaloisField 2 f))
      (H := torus (τ := .G2) (GaloisField 2 f))).trans hBA
  have hUp : posUnipotent (g2Datum (GaloisField 2 f)) ≤
      rankOne (g2Datum (GaloisField 2 f)).rootGroup i ⊔
        posUnipotentExcept (g2Datum (GaloisField 2 f)) i := by
    rw [posUnipotent_eq_sup hQ.extras i]
    exact sup_le le_sup_right (le_sup_of_le_left (le_sup_left : _ ≤ rankOne _ i))
  have hsub : (posUnipotent (g2Datum (GaloisField 2 f))).subgroupOf A ≤ Λ ⊔ U := by
    rw [hΛ, hU, ← Subgroup.subgroupOf_sup hLA hUA]
    exact Subgroup.subgroupOf_mono A hUp
  have hoddA : ¬ 2 ∣ ((posUnipotent (g2Datum (GaloisField 2 f))).subgroupOf A).index := by
    intro h2
    refine hQ.not_dvd_index ?_
    rw [← Subgroup.relIndex_mul_index hUplus]
    exact dvd_mul_of_dvd_left h2 _
  have hoddLU : ¬ 2 ∣ (Λ ⊔ U).index := fun h2 =>
    hoddA (h2.trans (Subgroup.index_dvd_of_le hsub))
  have hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range :=
    not_two_dvd_relIndex_pi_oneBlock U Λ hoddLU
  have hS : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j) := fun _ => Or.inr hWblock
  have hZ : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z : ↥A, π' ↑z = 1 →
      β z ∈ (S j).map (MonoidHom.mulSingle (fun _ : Fin 1 => ↥A ⧸ U) j) → β z = 1 :=
    fun _ hj => absurd hqsS hj
  exact hasLeviCensus_of_cover_of_finite hCP.parab.1 π' hQ.surj
    (fun z hz => hQ.ker_central z hz)
    (odd_card_of_pow_eq_one (M := Nat.card (GaloisField 2 f) - 1) hQ.odd fun z =>
      Subtype.ext (by simpa using hQ.ker_pow (z : ↥(adjointGroup .G2 (GaloisField 2 f))) z.2))
    β hβ hle hn hi hS hZ

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
