module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoData
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28G2Data
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28G2Torus
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LieType.Chevalley.PerfectSimpleRoot
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.ToralCensus CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs (gtwoTorusHom gtwoTorusHom_apply gtwoNode0
  gtwoNode1 gtwo_sq_eq_one_of_torusHom_eq_one gtwo_exists_cartan_inverse gtwo_exists_cover
  isElemAbelian_range_of_pow)

private theorem sixty_mem_of_isFiveComponent (hLB : LeviBlocksOfFiveComponents) {Y : Type}
    [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L) {K : Type} [Group K] [Finite K]
    (ρ : K →* ↥L) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center K) {𝒯 : Set ℕ}
    (hQ : HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯) {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)}
    (hC : IsFiveComponent P C) : 60 ∈ 𝒯 := by
  obtain ⟨k, G, _, _, S, β, hkerβ, hpi, hcomm, hS, h𝒯⟩ := hQ
  obtain ⟨j, hq, h60⟩ := (hLB Y L P hPL K ρ hρ hker (Fin k) G S β hkerβ hpi hcomm hS).1 C hC
  exact h60 ▸ h𝒯 j hq

private theorem e9_of_torus {Y : Type} [Group Y] {L : Subgroup Y} {M : Type} [CommGroup M]
    (hM : Nat.card M = 3) (f : (Fin 2 → M) →* Y) (hf : Function.Injective f)
    (hL : f.range ≤ L) (hc : ∀ a, f a ∈ Subgroup.centralizer (L : Set Y) → a = 1) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  have hpow : ∀ a : Fin 2 → M, a ^ 3 = 1 := fun a => funext fun j => by
    rw [Pi.pow_apply, Pi.one_apply, ← hM]
    exact pow_card_eq_one'
  refine ⟨f.range, hL, isElemAbelian_range_of_pow (fun a b => mul_comm a b) hpow f, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_fun, hM, Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, hxC⟩
    rw [hc a hxC, map_one]
    exact Subgroup.one_mem _

private theorem gtwo_eq_one_of_torusHom_eq_one_three
    {F : Type} [Field F] (hF : Nat.card Fˣ = 3)
    (i : Fin (Tag.rank .G2)) {t : Fˣ} (ht : torusHom F i t = 1) : t = 1 := by
  have h2 := gtwo_sq_eq_one_of_torusHom_eq_one i ht
  have h3 : t ^ 3 = 1 := by rw [← hF]; exact pow_card_eq_one'
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 3)
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))

private theorem gtwoTorusHom_injective_three
    {F : Type} [Field F]
    (hF : Nat.card Fˣ = 3) : Function.Injective (gtwoTorusHom F) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨B, hB⟩ := gtwo_exists_cartan_inverse
  have hdis : Disjoint (torus F gtwoNode0) (torus F gtwoNode1) :=
    (torus_iSupIndep (K := F) hB).pairwiseDisjoint (by decide : gtwoNode0 ≠ gtwoNode1)
  rw [gtwoTorusHom_apply] at ha
  have h0 : torusHom F gtwoNode0 (a 0) = 1 := by
    refine Subgroup.disjoint_def.1 hdis ⟨a 0, rfl⟩ ?_
    have h : torusHom F gtwoNode0 (a 0) = torusHom F gtwoNode1 (a 1)⁻¹ := by
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_left ha
    rw [h]
    exact ⟨(a 1)⁻¹, rfl⟩
  have h1 : torusHom F gtwoNode1 (a 1) = 1 := by
    rw [h0, one_mul] at ha
    exact ha
  funext i
  fin_cases i
  · exact gtwo_eq_one_of_torusHom_eq_one_three hF _ h0
  · exact gtwo_eq_one_of_torusHom_eq_one_three hF _ h1


private theorem gtwo_exists_leviData_central (hGA : GriessAllModelsStatement) {Y : Type}
    [Group Y] [Finite Y] {L P : Subgroup Y} (hCP : CompParab L P)
    (hG : IsLieOf IdxG2 (↥L ⧸ Subgroup.center ↥L)) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (G : Type) (_ : Group G)
      (_ : Finite G) (S : Subgroup G) (β : ↥((P.subgroupOf L).comap ρ) →* (Fin 1 → G)),
      Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center K ∧ IsPGroup 2 β.ker ∧
      Subgroup.pi Set.univ (fun _ => S) ≤ β.range ∧
      ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ (fun _ => S) ∧ CFSG.Open.IsQuasisimple ↥S := by
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_mulEquiv_g2 hGA hCP hG
  obtain ⟨T, hNT, hne, htop⟩ := exists_sylow_le_subgroupOf_of_compParab hCP
  obtain ⟨π', hQ, hBA, i, hI⟩ := exists_single_node_g2 e T hNT hne htop
  have : Finite ↥(adjointGroup .G2 (GaloisField 2 f)) := generated_group_finite .G2 _
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := GaloisField 2 f) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    sl2_isSimpleGroup h4
  have : IsSimpleGroup ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i) := eL.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(rankOne (g2Datum (GaloisField 2 f)).rootGroup i), a * b ≠ b * a :=
    ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
      sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩
  obtain ⟨G, _, _, S, β, hker, hpi, hcomm, ⟨eS⟩⟩ :=
    exists_leviData_of_negIndices_eq hQ hBA hI (rankOne_inf_posUnipotentExcept_eq_bot hQ i hnc)
  obtain ⟨hqs, -, -⟩ := sl2Block_facts h4 (eL.trans eS)
  exact ⟨_, inferInstance, inferInstance, π', G, inferInstance, inferInstance, S, β, hQ.surj,
    fun z hz => hQ.ker_central z (MonoidHom.mem_ker.mp hz), hker, hpi, hcomm, hqs⟩

theorem kFactCompParabTwoFivesOn_g2 (hLB : LeviBlocksOfFiveComponents)
    (hGA : GriessAllModelsStatement) : KFactCompParabTwoFivesOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG _ C₁ C₂ hne hC₁ hC₂
  obtain ⟨K, _, _, ρ, G, _, _, S, β, hρ, hker, hkerβ, hpi, hcomm, hqs⟩ :=
    gtwo_exists_leviData_central hGA hCP hG
  obtain ⟨j₁, j₂, hj, -⟩ := (hLB Y L P hCP.parab.1 K ρ hρ hker (Fin 1) (fun _ => G)
    (fun _ => S) β hkerβ hpi hcomm (fun _ => Or.inl hqs)).2 C₁ C₂ hne hC₁ hC₂
  exact absurd (Subsingleton.elim j₁ j₂) hj

theorem kFactCompParabOneFiveOn_g2 (hLB : LeviBlocksOfFiveComponents)
    (hGA : GriessAllModelsStatement) : KFactCompParabOneFiveOn (IsLieOf IdxG2) := by
  intro Y _ _ L P hCP hG C hC
  obtain ⟨f, π, hπs, hπi, hQ⟩ := gtwo_exists_cover hGA hCP hG
  have : Finite ↥(adjointGroup .G2 (GaloisField 2 f)) := generated_group_finite .G2 _
  have hker : π.ker ≤ Subgroup.center ↥(adjointGroup .G2 (GaloisField 2 f)) := by
    rw [(MonoidHom.ker_eq_bot_iff π).2 hπi]
    exact bot_le
  have h60 := sixty_mem_of_isFiveComponent hLB hCP.parab.1 π hπs hker hQ hC
  have h4 : 2 ^ f = 4 := ((ordA_eq_sixty_iff rfl).1 (Set.mem_singleton_iff.1 h60).symm).2
  have hF : Nat.card (GaloisField 2 f) = 4 := by
    rw [GaloisField.card 2 f (by rintro rfl; norm_num at h4), h4]
  have hu : Nat.card (GaloisField 2 f)ˣ = 3 := by rw [Nat.card_units, hF]
  refine Or.inl (e9_of_torus hu (L.subtype.comp (π.comp (gtwoTorusHom (GaloisField 2 f))))
    ((Subgroup.subtype_injective L).comp (hπi.comp (gtwoTorusHom_injective_three hu))) ?_ ?_)
  · rintro _ ⟨a, rfl⟩
    exact (π (gtwoTorusHom (GaloisField 2 f) a)).2
  · intro a ha
    have hc : gtwoTorusHom (GaloisField 2 f) a ∈
        Subgroup.center ↥(adjointGroup .G2 (GaloisField 2 f)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply hπi
      rw [map_mul, map_mul]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 ha (π g) (π g).2)
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
    exact gtwoTorusHom_injective_three hu (hc.trans (map_one _).symm)

end CFSG.AGLEmbedding
