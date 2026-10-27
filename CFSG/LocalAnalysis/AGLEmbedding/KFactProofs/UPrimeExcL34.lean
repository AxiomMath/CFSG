module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SplitExc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Local
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer
public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMax

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.UPrimeExcL34

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open KFactProofs.L34Local

theorem card_galoisField_two_two : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem card_sylow_three_of_isLinThreeFour {K : Type} [Group K] [Finite K]
    (hK : IsLinThreeFour K) (T : Sylow 3 K) : Nat.card (T : Subgroup K) = 9 := by
  obtain ⟨ε₀⟩ := nonempty_equiv_of_isLinThreeFour hK
  refine card_sylow_three ?_ T
  rw [Nat.card_congr ε₀.toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL card_galoisField_two_two

theorem localData_of_isLinThreeFour {K : Type} [Group K] [Finite K] (hK : IsLinThreeFour K)
    (T : Sylow 3 K) : LocalData K (T : Subgroup K) := by
  obtain ⟨ε₀⟩ := nonempty_equiv_of_isLinThreeFour hK
  have hP₁ : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← card_sylow_three_of_isLinThreeFour hK T]
    exact (Nat.card_congr (ε₀.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.L34.exists_eq_map_conj_eZero
    card_galoisField_two_two hP₁
  let ε : projectiveSL 3 (GaloisField 2 2) ≃* K := (MulAut.conj g).trans ε₀.symm
  have hεT : ∀ y, y ∈ CFSG.RankThree.PartTwo.KFacts.L34.eZero (GaloisField 2 2) ↔
      ε y ∈ (T : Subgroup K) := by
    intro y
    have h1 : ε y ∈ (T : Subgroup K) ↔ g * y * g⁻¹ ∈ (T : Subgroup K).map ε₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      rfl
    rw [h1, hg, Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  exact (localData_eZero card_galoisField_two_two).map ε hεT

theorem glbCore_eq_normalizer {K : Type} [Group K] [Finite K] {T : Subgroup K}
    (h : LocalData K T) : GLBCore 3 1 T = Subgroup.normalizer (T : Set K) :=
  GLBCoreNormalizer.glbCore_eq_normalizer Nat.prime_three (by rw [h.card_eq]; norm_num)
    h.commute_of_card_eq h.centralizer_le

theorem nonempty_equiv_projSL {K : Type} [Group K] (hK : IsLinThreeFour K) :
    Nonempty (K ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) := by
  obtain ⟨ε₀⟩ := nonempty_equiv_of_isLinThreeFour hK
  exact ⟨ε₀.trans
    (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm⟩

theorem eq_bot_of_le_normalizer_of_isLinThreeFour {K : Type} [Group K] (hK : IsLinThreeFour K)
    {E Y : Subgroup K} (hE : Nat.card E = 9) (hY : ¬ 3 ∣ Nat.card Y)
    (hEY : E ≤ Subgroup.normalizer (Y : Set K)) : Y = ⊥ := by
  obtain ⟨ε⟩ := nonempty_equiv_of_isLinThreeFour hK
  have hE' : Nat.card (E.map ε.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ε.injective, hE]
  have hY' : ¬ 3 ∣ Nat.card (Y.map ε.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective ε.injective]
  have hEY' : E.map ε.toMonoidHom ≤ Subgroup.normalizer ((Y.map ε.toMonoidHom : Subgroup _) :
      Set (projectiveSL 3 (GaloisField 2 2))) := by
    rw [← Subgroup.map_equiv_normalizer_eq Y ε]
    exact Subgroup.map_mono hEY
  exact (Subgroup.map_eq_bot_iff_of_injective Y ε.injective).1
    (CFSG.RankThree.PartTwo.KFacts.L34.eq_bot_of_le_normalizer card_galoisField_two_two hE' hY'
      hEY')

end KFactProofs.UPrimeExcL34

open CFSG.Open KFactProofs.UPrimeExcL34

theorem kFactUPrimeExcL34 :
    KFactUPrimeExcL34 := by
  intro K _ _ p hpK T _
  obtain ⟨rfl, hK⟩ := hpK
  obtain ⟨e⟩ := nonempty_equiv_projSL hK
  have hTcard : Nat.card (T : Subgroup K) = 9 := card_sylow_three_of_isLinThreeFour hK T
  have hΓ : GLBCore 3 1 (T : Subgroup K) = Subgroup.normalizer ((T : Subgroup K) : Set K) :=
    glbCore_eq_normalizer (localData_of_isLinThreeFour hK T)
  rw [hΓ]
  refine ⟨fun Y hY => ?_, fun N hNle hNn hcop => ?_⟩
  · by_cases hYtop : Y = ⊤
    · exact Or.inr hYtop
    · exact Or.inl
        (CFSG.RankThree.PartTwo.KFacts.L34Max.eq_normalizer_of_normalizer_le e hTcard hY hYtop)
  · have hconj : ∀ t ∈ (T : Subgroup K), ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
      intro t ht n hn
      have htΓ : t ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := Subgroup.le_normalizer ht
      have h1 := hNn.conj_mem ⟨n, hNle hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨t, htΓ⟩
      exact Subgroup.mem_subgroupOf.1 h1
    have hT : (T : Subgroup K) ≤ Subgroup.normalizer (N : Set K) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro n
      refine ⟨fun hn => hconj t ht n hn, fun hn => ?_⟩
      have := hconj t⁻¹ ((T : Subgroup K).inv_mem ht) _ hn
      rwa [show t⁻¹ * (t * n * t⁻¹) * t⁻¹⁻¹ = n by group] at this
    exact eq_bot_of_le_normalizer_of_isLinThreeFour hK hTcard
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop) hT

end CFSG.AGLEmbedding
