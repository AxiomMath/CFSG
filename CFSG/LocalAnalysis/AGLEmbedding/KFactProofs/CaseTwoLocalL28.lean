module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SplitExc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28Model
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.L28Local

open CFSG.Quasithin.F6.L28Res

theorem nonempty_equiv_G8 {K : Type} [Group K] (hK : IsCaseTwoGroup 3 K) :
    Nonempty (K ≃* G8) := by
  obtain ⟨⟨i, hi⟩, hd, ⟨e⟩⟩ := hK
  rcases hd with ⟨-, ⟨p, f, hp, hf⟩, hqp, hqe, hi1⟩ | ⟨h35, -⟩
  · subst hi1
    simp only at hqp hqe
    subst hqp hqe
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have hK : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    obtain ⟨e₂⟩ := CFSG.Quasithin.F6.L28Res.nonempty_equiv (GaloisField 2 3) hK
    exact ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hi)).trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e₂)⟩
  · omega

theorem exists_conj_of_card_nine {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 504)
    {E E' : Subgroup P} (hE : Nat.card E = 9) (hE' : Nat.card E' = 9) :
    ∃ g : P, ∀ y, y ∈ E ↔ g * y * g⁻¹ ∈ E' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ^ (Nat.card P).factorization 3 = 9 := by
    rw [hP, show (504 : ℕ) = 3 ^ 2 * 56 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (Sylow.ofCard E (h3.symm ▸ hE))
    (Sylow.ofCard E' (h3.symm ▸ hE'))
  have h := congrArg (fun Q : Sylow 3 P => (Q : Subgroup P)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h
  have hmap : E.map (MulAut.conj g).toMonoidHom = E' := by
    rw [← h]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  refine ⟨g, fun y => ?_⟩
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).symm

theorem card_sylow_three {K : Type} [Group K] [Finite K] (ε₀ : K ≃* G8) (T : Sylow 3 K) :
    Nat.card (T : Subgroup K) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card K = 504 := by rw [Nat.card_congr ε₀.toEquiv, card_G8]
  have hf : Nat.factorization (Nat.card K) 3 = 2 := by
    rw [hK, show (504 : ℕ) = 3 ^ 2 * 56 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [Sylow.card_eq_multiplicity, hf]
  norm_num

theorem l28Data_of_equiv {K : Type} [Group K] [Finite K] (ε₀ : K ≃* G8) (T : Sylow 3 K) :
    L28Data K (T : Subgroup K) := by
  have hE : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← card_sylow_three ε₀ T]
    exact (Nat.card_congr (ε₀.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_conj_of_card_nine card_G8 hE card_T0
  let ε : G8 ≃* K := (MulAut.conj g⁻¹).trans ε₀.symm
  have hεT : ∀ y, y ∈ T0 ↔ ε y ∈ (T : Subgroup K) := by
    intro y
    have h1 : ε y ∈ (T : Subgroup K) ↔ g⁻¹ * y * g ∈ (T : Subgroup K).map ε₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      rfl
    rw [h1, hg]
    rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
  exact l28Data_T0.map ε hεT

end KFactProofs.L28Local

open CFSG.Open KFactProofs.L28Local

theorem kFactCaseTwoLocalL28 : KFactCaseTwoLocalL28 := by
  rintro p K _ _ ⟨rfl, d, hd, he⟩
  have hK : IsCaseTwoGroup 3 K := ⟨d, Or.inl ⟨rfl, hd⟩, he⟩
  obtain ⟨ε₀⟩ := nonempty_equiv_G8 hK
  have hdata : ∀ T : Sylow 3 K, L28Data K (T : Subgroup K) := fun T => l28Data_of_equiv ε₀ T
  have hcard : Nat.card (MulAut K) = 1512 := by
    rw [Nat.card_congr (MulAut.congr ε₀).toEquiv]
    exact CFSG.Quasithin.F6.L28Res.card_mulAut
  have hΓ : ∀ T : Sylow 3 K,
      GLBCore 3 1 (T : Subgroup K) = Subgroup.normalizer ((T : Subgroup K) : Set K) := fun T =>
    KFactProofs.GLBCoreNormalizer.glbCore_eq_normalizer Nat.prime_three
      (by rw [(hdata T).card_eq]; norm_num) (hdata T).commute (hdata T).centralizer_le
  refine ⟨?_, fun t ht => (L28Data.isPGroup_stabilizer hdata hcard ht), fun T => ?_⟩
  · intro T _
    rw [hΓ T]
    exact ⟨fun Y hY => (hdata T).maximal hY,
      fun N hNle hNn hcop => (hdata T).eq_bot_of_normal hNle hNn hcop,
      fun f hf => (hdata T).eq_one_of_fixes_normalizer hf⟩
  · refine ⟨(hdata T).inv, (hdata T).aut, ?_⟩
    rw [hΓ T]
    exact (hdata T).isSolvable_normalizer

end CFSG.AGLEmbedding
