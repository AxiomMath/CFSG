module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterModelOf

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.BenderSuzuki.MatrixGroups

variable {L : Type} [Group L] [Finite L]

theorem center_eq_bot_of_mulEquiv_sz {a : ℕ} (ha : 1 ≤ a) (e : L ≃* Sz a) : center L = ⊥ := by
  have : IsSimpleGroup L :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inr (Or.inr ⟨a, ha, ⟨e⟩⟩))
  have hq : 2 ≤ 2 ^ (2 * a + 1) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ 2 * a + 1 by omega))
  exact center_eq_bot_of_fusionBenderBorel (fusionBenderBorel_of_mulEquiv_sz ha e) hq le_rfl

theorem center_eq_bot_of_mulEquiv_psu3 {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3 2 f) :
    center L = ⊥ := by
  have : IsSimpleGroup L :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩))
  have hq : 2 ≤ 2 ^ f :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 1 ≤ f by omega))
  exact center_eq_bot_of_fusionBenderBorel (fusionBenderBorel_of_mulEquiv_psu3 hf e) hq
    (by norm_num)

theorem apply_eq_of_mulEquiv_sz {a : ℕ} (ha : 1 ≤ a) (e : L ≃* Sz a) (P : Sylow 2 L)
    (φ : MulAut L) (hφ2 : φ * φ = 1) (hφP : ∀ x ∈ (P : Subgroup L), φ x ∈ (P : Subgroup L))
    {z : L} (hz : z ∈ centralizer ((P : Subgroup L) : Set L)) : φ z = z := by
  obtain ⟨b, rfl⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover.exists_eq_conj_of_suzuki ha e φ hφ2
  have hb2 : b * b = 1 := by
    have h1 : MulAut.conj (b * b) = 1 := by rw [map_mul, hφ2]
    have h2 : b * b ∈ center L := mem_center_iff.mpr fun g => by
      have h3 : b * b * g * (b * b)⁻¹ = g := by
        simpa only [MulAut.conj_apply, MulAut.one_apply] using DFunLike.congr_fun h1 g
      calc g * (b * b) = b * b * g * (b * b)⁻¹ * (b * b) := by rw [h3]
        _ = b * b * g := by group
    rw [center_eq_bot_of_mulEquiv_sz ha e] at h2
    exact h2
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hbN : b ∈ normalizer ((P : Subgroup L) : Set L) := mem_normalizer_iff.mpr fun h =>
    ⟨fun hh => by simpa only [MulAut.conj_apply] using hφP h hh, fun hh => by
      have h4 := hφP _ hh
      rw [MulAut.conj_apply, hbinv,
        show b * (b * h * b) * b = b * b * h * (b * b) by group, hb2, one_mul, mul_one] at h4
      exact h4⟩
  have hp : IsPGroup 2 (zpowers b) := by
    have hb2' : b ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two, hb2]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hb2')
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hbP : b ∈ (P : Subgroup L) := by
    have hmem : b ∈ zpowers b ⊓ (P : Subgroup L) := by
      rw [← hp.inf_normalizer_sylow P]
      exact ⟨mem_zpowers b, hbN⟩
    exact hmem.2
  rw [MulAut.conj_apply, Subgroup.mem_centralizer_iff.mp hz b hbP, mul_inv_cancel_right]

theorem apply_eq_of_mulEquiv_psu3 {f : ℕ} (hf : 2 ≤ f) (e : L ≃* PSU3 2 f) (P : Sylow 2 L)
    (φ : MulAut L) (hφ2 : φ * φ = 1) (hφP : ∀ x ∈ (P : Subgroup L), φ x ∈ (P : Subgroup L))
    {z : L} (hzP : z ∈ (P : Subgroup L)) (hz : z ∈ centralizer ((P : Subgroup L) : Set L)) :
    φ z = z := by
  obtain ⟨K, _, _, _, J, hJ, hKcard, hfixed, ⟨e'⟩⟩ :=
    exists_mulEquiv_hermitian_of_mulEquiv_psu3 hf e
  have hPφ : (P : Subgroup L).map φ.toMonoidHom = P := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hφP x hx
    · rw [Subgroup.card_map_of_injective φ.injective]
  have hφ2' : φ ^ 2 ∈ (P : Subgroup L).map MulAut.conj :=
    ⟨1, one_mem _, by rw [map_one, pow_two, hφ2]⟩
  exact CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.fix_omega J hf hKcard hfixed hJ e' P φ
    hPφ hφ2' hzP
    (sq_eq_one_of_fusionBenderBorel (fusionBenderBorel_of_mulEquiv_psu3 hf e) P hzP hz)

end CFSG.ComponentClassification.Asc76X
