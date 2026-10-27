module

public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem mem_sup_centralizer_of_congr {X L : Type*} [Group X] [Group L] {KC : Subgroup X}
    [KC.Normal] (e : KC ≃* L) {x : X}
    (h : MulAut.congr e (MulAut.conjNormal x) ∈ (MulAut.conj : L →* MulAut L).range) :
    x ∈ KC ⊔ Subgroup.centralizer (KC : Set X) := by
  obtain ⟨κ, hκ⟩ := h
  set κ' : X := ((e.symm κ : KC) : X) with hκ'
  have hκ'K : κ' ∈ KC := (e.symm κ).2
  have hcen : κ'⁻¹ * x ∈ Subgroup.centralizer (KC : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have h1 := congrArg (fun f : MulAut L => e.symm (f (e ⟨k, hk⟩))) hκ
    simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, map_mul, map_inv] at h1
    have h2 : κ' * k * κ'⁻¹ = x * k * x⁻¹ := by
      have := congrArg Subtype.val h1
      simpa [hκ', MulAut.conjNormal_apply] using this
    calc k * (κ'⁻¹ * x) = κ'⁻¹ * (κ' * k * κ'⁻¹) * x := by group
      _ = κ'⁻¹ * (x * k * x⁻¹) * x := by rw [h2]
      _ = κ'⁻¹ * x * k := by group
  have : x = κ' * (κ'⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hκ'K hcen

theorem exists_pow_eq_of_map {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (O : Subgroup Y) [O.Normal] (hO : p.Coprime (Nat.card O)) {T : Subgroup Y}
    (hT : IsPGroup p T) {z : Y} (hzT : z ∈ T) {N : ℕ}
    (hN : ∀ t ∈ T.map (QuotientGroup.mk' O), t ^ N ∈ Subgroup.zpowers (QuotientGroup.mk' O z))
    (ho : ∃ o ∈ T.map (QuotientGroup.mk' O), o ^ N = QuotientGroup.mk' O z) :
    (∀ t ∈ T, t ^ N ∈ Subgroup.zpowers z) ∧ ∃ o ∈ T, o ^ N = z := by
  have hinj : ∀ a ∈ T, ∀ b ∈ T, QuotientGroup.mk' O a = QuotientGroup.mk' O b → a = b := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ T ⊓ O := ⟨T.mul_mem (T.inv_mem ha) hb, QuotientGroup.eq.mp hab⟩
    rwa [inf_eq_bot_of_isPGroup hp hT hO, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hN _ (Subgroup.mem_map_of_mem _ ht))
    rw [← map_zpow, ← map_pow] at hj
    have heq := hinj _ (T.zpow_mem hzT j) _ (T.pow_mem ht N) hj
    rw [← heq]
    exact Subgroup.zpow_mem_zpowers z j
  · obtain ⟨_, ⟨o, hoT, rfl⟩, hoz⟩ := ho
    rw [← map_pow] at hoz
    exact ⟨o, hoT, hinj _ (T.pow_mem hoT N) _ hzT hoz⟩

end CFSG.AGLEmbedding
