module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux
public import CFSG.LocalAnalysis.AGLEmbedding.CentralComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

@[expose] def KGenTwoMod (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ E : Subgroup (MulAut K), IsElemAbelian p E → Nat.card E = p ^ 2 →
    Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k * k⁻¹ ∈ Subgroup.center K} = ⊤

theorem mem_zpowers_of_mem_center_of_card {p : ℕ} {X : Type} [Group X] [Finite X] {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} (hzK : z ∈ K)
    (hZK : Nat.card (Subgroup.center K) = p) :
    ∀ c : K, c ∈ Subgroup.center K → (c : X) ∈ Subgroup.zpowers z := by
  have hzZ : (⟨z, hzK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp hz k)
  have hle : Subgroup.zpowers (⟨z, hzK⟩ : K) ≤ Subgroup.center K :=
    Subgroup.zpowers_le.mpr hzZ
  have hcard : Nat.card (Subgroup.center K) ≤ Nat.card (Subgroup.zpowers (⟨z, hzK⟩ : K)) := by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hzp, hZK]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  intro c hc
  rw [← heq] at hc
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hc
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, by rw [← hn, Subgroup.coe_zpow]⟩

namespace ReducedNongeneration

section Gen

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem mem_of_conjNormal_mul_inv_mem (h : ReducedNongeneration p X R X₀) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} [K.Normal]
    (hZ : ∀ c : K, c ∈ Subgroup.center K → (c : X) ∈ Subgroup.zpowers z)
    {A : Subgroup X} (hAR : A ≤ R) (hA : IsElemAbelian p A) (hA3 : 3 ≤ Open.pRank p A)
    {f : X} (hfA : f ∈ A) (hf : MulAut.conjNormal (H := K) f ≠ 1) {k : K}
    (hk : MulAut.conjNormal (H := K) f k * k⁻¹ ∈ Subgroup.center K) : (k : X) ∈ X₀ := by
  have hp := h.prime
  have hfC : f ∉ Subgroup.centralizer (K : Set X) := fun hfC =>
    hf (by rwa [← MonoidHom.mem_ker, ker_conjNormal_eq_centralizer])
  have hfz : f ∉ Subgroup.zpowers z := fun hfz =>
    hfC (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hz) hfz)
  have hQR : Subgroup.zpowers z ⊔ Subgroup.zpowers f ≤ R :=
    sup_le (Subgroup.zpowers_le.mpr (mem_sylow_of_mem_center hz hzp R))
      (Subgroup.zpowers_le.mpr (hAR hfA))
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers z ⊔ Subgroup.zpowers f) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp hzp (hA.2 f hfA) hfz
      (Subgroup.mem_center_iff.mp hz f).symm (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))
  have hAQ : A ≤ Subgroup.centralizer
      ((Subgroup.zpowers z ⊔ Subgroup.zpowers f : Subgroup X) : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.center_le_centralizer _ hz))
      (Subgroup.zpowers_le.mpr (Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1 hfA))
  have hN := (normalizer_le_weakCore p hQR hQ2 (hA3.trans
    (PreuniquenessRankFour.Helpers.pRank_mono p hp ((le_inf hAR hAQ).trans le_sup_right)))).trans
    h.weakCore_le
  have hζ : f * (k : X) * f⁻¹ * (k : X)⁻¹ ∈ Subgroup.zpowers z := by
    simpa [MulAut.conjNormal_apply] using hZ _ hk
  refine hN (mem_normalizer_sup_zpowers ?_ ?_)
  · rw [Subgroup.mem_center_iff.mp hz (k : X), mul_inv_cancel_right]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  · have hkf : (k : X) * f * (k : X)⁻¹ = (f * (k : X) * f⁻¹ * (k : X)⁻¹)⁻¹ * f := by group
    rw [hkf]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hζ))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers f))

end Gen

end ReducedNongeneration

end CFSG.AGLEmbedding
