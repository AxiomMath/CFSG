module


public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeFreeGammaContainment

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem le_rankThreeGamma_of_normal_coprime {p : ℕ} (hp : p.Prime) {E X : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) (hX : X.Normal)
    (hcop : ¬ p ∣ Nat.card X) :
    X ≤ rankThreeGamma 1 p E := by
  have centralizer_le_normalizer_zpowers (e : G) :
      Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    intro x hx
    have hx' : x * e = e * x := by
      have := Subgroup.mem_centralizer_iff.1 hx e (by simp)
      exact this.symm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hc : Commute x e := hx'
    have key : ∀ k : ℤ, x * e ^ k * x⁻¹ = e ^ k := fun k => by
      rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (key k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h3 : x * y * x⁻¹ = x * e ^ k * x⁻¹ := by rw [key, ← hk]
      exact (mul_left_cancel (mul_right_cancel h3)).symm
  have one_le_pRank_zpowers {p : ℕ} (hp : p.Prime) {e : G} (he : e ≠ 1) (hep : e ^ p = 1) :
      1 ≤ CFSG.Open.pRank p (Subgroup.zpowers e) := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hord : orderOf e = p := (orderOf_eq_prime hep he)
    have hcard : Nat.card (Subgroup.zpowers e) = p ^ 1 := by
      rw [Nat.card_zpowers, hord, pow_one]
    unfold CFSG.Open.pRank
    refine le_csSup ?_ ⟨Subgroup.zpowers e, le_rfl, ⟨inferInstance, ?_⟩, hcard⟩
    · refine ⟨Nat.card (Subgroup.zpowers e), ?_⟩
      rintro k ⟨E, hEle, _, hk⟩
      have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers e) :=
        Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hEle)
      have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
      omega
    · intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hep, one_zpow]
  have normalizer_zpowers_le_gamma {p : ℕ} (hp : p.Prime) {E : Subgroup G}
      (hE : IsElemAbelian p E) {e : G} (heE : e ∈ E) (he : e ≠ 1) :
      Subgroup.normalizer (Subgroup.zpowers e : Set G) ≤ rankThreeGamma 1 p E := by
    refine le_sSup ⟨Subgroup.zpowers e, ?_, one_le_pRank_zpowers hp he (hE.2 e heE), rfl⟩
    rw [Subgroup.zpowers_le]; exact heE
  have centralizer_le_gamma {p : ℕ} (hp : p.Prime) {E : Subgroup G}
      (hE : IsElemAbelian p E) {e : G} (heE : e ∈ E) (he : e ≠ 1) :
      Subgroup.centralizer ({e} : Set G) ≤ rankThreeGamma 1 p E :=
    (centralizer_le_normalizer_zpowers e).trans (normalizer_zpowers_le_gamma hp hE heE he)
  have : Fact p.Prime := ⟨hp⟩
  have hEN : E ≤ Subgroup.normalizer (X : Set G) := fun g _ =>
    (Subgroup.mem_normalizer_iff).2 fun h => ⟨fun hh => by simpa [mul_assoc] using hX.conj_mem _ hh g,
      fun hh => by simpa [mul_assoc] using hX.conj_mem _ hh g⁻¹⟩
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    p hp E X (fun m => Subtype.ext (hE.2 m m.2)) hEcard hcop hEN
  refine hgen.le.trans (iSup_le fun e => iSup_le fun he1 => ?_)
  exact inf_le_right.trans (centralizer_le_gamma hp hE e.2 (fun h => he1 (Subtype.ext h)))

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PrimeFreeGammaContainment
