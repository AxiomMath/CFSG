module

public import CFSG.LocalAnalysis.AGLEmbedding.IsolatedVertex
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (KFactInnerAction KFactWeakClosure)

@[expose] def KFactWeakClosureRank2 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X),
    K.Normal → IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K →
    Subgroup.centralizer (K : Set X) = ⊥ → p ∣ Nat.card K →
    ∀ Q : Sylow p X, K ⊔ (Q : Subgroup X) = ⊤ → IsMulCommutative (Q : Subgroup X) →
      2 ≤ CFSG.Open.pRank p (Q : Subgroup X) →
      ∀ A : Subgroup X, A ≤ (Q : Subgroup X) → Nat.card A = p →
        ∃ g : X, A.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) ∧
          A.map (MulAut.conj g).toMonoidHom ≠ A

private theorem kFactRank2_Q_le_K {p : ℕ} {X : Type} [Group X] [Finite X]
    (hInn : KFactInnerAction) (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X} (hKn : K.Normal)
    (hKs : IsSimpleGroup K) (hKnab : ∃ a b : K, a * b ≠ b * a) (hKcat : IsCatalogGroup K)
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) (hpK : p ∣ Nat.card K)
    (Q : Sylow p X) (hQab : IsMulCommutative (Q : Subgroup X)) :
    (Q : Subgroup X) ≤ K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQS : CFSG.ABGLocalTools.IsSylowOf p (Q : Subgroup X) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
  have hKN : (⊤ : Subgroup X) ≤ normalizer (K : Set X) :=
    le_of_eq (Subgroup.normalizer_eq_top K).symm
  have hQK : CFSG.ABGLocalTools.IsSylowOf p ((Q : Subgroup X) ⊓ K) K :=
    hQS.inf_of_le_normalizer le_top hKN
  obtain ⟨P, hP⟩ := hQK.exists_sylow_eq_subgroupOf
  rw [Subgroup.inf_subgroupOf_right] at hP
  have hPmem : ∀ k : K, k ∈ (P : Subgroup K) ↔ (k : X) ∈ (Q : Subgroup X) := fun k => by
    rw [hP, Subgroup.mem_subgroupOf]
  have hPbot : (P : Subgroup K) ≠ ⊥ := by
    intro h
    have h1 := P.not_dvd_index
    rw [h, Subgroup.index_bot] at h1
    exact h1 hpK
  have hPab : IsMulCommutative (P : Subgroup K) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (setLike_mul_comm ((hPmem (a : K)).mp a.2) ((hPmem (b : K)).mp b.2)))
  intro q hq
  obtain ⟨n, hn⟩ : ∃ n : ℕ, q ^ (p ^ n) = 1 := by
    obtain ⟨n, hn⟩ := Q.isPGroup' ⟨q, hq⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  have hqN : q ∈ normalizer (K : Set X) := hKN (Subgroup.mem_top q)
  set φ : MulAut K := K.normalizerMonoidHom ⟨q, hqN⟩ with hφdef
  have hφ : ∀ k : K, ((φ k : K) : X) = q * (k : X) * q⁻¹ := fun _ => rfl
  have hφp : φ ^ (p ^ n) = 1 := by
    have h1 : (⟨q, hqN⟩ : normalizer (K : Set X)) ^ (p ^ n) = 1 :=
      Subtype.ext hn
    rw [hφdef, ← map_pow, h1, map_one]
  have hcomm : ∀ g ∈ (P : Subgroup K), φ * MulAut.conj g = MulAut.conj g * φ := fun g hg => by
    have hqg : q * (g : X) = (g : X) * q := setLike_mul_comm hq ((hPmem g).mp hg)
    ext m
    change q * ((g : X) * (m : X) * (g : X)⁻¹) * q⁻¹ = (g : X) * (q * (m : X) * q⁻¹) * (g : X)⁻¹
    calc q * ((g : X) * (m : X) * (g : X)⁻¹) * q⁻¹ = (q * g) * m * (q * g)⁻¹ := by group
      _ = (g * q) * m * (g * q)⁻¹ := by rw [hqg]
      _ = (g : X) * (q * m * q⁻¹) * (g : X)⁻¹ := by group
  obtain ⟨g, hgP, hg⟩ := hInn p hp hp2 K hKs hKnab hKcat P hPbot hPab φ ⟨n, hφp⟩ hcomm
  have hkey : ∀ h : X, h ∈ K → q * h * q⁻¹ = (g : X) * h * (g : X)⁻¹ := by
    intro h hh
    have hk : φ ⟨h, hh⟩ = MulAut.conj g ⟨h, hh⟩ := by rw [hg]
    have hk' := congrArg Subtype.val hk
    rw [hφ ⟨h, hh⟩] at hk'
    exact hk'
  have hx : (g : X)⁻¹ * q ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    calc h * ((g : X)⁻¹ * q) = (g : X)⁻¹ * ((g : X) * h * (g : X)⁻¹) * q := by group
      _ = (g : X)⁻¹ * (q * h * q⁻¹) * q := by rw [hkey h hh]
      _ = (g : X)⁻¹ * q * h := by group
  rw [hKc, Subgroup.mem_bot, inv_mul_eq_one] at hx
  rw [← hx]
  exact g.2

theorem kFactWeakClosureRank2_of (hInn : KFactInnerAction) (hWC : KFactWeakClosure) :
    KFactWeakClosureRank2 := by
  intro p hp hp2 X _ _ K hKn hKs hKnab hKcat hKc hpK Q _hQ hQab hrank A hAQ hA
  by_cases h2 : 2 ≤ CFSG.Open.pRank p ((Q : Subgroup X) ⊓ K)
  · exact hWC p hp hp2 X K hKn hKs hKnab hKcat hKc hpK Q _hQ hQab h2 A hAQ hA
  · exfalso
    have hQK : (Q : Subgroup X) ≤ K :=
      kFactRank2_Q_le_K hInn hp hp2 hKn hKs hKnab hKcat hKc hpK Q hQab
    rw [inf_eq_left.mpr hQK] at h2
    exact h2 hrank

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
