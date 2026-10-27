module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts4
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34MKlein
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34OuterGen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup

theorem l34OuterCentralizer_proved :
    KFactL34OuterCentralizer := by
  intro X _ _ K hKn hC hL T hTK ⟨Q, hQ⟩ y hyT hyK hy3 hcent
  have : K.Normal := hKn
  have hLT : CFSG.AGLEmbedding.IsLinThreeFour ↥K := by
    obtain ⟨q, hq2, hqe, hv, he⟩ := hL
    exact ⟨⟨.A 2 q, hv⟩, ⟨q, hq2, hqe, rfl⟩, he⟩
  have hf : ∀ k : K, (((MulAut.conjNormal y : MulAut K) k : K) : X) = y * k * y⁻¹ :=
    fun k => MulAut.conjNormal_apply y k
  have hf3 : (MulAut.conjNormal y : MulAut K) ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have hfout : (MulAut.conjNormal y : MulAut K) ∉ (MulAut.conj : K →* MulAut K).range := by
    rintro ⟨k, hk⟩
    have hz : ∀ z : K, (k : X) * z * (k : X)⁻¹ = y * z * y⁻¹ := fun z => by
      rw [← hf z, ← hk]
      rfl
    have hmem : (k : X)⁻¹ * y ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro z hz'
      have h1 : (k : X) * z * (k : X)⁻¹ = y * z * y⁻¹ := hz ⟨z, hz'⟩
      calc z * ((k : X)⁻¹ * y) = (k : X)⁻¹ * ((k : X) * z * (k : X)⁻¹) * y := by group
        _ = (k : X)⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = (k : X)⁻¹ * y * z := by group
    rw [hC, mem_bot, inv_mul_eq_one] at hmem
    exact hyK (hmem ▸ k.2)
  have hQmem : ∀ q : K, q ∈ (Q : Subgroup K) ↔ (q : X) ∈ T := by
    intro q
    rw [← hQ]
    refine ⟨fun h => Subgroup.mem_map_of_mem K.subtype h, fun h => ?_⟩
    obtain ⟨q', hq', hq'q⟩ := Subgroup.mem_map.mp h
    exact (Subtype.ext hq'q) ▸ hq'
  have hfQ : ∀ t ∈ (Q : Subgroup K), (MulAut.conjNormal y : MulAut K) t ∈ (Q : Subgroup K) := by
    intro t ht
    have h1 : y * (t : X) * y⁻¹ ∈ T := (mem_normalizer_iff.1 hyT (t : X)).1 ((hQmem t).1 ht)
    rw [hQmem, hf]
    exact h1
  have hfix : ∀ k : K, (MulAut.conjNormal y : MulAut K) k = k →
      k ∈ normalizer ((Q : Subgroup K) : Set K) := by
    intro k hk
    have hky : (k : X) ∈ centralizer ({y} : Set X) ⊓ K := by
      refine Subgroup.mem_inf.2 ⟨?_, k.2⟩
      rw [mem_centralizer_singleton_iff]
      have h1 := hf k
      rw [hk] at h1
      calc (k : X) * y = y * k * y⁻¹ * y := by rw [← h1]
        _ = y * k := by group
    have hkN := mem_normalizer_iff.1 (hcent hky)
    refine mem_normalizer_iff.2 fun q => ?_
    change q ∈ (Q : Subgroup K) ↔ k * q * k⁻¹ ∈ (Q : Subgroup K)
    rw [hQmem q, hQmem (k * q * k⁻¹)]
    exact hkN (q : X)
  have hS := CFSG.AGLEmbedding.kFactL34OuterGen ↥K hLT Q (MulAut.conjNormal y) hf3 hfout hfQ
    (normalizer ((Q : Subgroup K) : Set K)) hfix le_rfl
  obtain ⟨-, -, -, x, -, -, -, -, -, -, hxN⟩ := l34KleinOfSylow hL Q
  exact hxN (by rw [hS]; exact Subgroup.mem_top x)

end CFSG.LocalAnalysis.RankThreeTheoremC
