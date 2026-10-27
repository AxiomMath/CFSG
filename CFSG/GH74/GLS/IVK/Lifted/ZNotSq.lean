module

public import CFSG.GH74.GLS.IVK.Lifted.Out
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue1
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L284

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6

theorem z_not_sq_of_II4 (h44 : II4_44) (hAut : II4_Aut) (hII : II4_4_4_center)
    (hrec : Bg.B_reciprocity) : Z_not_sq := by
  intro G _ _ z S K F h hQF y hyS hyc hyR w hwy hw
  classical
  have h6 := h.toStd6r1
  have hz2 : z * z = 1 := h.z_sq
  have hz1 : z ≠ 1 := h.z_ne
  have hzK : z ∈ K := h.z_mem_K hII
  have hzR : z ∈ Rz S z := by
    rw [h.Rz_eq]
    exact mem_sup_left (h.z_mem_P hII)
  obtain ⟨c, hc⟩ := isConj_iff.1 hyc
  have hy2' : y * y = 1 := by
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hy1 : y ≠ 1 := by
    intro h1
    apply hz1
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [hc, h1]; group
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2') hy1
  have hzy : z * y = y * z := h.z_cent hyS
  have hyN : y ∈ normalizer (K : Set G) := h.S_normalizes hyS
  have hRz : Rz S z = Pz S z ⊔ F := by rw [← hQF]; rfl
  have hnfy : ¬ InducesFAut y K := by
    intro hf
    apply hyR
    rw [hRz]
    exact h.inv_fAut y hyS hy2 hf
  have hKi : IsIntrinsic z K := ⟨h.comp_isPCompIn, h.comp_pRank, hzK⟩
  have hg₀ : (c⁻¹)⁻¹ * z * c⁻¹ = y := by rw [inv_inv, hc]
  have hHi : IsIntrinsic y (cmap c K) := by
    have h1 := isIntrinsic_cj hg₀ hKi
    have e : M.cj K c⁻¹ = cmap c K := by
      ext x
      rw [M.mem_cj, mem_cmap, inv_inv]
    rwa [e] at h1
  have hzNH : z ∈ normalizer ((cmap c K : Subgroup G) : Set G) :=
    (hrec G h.simple y z hy2 h.orderOf_z hzy.symm (cmap c K) K hHi hKi).1 hyN
  have hnfz : ¬ InducesFAut z (cmap c K) := by
    intro hf
    have h1 := inducesFAut_conj c⁻¹ hf
    have e : (cmap c K).map (MulAut.conj c⁻¹).toMonoidHom = K := cmap_inv_cancel c K
    rw [e, inv_inv] at h1
    have ht2 : (c⁻¹ * z * c) * (c⁻¹ * z * c) = 1 := by
      calc (c⁻¹ * z * c) * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
        _ = 1 := by rw [hz2]; group
    have ht1 : c⁻¹ * z * c ≠ 1 := by
      intro h1
      apply hz1
      calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have htC : c⁻¹ * z * c ∈ centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : z * (c * z * c⁻¹) = (c * z * c⁻¹) * z := by rw [hc]; exact hzy
      symm
      calc z * (c⁻¹ * z * c) = c⁻¹ * ((c * z * c⁻¹) * z) * c := by group
        _ = c⁻¹ * (z * (c * z * c⁻¹)) * c := by rw [h2]
        _ = (c⁻¹ * z * c) * z := by group
    have htconj : IsConj z (c⁻¹ * z * c) := isConj_iff.2 ⟨c⁻¹, by rw [inv_inv]⟩
    have htn : c⁻¹ * z * c ∉ zStar (rigidProduct z) := by
      rw [h.rigidProduct_eq]
      intro htz
      rcases h.inv_zStarK htz ht2 with h3 | h3
      · exact ht1 h3
      · apply hyR
        have hzy' : z = y := by
          calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
            _ = c * z * c⁻¹ := by rw [h3]
            _ = y := hc
        rw [← hzy']
        exact hzR
    exact (h.classical.2 _ htC htconj htn).2.2.2.2.1 K h.comp_rigid h1
  obtain ⟨g, hg1, hg2⟩ := ((lemma_28_4 h44 hAut) G h.simple z h.orderOf_z K hKi y hy2 hyN hnfy).2
    (cmap c K) hHi hzNH hnfz
  have hzg : z = g * y * g⁻¹ := by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [hg1]
  have hyg : y = g * z * g⁻¹ := by
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hg2]
  have hw'z : g * w * g⁻¹ ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    calc z * (g * w * g⁻¹) = (g * y * g⁻¹) * (g * w * g⁻¹) := by rw [← hzg]
      _ = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hwy]
      _ = (g * w * g⁻¹) * (g * y * g⁻¹) := by group
      _ = (g * w * g⁻¹) * z := by rw [← hzg]
  have hw'sq : (g * w * g⁻¹) * (g * w * g⁻¹) = y := by
    calc (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = g * z * g⁻¹ := by rw [hw]
      _ = y := hyg.symm
  have hw'N : g * w * g⁻¹ ∈ normalizer (K : Set G) := std6r1_C_normalizes h6 hw'z
  have hQ : IsSL2Or2A7 (Hat K) := h44 G h.simple z h.orderOf_z K h.comp_isPCompIn h.comp_pRank
  have hD := ((hAut (↥K ⧸ pPrimeCore 2 ↥K) hQ).2.2 (phi K y hyN) (phi_mul_self K hyN hy2')).2
  have hninn : phi K y hyN ∉ innOf (Hat K) := by
    intro hmem
    have hin : InducesInner y K := (phi_mem_inn_iff K hyN).1 hmem
    obtain ⟨k₀, hk₀, hk⟩ := std6r1_lift_inner h6 (sq_eq_one_of_card_center hQ.2) hyS hin
    apply hyR
    rw [h.Rz_eq]
    have e : y = (y * k₀⁻¹) * k₀ := by group
    rw [e]
    exact mul_mem (mem_sup_right hk) (mem_sup_left hk₀)
  have hnfa : ¬ IsFAutomorphism (Hat K) (phi K y hyN) := fun hf => hnfy ⟨hyN, hf⟩
  refine hD hninn hnfa (phi K (g * w * g⁻¹) hw'N) ?_
  rw [← phi_mul K hw'N hw'N]
  exact phi_congr K hw'sq _ hyN

end CFSG.GH74.GLS.IVK.Lifted
