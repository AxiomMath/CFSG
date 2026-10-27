module

public import CFSG.LocalAnalysis.OddStandard.GH71.L102
public import CFSG.LocalAnalysis.OddStandard.GH71.Transitivity
public import CFSG.LocalAnalysis.OddStandard.GH71.Constrained

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_cen (g z : G) :
    (Cen z).map (MulAut.conj g).toMonoidHom = Cen (g * z * g⁻¹) := by
  ext x
  rw [mem_map_conj, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * (g * z * g⁻¹) = g * (g⁻¹ * x * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
      _ = g * z * g⁻¹ * x := by group
  · intro hx
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

section Ly


theorem false_of_unbalanced (h : Ctx71 G z S U u) (hB : AlternatingBalanceData 11)
    (hB0 : SpecB0) (hB1 : SpecB1) (hB2 : SpecB2) (hB2' : SpecB2') (hB3 : SpecB3)
    (hB4 : SpecB4) (hB5 : SpecB5) (h812 : IVK_8_12_ly)
    (hD : ¬ pPrimeCoreOf 2 (Cen z) ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u)) : False := by
  have hSO : S ≤ normalizer (pPrimeCoreOf 2 (Cen z) : Set G) :=
    h.S_le.trans (le_normalizer_pPrimeCoreOf' _)
  obtain ⟨P₁, hP₁, -, hSP₁⟩ := Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_two
    Nat.prime_three h.S2 (not_two_dvd_of_odd (odd_card_pPrimeCoreOf' _)) hSO bot_le
    IsPGroup.of_bot (by rw [normalizer_eq_top]; exact le_top)
  have hP₁u : ¬ P₁ ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u) := h.not_le_of_unbalanced hB hD hP₁ hSP₁
  have hP₁1 : P₁ ≠ ⊥ := fun hb => hP₁u (by rw [hb, bot_inf_eq]; exact bot_le)
  have hP₁S : ¬ S ≤ centralizer (P₁ : Set G) := fun hS =>
    h.not_T₂_le_centralizer hB hB1 hB2' hB3 hD hP₁ hSP₁
      (inf_le_left.trans (hS.trans (centralizer_le inf_le_left)))
  obtain ⟨P, K, hP, hP₁P, hPK, hK, hKcov⟩ := h.lemma_10_2 hB0 hB1 hB4 hB5 h812 hP₁ hSP₁ hP₁1 hP₁S
  have hP₁uV : P₁ ⊓ Cen u ≤ P ⊓ centralizer (U : Set G) := le_inf (inf_le_left.trans hP₁P)
    (by rw [h.centralizer_U]; exact inf_le_inf_right _ (hP₁.1.trans (pPrimeCoreOf_le' _)))
  have hV1 : P ⊓ centralizer (U : Set G) ≠ ⊥ := fun hb => hP₁u ((hb ▸ hP₁uV).trans bot_le)
  have hV3 : IsPGroup 3 ↥(P ⊓ centralizer (U : Set G)) := hP.2.1.to_le inf_le_left
  have hSV : S ≤ normalizer ((P ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := fun s hs =>
    inf_normalizer_le_normalizer_inf
      ⟨hP.2.2.1 hs, normalizer_le_normalizer_centralizer U (h.U_norm hs)⟩
  have hVO : P ⊓ centralizer (U : Set G) ≤ pPrimeCoreOf 2 (normalizer (U : Set G)) := by
    rw [h.pPrimeCoreOf_normalizer_U]
    exact h.le_pPrimeCoreOf_centralizer_U hB1 hB2 inf_le_right hV3 hSV
  have hSON : S ≤ normalizer (pPrimeCoreOf 2 (normalizer (U : Set G)) : Set G) :=
    h.U_norm.trans (le_normalizer_pPrimeCoreOf' _)
  obtain ⟨Q₁, hQ₁, hVQ₁, hSQ₁⟩ := Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_two Nat.prime_three h.S2 (not_two_dvd_of_odd (odd_card_pPrimeCoreOf' _)) hSON hVO
    hV3 hSV
  have hQ₁1 : Q₁ ≠ ⊥ := fun hb => hV1 (le_bot_iff.mp (hb ▸ hVQ₁))
  obtain ⟨Q, hQ, hQ₁Q, hQcov⟩ := h.lemma_10_3 hB0 hB1 hB2 h812 hQ₁ hSQ₁ hQ₁1
  have hPQ : P ⊓ Q ≠ ⊥ := fun hb =>
    hV1 (le_bot_iff.mp (hb ▸ le_inf inf_le_left (hVQ₁.trans hQ₁Q)))
  obtain ⟨c, hcS, hQc⟩ := transitivity h812 h.ctx hP hQ hPQ
  have hcz : c⁻¹ * z * c = z := by
    rw [mul_assoc, mem_centralizer_iff.mp hcS z h.ctx.z_mem]; group
  have hcu : c * u * c⁻¹ = u := by
    rw [(mem_centralizer_iff.mp hcS u h.u_S).symm]; group
  obtain ⟨k, hkQ, hkz⟩ := h.exists_conj_of_covers_N hQcov
  have hk'P : c * k * c⁻¹ ∈ normalizer (P : Set G) := by
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 : c⁻¹ * x * c ∈ Q := by
      rw [hQc, mem_conjugate_iff]
      have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
      rw [e]; exact hx
    have h2 := (mem_normalizer_iff.mp hkQ _).mp h1
    rw [hQc, mem_conjugate_iff] at h2
    have e : c * k * c⁻¹ * x * (c * k * c⁻¹)⁻¹ = c * (k * (c⁻¹ * x * c) * k⁻¹) * c⁻¹ := by group
    rw [e]; exact h2
  have hk'z : c * k * c⁻¹ * z * (c * k * c⁻¹)⁻¹ = u := by
    calc c * k * c⁻¹ * z * (c * k * c⁻¹)⁻¹ = c * (k * (c⁻¹ * z * c) * k⁻¹) * c⁻¹ := by group
      _ = u := by rw [hcz, hkz, hcu]
  have hk'K : c * k * c⁻¹ ∈ K := hPK hk'P
  have hSK : S ≤ K := hP.2.2.1.trans hPK
  have hbarK := h.hbar_of_covers hB1 h812 hK hSK hKcov
  have hP₁K : P₁ ≤ pPrimeCoreOf 2 K :=
    (le_inf hP₁.1 (hP₁P.trans (le_normalizer.trans hPK))).trans (h.inf_pPrimeCoreOf_le hSK hbarK)
  have hcovu : Covers K (Cen u) (pPrimeCoreOf 2 (Cen u)) := by
    have h1 := covers_map_conj (c * k * c⁻¹) hKcov
    have e1 : K.map (MulAut.conj (c * k * c⁻¹)).toMonoidHom = K :=
      map_conj_eq_of_mem_normalizer (le_normalizer hk'K)
    have e2 : (Cen z).map (MulAut.conj (c * k * c⁻¹)).toMonoidHom = Cen u := by
      rw [map_conj_cen, hk'z]
    have e3 : (pPrimeCoreOf 2 (Cen z)).map (MulAut.conj (c * k * c⁻¹)).toMonoidHom =
        pPrimeCoreOf 2 (Cen u) := by
      rw [← e2]; exact (CoreAux.oddCoreOf_map_equiv (MulAut.conj (c * k * c⁻¹)) (Cen z)).symm
    rwa [e1, e2, e3] at h1
  have hOKu : pPrimeCoreOf 2 K ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u) :=
    le_pPrimeCoreOf_of_covers hcovu inf_le_right
      (odd_card_of_le inf_le_left (odd_card_pPrimeCoreOf' K))
      (fun y hy => inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pPrimeCoreOf' K hy.1, le_normalizer hy.2⟩)
  exact hP₁u ((inf_le_inf_right _ hP₁K).trans hOKu)

end Ly


theorem oddCore_eq_bot_of_ivk (h : Ctx71 G z S U u) (hD' : CoverSylowData 11)
    (hB : AlternatingBalanceData 11) (hspec : AhatSpecAll) (h812 : IVK_8_12_ly) :
    pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨hB0, hB1, hB2, hB2', hB3, hB4, hB5⟩ := hspec
  by_cases hD : pPrimeCoreOf 2 (Cen z) ⊓ Cen u ≤ pPrimeCoreOf 2 (Cen u)
  · exact h.oddCore_eq_bot_of_pair hD' hB hD
  · exact (h.false_of_unbalanced hB hB0 hB1 hB2 hB2' hB3 hB4 hB5 h812 hD).elim

end Ctx71


theorem oddCore_eq_bot_of_stage2_of_ivk (hspec : AhatSpecAll) (h812 : IVK_8_12_ly)
    (hD' : CoverSylowData 11) (hB : AlternatingBalanceData 11) {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.ly S) (hcov : IsDoubleCoverOfAlt (CentralizerBar z) 11) :
    pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨U, u, h⟩ := exists_ctx71 hctx hcov
  exact h.oddCore_eq_bot_of_ivk hD' hB hspec h812

end CFSG.OddStandard.GH71
