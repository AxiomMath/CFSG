module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Embed
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Struct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv

theorem a7_quotient_structure {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [hKn : K.Normal]
    (hK : (3 : ℕ).Coprime (Nat.card K))
    (hKmax : ∀ N : Subgroup Y, N.Normal → (3 : ℕ).Coprime (Nat.card N) → N ≤ K)
    (h3 : CFSG.pCore 3 (Y ⧸ K) = ⊥)
    (hrk : ∀ E : Subgroup Y, CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9)
    {J : Subgroup (Y ⧸ K)} (hJ : CFSG.IsComponent J)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7))
    {Dy Vy : Subgroup Y} (hD9 : Nat.card Dy = 9) (hD3 : IsPGroup 3 Dy)
    (hV : rankTwoMaximalInvariantTwoSubgroup Dy Vy) :
    Nat.card Vy = 4 * Nat.card (Vy ⊓ K : Subgroup Y) ∧ ∃ m ∈ normalizer (Dy : Set Y),
      3 ∣ Nat.card (Vy ⊔ Vy.map (MulAut.conj m).toMonoidHom : Subgroup Y) := by
  classical
  have hfact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : Y →* Y ⧸ K := QuotientGroup.mk' K with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hker : π.ker = K := QuotientGroup.ker_mk' K
  have hkerc : (3 : ℕ).Coprime (Nat.card π.ker) := by rw [hker]; exact hK
  have h3' : CFSG.pPrimeCore 3 (Y ⧸ K) = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    intro N hN hNc
    have hNt : (N.comap π).Normal := hN.comap π
    have hcop : (3 : ℕ).Coprime (Nat.card (N.comap π)) := by
      rw [card_comap_eq_card_ker_mul π hπs N]
      exact hkerc.mul_right hNc
    have hle : N.comap π ≤ K := hKmax _ hNt hcop
    rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective hπs N]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff x).mpr (hle hx)
  have hrk' : ∀ E : Subgroup (Y ⧸ K), CFSG.Open.IsElemAbelian 3 E → Nat.card E ≤ 9 := by
    intro E hE
    obtain ⟨E', hE', hcard⟩ := exists_isElemAbelian_card_eq_of_map Nat.prime_three π hπs hkerc hE
    rw [← hcard]
    exact hrk E' hE'
  obtain ⟨ι, hι, hA7⟩ := exists_injective_hom_perm_seven h3 h3' hrk' hJ e
  have hinfD : Dy ⊓ π.ker = ⊥ := inf_eq_bot_of_isPGroup_of_coprime Nat.prime_three hD3 hkerc
  have hDbar9 : Nat.card (Dy.map π) = 9 := by
    have := card_eq_card_map_mul_card_inf_ker π Dy
    rw [hinfD, Subgroup.card_bot, mul_one, hD9] at this
    exact this.symm
  have hVbar := rankTwoMaximalInvariantTwoSubgroup_map_of_ker Nat.prime_three (by norm_num) π hπs
    hkerc hD3 hV
  obtain ⟨hV4, nbar, hnbar, hjoin⟩ := a7_structure_of_embedding hι hA7 hDbar9 hVbar
  refine ⟨?_, ?_⟩
  · have := card_eq_card_map_mul_card_inf_ker π Vy
    rw [hV4, hker] at this
    exact this
  · obtain ⟨m, hm, d, hd, hmd⟩ :=
      exists_mem_normalizer_map_eq_mul Nat.prime_three π hπs hkerc hD3 hnbar
    refine ⟨m, hm, ?_⟩
    have hdN : d ∈ normalizer ((Vy.map π : Subgroup (Y ⧸ K)) : Set (Y ⧸ K)) := hVbar.2.1 hd
    have hVm : (Vy.map π).map (MulAut.conj (π m)).toMonoidHom =
        (Vy.map π).map (MulAut.conj nbar).toMonoidHom := by
      ext x
      rw [mem_map_conj_iff_implicit, mem_map_conj_iff_implicit, hmd]
      have h1 := mem_normalizer_iff.mp (inv_mem hdN) (nbar⁻¹ * x * nbar)
      rw [h1]
      have : (nbar * d)⁻¹ * x * (nbar * d) = d⁻¹ * (nbar⁻¹ * x * nbar) * d⁻¹⁻¹ := by group
      rw [this]
    have hmap : (Vy ⊔ Vy.map (MulAut.conj m).toMonoidHom : Subgroup Y).map π =
        (Vy.map π) ⊔ (Vy.map π).map (MulAut.conj (π m)).toMonoidHom := by
      rw [Subgroup.map_sup, Subgroup.map_map]
      have : π.comp (MulAut.conj m).toMonoidHom = (MulAut.conj (π m)).toMonoidHom.comp π := by
        ext x
        simp [MulAut.conj_apply]
      rw [this, ← Subgroup.map_map]
    have hdvd := Subgroup.card_map_dvd (Vy ⊔ Vy.map (MulAut.conj m).toMonoidHom : Subgroup Y) π
    rw [hmap, hVm] at hdvd
    exact hjoin.trans hdvd

end CFSG.LocalAnalysis.RankThreeTheoremC
