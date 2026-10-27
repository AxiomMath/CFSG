module

public import CFSG.GH74.GLS.Stage2.Final.ModelLayer
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerTransport

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup
open CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

variable {F : Type} [Field F]

theorem layerBar_transport {Gs : Type} [Group Gs] [Finite Gs] [Finite F] (M : ModelData F)
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn0 : n ≠ 0) (hneven : 2 ∣ n)
    (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1)
    (hdet : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    (hdvd : n ∣ Nat.card F - 1) (hodd : Odd (Nsub M).index) (hqs : CFSG.IsQuasisimple ↥M.H2)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥M.H2)) (hev : 2 ∣ Nat.card ↥M.H2) {a b : F}
    (hab : a ^ 2 + b ^ 2 = -1) (hH : ∀ g, rhoQ hab g ∈ M.H2)
    (Φ : Gs ≃* PG M) (S' : Sylow 2 Gs) (z' : Gs) (hΦ : Φ z' = yP M)
    (hc : CenterIs (S' : Subgroup Gs) z') :
    layerTimesSylow z' (S' : Subgroup Gs) ⊓ OddCore z' = ⊥ ∧
      barOf z' (layerTimesSylow z' (S' : Subgroup Gs)) = oPrimeResidual 2 (CentralizerBar z') := by
  apply CFSG.GH74.GLS.Stage2.Final.ModelLT.layerBarAt_of_equiv Φ z' (S' : Subgroup Gs)
  rw [hΦ]
  have hSC : ((sylowMap Φ S' : Sylow 2 (PG M)) : Subgroup (PG M)) ≤ Cg M := by
    rw [coe_sylowMap]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hs' := ((hc z').2 (Subgroup.mem_zpowers z')).2 s hs
    rw [← hΦ]
    show Φ s * Φ z' = Φ z' * Φ s
    rw [← map_mul, ← map_mul, hs']
  have key := layerBar_family M h2 hn0 hneven hU2 hdet hdvd hodd hqs hZ hev hab hH (sylowMap Φ S') hSC
  rw [coe_sylowMap] at key
  exact key

end CFSG.GH74.GLS.Stage2.Final.ModelBlock

namespace CFSG.GH74.GLS.Stage2.Final

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final.ModelBlock

theorem modelLayerBar : ModelLayerBar := by
  intro Gs _ _ p f S' z' hGs hLU hz'ord hz'c
  obtain ⟨hp, hp2, hq3, -⟩ := hGs
  have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq5 : 5 ≤ p ^ f := by obtain ⟨k, hk⟩ := hqodd; omega
  rcases hLU with hL | hU
  · obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psl_unpack hL
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF
    obtain ⟨a, b, hab⟩ := (CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices
      (ringChar_ne_two_of_two_ne_zero h2)).1
    have hH := rhoQ_mem_H2_lin hab
    obtain ⟨S₁, hS₁⟩ := exists_sylow_center_of_quat (ModelData.lin F) h2
      (ModelOrd.odd_index_lin F h2) hab hH
    obtain ⟨Φ, hΦ⟩ := exists_equiv_of_center (show Gs ≃* PG (ModelData.lin F) from e) S₁ (yP _)
      (orderOf_yP _ h2) ((centerIs_iff _ _).1 hS₁) S' z' hz'ord hz'c
    have h5 : 5 ≤ Nat.card F := by rw [hF]; exact hq5
    have hev : 2 ∣ p ^ f - 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k, by omega⟩
    exact layerBar_transport (ModelData.lin F) h2 (n := p ^ f - 1) (by omega) hev
      (fun l => ⟨fun _ => by
        have h := pow_card_eq_one' (G := Fˣ) (x := l)
        rwa [Nat.card_units, hF] at h, fun _ => Subgroup.mem_top _⟩)
      (fun a _ => by
        have h := det_lin_pow a
        rwa [hF] at h)
      (by rw [hF]) (odd_index_Nsub _ h2 (ModelOrd.odd_index_lin F h2))
      (ModelH2.h2_quasisimple_lin F h5) (ModelH2.h2_center_two_lin F) (ModelH2.h2_even_lin F h2)
      hab hH Φ S' z' hΦ ((centerIs_iff _ _).1 hz'c)
  · obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := lieModel_psu_unpack hU
    have : Fact p.Prime := ⟨hp⟩
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    have : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := 2 * f) (by rw [← Nat.card_eq_fintype_card]; exact hF')
    have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hp hp2 hF'
    obtain ⟨a, b, hab, hH⟩ := exists_rhoQ_uni hF hp2
    obtain ⟨S₁, hS₁⟩ := exists_sylow_center_of_quat (ModelData.uni hF) h2
      (ModelOrd.odd_index_uni hF hp2) hab hH
    obtain ⟨Φ, hΦ⟩ := exists_equiv_of_center (show Gs ≃* PG (ModelData.uni hF) from e) S₁ (yP _)
      (orderOf_yP _ h2) ((centerIs_iff _ _).1 hS₁) S' z' hz'ord hz'c
    have hev : 2 ∣ p ^ f + 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k + 1, by omega⟩
    have hdvd : p ^ f + 1 ∣ Nat.card F - 1 := by
      rw [hF]
      obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
      rw [hk]
      refine ⟨k, ?_⟩
      apply Nat.sub_eq_of_eq_add
      ring
    exact layerBar_transport (ModelData.uni hF) h2 (n := p ^ f + 1) (by omega) hev
      (sc2_mem_uni_iff hF) (fun a ha => det_uni_pow hF ha) hdvd
      (odd_index_Nsub _ h2 (ModelOrd.odd_index_uni hF hp2))
      (ModelH2.h2_quasisimple_uni hF hq5) (ModelH2.h2_center_two_uni hF)
      (ModelH2.h2_even_uni hF hp2) hab hH Φ S' z' hΦ ((centerIs_iff _ _).1 hz'c)

end CFSG.GH74.GLS.Stage2.Final
