module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoConj
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Transport
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Sp4
public import CFSG.GH74.Generic.Context
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp

public section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem pPrimeCore_Lsub [Finite K] (h4 : 4 ≤ Nat.card K) : CFSG.pPrimeCore 2 (Lsub K) = ⊥ := by
  have := isSimpleGroup_Lsub (K := K) h4
  rcases (CFSG.pPrimeCore_normal (p := 2) (G := Lsub K)).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hcop := CFSG.pPrimeCore_coprime_card (p := 2) (G := Lsub K)
    rw [h, Subgroup.card_top] at hcop
    have hdvd : 2 ∣ Nat.card (Lsub K) := by
      have := orderOf_dvd_natCard (⟨w0 K, w0_mem_Lsub⟩ : Lsub K)
      rwa [Subgroup.orderOf_mk, orderOf_w0] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop hdvd

theorem exists_model_conj [Finite K] (hodd : Odd (Nat.card K)) {u : StatedProj (StatedSp 2 K)}
    (hu : orderOf u = 2) :
    ∃ φ : StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 K), φ u = u1 K ∨ φ u = u2 K := by
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd hu
  refine ⟨MulAut.conj g⁻¹, ?_⟩
  simp only [MulAut.conj_apply, inv_inv]
  exact hg

theorem pPrimeCore_eq_bot_P [Finite K] (hodd : Odd (Nat.card K))
    {u : StatedProj (StatedSp 2 K)} (hu : orderOf u = 2) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX : M ≤ centralizer {u}) (hM : CFSG.IsPComponent 2 (M.subgroupOf (centralizer {u}))) :
    CFSG.pPrimeCore 2 M = ⊥ := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd hu
  apply pPrimeCore_eq_bot_of_map 2 φ
  have hM' := isPComponent_map_subgroupOf 2 φ hMX hM
  have hMX' := Subgroup.map_mono (f := φ.toMonoidHom) hMX
  rw [map_centralizer_singleton] at hM' hMX'
  rcases hφ with h | h <;> rw [h] at hM' hMX'
  · obtain ⟨hE | hE, h5⟩ := pComponent_centralizer_u1 hodd hMX' hM'
    · rw [hE]
      exact pPrimeCore_E1 h2 (by omega)
    · rw [hE]
      exact pPrimeCore_E2 h2 (by omega)
  · obtain ⟨hL, h5⟩ := pComponent_centralizer_u2 hodd hMX' hM'
    rw [hL]
    exact pPrimeCore_Lsub (by omega)

theorem exists_involution_conj_P [Finite K] (hodd : Odd (Nat.card K))
    (hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K))
    {u : StatedProj (StatedSp 2 K)} (hu : orderOf u = 2) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX : M ≤ centralizer {u}) (hM : CFSG.IsPComponent 2 (M.subgroupOf (centralizer {u})))
    {w : StatedProj (StatedSp 2 K)} (hw : w ∈ M) (hwo : orderOf w = 2) :
    ∃ r : StatedProj (StatedSp 2 K), r * r = 1 ∧ r⁻¹ * u * r = w := by
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨φ, hφ⟩ := exists_model_conj hodd hu
  have hM' := isPComponent_map_subgroupOf 2 φ hMX hM
  have hMX' := Subgroup.map_mono (f := φ.toMonoidHom) hMX
  rw [map_centralizer_singleton] at hM' hMX'
  have hw' : φ w ∈ M.map φ.toMonoidHom := mem_map_of_mem _ hw
  have hwo' : orderOf (φ w) = 2 := by rw [MulEquiv.orderOf_eq, hwo]
  suffices h : ∃ r', r' * r' = 1 ∧ r'⁻¹ * φ u * r' = φ w by
    obtain ⟨r', hr', hr'u⟩ := h
    refine ⟨φ.symm r', ?_, ?_⟩
    · rw [← map_mul, hr', map_one]
    · apply φ.injective
      rw [map_mul, map_mul, map_inv, φ.apply_symm_apply, hr'u]
  rcases hφ with h | h <;> rw [h] at hM' hMX' ⊢
  · refine ⟨1, mul_one 1, ?_⟩
    rw [inv_one, one_mul, mul_one]
    obtain ⟨hE | hE, -⟩ := pComponent_centralizer_u1 hodd hMX' hM' <;> rw [hE] at hw'
    · exact (eq_u1_of_mem_E1 h2 hw' hwo').symm
    · exact (eq_u1_of_mem_E2 h2 hw' hwo').symm
  · obtain ⟨hL, -⟩ := pComponent_centralizer_u2 hodd hMX' hM'
    rw [hL] at hw'
    exact exists_involution_conj_u2 hodd hpp hw' hwo'

theorem odd_card_of_card_eq {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Finite K]
    (hK : Nat.card K = p ^ f) : Odd (Nat.card K) := by
  rw [hK]
  exact (hp.odd_of_ne_two hp2).pow

theorem cfSp4Comp : GSThmB.CFSp4Comp := by
  intro Y _ _ p f hp hp2 hf hY t ht M hMt hM
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hodd := odd_card_of_card_eq hp hp2 hK
  apply pPrimeCore_eq_bot_of_map 2 e
  have hM' := isPComponent_map_subgroupOf 2 e hMt hM
  have hMX' := Subgroup.map_mono (f := e.toMonoidHom) hMt
  rw [map_centralizer_singleton] at hM' hMX'
  exact pPrimeCore_eq_bot_P hodd (by rw [MulEquiv.orderOf_eq, ht]) hMX' hM'

theorem cfSp4Conj : GSThmB.CFSp4Conj := by
  intro Y _ _ p f hp hp2 hf hY t w ht hw M hMt hM hwM
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hY
  have hodd := odd_card_of_card_eq hp hp2 hK
  have hpp : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩
  have hM' := isPComponent_map_subgroupOf 2 e hMt hM
  have hMX' := Subgroup.map_mono (f := e.toMonoidHom) hMt
  rw [map_centralizer_singleton] at hM' hMX'
  obtain ⟨r', hr', hr'u⟩ := exists_involution_conj_P hodd hpp (by rw [MulEquiv.orderOf_eq, ht])
    hMX' hM' (mem_map_of_mem _ hwM) (by
      change orderOf (e w) = 2
      rw [MulEquiv.orderOf_eq, hw])
  refine ⟨e.symm r', ?_, ?_⟩
  · rw [← map_mul, hr', map_one]
  · apply e.injective
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact hr'u

end CFSG.ComponentClassification.CatFactsSp4
