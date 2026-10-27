module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1CentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundConj
public import Certificates.Certificate27209
public import Certificates.Certificate27203
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24AutRep

public noncomputable section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Co1Cent

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.G24Aut CFSG.EvenSporadicStandard.Induction.AutBound
  CFSG.Sporadic.Co1Schreier CFSG.EvenSporadicStandard.Co1Pair
open Subgroup

section Norm

theorem triHom_sElt (j : ℕ) :
    triHom (sElt j) = wordM [permOfArr 1365 xa, permOfArr 1365 ya] (sWords.getD j []) := by
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY, sElt, map_wordM, List.map_cons, List.map_cons, List.map_nil, triHom_px']

theorem norm_sound :
    ∃ T : Subgroup PP, T ≤ twoBD ∧ Nat.card T = 4096 ∧
      ∀ j < 6, triHom (sElt j) ∈ normalizer (T : Set PP) := by
  have h := Certificates.certificate27203
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  rw [hX, hY] at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hTD, hTc, -⟩ := h
  refine ⟨_, hTD, hTc, fun j hj => mem_normalizer_of_map_le _ _ ?_⟩
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  have hc := Certificates.certificate27209 j hj i hi
  rw [← triHom_sElt] at hc
  exact hc

end Norm

section R0

theorem R0_facts :
    ∃ R0 : Subgroup C₁, R0 ≤ K₁ ∧ Nat.card R0 = 4096 ∧
      ∀ j < 6, sElt j ∈ normalizer (R0 : Set C₁) := by
  obtain ⟨T, hTD, hTc, hTn⟩ := norm_sound
  obtain ⟨hperf, hcard⟩ := K₁_facts
  have hQ := CFSG.EvenSporadicStandard.Solomon78.co1_quot2Data
  refine ⟨K₁ ⊓ T.comap triHom, inf_le_left, ?_, fun j hj => ?_⟩
  ·
    have hinj : ∀ k ∈ K₁, ∀ k' ∈ K₁, triHom k = triHom k' → k = k' := by
      intro k hk k' hk' h
      have h1 : k⁻¹ * k' ∈ K₁ := K₁.mul_mem (K₁.inv_mem hk) hk'
      have := hQ.eq_one_of_map_eq_one hperf hcard h1 (by rw [map_mul, map_inv, h, inv_mul_cancel])
      exact inv_mul_eq_one.1 this
    let f : ↥(K₁ ⊓ T.comap triHom) → ↥T := fun k => ⟨triHom (k : C₁), k.2.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro k k' h
        exact Subtype.ext (hinj _ k.2.1 _ k'.2.1 (congrArg Subtype.val h))
      · rintro ⟨t, ht⟩
        have : t ∈ K₁.map triHom := by rw [map_K₁]; exact hTD ht
        obtain ⟨k, hk, hkt⟩ := this
        exact ⟨⟨k, Subgroup.mem_inf.2 ⟨hk, Subgroup.mem_comap.2 (by rw [hkt]; exact ht)⟩⟩,
          Subtype.ext hkt⟩
    rw [Nat.card_congr (Equiv.ofBijective f hf), hTc]
  ·
    have hs : sElt j ∈ K₁ := sElt_mem_K₁ j
    have hπ := hTn j hj
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, map_mul, map_inv]
    constructor
    · rintro ⟨hh, hT⟩
      exact ⟨K₁.mul_mem (K₁.mul_mem hs hh) (K₁.inv_mem hs),
        (Subgroup.mem_normalizer_iff.1 hπ _).1 hT⟩
    · rintro ⟨hh, hT⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.1 hπ _).2 hT⟩
      have := K₁.mul_mem (K₁.mul_mem (K₁.inv_mem hs) hh) hs
      simpa [mul_assoc] using this

end R0

end CFSG.EvenSporadicStandard.Co1Cent
