module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Suz
public import Certificates.Certificate25610

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.M12Cover
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.HypOne
open CFSG.EvenSporadicStandard.HypOne.Suz

theorem centerInv_suz_rep
    {i : ℕ} (hi : i < 2) :
    ∀ z ∈ suzM, z * z = 1 → z * suzInv i = suzInv i * z →
      (∀ y ∈ suzM, y * suzInv i = suzInv i * y → z * y = y * z) → z = 1 ∨ z = suzInv i :=
  Certificates.certificate25610.1 i hi


theorem centerInv_suz :
    ∀ a ∈ suzM, orderOf a = 2 → ∀ z ∈ suzM, z * z = 1 → z * a = a * z →
      (∀ y ∈ suzM, y * a = a * y → z * y = y * z) → z = 1 ∨ z = a := by
  intro a ha ha2 z hz hzz hza hzc
  obtain ⟨r, hr, c, hc, rfl⟩ := cover_suzM a ha ha2
  have hri : ∃ i, i < 2 ∧ r = suzInv i := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  obtain ⟨i, hi, rfl⟩ := hri
  have hz' : c⁻¹ * z * c ∈ suzM := suzM.mul_mem (suzM.mul_mem (suzM.inv_mem hc) hz) hc
  have h1 := centerInv_suz_rep hi (c⁻¹ * z * c) hz'
    (by calc c⁻¹ * z * c * (c⁻¹ * z * c) = c⁻¹ * (z * z) * c := by group
          _ = 1 := by rw [hzz]; group)
    (by calc c⁻¹ * z * c * suzInv i = c⁻¹ * (z * (c * suzInv i * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * suzInv i * c⁻¹) * z) * c := by rw [hza]
          _ = suzInv i * (c⁻¹ * z * c) := by group)
    (by
      intro y hy hyr
      have hy' : c * y * c⁻¹ ∈ suzM := suzM.mul_mem (suzM.mul_mem hc hy) (suzM.inv_mem hc)
      have h2 := hzc (c * y * c⁻¹) hy' (by
        calc c * y * c⁻¹ * (c * suzInv i * c⁻¹) = c * (y * suzInv i) * c⁻¹ := by group
          _ = c * (suzInv i * y) * c⁻¹ := by rw [hyr]
          _ = c * suzInv i * c⁻¹ * (c * y * c⁻¹) := by group)
      calc c⁻¹ * z * c * y = c⁻¹ * (z * (c * y * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * y * c⁻¹) * z) * c := by rw [h2]
        _ = y * (c⁻¹ * z * c) := by group)
  rcases h1 with h1 | h1
  · left
    calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right
    calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      _ = c * suzInv i * c⁻¹ := by rw [h1]

theorem card_centralizerIn_suzM_inner
    {a : Equiv.Perm (Fin 1782)} (ha : a ∈ suzM) (ha2 : orderOf a = 2) :
    Nat.card ↥(centralizerIn suzM a) = 161280 ∨ Nat.card ↥(centralizerIn suzM a) = 3317760 := by
  obtain ⟨r, hr, c, hc, rfl⟩ := cover_suzM a ha ha2
  rw [← Nat.card_congr (centralizerInConjEquiv suzM hc r).toEquiv]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [card_centralizerIn_suzM (i := 0) (by norm_num)]
    rfl
  · right
    rw [card_centralizerIn_suzM (i := 1) (by norm_num)]
    rfl

theorem card_centralizerIn_suzM_outer
    {w : Equiv.Perm (Fin 1782)} (hw : w ∈ suzT) (hwM : w ∉ suzM) (hw2 : orderOf w = 2) :
    Nat.card ↥(centralizerIn suzM w) = 190080 ∨ Nat.card ↥(centralizerIn suzM w) = 1209600 := by
  obtain ⟨i, hi, g, hg, rfl⟩ := cover_outer hw hw2 hwM
  rw [← Nat.card_congr (centralizerInConjEquiv suzM hg (suzInv i)).toEquiv]
  rcases hi with rfl | rfl
  · left
    rw [card_centralizerIn_suzM (i := 2) (by norm_num)]
    rfl
  · right
    rw [card_centralizerIn_suzM (i := 3) (by norm_num)]
    rfl

theorem exists_commuting_rep
    {i j : ℕ} (hi : i < 2) (hj : j < 4) :
    ∃ x ∈ suzM, (x * suzInv i * x⁻¹) * suzInv j = suzInv j * (x * suzInv i * x⁻¹) :=
  Certificates.certificate25610.2 i hi j hj

end CFSG.EvenSporadicStandard.Solomon78
