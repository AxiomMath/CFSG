module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44SimpleAct
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44

open Subgroup MulAction

theorem simple_no_index_eleven {M V : Type*} [Group M] [Mul V] [MulAction M V]
    (hmul : ∀ (m : M) (u u' : V), m • (u * u') = (m • u) * (m • u'))
    (W : Subgroup M) [W.Normal] (hW : W.index = 11) (hM : Nat.card M = 443520)
    {x y : V} (hA22 : (orbit M x).ncard = 22) (hB231 : (orbit M y).ncard = 231)
    (hprod : ∀ u ∈ orbit M x, ∀ u' ∈ orbit M x, u ≠ u' → u * u' ∈ orbit M y) : False := by
  classical
  have hWcard : Nat.card W = 40320 := by
    have h := Subgroup.card_mul_index W
    rw [hW, hM] at h
    omega
  have hS : Nat.card (stabilizer M x) * 22 = 443520 := by
    have h := simple_card_stabilizer_mul_ncard_orbit (G := M) x
    rwa [hA22, hM] at h
  have hSW : stabilizer M x ≤ W := by
    have hdvd : (W ⊔ stabilizer M x).index ∣ 11 := by
      have h := Subgroup.index_dvd_of_le (le_sup_left : W ≤ W ⊔ stabilizer M x)
      rwa [hW] at h
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h11
    · exfalso
      have htop : W ⊔ stabilizer M x = ⊤ := Subgroup.index_eq_one.mp h1
      have hsub : orbit M x ⊆ orbit W x := by
        rintro _ ⟨m, rfl⟩
        have hm : (m : M) ∈ W ⊔ stabilizer M x := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨w, hw, s, hs, hws⟩ := Subgroup.mem_sup_of_normal_left.mp hm
        refine ⟨⟨w, hw⟩, ?_⟩
        show w • x = (m : M) • x
        rw [← hws, mul_smul, mem_stabilizer_iff.mp hs]
      have heq : orbit W x = orbit M x := by
        refine Set.Subset.antisymm (fun z hz => ?_) hsub
        obtain ⟨w, hw⟩ := hz
        exact ⟨(w : M), hw⟩
      have h22 := simple_card_stabilizer_mul_ncard_orbit (G := W) x
      rw [heq, hA22, hWcard] at h22
      omega
    · have h := Subgroup.relIndex_mul_index (le_sup_left : W ≤ W ⊔ stabilizer M x)
      rw [h11, hW] at h
      have h1 : W.relIndex (W ⊔ stabilizer M x) = 1 := by omega
      rw [Subgroup.relIndex_eq_one] at h1
      exact le_sup_right.trans h1
  have hStabW : Nat.card (stabilizer W x) = Nat.card (stabilizer M x) := by
    rw [← stabilizer_subgroupOf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSW).toEquiv
  have hW2 : (orbit W x).ncard = 2 := by
    have h := simple_card_stabilizer_mul_ncard_orbit (G := W) x
    rw [hStabW, hWcard] at h
    have h20160 : Nat.card (stabilizer M x) = 20160 := by omega
    rw [h20160] at h
    omega
  obtain ⟨p, q, hpq, hpqeq⟩ := Set.ncard_eq_two.mp hW2
  obtain ⟨b, hbx, hWb⟩ : ∃ b, b ≠ x ∧ orbit W x = {x, b} := by
    have hxmem : x ∈ orbit W x := mem_orbit_self x
    rw [hpqeq] at hxmem
    rcases hxmem with h | h
    · exact ⟨q, fun hqx => hpq (h.symm.trans hqx.symm), by rw [hpqeq, h]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨p, fun hpx => hpq (hpx.trans h), by rw [hpqeq, h, Set.pair_comm]⟩
  have hbW : b ∈ orbit W x := by rw [hWb]; exact Set.mem_insert_of_mem _ rfl
  have hxA : x ∈ orbit M x := mem_orbit_self x
  have hbA : b ∈ orbit M x := by
    obtain ⟨w, hw⟩ := hbW
    exact ⟨(w : M), hw⟩
  have hfix : ∀ s ∈ stabilizer M x, s • b = b := by
    intro s hs
    have hsW : s ∈ W := hSW hs
    have hsx : s • x = x := mem_stabilizer_iff.mp hs
    have hmem : s • b ∈ orbit W x := by
      obtain ⟨w, hw⟩ := hbW
      refine ⟨⟨s, hsW⟩ * w, ?_⟩
      show ((s : M) * (w : M)) • x = s • b
      rw [mul_smul]
      exact congrArg (s • ·) hw
    rw [hWb] at hmem
    rcases hmem with h | h
    · exact absurd (MulAction.injective s (h.trans hsx.symm)) hbx
    · exact h
  have hp : x * b ∈ orbit M y := hprod x hxA b hbA hbx.symm
  have hstab : stabilizer M x ≤ stabilizer M (x * b) := by
    intro s hs
    rw [mem_stabilizer_iff, hmul, mem_stabilizer_iff.mp hs, hfix s hs]
  have horb : orbit M (x * b) = orbit M y := orbit_eq_iff.mpr hp
  have hcard := simple_card_stabilizer_mul_ncard_orbit (G := M) (x * b)
  rw [horb, hB231, hM] at hcard
  have hle : Nat.card (stabilizer M x) ≤ Nat.card (stabilizer M (x * b)) :=
    Nat.le_of_dvd (by omega) (Subgroup.card_dvd_of_le hstab)
  omega

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44
