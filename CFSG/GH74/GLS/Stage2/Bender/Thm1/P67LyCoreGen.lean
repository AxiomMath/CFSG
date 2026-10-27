module

public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore

open Subgroup CFSG

theorem eq_bot_of_normal_coprime {M : Type} [Group M] [Finite M] (hM : IsQuasisimple M)
    {r : ℕ} [Fact r.Prime] (hZ : IsPGroup r (center M)) (hZr : r ∣ Nat.card (center M))
    {W : Subgroup M} (hW : ∀ c : M, ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hcop : Nat.Coprime (Nat.card W) r) : W = ⊥ := by
  classical
  have hWn : W.Normal := ⟨fun w hw c => hW c w hw⟩
  obtain ⟨hperf, hsimple, -⟩ := hM
  have hmapn : (W.map (QuotientGroup.mk' (center M))).Normal :=
    Subgroup.Normal.map hWn _ (QuotientGroup.mk'_surjective _)
  have := hmapn
  rcases hsimple.eq_bot_or_eq_top_of_normal (W.map (QuotientGroup.mk' (center M))) with h | h
  ·
    have hle : W ≤ center M := by
      intro w hw
      have : QuotientGroup.mk' (center M) w ∈ W.map (QuotientGroup.mk' (center M)) :=
        Subgroup.mem_map_of_mem _ hw
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff w).mp this
    have hd : Nat.card W ∣ Nat.card (center M) := Subgroup.card_dvd_of_le hle
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hZ
    rw [hn] at hd
    have hd' : Nat.card W ∣ r ^ n := hd
    have : Nat.card W = 1 := by
      have h1 : Nat.Coprime (Nat.card W) (r ^ n) := hcop.pow_right n
      exact Nat.Coprime.eq_one_of_dvd h1 hd'
    exact Subgroup.card_eq_one.mp this
  ·
    exfalso
    have hmk : ∀ x : M, ∃ z ∈ center M, (QuotientGroup.mk x : M ⧸ W) = QuotientGroup.mk z := by
      intro x
      have hx : QuotientGroup.mk' (center M) x ∈ W.map (QuotientGroup.mk' (center M)) := by
        rw [h]; trivial
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
      have hz : w⁻¹ * x ∈ center M := by
        rw [← QuotientGroup.eq_one_iff (N := center M), QuotientGroup.mk_mul,
          QuotientGroup.mk_inv]
        have : (QuotientGroup.mk w : M ⧸ center M) = QuotientGroup.mk x := hwx
        rw [this, inv_mul_cancel]
      refine ⟨w⁻¹ * x, hz, ?_⟩
      rw [QuotientGroup.eq]
      have := hW x⁻¹ w⁻¹ (W.inv_mem hw)
      simpa [mul_assoc] using this
    let _ : CommGroup (M ⧸ W) :=
      { (inferInstance : Group (M ⧸ W)) with
        mul_comm := fun a b => by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
          obtain ⟨z₁, hz₁, e₁⟩ := hmk x
          obtain ⟨z₂, hz₂, e₂⟩ := hmk y
          rw [e₁, e₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            Subgroup.mem_center_iff.mp hz₁ z₂] }
    have hcomm : commutator M ≤ W := by
      have := Abelianization.commutator_subset_ker (QuotientGroup.mk' W)
      rwa [QuotientGroup.ker_mk'] at this
    have hWM : W = ⊤ := by
      rw [eq_top_iff]
      rw [hperf.commutator_eq_top] at hcomm
      exact hcomm
    rw [hWM] at hcop
    have : r ∣ Nat.card (⊤ : Subgroup M) := by
      rw [Subgroup.card_top]
      exact hZr.trans (Subgroup.card_subgroup_dvd_card _)
    have h2 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hcop) this
    exact (Fact.out : r.Prime).one_lt.ne' h2

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyCore
