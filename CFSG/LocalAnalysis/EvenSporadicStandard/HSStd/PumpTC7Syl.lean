module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup

variable {G : Type*} [Group G]

theorem centralizer_conj_eq (c x : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * x * c⁻¹} : Set G) := by
  ext z
  simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    calc c * w * c⁻¹ * (c * x * c⁻¹) = c * (w * x) * c⁻¹ := by group
      _ = c * (x * w) * c⁻¹ := by rw [hw]
      _ = c * x * c⁻¹ * (c * w * c⁻¹) := by group
  · intro hz
    refine ⟨c⁻¹ * z * c, ?_, by group⟩
    calc c⁻¹ * z * c * x = c⁻¹ * (z * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * x * c⁻¹) * z) * c := by rw [hz]
      _ = x * (c⁻¹ * z * c) := by group

variable [Finite G] {p : ℕ} [hp : Fact p.Prime]

noncomputable def sylowZpowers {g : G} (hg : orderOf g = p) (h2 : ¬ p ^ 2 ∣ Nat.card G) :
    Sylow p G :=
  Sylow.ofCard (zpowers g) (by
    have hdvd : p ∣ Nat.card G := hg ▸ orderOf_dvd_natCard g
    have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card G).factorization p :=
      (hp.out.factorization_pos_of_dvd hpos hdvd)
    have h2' : (Nat.card G).factorization p < 2 := by
      by_contra hle
      exact h2 ((hp.out.pow_dvd_iff_le_factorization hpos).2 (by omega))
    rw [Nat.card_zpowers, hg, show (Nat.card G).factorization p = 1 by omega, pow_one])

theorem exists_conj_mem_zpowers {g₀ g : G} (h₀ : orderOf g₀ = p) (hg : orderOf g = p)
    (h2 : ¬ p ^ 2 ∣ Nat.card G) : ∃ c : G, c⁻¹ * g * c ∈ zpowers g₀ := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G (sylowZpowers h₀ h2) (sylowZpowers hg h2)
  refine ⟨c, ?_⟩
  have hmem : g ∈ (sylowZpowers hg h2 : Subgroup G) := mem_zpowers g
  rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hmem
  have hcoe : (sylowZpowers h₀ h2 : Subgroup G) = zpowers g₀ := rfl
  simpa [MulAut.smul_def, MulAut.conj_inv_apply, hcoe] using hmem

theorem exists_conj_mem_of_pow_eq_one {k : ℕ} {H : Subgroup G} (hH : Nat.card H = p ^ k)
    (hk : ¬ p ^ (k + 1) ∣ Nat.card G) {y : G} (hy : y ^ p = 1) : ∃ c : G, c⁻¹ * y * c ∈ H := by
  have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hdvd : p ^ k ∣ Nat.card G := hH ▸ Subgroup.card_subgroup_dvd_card H
  have h1 : k ≤ (Nat.card G).factorization p :=
    (hp.out.pow_dvd_iff_le_factorization hpos).1 hdvd
  have h2 : (Nat.card G).factorization p < k + 1 := by
    by_contra hle
    exact hk ((hp.out.pow_dvd_iff_le_factorization hpos).2 (by omega))
  let SH : Sylow p G := Sylow.ofCard H (by rw [hH]; congr 1; omega)
  have hyP : IsPGroup p (zpowers y) := by
    have hord : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy
    rcases (Nat.dvd_prime hp.out).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨Q, hQ⟩ := hyP.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G SH Q
  have hmem : y ∈ (Q : Subgroup G) := hQ (mem_zpowers y)
  rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hmem
  have hcoe : (SH : Subgroup G) = H := rfl
  exact ⟨c, by simpa [MulAut.smul_def, MulAut.conj_inv_apply, hcoe] using hmem⟩

theorem exists_conj_zpowers_eq {g₀ g : G} (h₀ : orderOf g₀ = p) (hg : orderOf g = p)
    (h2 : ¬ p ^ 2 ∣ Nat.card G) : ∃ c : G, zpowers (c⁻¹ * g * c) = zpowers g₀ := by
  obtain ⟨c, hc⟩ := exists_conj_mem_zpowers h₀ hg h2
  have hxo : orderOf (c⁻¹ * g * c) = p := by
    have h := (MulAut.conj c⁻¹).orderOf_eq g
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, hg]
  exact ⟨c, eq_of_le_of_card_ge ((zpowers_le).2 hc)
    (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo, h₀]))⟩

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
