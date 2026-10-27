module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus2

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem conj_mem_commutator_of_mem_normalizer {G : Type*} [Group G] {S : Subgroup G} {g u : G}
    (hg : g ∈ normalizer (S : Set G)) (hu : u ∈ ⁅S, S⁆) : g * u * g⁻¹ ∈ ⁅S, S⁆ := by
  have h1 : conjugate ⁅S, S⁆ g = ⁅S, S⁆ := by
    change (⁅S, S⁆).map (MulAut.conj g⁻¹).toMonoidHom = ⁅S, S⁆
    rw [map_commutator]
    change ⁅conjugate S g, conjugate S g⁆ = ⁅S, S⁆
    rw [conjugate_eq_of_mem_normalizer hg]
  rw [← h1] at hu
  exact (mem_conjugate_iff.mp hu)

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable (d : Data H₁)

theorem z_mul_self : d.z * d.z = 1 := by rw [← pow_two, ← d.z_ord, pow_orderOf_eq_one]

theorem z_comm_a : d.z * h.a = h.a * d.z :=
  (mem_centralizer_iff.mp d.z_S h.a h.toHyp52.a_mem_S).symm

theorem z_ne_one : d.z ≠ 1 := fun h1 => by
  have := d.z_ord
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem z_ne_a : d.z ≠ h.a := by
  intro h1
  have := (h.toHyp52.D_inf_P_eq_bot H₁.center_J) ▸ mem_inf.mpr ⟨h1 ▸ d.z_D, h.toHyp52.a_mem_P⟩
  exact d.z_ne_one (h1 ▸ mem_bot.mp this)

theorem inv_SS_cases {u : H} (hu : u ∈ ⁅h.S, h.S⁆) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    u = h.a ∨ u = d.z ∨ u = h.a * d.z := by
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hcl := d.SS_inv u hu hord
  rcases Six.mem_closure_pair_cases d.z_mul_self (Six.a_mul_a_self h.toHyp52) d.z_comm_a.symm
    hcl with h1 | h1 | h1 | h1
  · exact absurd h1 hu1
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h1
  · exact Or.inr (Or.inr (h1.trans d.z_comm_a))

theorem exists_v (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCF1 : CFSec8Simple)
    (hCF2 : CFSec8InnerCentralizer) (hC : CFL2C) (F : d.Facts) :
    ∃ v : H, v ∈ normalizer (h.S : Set H) ∧ v⁻¹ * h.a * v = d.z ∧ v⁻¹ * d.z * v = h.a ∧
      v * v ∈ h.S ∧ IsPGroup 2 (zpowers v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := d.exists_conj_a_z hB1 hB6 hCF23 hCF24 hCFc hCF1 hCF2 F
  have hSz : h.S ≤ centralizer ({d.z} : Set H) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp d.z_S w hw)
  obtain ⟨n, hnN, hn⟩ := Seven.exists_normalizer_conj_of_sylow H₁.isSylowIn_S hSz hc
  have haSS := d.a_mem_commutator
  have hnz : n⁻¹ * d.z * n = h.a := by
    have hmem : n⁻¹ * d.z * n ∈ ⁅h.S, h.S⁆ := by
      rw [← hn, show n⁻¹ * (n⁻¹ * h.a * n) * n = n⁻¹ * (n⁻¹ * h.a * n⁻¹⁻¹) * n⁻¹⁻¹ by group]
      exact conj_mem_commutator_of_mem_normalizer (inv_mem hnN)
        (conj_mem_commutator_of_mem_normalizer (inv_mem hnN) haSS)
    have h2 : n⁻¹ * d.z * n * (n⁻¹ * d.z * n) = 1 := by
      rw [show n⁻¹ * d.z * n * (n⁻¹ * d.z * n) = n⁻¹ * (d.z * d.z) * n by group, d.z_mul_self]
      group
    have h1 : n⁻¹ * d.z * n ≠ 1 := fun h1 => d.z_ne_one (by
      calc d.z = n * (n⁻¹ * d.z * n) * n⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    rcases d.inv_SS_cases hmem h2 h1 with h3 | h3 | h3
    · exact h3
    · exfalso
      apply d.z_ne_a
      calc d.z = n * (n⁻¹ * d.z * n) * n⁻¹ := by group
        _ = n * d.z * n⁻¹ := by rw [h3]
        _ = n * (n⁻¹ * h.a * n) * n⁻¹ := by rw [hn]
        _ = h.a := by group
    · exfalso
      apply d.not_conj_a_az hC F (n * n)
      rw [show (n * n)⁻¹ * h.a * (n * n) = n⁻¹ * (n⁻¹ * h.a * n) * n by group, hn, h3]
  have hpar : ∀ i : ℕ, (n ^ (2 * i))⁻¹ * h.a * n ^ (2 * i) = h.a ∧
      (n ^ (2 * i + 1))⁻¹ * h.a * n ^ (2 * i + 1) = d.z := by
    intro i
    induction i with
    | zero => exact ⟨by simp, by simpa using hn⟩
    | succ i ih =>
      have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
      refine ⟨?_, ?_⟩
      · rw [e1, pow_succ, mul_inv_rev, show n⁻¹ * (n ^ (2 * i + 1))⁻¹ * h.a * (n ^ (2 * i + 1) *
          n) = n⁻¹ * ((n ^ (2 * i + 1))⁻¹ * h.a * n ^ (2 * i + 1)) * n by group, ih.2, hnz]
      · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring, pow_succ, pow_succ, mul_inv_rev,
          mul_inv_rev, show n⁻¹ * (n⁻¹ * (n ^ (2 * i + 1))⁻¹) * h.a * (n ^ (2 * i + 1) * n * n) =
          n⁻¹ * (n⁻¹ * ((n ^ (2 * i + 1))⁻¹ * h.a * n ^ (2 * i + 1)) * n) * n by group, ih.2,
          hnz, hn]
  obtain ⟨e, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  obtain ⟨i, rfl⟩ := hm
  set v := n ^ (2 * i + 1) with hv
  have hva : v⁻¹ * h.a * v = d.z := (hpar i).2
  have hvz : v⁻¹ * d.z * v = h.a := by
    rw [← (hpar i).2, show v⁻¹ * (v⁻¹ * h.a * v) * v = (v * v)⁻¹ * h.a * (v * v) by group,
      hv, ← pow_add, show 2 * i + 1 + (2 * i + 1) = 2 * (2 * i + 1) by ring]
    exact (hpar (2 * i + 1)).1
  have hvN : v ∈ normalizer (h.S : Set H) := pow_mem hnN _
  have hv2 : IsPGroup 2 (zpowers v) := by
    have h1 : v ^ 2 ^ e = 1 := by
      rw [hv, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    exact IsPGroup.of_card (by
      rw [Nat.card_zpowers]
      exact (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1) |>.choose_spec.2)
  refine ⟨v, hvN, hva, hvz, ?_, hv2⟩
  have hvva : (v * v)⁻¹ * h.a * (v * v) = h.a := by
    rw [show (v * v)⁻¹ * h.a * (v * v) = v⁻¹ * (v⁻¹ * h.a * v) * v by group, hva, hvz]
  have hvvC : v * v ∈ centralizer ({h.a} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    calc v * v * h.a = v * v * ((v * v)⁻¹ * h.a * (v * v)) := by rw [hvva]
      _ = h.a * (v * v) := by group
  have hvv2 : IsPGroup 2 (zpowers (v * v)) := hv2.to_le (zpowers_le.mpr (mul_mem (mem_zpowers v)
    (mem_zpowers v)))
  have hR : IsPGroup 2 ↥(h.S ⊔ zpowers (v * v)) :=
    IsPGroup.to_sup_of_normal_left' h.toHyp52.isPGroup_S hvv2
      (zpowers_le.mpr (mul_mem hvN hvN))
  have hRC : h.S ⊔ zpowers (v * v) ≤ centralizer ({h.a} : Set H) :=
    sup_le H₁.isSylowIn_S.1 (zpowers_le.mpr hvvC)
  have heq := eq_of_sylow_of_le H₁.isSylowIn_S.2 le_sup_left hRC hR
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
