module

public import CFSG.GH74.GLS.Balance.SL23Ext
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5NRankAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {Ψ : SL2F3 × SL2F3 →* G}

theorem nrQ_le_range : nrQ Ψ ≤ Ψ.range := Subgroup.map_le_range _ _

theorem nrQ_pow_four {x : G} (hx : x ∈ nrQ Ψ) : x ^ 4 = 1 := by
  obtain ⟨p, hp, rfl⟩ := (mem_nrQ Ψ).mp hx
  have h4 : p ^ 4 = 1 := Prod.ext (by simpa using hp.1) (by simpa using hp.2)
  rw [← map_pow, h4, map_one]

theorem nrQ_conj_mem {x y : G} (hx : x ∈ Ψ.range) (hy : y ∈ nrQ Ψ) : x * y * x⁻¹ ∈ nrQ Ψ := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨p', hp', rfl⟩ := (mem_nrQ Ψ).mp hy
  refine (mem_nrQ Ψ).mpr ⟨p * p' * p⁻¹, ⟨?_, ?_⟩, by simp⟩
  · simp only [Prod.fst_mul, Prod.fst_inv, conj_pow, hp'.1, mul_one, mul_inv_cancel]
  · simp only [Prod.snd_mul, Prod.snd_inv, conj_pow, hp'.2, mul_one, mul_inv_cancel]

theorem NrKer.mem_nrQ_of_two_pow (h : NrKer Ψ) {x : G} (hx : x ∈ Ψ.range) {m : ℕ}
    (hm : x ^ 2 ^ m = 1) : x ∈ nrQ Ψ := by
  obtain ⟨⟨A, B⟩, rfl⟩ := hx
  have hsq : ((A, B) : SL2F3 × SL2F3) ^ 2 ^ (m + 1) = (((A, B) : SL2F3 × SL2F3) ^ 2 ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_succ]
  have h1 : Ψ (((A, B) : SL2F3 × SL2F3) ^ 2 ^ m) = 1 := by rw [map_pow]; exact hm
  have h2 : ((A, B) : SL2F3 × SL2F3) ^ 2 ^ (m + 1) = 1 := by
    rw [hsq]
    rcases (h _).mp h1 with h3 | h3
    · rw [h3, one_pow]
    · rw [h3]
      decide +kernel
  have hA : A ^ 2 ^ (m + 1) = 1 := by simpa using congrArg Prod.fst h2
  have hB : B ^ 2 ^ (m + 1) = 1 := by simpa using congrArg Prod.snd h2
  exact (mem_nrQ Ψ).mpr ⟨(A, B), ⟨CFSG.GH74.GLS.Balance.SL23.pow_four_of_pow_two_pow hA,
    CFSG.GH74.GLS.Balance.SL23.pow_four_of_pow_two_pow hB⟩, rfl⟩

theorem NrKer.setting (h : NrKer Ψ) {E : Subgroup G} (hE : E ≤ normalizer (Ψ.range : Set G)) :
    NrSetting Ψ E where
  ker := h
  norm e he x hx := by
    have h1 : e * x * e⁻¹ ∈ Ψ.range :=
      (Subgroup.mem_normalizer_iff.mp (hE he) x).mp (nrQ_le_range hx)
    have h4 : (e * x * e⁻¹) ^ 2 ^ 2 = 1 := by
      rw [conj_pow]
      show e * x ^ 4 * e⁻¹ = 1
      rw [nrQ_pow_four hx]
      group
    exact h.mem_nrQ_of_two_pow h1 h4

theorem nrzG_comm_range {k : G} (hk : k ∈ Ψ.range) : k * nrzG Ψ = nrzG Ψ * k := by
  obtain ⟨p, rfl⟩ := hk
  rw [nrzG, ← map_mul, ← map_mul, ← nrZ_mul_comm p]

theorem NrKer.comm_of_odd (h : NrKer Ψ) {c k : G} (hc : c ∈ normalizer (Ψ.range : Set G))
    (hcQ : ∀ x ∈ nrQ Ψ, x * c = c * x) (hk : k ∈ Ψ.range) (hodd : Odd (orderOf k)) :
    c * k = k * c := by
  have hck : c * k * c⁻¹ ∈ Ψ.range := (Subgroup.mem_normalizer_iff.mp hc k).mp hk
  have hw : k⁻¹ * c * k * c⁻¹ ∈ Ψ.range := by
    have h1 : k⁻¹ * c * k * c⁻¹ = k⁻¹ * (c * k * c⁻¹) := by group
    rw [h1]
    exact mul_mem (inv_mem hk) hck
  have hcx : ∀ x ∈ nrQ Ψ, c * x * c⁻¹ = x := fun x hx => by
    calc c * x * c⁻¹ = (x * c) * c⁻¹ := by rw [hcQ x hx]
      _ = x := by group
  have hcx' : ∀ x ∈ nrQ Ψ, c⁻¹ * x * c = x := fun x hx => by
    calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
      _ = c⁻¹ * (c * x) := by rw [hcQ x hx]
      _ = x := by group
  have hwQ : ∀ x ∈ nrQ Ψ, x * (k⁻¹ * c * k * c⁻¹) = (k⁻¹ * c * k * c⁻¹) * x := fun x hx => by
    have hconj : (k⁻¹ * c * k * c⁻¹) * x * (k⁻¹ * c * k * c⁻¹)⁻¹ = x := by
      calc (k⁻¹ * c * k * c⁻¹) * x * (k⁻¹ * c * k * c⁻¹)⁻¹
          = k⁻¹ * c * (k * (c⁻¹ * x * c) * k⁻¹) * c⁻¹ * k := by group
        _ = k⁻¹ * c * (k * x * k⁻¹) * c⁻¹ * k := by rw [hcx' x hx]
        _ = k⁻¹ * (c * (k * x * k⁻¹) * c⁻¹) * k := by group
        _ = k⁻¹ * (k * x * k⁻¹) * k := by rw [hcx _ (nrQ_conj_mem hk hx)]
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  generalize hwdef : k⁻¹ * c * k * c⁻¹ = w at hw hwQ
  obtain ⟨p, hpw⟩ := hw
  have hcen := sec5nr_center p (fun p' hp' => by
    have h1 : Ψ (p * p' * p⁻¹ * p'⁻¹) = 1 := by
      have h2 := hwQ (Ψ p') (map_mem_nrQ Ψ hp')
      simp only [map_mul, map_inv]
      rw [hpw]
      calc w * Ψ p' * w⁻¹ * (Ψ p')⁻¹ = (Ψ p' * w) * w⁻¹ * (Ψ p')⁻¹ := by rw [h2]
        _ = 1 := by group
    rcases (h _).mp h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (by rw [h2, one_mul]))
  have hw1 : w = 1 ∨ w = nrzG Ψ := by
    rcases hcen with h1 | h1 | h1
    · left
      rw [← hpw, h.map_eq h1, map_one]
    · right
      rw [← hpw]
      exact h.map_eq h1
    · right
      rw [← hpw]
      exact (h.map_eq h1).trans (h.map_eq (Or.inr nrZ'_eq))
  rcases hw1 with hw1 | hw1
  · calc c * k = k * (k⁻¹ * c * k * c⁻¹) * c := by group
      _ = k * c := by rw [hwdef, hw1]; group
  · exfalso
    have hz : c * k * c⁻¹ = k * nrzG Ψ := by
      calc c * k * c⁻¹ = k * (k⁻¹ * c * k * c⁻¹) := by group
        _ = k * nrzG Ψ := by rw [hwdef, hw1]
    have hord : orderOf (k * nrzG Ψ) = orderOf k := by
      rw [← hz]
      have h1 := (MulAut.conj c).orderOf_eq k
      rwa [MulAut.conj_apply] at h1
    have hcomm : Commute k (nrzG Ψ) := nrzG_comm_range hk
    have h3 : (k * nrzG Ψ) ^ orderOf k = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one _
    obtain ⟨j, hj⟩ := hodd
    have h4 : nrzG Ψ ^ orderOf k = nrzG Ψ := by
      rw [hj, pow_succ, pow_mul, pow_two, nrzG_mul_self, one_pow, one_mul]
    rw [hcomm.mul_pow, pow_orderOf_eq_one, one_mul, h4] at h3
    exact h.nrzG_ne_one h3

theorem NrKer.comm_range (h : NrKer Ψ) {c : G} (hc : c ∈ normalizer (Ψ.range : Set G))
    (hcQ : ∀ x ∈ nrQ Ψ, x * c = c * x)
    (hgen : Ψ.range ≤ Subgroup.closure {g : G | g ∈ Ψ.range ∧ Odd (orderOf g)}) :
    ∀ x ∈ Ψ.range, x * c = c * x := by
  have hle : Subgroup.closure {g : G | g ∈ Ψ.range ∧ Odd (orderOf g)} ≤
      centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h.comm_of_odd hc hcQ hg.1 hg.2).symm
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hgen hx))

end CFSG.OddStandard.SmallF3.Omega
