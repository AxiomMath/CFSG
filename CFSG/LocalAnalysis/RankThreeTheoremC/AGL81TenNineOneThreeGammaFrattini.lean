module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

theorem exists_conj_le_of_card_full {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q E : Subgroup G} (hQ : Nat.card Q = p ^ (Nat.card G).factorization p)
    (hE : IsPGroup p E) : ∃ g : G, ∀ e ∈ E, g⁻¹ * e * g ∈ Q := by
  let S0 : Sylow p G := Sylow.ofCard Q hQ
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S0 S
  refine ⟨g, fun e he => ?_⟩
  have hmem : e ∈ ((g • S0 : Sylow p G) : Subgroup G) := by
    rw [hg]
    exact hS he
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv] at hmem
  exact hmem

variable {H B : Type*} [Group H] [Finite H] [Group B] {p : ℕ} [Fact p.Prime]

theorem card_inf_comap_of_sylow (π : H →* B) {Q : Subgroup H}
    (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) {R : Subgroup B} (hR : R ≤ Q.map π) :
    Nat.card (Q ⊓ R.comap π : Subgroup H) =
      p ^ (Nat.card (R.comap π : Subgroup H)).factorization p := by
  have hp := (Fact.out : p.Prime)
  set Rs := R.comap π with hRs
  set R₂ := Q ⊓ Rs with hR₂
  set N := π.ker with hN
  have hNRs : N ≤ Rs := fun x hx => by
    show π x ∈ R
    rw [MonoidHom.mem_ker.mp hx]
    exact R.one_mem
  have hsup : R₂ ⊔ N = Rs := by
    refine le_antisymm (sup_le inf_le_right hNRs) (fun x hx => ?_)
    obtain ⟨q, hq, hqx⟩ := hR hx
    have hk : q⁻¹ * x ∈ N := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqx, inv_mul_cancel]
    have hqRs : q ∈ Rs := by
      show π q ∈ R
      rw [hqx]
      exact hx
    have : x = q * (q⁻¹ * x) := by group
    rw [this]
    exact mul_mem (mem_sup_left ⟨hq, hqRs⟩) (mem_sup_right hk)
  have hinf : N ⊓ R₂ = N ⊓ Q := by
    rw [hR₂, inf_left_comm, inf_eq_left.mpr hNRs, inf_comm]
  have hNQ := CFSG.Quasithin.card_inf_normal_of_sylow Q N hQ
  have hr1 := Subgroup.relIndex_mul_card (H := N) (K := R₂)
  have hr2 : N.relIndex (R₂ ⊔ N) = N.relIndex R₂ := Subgroup.relIndex_sup_right R₂ N
  have hr3 := Subgroup.relIndex_mul_card (H := N) (K := R₂ ⊔ N)
  rw [inf_eq_left.2 le_sup_right, hr2, hsup] at hr3
  rw [hinf, hNQ] at hr1
  have hR₂p : IsPGroup p R₂ := (IsPGroup.of_card hQ).to_le inf_le_left
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).1 hR₂p
  have hrd : N.relIndex R₂ ∣ p ^ e := ⟨_, by rw [← he, ← hr1]⟩
  obtain ⟨j, -, hrj⟩ := (Nat.dvd_prime_pow hp).1 hrd
  have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hRsfac : (Nat.card Rs).factorization p = j + (Nat.card N).factorization p := by
    rw [← hr3, hrj, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hNpos, Finsupp.add_apply,
      hp.factorization_pow, Finsupp.single_eq_same]
  rw [← hr1, hrj, ← pow_add, hRsfac]

theorem exists_mul_of_map_mem_normalizer (π : H →* B) {Q : Subgroup H}
    (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) {R : Subgroup B} (hR : R ≤ Q.map π)
    {h : H} (hh : π h ∈ normalizer (R : Set B)) :
    ∃ r ∈ R.comap π, ∃ n ∈ normalizer ((Q ⊓ R.comap π : Subgroup H) : Set H), h = r * n := by
  classical
  set Rs := R.comap π with hRs
  set R₂ := Q ⊓ Rs with hR₂
  have hR₂Rs : R₂ ≤ Rs := inf_le_right
  have hhRs : ∀ x ∈ Rs, h * x * h⁻¹ ∈ Rs := by
    intro x hx
    show π (h * x * h⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hh (π x)).mp hx
  have hcard := card_inf_comap_of_sylow π hQ hR
  set S₁ : Subgroup Rs := R₂.subgroupOf Rs with hS₁
  have hS₁c : Nat.card S₁ = p ^ (Nat.card Rs).factorization p := by
    rw [hS₁, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₂Rs).toEquiv, hcard]
  set E : Subgroup Rs :=
    (R₂.map (MulAut.conj h).toMonoidHom).subgroupOf Rs with hE
  have hEp : IsPGroup p E := by
    have hR₂p : IsPGroup p R₂ := (IsPGroup.of_card hQ).to_le inf_le_left
    exact (hR₂p.map _).comap_of_injective Rs.subtype Rs.subtype_injective
  obtain ⟨g, hg⟩ := exists_conj_le_of_card_full hS₁c hEp
  refine ⟨(g : H), g.2, (g : H)⁻¹ * h, ?_, by group⟩
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  have hxRs : h * x * h⁻¹ ∈ Rs := hhRs x (hR₂Rs hx)
  have hmem : (⟨h * x * h⁻¹, hxRs⟩ : Rs) ∈ E :=
    Subgroup.mem_subgroupOf.mpr ⟨x, hx, by simp⟩
  have h1 := hg _ hmem
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : ((g⁻¹ * ⟨h * x * h⁻¹, hxRs⟩ * g : Rs) : H) =
      (g : H)⁻¹ * h * x * ((g : H)⁻¹ * h)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h2] at h1
  exact h1

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
