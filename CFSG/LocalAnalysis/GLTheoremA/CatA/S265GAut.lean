module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false

private theorem card_eq_inf_ker_mul_map {Γ Γ' : Type*} [Group Γ] [Group Γ'] (φ : Γ →* Γ')
    (S : Subgroup Γ) :
    Nat.card S = Nat.card (S ⊓ φ.ker : Subgroup Γ) * Nat.card (S.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp S.subtype)
  have hker : (φ.comp S.subtype).ker.map S.subtype = S ⊓ φ.ker := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_inf.2 ⟨s.2, hs⟩
    · intro hx
      obtain ⟨hxS, hxk⟩ := Subgroup.mem_inf.1 hx
      exact ⟨⟨x, hxS⟩, hxk, rfl⟩
  have hrange : (φ.comp S.subtype).range = S.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← h, hrange, ← hker, Subgroup.card_map_of_injective S.subtype_injective]

private theorem apply_eq_of_commute_conj_of_center {H : Type*} [Group H]
    (hZ : Subgroup.center H = ⊥) {α : MulAut H} {g : H}
    (h : α * MulAut.conj g = MulAut.conj g * α) : α g = g := by
  apply mulAut_conj_injective_of_center_eq_bot hZ
  ext y
  have hy := congrArg (fun φ : MulAut H => φ (α⁻¹ y)) h
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self] at hy
  rw [MulAut.conj_apply, MulAut.conj_apply]
  exact hy

section F4Eight

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_outHom_F4Eight (hK : Nat.card K = 2 ^ 3) :
    ∃ Θ : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod 6),
      Θ.ker = (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (by norm_num : 1 ≤ 3) K hK
  exact ⟨Θ, hker⟩

theorem exists_conj_entrywise_of_noninner (hK : Nat.card K = 2 ^ 3)
    {β : MulAut (adjointGroup .F4 K)}
    (hβ : β ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range)
    (hβ3 : orderOf β = 3) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧
      ∃ ψ : MulAut (adjointGroup .F4 K), ψ * β * ψ⁻¹ = entrywiseAdjointAut .F4 σ := by
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form (by norm_num : 1 ≤ 3) K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF β
  obtain ⟨-, -, ⟨σ, hσ⟩, hall, -⟩ :=
    even_F4_noninner_odd_prime_field_descent_and_local_core_trivial (by norm_num : 1 ≤ 3) hK
      Nat.prime_three (by norm_num) ⊤ le_top ⟨β, Subgroup.mem_top β⟩ hβ
      (by rw [← Subgroup.orderOf_coe]; exact hβ3) g k k.2 hgk
  obtain ⟨hσ3, ψ, hψ⟩ := hall σ hσ
  exact ⟨σ, hσ3, ψ, hψ⟩

theorem card_le_three_mul_card_inf_conj (hK : Nat.card K = 2 ^ 3)
    {E : Subgroup (MulAut (adjointGroup .F4 K))} (hE : IsPGroup 3 E) :
    Nat.card E ≤ 3 * Nat.card ↥(E ⊓ (MulAut.conj : adjointGroup .F4 K →*
      MulAut (adjointGroup .F4 K)).range) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Θ, hker⟩ := exists_outHom_F4Eight hK
  have h := card_eq_inf_ker_mul_map Θ E
  rw [hker] at h
  have hmap : Nat.card (E.map Θ) ≤ 3 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (hE.map Θ)
    have hdvd : Nat.card (E.map Θ) ∣ 6 := by
      have h6 := Subgroup.card_subgroup_dvd_card (E.map Θ)
      rwa [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 6) ≃ ZMod 6),
        Nat.card_zmod] at h6
    rw [hn] at hdvd ⊢
    rcases n with _ | _ | n
    · norm_num
    · norm_num
    · exfalso
      have h9 : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 (by omega : 2 ≤ n + 1 + 1)).trans hdvd
      norm_num at h9
  rw [h, mul_comm]
  exact Nat.mul_le_mul_right _ hmap

theorem commutator_le_range_conj (hK : Nat.card K = 2 ^ 3)
    (H H' : Subgroup (MulAut (adjointGroup .F4 K))) :
    ⁅H, H'⁆ ≤ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  obtain ⟨Θ, hker⟩ := exists_outHom_F4Eight hK
  rw [Subgroup.commutator_le]
  intro α _ β _
  rw [← hker, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

end F4Eight

section Center

variable
  {τ : Tag} {K : Type} [Field K] [Finite K]

theorem apply_eq_of_commute_conj {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K}
    (h : α * MulAut.conj g = MulAut.conj g * α) : α g = g :=
  apply_eq_of_commute_conj_of_center center_adjointGroup_eq_bot h

end Center

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
