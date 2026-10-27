module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GY1
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.GoldschmidtFour

private theorem sq_eq_one_of_mem_conjugate {Y : Type*} [Group Y] {V : Subgroup Y}
    (hV : ∀ x ∈ V, x ^ 2 = 1) (k : Y) {x : Y} (hx : x ∈ CFSG.conjugate V k) :
    x ^ 2 = 1 := by
  rw [CFSG.conjugate] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  rw [← map_pow, hV v hv, map_one]

theorem goldschmidtYoshidaCount_holds :
    ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 2 Y) (V : Subgroup Y), V ≤ P →
      CFSG.Open.IsElemAbelian 2 V →
      (∀ k : Y, CFSG.conjugate V k ≤ P → CFSG.conjugate V k = V) →
      ∀ u ∈ (P : Subgroup Y), u ∉ V → (∃ k : Y, u ∈ CFSG.conjugate V k) →
        ∃ (V₀ V₂ : Subgroup Y) (g : Y), V₀ < V₂ ∧ V₂ ≤ V ∧ V ⊓ centralizer ({u} : Set Y) ≤ V₂ ∧
          V₀ ≤ V ⊓ centralizer ({u} : Set Y) ∧
          CFSG.conjugate V₂ g ≤ P ∧ V ⊓ CFSG.conjugate V₂ g = CFSG.conjugate V₀ g ∧
          V₂.relIndex V * V₀.relIndex (V ⊓ centralizer ({u} : Set Y)) ≤
            V₀.relIndex (V ⊓ centralizer ({u} : Set Y)) *
              V₀.relIndex (V ⊓ centralizer ({u} : Set Y)) := by
  intro Y _ _ P V hVP hVe hweak u huP hu_ne_V huV
  have hV : GoldschmidtFour.Hyp P V := ⟨hVP, hVe, hweak⟩
  obtain ⟨V₀, V₂, k, g, huk, hV₀eq, hV₀₂, hV₂V, hV₂mem, hV₂g, hinter⟩ :=
    gy_construction hV huP huV
  have hVcomm : IsMulCommutative V := hVe.1
  have huN : u ∈ Subgroup.normalizer (V : Set Y) := hV.le_normalizer huP
  have hu2 : u ^ 2 = 1 := sq_eq_one_of_mem_conjugate (V := V) hVe.2 k huk
  haveI : IsMulCommutative V := hVcomm
  haveI hV'c : IsMulCommutative (CFSG.conjugate V k) := by
    rw [CFSG.conjugate]; infer_instance
  have hV₀C : V₀ ≤ V ⊓ centralizer ({u} : Set Y) := by
    intro x hx
    rw [hV₀eq, Subgroup.mem_inf] at hx
    exact ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.2
      (comm_of_mem hV'c hx.2 huk)⟩
  have hCV₂ : V ⊓ centralizer ({u} : Set Y) ≤ V₂ := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    refine (hV₂mem x).2 ⟨hx.1, ?_⟩
    have h1 : x * u * x⁻¹ * u⁻¹ = 1 := by rw [hxu]; group
    rw [h1]
    exact V₀.one_mem
  have hlt : V₀ < V₂ := by
    refine lt_of_le_of_ne hV₀₂ ?_
    intro hEq
    have hV₂le : V₂ ≤ V₀ := hEq ▸ le_rfl
    have hCeq : V ⊓ centralizer ({u} : Set Y) = V₀ := le_antisymm (hCV₂.trans hV₂le) hV₀C
    have hVle : V ≤ CFSG.conjugate V k := by
      intro e he
      have hcV : e * u * e⁻¹ * u⁻¹ ∈ V := by
        have h := commHom_mem hVcomm huN ⟨e, he⟩
        simpa [commHom_apply, commutatorElement_def] using h
      have hu_inv : u⁻¹ = u := inv_eq_of_sq hu2
      have hu_mul : u * u = 1 := by simpa [pow_two] using hu2
      have hc8 : u * (e * u * e⁻¹ * u⁻¹) * u⁻¹ = (e * u * e⁻¹ * u⁻¹)⁻¹ := by
        rw [hu_inv]
        have hL : u * (e * u * e⁻¹ * u) * u = u * e * u * e⁻¹ := by
          rw [show u * (e * u * e⁻¹ * u) * u = u * e * u * e⁻¹ * (u * u) by group,
            hu_mul, mul_one]
        have hR : (e * u * e⁻¹ * u)⁻¹ = u * e * u * e⁻¹ := by
          rw [show (e * u * e⁻¹ * u)⁻¹ = u⁻¹ * e * u⁻¹ * e⁻¹ by group, hu_inv]
        rw [hL, hR]
      have hcinv : (e * u * e⁻¹ * u⁻¹)⁻¹ = e * u * e⁻¹ * u⁻¹ :=
        inv_eq_of_sq (hVe.2 _ hcV)
      have hccomm : (e * u * e⁻¹ * u⁻¹) * u = u * (e * u * e⁻¹ * u⁻¹) := by
        conv_lhs => rw [← hc8.trans hcinv]
        group
      have hcV0 : e * u * e⁻¹ * u⁻¹ ∈ V₀ := by
        rw [← hCeq]
        exact ⟨hcV, Subgroup.mem_centralizer_singleton_iff.2 hccomm⟩
      have heV2 : e ∈ V₂ := (hV₂mem e).2 ⟨he, hcV0⟩
      have heV0 : e ∈ V₀ := hV₂le heV2
      rw [hV₀eq, Subgroup.mem_inf] at heV0
      exact heV0.2
    have hcard : Nat.card (CFSG.conjugate V k) = Nat.card V :=
      Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective
    have hVeq : V = CFSG.conjugate V k :=
      Subgroup.eq_of_le_of_card_ge hVle (le_of_eq hcard)
    exact hu_ne_V (hVeq.symm ▸ huk)
  have hindex : V₂.relIndex V ≤ V₀.relIndex (V ⊓ centralizer ({u} : Set Y)) := by
    have hsub : V₂.subgroupOf V = V₀.comap (commHom hVcomm huN) := by
      ext e
      rw [Subgroup.mem_subgroupOf, hV₂mem, Subgroup.mem_comap]
      constructor
      · rintro ⟨-, h0⟩
        simpa [commHom_apply, commutatorElement_def] using h0
      · intro he
        exact ⟨e.2, by simpa [commHom_apply, commutatorElement_def] using he⟩
    have hrange : (commHom hVcomm huN).range ≤ V ⊓ centralizer ({u} : Set Y) := by
      rintro y ⟨e, rfl⟩
      exact ⟨commHom_mem hVcomm huN e,
        Subgroup.mem_centralizer_singleton_iff.2 (commHom_mul_comm hVcomm huN hVe.2 hu2 e)⟩
    have h1 : V₂.relIndex V = (V₀.comap (commHom hVcomm huN)).index :=
      congrArg Subgroup.index hsub
    rw [h1, Subgroup.index_comap]
    exact Subgroup.relIndex_le_of_le_right hrange (relIndex_ne_zero_of_finite V₀ _)
  refine ⟨V₀, V₂, g, hlt, hV₂V, hCV₂, hV₀C, hV₂g, hinter, ?_⟩
  exact Nat.mul_le_mul_right _ hindex

end CFSG.OddStandard.SmallF3.Omega
