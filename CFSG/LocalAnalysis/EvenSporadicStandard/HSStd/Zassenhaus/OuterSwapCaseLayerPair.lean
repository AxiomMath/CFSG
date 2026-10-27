module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerSingle
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseCatalog

public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG CFSG.LocalCores CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

section Pair

variable {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ} {τ : Γ} {K : Subgroup Γ}

theorem SwapOrbit.pair_comm (hK : SwapOrbit J τ K) (hcj : PartA.cj τ K ≠ K) :
    ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a := by
  intro a ha b hb
  have := PartA.le_centralizer_of_ne hK.comp (PartA.isComponent_cj τ hK.comp) hcj.symm
  exact (mem_centralizer_iff.1 (this ha) b hb).symm

@[expose] def diagHom (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a) :
    ↥K →* Γ where
  toFun k := (k : Γ) * (τ * k * τ⁻¹)
  map_one' := by simp
  map_mul' k k' := by
    have h1 := hcomm k' k'.2 (τ * k * τ⁻¹) (mem_cj_mk k.2)
    have e : τ * ((k : Γ) * k') * τ⁻¹ = (τ * k * τ⁻¹) * (τ * k' * τ⁻¹) := by group
    show (k : Γ) * k' * (τ * (k * k' : ↥K) * τ⁻¹) = _
    simp only [Subgroup.coe_mul]
    rw [e]
    calc (k : Γ) * k' * ((τ * k * τ⁻¹) * (τ * k' * τ⁻¹))
        = k * (k' * (τ * k * τ⁻¹)) * (τ * k' * τ⁻¹) := by group
      _ = k * ((τ * k * τ⁻¹) * k') * (τ * k' * τ⁻¹) := by rw [h1]
      _ = _ := by group

theorem diagHom_apply (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a)
    (k : ↥K) : diagHom hcomm k = (k : Γ) * (τ * k * τ⁻¹) := rfl

theorem diagHom_comm (ht2 : τ * τ = 1) (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a)
    (k : ↥K) : diagHom hcomm k * τ = τ * diagHom hcomm k := by
  rw [diagHom_apply]
  have h1 := hcomm k k.2 (τ * k * τ⁻¹) (mem_cj_mk k.2)
  have e : τ * ((k : Γ) * (τ * k * τ⁻¹)) * τ⁻¹ = (k : Γ) * (τ * k * τ⁻¹) := by
    calc τ * ((k : Γ) * (τ * k * τ⁻¹)) * τ⁻¹
        = (τ * k * τ⁻¹) * (τ * (τ * k * τ⁻¹) * τ⁻¹) := by group
      _ = (τ * k * τ⁻¹) * k := by rw [conj_conj_of_sq ht2]
      _ = _ := h1.symm
  exact (mul_inv_eq_iff_eq_mul.1 e).symm

theorem SwapOrbit.exists_diag_mul (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a) {j : Γ} (hj : j ∈ J) :
    ∃ k ∈ K, ∃ c ∈ K ⊓ PartA.cj τ K, j = k * (τ * k * τ⁻¹) * c := by
  have ht2 := hX.sq
  obtain ⟨a, ha, b, hb, rfl⟩ := PartA.exists_mul_of_mem_sup hcomm (hK.le hj)
  have hjτ : τ * (a * b) * τ⁻¹ = a * b := by
    have := hX.cent _ hj
    rw [← this]; group
  have ha' : τ * a * τ⁻¹ ∈ PartA.cj τ K := mem_cj_mk ha
  have hb0 : τ * b * τ⁻¹ ∈ K := (PartA.mem_cj ht2).1 hb
  have e1 : (τ * a * τ⁻¹) * (τ * b * τ⁻¹) = a * b := by
    calc (τ * a * τ⁻¹) * (τ * b * τ⁻¹) = τ * (a * b) * τ⁻¹ := by group
      _ = a * b := hjτ
  have e2 : (τ * b * τ⁻¹) * (τ * a * τ⁻¹) = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) :=
    hcomm _ hb0 _ ha'
  have e3 : a⁻¹ * (τ * b * τ⁻¹) = b * (τ * a * τ⁻¹)⁻¹ := by
    calc a⁻¹ * (τ * b * τ⁻¹) = a⁻¹ * ((τ * b * τ⁻¹) * (τ * a * τ⁻¹)) * (τ * a * τ⁻¹)⁻¹ := by group
      _ = a⁻¹ * (a * b) * (τ * a * τ⁻¹)⁻¹ := by rw [e2, e1]
      _ = b * (τ * a * τ⁻¹)⁻¹ := by group
  set c : Γ := a⁻¹ * (τ * b * τ⁻¹) with hc
  have hcK : c ∈ K := K.mul_mem (K.inv_mem ha) hb0
  have hcK' : c ∈ PartA.cj τ K := by
    rw [e3]
    exact (PartA.cj τ K).mul_mem hb ((PartA.cj τ K).inv_mem ha')
  have hc'K : τ * c * τ⁻¹ ∈ K := (PartA.mem_cj ht2).1 hcK'
  have hc'K' : τ * c * τ⁻¹ ∈ PartA.cj τ K := mem_cj_mk hcK
  refine ⟨a, ha, τ * c * τ⁻¹, ⟨hc'K, hc'K'⟩, ?_⟩
  have hb' : b = τ * (τ * b * τ⁻¹) * τ⁻¹ := (conj_conj_of_sq ht2 b).symm
  have hb0c : τ * b * τ⁻¹ = a * c := by rw [hc]; group
  calc a * b = a * (τ * (τ * b * τ⁻¹) * τ⁻¹) := by rw [← hb']
    _ = a * (τ * (a * c) * τ⁻¹) := by rw [hb0c]
    _ = a * (τ * a * τ⁻¹) * (τ * c * τ⁻¹) := by group

theorem SwapOrbit.range_diag_le (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a) : (diagHom hcomm).range ≤ J := by
  have hperf : ⁅(diagHom hcomm).range, (diagHom hcomm).range⁆ = (diagHom hcomm).range := by
    have hK1 : commutator ↥K = ⊤ := hK.comp.1.1.1
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hK1]
  refine hX.perfect_le (fun q hq => ?_) hperf
  obtain ⟨k, rfl⟩ := hq
  exact diagHom_comm hX.sq hcomm k

theorem SwapOrbit.le_range_diag (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a) : J ≤ (diagHom hcomm).range := by
  have hJp := hX.perfect
  conv_lhs => rw [← hJp]
  rw [Subgroup.commutator_le]
  intro j hj j' hj'
  obtain ⟨k, hk, c, hc, rfl⟩ := hK.exists_diag_mul hX hcomm hj
  obtain ⟨k', hk', c', hc', rfl⟩ := hK.exists_diag_mul hX hcomm hj'
  have hcc : ∀ c ∈ K ⊓ PartA.cj τ K, ∀ k ∈ K, Commute c (k * (τ * k * τ⁻¹)) := by
    intro c hc k hk
    have h1 : Commute c k := (hcomm k hk c hc.2).symm
    have h2 : Commute c (τ * k * τ⁻¹) := hcomm c hc.1 _ (mem_cj_mk hk)
    exact h1.mul_right h2
  have e : ⁅k * (τ * k * τ⁻¹) * c, k' * (τ * k' * τ⁻¹) * c'⁆ =
      ⁅k * (τ * k * τ⁻¹), k' * (τ * k' * τ⁻¹)⁆ :=
    PartA.comm_mul_central (hcc c hc k' hk') (hcc c' hc' k hk) (hcomm c' hc'.1 c hc.2)
  rw [e]
  refine ⟨⁅(⟨k, hk⟩ : ↥K), (⟨k', hk'⟩ : ↥K)⁆, ?_⟩
  rw [map_commutatorElement]
  rfl

theorem SwapOrbit.range_diag_eq (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a) : (diagHom hcomm).range = J :=
  le_antisymm (hK.range_diag_le hX hcomm) (hK.le_range_diag hX hcomm)

theorem SwapOrbit.ker_diag (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ PartA.cj τ K, a * b = b * a) :
    (diagHom hcomm).ker = center ↥K := by
  apply le_antisymm
  · intro k hk
    rw [MonoidHom.mem_ker, diagHom_apply] at hk
    have h1 : (k : Γ) = (τ * k * τ⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have hk' : (k : Γ) ∈ PartA.cj τ K := by
      rw [h1]
      exact (PartA.cj τ K).inv_mem (mem_cj_mk k.2)
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 k hk')
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hz1 : diagHom hcomm z ∈ J := hK.range_diag_le hX hcomm ⟨z, rfl⟩
    refine eq_one_of_comm_alt8 hX.alt8.some hz1 fun j hj => ?_
    obtain ⟨k, rfl⟩ := hK.le_range_diag hX hcomm hj
    rw [← map_mul, ← map_mul]
    congr 1
    exact mem_center_iff.1 hz k

theorem SwapOrbit.pair_quot_alt8 (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K)
    (hcj : PartA.cj τ K ≠ K) :
    Nonempty (↥K ⧸ center ↥K ≃* alternatingGroup (Fin 8)) := by
  have hcomm := hK.pair_comm hcj
  obtain ⟨e⟩ := hX.alt8
  have e1 : ↥K ⧸ center ↥K ≃* ↥(diagHom hcomm).range :=
    (QuotientGroup.quotientMulEquivOfEq (hK.ker_diag hX hcomm).symm).trans
      (QuotientGroup.quotientKerEquivRange (diagHom hcomm))
  exact ⟨(e1.trans (MulEquiv.subgroupCongr (hK.range_diag_eq hX hcomm))).trans e⟩

theorem SwapOrbit.pair_elem (hX : SwapX Γ J τ) (hK : SwapOrbit J τ K) (hcj : PartA.cj τ K ≠ K)
    (hc : KGA8CoverElem) :
    ∃ E : Subgroup Γ, E ≤ K ∧ (∀ e ∈ E, e * e = 1) ∧ 4 < Nat.card E := by
  obtain ⟨E, hE2, hE4⟩ := hc ↥K hK.comp.1 (hK.pair_quot_alt8 hX hcj)
  refine ⟨E.map K.subtype, Subgroup.map_subtype_le E, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := hE2 x hx
    exact congrArg Subtype.val this
  · rwa [Subgroup.card_map_of_injective K.subtype_injective]

end Pair

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
