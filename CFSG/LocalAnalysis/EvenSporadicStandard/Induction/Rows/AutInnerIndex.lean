module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.Induction.AutInner

open Subgroup
open scoped commutatorElement

@[expose] def innerAut (K : Type*) [Group K] : Subgroup (MulAut K) :=
  (MulAut.conj : K →* MulAut K).range

section Aut

variable {K : Type*} [Group K]

theorem ker_conj_eq_center (K : Type*) [Group K] :
    (MulAut.conj : K →* MulAut K).ker = center K := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro h x
    have h' := congrArg (fun α : MulAut K => α x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h'
    calc x * g = g * x * g⁻¹ * g := by rw [h']
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]
    group

theorem card_innerAut (K : Type*) [Group K] :
    Nat.card (innerAut K) = Nat.card (K ⧸ center K) := by
  rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq (ker_conj_eq_center K)).toEquiv]
  exact (Nat.card_congr
    (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).toEquiv).symm

theorem commutator_mul_central {d d' z z' : K} (hz : z ∈ center K) (hz' : z' ∈ center K) :
    ⁅d * z, d' * z'⁆ = ⁅d, d'⁆ := by
  have h1 : Commute z (d' * z') := (mem_center_iff.1 hz _).symm
  have h2 : Commute d z' := mem_center_iff.1 hz' _
  rw [commutatorElement_mul_left_eq_conj_mul, h1.commutator_eq,
    commutatorElement_mul_right_eq_mul_conj, h2.commutator_eq]
  simp

theorem eq_of_forall_mem_center (hK : commutator K = ⊤) (φ ψ : K →* K)
    (h : ∀ g, (φ g)⁻¹ * ψ g ∈ center K) : φ = ψ := by
  have hle : commutator K ≤ MonoidHom.eqLocus φ ψ := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨g, g', rfl⟩
    have hg := h g
    have hg' := h g'
    have e1 : ψ g = φ g * ((φ g)⁻¹ * ψ g) := by group
    have e2 : ψ g' = φ g' * ((φ g')⁻¹ * ψ g') := by group
    show φ ⁅g, g'⁆ = ψ ⁅g, g'⁆
    rw [map_commutatorElement, map_commutatorElement, e1, e2, commutator_mul_central hg hg']
  rw [hK] at hle
  ext g
  exact hle (mem_top g)

noncomputable def autQuotHom (K : Type*) [Group K] : MulAut K →* MulAut (K ⧸ center K) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | H x => simp
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on with | H x => simp

theorem autQuotHom_mk (φ : MulAut K) (x : K) :
    autQuotHom K φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk _ _ _ (Subgroup.map_center_eq φ) x

theorem autQuotHom_injective (hK : commutator K = ⊤) : Function.Injective (autQuotHom K) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have h : ∀ g, (g : K)⁻¹ * φ g ∈ center K := by
    intro g
    have h1 := DFunLike.congr_fun hφ (QuotientGroup.mk g)
    rw [autQuotHom_mk, MulAut.one_apply] at h1
    exact QuotientGroup.eq.1 h1.symm
  have h2 := eq_of_forall_mem_center hK (MonoidHom.id K) φ.toMonoidHom h
  ext g
  exact (DFunLike.congr_fun h2 g).symm

theorem index_innerAut_le_two [Finite K] (hK : commutator K = ⊤) {Q : Type*} [Group Q]
    (e : K ⧸ center K ≃* Q) (hQ : center Q = ⊥) (hout : (innerAut Q).index ≤ 2) :
    (innerAut K).index ≤ 2 := by
  have : Finite Q := Finite.of_equiv _ e.toEquiv
  have h1 : Nat.card (MulAut K) ≤ Nat.card (MulAut (K ⧸ center K)) :=
    Nat.card_le_card_of_injective _ (autQuotHom_injective hK)
  have h2 : Nat.card (MulAut (K ⧸ center K)) = Nat.card (MulAut Q) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have h3 : Nat.card (innerAut Q) * (innerAut Q).index = Nat.card (MulAut Q) :=
    Subgroup.card_mul_index _
  have h4 : Nat.card (innerAut Q) = Nat.card Q := by
    rw [card_innerAut Q]
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hQ).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := Q)).toEquiv
  have h5 : Nat.card Q = Nat.card (K ⧸ center K) := (Nat.card_congr e.toEquiv).symm
  have h6 : Nat.card (innerAut K) = Nat.card (K ⧸ center K) := card_innerAut K
  have h7 : Nat.card (innerAut K) * (innerAut K).index = Nat.card (MulAut K) :=
    Subgroup.card_mul_index _
  have hpos : 0 < Nat.card (innerAut K) := Nat.card_pos
  have h8 : Nat.card (innerAut Q) * (innerAut Q).index ≤ Nat.card (innerAut Q) * 2 :=
    Nat.mul_le_mul_left _ hout
  have h9 : Nat.card (innerAut K) * (innerAut K).index ≤ Nat.card (innerAut K) * 2 := by
    calc Nat.card (innerAut K) * (innerAut K).index = Nat.card (MulAut K) := h7
      _ ≤ Nat.card (MulAut (K ⧸ center K)) := h1
      _ = Nat.card (MulAut Q) := h2
      _ = Nat.card (innerAut Q) * (innerAut Q).index := h3.symm
      _ ≤ Nat.card (innerAut Q) * 2 := h8
      _ = Nat.card (innerAut K) * 2 := by rw [h4, h5, h6]
  exact Nat.le_of_mul_le_mul_left h9 hpos

theorem index_innerAut_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (innerAut Y).index = (innerAut X).index := by
  have h1 : (innerAut X).map (MulAut.congr e).toMonoidHom = innerAut Y := by
    ext α
    constructor
    · rintro ⟨β, ⟨x, rfl⟩, rfl⟩
      refine ⟨e x, ?_⟩
      ext y
      simp [MulAut.conj_apply]
    · rintro ⟨y, rfl⟩
      refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
      ext z
      simp [MulAut.conj_apply]
  have h2 : ((innerAut X).map (MulAut.congr e).toMonoidHom).index = (innerAut X).index :=
    Subgroup.index_map_of_bijective (MulAut.congr e).bijective _
  rw [← h1]
  exact h2

end Aut

theorem index_comap_innerAut_le_two {K : Type*} [Group K] [Finite K]
    (hidx : (innerAut K).index ≤ 2) {G : Type*} [Group G] (φ : G →* MulAut K) :
    ((innerAut K).comap φ).index ≤ 2 := by
  have : Finite (MulAut K) := Finite.of_injective (fun α : MulAut K => (α : K → K))
    (fun a b h => MulEquiv.ext (fun x => congrFun h x))
  rw [Subgroup.index_comap]
  calc (innerAut K).relIndex φ.range ≤ (innerAut K).relIndex ⊤ :=
        Subgroup.relIndex_le_of_le_right le_top (by
          rw [Subgroup.relIndex_top_right]
          exact Subgroup.index_ne_zero_of_finite)
    _ = (innerAut K).index := Subgroup.relIndex_top_right _
    _ ≤ 2 := hidx

end CFSG.EvenSporadicStandard.Induction.AutInner
