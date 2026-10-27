module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Glue
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaPlus4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaPSU

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {T : Type} [Group T]

@[expose] def OddCoreExp (α : MulAut T) (k : ℕ) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ y ∈ oddCoreIn B α, y ^ k = 1

theorem OddCoreExp.of_core [Finite T] (hZ : center T = ⊥) {α : MulAut T} (h : BurgCoreFor α)
    (k : ℕ) : OddCoreExp α k := by
  intro B hB y hy
  rw [oddCoreIn_eq_bot_of_core hZ hB h, mem_bot] at hy
  rw [hy, one_pow]

theorem OddCoreExp.conj (ψ : MulAut T) {α : MulAut T} {k : ℕ} (h : OddCoreExp α k) :
    OddCoreExp (ψ * α * ψ⁻¹) k := by
  intro B hB y hy
  set φ := MulAut.conj ψ⁻¹ with hφ
  have hB' : (MulAut.conj : T →* MulAut T).range ≤ B.map φ.toMonoidHom := by
    rintro _ ⟨x, rfl⟩
    refine ⟨MulAut.conj (ψ x), hB ⟨_, rfl⟩, ?_⟩
    change ψ⁻¹ * MulAut.conj (ψ x) * ψ⁻¹⁻¹ = MulAut.conj x
    ext z
    simp [MulAut.conj_apply]
  have hφα : φ (ψ * α * ψ⁻¹) = α := by
    change ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α
    group
  have hy' : φ y ∈ oddCoreIn (B.map φ.toMonoidHom) α := by
    rw [← hφα, ← O.map_oddCoreIn_mulEquiv]
    exact ⟨y, hy, rfl⟩
  apply φ.injective
  rw [map_pow, h _ hB' _ hy', map_one]

theorem fix_of_mem_oddCoreIn [Finite T] (hZ : center T = ⊥) {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) {α : MulAut T} {Q : Subgroup T}
    (hQq : IsQuasisimple Q) (hQα : Q ≤ fixedSubgroup α)
    (hQN : fixedSubgroup α ≤ normalizer (Q : Set T)) {β : MulAut T}
    (hβO : β ∈ oddCoreIn B α) {x : T} (hx : x ∈ Q) : β x = x := by
  set c : T →* MulAut T := MulAut.conj with hcdef
  have hci : Function.Injective c := conj_injective hZ
  let eQ : Q ≃* Q.map c := Q.equivMapOfInjective c hci
  have hQq' : IsQuasisimple (Q.map c) := LocalCores.isQuasisimple_of_mulEquiv eQ hQq
  have hQe : Even (Nat.card (Q.map c)) := even_card_of_isQuasisimple hQq'
  obtain ⟨hFH, hFn⟩ := normal_map_fixedSubgroup hB α
  have hQH : Q.map c ≤ B ⊓ centralizer ({α} : Set (MulAut T)) := (map_mono hQα).trans hFH
  have hQs : ((Q.map c).subgroupOf (B ⊓ centralizer ({α} : Set (MulAut T)))).IsSubnormal :=
    isSubnormal_map_conj hQα hQN hFH hFn
  exact apply_eq_of_commute_conj hZ (commute_of_mem_pPrimeCore hQH hQq' hQs hQe hβO ⟨x, hx, rfl⟩)

theorem oddCoreExp_of_fix [Finite T] (hZ : center T = ⊥) {α : MulAut T} {Q : Subgroup T}
    (hQq : IsQuasisimple Q) (hQα : Q ≤ fixedSubgroup α)
    (hQN : fixedSubgroup α ≤ normalizer (Q : Set T)) {k : ℕ}
    (hfix : ∀ β : MulAut T, Odd (orderOf β) → α * β = β * α → (∀ x ∈ Q, β x = x) → β ^ k = 1) :
    OddCoreExp α k := by
  intro B hB y hy
  exact hfix y (odd_orderOf_of_mem_oddCoreIn hy) (commute_of_mem_oddCoreIn hy).symm
    fun x hx => fix_of_mem_oddCoreIn hZ hB hQq hQα hQN hy hx

theorem pow_eq_one_of_rows {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    [Finite T] (hZ : center T = ⊥) (θ : GeneralizedFitting.subgroup X ≃* T) {k : ℕ}
    (hrow : ∀ α : MulAut T, orderOf α = 2 → BurgCoreFor α ∨ OddCoreExp α k)
    {t : X} (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) : y ^ k = 1 := by
  set ψ := socleAction θ with hψdef
  have hψ : Function.Injective ψ := socleAction_injective hsimple hnab θ
  have hB : (MulAut.conj : T →* MulAut T).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hα : orderOf (ψ t) = 2 := by rw [orderOf_injective ψ hψ]; exact ht
  refine pow_eq_one_of_transfer hψ (fun y' hy' => ?_) hy
  rcases hrow (ψ t) hα with hc | hT
  · exact OddCoreExp.of_core hZ hc k _ hB y' hy'
  · exact hT _ hB y' hy'

end CFSG.ComponentClassification.Burgoyne.E2
