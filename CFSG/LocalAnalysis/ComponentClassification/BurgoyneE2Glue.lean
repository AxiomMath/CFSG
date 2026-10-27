module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Torus

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {T : Type} [Group T]

@[expose] def BurgCoreFor (α : MulAut T) : Prop :=
  pPrimeCore 2 (fixedSubgroup α) = ⊥ ∧
    ∀ β : MulAut T, Odd (orderOf β) → α * β = β * α → (∀ x ∈ fixedSubgroup α, β x = x) → β = 1

theorem oddCoreIn_eq_bot_of_core [Finite T] (hZ : center T = ⊥) {B : Subgroup (MulAut T)}
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) {α : MulAut T} (h : BurgCoreFor α) :
    oddCoreIn B α = ⊥ := by
  obtain ⟨h1, h2⟩ := h
  set c : T →* MulAut T := MulAut.conj with hcdef
  set F := fixedSubgroup α with hF
  have hci : Function.Injective c := conj_injective hZ
  have hcF : ∀ l ∈ F, c l ∈ B ⊓ centralizer ({α} : Set (MulAut T)) := by
    intro l hl
    have hl' : α l = l := hl
    refine mem_inf.2 ⟨hB ⟨l, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have := mul_conj_mul_inv α l
    rw [hl'] at this
    calc c l * α = (α * c l * α⁻¹) * α := by rw [this]
      _ = α * c l := by group
  have hOn : ∀ k ∈ B ⊓ centralizer ({α} : Set (MulAut T)), ∀ o ∈ oddCoreIn B α,
      k * o * k⁻¹ ∈ oddCoreIn B α := by
    rintro k hk _ ⟨o, ho, rfl⟩
    exact ⟨⟨k, hk⟩ * o * ⟨k, hk⟩⁻¹, (pPrimeCore_normal (p := 2)).conj_mem o ho ⟨k, hk⟩, rfl⟩
  let W : Subgroup F := (oddCoreIn B α).comap (c.comp F.subtype)
  have hWn : W.Normal := ⟨fun w hw k => by
    change c ((k : T) * w * (k : T)⁻¹) ∈ oddCoreIn B α
    rw [map_mul, map_mul, map_inv]
    exact hOn _ (hcF _ k.2) _ hw⟩
  have hWodd : Nat.Coprime 2 (Nat.card W) := by
    have hcop : Nat.Coprime 2 (Nat.card (oddCoreIn B α)) := by
      rw [card_map_of_injective (subtype_injective _)]
      exact pPrimeCore_coprime_card
    let φ : W →* oddCoreIn B α :=
      { toFun := fun w => ⟨c (w : F), w.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun w w' => Subtype.ext (by simp) }
    have hφ : Function.Injective φ := by
      intro w w' hww
      apply Subtype.ext
      apply Subtype.ext
      exact hci (congrArg Subtype.val hww)
    exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_injective φ hφ)
  have hW : W = ⊥ := pPrimeCore_eq_bot_iff.1 h1 W hWn hWodd
  rw [eq_bot_iff]
  intro β hβ
  rw [mem_bot]
  have hcomm : α * β = β * α := (commute_of_mem_oddCoreIn hβ).symm
  refine h2 β (odd_orderOf_of_mem_oddCoreIn hβ) hcomm fun l hl => ?_
  have hβl : β l ∈ F := by
    change α (β l) = β l
    have hl' : α l = l := hl
    rw [← MulAut.mul_apply, hcomm, MulAut.mul_apply, hl']
  have hw : (⟨β l * l⁻¹, mul_mem hβl (inv_mem hl)⟩ : F) ∈ W := by
    change c (β l * l⁻¹) ∈ oddCoreIn B α
    rw [map_mul, map_inv, ← mul_conj_mul_inv]
    have h3 : c l * β⁻¹ * (c l)⁻¹ ∈ oddCoreIn B α := hOn _ (hcF l hl) _ (inv_mem hβ)
    have h4 := mul_mem hβ h3
    rwa [show β * (c l * β⁻¹ * (c l)⁻¹) = β * c l * β⁻¹ * (c l)⁻¹ by group] at h4
  rw [hW, mem_bot] at hw
  exact mul_inv_eq_one.1 (congrArg Subtype.val hw)

theorem BurgCoreFor.congr {T' : Type} [Group T'] (e : T ≃* T') {α : MulAut T}
    (h : BurgCoreFor α) : BurgCoreFor (MulAut.congr e α) := by
  obtain ⟨h1, h2⟩ := h
  have hα' : ∀ y, MulAut.congr e α y = e (α (e.symm y)) := fun _ => rfl
  have hfix : fixedSubgroup (MulAut.congr e α) = (fixedSubgroup α).map e.toMonoidHom := by
    ext y
    rw [mem_map_equiv]
    change MulAut.congr e α y = y ↔ α (e.symm y) = e.symm y
    rw [hα']
    constructor
    · intro hy
      have := congrArg e.symm hy
      rwa [MulEquiv.symm_apply_apply] at this
    · intro hy
      rw [hy, MulEquiv.apply_symm_apply]
  refine ⟨?_, fun β' hβ' hcomm hfix' => ?_⟩
  · let eF : fixedSubgroup α ≃* fixedSubgroup (MulAut.congr e α) :=
      ((fixedSubgroup α).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hfix.symm)
    rw [← pPrimeCore_map_iso 2 eF, h1, Subgroup.map_bot]
  · set β := (MulAut.congr e).symm β' with hβdef
    have hβ'eq : β' = MulAut.congr e β := by rw [hβdef, MulEquiv.apply_symm_apply]
    have hβapp : ∀ x, β x = e.symm (β' (e x)) := fun _ => rfl
    have hodd : Odd (orderOf β) := by
      rw [hβdef, MulEquiv.orderOf_eq]
      exact hβ'
    have hcomm' : α * β = β * α := by
      apply (MulAut.congr e).injective
      rw [map_mul, map_mul, ← hβ'eq]
      exact hcomm
    have hfix'' : ∀ x ∈ fixedSubgroup α, β x = x := by
      intro x hx
      have hx' : e x ∈ fixedSubgroup (MulAut.congr e α) := by
        rw [hfix]
        exact ⟨x, hx, rfl⟩
      rw [hβapp, hfix' (e x) hx', MulEquiv.symm_apply_apply]
    rw [hβ'eq, h2 β hodd hcomm' hfix'', map_one]

theorem BurgCoreFor.conj (ψ : MulAut T) {α : MulAut T} (h : BurgCoreFor α) :
    BurgCoreFor (ψ * α * ψ⁻¹) := by
  have e : MulAut.congr ψ α = ψ * α * ψ⁻¹ := by
    ext x
    rfl
  rw [← e]
  exact h.congr ψ

theorem propAConclusion_of_rows {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a)
    [Finite T] (hZ : center T = ⊥) (θ : GeneralizedFitting.subgroup X ≃* T)
    (hrow : ∀ α : MulAut T, orderOf α = 2 → BurgCoreFor α ∨ BurgTorusFor α)
    {t : X} (ht : orderOf t = 2) {Y : Subgroup X} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  set ψ := socleAction θ with hψdef
  have hψ : Function.Injective ψ := socleAction_injective hsimple hnab θ
  have hB : (MulAut.conj : T →* MulAut T).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hα : orderOf (ψ t) = 2 := by rw [orderOf_injective ψ hψ]; exact ht
  have hYO' : Y.map ψ ≤ oddCoreIn ψ.range (ψ t) := by
    rw [← map_oddCentralizerCore_of_injective hψ t]
    exact map_mono hYO
  have hY' : Y.map ψ ≠ ⊥ := fun h => hY ((map_eq_bot_iff_of_injective Y hψ).1 h)
  rcases hrow (ψ t) hα with hc | hT
  · exact (hY' (le_bot_iff.1 ((oddCoreIn_eq_bot_of_core hZ hB hc) ▸ hYO'))).elim
  · exact PropAConclusion.of_injective hψ (propAConclusionIn_of_burgTorusFor hZ hB hα hT hY' hYO')

end CFSG.ComponentClassification.Burgoyne.E2
