module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.BetaFor

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def IsInnerAut {Y : Type*} [Group Y] (r : MulAut Y) : Prop :=
  ∃ y : Y, r = MulAut.conj y

theorem IsInnerAut.mul {Y : Type*} [Group Y] {r s : MulAut Y} (hr : IsInnerAut r)
    (hs : IsInnerAut s) : IsInnerAut (r * s) := by
  obtain ⟨y, rfl⟩ := hr
  obtain ⟨w, rfl⟩ := hs
  exact ⟨y * w, by rw [map_mul]⟩

theorem IsInnerAut.inv {Y : Type*} [Group Y] {r : MulAut Y} (hr : IsInnerAut r) :
    IsInnerAut r⁻¹ := by
  obtain ⟨y, rfl⟩ := hr
  exact ⟨y⁻¹, by rw [map_inv]⟩

theorem IsInnerAut.congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {r : MulAut X}
    (hr : IsInnerAut r) : IsInnerAut (MulAut.congr e r) := by
  obtain ⟨x, rfl⟩ := hr
  refine ⟨e x, ?_⟩
  ext w
  simp [MulAut.conj_apply]

structure OuterBetaFor (Y : Type*) [Group Y] (β : Y) : Prop where
  fix : ∃ r : MulAut Y, ¬ IsInnerAut r ∧ r β = β
  noInv : ∀ r : MulAut Y, r * r = 1 → r β = β → IsInnerAut r

theorem OuterBetaFor.map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {β : X}
    (h : OuterBetaFor X β) : OuterBetaFor Y (e β) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr, hrβ⟩ := h.fix
    refine ⟨MulAut.congr e r, fun hin => hr ?_, ?_⟩
    · have := hin.congr e.symm
      have e1 : MulAut.congr e.symm (MulAut.congr e r) = r := by
        ext w
        simp [MulAut.congr_apply]
      rwa [e1] at this
    · simp [MulAut.congr_apply, hrβ]
  · intro r hr1 hrβ
    have h2 : (MulAut.congr e.symm r) * (MulAut.congr e.symm r) = 1 := by
      rw [← map_mul, hr1, map_one]
    have h3 : MulAut.congr e.symm r β = β := by
      simp only [MulAut.congr_apply]
      rw [← e.symm_apply_apply β]
      simp only [MulEquiv.trans_apply]
      have := hrβ
      rw [MulEquiv.symm_apply_apply]
      simpa using congrArg e.symm this
    have h4 := (h.noInv _ h2 h3).congr e
    have e1 : MulAut.congr e (MulAut.congr e.symm r) = r := by
      ext w
      simp [MulAut.congr_apply]
    rwa [e1] at h4

theorem OuterBetaFor.conj {Y : Type*} [Group Y] {β : Y} (h : OuterBetaFor Y β) (g : Y) :
    OuterBetaFor Y (g * β * g⁻¹) := by
  have := h.map (MulAut.conj g)
  simpa [MulAut.conj_apply] using this

@[expose] def BetaDataSqBO (X : Type*) [Group X] : Prop :=
  ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ (B : Subgroup X) (β : X),
    B ≤ centralizer ({t} : Set X) ∧ Nonempty (↥B ≃* alternatingGroup (Fin 5)) ∧ β ∈ B ∧
      BetaFor X β ∧ OuterBetaFor X β

theorem BetaDataSqBO.of_class {X : Type*} [Group X] [Finite X] (t₀ β₀ : X) (B₀ : Subgroup X)
    (hcls : ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ g : X, t = g * t₀ * g⁻¹)
    (hB : B₀ ≤ centralizer ({t₀} : Set X)) (hiso : Nonempty (↥B₀ ≃* alternatingGroup (Fin 5)))
    (hβB : β₀ ∈ B₀) (hβ : BetaFor X β₀) (hO : OuterBetaFor X β₀) : BetaDataSqBO X := by
  intro t ht2 hsq
  obtain ⟨g, rfl⟩ := hcls t ht2 hsq
  refine ⟨B₀.map (MulAut.conj g).toMonoidHom, g * β₀ * g⁻¹, ?_, ?_, ⟨β₀, hβB, rfl⟩, hβ.conj g,
    hO.conj g⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hbt := mem_centralizer_singleton_iff.1 (hB hb)
    show g * b * g⁻¹ * (g * t₀ * g⁻¹) = g * t₀ * g⁻¹ * (g * b * g⁻¹)
    calc g * b * g⁻¹ * (g * t₀ * g⁻¹) = g * (b * t₀) * g⁻¹ := by group
      _ = g * (t₀ * b) * g⁻¹ := by rw [hbt]
      _ = g * t₀ * g⁻¹ * (g * b * g⁻¹) := by group
  · obtain ⟨e⟩ := hiso
    exact ⟨((B₀.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).symm.trans e⟩

theorem BetaDataSqBO.of_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) (h : BetaDataSqBO X) : BetaDataSqBO Y := by
  intro t ht2 ⟨g, hg⟩
  have ht2' : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht2
  obtain ⟨B, β, hB, ⟨eB⟩, hβB, hβ, hO⟩ := h (e.symm t) ht2' ⟨e.symm g, by rw [← map_mul, hg]⟩
  refine ⟨B.map e.toMonoidHom, e β, ?_, ⟨((B.equivMapOfInjective e.toMonoidHom
    e.injective)).symm.trans eB⟩, ⟨β, hβB, rfl⟩, hβ.map e, hO.map e⟩
  rintro _ ⟨b, hb, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have hbt := mem_centralizer_singleton_iff.1 (hB hb)
  have := congrArg e hbt
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  exact this

@[expose] def OuterInvData (Y : Type*) [Group Y] : Prop :=
  (∃ r : MulAut Y, r * r = 1 ∧ ¬ IsInnerAut r) ∧
    ∀ a : Y, a * a = 1 → ∃ r : MulAut Y, r * r = MulAut.conj a

theorem OuterInvData.of_reps {Y : Type*} [Group Y] (reps : List Y)
    (hcls : ∀ a : Y, a * a = 1 → a ≠ 1 → ∃ g : Y, ∃ a₀ ∈ reps, a = g * a₀ * g⁻¹)
    (hsq : ∀ a₀ ∈ reps, ∃ r : MulAut Y, r * r = MulAut.conj a₀)
    (hout : ∃ r : MulAut Y, r * r = 1 ∧ ¬ IsInnerAut r) : OuterInvData Y := by
  refine ⟨hout, fun a ha => ?_⟩
  by_cases ha1 : a = 1
  · exact ⟨1, by simp [ha1]⟩
  · obtain ⟨g, a₀, h0, rfl⟩ := hcls a ha ha1
    obtain ⟨r, hr⟩ := hsq a₀ h0
    refine ⟨MulAut.conj g * r * (MulAut.conj g)⁻¹, ?_⟩
    calc (MulAut.conj g * r * (MulAut.conj g)⁻¹) * (MulAut.conj g * r * (MulAut.conj g)⁻¹)
        = MulAut.conj g * (r * r) * (MulAut.conj g)⁻¹ := by group
      _ = MulAut.conj g * MulAut.conj a₀ * (MulAut.conj g)⁻¹ := by rw [hr]
      _ = MulAut.conj (g * a₀ * g⁻¹) := by simp [map_mul, map_inv]

theorem OuterInvData.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : OuterInvData X) : OuterInvData Y := by
  obtain ⟨⟨r, hr1, hr⟩, hsq⟩ := h
  refine ⟨⟨MulAut.congr e r, ?_, fun hin => hr ?_⟩, fun a ha => ?_⟩
  · rw [← map_mul, hr1, map_one]
  · have := hin.congr e.symm
    have e1 : MulAut.congr e.symm (MulAut.congr e r) = r := by
      ext w
      simp [MulAut.congr_apply]
    rwa [e1] at this
  · obtain ⟨s, hs⟩ := hsq (e.symm a) (by rw [← map_mul, ha, map_one])
    refine ⟨MulAut.congr e s, ?_⟩
    rw [← map_mul, hs]
    ext w
    simp [MulAut.congr_apply, MulAut.conj_apply]

end CFSG.EvenSporadicStandard.Fin76b
