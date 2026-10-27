module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22FixedData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22LiftData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsTransport

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std CFSG.Blueprint.NativeSporadic
open scoped Pointwise

structure EngineData (Y : Type) [Group Y] (F : Subgroup Y) : Prop where
  fixed : FixedData (⊤ : Subgroup Y) F
  lift : LiftData (⊤ : Subgroup Y) F

theorem EngineData.map_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {F : Subgroup X}
    (D : EngineData X F) : EngineData Y (F.map e.toMonoidHom) := by
  have hr : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 e.surjective
  refine ⟨?_, ?_⟩
  · have := FixedData.map (φ := e.toMonoidHom) e.injective D.fixed
    rwa [hr] at this
  · have := LiftData.map (φ := e.toMonoidHom) e.injective D.lift
    rwa [hr] at this

@[expose] def AutSylowEngine (Y : Type) [Group Y] : Prop :=
  ∀ S : Subgroup (MulAut Y), IsPGroup 2 S → ¬ 2 ∣ S.index → ∃ (t : Y) (F : Subgroup Y),
    SylowWitness Y S t F ∧ EngineData Y F

theorem AutSylowEngine.facts {Y : Type} [Group Y] (h : AutSylowEngine Y) : AutSylowFacts Y :=
  fun S hS hidx => by
    obtain ⟨t, F, W, -⟩ := h S hS hidx
    exact ⟨t, F, W⟩

theorem AutSylowEngine.of_sylow {Y : Type} [Group Y] [Finite (MulAut Y)]
    {S₀ : Subgroup (MulAut Y)} (hp : IsPGroup 2 S₀) (hidx : ¬ 2 ∣ S₀.index) {t : Y}
    {F : Subgroup Y} (W : SylowWitness Y S₀ t F) (E : EngineData Y F) : AutSylowEngine Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hS hSidx
  let P1 : Sylow 2 (MulAut Y) := hp.toSylow hidx
  let P2 : Sylow 2 (MulAut Y) := hS.toSylow hSidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (MulAut Y) P1 P2
  have hmem : ∀ α : MulAut Y, α ∈ S ↔ c⁻¹ * α * c ∈ S₀ := by
    intro α
    have h1 : (P2 : Subgroup (MulAut Y)) = MulAut.conj c • (P1 : Subgroup (MulAut Y)) := by
      rw [← hc, Sylow.coe_subgroup_smul]
    have h2 : α ∈ (P2 : Subgroup (MulAut Y)) ↔
        (MulAut.conj c)⁻¹ • α ∈ (P1 : Subgroup (MulAut Y)) := by
      rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have h3 : (P2 : Subgroup (MulAut Y)) = S := rfl
    have h4 : (P1 : Subgroup (MulAut Y)) = S₀ := rfl
    rw [h3, h4] at h2
    rw [h2]
    simp [MulAut.smul_def, mul_assoc]
  have hS_eq : S₀.map (MulAut.congr c).toMonoidHom = S := by
    ext β
    rw [mem_map_phi (MulAut.congr c), congr_self_symm_apply, hmem]
  have W' := SylowWitness.map' c (MulAut.congr c) (congr_conj c) (congr_apply_mk c) W
  rw [hS_eq] at W'
  exact ⟨c t, F.map c.toMonoidHom, W', E.map_equiv c⟩

theorem AutSylowEngine.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : AutSylowEngine X) : AutSylowEngine Y := by
  intro S hS hidx
  let φ : MulAut X ≃* MulAut Y := MulAut.congr e
  let S' : Subgroup (MulAut X) := S.map φ.symm.toMonoidHom
  have hS'p : IsPGroup 2 S' :=
    hS.of_equiv (Subgroup.equivMapOfInjective S φ.symm.toMonoidHom φ.symm.injective)
  have hS'idx : ¬ 2 ∣ S'.index := by
    have : S'.index = S.index := Subgroup.index_map_equiv (H := S) φ.symm
    rwa [this]
  obtain ⟨t, F, W, E⟩ := h S' hS'p hS'idx
  refine ⟨e t, F.map e.toMonoidHom, ?_, E.map_equiv e⟩
  have h1 := SylowWitness.map' e φ (congr_conj e) (congr_apply_mk e) W
  have h2 : S'.map φ.toMonoidHom = S := by
    ext β
    rw [mem_map_phi φ, show S' = S.map φ.symm.toMonoidHom from rfl, Subgroup.mem_map_equiv,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  rwa [h2] at h1

theorem engineData_pinned
    {F1 : Subgroup (Carrier .M22)} (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    EngineData (Carrier .M22) F1 :=
  ⟨fixedData_pinned hmem1, liftData_pinned hmem1⟩

theorem autSylowEngine_m22 :
    AutSylowEngine (Carrier .M22) := by
  obtain ⟨S₀, t, F1, hp, hidx, hmem1, W⟩ := sylowWitness_m22_pinned
  exact AutSylowEngine.of_sylow hp hidx W (engineData_pinned hmem1)

end CFSG.EvenSporadicStandard.M22Std
