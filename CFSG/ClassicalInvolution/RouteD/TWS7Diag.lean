module

public import CFSG.ClassicalInvolution.RouteD.TypeDModel
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutPlus

public section

open CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD)
open CFSG.Timmesfeld.LevisSpin (cartanD_of_not_edgeD)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.ClassicalInvolution.RouteD (rankOne_mem_fundamentalSubgroups_plusDatum
  commutes_rankOne_plusDatum standardPair_plusDatum_edge conjSub_mem_fundamentalSubgroups)
open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups)
open scoped Matrix MatrixGroups

namespace CFSG.ClassicalInvolution.RouteD.TWS7

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] noncomputable def isoSemiSim (w : V ≃ₗ[F] V) (hw : ∀ x, Q (w x) = Q x) : SemiSim Q where
  toFun := w
  φ := RingEquiv.refl F
  μ := 1
  map_add := map_add w
  map_smul c x := by simp
  bijective := w.bijective
  map_Q x := by simp [hw]

theorem isoSemiSim_apply (w : V ≃ₗ[F] V) (hw : ∀ x, Q (w x) = Q x) (x : V) :
    isoSemiSim w hw x = w x := rfl

theorem isConj_isoSemiSim (w : V ≃ₗ[F] V) (hw : ∀ x, Q (w x) = Q x)
    {α : spinGroup Q ≃* spinGroup Q}
    (hθw : ∀ y, spinAction Q (α y) = w * spinAction Q y * w⁻¹) :
    IsConj α (isoSemiSim w hw) := by
  intro y z
  rw [isoSemiSim_apply, isoSemiSim_apply, hθw y]
  simp [LinearEquiv.mul_apply]

@[expose] def lamD (F : Type) [Field F] (i : Fin 4) : F := if i.val = 0 then -1 else 1

theorem alpha_longRoot {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1) (F₀ : HypFrame Q 4)
    {α : spinGroup Q ≃* spinGroup Q} {w : V ≃ₗ[F] V} (hw : ∀ x, Q (w x) = Q x)
    (hθw : ∀ y, spinAction Q (α y) = w * spinAction Q y * w⁻¹) (κ : spinGroup Q)
    (hκ : ∀ i s, w (spinAction Q κ (F₀.vec i s)) = lamD F i • spinAction Q κ (F₀.vec i s))
    {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : F) :
    α (κ * F₀.longRoot hij s t (.ofAdd c) * κ⁻¹) =
      κ * F₀.longRoot hij s t (.ofAdd (lamD F j * (lamD F i * c))) * κ⁻¹ := by
  have hα : IsConj α (isoSemiSim w hw) := isConj_isoSemiSim w hw hθw
  have hα₂c := hα.conjSpin κ
  have hg₂ : ∀ i s, (isoSemiSim w hw).conjSpin κ (F₀.vec i s) =
      lamD F i • F₀.vec i ((fun _ s => s) i s) := by
    intro i s
    rw [SemiSim.conjSpin_apply, isoSemiSim_apply, hκ, map_smul, spinAction_inv_apply]
  have h3 := IsConj.longRoot_eq hp2 hker2 F₀ hα₂c (fun i _ => lamD F i) (fun _ s => s) hg₂ hij s t c
  have e1 : α (κ * F₀.longRoot hij s t (.ofAdd c) * κ⁻¹) =
      κ * conjTwist α κ (F₀.longRoot hij s t (.ofAdd c)) * κ⁻¹ := by
    rw [conjTwist_apply]
    group
  rw [e1, h3]
  have hμ : ((((isoSemiSim w hw).conjSpin κ).μ : Fˣ) : F) = 1 := rfl
  have hφ : ((isoSemiSim w hw).conjSpin κ).φ c = c := rfl
  rw [hμ, hφ, inv_one, one_mul]

section Nodes

variable [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

omit [Finite F] in
theorem lamD_nodes (a : Fin 4) :
    (1 ≤ a.val → lamD F (rootIdxD 4 a) * lamD F (rootIdxD' 4 a) = 1) ∧
    (a.val = 0 → lamD F (rootIdxD 4 a) * lamD F (rootIdxD' 4 a) = -1) := by
  fin_cases a <;> simp [rootIdxD, rootIdxD', lamD]

theorem node_facts (hp2 : p ≠ 2) (hm3 : 3 ≤ 4) {X : Type} [Group X]
    (ψ : spinGroup (quadPlus 4 F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 F))) (τ : X ≃* X)
    {α : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)}
    (hαψ : ∀ y, ψ (α y) = τ (ψ y)) {w : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)}
    (hw : ∀ x, quadPlus 4 F (w x) = quadPlus 4 F x)
    (hθw : ∀ y, spinAction (quadPlus 4 F) (α y) = w * spinAction (quadPlus 4 F) y * w⁻¹)
    (κ : spinGroup (quadPlus 4 F))
    (hκ : ∀ i s, w (spinAction (quadPlus 4 F) κ ((plusFrame 4 F hm3).vec i s)) =
      lamD F i • spinAction (quadPlus 4 F) κ ((plusFrame 4 F hm3).vec i s)) :
    (∀ a : Fin 4, 1 ≤ a.val → ∀ g ∈ conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup a),
      τ (ψ g) = ψ g) ∧
    (∀ g ∈ conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup (⟨0, by omega⟩ : Fin 4)),
      τ (ψ g) ∈ (conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup (⟨0, by omega⟩ : Fin 4))).map ψ) ∧
    (∃ g ∈ conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup (⟨0, by omega⟩ : Fin 4)),
      τ (ψ g) ≠ ψ g) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_ne_two (F := F) hp2)
  obtain ⟨hZ, -⟩ := plus_center_facts (F := F) hp2 hm3
  have hker2 := plus_hker2 (F := F) 4
  set F₀ := plusFrame 4 F hm3 with hF₀
  have hrank : ∀ a : Fin 4, rankOne (plusDatum 4 F hm3).rootGroup a =
      (rootD F hm3 a).range ⊔ (negRootD F hm3 a).range := by
    intro a
    show plusRootGroup 4 F hm3 (Pi.single a 1) ⊔ plusRootGroup 4 F hm3 (-Pi.single a 1) = _
    rw [plusRootGroup_single, plusRootGroup_neg_single]
  have hpos : ∀ (a : Fin 4) (c : F), α (κ * rootD F hm3 a (.ofAdd c) * κ⁻¹) =
      κ * rootD F hm3 a (.ofAdd (lamD F (rootIdxD' 4 a) * (lamD F (rootIdxD 4 a) * c))) * κ⁻¹ :=
    fun a c => alpha_longRoot hp2 hker2 F₀ hw hθw κ hκ (rootIdxD_ne 4 (by omega) a) true
      (rootSignD 4 a) c
  have hneg : ∀ (a : Fin 4) (c : F), α (κ * negRootD F hm3 a (.ofAdd c) * κ⁻¹) =
      κ * negRootD F hm3 a (.ofAdd (lamD F (rootIdxD 4 a) * (lamD F (rootIdxD' 4 a) * c))) *
        κ⁻¹ :=
    fun a c => alpha_longRoot hp2 hker2 F₀ hw hθw κ hκ (rootIdxD_ne 4 (by omega) a).symm
      (!rootSignD 4 a) false c
  have hconj : ∀ (a : Fin 4) (S : Subgroup (spinGroup (quadPlus 4 F))),
      (∀ c : F, κ * rootD F hm3 a (.ofAdd c) * κ⁻¹ ∈ S) →
      (∀ c : F, κ * negRootD F hm3 a (.ofAdd c) * κ⁻¹ ∈ S) →
      conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup a) ≤ S := by
    intro a S h1 h2
    rw [hrank, conjSub, Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact h1 y.toAdd
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact h2 y.toAdd
  have hmem : ∀ (a : Fin 4) (c : F), κ * rootD F hm3 a (.ofAdd c) * κ⁻¹ ∈
      conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup a) := fun a c =>
    CFSG.ClassicalInvolution.Generic.conj_mem_conjSub (by
      rw [hrank]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩)
  have hmem' : ∀ (a : Fin 4) (c : F), κ * negRootD F hm3 a (.ofAdd c) * κ⁻¹ ∈
      conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup a) := fun a c =>
    CFSG.ClassicalInvolution.Generic.conj_mem_conjSub (by
      rw [hrank]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩)
  have hl0 : lamD F (rootIdxD 4 ⟨0, by omega⟩) * lamD F (rootIdxD' 4 ⟨0, by omega⟩) = -1 :=
    (lamD_nodes (F := F) ⟨0, by omega⟩).2 rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    intro a ha
    set S : Subgroup (spinGroup (quadPlus 4 F)) :=
      MonoidHom.eqLocus (α : spinGroup (quadPlus 4 F) →* spinGroup (quadPlus 4 F))
        (MonoidHom.id _) with hS
    have hl := (lamD_nodes (F := F) a).1 ha
    have key : conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup a) ≤ S := by
      refine hconj a S (fun c => ?_) (fun c => ?_)
      · show α _ = _
        rw [hpos, show lamD F (rootIdxD' 4 a) * (lamD F (rootIdxD 4 a) * c) = c by
          rw [← mul_assoc, mul_comm (lamD F (rootIdxD' 4 a)), hl, one_mul]]
        rfl
      · show α _ = _
        rw [hneg, show lamD F (rootIdxD 4 a) * (lamD F (rootIdxD' 4 a) * c) = c by
          rw [← mul_assoc, hl, one_mul]]
        rfl
    intro g hg
    have : α g = g := key hg
    rw [← hαψ, this]
  ·
    intro g hg
    set T : Subgroup (spinGroup (quadPlus 4 F)) :=
      (conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup (⟨0, by omega⟩ : Fin 4))).comap
        (α : spinGroup (quadPlus 4 F) →* spinGroup (quadPlus 4 F)) with hT
    have hT' : ∀ x, x ∈ T ↔ α x ∈
        conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup (⟨0, by omega⟩ : Fin 4)) :=
      fun x => Iff.rfl
    have key : conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup (⟨0, by omega⟩ : Fin 4)) ≤ T := by
      refine hconj _ T (fun c => (hT' _).mpr ?_) (fun c => (hT' _).mpr ?_)
      · rw [hpos]
        exact hmem _ _
      · rw [hneg]
        exact hmem' _ _
    exact ⟨α g, (hT' g).mp (key hg), hαψ g⟩
  ·
    refine ⟨κ * rootD F hm3 ⟨0, by omega⟩ (.ofAdd 1) * κ⁻¹, hmem _ _, fun h => ?_⟩
    rw [← hαψ, hpos] at h
    have h1 : (κ * rootD F hm3 ⟨0, by omega⟩ (.ofAdd 1) * κ⁻¹)⁻¹ *
        (κ * rootD F hm3 ⟨0, by omega⟩ (.ofAdd (lamD F (rootIdxD' 4 ⟨0, by omega⟩) *
          (lamD F (rootIdxD 4 ⟨0, by omega⟩) * 1))) * κ⁻¹) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    have h2' := hψ h1
    have h3 : lamD F (rootIdxD' 4 ⟨0, by omega⟩) * (lamD F (rootIdxD 4 ⟨0, by omega⟩) * 1) =
        -1 := by rw [mul_one, mul_comm]; exact hl0
    rw [h3] at h2'
    have h4 : (κ * rootD F hm3 ⟨0, by omega⟩ (.ofAdd 1) * κ⁻¹)⁻¹ *
        (κ * rootD F hm3 ⟨0, by omega⟩ (.ofAdd (-1)) * κ⁻¹) =
        κ * rootD F hm3 ⟨0, by omega⟩ (.ofAdd (-2)) * κ⁻¹ := by
      have h5 : (Multiplicative.ofAdd (1 : F))⁻¹ * Multiplicative.ofAdd (-1) =
          Multiplicative.ofAdd (-2) := by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
        ring
      rw [← h5, map_mul, map_inv]
      group
    rw [h4] at h2'
    have h6 := eq_zero_of_conj_central hZ F₀ (rootIdxD_ne 4 (by omega) ⟨0, by omega⟩) true
      (rootSignD 4 ⟨0, by omega⟩) (-2) κ h2'
    apply h2
    have : (2 : F) = -(-2) := by ring
    rw [this, h6, neg_zero]

theorem exists_node_system (hp2 : p ≠ 2) (hm3 : 3 ≤ 4) {X : Type} [Group X]
    (ψ : spinGroup (quadPlus 4 F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus 4 F))) (τ : X ≃* X)
    {α : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)}
    (hαψ : ∀ y, ψ (α y) = τ (ψ y)) {w : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)}
    (hw : ∀ x, quadPlus 4 F (w x) = quadPlus 4 F x)
    (hθw : ∀ y, spinAction (quadPlus 4 F) (α y) = w * spinAction (quadPlus 4 F) y * w⁻¹)
    (κ : spinGroup (quadPlus 4 F))
    (hκ : ∀ i s, w (spinAction (quadPlus 4 F) κ ((plusFrame 4 F hm3).vec i s)) =
      lamD F i • spinAction (quadPlus 4 F) κ ((plusFrame 4 F hm3).vec i s)) :
    ∃ R : Fin 4 → Subgroup (spinGroup (quadPlus 4 F)),
      (∀ a, R a ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F hm3)) ∧
      (∀ a b, a ≠ b → ¬ edgeD 4 a b → ¬ edgeD 4 b a → Commutes (R a) (R b)) ∧
      (∀ a b, edgeD 4 a b → ∃ W, LinearBlockStandardPair F W (R a) (R b)) ∧
      (∀ a : Fin 4, 1 ≤ a.val → ∀ g ∈ R a, τ (ψ g) = ψ g) ∧
      (∀ g ∈ R ⟨0, by omega⟩, τ (ψ g) ∈ (R ⟨0, by omega⟩).map ψ) ∧
      (∃ g ∈ R ⟨0, by omega⟩, τ (ψ g) ≠ ψ g) := by
  obtain ⟨h1, h2, h3⟩ := node_facts hp2 hm3 ψ hψ τ hαψ hw hθw κ hκ
  refine ⟨fun a => conjSub κ (rankOne (plusDatum 4 F hm3).rootGroup a), fun a =>
    conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamentalSubgroups_plusDatum hm3 a) κ,
    ?_, ?_, h1, h2, h3⟩
  · intro a b hab hn1 hn2
    exact (commutes_rankOne_plusDatum hm3 (cartanD_of_not_edgeD hab hn1 hn2).1).conjSub κ
  · intro a b hab
    obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hm3 hab
    exact ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW κ⟩

end Nodes

end CFSG.ClassicalInvolution.RouteD.TWS7
