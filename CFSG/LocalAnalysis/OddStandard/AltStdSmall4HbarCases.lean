module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarPsi
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.OddStandard.AltStdSmall4.HbarCoords

open Subgroup Matrix

section Transport

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}
  (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T)
  {cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G}
  (hc : ModIso.TCoords z T (ModIso.kap θ c.hn8) (E θ c.hn8) cT)
  (hact : ∀ (A : GL (Fin 3) (ZMod 2)) (v w : Fin 3 → ZMod 2),
    ModIso.act T (ModIso.Ocore θ c.hn8 z) (ModIso.kap θ c.hn8 A) (cT v w) =
      cT ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w))

theorem card_map_psi : Nat.card ((Hbar T).map (psi hc).toMonoidHom) = Nat.card (Hbar T) :=
  card_map_of_injective (psi hc).injective

include hH in
theorem psi_normAct_z : psi hc (AltStdBal.normAct T ⟨z, hH.n0.norm⟩) = GL62.z₀ :=
  psi_normAct_eq_of hc fun v w => by rw [hc.conj_z, GL62.z0_mulVec, cT6_append]

include hH hact in
theorem dg_mem_map (A : GL (Fin 3) (ZMod 2)) :
    GL62.dg A ∈ (Hbar T).map (psi hc).toMonoidHom := by
  obtain ⟨g, hg, hgv⟩ := exists_normalizer_dg c hH hc hact A
  exact ⟨AltStdBal.normAct T ⟨g, hg⟩, ⟨_, rfl⟩,
    psi_normAct_eq_of hc fun v w => by rw [hgv, GL62.dg_mulVec, cT6_append]⟩

include hH hact in
theorem B₀_le_map : GL62.B₀ ≤ (Hbar T).map (psi hc).toMonoidHom := by
  refine sup_le ?_ (zpowers_le.2 ?_)
  · rintro _ ⟨A, rfl⟩
    exact dg_mem_map c hH hc hact A
  · exact ⟨AltStdBal.normAct T ⟨z, hH.n0.norm⟩, ⟨_, rfl⟩, psi_normAct_z c hH hc⟩

include hH hact in
theorem cent_le_B₀ : ∀ x ∈ (Hbar T).map (psi hc).toMonoidHom,
    x * GL62.z₀ = GL62.z₀ * x → x ∈ GL62.B₀ := by
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩ hx
  set gz : normalizer (T : Set G) := ⟨z, hH.n0.norm⟩
  set F : normalizer (T : Set G) →* GL (Fin 6) (ZMod 2) :=
    (psi hc).toMonoidHom.comp (AltStdBal.normAct T)
  have hFz : F gz = GL62.z₀ := psi_normAct_z c hH hc
  have h1 : AltStdBal.normAct T (g * gz * g⁻¹ * gz⁻¹) = 1 := by
    apply (psi hc).injective
    have h2 : F (g * gz * g⁻¹ * gz⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hFz]
      have hx' : F g * GL62.z₀ = GL62.z₀ * F g := hx
      rw [hx', mul_inv_cancel_right, mul_inv_cancel]
    rw [map_one]
    exact h2
  have h3 := (mem_ker_normAct_iff (g * gz * g⁻¹ * gz⁻¹)).1 h1
  have h4 : (g : G) * z * (g : G)⁻¹ * z⁻¹ ∈ centralizer (T : Set G) := h3
  obtain ⟨k, hk, hkz⟩ := exists_cent_lift c hH g.2 h4
  have hkN : k ∈ normalizer (T : Set G) := Subgroup.centralizer_le_normalizer _ hk
  have hhN : k * g ∈ normalizer (T : Set G) := mul_mem hkN g.2
  have hk1 : AltStdBal.normAct T ⟨k, hkN⟩ = 1 := (mem_ker_normAct_iff ⟨k, hkN⟩).2 hk
  have hkg : AltStdBal.normAct T ⟨k * g, hhN⟩ = AltStdBal.normAct T g := by
    have : (⟨k * g, hhN⟩ : normalizer (T : Set G)) = ⟨k, hkN⟩ * g := rfl
    rw [this, map_mul, hk1, one_mul]
  obtain ⟨P, ε, hP⟩ := cent_act c hH hc hact hhN hkz
  show F g ∈ GL62.B₀
  have hFg : F g = psi hc (AltStdBal.normAct T ⟨k * g, hhN⟩) := by
    rw [hkg]
    rfl
  have hdg : GL62.dg P ∈ GL62.B₀ := mem_sup_left ⟨P, rfl⟩
  have hz0 : GL62.z₀ ∈ GL62.B₀ := mem_sup_right (mem_zpowers _)
  cases ε with
  | false =>
    have h5 : psi hc (AltStdBal.normAct T ⟨k * g, hhN⟩) = GL62.dg P :=
      psi_normAct_eq_of hc fun v w => by
        rw [hP, GL62.dg_mulVec, cT6_append]
        rfl
    rw [hFg, h5]
    exact hdg
  | true =>
    have h5 : psi hc (AltStdBal.normAct T ⟨k * g, hhN⟩) = GL62.dg P * GL62.z₀ :=
      psi_normAct_eq_of hc fun v w => by
        rw [hP, Units.val_mul, ← mulVec_mulVec, GL62.z0_mulVec, GL62.dg_mulVec, cT6_append]
        rfl
    rw [hFg, h5]
    exact mul_mem hdg hz0

include hH hact in
theorem hbar_transport_of : GL62.B₀ ≤ (Hbar T).map (psi hc).toMonoidHom ∧
    ∀ x ∈ (Hbar T).map (psi hc).toMonoidHom, x * GL62.z₀ = GL62.z₀ * x → x ∈ GL62.B₀ :=
  ⟨B₀_le_map c hH hc hact, cent_le_B₀ c hH hc hact⟩

end Transport

section Main

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ}
  {θ : L ≃* alternatingGroup (Fin n)} {z : G} {T : Subgroup G}

theorem hbar_transport (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T) :
    ∃ Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2), GL62.B₀ ≤ (Hbar T).map Ψ.toMonoidHom ∧
      ∀ x ∈ (Hbar T).map Ψ.toMonoidHom, x * GL62.z₀ = GL62.z₀ * x → x ∈ GL62.B₀ := by
  obtain ⟨cT, hc, hact⟩ := ModIso.exists_tCoords_act c hH
  exact ⟨psi hc, hbar_transport_of c hH hc hact⟩

end Main

theorem sec4HbarCases_of (h : GL62.GL62Overgroups) : Sec4HbarCases := by
  intro G _ _ L Q n θ z c T hH
  obtain ⟨Ψ, hB, hC⟩ := hbar_transport c hH
  have hcard : Nat.card ((Hbar T).map Ψ.toMonoidHom) = Nat.card (Hbar T) :=
    card_map_of_injective Ψ.injective
  rw [← hcard]
  exact h _ hB hC

@[expose] def Sec4HbarIdent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L Q : Subgroup G) (n : ℕ)
    (θ : L ≃* alternatingGroup (Fin n)) (z : G) (c : Config G L Q n θ z) (T : Subgroup G),
    HData θ c.hn8 z T →
    ∃ (cT : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) → G) (Ψ : MulAut T ≃* GL (Fin 6) (ZMod 2)),
      ModIso.TCoords z T (ModIso.kap θ c.hn8) (E θ c.hn8) cT ∧
      (∀ (g : normalizer (T : Set G)) (v w : Fin 3 → ZMod 2),
        (g : G) * cT v w * (g : G)⁻¹ =
          cT (GL62.fst ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
              Fin.append v w))
            (GL62.snd ((Ψ (AltStdBal.normAct T g) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
              Fin.append v w))) ∧
      ((Hbar T).map Ψ.toMonoidHom = GL62.B₀ ∨ (Hbar T).map Ψ.toMonoidHom = GL62.MN ∨
        (Hbar T).map Ψ.toMonoidHom = GL62.MW ∨ (Hbar T).map Ψ.toMonoidHom = GL62.MS ∨
        (Hbar T).map Ψ.toMonoidHom = GL62.MG)

theorem sec4HbarIdent_of (h : GL62.GL62OvergroupsEq) : Sec4HbarIdent := by
  intro G _ _ L Q n θ z c T hH
  obtain ⟨cT, hc, hact⟩ := ModIso.exists_tCoords_act c hH
  obtain ⟨hB, hC⟩ := hbar_transport_of c hH hc hact
  refine ⟨cT, psi hc, hc, fun g v w => conj_eq_psi_normAct hc g v w, ?_⟩
  rcases h _ hB hC with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

end CFSG.OddStandard.AltStdSmall4.HbarCoords
