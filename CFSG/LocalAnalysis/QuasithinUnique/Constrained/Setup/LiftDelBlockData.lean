module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockDict

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization commutatorElement

section Model

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] {F : Type} [Field F]
  {H T : Subgroup (W ≃ₗ[ZMod 2] W)} {n r : ℕ} {Lc : Fin r → Subgroup (W ≃ₗ[ZMod 2] W)}

theorem del_model_module (layer : EvenSL2LayerOutput H T r F Lc) (hdel : DeletedFamily H n r Lc)
    (i : Fin r) :
    commGL (Lc i) ⊤ ≠ ⊥ ∧
    (∀ u ∈ commGL (Lc i) ⊤, (∀ l ∈ Lc i, l u = u) → u = 0) ∧
    commSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (Lc i) (commGL (Lc i) ⊤) = commGL (Lc i) ⊤ ∧
    (∀ U : Submodule (ZMod 2) W, U ≤ commGL (Lc i) ⊤ → (∀ l ∈ Lc i, ∀ u ∈ U, l u ∈ U) →
      U = ⊥ ∨ U = commGL (Lc i) ⊤) := by
  obtain ⟨hnot, hirr⟩ := layer.irr i
  have hZ : commGL (Lc i) ⊤ ⊓ fixGL (Lc i) = ⊥ := hdel.Z_bot i
  have hinv : Offender.IsInvariant (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (Lc i) (commGL (Lc i) ⊤) :=
    isInvariant_commGL_self (Lc i)
  have hne : commGL (Lc i) ⊤ ≠ ⊥ := by
    intro h
    apply hnot
    rw [h]
    exact bot_le
  have hfix : ∀ u ∈ commGL (Lc i) ⊤, (∀ l ∈ Lc i, l u = u) → u = 0 := by
    intro u hu hf
    have h1 : u ∈ commGL (Lc i) ⊤ ⊓ fixGL (Lc i) := ⟨hu, fun l hl => hf l hl⟩
    rw [hZ] at h1
    exact (Submodule.mem_bot _).1 h1
  have hirr' : ∀ U : Submodule (ZMod 2) W, U ≤ commGL (Lc i) ⊤ →
      (∀ l ∈ Lc i, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = commGL (Lc i) ⊤ := by
    intro U hUI hUinv
    have hbot : commGL (Lc i) ⊤ ⊓ fixSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (Lc i) ≤ U := by
      rw [show commGL (Lc i) ⊤ ⊓ fixSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (Lc i) = ⊥ from hZ]
      exact bot_le
    rcases hirr U (fun l hl u hu => hUinv l hl u hu) hbot hUI with h | h
    · left
      rw [h]
      exact hZ
    · right
      exact h
  refine ⟨hne, hfix, ?_, hirr'⟩
  set U := commSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (Lc i) (commGL (Lc i) ⊤) with hU
  have hUle : U ≤ commGL (Lc i) ⊤ := commSub_le_of_isInvariant hinv
  have hUinv : Offender.IsInvariant (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (Lc i) U :=
    isInvariant_commSub hinv
  rcases hirr' U hUle (fun l hl u hu => hUinv l hl u hu) with h | h
  · exfalso
    apply hnot
    intro u hu l hl
    have h1 : (MonoidHom.id (W ≃ₗ[ZMod 2] W)) l u - u ∈ U := mem_commSub_of hl hu
    rw [h] at h1
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 h1)
  · exact h

end Model

section Main

variable {G : Type} [Group G] [Finite G]

structure DelFamilyData (R V : Subgroup G) {r : ℕ} (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  normS : ∀ i, autOn (baum R) V ≤ Subgroup.normalizer (Lc i : Set (MulAut V))
  others : ∀ i j, j ≠ i → ∀ x ∈ Lc j, ∀ u : V, (u : G) ∈ modComm V (Lc i) → x u = u
  fixed : ∀ i, ∀ u : V, (u : G) ∈ modComm V (Lc i) → (∀ x ∈ Lc i, x u = u) → u = 1
  nonzero : ∀ i, modComm V (Lc i) ≠ ⊥
  comm : ∀ i, ∀ u : V, (u : G) ∈ modComm V (Lc i) →
    (u : G) ∈ Subgroup.closure {g : G | ∃ x ∈ Lc i, ∃ w : V, (w : G) ∈ modComm V (Lc i) ∧
      g = ((x w : V) : G) * (w : G)⁻¹}
  irr : ∀ i, ∀ W' : Subgroup G, W' ≤ modComm V (Lc i) →
    (∀ x ∈ Lc i, ∀ w : V, (w : G) ∈ W' → ((x w : V) : G) ∈ W') →
      W' = ⊥ ∨ W' = modComm V (Lc i)
  alt : ∀ i, ∃ (e : ↥(Lc i) ≃* alternatingGroup (Fin 5))
    (β : ↥(modComm V (Lc i)) ≃* Multiplicative ↥(CFSG.QuasithinUnique.evenWeight 5)),
    ∀ (x : ↥(Lc i)) (u v : ↥(modComm V (Lc i))) (hu : (u : G) ∈ V) (hv : (v : G) ∈ V),
      ((x : MulAut V) ⟨u, hu⟩ : ↥V) = ⟨v, hv⟩ → ∀ k : Fin 5,
        ((Multiplicative.toAdd (β v) : ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2) k =
          ((Multiplicative.toAdd (β u) : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
            Fin 5 → ZMod 2) (((e x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))⁻¹ k)

theorem del_family_data
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc)
    (hdel : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V) :
    DelFamilyData R V Lc := by
  classical
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS hLc
  have hbridge := even_SL2_original_bridge hS hLc
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  have hbK : autOn L V = oddOrderSubgroup (autOn (⊤ : Subgroup G) V) := hbridge.K_eq
  have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
    rw [hbK]
    exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
  have hdelF : DeletedFamily ((autOn (⊤ : Subgroup G) V).map ψ) n r
      (fun i => (Lc i).map ψ) := by
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdelF, -⟩
    · exfalso
      apply hdel
      have h1 := (himg.natural hnat).2.1.1
      rw [← hKL] at h1
      exact (Subgroup.map_le_map_iff_of_injective (binPsi θ).injective).1 h1
    · exact hdelF
  have layer := hmax.offenders.family.layer
  have common := hmax.offenders.family.common
  obtain ⟨-, hcard, ψi, βi, Ai, h5, hD, hdata⟩ := himg.deleted hdelF
  have hAB : ∀ i, Ai i ≤ blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc i).map ψ) :=
    fun i => ((hdata i).2.2.1).trans inf_le_right
  have hnormS : ∀ i, autOn (baum R) V ≤ Subgroup.normalizer (Lc i : Set (MulAut V)) := by
    intro i
    refine le_normalizer_of_map_le_map (binPsi θ) ?_
    have hSD : (autOn (baum R) V).map ψ = ⨆ j, Ai j := himg.baumann_eq.symm.trans hD
    rw [hSD]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji
      have hder := hdelF.derived j
      have h1 := le_normalizer_commutator
        (blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc j).map ψ))
        (blockB ((autOn (⊤ : Subgroup G) V).map ψ) ((Lc j).map ψ))
      rw [hder, sup_idem] at h1
      exact (hAB j).trans h1
    · intro a ha
      have hc : a ∈ Subgroup.centralizer (((Lc i).map ψ : Subgroup (W ≃ₗ[ZMod 2] W)) :
          Set (W ≃ₗ[ZMod 2] W)) :=
        Subgroup.mem_centralizer_iff.2 fun y hy =>
          (common.B_comm j i hji a (hAB j ha) y (common.L_le_B i hy)).symm
      exact Subgroup.centralizer_le_normalizer _ hc
  have hothers : ∀ i j, j ≠ i → ∀ x ∈ Lc j, ∀ u : V, (u : G) ∈ modComm V (Lc i) → x u = u := by
    intro i j hji x hx u hu
    have hu' := (mem_modComm_iff θ (Lc i) u).1 hu
    have h1 := layer.others_fix i j hji (ψ x) (Subgroup.mem_map_of_mem ψ hx) (vecOf θ u) hu'
    have h2 : vecOf θ (x u) = vecOf θ u := by
      rw [← binPsi_vecOf]
      exact h1
    exact vecOf_injective θ h2
  have hfixed : ∀ i, ∀ u : V, (u : G) ∈ modComm V (Lc i) → (∀ x ∈ Lc i, x u = u) → u = 1 := by
    intro i u hu hf
    have hu' := (mem_modComm_iff θ (Lc i) u).1 hu
    have h0 := (del_model_module layer hdelF i).2.1 (vecOf θ u) hu' (by
      intro l hl
      obtain ⟨x, hx, rfl⟩ := hl
      show binPsi θ x (vecOf θ u) = vecOf θ u
      rw [binPsi_vecOf, hf x hx])
    apply vecOf_injective θ
    rw [h0, vecOf_one]
  have hnonzero : ∀ i, modComm V (Lc i) ≠ ⊥ := by
    intro i h
    apply (del_model_module layer hdelF i).1
    rw [eq_bot_iff]
    intro w hw
    have h1 := elOf_mem_modComm θ (Lc i) hw
    rw [h, Subgroup.mem_bot] at h1
    have h2 : elOf θ w = 1 := Subtype.ext h1
    exact (Submodule.mem_bot _).2 (by rw [← vecOf_elOf θ w, h2, vecOf_one])
  have hcomm : ∀ i, ∀ u : V, (u : G) ∈ modComm V (Lc i) →
      (u : G) ∈ Subgroup.closure {g : G | ∃ x ∈ Lc i, ∃ w : V, (w : G) ∈ modComm V (Lc i) ∧
        g = ((x w : V) : G) * (w : G)⁻¹} := by
    intro i u hu
    have hu' := (mem_modComm_iff θ (Lc i) u).1 hu
    rw [← (del_model_module layer hdelF i).2.2.1] at hu'
    have h1 := elOf_mem_of_span θ (Subgroup.closure {g : G | ∃ x ∈ Lc i, ∃ w : V,
        (w : G) ∈ modComm V (Lc i) ∧ g = ((x w : V) : G) * (w : G)⁻¹}) (S := {w : W |
        ∃ b ∈ (Lc i).map ψ, ∃ u ∈ commGL ((Lc i).map ψ) ⊤,
          w = (MonoidHom.id (W ≃ₗ[ZMod 2] W)) b u - u}) ?_ hu'
    · rwa [elOf_vecOf] at h1
    · rintro w ⟨b, hb, w', hw', rfl⟩
      obtain ⟨x, hx, rfl⟩ := hb
      have h2 : elOf θ ((MonoidHom.id (W ≃ₗ[ZMod 2] W)) (ψ x) w' - w') =
          x (elOf θ w') * (elOf θ w')⁻¹ := elOf_sub_eq θ x w'
      rw [h2]
      exact Subgroup.subset_closure ⟨x, hx, elOf θ w', elOf_mem_modComm θ (Lc i) hw', rfl⟩
  have hirr : ∀ i, ∀ W' : Subgroup G, W' ≤ modComm V (Lc i) →
      (∀ x ∈ Lc i, ∀ w : V, (w : G) ∈ W' → ((x w : V) : G) ∈ W') →
        W' = ⊥ ∨ W' = modComm V (Lc i) := by
    intro i W' hWI hinv
    let U : Submodule (ZMod 2) W :=
      { carrier := {w | ((elOf θ w : V) : G) ∈ W'}
        add_mem' := fun {a b} ha hb => by
          show ((elOf θ (a + b) : V) : G) ∈ W'
          rw [elOf_add]
          exact W'.mul_mem ha hb
        zero_mem' := by
          show ((elOf θ (0 : W) : V) : G) ∈ W'
          rw [elOf_zero]
          exact W'.one_mem
        smul_mem' := fun c a ha => by
          have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
          rcases hc c with rfl | rfl
          · show ((elOf θ ((0 : ZMod 2) • a) : V) : G) ∈ W'
            rw [zero_smul, elOf_zero]
            exact W'.one_mem
          · simpa using ha }
    have hU1 : U ≤ commGL ((Lc i).map ψ) ⊤ := by
      intro w hw
      have h1 : ((elOf θ w : V) : G) ∈ modComm V (Lc i) := hWI hw
      have h2 := (mem_modComm_iff θ (Lc i) (elOf θ w)).1 h1
      rwa [vecOf_elOf] at h2
    have hU2 : ∀ l ∈ (Lc i).map ψ, ∀ u ∈ U, l u ∈ U := by
      intro l hl u hu
      obtain ⟨x, hx, rfl⟩ := hl
      show ((elOf θ (binPsi θ x u) : V) : G) ∈ W'
      have h3 : elOf θ (binPsi θ x u) = x (elOf θ u) := by
        have h4 := binPsi_vecOf θ x (elOf θ u)
        rw [vecOf_elOf] at h4
        rw [h4, elOf_vecOf]
      rw [h3]
      exact hinv x hx (elOf θ u) hu
    rcases (del_model_module layer hdelF i).2.2.2 U hU1 hU2 with h | h
    · left
      rw [eq_bot_iff]
      intro g hg
      have hgV : g ∈ V := modComm_le V (Lc i) (hWI hg)
      have h1 : vecOf θ ⟨g, hgV⟩ ∈ U := by
        show ((elOf θ (vecOf θ ⟨g, hgV⟩) : V) : G) ∈ W'
        rw [elOf_vecOf]
        exact hg
      rw [h] at h1
      have h0 : vecOf θ ⟨g, hgV⟩ = 0 := (Submodule.mem_bot _).1 h1
      have h2 : (⟨g, hgV⟩ : ↥V) = 1 := vecOf_injective θ (by rw [h0, vecOf_one])
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h2
    · right
      refine le_antisymm hWI ?_
      intro g hg
      have hgV : g ∈ V := modComm_le V (Lc i) hg
      have h1 := (mem_modComm_iff θ (Lc i) ⟨g, hgV⟩).1 hg
      rw [← h] at h1
      have h2 : ((elOf θ (vecOf θ ⟨g, hgV⟩) : V) : G) ∈ W' := h1
      rwa [elOf_vecOf] at h2
  have halt : ∀ i, ∃ (e : ↥(Lc i) ≃* alternatingGroup (Fin 5))
      (β : ↥(modComm V (Lc i)) ≃* Multiplicative ↥(CFSG.QuasithinUnique.evenWeight 5)),
      ∀ (x : ↥(Lc i)) (u v : ↥(modComm V (Lc i))) (hu : (u : G) ∈ V) (hv : (v : G) ∈ V),
        ((x : MulAut V) ⟨u, hu⟩ : ↥V) = ⟨v, hv⟩ → ∀ k : Fin 5,
          ((Multiplicative.toAdd (β v) : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
              Fin 5 → ZMod 2) k =
            ((Multiplicative.toAdd (β u) : ↥(CFSG.QuasithinUnique.evenWeight 5)) :
              Fin 5 → ZMod 2) (((e x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))⁻¹ k) := by
    intro i
    obtain ⟨Ω, _, _, hΩ5, ψΩ, βΩ, hcompat, haltΩ, -⟩ := hdelF.model i
    exact alt_data_of_model θ (Lc i) hΩ5 _ (common.L_le_B i) ψΩ βΩ hcompat haltΩ
  exact ⟨hnormS, hothers, hfixed, hnonzero, hcomm, hirr, halt⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift
