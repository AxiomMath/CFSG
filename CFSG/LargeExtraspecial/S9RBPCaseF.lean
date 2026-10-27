module

public import CFSG.LargeExtraspecial.S9RBPCaseE
public import CFSG.LargeExtraspecial.S9RBPCaseA
public import CFSG.LargeExtraspecial.S9RBPSpread

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

namespace TriHyp

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g} {τ₁ τ₂ : S.O} (T : TriHyp H C ht ht1 hVQ τ₁ τ₂)
include T

theorem false_of_not_le (hNo : NoA2 S g) {k : S.O} (hkR : k ∈ Rbar S g t)
    (hkN : k ∉ Nbar S g t)
    (hk : ∀ x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t) : False := by
  have hcomm := T.forall_comm_of_not_le hkR hkN hk
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hth := mem_Lbar_of_pair H ht hh
  obtain ⟨m, hm, hLm⟩ := dtEqConj_of_transitive H ht T.data.transitive h hth
  obtain ⟨w₂, hw₂, h0₂, hf₂⟩ := T.exists_mem_clSub (H.mul h) (C.mul h) (cl_mem_Vt hth)
  have hu'U : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ∈
      Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Submodule.mem_sup_right (sub_mem_commSpace _ _)
  have hfa : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ∈ fixMod S (S.Lbar g) (Vt S g t) := by
    intro l hl
    have hl' : S.ρ m * l * (S.ρ m)⁻¹ ∈ S.Lbar ((h : G) * g) := by
      rw [hLm, Lbar_mul S m g]; exact ⟨l, hl, rfl⟩
    have h1 := hf₂ _ hl'
    have hsame := map_conj_eq_of_commute _ (hcomm ⟨S.ρ m, hm⟩ ⟨l, Lbar_le_Rbar ht hl⟩)
    have h3 := congrArg (fun e => ((e (secMk (Vt S g t) hu'U) :
      ↥((Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map (Vt S g t).mkQ)) :
        S.Qt ⧸ Vt S g t)) hsame
    simp only [coe_secHom_mk] at h3
    have h2 : ((S.ρ m * l * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) -
          (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂) ∈ Vt S g t :=
      (Submodule.Quotient.eq _).mp h3
    have := sub_mem h1 h2
    rwa [sub_sub_sub_cancel_left] at this
  have hu'W := T.U_le_Wt hu'U
  have hR := radBound_of_tau_not_mem H C ht ht1 hVQ T.data.tau_not_mem
  have hPI := pairInt_of_radBound H C ht ht1 hVQ hR
  have hCab := sup_Vt_inf_sup_Vt H C ht ht1 hVQ hh hb
    (clSub_inf_clSub_le_Vt H C ht ht1 hVQ hh hb hR)
  have ha := (forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hu'W).mp hfa
  have hb' := (forall_apply_sub_mem_Vt_iff_b H hNo C ht ht1 hVQ hh hb hPI hu'W).mp hf₂
  have hV : (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) w₂ - w₂ ∈
      Vt S g t ⊓ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    ⟨hCab ▸ ⟨ha, hb'⟩, sub_mem_commSpace _ _⟩
  rw [T.inf₁, Submodule.mem_bot] at hV
  exact h0₂ hV

theorem false_of_le (hNo : NoA2 S g)
    (hKN : ∀ k ∈ Rbar S g t, (∀ x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t) → k ∈ Nbar S g t) : False := by
  classical
  have haQ := H.conj_mem
  set U := Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hU
  have hpt : ∀ v : {v : Vt S g t // v ≠ 0}, ∃ k : S.M, S.ρ k ∈ Rbar S g t ∧
      ((v : Vt S g t) : S.Qt) = S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
    intro v
    have hv0 : ((v : Vt S g t) : S.Qt) ≠ 0 := fun h => v.2 (Subtype.ext h)
    exact exists_of_mem_orbit (mem_orbit_of_ne_zero ht T.data.transitive (v : Vt S g t).2 hv0)
      haQ
  choose κ hκR hκv using hpt
  set F := fun v : {v : Vt S g t // v ≠ 0} =>
    U ⊓ fixMod S (S.Lbar (((κ v : S.M) : G) * g)) (Vt S g t) with hF
  have hVF : ∀ v, Vt S g t ≤ F v := fun v => le_inf le_sup_left fun x hx l hl =>
    sub_mem (apply_mem_Vt_of_mem_Rbar haQ
      (Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar H ht (hκR v)) hl) hx) hx
  have hdim : ∀ v, finrank (ZMod 2) (F v) = finrank (ZMod 2) (Vt S g t) + 2 := fun v => by
    change finrank (ZMod 2) ↥(U ⊓ fixMod S (S.Lbar (((κ v : S.M) : G) * g)) (Vt S g t)) = _
    rw [hU, ← T.map_Fix (hκR v) g, LinearEquiv.finrank_map_eq]
    exact T.finrank_Fix hNo
  set ℓ := fun v : {v : Vt S g t // v ≠ 0} => (F v).map (Vt S g t).mkQ with hℓ
  have hcard : ∀ v, 4 ≤ Nat.card (ℓ v) := fun v => by
    have h1 : finrank (ZMod 2) (ℓ v) + finrank (ZMod 2) (Vt S g t) = finrank (ZMod 2) (F v) :=
      finrank_map_mkQ_add (hVF v)
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have : finrank (ZMod 2) (ℓ v) = 2 := by have := hdim v; omega
    rw [this]; norm_num
  have hle : ∀ v, ℓ v ≤ U.map (Vt S g t).mkQ := fun v => Submodule.map_mono inf_le_left
  have hZ : Nat.card ↥(U.map (Vt S g t).mkQ) ≤ 16 := by
    have h1 : finrank (ZMod 2) ↥(U.map (Vt S g t).mkQ) + finrank (ZMod 2) (Vt S g t) =
        finrank (ZMod 2) U := finrank_map_mkQ_add le_sup_left
    have dU : finrank (ZMod 2) U = finrank (ZMod 2) (Vt S g t) + 4 := T.finrank_U
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    have : finrank (ZMod 2) ↥(U.map (Vt S g t).mkQ) = 4 := by
      have := T.data.finrank_eq; omega
    rw [this]; norm_num
  have hρv : ∀ v : {v : Vt S g t // v ≠ 0}, ((v : Vt S g t) : S.Qt) =
      ((S.ρ (κ v) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := fun v => by
    rw [hκv v, ρ_cl_conj_z S (κ v) haQ]
  have hdisj : ∀ v v', v ≠ v' → ℓ v ⊓ ℓ v' = ⊥ := by
    intro v v' hvv'
    set k : S.M := (κ v')⁻¹ * κ v with hk
    have hkR : S.ρ k ∈ Rbar S g t := by
      rw [hk, map_mul, map_inv]; exact mul_mem (inv_mem (hκR v')) (hκR v)
    have hc : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) := by
      intro e
      apply hvv'
      rw [← ρ_cl_conj_z S k haQ, hk, map_mul, map_inv, coe_mul_apply] at e
      have e2 := congrArg ((S.ρ (κ v') : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e
      rw [apply_inv_apply_O] at e2
      exact Subtype.ext (Subtype.ext ((hρv v).trans (e2.trans (hρv v').symm)))
    have h1 := T.inf_le_of_le hNo hKN hkR hc
    have h2 := Submodule.map_mono
      (f := ((S.ρ (κ v') : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap) h1
    have hVm : (Vt S g t).map ((S.ρ (κ v') : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap =
        Vt S g t := map_eq_of_forall (fun x hx => apply_mem_Vt_of_mem_Rbar haQ (hκR v') hx)
      (fun x hx => apply_mem_Vt_of_mem_Rbar haQ (inv_mem (hκR v')) hx)
    have e : ((κ v' : S.M) : G) * ((k : G) * g) = ((κ v : S.M) : G) * g := by
      rw [hk, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [Submodule.map_inf _ (LinearEquiv.injective _), T.map_Fix (hκR v') g,
      T.map_Fix (hκR v') ((k : G) * g), e, hVm] at h2
    have h3 : ℓ v ⊓ ℓ v' = (F v' ⊓ F v).map (Vt S g t).mkQ := by
      rw [inf_comm (ℓ v)]
      exact map_mkQ_inf_of_le (hVF v')
    rw [h3, eq_bot_iff]
    refine (Submodule.map_mono h2).trans ?_
    rw [Submodule.map_le_iff_le_comap, Submodule.comap_bot, Submodule.ker_mkQ]
  have : Finite (S.Qt ⧸ Vt S g t) := Module.finite_of_finite (ZMod 2)
  have h5 := card_le_five_of_pairwise_inf_eq_bot hZ ℓ hle hcard hdisj
  have : Fintype (Vt S g t) := Fintype.ofFinite _
  have h15 : Nat.card {v : Vt S g t // v ≠ 0} = 15 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      T.data.finrank_eq]
    norm_num
  omega

theorem false (hNo : NoA2 S g) : False := by
  by_cases hKN : ∀ k ∈ Rbar S g t, (∀ x ∈ Vt S g t ⊔ commSpace (τ₁ : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t) → k ∈ Nbar S g t
  · exact T.false_of_le hNo hKN
  · push Not at hKN
    obtain ⟨k, hkR, hk, hkN⟩ := hKN
    exact T.false_of_not_le hNo hkR hkN hk

end TriHyp

end CFSG.LargeExtraspecial.S9.RB
