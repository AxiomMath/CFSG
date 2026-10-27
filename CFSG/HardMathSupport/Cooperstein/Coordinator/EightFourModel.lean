module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightOfData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open Equiv Equiv.Perm CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

@[expose] def dtA : Perm (Fin 4) := swap 0 1 * swap 2 3

@[expose] def dtB : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def dtC : Perm (Fin 4) := swap 0 3 * swap 1 2

@[expose] def kleinFin4 : Subgroup (Perm (Fin 4)) where
  carrier := {σ | σ = 1 ∨ σ = dtA ∨ σ = dtB ∨ σ = dtC}
  mul_mem' := by
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp only [Set.mem_ofPred_eq] <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    rintro a (rfl | rfl | rfl | rfl) <;> simp only [Set.mem_ofPred_eq] <;> decide

set_option maxRecDepth 100000 in
private theorem kleinFin4_conj_aux : ∀ g : Perm (Fin 4),
    (g * dtA * g⁻¹ = dtA ∨ g * dtA * g⁻¹ = dtB ∨ g * dtA * g⁻¹ = dtC) ∧
    (g * dtB * g⁻¹ = dtA ∨ g * dtB * g⁻¹ = dtB ∨ g * dtB * g⁻¹ = dtC) ∧
    (g * dtC * g⁻¹ = dtA ∨ g * dtC * g⁻¹ = dtB ∨ g * dtC * g⁻¹ = dtC) := by
  decide

instance kleinFin4_normal : kleinFin4.Normal := ⟨fun a ha g => by
  rcases ha with rfl | rfl | rfl | rfl
  · exact Or.inl (by group)
  · exact Or.inr (kleinFin4_conj_aux g).1
  · exact Or.inr (kleinFin4_conj_aux g).2.1
  · exact Or.inr (kleinFin4_conj_aux g).2.2⟩

theorem kleinFin4_mul_self {a : Perm (Fin 4)} (ha : a ∈ kleinFin4) : a * a = 1 := by
  rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem exists_kleinFin4_apply (i j : Fin 4) : ∃ π ∈ kleinFin4, π i = j := by
  have h : ∀ i j : Fin 4, (1 : Perm (Fin 4)) i = j ∨ dtA i = j ∨ dtB i = j ∨ dtC i = j := by
    decide
  rcases h i j with h | h | h | h
  · exact ⟨1, Or.inl rfl, h⟩
  · exact ⟨dtA, Or.inr (Or.inl rfl), h⟩
  · exact ⟨dtB, Or.inr (Or.inr (Or.inl rfl)), h⟩
  · exact ⟨dtC, Or.inr (Or.inr (Or.inr rfl)), h⟩

section PTilde

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

variable (Γ) in
@[expose] noncomputable def pTildeKlein : Subgroup ↥(pTilde (Fin 4) Γ) :=
  (kleinFin4.prod (⊥ : Subgroup (Perm Γ))).comap (eightAction (Fin 4) Γ)

theorem mem_pTildeKlein_iff (p : ↥(pTilde (Fin 4) Γ)) :
    p ∈ pTildeKlein Γ ↔ (eightAction (Fin 4) Γ p).1 ∈ kleinFin4 ∧ p.1.2 = 1 := by
  simp only [pTildeKlein, Subgroup.mem_comap, Subgroup.mem_prod, Subgroup.mem_bot, eightAction_snd]

theorem pTildeKlein_le_pCore : pTildeKlein Γ ≤ CFSG.pCore 2 ↥(pTilde (Fin 4) Γ) := by
  have hn : (pTildeKlein Γ).Normal := Subgroup.Normal.comap inferInstance _
  have hp : IsPGroup 2 (kleinFin4.prod (⊥ : Subgroup (Perm Γ))) := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    have hx := Subgroup.mem_prod.1 x.2
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    refine Prod.ext ?_ ?_
    · exact kleinFin4_mul_self hx.1
    · rw [Prod.snd_mul, Subgroup.mem_bot.1 hx.2, mul_one, Prod.snd_one]
  exact le_sSup ⟨hn, hp.comap_of_ker_isPGroup _ isPGroup_ker_eightAction⟩

theorem exists_pTildeKlein (π : Perm (Fin 4)) (hπ : π ∈ kleinFin4) (t : Perm (Fin 4 × Bool))
    (ht : ∀ z, (t z).1 = z.1) (hts : sign t = 1) :
    ∃ p ∈ pTildeKlein Γ, p.1.1 = t * wLift π := by
  have hw : t * wLift π ∈ wStab (Fin 4) Bool :=
    mul_mem (mem_wStab.2 fun x y => by rw [ht, ht]) (wLift_mem_wStab π)
  have hs : sign (t * wLift π) * sign (1 : Perm Γ) = 1 := by
    rw [map_mul, hts, wLift_sign (by decide) π, map_one]; rfl
  refine ⟨⟨(t * wLift π, 1), hw, hs⟩, ?_, rfl⟩
  rw [mem_pTildeKlein_iff]
  refine ⟨?_, rfl⟩
  have h : (eightAction (Fin 4) Γ ⟨(t * wLift π, 1), hw, hs⟩).1 = π := by
    refine Equiv.ext fun k => ?_
    have h1 := eightAction_fst_apply (Γ := Γ) ⟨(t * wLift π, 1), hw, hs⟩ (k, false)
    rw [h1]
    show (t (wLift π (k, false))).1 = π k
    rw [ht, wLift_apply]
  rw [h]
  exact hπ

@[expose] def flipTwo (j k : Fin 4) : Perm (Fin 4 × Bool) :=
  swap (j, false) (j, true) * swap (k, false) (k, true)

theorem flipTwo_fst (j k : Fin 4) (z : Fin 4 × Bool) : (flipTwo j k z).1 = z.1 := by
  revert j k z; decide

theorem sign_flipTwo (j k : Fin 4) : sign (flipTwo j k) = 1 := by
  rw [flipTwo, map_mul, sign_swap (by simp), sign_swap (by simp)]; rfl

theorem flipTwo_apply_left {j k : Fin 4} (hjk : j ≠ k) (b : Bool) :
    flipTwo j k (j, b) = (j, !b) := by
  revert j k b; decide

theorem exists_mem_pTildeKlein_apply (x y : Fin 4 × Bool) :
    ∃ p ∈ pTildeKlein Γ, p.1.1 x = y := by
  obtain ⟨π, hπ, hπx⟩ := exists_kleinFin4_apply x.1 y.1
  by_cases hb : x.2 = y.2
  · obtain ⟨p, hp, hp1⟩ := exists_pTildeKlein (Γ := Γ) π hπ 1 (fun _ => rfl) (map_one _)
    refine ⟨p, hp, ?_⟩
    rw [hp1, one_mul]
    show wLift π (x.1, x.2) = y
    rw [wLift_apply, hπx, hb]
  · obtain ⟨k, hk⟩ : ∃ k : Fin 4, y.1 ≠ k := by
      by_cases h0 : y.1 = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, h0⟩
    obtain ⟨p, hp, hp1⟩ := exists_pTildeKlein (Γ := Γ) π hπ (flipTwo y.1 k) (flipTwo_fst y.1 k)
      (sign_flipTwo y.1 k)
    refine ⟨p, hp, ?_⟩
    rw [hp1]
    show flipTwo y.1 k (wLift π (x.1, x.2)) = y
    rw [wLift_apply, hπx, flipTwo_apply_left hk]
    refine Prod.ext rfl ?_
    show (!x.2) = y.2
    revert hb
    cases x.2 <;> cases y.2 <;> decide

end PTilde

@[expose] def cycThree : Perm (Fin 4 × Bool) :=
  swap (0, false) (0, true) * swap (0, true) (1, false)

theorem sign_cycThree : sign cycThree = 1 := by
  rw [cycThree, map_mul, sign_swap (by decide), sign_swap (by decide)]; rfl

theorem cycThree_not_mem_wStab : cycThree ∉ wStab (Fin 4) Bool := by
  intro h
  have h1 := (mem_wStab.1 h) (0, false) (0, true)
  revert h1
  decide

@[expose] def cycE (s : ℕ) : AltE 4 s :=
  ⟨Perm.sumCongr cycThree 1, by
    rw [mem_alternatingGroup, sign_sumCongr, sign_cycThree, map_one, one_mul]⟩

theorem cycE_apply_inr (s : ℕ) (j : Fin s) :
    ((cycE s : AltE 4 s) : Perm (OmegaE 4 s)) (Sum.inr j) = Sum.inr j := rfl

theorem cycE_not_mem_eightN (s : ℕ) : cycE s ∉ eightN 4 s := by
  rintro ⟨⟨a, b⟩, hp, hab⟩
  have h1 : Perm.sumCongrHom (Fin 4 × Bool) (Fin s) (a, b) =
      Perm.sumCongrHom (Fin 4 × Bool) (Fin s) (cycThree, 1) := hab.trans rfl
  have h2 := Perm.sumCongrHom_injective h1
  exact cycThree_not_mem_wStab ((Prod.mk.inj h2).1 ▸ hp.1)

theorem exists_equiv_of_altEquiv {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (hα : Fintype.card α = n)
    (φ : ↥(alternatingGroup α) ≃* ↥(alternatingGroup (Fin n))) :
    ∃ ε : α ≃ Fin n, ∀ (x : ↥(alternatingGroup α)) (a : α),
      ((φ x : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) (ε a) = ε ((x : Perm α) a) := by
  let e₀ : α ≃ Fin n := Fintype.equivFinOfCardEq hα
  let β : MulAut ↥(alternatingGroup (Fin n)) := (Equiv.altCongrHom e₀).symm.trans φ
  obtain ⟨τ, hτ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).2 β
  refine ⟨e₀.trans τ, fun x a => ?_⟩
  have h1 : φ x = β (Equiv.altCongrHom e₀ x) := by
    simp only [β, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h2 : ((β (Equiv.altCongrHom e₀ x) : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) =
      τ * ((Equiv.altCongrHom e₀ x : ↥(alternatingGroup (Fin n))) : Perm (Fin n)) * τ⁻¹ := by
    rw [← hτ]
    exact MulAut.conjNormal_apply τ _
  rw [h1, h2]
  show (τ * e₀.permCongr (x : Perm α) * τ⁻¹) (τ (e₀ a)) = τ (e₀ ((x : Perm α) a))
  rw [Perm.mul_apply, Perm.mul_apply, show τ⁻¹ (τ (e₀ a)) = e₀ a from τ.symm_apply_apply _,
    Equiv.permCongr_apply, Equiv.symm_apply_apply]

end CFSG.HardMathSupport.Cooperstein.Coordinator
