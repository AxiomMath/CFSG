module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSixTotals

public section

namespace CFSG.QuasithinUnique.Ch1.AltSix
open Equiv Equiv.Perm CFSG.QuasithinUnique

theorem total_injective : Function.Injective total := fun i j h => total_inj i j h

theorem total_closed : ∀ (σ : Perm (Fin 6)) (i : Fin 6), ∃ j : Fin 6, act σ (total i) = total j := by
  intro σ
  have hσ : σ ∈ Submonoid.closure (Set.range fun a : Fin 5 => swap a.castSucc a.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    trivial
  induction hσ using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact total_closed_gen a
  | one => exact fun i => ⟨i, by rw [act_one]⟩
  | mul x y _ _ hx hy =>
    intro i
    obtain ⟨j, hj⟩ := hy i
    obtain ⟨k, hk⟩ := hx j
    exact ⟨k, by rw [act_mul, hj, hk]⟩

@[expose, irreducible] def epsFun (σ : Perm (Fin 6)) (i : Fin 6) : Fin 6 :=
  ((List.finRange 6).find? fun j => decide (act σ (total i) = total j)).getD 0

theorem act_total_epsFun (σ : Perm (Fin 6)) (i : Fin 6) :
    act σ (total i) = total (epsFun σ i) := by
  obtain ⟨j, hj⟩ := total_closed σ i
  have hs : ((List.finRange 6).find? fun k => decide (act σ (total i) = total k)).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨j, List.mem_finRange j, by simpa using hj⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hs
  have hpk := List.find?_some hk
  simp only [epsFun, hk, Option.getD_some]
  exact of_decide_eq_true hpk

theorem epsFun_mul (σ τ : Perm (Fin 6)) (i : Fin 6) :
    epsFun (σ * τ) i = epsFun σ (epsFun τ i) := by
  apply total_injective
  rw [← act_total_epsFun (σ * τ) i, ← act_total_epsFun σ (epsFun τ i), ← act_total_epsFun τ i,
    act_mul]

theorem epsFun_one (i : Fin 6) : epsFun 1 i = i := by
  apply total_injective
  rw [← act_total_epsFun 1 i, act_one]

@[expose] def epsEquiv (σ : Perm (Fin 6)) : Perm (Fin 6) where
  toFun := epsFun σ
  invFun := epsFun σ⁻¹
  left_inv := fun i => by rw [← epsFun_mul, inv_mul_cancel, epsFun_one]
  right_inv := fun i => by rw [← epsFun_mul, mul_inv_cancel, epsFun_one]

theorem epsEquiv_apply (σ : Perm (Fin 6)) (i : Fin 6) : epsEquiv σ i = epsFun σ i := rfl

@[expose] def epsPerm : Perm (Fin 6) →* Perm (Fin 6) where
  toFun := epsEquiv
  map_one' := by
    apply Equiv.ext
    intro i
    rw [epsEquiv_apply, epsFun_one]
    rfl
  map_mul' := by
    intro σ τ
    apply Equiv.ext
    intro i
    rw [epsEquiv_apply, Perm.mul_apply, epsEquiv_apply, epsEquiv_apply]
    exact epsFun_mul σ τ i

@[expose] def tabOf (σ : Perm (Fin 6)) : List (Fin 6) := List.ofFn fun i => σ i

theorem tabOf_getD (σ : Perm (Fin 6)) (i : Fin 6) : (tabOf σ).getD i.val 0 = σ i := by
  fin_cases i <;> simp [tabOf, List.getD_eq_getElem?_getD]

@[expose] def flat (σ : Perm (Fin 6)) : Perm (Fin 6) where
  toFun := let t := tabOf σ; fun i => t.getD i.val 0
  invFun := let t := tabOf σ⁻¹; fun i => t.getD i.val 0
  left_inv := fun i => by
    simp only [tabOf_getD]
    simp
  right_inv := fun i => by
    simp only [tabOf_getD]
    simp

@[expose] def permKey (σ : Perm (Fin 6)) : ℕ :=
  (σ 0).val + 6 * ((σ 1).val + 6 * ((σ 2).val + 6 * ((σ 3).val + 6 * ((σ 4).val +
    6 * (σ 5).val))))

@[expose] def epsTable : Array (Perm (Fin 6)) :=
  (permsOfList (List.finRange 6)).foldl (fun t a => t.set! (permKey a) (flat (epsPerm a)))
    (Array.replicate 46656 1)

@[expose] def epsFast (a : Perm (Fin 6)) : Perm (Fin 6) := epsTable.getD (permKey a) 1

@[expose] def twist : Bool → Perm (Fin 6) → Perm (Fin 6)
  | false, a => a
  | true, a => epsFast a

@[expose] def phi (σ : Perm (Fin 6)) (b : Bool) (a : Perm (Fin 6)) : Perm (Fin 6) :=
  σ * twist b a * σ⁻¹

@[expose] def DatumPremise (σ : Perm (Fin 6)) (b : Bool) : Prop :=
  (∀ a : Perm (Fin 6), Perm.sign a = 1 → phi σ b (phi σ b a) = a) ∧
    8 ∣ (Finset.univ.filter fun a : Perm (Fin 6) => Perm.sign a = 1 ∧ phi σ b a = a).card ∧
    ∃ a : Perm (Fin 6), Perm.sign a = 1 ∧ phi σ b a ≠ a

instance (σ : Perm (Fin 6)) (b : Bool) : Decidable (DatumPremise σ b) := by
  unfold DatumPremise
  infer_instance

end CFSG.QuasithinUnique.Ch1.AltSix
