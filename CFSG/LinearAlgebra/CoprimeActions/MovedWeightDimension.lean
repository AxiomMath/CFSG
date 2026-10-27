module


public import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

public section

namespace CFSG.LinearAlgebra.CoprimeActions.MovedWeightDimension

open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

theorem bound {F V E : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Group E] (τ : Representation F E V) (σ : V ≃ₗ[F] V) (α : MulAut E) (q : ℕ)
    (hq : q.Prime) (hα : α ^ q = 1)
    (hcov : ∀ g v, σ (τ g v) = τ (α g) (σ v))
    (χ : E →* Fˣ) (hχ : weightSpace τ χ ≠ ⊥) (hmove : χ.comp α.toMonoidHom ≠ χ) :
    q ≤ Module.finrank F V := by
  let P (β : MulAut E) (χ : E →* Fˣ) (n : ℕ) :
      E →* Fˣ := χ.comp (β ^ n).toMonoidHom
  have P_add (β : MulAut E) (χ : E →* Fˣ) (a b : ℕ) :
      P β χ (a + b) = (P β χ a).comp (β ^ b).toMonoidHom := by
    ext g; simp [P, pow_add]
  have P_zero (β : MulAut E) (χ : E →* Fˣ) :
      P β χ 0 = χ := by
    ext g; simp [P]
  have P_one (β : MulAut E) (χ : E →* Fˣ) :
      P β χ 1 = χ.comp β.toMonoidHom := by
    ext g; simp [P]
  have P_mod (β : MulAut E) (r : ℕ) (hβ : β ^ r = 1)
      (χ : E →* Fˣ) (n : ℕ) : P β χ (n % r) = P β χ n := by
    have : β ^ (n % r) = β ^ n := by
      conv_rhs => rw [← Nat.mod_add_div n r, pow_add, pow_mul, hβ, one_pow, mul_one]
    simp [P, this]
  have P_inj (β : MulAut E) (r : ℕ) [hr : Fact r.Prime]
      (hβ : β ^ r = 1) (χ : E →* Fˣ) (hχ : χ.comp β.toMonoidHom ≠ χ) (i j : ℕ) (hij : i < j)
      (hj : j < r) : P β χ i ≠ P β χ j := by
    intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij

    set k' := k + 1 with hk'
    have h1 : P β χ (i + k') = (P β χ k').comp (β ^ i).toMonoidHom := by
      rw [add_comm]; exact P_add β χ k' i
    have h2 : P β χ i = (P β χ 0).comp (β ^ i).toMonoidHom := by
      have := P_add β χ 0 i; simpa using this
    have h3 : P β χ k' = P β χ 0 := by
      have hs : Function.Surjective (β ^ i).toMonoidHom := fun y => ⟨(β ^ i).symm y, by simp⟩
      rw [← MonoidHom.cancel_right hs, ← h1, ← h2]
      exact h.symm
    have hcop : Nat.Coprime k' r := by
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hr.out).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.out.one_lt
    have h4 : ∀ n, P β χ (k' * n) = χ := by
      intro n
      induction n with
      | zero => simpa using P_zero β χ
      | succ n ih =>
        rw [Nat.mul_succ, P_add, ih]
        exact h3.trans (P_zero β χ)
    apply hχ
    rw [← P_one, ← hm, P_mod β r hβ, h4]
  have map_weight (τ : Representation F E V) (σ : V ≃ₗ[F] V) (α : MulAut E)
      (hcov : ∀ g v, σ (τ g v) = τ (α g) (σ v)) (χ : E →* Fˣ) (v : V)
      (hv : v ∈ weightSpace τ χ) :
      σ v ∈ weightSpace τ (χ.comp (α⁻¹).toMonoidHom) := by
    intro g
    have h := hcov (α⁻¹ g) v
    have e : α (α⁻¹ g) = g := by simp
    rw [e] at h
    rw [← h, hv, map_smul]
    simp
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  set β : MulAut E := α⁻¹ with hβdef
  have hβ : β ^ q = 1 := by rw [hβdef, inv_pow, hα, inv_one]
  have hχ' : χ.comp β.toMonoidHom ≠ χ := by
    intro h
    apply hmove
    refine MonoidHom.ext fun g => ?_
    have := DFunLike.congr_fun h (α g)
    simpa [hβdef] using this.symm
  have hmap : ∀ n v, v ∈ weightSpace τ (P β χ n) → σ v ∈ weightSpace τ (P β χ (n + 1)) := by
    intro n v hv
    have := map_weight τ σ α hcov _ v hv
    have e : P β χ (n + 1) = (P β χ n).comp (α⁻¹).toMonoidHom := by
      rw [P_add]; ext g; simp [P, hβdef]
    rw [e]; exact this
  have hne : ∀ n : ℕ, weightSpace τ (P β χ n) ≠ ⊥ := by
    intro n
    induction n with
    | zero => rw [P_zero]; exact hχ
    | succ n ih =>
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ih
      intro hbot
      have := hmap n v hv
      rw [hbot] at this
      exact hv0 (σ.injective (by simpa using this))
  have hinj : Function.Injective (fun i : Fin q => P β χ i) := by
    intro i j hij
    by_contra hn
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hn) with h | h
    · exact P_inj β q hβ χ hχ' i j h j.2 hij
    · exact P_inj β q hβ χ hχ' j i h i.2 hij.symm
  have hind := independent τ (fun i : Fin q => P β χ i) hinj
  have := hind.subtype_ne_bot_le_finrank
  have hall : Fintype.card { i : Fin q // weightSpace τ (P β χ i) ≠ ⊥ } = q := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun x : Fin q => weightSpace τ (P β χ x) ≠ ⊥) = Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => hne (i : ℕ))
    rw [this]
    simp
  rw [hall] at this
  exact this

end CFSG.LinearAlgebra.CoprimeActions.MovedWeightDimension
