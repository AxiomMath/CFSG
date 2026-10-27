module

public import CFSG.CGT.Stroth77.NonSplitCore.Cert

public section

namespace CFSG.CGT.Stroth77.Core

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm Function
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
  CFSG.Permutation.SymmetricCoxeter

variable {G : Type*} [Group G]

theorem list_sum_apply {α A B : Type*} [AddCommMonoid A] [AddCommMonoid B] (L : List α)
    (f : α → A →+ B) (x : A) : (L.map f).sum x = (L.map fun a => f a x).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

@[expose] noncomputable def mkExt (θ : G →* Perm (Fin 6)) (hθ : Surjective θ)
    (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G)) : Ext G (Perm (Fin 6)) U4 where
  θ := θ
  θ_surj := hθ
  ι :=
    { toFun := fun u => (ψ (Multiplicative.ofAdd (coordE.symm u.toAdd)) : G)
      map_one' := by
        show ((ψ (Multiplicative.ofAdd (coordE.symm (0 : U4)))) : G) = 1
        rw [map_zero, ofAdd_zero, map_one]; rfl
      map_mul' := fun a b => by
        show ((ψ (Multiplicative.ofAdd (coordE.symm (a.toAdd + b.toAdd)))) : G) = _
        rw [map_add, ofAdd_add, map_mul]; rfl }
  ι_inj := fun a b h => by
    have h1 := ψ.injective (Subtype.ext h)
    simpa using h1
  mem_range g hg := ⟨Multiplicative.ofAdd (coordE (ψ.symm ⟨g, hg⟩).toAdd), by simp⟩
  θ_ι u := (ψ (Multiplicative.ofAdd (coordE.symm u.toAdd))).2
  act := actC
  conj g u := by
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [hconj]
    congr 3
    apply coordE.injective
    rw [coordE_altAct]
    simp only [toAdd_ofAdd, AddEquiv.apply_symm_apply]
    rfl
  two u := funext fun _ => zmod2_add_self _

theorem mkExt_ι {θ : G →* Perm (Fin 6)} {hθ : Surjective θ}
    {ψ : Multiplicative (altHeart 6) ≃* θ.ker} {hconj} (u : U4) :
    (mkExt θ hθ ψ hconj).ι (Multiplicative.ofAdd u) =
      (ψ (Multiplicative.ofAdd (coordE.symm u)) : G) := rfl

theorem comm_of_eq_one {a b : G} (h : a * (b * (a⁻¹ * (b⁻¹ * 1))) = 1) : a * b = b * a := by
  calc a * b = a * (b * (a⁻¹ * (b⁻¹ * 1))) * (b * a) := by group
    _ = b * a := by rw [h, one_mul]

theorem braid_of_eq_one {a b : G} (h : a * (b * (a * (b⁻¹ * (a⁻¹ * (b⁻¹ * 1))))) = 1) :
    a * b * a = b * a * b := by
  calc a * b * a = a * (b * (a * (b⁻¹ * (a⁻¹ * (b⁻¹ * 1))))) * (b * a * b) := by group
    _ = b * a * b := by rw [h, one_mul]

theorem titsVal_pair : ∀ k : Fin 5, titsVal (Fin.castLE (by omega) k) =
    coordFun fun p => (if p = k.castSucc then 1 else 0) + (if p = k.succ then 1 else 0) := by
  decide

theorem titsVal_eq_zero : ∀ j : Fin 15, 5 ≤ j.val → titsVal j = 0 := by decide

theorem exists_lifts_normalized
    (θ : G →* Perm (Fin 6)) (hθ : Surjective θ)
    (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G)) :
    ∃ (t : Fin 5 → G) (c : ZMod 2), (∀ k, θ (t k) = sw k) ∧
      ∀ j, evalW t (rel j) = (mkExt θ hθ ψ hconj).ι (Multiplicative.ofAdd (c • titsVal j)) := by
  set X := mkExt θ hθ ψ hconj
  let t0 : Fin 5 → G := fun k => X.sec (sw k)
  have ht0 : ∀ k, X.θ (t0 k) = sw k := fun k => X.θ_sec _
  let v : Fin 15 → U4 := fun j => X.relVal t0 (rel j)
  have hv : ∀ i, cycHom i v = 0 := fun i => by
    have := X.sum_act_relVal_eq_zero ht0 ((cycles i).map fun c => (vtx c.1, rel c.2))
      (fun c hc => by
        obtain ⟨d, -, rfl⟩ := List.mem_map.1 hc
        exact rel_eq_one d.2) (cycles_even i)
    rw [List.map_map] at this
    rw [cycHom, list_sum_apply]
    exact this
  refine ⟨X.adjust t0 (corr v), lamHom v, X.θ_adjust ht0 _, fun j => ?_⟩
  rw [← X.ι_relVal (X.θ_adjust ht0 _) (rel_eq_one j), X.relVal_adjust ht0 _ (rel_eq_one j)]
  exact congrArg _ (congrArg _ (normalize v hv j))

theorem exists_tits_lifts
    (θ : G →* Perm (Fin 6)) (hθ : Surjective θ)
    (ψ : Multiplicative (altHeart 6) ≃* θ.ker)
    (hconj : ∀ (g : G) (v : Multiplicative (altHeart 6)), g * (ψ v : G) * g⁻¹ =
      (ψ (Multiplicative.ofAdd (altAct (θ g) v.toAdd)) : G))
    (hns : ¬ ∃ K : Subgroup G, θ.ker ⊓ K = ⊥ ∧ θ.ker ⊔ K = ⊤) :
    ∃ t : ℕ → G, (∀ k < 5, θ (t k) = adjSwap 5 k) ∧
      (∀ (k : ℕ) (hk : k < 5), t k * t k = (ψ (Multiplicative.ofAdd
        ((pairEW ⟨k, by omega⟩ ⟨k + 1, by omega⟩ : evenWeight 6) : altHeart 6)) : G)) ∧
      (∀ k, k + 1 < 5 → t k * t (k + 1) * t k = t (k + 1) * t k * t (k + 1)) ∧
      (∀ k l, k + 2 ≤ l → l < 5 → t k * t l = t l * t k) := by
  obtain ⟨t1, c, ht1, hrel⟩ := exists_lifts_normalized θ hθ ψ hconj
  set X := mkExt θ hθ ψ hconj
  have h1 : ∀ j : Fin 15, 5 ≤ j.val → evalW t1 (rel j) = 1 := fun j hj => by
    rw [hrel, titsVal_eq_zero j hj, smul_zero, ofAdd_zero, map_one]
  let t : ℕ → G := fun k => if h : k < 5 then t1 ⟨k, h⟩ else 1
  have hbr : ∀ k, k + 1 < 5 → t k * t (k + 1) * t k = t (k + 1) * t k * t (k + 1) := by
    intro k hk
    apply braid_of_eq_one
    have hk' : k < 4 := by omega
    interval_cases k
    · exact h1 5 (by decide)
    · exact h1 6 (by decide)
    · exact h1 7 (by decide)
    · exact h1 8 (by decide)
  have hcm : ∀ k l, k + 2 ≤ l → l < 5 → t k * t l = t l * t k := by
    intro k l hkl hl
    apply comm_of_eq_one
    have hk : k < 3 := by omega
    interval_cases k <;> interval_cases l <;> first
      | omega
      | exact h1 9 (by decide)
      | exact h1 10 (by decide)
      | exact h1 11 (by decide)
      | exact h1 12 (by decide)
      | exact h1 13 (by decide)
      | exact h1 14 (by decide)
  have hθt : ∀ k < 5, θ (t k) = adjSwap 5 k := fun k hk => by
    simp only [t, dif_pos hk]
    exact ht1 ⟨k, hk⟩
  rcases zmod_two_cases c with rfl | rfl
  ·
    exfalso
    have hsq : ∀ k < 5, t k * t k = 1 := fun k hk => by
      have := hrel ⟨k, by omega⟩
      rw [zero_smul, ofAdd_zero, map_one] at this
      simp only [t, dif_pos hk]
      interval_cases k <;> simpa [rel, relL, evalW] using this
    obtain ⟨h, hh⟩ := exists_hom_perm 5 t ⟨hsq, hbr, hcm⟩
    have hθh : θ.comp h = MonoidHom.id _ := by
      refine MonoidHom.eq_of_eqOn_dense (closure_adjSwap 5) fun x hx => ?_
      obtain ⟨i, hi, rfl⟩ := hx
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hh i hi]
      exact hθt i hi
    have hθh' : ∀ σ, θ (h σ) = σ := fun σ => DFunLike.congr_fun hθh σ
    refine hns ⟨h.range, ?_, ?_⟩
    · refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨hx1, σ, rfl⟩ := hx
      have : σ = 1 := by rw [← hθh' σ]; exact hx1
      rw [this, map_one]; rfl
    · refine eq_top_iff.2 fun x _ => ?_
      have hx : x = (x * (h (θ x))⁻¹) * h (θ x) := by group
      rw [hx]
      refine Subgroup.mul_mem_sup ?_ ⟨θ x, rfl⟩
      show θ (x * (h (θ x))⁻¹) = 1
      rw [map_mul, map_inv, hθh', mul_inv_cancel]
  ·
    refine ⟨t, hθt, fun k hk => ?_, hbr, hcm⟩
    have := hrel ⟨k, by omega⟩
    rw [one_smul, mkExt_ι] at this
    simp only [t, dif_pos hk]
    have e : coordE.symm (titsVal ⟨k, by omega⟩) =
        ((pairEW ⟨k, by omega⟩ ⟨k + 1, by omega⟩ : evenWeight 6) : altHeart 6) := by
      apply coordE.injective
      rw [AddEquiv.apply_symm_apply, coordE_pairEW]
      exact titsVal_pair ⟨k, hk⟩
    rw [← e, ← this]
    interval_cases k <;> simp [rel, relL, evalW]

end CFSG.CGT.Stroth77.Core
