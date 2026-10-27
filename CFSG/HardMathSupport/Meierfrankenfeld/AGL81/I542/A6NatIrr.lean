module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6NatBlock
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6NatRestrict

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X3E

variable {S : Type} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]

@[expose] noncomputable def unitLE : (Module.End (ZMod 2) S)ˣ →* (S ≃ₗ[ZMod 2] S) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S).toMonoidHom

theorem inv_apply_mem_of_forall (u : (Module.End (ZMod 2) S)ˣ) (N : Submodule (ZMod 2) S)
    (h : ∀ v ∈ N, (u : Module.End (ZMod 2) S) v ∈ N) :
    ∀ v ∈ N, ((u⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v ∈ N := by
  intro v hv
  have : FiniteDimensional (ZMod 2) S := Module.Finite.of_finite
  have hmap : N.map (unitLE u : S →ₗ[ZMod 2] S) = N := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (LinearEquiv.finrank_map_eq (unitLE u) N)
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  rw [← hmap] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  have : ((u⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
      ((u : Module.End (ZMod 2) S) w) = w := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  show ((u⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
    ((u : Module.End (ZMod 2) S) w) ∈ N
  rw [this]
  exact hw

theorem sup_invariant {Y A : Subgroup (Module.End (ZMod 2) S)ˣ} {N : Submodule (ZMod 2) S}
    (hY : ∀ y ∈ Y, ∀ v ∈ N, (y : Module.End (ZMod 2) S) v ∈ N)
    (hA : ∀ a ∈ A, ∀ v ∈ N, (a : Module.End (ZMod 2) S) v ∈ N) :
    ∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N := by
  intro d hd
  rw [Subgroup.sup_eq_closure] at hd
  refine Subgroup.closure_induction
    (p := fun (d : (Module.End (ZMod 2) S)ˣ) _ => ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N)
    ?_ ?_ ?_ ?_ hd
  · intro x hx
    rcases hx with hx | hx
    · exact hY x hx
    · exact hA x hx
  · intro v hv
    simpa using hv
  · intro x y _ _ hx hy v hv
    rw [Units.val_mul, Module.End.mul_apply]
    exact hx _ (hy v hv)
  · intro x _ hx
    exact inv_apply_mem_of_forall x N hx

theorem c3A6_ne_one : c3A6 ≠ 1 := fun h => gx_ne_one (congrArg Subtype.val h)

section Irr

variable {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}

omit [Finite S] in
theorem nontrivial_of_eY (eY : ↥Y ≃* alternatingGroup (Fin 6)) : Nontrivial S := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  have h1 : ((eY.symm c3A6 : ↥Y) : (Module.End (ZMod 2) S)ˣ) = 1 :=
    Units.ext (LinearMap.ext fun v => Subsingleton.elim _ _)
  have h2 : eY.symm c3A6 = 1 := Subtype.ext h1
  exact c3A6_ne_one (by simpa using congrArg eY h2)

theorem a6_irreducible
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ))
    (eY : ↥Y ≃* alternatingGroup (Fin 6)) (hdim : Module.finrank (ZMod 2) S ≤ 6) :
    ∀ N : Submodule (ZMod 2) S, (∀ y ∈ Y, ∀ v ∈ N, (y : Module.End (ZMod 2) S) v ∈ N) →
      N = ⊥ ∨ N = ⊤ := by
  classical
  have hnt : Nontrivial S := nontrivial_of_eY eY
  have hfd : FiniteDimensional (ZMod 2) S := Module.Finite.of_finite
  let σ : S6 →* (S ≃ₗ[ZMod 2] S) := unitLE.comp (Y.subtype.comp eY.symm.toMonoidHom)
  have hσ : ∀ g v, σ g v = (((eY.symm g : ↥Y) : (Module.End (ZMod 2) S)ˣ) :
      Module.End (ZMod 2) S) v := fun _ _ => rfl
  have hσinv : ∀ N : Submodule (ZMod 2) S,
      (∀ y ∈ Y, ∀ v ∈ N, (y : Module.End (ZMod 2) S) v ∈ N) → ∀ g : S6, ∀ n ∈ N, σ g n ∈ N :=
    fun N hN g n hn => hN _ (eY.symm g).2 n hn
  have hσinv' : ∀ N : Submodule (ZMod 2) S, (∀ g : S6, ∀ n ∈ N, σ g n ∈ N) →
      ∀ y ∈ Y, ∀ v ∈ N, (y : Module.End (ZMod 2) S) v ∈ N := by
    intro N hN y hy v hv
    have := hN (eY ⟨y, hy⟩) v hv
    rwa [hσ, MulEquiv.symm_apply_apply] at this
  have hconj : ∀ a ∈ A, ∀ y ∈ Y, a⁻¹ * y * a ∈ Y := by
    intro a ha y hy
    have := (Subgroup.mem_normalizer_iff.1 (hAN (A.inv_mem ha)) y).1 hy
    simpa using this
  have hy0 : ((eY.symm c3A6 : ↥Y) : (Module.End (ZMod 2) S)ˣ) ≠ 1 := by
    intro h
    have h2 : eY.symm c3A6 = 1 := Subtype.ext h
    exact c3A6_ne_one (by simpa using congrArg eY h2)
  have hex : ∃ n, ∃ M : Submodule (ZMod 2) S,
      (∀ y ∈ Y, ∀ v ∈ M, (y : Module.End (ZMod 2) S) v ∈ M) ∧ M ≠ ⊥ ∧
        Module.finrank (ZMod 2) M = n :=
    ⟨_, ⊤, fun y _ v _ => trivial, top_ne_bot, rfl⟩
  obtain ⟨M, hMY, hM0, hMmin⟩ : ∃ M : Submodule (ZMod 2) S,
      (∀ y ∈ Y, ∀ v ∈ M, (y : Module.End (ZMod 2) S) v ∈ M) ∧ M ≠ ⊥ ∧
        ∀ N : Submodule (ZMod 2) S, (∀ y ∈ Y, ∀ v ∈ N, (y : Module.End (ZMod 2) S) v ∈ N) →
          N ≠ ⊥ → Module.finrank (ZMod 2) M ≤ Module.finrank (ZMod 2) N := by
    obtain ⟨M, hMY, hM0, hMn⟩ := Nat.find_spec hex
    refine ⟨M, hMY, hM0, fun N hN hN0 => ?_⟩
    rw [hMn]
    exact Nat.find_min' hex ⟨N, hN, hN0, rfl⟩
  have hmin : ∀ N : Submodule (ZMod 2) S,
      (∀ y ∈ Y, ∀ v ∈ N, (y : Module.End (ZMod 2) S) v ∈ N) → N ≠ ⊥ → N ≤ M → N = M :=
    fun N hN hN0 hle => Submodule.eq_of_le_of_finrank_le hle (hMmin N hN hN0)
  have hnotriv : ¬ ∀ y ∈ Y, ∀ v ∈ M, (y : Module.End (ZMod 2) S) v = v := by
    intro htriv
    let F : Submodule (ZMod 2) S :=
      { carrier := {v | ∀ y ∈ Y, (y : Module.End (ZMod 2) S) v = v}
        add_mem' := fun {a b} ha hb y hy => by rw [map_add, ha y hy, hb y hy]
        zero_mem' := fun y _ => map_zero _
        smul_mem' := fun c v hv y hy => by rw [map_smul, hv y hy] }
    have hFY : ∀ y ∈ Y, ∀ v ∈ F, (y : Module.End (ZMod 2) S) v ∈ F := by
      intro y hy v hv y' hy'
      have := hv y hy
      rw [this]
      exact hv y' hy'
    have hFA : ∀ a ∈ A, ∀ v ∈ F, (a : Module.End (ZMod 2) S) v ∈ F := by
      intro a ha v hv y hy
      have h1 := hv _ (hconj a ha y hy)
      have h2 : (y : Module.End (ZMod 2) S) ((a : Module.End (ZMod 2) S) v) =
          (a : Module.End (ZMod 2) S) (((a⁻¹ * y * a : (Module.End (ZMod 2) S)ˣ) :
            Module.End (ZMod 2) S) v) := by
        have e : y * a = a * (a⁻¹ * y * a) := by group
        calc (y : Module.End (ZMod 2) S) ((a : Module.End (ZMod 2) S) v)
            = ((y * a : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v := rfl
          _ = ((a * (a⁻¹ * y * a) : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v := by
            rw [e]
          _ = _ := rfl
      rw [h2, h1]
    have hMF : M ≤ F := fun v hv y hy => htriv y hy v hv
    rcases hirr F (sup_invariant hFY hFA) with hF | hF
    · exact hM0 (eq_bot_iff.2 (hF ▸ hMF))
    · apply hy0
      apply Units.ext
      apply LinearMap.ext
      intro v
      have : v ∈ F := by rw [hF]; trivial
      exact this _ (eY.symm c3A6).2
  have hMσ : ∀ g : S6, ∀ m ∈ M, σ g m ∈ M := hσinv M hMY
  have hsimple : IsLSimple (restrictHom σ M hMσ) ⊤ ⊤ :=
    isLSimple_restrictHom σ M hMσ hM0 fun N hN0 hN hle =>
      hmin N (hσinv' N hN) hN0 hle
  have hnt' : restrictHom σ M hMσ c3A6 ≠ 1 := by
    intro h1
    have hsimpleS6 : IsSimpleGroup S6 :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (restrictHom σ M hMσ).ker with hk | hk
    · have : c3A6 ∈ (restrictHom σ M hMσ).ker := h1
      rw [hk, Subgroup.mem_bot] at this
      exact c3A6_ne_one this
    · apply hnotriv
      intro y hy v hv
      have h2 : eY ⟨y, hy⟩ ∈ (restrictHom σ M hMσ).ker := by rw [hk]; trivial
      have h3 : restrictHom σ M hMσ (eY ⟨y, hy⟩) = 1 := h2
      have h4 := congrArg (fun f : M ≃ₗ[ZMod 2] M => ((f ⟨v, hv⟩ : M) : S)) h3
      simp only [restrictHom_apply, LinearEquiv.coe_one, id_eq] at h4
      rw [hσ, MulEquiv.symm_apply_apply] at h4
      exact h4
  have hdimM : Module.finrank (ZMod 2) M ≤ 6 := (Submodule.finrank_le M).trans hdim
  have h4 := (a6_block_dims (restrictHom σ M hMσ) hsimple hdimM hnt').1
  have hMtop : M = ⊤ := by
    by_contra hMtop
    have hMA : ¬ ∀ a ∈ A, ∀ m ∈ M, (a : Module.End (ZMod 2) S) m ∈ M := by
      intro h
      rcases hirr M (sup_invariant hMY h) with h0 | h1
      · exact hM0 h0
      · exact hMtop h1
    push Not at hMA
    obtain ⟨a, ha, m, hm, hnm⟩ := hMA
    let M' : Submodule (ZMod 2) S := M.map (a : Module.End (ZMod 2) S)
    have hM'Y : ∀ y ∈ Y, ∀ v ∈ M', (y : Module.End (ZMod 2) S) v ∈ M' := by
      rintro y hy _ ⟨w, hw, rfl⟩
      refine ⟨((a⁻¹ * y * a : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) w,
        hMY _ (hconj a ha y hy) w hw, ?_⟩
      show (a : Module.End (ZMod 2) S) _ = (y : Module.End (ZMod 2) S) ((a : Module.End (ZMod 2) S) w)
      have e : y * a = a * (a⁻¹ * y * a) := by group
      calc (a : Module.End (ZMod 2) S) (((a⁻¹ * y * a : (Module.End (ZMod 2) S)ˣ) :
              Module.End (ZMod 2) S) w)
          = ((a * (a⁻¹ * y * a) : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) w := rfl
        _ = ((y * a : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) w := by rw [e]
        _ = _ := rfl
    have hfin' : Module.finrank (ZMod 2) M' = Module.finrank (ZMod 2) M :=
      LinearEquiv.finrank_map_eq (unitLE a) M
    have hinfY : ∀ y ∈ Y, ∀ v ∈ M ⊓ M', (y : Module.End (ZMod 2) S) v ∈ M ⊓ M' :=
      fun y hy v hv => ⟨hMY y hy v hv.1, hM'Y y hy v hv.2⟩
    by_cases hbot : M ⊓ M' = ⊥
    · have h1 := Submodule.finrank_sup_add_finrank_inf_eq M M'
      rw [hbot, finrank_bot, hfin'] at h1
      have h2 := Submodule.finrank_le (M ⊔ M')
      omega
    · have heq : M ⊓ M' = M := hmin _ hinfY hbot inf_le_left
      have hle : M ≤ M' := heq ▸ inf_le_right
      have hMM' : M = M' := Submodule.eq_of_le_of_finrank_eq hle hfin'.symm
      exact hnm (hMM' ▸ ⟨m, hm, rfl⟩)
  intro N hN
  by_cases hN0 : N = ⊥
  · exact Or.inl hN0
  · right
    have := hMmin N hN hN0
    rw [hMtop, finrank_top] at this
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le N) this)

end Irr

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
