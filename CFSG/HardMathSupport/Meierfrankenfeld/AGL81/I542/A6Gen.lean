module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Factor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.Quasithin.Background.BlueprintB2Bridge

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open Module

section Codim

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]

theorem codim_inf_le (F G : Submodule (ZMod 2) S) :
    finrank (ZMod 2) S - finrank (ZMod 2) ↥(F ⊓ G) ≤
      (finrank (ZMod 2) S - finrank (ZMod 2) ↥F) + (finrank (ZMod 2) S - finrank (ZMod 2) ↥G) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F G
  have h2 : finrank (ZMod 2) ↥(F ⊔ G) ≤ finrank (ZMod 2) S := Submodule.finrank_le _
  have h3 : finrank (ZMod 2) ↥F ≤ finrank (ZMod 2) S := Submodule.finrank_le _
  have h4 : finrank (ZMod 2) ↥G ≤ finrank (ZMod 2) S := Submodule.finrank_le _
  omega

theorem codim_iInf_le {ι : Type*} (F : ι → Submodule (ZMod 2) S) (s : Finset ι) :
    finrank (ZMod 2) S - finrank (ZMod 2) ↥(⨅ i ∈ s, F i) ≤
      ∑ i ∈ s, (finrank (ZMod 2) S - finrank (ZMod 2) ↥(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : (⨅ i ∈ (∅ : Finset ι), F i) = ⊤ := by simp
    rw [this, finrank_top]
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : (⨅ i ∈ insert a s, F i) = F a ⊓ ⨅ i ∈ s, F i := by
      ext v
      simp [Submodule.mem_iInf, Finset.mem_insert, forall_eq_or_imp]
    rw [e]
    exact (codim_inf_le _ _).trans (Nat.add_le_add_left ih _)

theorem finrank_le_sum_codim {m : ℕ} (F : Fin m → Submodule (ZMod 2) S) (h : (⨅ i, F i) = ⊥) :
    finrank (ZMod 2) S ≤ ∑ i, (finrank (ZMod 2) S - finrank (ZMod 2) ↥(F i)) := by
  have := codim_iInf_le F Finset.univ
  have e : (⨅ i ∈ (Finset.univ : Finset (Fin m)), F i) = ⊥ := by simpa using h
  rw [e, finrank_bot] at this
  simpa using this

end Codim


section Embed

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
  {Y A : Subgroup (Module.End (ZMod 2) S)ˣ} {K : Type*} [Group K]

@[expose] noncomputable def conjOn
    (hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ)) (eY : ↥Y ≃* K) :
    ↥(Y ⊔ A) →* MulAut K :=
  (MulAut.congr eY).toMonoidHom.comp ((Y.normalizerMonoidHom).comp (Subgroup.inclusion hDN))

theorem conjOn_symm_coe
    (hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ)) (eY : ↥Y ≃* K)
    (d : ↥(Y ⊔ A)) (k : K) :
    ((eY.symm (conjOn hDN eY d k) : ↥Y) : (Module.End (ZMod 2) S)ˣ) =
      (d : (Module.End (ZMod 2) S)ˣ) * (eY.symm k : ↥Y) * (d : (Module.End (ZMod 2) S)ˣ)⁻¹ := by
  simp [conjOn, MulAut.congr_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem conjOn_of_mem
    (hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ)) (eY : ↥Y ≃* K)
    (y : ↥Y) : conjOn hDN eY ⟨y, Subgroup.mem_sup_left y.2⟩ = MulAut.conj (eY y) := by
  ext k
  apply eY.symm.injective
  apply Subtype.ext
  rw [conjOn_symm_coe]
  simp [MulAut.conj_apply]

end Embed


section PullBack

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S] [Nontrivial S]
  {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}

open CFSG.QuasithinUnique.Setup

theorem a6_pullback
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ))
    (eY : ↥Y ≃* alternatingGroup (Fin 6)) (hA1 : A ≠ ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      ∃ t : Fin m → (Module.End (ZMod 2) S)ˣ, (∀ i, t i ∈ Y) ∧
        ∀ y ∈ Y, y ∈ Subgroup.closure (⋃ i,
          ((A.map (MulAut.conj (t i)).toMonoidHom : Subgroup (Module.End (ZMod 2) S)ˣ) :
            Set (Module.End (ZMod 2) S)ˣ)) := by
  classical
  have hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ) :=
    sup_le Subgroup.le_normalizer hAN
  have hcenter : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  set Φ := conjOn hDN eY with hΦ
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    refine Subtype.ext (eq_one_of_commute_of_irreducible_of_center hcenter hirr hAN eY hA2
      (d : (Module.End (ZMod 2) S)ˣ) d.2 fun y hy => ?_)
    have h := conjOn_symm_coe hDN eY d (eY ⟨y, hy⟩)
    rw [← hΦ, hd, MulAut.one_apply, MulEquiv.symm_apply_apply] at h
    have h' : (d : (Module.End (ZMod 2) S)ˣ) * y = y * d := by
      calc (d : (Module.End (ZMod 2) S)ˣ) * y
          = ((d : (Module.End (ZMod 2) S)ˣ) * y * (d : (Module.End (ZMod 2) S)ˣ)⁻¹) * d := by
            rw [inv_mul_cancel_right]
        _ = y * d := by rw [← h]
    exact h'
  set A₀ : Subgroup ↥(Y ⊔ A) := A.subgroupOf (Y ⊔ A) with hA₀
  set A' : Subgroup (MulAut (alternatingGroup (Fin 6))) := A₀.map Φ with hA'
  have hcardA' : Nat.card A' = Nat.card A := by
    rw [hA', Subgroup.card_map_of_injective hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ Y ⊔ A)).toEquiv
  have hA'ne : A' ≠ ⊥ := by
    intro h
    apply hA1
    rw [← Subgroup.card_eq_one, ← hcardA', h, Subgroup.card_bot]
  have hel : CFSG.IsElementaryAbelian 2 ↥A' := by
    refine (CFSG.Quasithin.BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).1 ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      show Φ x * Φ y = Φ y * Φ x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAc _ hx _ hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (hA2 _ hx)
      rw [this, map_one]
  obtain ⟨r, m, hcard, hr1, hr3, hmr, s, hgen⟩ := X3Aut.d4_alt6 A' hA'ne hel
  refine ⟨r, m, hcardA' ▸ hcard, hr1, hr3, hmr, fun i => ((eY.symm (s i) : ↥Y) :
    (Module.End (ZMod 2) S)ˣ), fun i => (eY.symm (s i)).2, ?_⟩
  set H : Subgroup (Module.End (ZMod 2) S)ˣ := Subgroup.closure (⋃ i,
    ((A.map (MulAut.conj ((eY.symm (s i) : ↥Y) : (Module.End (ZMod 2) S)ˣ)).toMonoidHom :
      Subgroup (Module.End (ZMod 2) S)ˣ) : Set (Module.End (ZMod 2) S)ˣ)) with hH
  have hΦτ : ∀ i, Φ ⟨((eY.symm (s i) : ↥Y) : (Module.End (ZMod 2) S)ˣ),
      Subgroup.mem_sup_left (eY.symm (s i)).2⟩ = MulAut.conj (s i) := by
    intro i
    have := conjOn_of_mem hDN eY (eY.symm (s i))
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hle : Subgroup.closure (⋃ i, ((A'.map (MulAut.conj (MulAut.conj (s i))).toMonoidHom :
      Subgroup (MulAut (alternatingGroup (Fin 6)))) : Set (MulAut (alternatingGroup (Fin 6))))) ≤
      (H.subgroupOf (Y ⊔ A)).map Φ := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hi
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hq
    set τ : ↥(Y ⊔ A) := ⟨((eY.symm (s i) : ↥Y) : (Module.End (ZMod 2) S)ˣ),
      Subgroup.mem_sup_left (eY.symm (s i)).2⟩ with hτ
    refine ⟨τ * a * τ⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.2 ?_
      refine Subgroup.subset_closure (Set.mem_iUnion.2 ⟨i, Subgroup.mem_map.2 ⟨a, ha, ?_⟩⟩)
      rfl
    · rw [map_mul, map_mul, map_inv, hΦτ]
      simp [MulAut.conj_apply]
  intro y hy
  have hyD : y ∈ Y ⊔ A := Subgroup.mem_sup_left hy
  have hinn : Φ ⟨y, hyD⟩ ∈ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
    have := conjOn_of_mem hDN eY ⟨y, hy⟩
    exact ⟨eY ⟨y, hy⟩, this.symm⟩
  obtain ⟨h, hh, hΦh⟩ := Subgroup.mem_map.1 (hle (hgen hinn))
  have : h = ⟨y, hyD⟩ := hinj hΦh
  rw [this, Subgroup.mem_subgroupOf] at hh
  exact hh

end PullBack


section Main

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S] [Nontrivial S]
  {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}

theorem a6_short_gen
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ))
    (eY : ↥Y ≃* alternatingGroup (Fin 6)) (hA1 : A ≠ ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      Module.finrank (ZMod 2) S ≤ m * (Module.finrank (ZMod 2) S -
        Module.finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub A)) := by
  classical
  obtain ⟨r, m, hcard, hr1, hr3, hmr, t, htY, hgen⟩ := a6_pullback hirr hAN eY hA1 hAc hA2
  refine ⟨r, m, hcard, hr1, hr3, hmr, ?_⟩
  have hDN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ) :=
    sup_le Subgroup.le_normalizer hAN
  let CY : Submodule (ZMod 2) S :=
    { carrier := {v | ∀ y ∈ Y, (y : Module.End (ZMod 2) S) v = v}
      add_mem' := fun {u v} hu hv y hy => by rw [map_add, hu y hy, hv y hy]
      zero_mem' := fun y _ => map_zero _
      smul_mem' := fun c v hv y hy => by rw [map_smul, hv y hy] }
  have hCYinv : ∀ d ∈ Y ⊔ A, ∀ v ∈ CY, (d : Module.End (ZMod 2) S) v ∈ CY := by
    intro d hd v hv y hy
    have h1 : d⁻¹ * y * d⁻¹⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.1 (hDN ((Y ⊔ A).inv_mem hd)) y).1 hy
    have h2 := hv _ h1
    have e : (y : Module.End (ZMod 2) S) ((d : Module.End (ZMod 2) S) v) =
        (d : Module.End (ZMod 2) S) (((d⁻¹ * y * d⁻¹⁻¹ : (Module.End (ZMod 2) S)ˣ) :
          Module.End (ZMod 2) S) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, ← Units.val_mul]
      congr 2
      group
    rw [e, h2]
  have hCY : CY = ⊥ := by
    rcases hirr CY hCYinv with h | h
    · exact h
    · exfalso
      have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
      obtain ⟨k, hk⟩ := exists_ne (1 : alternatingGroup (Fin 6))
      apply hk
      have hy : ∀ y ∈ Y, y = 1 := by
        intro y hy
        apply Units.ext
        refine LinearMap.ext fun v => ?_
        have hv : v ∈ CY := by rw [h]; exact Submodule.mem_top
        exact hv y hy
      have : eY.symm k = 1 := Subtype.ext (hy _ (eY.symm k).2)
      simpa using congrArg eY this
  let F : Fin m → Submodule (ZMod 2) S := fun i =>
    (CFSG.LocalAnalysis.CommutingFactor.fixedSub A).map
      (↑(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S (t i)) : S →ₗ[ZMod 2] S)
  have hcancel : ∀ (u : (Module.End (ZMod 2) S)ˣ) (x : S),
      ((u⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S)
        ((u : Module.End (ZMod 2) S) x) = x := by
    intro u x
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  have hF : (⨅ i, F i) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_iInf] at hv
    have hvCY : v ∈ CY := by
      intro y hy
      let Stab : Subgroup (Module.End (ZMod 2) S)ˣ :=
        { carrier := {u | (u : Module.End (ZMod 2) S) v = v}
          mul_mem' := fun {a b} ha hb => by
            show ((a * b : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v = v
            rw [Units.val_mul, Module.End.mul_apply]
            have ha' : (a : Module.End (ZMod 2) S) v = v := ha
            have hb' : (b : Module.End (ZMod 2) S) v = v := hb
            rw [hb', ha']
          one_mem' := by
            show (((1 : (Module.End (ZMod 2) S)ˣ)) : Module.End (ZMod 2) S) v = v
            simp
          inv_mem' := fun {a} ha => by
            have ha' : (a : Module.End (ZMod 2) S) v = v := ha
            show ((a⁻¹ : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) v = v
            have := hcancel a v
            rwa [ha'] at this }
      have hle : Subgroup.closure (⋃ i,
          ((A.map (MulAut.conj (t i)).toMonoidHom : Subgroup (Module.End (ZMod 2) S)ˣ) :
            Set (Module.End (ZMod 2) S)ˣ)) ≤ Stab := by
        rw [Subgroup.closure_le]
        intro g hg
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hg
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hi
        obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 (hv i)
        have hwv' : ((t i : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) w = v := by
          rw [← hwv]
          show _ = ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) S (t i)) w)
          rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
        have hwA : (a : Module.End (ZMod 2) S) w = w :=
          CFSG.LocalAnalysis.CommutingFactor.mem_fixedSub.1 hw a ha
        show (((MulAut.conj (t i)).toMonoidHom a : (Module.End (ZMod 2) S)ˣ) :
          Module.End (ZMod 2) S) v = v
        have e : (MulAut.conj (t i)).toMonoidHom a = t i * a * (t i)⁻¹ := rfl
        rw [e, ← hwv', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
          hcancel, hwA]
      exact hle (hgen y hy)
    rw [hCY] at hvCY
    exact hvCY
  have hsum := finrank_le_sum_codim F hF
  have hcodim : ∀ i, finrank (ZMod 2) S - finrank (ZMod 2) ↥(F i) =
      finrank (ZMod 2) S -
        finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub A) := fun i => by
    simp only [F]
    rw [LinearEquiv.finrank_map_eq]
  simp only [hcodim, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
