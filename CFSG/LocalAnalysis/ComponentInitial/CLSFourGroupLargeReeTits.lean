module

public import CFSG.LieType.Simplicity.TitsModel
public import CFSG.LieType.Ree.TitsGeneratorData
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity

section BaseChange

variable {k K : Type} [Field k] [Field K] {τ : Tag}

theorem baseChangeGL_mem_adjointGroup (ι : k →+* K) {g : ModGL τ k}
    (hg : g ∈ adjointGroup τ k) : baseChangeGL ι g ∈ adjointGroup τ K := by
  have h : (adjointGroup τ k).map (baseChangeGL ι) ≤ adjointGroup τ K := by
    rw [map_baseChangeGL_adjointGroup, Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · exact xUnit_mem_adjointGroup i _
    · exact yUnit_mem_adjointGroup i _
  exact h ⟨g, hg, rfl⟩

variable (τ) in
@[expose] def adjointBaseChange (ι : k →+* K) : adjointGroup τ k →* adjointGroup τ K :=
  ((baseChangeGL ι).comp (adjointGroup τ k).subtype).codRestrict _ fun g =>
    baseChangeGL_mem_adjointGroup ι g.2

theorem coe_adjointBaseChange (ι : k →+* K) (g : adjointGroup τ k) :
    (adjointBaseChange τ ι g : ModGL τ K) = baseChangeGL ι (g : ModGL τ k) :=
  rfl

theorem adjointBaseChange_xElement (ι : k →+* K) (i : Fin τ.rank) (c : k) :
    adjointBaseChange τ ι (xElement i c) = xElement i (ι c) :=
  Subtype.ext (baseChangeGL_xUnit ι i c)

theorem adjointBaseChange_yElement (ι : k →+* K) (i : Fin τ.rank) (c : k) :
    adjointBaseChange τ ι (yElement i c) = yElement i (ι c) :=
  Subtype.ext (baseChangeGL_yUnit ι i c)

end BaseChange

section Ree

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem pow_ringHom_zmod_two (ι : ZMod 2 →+* K) (c : ZMod 2) {e : ℕ} (he : e ≠ 0) :
    ι c ^ e = ι c := by
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hc c with rfl | rfl
  · rw [map_zero, zero_pow he]
  · rw [map_one, one_pow]

theorem relationExponent_ne_zero (t : ReeTag) (a : ℕ) (i : Fin t.tag.rank) :
    t.relationExponent a i ≠ 0 := by
  unfold ReeTag.relationExponent
  split_ifs <;> exact pow_ne_zero _ (ReeTag.fact_prime t).out.ne_zero

theorem finiteReeAut_adjointBaseChange (ι : ZMod 2 →+* K) (m : ℕ)
    (g : adjointGroup ReeTag.F4.tag (ZMod 2)) :
    ReeTag.F4.finiteReeAut K m (adjointBaseChange _ ι g) =
      adjointBaseChange _ ι (@ReeTag.finiteReeAut ReeTag.F4 (ZMod 2) _ _ (ZMod.charP 2)
        0 g) := by
  have : CharP (ZMod 2) ReeTag.F4.prime := ZMod.charP 2
  have hFK : ∀ x, ReeTag.F4.finiteReeAut K m x = ReeTag.F4.reeEndo K
      (ReeTag.shortFaithful (CharP.cast_eq_zero K ReeTag.F4.prime)) m x := fun x =>
    DFunLike.congr_fun (ReeTag.finiteReeAut_toMonoidHom m) x
  have hF2 : ∀ x, ReeTag.F4.finiteReeAut (ZMod 2) 0 x = ReeTag.F4.reeEndo (ZMod 2)
      (ReeTag.shortFaithful (CharP.cast_eq_zero (ZMod 2) ReeTag.F4.prime)) 0 x := fun x =>
    DFunLike.congr_fun (ReeTag.finiteReeAut_toMonoidHom 0) x
  have h := adjointGroup_hom_ext
    (f := (ReeTag.F4.finiteReeAut K m).toMonoidHom.comp (adjointBaseChange _ ι))
    (g := (adjointBaseChange _ ι).comp (ReeTag.F4.finiteReeAut (ZMod 2) 0).toMonoidHom)
    (fun i c => by
      change ReeTag.F4.finiteReeAut K m (adjointBaseChange _ ι (xElement i c)) =
        adjointBaseChange _ ι (ReeTag.F4.finiteReeAut (ZMod 2) 0 (xElement i c))
      rw [hFK, hF2, adjointBaseChange_xElement, ReeTag.reeEndo_xElement, ReeTag.reeEndo_xElement,
        adjointBaseChange_xElement, map_pow,
        pow_ringHom_zmod_two ι c (relationExponent_ne_zero _ _ _),
        pow_ringHom_zmod_two ι c (relationExponent_ne_zero _ _ _)])
    (fun i c => by
      change ReeTag.F4.finiteReeAut K m (adjointBaseChange _ ι (yElement i c)) =
        adjointBaseChange _ ι (ReeTag.F4.finiteReeAut (ZMod 2) 0 (yElement i c))
      rw [hFK, hF2, adjointBaseChange_yElement, ReeTag.reeEndo_yElement, ReeTag.reeEndo_yElement,
        adjointBaseChange_yElement, map_pow,
        pow_ringHom_zmod_two ι c (relationExponent_ne_zero _ _ _),
        pow_ringHom_zmod_two ι c (relationExponent_ne_zero _ _ _)])
  exact DFunLike.congr_fun h g

theorem map_titsGamma_le_reeGamma (ι : ZMod 2 →+* K) (m : ℕ) :
    ReeTag.titsGamma.map (baseChangeGL ι) ≤ ReeTag.F4.reeGamma K m := by
  have : CharP (ZMod 2) ReeTag.F4.prime := ZMod.charP 2
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hg', hF⟩ := ReeTag.mem_reeGamma.1 hg
  refine ReeTag.mem_reeGamma.2 ⟨baseChangeGL_mem_adjointGroup ι hg', ?_⟩
  have h := finiteReeAut_adjointBaseChange ι m ⟨g, hg'⟩
  rw [hF] at h
  exact h

end Ree

theorem map_subtype_commutator {G : Type*} [Group G] (H : Subgroup G) :
    (commutator H).map H.subtype = ⁅H, H⁆ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem center_commutator_reeFixed_eq_bot {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    Subgroup.center (commutator (reeFixed ReeTag.F4 k 0)) = ⊥ := by
  set T := titsData k hk
  set D := commutator (reeFixed ReeTag.F4 k 0)
  set M := (Subgroup.center D).map D.subtype
  have hMD : M ≤ D := Subgroup.map_subtype_le _
  have hMn : ∀ d ∈ D, ∀ m ∈ M, d * m * d⁻¹ ∈ M := by
    rintro d hd _ ⟨z, hz, rfl⟩
    have hc := Subgroup.mem_center_iff.1 hz ⟨d, hd⟩
    have hc' : d * (z : reeFixed ReeTag.F4 k 0) = (z : reeFixed ReeTag.F4 k 0) * d :=
      congrArg Subtype.val hc
    refine ⟨z, hz, ?_⟩
    change (z : reeFixed ReeTag.F4 k 0) = d * z * d⁻¹
    rw [hc', mul_inv_cancel_right]
  rcases T.eq_bot_or_eq_of_le hk M hMD hMn with h | h
  · exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 h
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := T.nonabelian
    have hxM : x ∈ M := h ▸ hx
    obtain ⟨z, hz, rfl⟩ := hxM
    exact hxy (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)).symm

theorem large_Ree_prime_field_Tits_fixed_four_group (m : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (ι : ZMod 2 →+* K) :
    Function.Injective (baseChangeGL (τ := ReeTag.F4.tag) ι) ∧
    (adjointGroup ReeTag.F4.tag (ZMod 2)).map (baseChangeGL ι) ≤ adjointGroup ReeTag.F4.tag K ∧
    ⁅ReeTag.titsGamma, ReeTag.titsGamma⁆.map (baseChangeGL ι) ≤ ReeTag.F4.reeGamma K m ∧
    ∃ A : Subgroup (ModGL ReeTag.F4.tag K),
      A ≤ ⁅ReeTag.titsGamma, ReeTag.titsGamma⁆.map (baseChangeGL ι) ∧
      A ≤ ReeTag.F4.reeGamma K m ∧ CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  have : CharP (ZMod 2) ReeTag.F4.prime := ZMod.charP 2
  have hk : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hinj := baseChangeGL_injective (τ := ReeTag.F4.tag) ι
  have hcomm : ⁅ReeTag.titsGamma, ReeTag.titsGamma⁆.map (baseChangeGL ι) ≤
      ReeTag.F4.reeGamma K m :=
    (Subgroup.map_mono (Subgroup.commutator_le_self _)).trans (map_titsGamma_le_reeGamma ι m)
  have hΓ : ReeTag.titsGamma = (reeFixed ReeTag.F4 (ZMod 2) 0).map
      (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype :=
    ReeTag.reeGamma_eq_reeFixedGroup.trans (reeFixedGroup_eq_map_reeFixed ReeTag.F4 (ZMod 2) 0)
  set D := commutator (reeFixed ReeTag.F4 (ZMod 2) 0)
  have hD : ⁅ReeTag.titsGamma, ReeTag.titsGamma⁆ =
      (D.map (reeFixed ReeTag.F4 (ZMod 2) 0).subtype).map
        (adjointGroup ReeTag.F4.tag (ZMod 2)).subtype := by
    rw [hΓ, ← Subgroup.map_commutator, map_subtype_commutator]
  have : Finite (Module.End (ZMod 2) (RootModule ReeTag.F4.tag (ZMod 2))) :=
    Module.finite_of_finite (ZMod 2)
  have hZ : Odd (Nat.card (Subgroup.center D)) := by
    rw [center_commutator_reeFixed_eq_bot hk, Subgroup.card_bot]
    exact odd_one
  obtain ⟨A₀, ⟨hc, hp⟩, hcard₀⟩ := (quasisimple_odd_center_fixed_four_group_rank.{0, 0}
    ((titsData (ZMod 2) hk).isQuasisimple hk) hZ).1
  set f : D →* ModGL ReeTag.F4.tag K := (baseChangeGL ι).comp
    ((adjointGroup ReeTag.F4.tag (ZMod 2)).subtype.comp
      ((reeFixed ReeTag.F4 (ZMod 2) 0).subtype.comp D.subtype))
  have hfinj : Function.Injective f :=
    hinj.comp (Subtype.val_injective.comp (Subtype.val_injective.comp Subtype.val_injective))
  have hfD : ∀ x : D, f x ∈ ⁅ReeTag.titsGamma, ReeTag.titsGamma⁆.map (baseChangeGL ι) :=
    fun x => by
      rw [hD]
      exact ⟨_, ⟨_, ⟨x, x.2, rfl⟩, rfl⟩, rfl⟩
  refine ⟨hinj, ?_, hcomm, A₀.map f, ?_, ?_, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_adjointGroup ι hg
  · rintro _ ⟨x, -, rfl⟩
    exact hfD x
  · rintro _ ⟨x, -, rfl⟩
    exact hcomm (hfD x)
  · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
    apply Subtype.ext
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hp x hx, map_one]
  · rw [Subgroup.card_map_of_injective hfinj, hcard₀]

end CFSG.LocalAnalysis.ComponentInitial
