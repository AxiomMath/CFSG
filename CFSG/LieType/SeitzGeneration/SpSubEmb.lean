module

public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.CTP CFSG.LocalAnalysis.ComponentInitial

variable {r m : ℕ} {K : Type} [Field K]

@[expose] noncomputable def spLinEquiv (r : ℕ) (K : Type) [Field K] :
    StatedSp r K ≃* sesqUnitaryGroup (spForm r K) :=
  (MonoidHom.ofInjective spLin_injective).trans (MulEquiv.subgroupCongr range_spLin)

theorem spLin_spLinEquiv_symm (h : sesqUnitaryGroup (spForm r K)) :
    spLin r K ((spLinEquiv r K).symm h) = h := by
  have := congrArg Subtype.val ((spLinEquiv r K).apply_symm_apply h)
  exact this

@[expose] def spStab (U : Submodule K (Fin r ⊕ Fin r → K)) : Subgroup (StatedSp r K) where
  carrier := {a | ∀ u ∈ U, spEnd a u ∈ U ∧ spEnd a⁻¹ u ∈ U}
  mul_mem' := fun {a b} ha hb u hu => by
    refine ⟨?_, ?_⟩
    · rw [spEnd_mul, Module.End.mul_apply]
      exact (ha _ (hb u hu).1).1
    · rw [mul_inv_rev, spEnd_mul, Module.End.mul_apply]
      exact (hb _ (ha u hu).2).2
  one_mem' := fun u hu => by simpa [spEnd_one] using hu
  inv_mem' := fun {a} ha u hu => by simpa using (ha u hu).symm

structure SpSubEmb (r m : ℕ) (K : Type) [Field K] where
  U : Submodule K (Fin r ⊕ Fin r → K)
  φ : (Fin m ⊕ Fin m → K) ≃ₗ[K] U
  form_φ : ∀ x y, spForm r K (φ x) (φ y) = spForm m K x y
  compl : IsCompl U ((spForm r K).orthogonal U)

namespace SpSubEmb

variable (e : SpSubEmb r m K)

abbrev W : Submodule K (Fin r ⊕ Fin r → K) := (spForm r K).orthogonal e.U

theorem form_of_mem_W {u w : Fin r ⊕ Fin r → K} (hu : u ∈ e.U) (hw : w ∈ e.W) :
    spForm r K u w = 0 := hw u hu

theorem form_of_mem_W' {u w : Fin r ⊕ Fin r → K} (hu : u ∈ e.U) (hw : w ∈ e.W) :
    spForm r K w u = 0 := by
  rw [← spForm_isAlt.neg_eq, hw u hu, neg_zero]

theorem sup_eq_top : e.U ⊔ e.W = ⊤ := codisjoint_iff.mp e.compl.2

theorem linearMap_ext {f f' : Module.End K (Fin r ⊕ Fin r → K)}
    (hU : ∀ u ∈ e.U, f u = f' u) (hW : ∀ w ∈ e.W, f w = f' w) : f = f' := by
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ e.U ⊔ e.W := by rw [e.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, map_add, hU u hu, hW w hw]

theorem form_add {u u' w w' : Fin r ⊕ Fin r → K} (hu : u ∈ e.U) (hu' : u' ∈ e.U)
    (hw : w ∈ e.W) (hw' : w' ∈ e.W) :
    spForm r K (u + w) (u' + w') = spForm r K u u' + spForm r K w w' := by
  simp only [map_add, LinearMap.add_apply, e.form_of_mem_W hu hw', e.form_of_mem_W' hu' hw]
  ring

@[expose] noncomputable def extEquiv (g : StatedSp m K) :
    (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
  (Submodule.prodEquivOfIsCompl _ _ e.compl).symm.trans
    ((((e.φ.symm.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (spLin m K g))).trans
      e.φ).prodCongr (LinearEquiv.refl K e.W)).trans (Submodule.prodEquivOfIsCompl _ _ e.compl))

theorem extEquiv_of_mem (g : StatedSp m K) (x : Fin m ⊕ Fin m → K) :
    e.extEquiv g (e.φ x) = e.φ (spEnd g x) := by
  simp [extEquiv]

theorem extEquiv_of_mem_W (g : StatedSp m K) {w : Fin r ⊕ Fin r → K} (hw : w ∈ e.W) :
    e.extEquiv g w = w := by
  have := Submodule.prodEquivOfIsCompl_symm_apply_right _ _ e.compl ⟨w, hw⟩
  simp only [extEquiv, LinearEquiv.trans_apply]
  rw [this]
  simp

theorem exists_decomp (v : Fin r ⊕ Fin r → K) :
    ∃ x w, w ∈ e.W ∧ v = (e.φ x : Fin r ⊕ Fin r → K) + w := by
  have hv : v ∈ e.U ⊔ e.W := by rw [e.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  exact ⟨e.φ.symm ⟨u, hu⟩, w, hw, by simp⟩

theorem extEquiv_add (g : StatedSp m K) (x : Fin m ⊕ Fin m → K) {w : Fin r ⊕ Fin r → K}
    (hw : w ∈ e.W) :
    e.extEquiv g ((e.φ x : Fin r ⊕ Fin r → K) + w) = (e.φ (spEnd g x) : Fin r ⊕ Fin r → K) + w := by
  rw [map_add, e.extEquiv_of_mem, e.extEquiv_of_mem_W g hw]

theorem extEquiv_isometry (g : StatedSp m K) (v v' : Fin r ⊕ Fin r → K) :
    spForm r K (e.extEquiv g v) (e.extEquiv g v') = spForm r K v v' := by
  obtain ⟨x, w, hw, rfl⟩ := e.exists_decomp v
  obtain ⟨x', w', hw', rfl⟩ := e.exists_decomp v'
  rw [e.extEquiv_add g x hw, e.extEquiv_add g x' hw', e.form_add (e.φ _).2 (e.φ _).2 hw hw',
    e.form_add (e.φ _).2 (e.φ _).2 hw hw', e.form_φ, e.form_φ, spEnd_isometry]

@[expose] noncomputable def extUnitary : StatedSp m K →* sesqUnitaryGroup (spForm r K) where
  toFun g := ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv (e.extEquiv g),
    fun v v' => e.extEquiv_isometry g v v'⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    refine e.linearMap_ext (fun u hu => ?_) (fun w hw => ?_)
    · obtain ⟨x, rfl⟩ : ∃ x, (e.φ x : Fin r ⊕ Fin r → K) = u :=
        ⟨e.φ.symm ⟨u, hu⟩, by simp⟩
      change e.extEquiv 1 (e.φ x) = e.φ x
      rw [e.extEquiv_of_mem, spEnd_one, Module.End.one_apply]
    · exact e.extEquiv_of_mem_W 1 hw
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    refine e.linearMap_ext (fun u hu => ?_) (fun w hw => ?_)
    · obtain ⟨x, rfl⟩ : ∃ x, (e.φ x : Fin r ⊕ Fin r → K) = u :=
        ⟨e.φ.symm ⟨u, hu⟩, by simp⟩
      change e.extEquiv (g * h) (e.φ x) = e.extEquiv g (e.extEquiv h (e.φ x))
      rw [e.extEquiv_of_mem, e.extEquiv_of_mem, e.extEquiv_of_mem, spEnd_mul,
        Module.End.mul_apply]
    · change e.extEquiv (g * h) w = e.extEquiv g (e.extEquiv h w)
      rw [e.extEquiv_of_mem_W _ hw, e.extEquiv_of_mem_W _ hw, e.extEquiv_of_mem_W _ hw]

@[expose] noncomputable def ext : StatedSp m K →* StatedSp r K :=
  (spLinEquiv r K).symm.toMonoidHom.comp e.extUnitary

theorem spEnd_ext (g : StatedSp m K) (v : Fin r ⊕ Fin r → K) :
    spEnd (e.ext g) v = e.extEquiv g v := by
  change ((spLin r K ((spLinEquiv r K).symm (e.extUnitary g)) :
    LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v = _
  rw [spLin_spLinEquiv_symm]
  rfl

theorem spEnd_ext_of_mem (g : StatedSp m K) (x : Fin m ⊕ Fin m → K) :
    spEnd (e.ext g) (e.φ x) = e.φ (spEnd g x) := by
  rw [spEnd_ext, e.extEquiv_of_mem]

theorem spEnd_ext_of_mem_orth (g : StatedSp m K) {w : Fin r ⊕ Fin r → K} (hw : w ∈ e.W) :
    spEnd (e.ext g) w = w := by
  rw [spEnd_ext, e.extEquiv_of_mem_W g hw]

theorem ext_eq_iff {a b : StatedSp r K} : a = b ↔ spEnd a = spEnd b :=
  ⟨fun h => h ▸ rfl, fun h => spLin_injective (Units.ext h)⟩

theorem ext_spTransvection (x : Fin m ⊕ Fin m → K) (t : K) :
    e.ext (spTransvection x t) = spTransvection (e.φ x : Fin r ⊕ Fin r → K) t := by
  rw [ext_eq_iff]
  refine e.linearMap_ext (fun u hu => ?_) (fun w hw => ?_)
  · obtain ⟨y, rfl⟩ : ∃ y, (e.φ y : Fin r ⊕ Fin r → K) = u :=
      ⟨e.φ.symm ⟨u, hu⟩, by simp⟩
    rw [e.spEnd_ext_of_mem, spEnd_spTransvection, spEnd_spTransvection, map_add, map_smul,
      e.form_φ]
    rfl
  · rw [e.spEnd_ext_of_mem_orth _ hw, spEnd_spTransvection, e.form_of_mem_W' (e.φ x).2 hw,
      mul_zero, zero_smul, add_zero]

@[expose] noncomputable def restrictEquiv (a : spStab e.U) : e.U ≃ₗ[K] e.U :=
  LinearEquiv.ofLinearMap ((spEnd (a : StatedSp r K)).restrict fun u hu => (a.2 u hu).1)
    ((spEnd (a : StatedSp r K)⁻¹).restrict fun u hu => (a.2 u hu).2)
    (by
      ext u
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrict_apply,
        LinearMap.id_coe, id_eq]
      rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one, Module.End.one_apply])
    (by
      ext u
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrict_apply,
        LinearMap.id_coe, id_eq]
      rw [← Module.End.mul_apply, ← spEnd_mul, inv_mul_cancel, spEnd_one, Module.End.one_apply])

theorem restrictEquiv_apply (a : spStab e.U) (u : e.U) :
    (e.restrictEquiv a u : Fin r ⊕ Fin r → K) = spEnd (a : StatedSp r K) u := rfl

@[expose] noncomputable def resEquiv (a : spStab e.U) :
    (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K) :=
  (e.φ.trans (e.restrictEquiv a)).trans e.φ.symm

theorem φ_resEquiv (a : spStab e.U) (x : Fin m ⊕ Fin m → K) :
    (e.φ (e.resEquiv a x) : Fin r ⊕ Fin r → K) = spEnd (a : StatedSp r K) (e.φ x) := by
  simp [resEquiv, restrictEquiv_apply]

theorem resEquiv_isometry (a : spStab e.U) (x y : Fin m ⊕ Fin m → K) :
    spForm m K (e.resEquiv a x) (e.resEquiv a y) = spForm m K x y := by
  rw [← e.form_φ, ← e.form_φ, e.φ_resEquiv, e.φ_resEquiv, spEnd_isometry]

@[expose] noncomputable def res : spStab e.U →* StatedSp m K where
  toFun a := (spLinEquiv m K).symm ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv (e.resEquiv a),
    fun x y => e.resEquiv_isometry a x y⟩
  map_one' := by
    rw [MulEquiv.symm_apply_eq, map_one]
    apply Subtype.ext
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    apply e.φ.injective
    apply Subtype.ext
    change (e.φ (e.resEquiv 1 x) : Fin r ⊕ Fin r → K) = e.φ x
    rw [e.φ_resEquiv]
    simp [spEnd_one]
  map_mul' a b := by
    rw [MulEquiv.symm_apply_eq, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Units.ext
    refine LinearMap.ext fun x => ?_
    apply e.φ.injective
    apply Subtype.ext
    change (e.φ (e.resEquiv (a * b) x) : Fin r ⊕ Fin r → K) =
      e.φ (e.resEquiv a (e.resEquiv b x))
    rw [e.φ_resEquiv, e.φ_resEquiv, e.φ_resEquiv]
    simp [spEnd_mul]

theorem φ_spEnd_res (a : spStab e.U) (x : Fin m ⊕ Fin m → K) :
    (e.φ (spEnd (e.res a) x) : Fin r ⊕ Fin r → K) = spEnd (a : StatedSp r K) (e.φ x) := by
  have h : spLin m K (e.res a) = LinearMap.GeneralLinearGroup.ofLinearEquiv (e.resEquiv a) :=
    spLin_spLinEquiv_symm (r := m) (K := K) _
  have h2 : spEnd (e.res a) x = e.resEquiv a x := by
    change ((spLin m K (e.res a) : LinearMap.GeneralLinearGroup K (Fin m ⊕ Fin m → K)) :
      Module.End K (Fin m ⊕ Fin m → K)) x = _
    rw [h]
    rfl
  rw [h2, e.φ_resEquiv]

theorem spEnd_mem_W (a : spStab e.U) {w : Fin r ⊕ Fin r → K} (hw : w ∈ e.W) :
    spEnd (a : StatedSp r K) w ∈ e.W := by
  intro u hu
  have h := spEnd_isometry (a : StatedSp r K) (spEnd (a : StatedSp r K)⁻¹ u) w
  rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one,
    Module.End.one_apply] at h
  rw [h]
  exact hw _ (a.2 u hu).2

theorem commute_ext (a : spStab e.U) {g : StatedSp m K} (h : e.res a * g = g * e.res a) :
    (a : StatedSp r K) * e.ext g = e.ext g * a := by
  rw [ext_eq_iff, spEnd_mul, spEnd_mul]
  refine e.linearMap_ext (fun u hu => ?_) (fun w hw => ?_)
  · obtain ⟨x, rfl⟩ : ∃ x, (e.φ x : Fin r ⊕ Fin r → K) = u :=
      ⟨e.φ.symm ⟨u, hu⟩, by simp⟩
    rw [Module.End.mul_apply, Module.End.mul_apply, e.spEnd_ext_of_mem, ← e.φ_spEnd_res,
      ← e.φ_spEnd_res, e.spEnd_ext_of_mem, ← Module.End.mul_apply, ← Module.End.mul_apply,
      ← spEnd_mul, ← spEnd_mul, h]
  · rw [Module.End.mul_apply, Module.End.mul_apply, e.spEnd_ext_of_mem_orth _ hw,
      e.spEnd_ext_of_mem_orth _ (e.spEnd_mem_W a hw)]

theorem res_eq_one_iff (a : spStab e.U) :
    e.res a = 1 ↔ ∀ u ∈ e.U, spEnd (a : StatedSp r K) u = u := by
  constructor
  · intro h u hu
    obtain ⟨x, rfl⟩ : ∃ x, (e.φ x : Fin r ⊕ Fin r → K) = u :=
      ⟨e.φ.symm ⟨u, hu⟩, by simp⟩
    rw [← e.φ_spEnd_res, h, spEnd_one, Module.End.one_apply]
  · intro h
    rw [ext_eq_iff, spEnd_one]
    refine LinearMap.ext fun x => ?_
    apply e.φ.injective
    apply Subtype.ext
    rw [e.φ_spEnd_res, h _ (e.φ x).2, Module.End.one_apply]

end SpSubEmb

theorem SpSubEmb.exists [FiniteDimensional K (Fin r ⊕ Fin r → K)]
    {U : Submodule K (Fin r ⊕ Fin r → K)} (hU : ((spForm r K).restrict U).Nondegenerate) :
    ∃ (m : ℕ) (e : SpSubEmb r m K), e.U = U ∧ Module.finrank K U = 2 * m := by
  have hUalt : ((spForm r K).restrict U).IsAlt := fun u => spForm_isAlt (u : Fin r ⊕ Fin r → K)
  obtain ⟨m, hm⟩ := hUalt.even_finrank hU
  have hdim : Module.finrank K (Fin m ⊕ Fin m → K) = Module.finrank K U := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, hm]
  obtain ⟨φ, hφ⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isometry_of_finrank_eq
    (spForm_isAlt (r := m) (K := K)) spForm_nondegenerate hUalt hU hdim
  refine ⟨m, ⟨U, φ, fun x y => hφ x y,
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate spForm_isAlt.isRefl hU⟩,
    rfl, by rw [hm, two_mul]⟩

end CFSG.LieType.SeitzGeneration
