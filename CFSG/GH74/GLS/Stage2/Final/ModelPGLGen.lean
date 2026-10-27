module

public import CFSG.GH74.GLS.Stage2.Final.ModelIVKGen

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GorensteinWalter

theorem abs_quot {G H P : Type*} [Group G] [Group H] [Group P] (z : G) (X : Subgroup G)
    (Θ : H →* G) (hΘ : Function.Injective Θ) (hX : Θ.range = X) (ψ : H →* P)
    (hker : ∀ h, Θ h ∈ zpowers z ↔ h ∈ ψ.ker) :
    ∃ _ : ((zpowers z).subgroupOf X).Normal,
      Nonempty (↥X ⧸ (zpowers z).subgroupOf X ≃* ↥ψ.range) := by
  let e : H ≃* X := (MonoidHom.ofInjective hΘ).trans (MulEquiv.subgroupCongr hX)
  have he : ∀ h, ((e h : X) : G) = Θ h := fun h => rfl
  have hN : ψ.ker.map e.toMonoidHom = (zpowers z).subgroupOf X := by
    ext x
    obtain ⟨h, rfl⟩ := e.surjective x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf, he, hker]
  have hnorm : ((zpowers z).subgroupOf X).Normal := by
    rw [← hN]
    exact (inferInstance : ψ.ker.Normal).map e.toMonoidHom e.surjective
  refine ⟨hnorm, ⟨?_⟩⟩
  exact (QuotientGroup.congr ψ.ker ((zpowers z).subgroupOf X) e hN).symm.trans
    (QuotientGroup.quotientKerEquivRange ψ)

theorem pgl_quot_transport {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') {z w : G} {z' w' : G'}
    {E : Subgroup G} {E' : Subgroup G'} (hz : Φ z = z') (hw : Φ w = w')
    (hE : E.map Φ.toMonoidHom = E') {P : ℕ → Prop}
    (h : ∃ _ : ((zpowers z).subgroupOf (E ⊔ zpowers w)).Normal,
      IVK.IsPGL2 (↥(E ⊔ zpowers w) ⧸ (zpowers z).subgroupOf (E ⊔ zpowers w)) P) :
    ∃ _ : ((zpowers z').subgroupOf (E' ⊔ zpowers w')).Normal,
      IVK.IsPGL2 (↥(E' ⊔ zpowers w') ⧸ (zpowers z').subgroupOf (E' ⊔ zpowers w')) P := by
  obtain ⟨hn, F₀, iF, fF, hP, ⟨φ⟩⟩ := h
  have hH : (E ⊔ zpowers w).map Φ.toMonoidHom = E' ⊔ zpowers w' := by
    rw [Subgroup.map_sup, hE, MonoidHom.map_zpowers]
    show E' ⊔ zpowers (Φ w) = _
    rw [hw]
  let e : ↥(E ⊔ zpowers w) ≃* ↥(E' ⊔ zpowers w') :=
    (MulEquiv.subgroupMap Φ (E ⊔ zpowers w)).trans (MulEquiv.subgroupCongr hH)
  have he : ∀ x, ((e x : ↥(E' ⊔ zpowers w')) : G') = Φ x := fun x => rfl
  have hN : ((zpowers z).subgroupOf (E ⊔ zpowers w)).map e.toMonoidHom =
      (zpowers z').subgroupOf (E' ⊔ zpowers w') := by
    ext x
    obtain ⟨h, rfl⟩ := e.surjective x
    have hzp : zpowers z' = (zpowers z).map Φ.toMonoidHom := by
      rw [← hz]
      exact (MonoidHom.map_zpowers Φ.toMonoidHom z).symm
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, he, hzp]
    constructor
    · intro hh
      exact Subgroup.mem_map_of_mem _ hh
    · intro hh
      obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.1 hh
      have : y = (h : G) := Φ.injective hyh
      rw [← this]
      exact hy
  have hn' : ((zpowers z').subgroupOf (E' ⊔ zpowers w')).Normal := by
    rw [← hN]
    exact hn.map e.toMonoidHom e.surjective
  refine ⟨hn', F₀, iF, fF, hP, ⟨?_⟩⟩
  haveI := hn
  haveI := hn'
  exact (QuotientGroup.congr _ _ e hN).symm.trans φ

theorem pgl_quot_conj {G : Type} [Group G] {z t w : G} {E E' : Subgroup G}
    (hE : E.map (MulAut.conj t).toMonoidHom = E') (htw : t * w = w * t) (htz : t * z = z * t)
    {P : ℕ → Prop}
    (h : ∃ _ : ((zpowers z).subgroupOf (E ⊔ zpowers w)).Normal,
      IVK.IsPGL2 (↥(E ⊔ zpowers w) ⧸ (zpowers z).subgroupOf (E ⊔ zpowers w)) P) :
    ∃ _ : ((zpowers z).subgroupOf (E' ⊔ zpowers w)).Normal,
      IVK.IsPGL2 (↥(E' ⊔ zpowers w) ⧸ (zpowers z).subgroupOf (E' ⊔ zpowers w)) P :=
  pgl_quot_transport (MulAut.conj t) (z := z) (z' := z) (w := w) (w' := w)
    (by rw [MulAut.conj_apply, htz]; group) (by rw [MulAut.conj_apply, htw]; group) hE h

variable {F : Type} [Field F]

@[expose] def Hpm (M : ModelData F) : Subgroup (GL (Fin 2) F) where
  carrier := {g | g ∈ M.U2 ∧ ((g : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
    (g : Matrix (Fin 2) (Fin 2) F).det = -1)}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.U2.mul_mem ha hb, ?_⟩
    rw [Units.val_mul, Matrix.det_mul]
    rcases ha' with h | h <;> rcases hb' with h' | h' <;> rw [h, h'] <;> simp
  one_mem' := ⟨M.U2.one_mem, Or.inl (by simp)⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.U2.inv_mem ha, ?_⟩
    have h1 : ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det *
        (a : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rcases ha' with h | h
    · left; rw [h, mul_one] at h1; exact h1
    · right; rw [h] at h1; linear_combination -h1

theorem mem_Hpm {M : ModelData F} {g : GL (Fin 2) F} :
    g ∈ Hpm M ↔ g ∈ M.U2 ∧ ((g : Matrix (Fin 2) (Fin 2) F).det = 1 ∨
      (g : Matrix (Fin 2) (Fin 2) F).det = -1) := Iff.rfl

theorem det_unit_cases {g : GL (Fin 2) F}
    (h : (g : Matrix (Fin 2) (Fin 2) F).det = 1 ∨ (g : Matrix (Fin 2) (Fin 2) F).det = -1) :
    Matrix.GeneralLinearGroup.det g = 1 ∨ Matrix.GeneralLinearGroup.det g = -1 := by
  rcases h with h | h
  · left; apply Units.ext; rw [Matrix.GeneralLinearGroup.val_det_apply, h]; rfl
  · right; apply Units.ext; rw [Matrix.GeneralLinearGroup.val_det_apply, h]; simp

@[expose] def dd (g : GL (Fin 2) F) : GL (Fin 2) F := dgen 1 (Matrix.GeneralLinearGroup.det g)

theorem dd_mul (g h : GL (Fin 2) F) : dd (g * h) = dd g * dd h := by
  rw [dd, dd, dd, map_mul, dgen_mul, one_mul]

theorem dgen_one_one : (dgen (1 : Fˣ) 1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  rw [coe_dgen]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem dgen_one_neg_one : (dgen (1 : Fˣ) (-1) : GL (Fin 2) F) = dRefl F := by
  apply Units.ext
  rw [coe_dgen, coe_dRefl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem dd_one : dd (1 : GL (Fin 2) F) = 1 := by
  rw [dd, map_one, dgen_one_one]

theorem det_dd (g : GL (Fin 2) F) :
    ((dd g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := by
  rw [dd, det_dgen, Units.val_one, one_mul, Matrix.GeneralLinearGroup.val_det_apply]

theorem dd_mem_U2 {M : ModelData F} (hd : dRefl F ∈ M.U2) {g : GL (Fin 2) F} (hg : g ∈ Hpm M) :
    dd g ∈ M.U2 := by
  rcases det_unit_cases hg.2 with h | h
  · rw [dd, h, dgen_one_one]; exact M.U2.one_mem
  · rw [dd, h, dgen_one_neg_one]; exact hd

theorem Theta_mem {M : ModelData F} (hd : dRefl F ∈ M.U2) {g : GL (Fin 2) F} (hg : g ∈ Hpm M) :
    diagGL g (dd g) ∈ M.K4 := by
  refine M.diagGL_mem_K4_iff.2 ⟨hg.1, dd_mem_U2 hd hg, ?_⟩
  rw [det_dd]
  rcases hg.2 with h | h <;> rw [h] <;> norm_num

@[expose] noncomputable def Theta (M : ModelData F) (hd : dRefl F ∈ M.U2) : ↥(Hpm M) →* PG M where
  toFun g := mkP M ⟨diagGL (g : GL (Fin 2) F) (dd (g : GL (Fin 2) F)), Theta_mem hd g.2⟩
  map_one' := by
    have : (⟨diagGL ((1 : ↥(Hpm M)) : GL (Fin 2) F) (dd ((1 : ↥(Hpm M)) : GL (Fin 2) F)),
        Theta_mem hd (1 : ↥(Hpm M)).2⟩ : ↥M.K4) = 1 := by
      apply Subtype.ext
      show diagGL (1 : GL (Fin 2) F) (dd 1) = 1
      rw [dd_one, diagGL_one]
    rw [this, map_one]
  map_mul' := by
    intro a b
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show diagGL ((a : GL (Fin 2) F) * (b : GL (Fin 2) F)) (dd ((a : GL (Fin 2) F) * (b : GL (Fin 2) F))) =
      diagGL (a : GL (Fin 2) F) (dd a) * diagGL (b : GL (Fin 2) F) (dd b)
    rw [dd_mul, diagGL_mul]

theorem Theta_apply (M : ModelData F) (hd : dRefl F ∈ M.U2) (g : ↥(Hpm M)) :
    Theta M hd g = mkP M ⟨diagGL (g : GL (Fin 2) F) (dd (g : GL (Fin 2) F)), Theta_mem hd g.2⟩ :=
  rfl

theorem Theta_injective (M : ModelData F) (hd : dRefl F ∈ M.U2) : Function.Injective (Theta M hd) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [Theta_apply] at hg
  obtain ⟨s, hs⟩ := mem_Zs.1 ((QuotientGroup.eq_one_iff _).1 hg)
  have hs' : diagGL (g : GL (Fin 2) F) (dd (g : GL (Fin 2) F)) = diagGL (sc2 s) (sc2 s) := by
    rw [← scalar4_eq]; exact hs.symm
  obtain ⟨h1, h2⟩ := diagGL_inj hs'
  have h3 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 0) h2
  have hs1 : s = 1 := by
    apply Units.ext
    simpa [dd, coe_dgen, sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h3.symm
  apply Subtype.ext
  rw [h1, hs1, sc2_one]
  rfl

theorem negOne_mem_Hpm (M : ModelData F) : (-1 : GL (Fin 2) F) ∈ Hpm M :=
  ⟨M.neg_mem, Or.inl (by simp [Matrix.det_neg])⟩

theorem Theta_neg_one (M : ModelData F) (hd : dRefl F ∈ M.U2) :
    Theta M hd ⟨-1, negOne_mem_Hpm M⟩ = yP M := by
  rw [Theta_apply]
  have h1 : dd (-1 : GL (Fin 2) F) = 1 := by
    have : Matrix.GeneralLinearGroup.det (-1 : GL (Fin 2) F) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      simp [Matrix.det_neg]
    rw [dd, this, dgen_one_one]
  show mkP M _ = mkP M M.yK
  congr 1
  apply Subtype.ext
  show diagGL (-1 : GL (Fin 2) F) (dd (-1)) = yGL F
  rw [h1]
  rfl

theorem Theta_mem_zpowers_iff (M : ModelData F) (hd : dRefl F ∈ M.U2) (g : ↥(Hpm M)) :
    Theta M hd g ∈ zpowers (yP M) ↔ (g : GL (Fin 2) F) = 1 ∨ (g : GL (Fin 2) F) = -1 := by
  constructor
  · intro h
    rcases mem_zpowers_of_sq_one (yP_sq M) h with h1 | h1
    · left
      have := Theta_injective M hd (h1.trans (map_one _).symm)
      rw [this]; rfl
    · right
      have := Theta_injective M hd (h1.trans (Theta_neg_one M hd).symm)
      rw [this]
  · rintro (h | h)
    · have : g = 1 := Subtype.ext h
      rw [this, map_one]; exact Subgroup.one_mem _
    · have : g = ⟨-1, negOne_mem_Hpm M⟩ := Subtype.ext h
      rw [this, Theta_neg_one]; exact Subgroup.mem_zpowers _

theorem det_unit_of_H2 {M : ModelData F} {a : GL (Fin 2) F} (ha : a ∈ M.H2) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact ((M.mem_H2 _).1 ha).2

theorem Theta_iota1 (M : ModelData F) (hd : dRefl F ∈ M.U2) (a : ↥M.H2)
    (ha : (a : GL (Fin 2) F) ∈ Hpm M) : Theta M hd ⟨a, ha⟩ = iota1 M a := by
  rw [Theta_apply, iota1_apply]
  congr 1
  apply Subtype.ext
  show diagGL (a : GL (Fin 2) F) (dd (a : GL (Fin 2) F)) = blkL F a
  have : dd (a : GL (Fin 2) F) = 1 := by
    rw [dd, det_unit_of_H2 a.2, dgen_one_one]
  rw [this, blkL_apply]

theorem dRefl_mem_Hpm {M : ModelData F} (hd : dRefl F ∈ M.U2) : dRefl F ∈ Hpm M :=
  ⟨hd, Or.inr det_dRefl⟩

theorem det_unit_dRefl : Matrix.GeneralLinearGroup.det (dRefl F) = -1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_dRefl]
  simp

theorem Theta_dRefl (M : ModelData F) (hd : dRefl F ∈ M.U2) :
    Theta M hd ⟨dRefl F, dRefl_mem_Hpm hd⟩ = dP M (dRefl F) hd := by
  rw [Theta_apply, dP]
  congr 1
  apply Subtype.ext
  show diagGL (dRefl F) (dd (dRefl F)) = diagGL (dRefl F) (dRefl F)⁻¹
  have h1 : dd (dRefl F) = dRefl F := by
    rw [dd, det_unit_dRefl, dgen_one_neg_one]
  rw [h1, dRefl_inv]

theorem range_Theta (M : ModelData F) (hd : dRefl F ∈ M.U2) :
    (Theta M hd).range = K1 M ⊔ zpowers (dP M (dRefl F) hd) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    rcases det_unit_cases g.2.2 with h | h
    · have hg1 : (g : GL (Fin 2) F) ∈ M.H2 := (M.mem_H2 _).2 ⟨g.2.1, by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, h]; rfl⟩
      have : Theta M hd g = iota1 M ⟨g, hg1⟩ := Theta_iota1 M hd ⟨g, hg1⟩ g.2
      rw [this]
      exact Subgroup.mem_sup_left ⟨_, rfl⟩
    · have hgd : (g : GL (Fin 2) F) * dRefl F ∈ M.H2 := (M.mem_H2 _).2 ⟨M.U2.mul_mem g.2.1 hd, by
        rw [Units.val_mul, Matrix.det_mul, det_dRefl, ← Matrix.GeneralLinearGroup.val_det_apply, h]
        simp⟩
      have hgdH : (g : GL (Fin 2) F) * dRefl F ∈ Hpm M := (Hpm M).mul_mem g.2 (dRefl_mem_Hpm hd)
      have hprod : Theta M hd g = iota1 M ⟨g * dRefl F, hgd⟩ * dP M (dRefl F) hd := by
        rw [← Theta_iota1 M hd ⟨_, hgd⟩ hgdH, ← Theta_dRefl M hd, ← map_mul]
        congr 1
        apply Subtype.ext
        show (g : GL (Fin 2) F) = g * dRefl F * dRefl F
        rw [mul_assoc, dRefl_mul_self, mul_one]
      rw [hprod]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      have ha : (a : GL (Fin 2) F) ∈ Hpm M :=
        ⟨((M.mem_H2 _).1 a.2).1, Or.inl ((M.mem_H2 _).1 a.2).2⟩
      exact ⟨⟨a, ha⟩, Theta_iota1 M hd a ha⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨dRefl F, dRefl_mem_Hpm hd⟩, Theta_dRefl M hd⟩

theorem mk_eq_one_iff_pm {M : ModelData F} (hC : ClsFacts M) {g : GL (Fin 2) F} (hg : g ∈ Hpm M) :
    (Matrix.ProjGenLinGroup.mk g : PGL2 F) = 1 ↔ g = 1 ∨ g = -1 := by
  constructor
  · intro h
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
    obtain ⟨u, rfl⟩ := h
    have hU : sc2 u ∈ M.U2 := hg.1
    rcases hg.2 with h | h
    · have hu : u * u = 1 := by
        rw [det_sc2] at h
        apply Units.ext
        simpa [sq] using h
      rcases units_sq_eq_one hu with rfl | rfl
      · left; exact sc2_one
      · right; exact sc2_neg_one
    · exfalso
      have hu : u * u = -1 := by
        rw [det_sc2] at h
        apply Units.ext
        simpa [sq] using h
      exact hC.no_scalar_i u hU hu
  · rintro (h | h)
    · rw [h]; exact Matrix.ProjGenLinGroup.mk_one
    · rw [h, ← sc2_neg_one]; exact Matrix.ProjGenLinGroup.mk_scalar _

theorem tP_comm_dP (M : ModelData F) (hd : dRefl F ∈ M.U2) :
    tP M * dP M (dRefl F) hd = dP M (dRefl F) hd * tP M := by
  have h := tP_conj_dP M hd
  have hu2 : dP M (dRefl F) hd * dP M (dRefl F) hd = 1 := dP_mul_self hd dRefl_mul_self
  have hinv : (dP M (dRefl F) hd)⁻¹ = dP M (dRefl F) hd := inv_eq_of_mul_eq_one_right hu2
  rw [hinv, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem pglStmt_of_surj {M : ModelData F} (hd : dRefl F ∈ M.U2) {q : ℕ}
    (hr : ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (Ψ : ↥(Hpm M) →* PGL2 F₀),
      Nat.card F₀ = q ∧ Function.Surjective Ψ ∧
        ∀ g : ↥(Hpm M), Ψ g = 1 ↔ (g : GL (Fin 2) F) = 1 ∨ (g : GL (Fin 2) F) = -1) :
    PglStmt M q (dP M (dRefl F) hd) := by
  obtain ⟨F₀, iF, fF, Ψ, hq, hs, hk⟩ := hr
  have hK1 : ∃ _ : ((zpowers (yP M)).subgroupOf (K1 M ⊔ zpowers (dP M (dRefl F) hd))).Normal,
      IVK.IsPGL2 (↥(K1 M ⊔ zpowers (dP M (dRefl F) hd)) ⧸
        (zpowers (yP M)).subgroupOf (K1 M ⊔ zpowers (dP M (dRefl F) hd))) (fun r => r = q) := by
    obtain ⟨hn, ⟨e⟩⟩ := abs_quot (yP M) _ (Theta M hd) (Theta_injective M hd) (range_Theta M hd) Ψ
      (fun g => by
        rw [Theta_mem_zpowers_iff, MonoidHom.mem_ker]
        exact (hk g).symm)
    exact ⟨hn, F₀, iF, fF, hq,
      ⟨e.trans ((MulEquiv.subgroupCongr (MonoidHom.range_eq_top.2 hs)).trans Subgroup.topEquiv)⟩⟩
  intro Ei hEi
  rcases hEi with rfl | rfl
  · exact hK1
  · exact pgl_quot_conj (z := yP M) (t := tP M) (w := dP M (dRefl F) hd) (E := K1 M) (tP_swap M)
      (tP_comm_dP M hd) (Subgroup.mem_centralizer_singleton_iff.1 (tP_mem_Cg M)) hK1

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
