module

public import CFSG.GH74.GLS.Stage1.Main.BrFusedH4
public import CFSG.GH74.GLS.Stage1.Main.BrFusedDefs
public import CFSG.GH74.GLS.Stage2.Final.ModelPGLGen

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GorensteinWalter CFSG.GH74.GLS.Stage1.Main

theorem abs_quot_subgroup {G H P : Type*} [Group G] [Group H] [Group P] (Z X : Subgroup G)
    (Θ : H →* G) (hΘ : Function.Injective Θ) (hX : Θ.range = X) (ψ : H →* P)
    (hker : ∀ h, Θ h ∈ Z ↔ h ∈ ψ.ker) :
    ∃ _ : (Z.subgroupOf X).Normal, Nonempty (↥X ⧸ Z.subgroupOf X ≃* ↥ψ.range) := by
  let e : H ≃* X := (MonoidHom.ofInjective hΘ).trans (MulEquiv.subgroupCongr hX)
  have he : ∀ h, ((e h : X) : G) = Θ h := fun h => rfl
  have hN : ψ.ker.map e.toMonoidHom = Z.subgroupOf X := by
    ext x
    obtain ⟨h, rfl⟩ := e.surjective x
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf, he, hker]
  have hnorm : (Z.subgroupOf X).Normal := by
    rw [← hN]
    exact (inferInstance : ψ.ker.Normal).map e.toMonoidHom e.surjective
  refine ⟨hnorm, ⟨?_⟩⟩
  exact (QuotientGroup.congr ψ.ker (Z.subgroupOf X) e hN).symm.trans
    (QuotientGroup.quotientKerEquivRange ψ)

variable {F : Type} [Field F]

theorem unit_det_dgen (α β : Fˣ) :
    Matrix.GeneralLinearGroup.det (dgen α β : GL (Fin 2) F) = α * β := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_dgen, Units.val_mul]

theorem unit_det_neg_one : Matrix.GeneralLinearGroup.det (-1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [Matrix.det_neg]

theorem dgen_mem_U2_of_pow_four {M : ModelData F} {i : Fˣ} (hii : i * i = -1)
    (ha₀ : dgen i 1 ∈ M.U2) {δ : Fˣ} (hδ : δ ^ 4 = 1) : dgen δ 1 ∈ M.U2 := by
  have h2 : (dgen i 1 : GL (Fin 2) F) ^ 2 = dgen (-1) 1 := by
    rw [sq, dgen_mul, hii, mul_one]
  have h3 : (dgen i 1 : GL (Fin 2) F)⁻¹ = dgen (-i) 1 := by
    have hi : i⁻¹ = -i := inv_eq_of_mul_eq_one_right (by rw [mul_neg, hii, neg_neg])
    rw [dgen_inv, inv_one, hi]
  rcases units_cases_pow_four hii hδ with rfl | rfl | rfl | rfl
  · rw [dgen_one_one]; exact M.U2.one_mem
  · rw [← h2]; exact M.U2.pow_mem ha₀ 2
  · exact ha₀
  · rw [← h3]; exact M.U2.inv_mem ha₀

@[expose] def dd4 (g : GL (Fin 2) F) : GL (Fin 2) F := dgen (Matrix.GeneralLinearGroup.det g)⁻¹ 1

theorem dd4_mul (g h : GL (Fin 2) F) : dd4 (g * h) = dd4 g * dd4 h := by
  rw [dd4, dd4, dd4, map_mul, mul_inv, dgen_mul, one_mul]

theorem dd4_one : dd4 (1 : GL (Fin 2) F) = 1 := by
  rw [dd4, map_one, inv_one, dgen_one_one]

theorem det_dd4 (g : GL (Fin 2) F) :
    ((dd4 g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (((Matrix.GeneralLinearGroup.det g)⁻¹ : Fˣ) : F) := by
  rw [dd4, det_dgen, Units.val_one, mul_one]

theorem dd4_mem_U2 {M : ModelData F} (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2)
    {g : GL (Fin 2) F} (hg : g ∈ H4 M) : dd4 g ∈ M.U2 :=
  h4 _ (by rw [inv_pow, hg.2, inv_one])

theorem Theta4_mem {M : ModelData F} (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2)
    {g : GL (Fin 2) F} (hg : g ∈ H4 M) : diagGL g (dd4 g) ∈ M.K4 := by
  refine M.diagGL_mem_K4_iff.2 ⟨hg.1, dd4_mem_U2 h4 hg, ?_⟩
  rw [det_dd4, ← Matrix.GeneralLinearGroup.val_det_apply, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

@[expose] noncomputable def Theta4 (M : ModelData F)
    (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2) : ↥(H4 M) →* PG M where
  toFun g := mkP M ⟨diagGL (g : GL (Fin 2) F) (dd4 (g : GL (Fin 2) F)), Theta4_mem h4 g.2⟩
  map_one' := by
    have : (⟨diagGL ((1 : ↥(H4 M)) : GL (Fin 2) F) (dd4 ((1 : ↥(H4 M)) : GL (Fin 2) F)),
        Theta4_mem h4 (1 : ↥(H4 M)).2⟩ : ↥M.K4) = 1 := by
      apply Subtype.ext
      show diagGL (1 : GL (Fin 2) F) (dd4 1) = 1
      rw [dd4_one, diagGL_one]
    rw [this, map_one]
  map_mul' := by
    intro a b
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show diagGL ((a : GL (Fin 2) F) * (b : GL (Fin 2) F))
        (dd4 ((a : GL (Fin 2) F) * (b : GL (Fin 2) F))) =
      diagGL (a : GL (Fin 2) F) (dd4 a) * diagGL (b : GL (Fin 2) F) (dd4 b)
    rw [dd4_mul, diagGL_mul]

theorem Theta4_apply (M : ModelData F) (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2) (g : ↥(H4 M)) :
    Theta4 M h4 g = mkP M ⟨diagGL (g : GL (Fin 2) F) (dd4 (g : GL (Fin 2) F)), Theta4_mem h4 g.2⟩ :=
  rfl

theorem Theta4_injective (M : ModelData F) (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2) :
    Function.Injective (Theta4 M h4) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [Theta4_apply] at hg
  obtain ⟨s, hs⟩ := mem_Zs.1 ((QuotientGroup.eq_one_iff _).1 hg)
  have hs' : diagGL (g : GL (Fin 2) F) (dd4 (g : GL (Fin 2) F)) = diagGL (sc2 s) (sc2 s) := by
    rw [← scalar4_eq]; exact hs.symm
  obtain ⟨h1, h2⟩ := diagGL_inj hs'
  have h3 := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 1 1) h2
  have hs1 : s = 1 := by
    apply Units.ext
    simpa [dd4, coe_dgen, sc2, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using
      h3.symm
  apply Subtype.ext
  rw [h1, hs1, sc2_one]
  rfl

theorem negOne_mem_H4 (M : ModelData F) : (-1 : GL (Fin 2) F) ∈ H4 M :=
  ⟨M.neg_mem, by rw [unit_det_neg_one, one_pow]⟩

theorem Theta4_neg_one (M : ModelData F) (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2) :
    Theta4 M h4 ⟨-1, negOne_mem_H4 M⟩ = yP M := by
  rw [Theta4_apply]
  have h1 : dd4 (-1 : GL (Fin 2) F) = 1 := by
    rw [dd4, unit_det_neg_one, inv_one, dgen_one_one]
  show mkP M _ = mkP M M.yK
  congr 1
  apply Subtype.ext
  show diagGL (-1 : GL (Fin 2) F) (dd4 (-1)) = yGL F
  rw [h1]
  rfl

theorem H2_le_H4 {M : ModelData F} {a : GL (Fin 2) F} (ha : a ∈ M.H2) : a ∈ H4 M :=
  ⟨((M.mem_H2 _).1 ha).1, by rw [det_unit_of_H2 ha, one_pow]⟩

theorem Theta4_iota1 (M : ModelData F) (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2) (a : ↥M.H2)
    (ha : (a : GL (Fin 2) F) ∈ H4 M) : Theta4 M h4 ⟨a, ha⟩ = iota1 M a := by
  rw [Theta4_apply, iota1_apply]
  congr 1
  apply Subtype.ext
  show diagGL (a : GL (Fin 2) F) (dd4 (a : GL (Fin 2) F)) = blkL F a
  have : dd4 (a : GL (Fin 2) F) = 1 := by
    rw [dd4, det_unit_of_H2 a.2, inv_one, dgen_one_one]
  rw [this, blkL_apply]

theorem a0_mem_H4 {M : ModelData F} {i : Fˣ} (hii : i * i = -1) (ha₀ : dgen i 1 ∈ M.U2) :
    (dgen i 1 : GL (Fin 2) F) ∈ H4 M :=
  ⟨ha₀, by rw [unit_det_dgen, mul_one]; exact pow_four_of_sq hii⟩

theorem Theta4_a0 (M : ModelData F) {i : Fˣ} (hii : i * i = -1) (ha₀ : dgen i 1 ∈ M.U2)
    (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2) :
    Theta4 M h4 ⟨dgen i 1, a0_mem_H4 hii ha₀⟩ = dP M (dgen i 1) ha₀ := by
  rw [Theta4_apply, dP]
  congr 1
  apply Subtype.ext
  show diagGL (dgen i 1) (dd4 (dgen i 1)) = diagGL (dgen i 1) (dgen i 1)⁻¹
  rw [dd4, unit_det_dgen, mul_one, dgen_inv, inv_one]

theorem range_Theta4 (M : ModelData F) {i : Fˣ} (hii : i * i = -1) (ha₀ : dgen i 1 ∈ M.U2)
    (h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2) :
    (Theta4 M h4).range = K1 M ⊔ zpowers (dP M (dgen i 1) ha₀) := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Matrix.GeneralLinearGroup.det (g : GL (Fin 2) F) = i ^ k := by
      rcases units_cases_pow_four hii g.2.2 with h | h | h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨2, by rw [h, sq, hii]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
      · exact ⟨3, by rw [h, pow_succ, sq, hii]; simp⟩
    have hmem : (g : GL (Fin 2) F) * ((dgen i 1 : GL (Fin 2) F) ^ k)⁻¹ ∈ M.H2 := by
      rw [M.mem_H2]
      refine ⟨M.U2.mul_mem g.2.1 (M.U2.inv_mem (M.U2.pow_mem ha₀ k)), ?_⟩
      rw [← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, map_pow, unit_det_dgen,
        mul_one, hk, mul_inv_cancel]
      rfl
    have hmem4 : (g : GL (Fin 2) F) * ((dgen i 1 : GL (Fin 2) F) ^ k)⁻¹ ∈ H4 M := H2_le_H4 hmem
    have hg : g = ⟨_, hmem4⟩ * (⟨dgen i 1, a0_mem_H4 hii ha₀⟩ : ↥(H4 M)) ^ k := by
      apply Subtype.ext
      simp
    rw [hg, map_mul, map_pow, Theta4_a0 M hii ha₀ h4, Theta4_iota1 M h4 ⟨_, hmem⟩ hmem4]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) k)
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      exact ⟨⟨a, H2_le_H4 a.2⟩, Theta4_iota1 M h4 a (H2_le_H4 a.2)⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨dgen i 1, a0_mem_H4 hii ha₀⟩, Theta4_a0 M hii ha₀ h4⟩

theorem sc2_eq_dgen (c : Fˣ) : (sc2 c : GL (Fin 2) F) = dgen c c := by
  apply Units.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sc2, coe_dgen, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal]

theorem a0_sq_eq {i : Fˣ} (hii : i * i = -1) :
    (dgen i 1 : GL (Fin 2) F) * dgen i 1 = sc2 i * dgen i (-i) := by
  rw [sc2_eq_dgen, dgen_mul, dgen_mul]
  have : i * (-i) = 1 := by rw [mul_neg, hii, neg_neg]
  rw [this, mul_one]

theorem dgen_i_neg_i_mem_U2 {M : ModelData F} {i : Fˣ} (hii : i * i = -1) (hsc2 : sc2 i ∈ M.U2)
    (ha₀ : dgen i 1 ∈ M.U2) : (dgen i (-i) : GL (Fin 2) F) ∈ M.U2 := by
  have hinv : (sc2 (-i) : GL (Fin 2) F) = (sc2 i)⁻¹ := by
    rw [sc2_inv]
    congr 1
    have h1 : i * (-i) = 1 := by rw [mul_neg, hii, neg_neg]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have : (dgen i (-i) : GL (Fin 2) F) = dgen i 1 * (sc2 (-i) * dgen i 1) := by
    rw [sc2_eq_dgen, dgen_mul, dgen_mul]
    have h1 : (-i) * i = 1 := by rw [neg_mul, hii, neg_neg]
    rw [h1, mul_one, mul_one, one_mul]
  rw [this, hinv]
  exact M.U2.mul_mem ha₀ (M.U2.mul_mem (M.U2.inv_mem hsc2) ha₀)

theorem fusedPGL_of_surj4 {M : ModelData F} {i : Fˣ} (hii : i * i = -1) (hsc2 : sc2 i ∈ M.U2)
    (ha₀ : dgen i 1 ∈ M.U2) {q : ℕ}
    (hr : ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (Ψ : ↥(H4 M) →* PGL2 F₀),
      Nat.card F₀ = q ∧ Function.Surjective Ψ ∧
        ∀ g : ↥(H4 M), Ψ g = 1 ↔ ∃ c : Fˣ, (g : GL (Fin 2) F) = sc2 c) :
    FusedPGL (yP M) (K1 M) (dP M (dgen i 1) ha₀) q := by
  obtain ⟨F₀, iF, fF, Ψ, hq, hs, hk⟩ := hr
  have h4 : ∀ δ : Fˣ, δ ^ 4 = 1 → dgen δ 1 ∈ M.U2 := fun δ hδ =>
    dgen_mem_U2_of_pow_four hii ha₀ hδ
  refine ⟨Ψ.ker.map (Theta4 M h4), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (hk x).1 (MonoidHom.mem_ker.1 hx)
    rw [iota1_apply, Theta4_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show blkL F a * diagGL (x : GL (Fin 2) F) (dd4 (x : GL (Fin 2) F)) =
      diagGL (x : GL (Fin 2) F) (dd4 (x : GL (Fin 2) F)) * blkL F a
    rw [blkL_apply, diagGL_mul, diagGL_mul, hc, sc2_comm c (a : GL (Fin 2) F), one_mul, mul_one]
  · rw [← range_Theta4 M hii ha₀ h4]
    exact Subgroup.map_le_range _ _
  · refine ⟨⟨-1, negOne_mem_H4 M⟩, MonoidHom.mem_ker.2 ((hk _).2 ⟨-1, sc2_neg_one.symm⟩),
      Theta4_neg_one M h4⟩
  ·
    have hdU := dgen_i_neg_i_mem_U2 hii hsc2 ha₀
    have hdH2 : (dgen i (-i) : GL (Fin 2) F) ∈ M.H2 := by
      refine (M.mem_H2 _).2 ⟨hdU, ?_⟩
      rw [det_dgen]
      have : (i : F) * ((-i : Fˣ) : F) = 1 := by
        have := congrArg (fun u : Fˣ => (u : F)) hii
        simp only [Units.val_mul, Units.val_neg, Units.val_one] at this
        rw [Units.val_neg]
        linear_combination -this
      exact this
    have hscH4 : (sc2 i : GL (Fin 2) F) ∈ H4 M :=
      ⟨hsc2, by
        have : Matrix.GeneralLinearGroup.det (sc2 i : GL (Fin 2) F) = i * i := by
          rw [sc2_eq_dgen, unit_det_dgen]
        rw [this, hii]
        norm_num⟩
    have hmul : (⟨dgen i 1, a0_mem_H4 hii ha₀⟩ * ⟨dgen i 1, a0_mem_H4 hii ha₀⟩ : ↥(H4 M)) =
        ⟨sc2 i, hscH4⟩ * ⟨dgen i (-i), H2_le_H4 hdH2⟩ := Subtype.ext (a0_sq_eq hii)
    rw [← Theta4_a0 M hii ha₀ h4, ← map_mul, hmul, map_mul,
      Theta4_iota1 M h4 ⟨_, hdH2⟩ (H2_le_H4 hdH2)]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right
        (Subgroup.mem_map.2 ⟨⟨sc2 i, hscH4⟩, MonoidHom.mem_ker.2 ((hk _).2 ⟨i, rfl⟩), rfl⟩))
      (Subgroup.mem_sup_left ⟨_, rfl⟩)
  · obtain ⟨hn, ⟨e⟩⟩ := abs_quot_subgroup (Ψ.ker.map (Theta4 M h4)) _ (Theta4 M h4)
      (Theta4_injective M h4) (range_Theta4 M hii ha₀ h4) Ψ
      (fun g => Subgroup.mem_map_iff_mem (Theta4_injective M h4))
    exact ⟨hn, F₀, iF, fF, hq,
      ⟨e.trans ((MulEquiv.subgroupCongr (MonoidHom.range_eq_top.2 hs)).trans Subgroup.topEquiv)⟩⟩

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
