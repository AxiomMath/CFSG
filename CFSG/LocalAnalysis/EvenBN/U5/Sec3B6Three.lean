module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Two
public import CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo)
open scoped Matrix MatrixGroups commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem proj_mul_comm_of_commutator_mem {A : Subgroup G} {x y : normalizer (A : Set G)}
    (hxy : ⁅(x : G), (y : G)⁆ ∈ A) : proj A x * proj A y = proj A y * proj A x := by
  have h1 : proj A ⁅x, y⁆ = 1 := proj_eq_one_iff.2 (by simpa [commutatorElement_def] using hxy)
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

theorem exists_proj_of_mem_bar {A X : Subgroup G} {x : Bar A} (hx : x ∈ bar A X) :
    ∃ y : normalizer (A : Set G), (y : G) ∈ X ∧ proj A y = x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, mem_subgroupOf.1 hy, rfl⟩

theorem mem_normalizer_lift_of_proj [Finite G] {A : Subgroup G} {Y : Subgroup (Bar A)}
    {g : normalizer (A : Set G)} (hg : proj A g ∈ normalizer (Y : Set (Bar A))) :
    (g : G) ∈ normalizer (lift Y : Set G) := by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxN, hxY⟩ := mem_lift_iff.1 hx
  refine mem_lift_iff.2 ⟨mul_mem (mul_mem g.2 hxN) (inv_mem g.2), ?_⟩
  have := (mem_normalizer_iff.1 hg _).1 hxY
  rwa [← map_inv, ← map_mul, ← map_mul] at this

end Generic

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

@[expose] def gv (h : UnitaryFieldData 2 f K) (v : Fin 2 → K) : hypSU h 2 1 :=
  (exists_Ssub_crd h v).choose

theorem gv_mem (v : Fin 2 → K) : gv h v ∈ Ssub h := (exists_Ssub_crd h v).choose_spec.1

theorem crd_gv (v : Fin 2 → K) : crd (gv h v) = v := (exists_Ssub_crd h v).choose_spec.2

theorem crd_inv_mul {g g' : hypSU h 2 1} (hg : g ∈ Ssub h) (hg' : g' ∈ Ssub h) :
    crd (g⁻¹ * g') = crd g' - crd g := by
  have h1 := crd_mul (inv_mem hg) hg
  rw [inv_mul_cancel, (crd_eq_zero_iff (one_mem _)).2 (one_mem _)] at h1
  rw [crd_mul (inv_mem hg) hg', eq_neg_of_add_eq_zero_left h1.symm, neg_add_eq_sub]

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

abbrev Hyp.tB (hd : d.Hyp) : Bar d.F := proj d.F ⟨d.t, hd.t_mem_normalizer_F⟩

abbrev HB (d : Data G h) : Subgroup (Bar d.F) :=
  bar d.F (normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G))

abbrev YB (d : Data G h) : Subgroup (Bar d.F) := bar d.F (d.F ⊔ d.A₃)

abbrev BB (d : Data G h) : Subgroup (Bar d.F) := bar d.F (d.F ⊔ d.B₃)

abbrev AB (d : Data G h) : Subgroup (Bar d.F) := bar d.F d.N₁

omit [Finite G] in
theorem t_mem_FB₃ (d : Data G h) : d.t ∈ d.F ⊔ d.B₃ :=
  mem_sup_right (mem_sup_left (mem_zpowers _))

omit [Finite G] in
theorem FA₃_le_FB₃ (d : Data G h) : d.F ⊔ d.A₃ ≤ d.F ⊔ d.B₃ := sup_le_sup_left d.A₃_le_B₃ _

theorem Hyp.N₁_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.N₁ ≤ normalizer (d.F : Set G) := fun _ hn =>
  hd.normalizer_B₁_le_normalizer_F hGMS (hd.N₁_le hn).1

theorem Hyp.proj_comm_FB₃ (hd : d.Hyp) {x y : normalizer (d.F : Set G)}
    (hx : (x : G) ∈ d.F ⊔ d.B₃) (hy : (y : G) ∈ d.F ⊔ d.B₃) :
    proj d.F x * proj d.F y = proj d.F y * proj d.F x :=
  proj_mul_comm_of_commutator_mem (hd.elemAbMod_F_FB₃.2 _ hx _ hy)

theorem Hyp.proj_sq_FB₃ (hd : d.Hyp) {x : normalizer (d.F : Set G)}
    (hx : (x : G) ∈ d.F ⊔ d.B₃) : proj d.F x * proj d.F x = 1 := by
  rw [← map_mul, proj_eq_one_iff]
  exact hd.elemAbMod_F_FB₃.1 _ hx

theorem Hyp.cosetData_bar (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CosetData (HB d) (YB d) hd.tB where
  mul_self := hd.proj_sq_FB₃ d.t_mem_FB₃
  le_centralizer := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_centralizer_singleton_iff.2
      (hd.proj_comm_FB₃ (d.FA₃_le_FB₃ (mem_subgroupOf.1 hy)) d.t_mem_FB₃)
  isElementaryAbelian := by
    refine isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact hd.proj_comm_FB₃ (d.FA₃_le_FB₃ (mem_subgroupOf.1 hx))
        (d.FA₃_le_FB₃ (mem_subgroupOf.1 hy))
    · rintro _ ⟨x, hx, rfl⟩
      exact hd.proj_sq_FB₃ (d.FA₃_le_FB₃ (mem_subgroupOf.1 hx))
  le_normalizer := bar_le_normalizer_bar le_sup_left (hd.normalizer_FB₃_le_normalizer_FA₃ hGMS)
  crossed_mem := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact proj_mem_bar (hd.cr_mem_FA₃ hGMS (mem_subgroupOf.1 hn))

theorem Hyp.exists_proj_eq_of_mem_HB (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {x : Bar d.F}
    (hx : x ∈ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F))) :
    ∃ c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G),
      ∃ hc : c ∈ normalizer (d.F : Set G), proj d.F ⟨c, hc⟩ = x := by
  obtain ⟨⟨n, hnF⟩, -, rfl⟩ := exists_proj_of_mem_bar (Subgroup.mem_inf.1 hx).1
  have hcomm := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hcomm
  change (n * d.t)⁻¹ * (d.t * n) ∈ d.F at hcomm
  have hnt : (n * d.t * n⁻¹)⁻¹ * d.t ∈ d.F := by
    have := (mem_normalizer_iff.1 hnF _).1 hcomm
    rwa [show n * ((n * d.t)⁻¹ * (d.t * n)) * n⁻¹ = (n * d.t * n⁻¹)⁻¹ * d.t by group] at this
  obtain ⟨y, hy, c, hc, rfl⟩ := hd.exists_F_mul hGMS (hd.mem_normalizer_B₁_of_conj hGMS hnF hnt)
  have hcF : c ∈ normalizer (d.F : Set G) := hd.normalizer_B₁_le_normalizer_F hGMS hc.1
  refine ⟨c, hc, hcF, proj_eq_proj_iff.2 ?_⟩
  change c⁻¹ * (y * c) ∈ d.F
  have := (mem_normalizer_iff.1 (inv_mem hcF) y).1 hy
  rw [inv_inv] at this
  rw [← mul_assoc]
  exact this

theorem Hyp.η_mem_normalizer_F (hd : d.Hyp) {g : hypSU h 2 1} (hg : g ∈ Ssub h) :
    d.η g ∈ normalizer (d.F : Set G) :=
  Subgroup.centralizer_le_normalizer _ (hd.A₃_le_centralizer_F ⟨g, hg, rfl⟩)

@[expose] def Hyp.ιfun (hd : d.Hyp) (v : Fin 2 → K) : Bar d.F :=
  proj d.F ⟨d.η (gv h v), hd.η_mem_normalizer_F (gv_mem v)⟩

theorem Hyp.proj_η_eq_ιfun (hd : d.Hyp) {g : hypSU h 2 1} (hg : g ∈ Ssub h) :
    proj d.F ⟨d.η g, hd.η_mem_normalizer_F hg⟩ = hd.ιfun (crd g) := by
  rw [Hyp.ιfun, proj_eq_proj_iff]
  change (d.η g)⁻¹ * d.η (gv h (crd g)) ∈ d.F
  rw [← map_inv, ← map_mul]
  have hm : g⁻¹ * gv h (crd g) ∈ Ssub h := mul_mem (inv_mem hg) (gv_mem _)
  have hv : g⁻¹ * gv h (crd g) ∈ Vsub h :=
    (crd_eq_zero_iff hm).1 (by rw [crd_inv_mul hg (gv_mem _), crd_gv, sub_self])
  exact hd.A₁_le_F ⟨_, hv, rfl⟩

theorem Hyp.ιfun_zero (hd : d.Hyp) : hd.ιfun (0 : Fin 2 → K) = 1 := by
  rw [Hyp.ιfun, proj_eq_one_iff]
  exact hd.A₁_le_F ⟨_, (crd_eq_zero_iff (gv_mem 0)).1 (crd_gv 0), rfl⟩

theorem Hyp.ιfun_add (hd : d.Hyp) (v w : Fin 2 → K) :
    hd.ιfun (v + w) = hd.ιfun v * hd.ιfun w := by
  have hm : gv h v * gv h w ∈ Ssub h := mul_mem (gv_mem v) (gv_mem w)
  have e := hd.proj_η_eq_ιfun hm
  rw [crd_mul (gv_mem v) (gv_mem w), crd_gv, crd_gv] at e
  rw [← e, Hyp.ιfun, Hyp.ιfun, ← map_mul]
  congr 1
  exact Subtype.ext (map_mul d.η _ _)

@[expose] def Hyp.ιHom (hd : d.Hyp) : Multiplicative (Fin 2 → K) →* Bar d.F where
  toFun m := hd.ιfun (Multiplicative.toAdd m)
  map_one' := hd.ιfun_zero
  map_mul' _ _ := hd.ιfun_add _ _

theorem Hyp.ιHom_apply (hd : d.Hyp) (m : Multiplicative (Fin 2 → K)) :
    hd.ιHom m = hd.ιfun (Multiplicative.toAdd m) := rfl

theorem Hyp.ιfun_eq_one_iff (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {v : Fin 2 → K} : hd.ιfun v = 1 ↔ v = 0 := by
  refine ⟨fun hv => ?_, fun hv => hv ▸ hd.ιfun_zero⟩
  rw [Hyp.ιfun, proj_eq_one_iff] at hv
  have hA : d.η (gv h v) ∈ d.A₁ := by
    rw [← hd.F_inf_A₃ hGMS]
    exact Subgroup.mem_inf.2 ⟨hv, ⟨_, gv_mem v, rfl⟩⟩
  obtain ⟨v', hv', he⟩ := hA
  have e : v' = gv h v := d.η_injOn (Ssub_le_Usub (Vsub_le_Ssub hv'))
    (Ssub_le_Usub (gv_mem v)) he
  rw [← crd_gv (h := h) v, ← e]
  exact (crd_eq_zero_iff (Vsub_le_Ssub hv')).2 hv'

theorem Hyp.ιHom_injective (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Function.Injective hd.ιHom := by
  refine (injective_iff_map_eq_one _).2 fun m hm => ?_
  rw [hd.ιHom_apply, hd.ιfun_eq_one_iff hGMS] at hm
  exact hm

theorem Hyp.range_ιHom (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    hd.ιHom.range = YB d := by
  ext y
  constructor
  · rintro ⟨m, rfl⟩
    exact proj_mem_bar (mem_sup_right ⟨gv h _, gv_mem _, rfl⟩)
  · intro hy
    obtain ⟨⟨x, hxN⟩, hx, rfl⟩ := exists_proj_of_mem_bar hy
    obtain ⟨y₁, hy₁, a, ⟨g, hg, rfl⟩, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (hd.A₃_le_normalizer_F hGMS) hx
    refine ⟨Multiplicative.ofAdd (crd g), ?_⟩
    rw [hd.ιHom_apply, toAdd_ofAdd, ← hd.proj_η_eq_ιfun hg, proj_eq_proj_iff]
    change (d.η g)⁻¹ * (y₁ * d.η g) ∈ d.F
    have := (mem_normalizer_iff.1 (inv_mem (hd.η_mem_normalizer_F hg)) y₁).1 hy₁
    rw [inv_inv] at this
    rw [← mul_assoc]
    exact this

@[expose] def Hyp.ιB (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Multiplicative (Fin 2 → K) ≃* YB d :=
  (MonoidHom.ofInjective (hd.ιHom_injective hGMS)).trans
    (MulEquiv.subgroupCongr (hd.range_ιHom hGMS))

theorem Hyp.coe_ιB (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (m : Multiplicative (Fin 2 → K)) :
    (hd.ιB hGMS m : Bar d.F) = hd.ιfun (Multiplicative.toAdd m) := rfl

theorem Hyp.exists_ιfun_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {w : Bar d.F} (hw : w ∈ YB d) : ∃ v : Fin 2 → K, hd.ιfun v = w := by
  rw [← hd.range_ιHom hGMS] at hw
  obtain ⟨m, rfl⟩ := hw
  exact ⟨Multiplicative.toAdd m, rfl⟩

theorem Hyp.proj_leviSU_conj (hd : d.Hyp) (B : SL(2, K))
    (hnF : d.η (UnitaryHigher.leviSU h 1 B) ∈ normalizer (d.F : Set G)) (v : Fin 2 → K) :
    proj d.F ⟨_, hnF⟩ * hd.ιfun v * (proj d.F ⟨_, hnF⟩)⁻¹ =
      hd.ιfun ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
  have p : IsUnit (B : Matrix (Fin 2) (Fin 2) K).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  have hs : lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) p * gv h v *
      (lev (hK := h) (B : Matrix (Fin 2) (Fin 2) K) p)⁻¹ ∈ Ssub h :=
    lev_conj_mem_Ssub _ p (gv_mem v)
  rw [Hyp.ιfun, ← map_inv, ← map_mul, ← map_mul]
  have e : (⟨d.η (UnitaryHigher.leviSU h 1 B), hnF⟩ *
      ⟨d.η (gv h v), hd.η_mem_normalizer_F (gv_mem v)⟩ *
        (⟨d.η (UnitaryHigher.leviSU h 1 B), hnF⟩ : normalizer (d.F : Set G))⁻¹ :
          normalizer (d.F : Set G)) = ⟨_, hd.η_mem_normalizer_F hs⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, lev_eq_leviSU B p]
  rw [e, hd.proj_η_eq_ιfun hs, crd_lev B (gv_mem v), crd_gv]

theorem Hyp.exists_SL_of_mem_N₁ (hd : d.Hyp) {n : G} (hn : n ∈ d.N₁) :
    ∃ B : SL(2, K), ∀ (hnF : n ∈ normalizer (d.F : Set G)) (v : Fin 2 → K),
      proj d.F ⟨n, hnF⟩ * hd.ιfun v * (proj d.F ⟨n, hnF⟩)⁻¹ =
        hd.ιfun ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hn
  exact ⟨B, fun hnF v => hd.proj_leviSU_conj B hnF v⟩

omit [Finite G] in
theorem η_leviSU_mem_N₁ (d : Data G h) (B : SL(2, K)) :
    d.η (UnitaryHigher.leviSU h 1 B) ∈ d.N₁ :=
  ⟨_, ⟨B, rfl⟩, rfl⟩

theorem Hyp.exists_semilinear_bar (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : Bar d.F} (hx : x ∈ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F))) :
    ∃ (σ : K ≃+* K) (κ : K) (M : Matrix (Fin 2) (Fin 2) K), κ ≠ 0 ∧ M.det ≠ 0 ∧
      ∀ v : Fin 2 → K, x * hd.ιfun v * x⁻¹ = hd.ιfun (κ • (M *ᵥ fun i => σ (v i))) := by
  obtain ⟨c, hc, hcF, rfl⟩ := hd.exists_proj_eq_of_mem_HB hGMS hx
  obtain ⟨σ, κ, M, hκ, hM, hs⟩ := hd.exists_semilinear hc
  refine ⟨σ, κ, M, hκ, hM, fun v => ?_⟩
  obtain ⟨g', hg', he, hcrd⟩ := hs (gv h v) (gv_mem v)
  rw [Hyp.ιfun, ← map_inv, ← map_mul, ← map_mul]
  have e : (⟨c, hcF⟩ * ⟨d.η (gv h v), hd.η_mem_normalizer_F (gv_mem v)⟩ *
      (⟨c, hcF⟩ : normalizer (d.F : Set G))⁻¹ : normalizer (d.F : Set G)) =
        ⟨d.η g', hd.η_mem_normalizer_F hg'⟩ := Subtype.ext he
  rw [e, hd.proj_η_eq_ιfun hg', hcrd, crd_gv]

theorem Hyp.AB_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    AB d ≤ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F)) := by
  rintro _ ⟨⟨n, hnF⟩, hn, rfl⟩
  have hn' := hd.N₁_le (mem_subgroupOf.1 hn)
  refine Subgroup.mem_inf.2 ⟨proj_mem_bar (hd.normalizer_B₁_le_normalizer_FB₃ hGMS hn'.1),
    mem_centralizer_singleton_iff.2 ?_⟩
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.1 hn'.2))

theorem Hyp.normalizes_AB (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∀ x ∈ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F)), ∀ g ∈ AB d, ∃ g' ∈ AB d, ∀ w ∈ YB d,
      x * g * x⁻¹ * w * (x * g * x⁻¹)⁻¹ = g' * w * g'⁻¹ := by
  intro x hx g hg
  obtain ⟨σ, κ, M, hκ, hM, hxs⟩ := hd.exists_semilinear_bar hGMS hx
  obtain ⟨⟨n, hnF⟩, hnN, rfl⟩ := exists_proj_of_mem_bar hg
  obtain ⟨B, hB⟩ := hd.exists_SL_of_mem_N₁ hnN
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  have hσB : ((B : Matrix (Fin 2) (Fin 2) K).map σ).det = 1 := by
    have e : (B : Matrix (Fin 2) (Fin 2) K).map σ =
        σ.toRingHom.mapMatrix (B : Matrix (Fin 2) (Fin 2) K) := rfl
    rw [e, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]
  have hdet : (M * (B : Matrix (Fin 2) (Fin 2) K).map σ * M⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hσB, mul_one, Matrix.det_nonsing_inv,
      Ring.mul_inverse_cancel _ hMu]
  let N : SL(2, K) := ⟨M * (B : Matrix (Fin 2) (Fin 2) K).map σ * M⁻¹, hdet⟩
  have hnN' := d.η_leviSU_mem_N₁ N
  have hnF' := hd.N₁_le_normalizer_F hGMS hnN'
  refine ⟨proj d.F ⟨_, hnF'⟩, proj_mem_bar hnN', fun w hw => ?_⟩
  obtain ⟨v, rfl⟩ := hd.exists_ιfun_eq hGMS hw
  set u : Fin 2 → K := fun i => σ.symm ((κ⁻¹ • (M⁻¹ *ᵥ v)) i) with hu
  have hσu : (fun i => σ (u i)) = κ⁻¹ • (M⁻¹ *ᵥ v) := by
    funext i
    simp only [hu, RingEquiv.apply_symm_apply]
  have hΛu : κ • (M *ᵥ fun i => σ (u i)) = v := by
    rw [hσu, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hMu,
      Matrix.one_mulVec, smul_smul, mul_inv_cancel₀ hκ, one_smul]
  have hx' : x⁻¹ * hd.ιfun v * x = hd.ιfun u := by
    rw [← hΛu, ← hxs u]
    group
  have hσBu : (fun i => σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ u) i)) =
      (B : Matrix (Fin 2) (Fin 2) K).map σ *ᵥ fun i => σ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_add, map_mul]
  have hmat : κ • (M *ᵥ fun i => σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ u) i)) =
      (M * (B : Matrix (Fin 2) (Fin 2) K).map σ * M⁻¹) *ᵥ v := by
    rw [hσBu, hσu, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hκ,
      one_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  calc x * proj d.F ⟨n, hnF⟩ * x⁻¹ * hd.ιfun v * (x * proj d.F ⟨n, hnF⟩ * x⁻¹)⁻¹ =
      x * (proj d.F ⟨n, hnF⟩ * (x⁻¹ * hd.ιfun v * x) * (proj d.F ⟨n, hnF⟩)⁻¹) * x⁻¹ := by
        group
    _ = x * (proj d.F ⟨n, hnF⟩ * hd.ιfun u * (proj d.F ⟨n, hnF⟩)⁻¹) * x⁻¹ := by rw [hx']
    _ = x * hd.ιfun ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ u) * x⁻¹ := by rw [hB hnF u]
    _ = hd.ιfun (κ • (M *ᵥ fun i => σ (((B : Matrix (Fin 2) (Fin 2) K) *ᵥ u) i))) := hxs _
    _ = hd.ιfun ((N : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by rw [hmat]
    _ = _ := (hd.proj_leviSU_conj N hnF' v).symm

theorem Hyp.exists_AB_conj (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {y y' : Bar d.F} (hy : y ∈ YB d) (hy' : y' ∈ YB d) (hy1 : y ≠ 1) (hy'1 : y' ≠ 1) :
    ∃ a ∈ AB d, a * y * a⁻¹ = y' := by
  obtain ⟨v, rfl⟩ := hd.exists_ιfun_eq hGMS hy
  obtain ⟨v', rfl⟩ := hd.exists_ιfun_eq hGMS hy'
  have hv : v ≠ 0 := fun e => hy1 ((hd.ιfun_eq_one_iff hGMS).2 e)
  have hv' : v' ≠ 0 := fun e => hy'1 ((hd.ιfun_eq_one_iff hGMS).2 e)
  obtain ⟨B, hB⟩ := CFSG.LocalAnalysis.EvenBN.LinearThree.Plane.exists_sl_smul hv hv'
  have hnN := d.η_leviSU_mem_N₁ B
  have hnF := hd.N₁_le_normalizer_F hGMS hnN
  refine ⟨proj d.F ⟨_, hnF⟩, proj_mem_bar hnN, ?_⟩
  rw [hd.proj_leviSU_conj B hnF v]
  exact congrArg hd.ιfun hB

theorem Hyp.htr_bar (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∀ y ∈ YB d, ∃ g ∈ HB d, g⁻¹ * hd.tB * g = hd.tB * y := by
  have hc := hd.cosetData_bar hGMS
  obtain ⟨y₀, hy₀N, hy₀B⟩ := hd.exists_mem_normalizer_FB₃_not_mem_normalizer_B₁ hGMS
  have hy₀F := hd.normalizer_FB₃_le_normalizer_F hGMS hy₀N
  set x₀ : Bar d.F := proj d.F ⟨y₀, hy₀F⟩ with hx₀
  have hx₀H : x₀ ∈ HB d := proj_mem_bar hy₀N
  set c₀ := x₀⁻¹ * hd.tB * x₀ * hd.tB with hc₀def
  have hc₀ : c₀ ∈ YB d := hc.crossed_mem x₀ hx₀H
  have h1 : x₀⁻¹ * hd.tB * x₀ = hd.tB * c₀ := hc.conj_eq_mul hx₀H
  have hc₀1 : c₀ ≠ 1 := by
    intro e
    apply hy₀B
    have h2 : x₀⁻¹ * hd.tB * x₀ = hd.tB := by rw [h1, e, mul_one]
    rw [hx₀, ← map_inv, ← map_mul, ← map_mul, proj_eq_proj_iff] at h2
    change (y₀⁻¹ * d.t * y₀)⁻¹ * d.t ∈ d.F at h2
    have h3 := hd.mem_normalizer_B₁_of_conj hGMS (inv_mem hy₀F) (x := y₀⁻¹)
      (by rwa [inv_inv])
    simpa using inv_mem h3
  intro y hy
  by_cases hy1 : y = 1
  · exact ⟨1, one_mem _, by rw [hy1]; group⟩
  obtain ⟨a, haA, hay⟩ := hd.exists_AB_conj hGMS hc₀ hy hc₀1 hy1
  have haC := hd.AB_le hGMS haA
  have hat : a * hd.tB = hd.tB * a := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 haC).2
  refine ⟨x₀ * a⁻¹, mul_mem hx₀H (inv_mem (Subgroup.mem_inf.1 haC).1), ?_⟩
  calc (x₀ * a⁻¹)⁻¹ * hd.tB * (x₀ * a⁻¹) = a * (x₀⁻¹ * hd.tB * x₀) * a⁻¹ := by group
    _ = a * (hd.tB * c₀) * a⁻¹ := by rw [h1]
    _ = (a * hd.tB) * c₀ * a⁻¹ := by group
    _ = hd.tB * (a * c₀ * a⁻¹) := by rw [hat]; group
    _ = hd.tB * y := by rw [hay]

theorem Hyp.kernel_bar_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    HB d ⊓ centralizer (YB d : Set (Bar d.F)) ⊓ centralizer ({hd.tB} : Set (Bar d.F)) ≤
      BB d := by
  intro k hk
  obtain ⟨⟨hkH, hkY⟩, hkt⟩ := hk
  obtain ⟨c, hc, hcF, rfl⟩ := hd.exists_proj_eq_of_mem_HB hGMS (Subgroup.mem_inf.2 ⟨hkH, hkt⟩)
  have hcA : ∀ a ∈ d.A₃, c * a * c⁻¹ * a⁻¹ ∈ d.A₁ := by
    intro a ha
    have haF : a ∈ normalizer (d.F : Set G) := hd.A₃_le_normalizer_F hGMS ha
    have hcomm := mem_centralizer_iff.1 hkY (proj d.F ⟨a, haF⟩) (proj_mem_bar (mem_sup_right ha))
    rw [← map_mul, ← map_mul, proj_eq_proj_iff] at hcomm
    change (a * c)⁻¹ * (c * a) ∈ d.F at hcomm
    have h1 : c * a * c⁻¹ * a⁻¹ ∈ d.F := by
      have := (mem_normalizer_iff.1 (mul_mem haF hcF) _).1 hcomm
      rwa [show a * c * ((a * c)⁻¹ * (c * a)) * (a * c)⁻¹ = c * a * c⁻¹ * a⁻¹ by group] at this
    have h2 : c * a * c⁻¹ * a⁻¹ ∈ d.A₃ :=
      mul_mem ((mem_normalizer_iff.1 (hd.normalizer_B₁_le_normalizer_A₃ hc.1) a).1 ha) (inv_mem ha)
    rw [← hd.F_inf_A₃ hGMS]
    exact Subgroup.mem_inf.2 ⟨h1, h2⟩
  exact proj_mem_bar (mem_sup_right (hd.mem_B₃_of_commutator_mem_A₁ hc hcA))

theorem Hyp.le_BB_of_normal (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {R : Subgroup (Bar d.F)} (hR : R ≤ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F)))
    (hRn : HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F)) ≤ normalizer (R : Set (Bar d.F)))
    (hR2 : IsPGroup 2 R) : R ≤ BB d := by
  set R' := lift R ⊓ (normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G)) with hR'
  have hcH : ∀ c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G),
      ∀ hcF : c ∈ normalizer (d.F : Set G),
        proj d.F ⟨c, hcF⟩ ∈ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F)) := by
    intro c hc hcF
    refine Subgroup.mem_inf.2 ⟨proj_mem_bar (hd.normalizer_B₁_le_normalizer_FB₃ hGMS hc.1),
      mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (mem_centralizer_singleton_iff.1 hc.2))
  have hR'n : normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      normalizer (R' : Set G) := by
    intro c hc
    have hcF : c ∈ normalizer (d.F : Set G) := hd.normalizer_B₁_le_normalizer_F hGMS hc.1
    exact Common.mem_normalizer_inf (mem_normalizer_lift_of_proj (g := ⟨c, hcF⟩)
      (hRn (hcH c hc hcF))) (le_normalizer hc)
  have hR'2 : IsPGroup 2 R' := by
    rintro ⟨r, hr⟩
    obtain ⟨hrN, hrR⟩ := mem_lift_iff.1 (Subgroup.mem_inf.1 hr).1
    obtain ⟨k, hk⟩ := hR2 ⟨_, hrR⟩
    have hk' : proj d.F (⟨r, hrN⟩ ^ 2 ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    have hkF : r ^ 2 ^ k ∈ d.F := by
      have := proj_eq_one_iff.1 hk'
      rwa [Subgroup.coe_pow] at this
    obtain ⟨m, hm⟩ := hd.isPGroup_F ⟨_, hkF⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have hm' : (r ^ 2 ^ k) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul, hm']
  have hR'B := hd.le_B₃_of_normal (inf_le_right : R' ≤ _) hR'n hR'2
  intro x hx
  obtain ⟨c, hc, hcF, rfl⟩ := hd.exists_proj_eq_of_mem_HB hGMS (hR hx)
  exact proj_mem_bar (mem_sup_right (hR'B (Subgroup.mem_inf.2
    ⟨mem_lift_of_proj_mem hx, hc⟩)))

theorem Hyp.isPGroup_BB (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    IsPGroup 2 (BB d) :=
  isPGroup_bar (IsPGroup.of_card (n := 1 + f * 12) (by rw [hd.card_FB₃ hGMS, pow_add, pow_one,
    pow_mul]))

theorem Hyp.two_core_bar (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    oTwo (HB d) ≤ centralizer (YB d : Set (Bar d.F)) ∧
      oTwo (HB d) ⊓ centralizer ({hd.tB} : Set (Bar d.F)) = BB d ∧
      (∀ y ∈ YB d, ∃ x ∈ oTwo (HB d), x⁻¹ * hd.tB * x = hd.tB * y) ∧
      ∀ g ∈ HB d, ∃ c ∈ HB d ⊓ centralizer ({hd.tB} : Set (Bar d.F)),
        ∃ x ∈ oTwo (HB d), g = c * x := by
  have := h.charP
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hc := hd.cosetData_bar hGMS
  have hBn : HB d ≤ normalizer (BB d : Set (Bar d.F)) := bar_le_normalizer_bar le_sup_left le_rfl
  have hBK : BB d ≤ HB d ⊓ centralizer (YB d : Set (Bar d.F)) ⊓
      centralizer ({hd.tB} : Set (Bar d.F)) := by
    rintro _ ⟨b, hb, rfl⟩
    have hb' := mem_subgroupOf.1 hb
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨proj_mem_bar (le_normalizer hb'), ?_⟩,
      mem_centralizer_singleton_iff.2 (hd.proj_comm_FB₃ hb' d.t_mem_FB₃)⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact hd.proj_comm_FB₃ (d.FA₃_le_FB₃ (mem_subgroupOf.1 hy)) hb'
  refine hc.sl_two_core (hd.ιB hGMS) (hd.htr_bar hGMS) (hd.AB_le hGMS) (fun g hg => ?_)
    (fun M => ?_) (hd.normalizes_AB hGMS) (hd.isPGroup_BB hGMS) hBK hBn
    (fun R hR hRn hR2 => hd.le_BB_of_normal hGMS hR hRn hR2) (fun a ha k hk => ?_)
  · obtain ⟨⟨n, hnF⟩, hnN, rfl⟩ := exists_proj_of_mem_bar hg
    obtain ⟨B, hB⟩ := hd.exists_SL_of_mem_N₁ hnN
    exact ⟨B, fun v => by rw [hd.coe_ιB, hd.coe_ιB, toAdd_ofAdd, toAdd_ofAdd]; exact hB hnF v⟩
  · have hnN := d.η_leviSU_mem_N₁ M
    have hnF := hd.N₁_le_normalizer_F hGMS hnN
    exact ⟨proj d.F ⟨_, hnF⟩, proj_mem_bar hnN, fun v => by
      rw [hd.coe_ιB, hd.coe_ιB, toAdd_ofAdd, toAdd_ofAdd]
      exact hd.proj_leviSU_conj M hnF v⟩
  · have hkB := hd.kernel_bar_le hGMS hk
    have haH := (Subgroup.mem_inf.1 (hd.AB_le hGMS ha)).1
    exact mul_mem ((mem_normalizer_iff.1 (hBn haH) k).1 hkB) (inv_mem hkB)

end Data

end CFSG.LocalAnalysis.EvenBN.U5
