module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Block
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinCent
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
import CFSG.GroupTheory.PLayer.CentralQuotient
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ModelA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3

variable {F : Type} [Field F] [Finite F] (ν : Type) [Fintype ν] [DecidableEq ν]

abbrev Lam := Fin 2 ⊕ ν
abbrev Kap := Fin 2 ⊕ Lam ν
abbrev Top := Fin 2 ⊕ Kap ν

abbrev G := SpecialLinearGroup (Top ν) F

abbrev X := G ν (F := F) ⧸ Subgroup.center (G ν (F := F))

noncomputable abbrev π : G ν (F := F) →* X ν (F := F) := QuotientGroup.mk' _

@[expose] noncomputable def Φ :
    SpecialLinearGroup (Fin 2) F × (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) →*
      G ν (F := F) :=
  (blk (Kap ν)).comp (MonoidHom.prodMap (MonoidHom.id _)
    ((blk (Lam ν)).comp (MonoidHom.prodMap (MonoidHom.id _)
      ((blk ν).comp (MonoidHom.inl _ _)))))

theorem Φ_apply (P Q R : SpecialLinearGroup (Fin 2) F) :
    Φ ν (P, (Q, R)) = blk (Kap ν) (P, blk (Lam ν) (Q, blk ν (R, 1))) := rfl

theorem Φ_injective : Function.Injective (Φ ν (F := F)) := by
  rintro ⟨P, Q, R⟩ ⟨P', Q', R'⟩ h
  rw [Φ_apply, Φ_apply] at h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (blk_injective h)
  obtain ⟨h3, h4⟩ := Prod.ext_iff.1 (blk_injective h2)
  obtain ⟨h5, -⟩ := Prod.ext_iff.1 (blk_injective h4)
  simp only at h1 h3 h5
  rw [h1, h3, h5]

omit [Finite F] [Fintype ν] [DecidableEq ν] in
theorem isElemAbelian_zpowers {H : Type*} [Group H] {g : H} (hg : g ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers g) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 b.2
    change (a : H) * b = b * a
    rw [← hm, ← hk, zpow_mul_comm]
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hg, _root_.one_zpow]

omit [Finite F] [Fintype ν] [DecidableEq ν] in
theorem isElemAbelian_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] {K₁ : Subgroup H₁}
    {K₂ : Subgroup H₂} (h₁ : IsElemAbelian 3 K₁) (h₂ : IsElemAbelian 3 K₂) :
    IsElemAbelian 3 (K₁.prod K₂) := by
  have c₁ := h₁.1
  have c₂ := h₂.1
  refine ⟨⟨⟨fun a b => Subtype.ext (Prod.ext ?_ ?_)⟩⟩, fun x hx => Prod.ext (h₁.2 _ hx.1)
    (h₂.2 _ hx.2)⟩
  · exact congrArg Subtype.val (c₁.is_comm.comm ⟨(a : H₁ × H₂).1, a.2.1⟩ ⟨(b : H₁ × H₂).1, b.2.1⟩)
  · exact congrArg Subtype.val (c₂.is_comm.comm ⟨(a : H₁ × H₂).2, a.2.2⟩ ⟨(b : H₁ × H₂).2, b.2.2⟩)

@[expose] noncomputable def a₁ : G ν (F := F) := blk (Kap ν) (c3, 1)

@[expose] noncomputable def a₂ : G ν (F := F) := blk (Kap ν) (1, blk (Lam ν) (c3, 1))

@[expose] def Adom : Subgroup (SpecialLinearGroup (Fin 2) F ×
    (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)) :=
  (Subgroup.zpowers c3).prod ((Subgroup.zpowers c3).prod (Subgroup.zpowers c3))

@[expose] def A12dom : Subgroup (SpecialLinearGroup (Fin 2) F ×
    (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)) :=
  (Subgroup.zpowers c3).prod ((Subgroup.zpowers c3).prod ⊥)

@[expose] def A1dom : Subgroup (SpecialLinearGroup (Fin 2) F ×
    (SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F)) :=
  Subgroup.zpowers (c3, (1, 1))

theorem A1dom_le_A12dom : A1dom (F := F) ≤ A12dom := by
  rw [A1dom, Subgroup.zpowers_le]
  exact ⟨Subgroup.mem_zpowers _, Subgroup.one_mem _, Subgroup.one_mem _⟩

theorem A12dom_le_Adom : A12dom (F := F) ≤ Adom :=
  Subgroup.prod_mono le_rfl (Subgroup.prod_mono le_rfl bot_le)

theorem isElemAbelian_Adom : IsElemAbelian 3 (Adom (F := F)) :=
  isElemAbelian_prod (isElemAbelian_zpowers c3_pow_three)
    (isElemAbelian_prod (isElemAbelian_zpowers c3_pow_three)
      (isElemAbelian_zpowers c3_pow_three))

theorem orderOf_c3 : orderOf (c3 : SpecialLinearGroup (Fin 2) F) = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime c3_pow_three c3_ne_one

omit [Finite F] [Fintype ν] [DecidableEq ν] in
theorem card_prod_subgroup {H₁ H₂ : Type*} [Group H₁] [Group H₂] (K₁ : Subgroup H₁)
    (K₂ : Subgroup H₂) : Nat.card (K₁.prod K₂) = Nat.card K₁ * Nat.card K₂ := by
  rw [Nat.card_congr (Subgroup.prodEquiv K₁ K₂).toEquiv, Nat.card_prod]

theorem card_Adom : Nat.card (Adom (F := F)) = 3 ^ 3 := by
  rw [Adom, card_prod_subgroup, card_prod_subgroup, Nat.card_zpowers, orderOf_c3]
  norm_num

theorem card_A12dom : Nat.card (A12dom (F := F)) = 3 ^ 2 := by
  rw [A12dom, card_prod_subgroup, card_prod_subgroup, Nat.card_zpowers, orderOf_c3,
    Subgroup.card_bot]
  norm_num

theorem card_A1dom : Nat.card (A1dom (F := F)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [A1dom, Nat.card_zpowers]
  refine orderOf_eq_prime ?_ ?_
  · simp [c3_pow_three]
  · intro h
    exact c3_ne_one (congrArg Prod.fst h)

omit [Finite F] in
theorem blk_one_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    blk ι ((1 : SpecialLinearGroup (Fin 2) F), (1 : SpecialLinearGroup ι F)) = 1 :=
  map_one (blk ι)

theorem Φ_c3 : Φ ν ((c3 : SpecialLinearGroup (Fin 2) F), ((1 : SpecialLinearGroup (Fin 2) F), 1)) =
    a₁ ν := by
  rw [Φ_apply, blk_one_one, blk_one_one, a₁]

theorem Φ_c3' : Φ ν ((1 : SpecialLinearGroup (Fin 2) F), ((c3 : SpecialLinearGroup (Fin 2) F), 1)) =
    a₂ ν := by
  rw [Φ_apply, blk_one_one, a₂]

omit [Finite F] in
theorem eq_one_of_blk_one_mem_center {ι : Type} [Fintype ι] [DecidableEq ι]
    {Y : SpecialLinearGroup ι F}
    (h : blk ι (1, Y) ∈ Subgroup.center (SpecialLinearGroup (Fin 2 ⊕ ι) F)) : Y = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  rw [coe_blk] at hr
  have hr1 : r = 1 := by
    have := congrFun (congrFun hr (Sum.inl 0)) (Sum.inl 0)
    simpa [scalar_apply] using this
  rw [hr1, map_one, ← fromBlocks_one] at hr
  obtain ⟨-, -, -, h4⟩ := Matrix.fromBlocks_inj.1 hr
  exact Subtype.ext h4.symm

omit [Finite F] in
theorem centralizer_le_normalizer_blkRange (h3 : (3 : F) ≠ 0) {ι : Type} [Fintype ι]
    [DecidableEq ι] :
    Subgroup.centralizer ({blk ι (c3, 1)} : Set (SpecialLinearGroup (Fin 2 ⊕ ι) F)) ≤
      Subgroup.normalizer ((blkRange (F := F) (ι := ι) : Subgroup _) : Set _) := by
  intro g hg
  have hg' : g * blk ι (c3, 1) = blk ι (c3, 1) * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hgi : g⁻¹ * blk ι (c3, 1) = blk ι (c3, 1) * g⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.inv_mem _ hg)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_blkRange h3 hg'
  · intro hy
    have := conj_mem_blkRange h3 hgi hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this

omit [Finite F] in
@[expose] noncomputable def slReindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) : SpecialLinearGroup m F ≃* SpecialLinearGroup n F where
  toFun g := ⟨reindexAlgEquiv F F e (g : Matrix m m F), by
    rw [reindexAlgEquiv_apply, det_reindex_self]; exact g.2⟩
  invFun g := ⟨reindexAlgEquiv F F e.symm (g : Matrix n n F), by
    rw [reindexAlgEquiv_apply, det_reindex_self]; exact g.2⟩
  left_inv g := Subtype.ext (by simp)
  right_inv g := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    change reindexAlgEquiv F F e ((g : Matrix m m F) * h) =
      reindexAlgEquiv F F e (g : Matrix m m F) * reindexAlgEquiv F F e (h : Matrix m m F)
    exact map_mul _ _ _)

theorem isQuasisimple_SL {ι : Type} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι)
    (h4 : 4 ≤ Nat.card F) : CFSG.Open.IsQuasisimple (SpecialLinearGroup ι F) := by
  have h := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := F) hι h4
  have h' : CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin (Fintype.card ι)) F) :=
    ⟨Group.isPerfect_def.1 h.1, h.2.1⟩
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (slReindex (Fintype.equivFin ι)) h'

omit [Finite F] in
theorem blkInr_injective {ι : Type} [Fintype ι] [DecidableEq ι] :
    Function.Injective ((blk ι (F := F)).comp (MonoidHom.inr _ _)) := fun Y Y' h =>
  congrArg Prod.snd (blk_injective h)

@[expose] noncomputable def mapEquivOfKer {G₁ G₂ : Type*} [Group G₁] [Group G₂] (f : G₁ →* G₂)
    (K : Subgroup G₁) (hf : ∀ x ∈ K, f x = 1 → x = 1) : ↥(K.map f) ≃* ↥K :=
  ((MonoidHom.ofInjective (f := f.comp K.subtype) (by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hf x x.2 hx))).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))).symm

theorem isQuasisimple_blkRange {ι : Type} [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι)
    (h4 : 4 ≤ Nat.card F) : CFSG.Open.IsQuasisimple ↥(blkRange (F := F) (ι := ι)) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (MonoidHom.ofInjective (blkInr_injective (F := F) (ι := ι))).symm (isQuasisimple_SL hι h4)

omit [Finite F] in
@[expose] def w2 : SpecialLinearGroup (Fin 2) F := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
theorem c3_mul_w2_ne : (c3 : SpecialLinearGroup (Fin 2) F) * w2 ≠ w2 * c3 := by
  intro h
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  change (HMul.hMul (c3Mat : Matrix (Fin 2) (Fin 2) F)
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 =
    (HMul.hMul (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F)
      (c3Mat : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 at this
  simp [c3Mat, Matrix.mul_apply, Fin.sum_univ_two] at this

theorem three_dvd_blkRange {μ : Type} [Fintype μ] [DecidableEq μ] :
    3 ∣ Nat.card (↥(blkRange (F := F) (ι := Fin 2 ⊕ μ)) ⧸
      Subgroup.center ↥(blkRange (F := F) (ι := Fin 2 ⊕ μ))) := by
  set h₁ : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2 ⊕ (Fin 2 ⊕ μ)) F :=
    ((blk (Fin 2 ⊕ μ)).comp (MonoidHom.inr _ _)).comp ((blk μ).comp (MonoidHom.inl _ _))
  have hinj : Function.Injective h₁ := (blkInr_injective).comp fun P P' h =>
    congrArg Prod.fst (blk_injective h)
  have hmem : ∀ P, h₁ P ∈ blkRange (F := F) (ι := Fin 2 ⊕ μ) := fun P => ⟨_, rfl⟩
  refine CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
    Nat.prime_three (hmem c3) (hmem w2) (by rw [← map_pow, c3_pow_three, map_one]) ?_
  intro h
  exact c3_mul_w2_ne (hinj (by rw [map_mul, map_mul, h]))

@[expose] noncomputable def Asub : Subgroup (X ν (F := F)) := (Adom (F := F)).map ((π ν).comp (Φ ν))

@[expose] noncomputable def A12sub : Subgroup (X ν (F := F)) :=
  (A12dom (F := F)).map ((π ν).comp (Φ ν))

@[expose] noncomputable def A1sub : Subgroup (X ν (F := F)) :=
  (A1dom (F := F)).map ((π ν).comp (Φ ν))

@[expose] noncomputable def Jsub : Subgroup (X ν (F := F)) :=
  (blkRange (F := F) (ι := Kap ν)).map (π ν)

@[expose] noncomputable def J2sub : Subgroup (X ν (F := F)) :=
  ((blkRange (F := F) (ι := Lam ν)).map ((blk (Kap ν)).comp (MonoidHom.inr _ _))).map (π ν)

theorem A1sub_eq : A1sub ν (F := F) = Subgroup.zpowers (π ν (a₁ ν)) := by
  rw [A1sub, A1dom, MonoidHom.map_zpowers, MonoidHom.comp_apply, Φ_c3]

variable (hF : ∀ x : F, x ^ 3 = 1 → x = 1)
include hF

theorem center_noThree : ∀ z ∈ Subgroup.center (G ν (F := F)), z ^ 3 = 1 → z = 1 :=
  fun _ hz hz3 => eq_one_of_mem_center_of_pow_three hF hz hz3

theorem ker_Adom : ∀ x ∈ Adom (F := F), (π ν).comp (Φ ν) x = 1 → x = 1 := by
  intro x hx h1
  have hc : Φ ν x ∈ Subgroup.center (G ν (F := F)) := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : Φ ν x ^ 3 = 1 := by rw [← map_pow, isElemAbelian_Adom.2 x hx, map_one]
  exact Φ_injective ν (by rw [center_noThree ν hF _ hc h3, map_one])

theorem card_Asub : Nat.card (Asub ν (F := F)) = 3 ^ 3 := by
  rw [Asub, card_map_eq_of_ker _ _ (ker_Adom ν hF), card_Adom]

theorem card_A12sub : Nat.card (A12sub ν (F := F)) = 3 ^ 2 := by
  rw [A12sub, card_map_eq_of_ker _ _ fun x hx => ker_Adom ν hF x (A12dom_le_Adom hx),
    card_A12dom]

theorem card_A1sub : Nat.card (A1sub ν (F := F)) = 3 := by
  rw [A1sub, card_map_eq_of_ker _ _ fun x hx =>
    ker_Adom ν hF x (A12dom_le_Adom (A1dom_le_A12dom hx)), card_A1dom]

omit hF in
theorem a₁_pow_three : a₁ ν (F := F) ^ 3 = 1 := by
  rw [a₁, ← map_pow]
  simp only [Prod.pow_mk, c3_pow_three, one_pow]
  exact blk_one_one

omit hF in
theorem a₂_pow_three : a₂ ν (F := F) ^ 3 = 1 := by
  rw [a₂, ← map_pow]
  simp only [Prod.pow_mk, one_pow, ← map_pow, c3_pow_three]
  rw [blk_one_one, blk_one_one]

omit hF in
theorem centralizer_zpowers_eq {H : Type*} [Group H] (g : H) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup H) : Set H) =
      Subgroup.centralizer ({g} : Set H) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (by simp [Subgroup.mem_zpowers])
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hx).symm m).eq

omit hF in
theorem blkRange_le_centralizer {ι : Type} [Fintype ι] [DecidableEq ι] :
    blkRange (F := F) (ι := ι) ≤ Subgroup.centralizer ({blk ι (c3, 1)} : Set _) := by
  rintro _ ⟨Y, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, ← map_mul]
  congr 1
  ext : 1 <;> simp

omit hF in
theorem isSubnormal_blkRange (h3 : (3 : F) ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι] :
    CFSG.Open.IsSubnormal (blkRange (F := F) (ι := ι))
      (Subgroup.centralizer ({blk ι (c3, 1)} : Set _)) := by
  refine CFSG.Open.IsSubnormal.step blkRange_le_centralizer ⟨fun n hn g => ?_⟩
    (CFSG.Open.IsSubnormal.refl _)
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact conj_mem_blkRange h3 (Subgroup.mem_centralizer_singleton_iff.1 g.2) hn

theorem glaPComponent_J (h3 : (3 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    GLAPComponent 3 (Subgroup.centralizer ((A1sub ν (F := F) : Subgroup (X ν (F := F))) :
      Set (X ν (F := F)))) (Jsub ν) := by
  rw [A1sub_eq, centralizer_zpowers_eq, Jsub,
    centralizer_mk_eq _ le_rfl (center_noThree ν hF) (a₁_pow_three ν)]
  refine (CFSG.glaPComponent_map_bijective_of_ker_le_center Nat.prime_three (π ν) ?_).1 _ ?_
  · rintro y ⟨-, hy⟩ x -
    rw [QuotientGroup.ker_mk'] at hy
    exact Subgroup.mem_center_iff.1 hy x
  · refine CFSG.LocalAnalysis.GLTheoremA.S10.glaPComponent_of_quasisimple Nat.prime_three
      (isSubnormal_blkRange h3) (isQuasisimple_blkRange ?_ h4) three_dvd_blkRange
    simp [Fintype.card_sum]

omit hF in
theorem c3_one_mem_Adom : ((c3 : SpecialLinearGroup (Fin 2) F),
    ((1 : SpecialLinearGroup (Fin 2) F), (1 : SpecialLinearGroup (Fin 2) F))) ∈ Adom :=
  ⟨Subgroup.mem_zpowers _, Subgroup.one_mem _, Subgroup.one_mem _⟩

omit hF in
theorem Asub_le_normalizer (h3 : (3 : F) ≠ 0) :
    Asub ν (F := F) ≤ Subgroup.normalizer ((Jsub ν : Subgroup (X ν (F := F))) : Set (X ν)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hc : Φ ν x ∈ Subgroup.centralizer ({a₁ ν} : Set (G ν (F := F))) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← Φ_c3, ← map_mul, ← map_mul]
    exact congrArg (Φ ν) (congrArg Subtype.val
      (isElemAbelian_Adom.1.is_comm.comm ⟨x, hx⟩ ⟨_, c3_one_mem_Adom⟩))
  exact Subgroup.le_normalizer_map (π ν) ⟨_, centralizer_le_normalizer_blkRange h3 hc, rfl⟩

theorem ker_blkRange : ∀ y ∈ blkRange (F := F) (ι := Kap ν), π ν y = 1 → y = 1 := by
  rintro _ ⟨Y, rfl⟩ h1
  have hc := (QuotientGroup.eq_one_iff _).1 h1
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply] at hc ⊢
  rw [eq_one_of_blk_one_mem_center hc, blk_one_one]

theorem isQuasisimple_Jsub (h4 : 4 ≤ Nat.card F) : CFSG.Open.IsQuasisimple ↥(Jsub ν (F := F)) :=
  CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (mapEquivOfKer (π ν) _ (ker_blkRange ν hF))
    (isQuasisimple_blkRange (by simp [Fintype.card_sum]) h4)

theorem three_dvd_Jsub : 3 ∣ Nat.card ↥(Jsub ν (F := F)) := by
  rw [Jsub, card_map_eq_of_ker _ _ (ker_blkRange ν hF)]
  exact three_dvd_blkRange.trans (Subgroup.card_quotient_dvd_card _)

theorem centMod_Asub (h4 : 4 ≤ Nat.card F) :
    ∀ x ∈ Asub ν (F := F), CentMod 3 (Jsub ν) x → x ∈ A1sub ν := by
  rintro _ ⟨⟨P₀, Q₀, R₀⟩, hy, rfl⟩ hc
  have hcent := mem_centralizer_of_centMod (isQuasisimple_Jsub ν hF h4) (three_dvd_Jsub ν hF) hc
  set Y₀ : SpecialLinearGroup (Kap ν) F := blk (Lam ν) (Q₀, blk ν (R₀, 1)) with hY₀
  have hY₀c : Y₀ ∈ Subgroup.center (SpecialLinearGroup (Kap ν) F) := by
    rw [Subgroup.mem_center_iff]
    intro Y
    have h1 := Subgroup.mem_centralizer_iff.1 hcent (π ν (blk (Kap ν) (1, Y)))
      ⟨_, ⟨Y, rfl⟩, rfl⟩
    rw [MonoidHom.comp_apply, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq, Φ_apply, ← map_mul, ← map_mul, ← map_inv,
      ← map_mul] at h1
    have e : ((1, Y) * (P₀, Y₀))⁻¹ * ((P₀, Y₀) * (1, Y)) =
        ((1 : SpecialLinearGroup (Fin 2) F), (Y * Y₀)⁻¹ * (Y₀ * Y)) :=
      Prod.ext (by simp) rfl
    rw [← hY₀, e] at h1
    have e' : (Y * Y₀)⁻¹ * (Y₀ * Y) = 1 := eq_one_of_blk_one_mem_center h1
    rw [inv_mul_eq_one] at e'
    exact e'
  have hQ3 : Q₀ ^ 3 = 1 := (isElemAbelian_zpowers c3_pow_three).2 _ hy.2.1
  have hR3 : R₀ ^ 3 = 1 := (isElemAbelian_zpowers c3_pow_three).2 _ hy.2.2
  have hY₀3 : Y₀ ^ 3 = 1 := by
    rw [hY₀, ← map_pow, Prod.pow_mk, ← map_pow, Prod.pow_mk, hQ3, hR3, one_pow, blk_one_one,
      blk_one_one]
  have hY₀1 : Y₀ = 1 := eq_one_of_mem_center_of_pow_three hF hY₀c hY₀3
  rw [hY₀, ← blk_one_one] at hY₀1
  obtain ⟨hQ, hR⟩ := Prod.ext_iff.1 (blk_injective hY₀1)
  simp only at hQ hR
  rw [← blk_one_one] at hR
  have hR' := congrArg Prod.fst (blk_injective hR)
  simp only at hR'
  subst hQ hR'
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hy.1
  replace hm : c3 ^ m = P₀ := hm
  have e : ((c3 : SpecialLinearGroup (Fin 2) F),
      ((1 : SpecialLinearGroup (Fin 2) F), (1 : SpecialLinearGroup (Fin 2) F))) ^ m =
      (P₀, (1, 1)) := by
    rw [← hm]
    ext : 1 <;> simp
  exact ⟨_, Subgroup.zpow_mem_zpowers _ m, by rw [e]⟩

omit hF in
theorem A1sub_le_A12sub : A1sub ν (F := F) ≤ A12sub ν := Subgroup.map_mono A1dom_le_A12dom

omit hF in
theorem A12sub_le_Asub : A12sub ν (F := F) ≤ Asub ν := Subgroup.map_mono A12dom_le_Adom

omit hF in
theorem J2sub_le_Jsub : J2sub ν (F := F) ≤ Jsub ν := by
  refine Subgroup.map_mono ?_
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

omit hF in
theorem J2sub_le_centralizer :
    J2sub ν (F := F) ≤ Subgroup.centralizer ((A12sub ν : Subgroup (X ν (F := F))) : Set (X ν)) := by
  rintro _ ⟨_, ⟨_, ⟨R, rfl⟩, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨⟨P, Q, R'⟩, hz, rfl⟩
  have hR' : R' = 1 := Subgroup.mem_bot.1 hz.2.2
  subst hR'
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply]
  rw [← map_mul, ← map_mul, Φ_apply, blk_one_one, ← map_mul, ← map_mul]
  congr 2
  ext : 1
  · simp
  · simp only [Prod.snd_mul]
    rw [← map_mul, ← map_mul]
    congr 1
    ext : 1 <;> simp

theorem J2sub_normal (h3 : (3 : F) ≠ 0) :
    ((J2sub ν (F := F)).subgroupOf (Jsub ν ⊓
      Subgroup.centralizer ((A12sub ν : Subgroup (X ν (F := F))) : Set (X ν)))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hgJ, hgC⟩ := g.2
  obtain ⟨_, ⟨Y, rfl⟩, hgY⟩ := hgJ
  have ha₂ : π ν (a₂ ν (F := F)) ∈ A12sub ν (F := F) :=
    ⟨((1 : SpecialLinearGroup (Fin 2) F), ((c3 : SpecialLinearGroup (Fin 2) F), 1)),
      ⟨Subgroup.one_mem _, Subgroup.mem_zpowers _, Subgroup.one_mem _⟩, by
      rw [MonoidHom.comp_apply, Φ_c3']⟩
  have hcomm := Subgroup.mem_centralizer_iff.1 hgC _ ha₂
  rw [← hgY] at hcomm
  have hlift := mem_centralizer_of_mk_mem _ le_rfl (center_noThree ν hF) (a₂_pow_three ν)
    (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)
  have hY : Y * blk (Lam ν) (c3, 1) = blk (Lam ν) (c3, 1) * Y := by
    have e := Subgroup.mem_centralizer_singleton_iff.1 hlift
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, a₂, ← map_mul] at e
    simpa using congrArg Prod.snd (blk_injective e)
  obtain ⟨_, ⟨_, ⟨R, rfl⟩, rfl⟩, hnR⟩ := hn
  have hconj := conj_mem_blkRange h3 hY
    (⟨R, rfl⟩ : blk (Lam ν) (1, R) ∈ blkRange (F := F) (ι := Lam ν))
  refine ⟨_, ⟨_, hconj, rfl⟩, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgY, ← hnR]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply]
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  congr 2
  ext : 1 <;> simp

theorem isQuasisimple_J2sub (h4 : 4 ≤ Nat.card F) : CFSG.Open.IsQuasisimple ↥(J2sub ν (F := F)) := by
  have hker : ∀ y ∈ (blkRange (F := F) (ι := Lam ν)).map ((blk (Kap ν)).comp (MonoidHom.inr _ _)),
      π ν y = 1 → y = 1 := fun y hy => ker_blkRange ν hF y (by
    obtain ⟨y', -, rfl⟩ := hy
    exact ⟨y', rfl⟩)
  refine CFSG.ComponentClassification.Components.quasisimple_of_equiv
    ((mapEquivOfKer (π ν) _ hker).trans (mapEquivOfKer _ _ fun x _ hx => ?_))
    (isQuasisimple_blkRange (by simp [Fintype.card_sum]) h4)
  exact blkInr_injective (hx.trans (map_one _).symm)

theorem three_dvd_J2sub : 3 ∣ Nat.card (↥(J2sub ν (F := F)) ⧸ Subgroup.center ↥(J2sub ν)) := by
  set h₁ : SpecialLinearGroup (Fin 2) F →* X ν (F := F) :=
    (π ν).comp (((blk (Kap ν)).comp (MonoidHom.inr _ _)).comp
      (((blk (Lam ν)).comp (MonoidHom.inr _ _)).comp ((blk ν).comp (MonoidHom.inl _ _))))
  have hinj : Function.Injective h₁ := by
    rw [injective_iff_map_eq_one]
    intro P hP
    have h1 := ker_blkRange ν hF _ ⟨_, rfl⟩ hP
    have h2 := blkInr_injective (h1.trans (map_one _).symm)
    have h3 := blkInr_injective (h2.trans (map_one _).symm)
    exact congrArg Prod.fst (blk_injective (h3.trans (blk_one_one).symm))
  have hmem : ∀ P, h₁ P ∈ J2sub ν := fun P => ⟨_, ⟨_, ⟨_, rfl⟩, rfl⟩, rfl⟩
  refine CFSG.LocalAnalysis.GLTheoremA.H81.LinA3.dvd_card_quotient_center_of_not_commute
    Nat.prime_three (hmem c3) (hmem w2) (by rw [← map_pow, c3_pow_three, map_one]) ?_
  intro h
  exact c3_mul_w2_ne (hinj (by rw [map_mul, map_mul, h]))

theorem layer_ne_bot (h3 : (3 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    GLAPLayer 3 (Jsub ν (F := F) ⊓
      Subgroup.centralizer ((A12sub ν : Subgroup (X ν (F := F))) : Set (X ν))) ≠ ⊥ :=
  CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPLayer_ne_bot_of_normal_quasisimple Nat.prime_three
    (le_inf (J2sub_le_Jsub ν) (J2sub_le_centralizer ν)) (J2sub_normal ν hF h3)
    (isQuasisimple_J2sub ν hF h4) (three_dvd_J2sub ν hF)

omit hF in
@[expose] def negOne : SpecialLinearGroup (Fin 2) F := ⟨-1, by simp [Matrix.det_neg]⟩

omit hF in
theorem negOne_mul_comm (P : SpecialLinearGroup (Fin 2) F) : negOne * P = P * negOne :=
  Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F) =
    (P : Matrix (Fin 2) (Fin 2) F) * -1 by simp)

omit hF in
theorem negOne_sq : (negOne : SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  simp [negOne, sq]

omit hF in
@[expose] noncomputable def tG : G ν (F := F) := blk (Kap ν) (negOne, 1)

omit hF in
theorem tG_not_mem_center (h2 : (2 : F) ≠ 0) : tG ν (F := F) ∉ Subgroup.center (G ν) := by
  intro h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  rw [tG, coe_blk] at hr
  have e1 := congrFun (congrFun hr (Sum.inl 0)) (Sum.inl 0)
  have e2 := congrFun (congrFun hr (Sum.inr (Sum.inl 0))) (Sum.inr (Sum.inl 0))
  simp [scalar_apply, negOne] at e1 e2
  apply h2
  linear_combination e1 - e2

omit hF in
theorem t_ne_one (h2 : (2 : F) ≠ 0) : π ν (tG ν (F := F)) ≠ 1 := fun h =>
  tG_not_mem_center ν h2 ((QuotientGroup.eq_one_iff _).1 h)

omit hF in
theorem t_sq : π ν (tG ν (F := F)) ^ 2 = 1 := by
  rw [← map_pow, tG, ← map_pow, Prod.pow_mk, negOne_sq, one_pow, blk_one_one, map_one]

omit hF in
theorem Jsub_le_centralizer_t :
    Jsub ν (F := F) ≤ Subgroup.centralizer ({π ν (tG ν)} : Set (X ν (F := F))) := by
  rintro _ ⟨_, ⟨Y, rfl⟩, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, tG]
  simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, ← map_mul]
  congr 2
  ext : 1 <;> simp

omit hF in
theorem Asub_le_centralizer_t :
    Asub ν (F := F) ≤ Subgroup.centralizer ({π ν (tG ν)} : Set (X ν (F := F))) := by
  rintro _ ⟨⟨P, Q, R⟩, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul, tG,
    Φ_apply, ← map_mul, ← map_mul]
  congr 2
  ext : 1
  · exact (negOne_mul_comm P).symm
  · simp

theorem modelA_psl (h3 : (3 : F) ≠ 0) (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F) :
    ModelA (X ν (F := F)) :=
  ⟨Asub ν, A1sub ν, A12sub ν, Jsub ν, π ν (tG ν),
    CFSG.SectionRank.isElemAbelian_map isElemAbelian_Adom _, card_Asub ν hF,
    A1sub_le_A12sub ν, A12sub_le_Asub ν, card_A1sub ν hF, card_A12sub ν hF,
    glaPComponent_J ν hF h3 h4, Asub_le_normalizer ν h3, centMod_Asub ν hF h4,
    layer_ne_bot ν hF h3 h4, t_ne_one ν h2, t_sq ν, Jsub_le_centralizer_t ν,
    Asub_le_centralizer_t ν⟩

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.Lin

end
