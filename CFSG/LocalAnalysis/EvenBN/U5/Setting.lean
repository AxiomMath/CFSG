module

public import CFSG.LocalAnalysis.EvenSmallLie.Children
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionKernel
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.RankThree.PartOne.U5K.Hyp.Aut

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf)

structure U5Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) : Prop where
  std : CFSG.EvenSmallLie.StandardSetting G L
  two_le : 2 ≤ f
  center_eq_bot : center L = ⊥
  model : LieModel L .PSU 5 2 f

@[expose] def CenterlessExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ), U5Setting G L f → False

theorem exists_hypPSU_equiv {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (hX : LieModel X .PSU 5 2 f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K), Nonempty (X ≃* hypPSU h 2 1) := by
  rcases hX with ⟨-, -, K, _, _, hcard, ⟨e⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have h : UnitaryFieldData 2 f K :=
      ⟨Nat.prime_two, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
    obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
    exact ⟨K, _, h, ⟨e.trans (hypPSUEquivStatedProj h hR (by norm_num)).symm⟩⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

variable {G : Type} [Group G] {f : ℕ} {K : Type} [Field K]

structure Data (G : Type) [Group G] (h : UnitaryFieldData 2 f K) where
  L : Subgroup G
  e : L ≃* hypPSU h 2 1
  t : G
  T : Subgroup G

namespace Data

variable {h : UnitaryFieldData 2 f K} (d : Data G h)

@[expose] def η : hypSU h 2 1 →* G :=
  d.L.subtype.comp (d.e.symm.toMonoidHom.comp (hypProj h 2 1))

@[expose] def pull (M : Subgroup (hypSU h 2 1)) : Subgroup G := M.map d.η

@[expose] def P : Subgroup G := d.pull (hypUnitriangular h 2 1)

@[expose] def A₁ : Subgroup G := d.pull (Vsub h)

@[expose] def A₃ : Subgroup G := d.pull (Ssub h)

@[expose] def B₁ : Subgroup G := zpowers d.t ⊔ d.A₁

@[expose] def B₃ : Subgroup G := zpowers d.t ⊔ d.A₃

@[expose] def tP : Subgroup G := zpowers d.t ⊔ d.P

@[expose] def ZtP : Subgroup G := CFSG.centerIn d.tP

@[expose] def B₄ : Subgroup G :=
  CFSG.ABGTheoremB.pCoreIn 2 (normalizer (d.ZtP : Set G))

@[expose] def act : normalizer (d.L : Set G) →* MulAut (hypPSU h 2 1) :=
  (MulAut.congr d.e).toMonoidHom.comp d.L.normalizerMonoidHom

structure Hyp [Finite G] : Prop where
  setting : U5Setting G d.L f
  t_mem : d.t ∈ centralizer (d.L : Set G)
  t_two : orderOf d.t = 2
  T_syl : IsSylowOf 2 d.T (centralizer ({d.t} : Set G))
  P_le : d.P ≤ d.T

theorem η_apply (g : hypSU h 2 1) : d.η g = ((d.e.symm (hypProj h 2 1 g) : d.L) : G) := rfl

theorem η_mem (g : hypSU h 2 1) : d.η g ∈ d.L := (d.e.symm (hypProj h 2 1 g)).2

theorem pull_le_L (M : Subgroup (hypSU h 2 1)) : d.pull M ≤ d.L := by
  rintro _ ⟨g, -, rfl⟩
  exact d.η_mem g

theorem pull_mono {M M' : Subgroup (hypSU h 2 1)} (hM : M ≤ M') : d.pull M ≤ d.pull M' :=
  Subgroup.map_mono hM

theorem range_η : d.η.range = d.L := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact d.η_mem g
  · intro hx
    obtain ⟨g, hg⟩ := hypProj_surjective h 2 1 (d.e ⟨x, hx⟩)
    refine ⟨g, ?_⟩
    rw [η_apply, hg, MulEquiv.symm_apply_apply]

theorem ker_η : d.η.ker = hypScalars h 2 1 := by
  ext g
  have hk := SetLike.ext_iff.1 (ker_hypProj h 2 1) g
  rw [MonoidHom.mem_ker] at hk
  rw [MonoidHom.mem_ker, η_apply, ← hk]
  constructor
  · intro hg
    have h1 : d.e.symm (hypProj h 2 1 g) = 1 := Subtype.ext hg
    rwa [MulEquiv.map_eq_one_iff] at h1
  · intro hg
    rw [hg, map_one]
    rfl

theorem η_injOn {g g' : hypSU h 2 1} (hg : g ∈ hypUnitriangular h 2 1)
    (hg' : g' ∈ hypUnitriangular h 2 1) (hgg : d.η g = d.η g') : g = g' := by
  have h1 : g⁻¹ * g' ∈ d.η.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgg, inv_mul_cancel]
  rw [ker_η] at h1
  have h2 : g⁻¹ * g' ∈ hypUnitriangular h 2 1 ⊓ hypScalars h 2 1 :=
    Subgroup.mem_inf.2 ⟨(hypUnitriangular h 2 1).mul_mem ((hypUnitriangular h 2 1).inv_mem hg)
      hg', h1⟩
  rw [Usub_inf_scalars, mem_bot] at h2
  exact inv_mul_eq_one.1 h2

theorem card_pull {M : Subgroup (hypSU h 2 1)} (hM : M ≤ hypUnitriangular h 2 1) :
    Nat.card (d.pull M) = Nat.card M := by
  have hinj : Function.Injective (d.η.comp M.subtype) := fun a b hab =>
    Subtype.ext (d.η_injOn (hM a.2) (hM b.2) hab)
  have e : M ≃* d.pull M := (MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]; rfl))
  exact (Nat.card_congr e.toEquiv).symm

theorem coe_e_symm_act_apply (n : normalizer (d.L : Set G)) (p : hypPSU h 2 1) :
    ((d.e.symm (d.act n p) : d.L) : G) = n * (d.e.symm p : G) * (n : G)⁻¹ := by
  simp [act, MulAut.congr_apply]

theorem act_eq_one_iff (n : normalizer (d.L : Set G)) :
    d.act n = 1 ↔ (n : G) ∈ centralizer (d.L : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro x hx
    have h2 := d.coe_e_symm_act_apply n (d.e ⟨x, hx⟩)
    rw [h1, MulAut.one_apply, MulEquiv.symm_apply_apply] at h2
    change x = n * x * (n : G)⁻¹ at h2
    calc x * n = n * x * (n : G)⁻¹ * n := by rw [← h2]
      _ = n * x := by group
  · intro h1
    refine MulEquiv.ext fun p => d.e.symm.injective (Subtype.ext ?_)
    rw [coe_e_symm_act_apply, MulAut.one_apply, ← mem_centralizer_iff.1 h1 _ (d.e.symm p).2]
    group

theorem act_η (g : hypSU h 2 1) :
    d.act ⟨d.η g, le_normalizer (d.η_mem g)⟩ = innM h g := by
  refine MulEquiv.ext fun p => d.e.symm.injective (Subtype.ext ?_)
  rw [coe_e_symm_act_apply, innM_apply, map_mul, map_mul, map_inv]
  simp [η_apply]

@[expose] def actImage (X : Subgroup G) : Subgroup (MulAut (hypPSU h 2 1)) :=
  (X.subgroupOf (normalizer (d.L : Set G))).map d.act

theorem mem_actImage {X : Subgroup G} {ρ : MulAut (hypPSU h 2 1)} :
    ρ ∈ d.actImage X ↔ ∃ x ∈ X, ∃ hx : x ∈ normalizer (d.L : Set G), d.act ⟨x, hx⟩ = ρ := by
  constructor
  · rintro ⟨⟨x, hxN⟩, hx, rfl⟩
    exact ⟨x, hx, hxN, rfl⟩
  · rintro ⟨x, hx, hxN, rfl⟩
    exact ⟨⟨x, hxN⟩, hx, rfl⟩

theorem actImage_pull (M : Subgroup (hypSU h 2 1)) : d.actImage (d.pull M) = M.map (innM h) := by
  ext ρ
  rw [mem_actImage]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, hxN, rfl⟩
    exact ⟨g, hg, (d.act_η g).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨d.η g, ⟨g, hg, rfl⟩, le_normalizer (d.η_mem g), d.act_η g⟩

theorem actImage_P : d.actImage d.P = Uh h := d.actImage_pull _

theorem actImage_A₁ : d.actImage d.A₁ = Vh h := d.actImage_pull _

theorem actImage_A₃ : d.actImage d.A₃ = Sh h := d.actImage_pull _

theorem actImage_L : d.actImage d.L = Pi h := by
  have : d.L = d.pull ⊤ := by
    rw [pull, ← MonoidHom.range_eq_map, range_η]
  rw [this, actImage_pull, ← MonoidHom.range_eq_map, range_innM]

theorem act_mem_Pi_iff {x : G} (hx : x ∈ normalizer (d.L : Set G)) :
    d.act ⟨x, hx⟩ ∈ Pi h ↔ x ∈ d.L ⊔ centralizer (d.L : Set G) := by
  constructor
  · intro hP
    rw [← d.actImage_L, mem_actImage] at hP
    obtain ⟨a, haL, haN, ha⟩ := hP
    have h1 : d.act (⟨a, haN⟩⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, ha, inv_mul_cancel]
    have h2 : a⁻¹ * x ∈ centralizer (d.L : Set G) := (d.act_eq_one_iff _).1 h1
    rw [show x = a * (a⁻¹ * x) by group]
    exact mul_mem_sup haL h2
  · intro hmem
    let M : Subgroup G := ((Pi h).comap d.act).map (normalizer (d.L : Set G)).subtype
    have hLM : d.L ≤ M := fun a ha => ⟨⟨a, le_normalizer ha⟩,
      mem_comap.2 (by rw [← d.actImage_L, mem_actImage]; exact ⟨a, ha, _, rfl⟩), rfl⟩
    have hCM : centralizer (d.L : Set G) ≤ M := fun c hc =>
      ⟨⟨c, centralizer_le_normalizer _ hc⟩,
        mem_comap.2 (by rw [(d.act_eq_one_iff _).2 hc]; exact one_mem _), rfl⟩
    obtain ⟨n, hn, hnx⟩ := sup_le hLM hCM hmem
    have : n = ⟨x, hx⟩ := Subtype.ext hnx
    rw [← this]
    exact hn

theorem card_U : Nat.card (hypUnitriangular h 2 1) = (2 ^ f) ^ 10 := by
  have := (unitary_order_and_Sylow h (r := 2) (ε := 1) (by norm_num) (by norm_num)).1
  rw [this]

theorem card_P : Nat.card d.P = (2 ^ f) ^ 10 := by
  rw [P, d.card_pull le_rfl, card_U]

theorem card_A₁ : Nat.card d.A₁ = (2 ^ f) ^ 4 := by
  rw [A₁, d.card_pull (Vsub_le_Ssub.trans Ssub_le_Usub), card_Vsub]

theorem isPGroup_P : IsPGroup 2 d.P :=
  IsPGroup.of_card (n := f * 10) (by rw [card_P, ← pow_mul])

theorem A₁_le_A₃ : d.A₁ ≤ d.A₃ := d.pull_mono Vsub_le_Ssub

theorem A₃_le_P : d.A₃ ≤ d.P := d.pull_mono Ssub_le_Usub

theorem A₁_le_P : d.A₁ ≤ d.P := d.A₁_le_A₃.trans d.A₃_le_P

theorem P_le_L : d.P ≤ d.L := d.pull_le_L _

theorem A₁_comm_sq : (∀ x ∈ d.A₁, ∀ y ∈ d.A₁, x * y = y * x) ∧ ∀ x ∈ d.A₁, x * x = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨v', hv', rfl⟩
    rw [← map_mul, ← map_mul, Vsub_comm hv hv']
  · rintro _ ⟨v, hv, rfl⟩
    rw [← map_mul, Vsub_sq hv, map_one]

theorem _root_.CFSG.LocalAnalysis.EvenBN.U5.isElementaryAbelian_of_forall {X : Subgroup G}
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hsq : ∀ x ∈ X, x * x = 1) :
    CFSG.IsElementaryAbelian 2 X := CFSG.IsElementaryAbelian.two_of_forall_mul_self hcomm hsq

theorem isElementaryAbelian_A₁ : CFSG.IsElementaryAbelian 2 d.A₁ :=
  isElementaryAbelian_of_forall d.A₁_comm_sq.1 d.A₁_comm_sq.2

end Data

namespace Data

variable {h : UnitaryFieldData 2 f K} {d : Data G h} [Finite G]

theorem Hyp.two_le (hd : d.Hyp) : 2 ≤ f := hd.setting.two_le

theorem Hyp.four_le (hd : d.Hyp) : 4 ≤ 2 ^ f :=
  (Nat.pow_le_pow_right two_pos hd.two_le).trans_eq' (by norm_num)

theorem Hyp.standard (hd : d.Hyp) : standardComponentIsStandard d.L := hd.setting.std.standard

theorem Hyp.center_hypPSU (hd : d.Hyp) : center (hypPSU h 2 1) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have hz' : d.e.symm z ∈ center d.L := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    apply d.e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (d.e y)
  rw [hd.setting.center_eq_bot, Subgroup.mem_bot] at hz'
  simpa using congrArg d.e hz'

theorem Hyp.inf_centralizer_eq_bot (hd : d.Hyp) : d.L ⊓ centralizer (d.L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  have hx : (⟨x, hxL⟩ : d.L) ∈ center d.L :=
    mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hxC y y.2)
  rw [hd.setting.center_eq_bot, mem_bot] at hx
  exact mem_bot.2 (congrArg Subtype.val hx)

theorem Hyp.centralizer_le_normalizer (hd : d.Hyp) :
    centralizer ({d.t} : Set G) ≤ normalizer (d.L : Set G) :=
  (standard_involution_centralizer_normality hd.standard hd.t_mem hd.t_two).1

theorem Hyp.L_le_centralizer (hd : d.Hyp) : d.L ≤ centralizer ({d.t} : Set G) :=
  (standard_involution_centralizer_normality hd.standard hd.t_mem hd.t_two).2.1

theorem Hyp.t_ne_one (hd : d.Hyp) : d.t ≠ 1 := fun h1 => by
  have := hd.t_two
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem Hyp.t_not_mem_L (hd : d.Hyp) : d.t ∉ d.L := fun htL => by
  have : d.t ∈ d.L ⊓ centralizer (d.L : Set G) := ⟨htL, hd.t_mem⟩
  rw [hd.inf_centralizer_eq_bot, mem_bot] at this
  exact hd.t_ne_one this

theorem Hyp.t_mul_t (hd : d.Hyp) : d.t * d.t = 1 := by
  rw [← sq, ← hd.t_two, pow_orderOf_eq_one]

theorem Hyp.T_le_centralizer (hd : d.Hyp) : d.T ≤ centralizer ({d.t} : Set G) := hd.T_syl.le

theorem Hyp.T_le_normalizer (hd : d.Hyp) : d.T ≤ normalizer (d.L : Set G) :=
  hd.T_le_centralizer.trans hd.centralizer_le_normalizer

theorem Hyp.isPGroup_T (hd : d.Hyp) : IsPGroup 2 d.T := hd.T_syl.isPGroup

theorem Hyp.isPGroup_zpowers_t (hd : d.Hyp) : IsPGroup 2 (zpowers d.t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.t_two, pow_one])

theorem Hyp.card_zpowers_t (hd : d.Hyp) : Nat.card (zpowers d.t) = 2 := by
  rw [Nat.card_zpowers, hd.t_two]

theorem Hyp.t_mem_T (hd : d.Hyp) : d.t ∈ d.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htN : zpowers d.t ≤ normalizer (d.T : Set G) := by
    rw [zpowers_le]
    refine Subgroup.centralizer_le_normalizer (d.T : Set G)
      (mem_centralizer_iff.2 fun x hx => ?_)
    exact mem_centralizer_singleton_iff.1 (hd.T_le_centralizer hx)
  have h2 : IsPGroup 2 (d.T ⊔ zpowers d.t : Subgroup G) :=
    hd.isPGroup_T.to_sup_of_normal_left' hd.isPGroup_zpowers_t htN
  have hle : d.T ⊔ zpowers d.t ≤ centralizer ({d.t} : Set G) := by
    refine sup_le hd.T_le_centralizer ?_
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  have heq := hd.T_syl.eq_of_le le_sup_left hle h2
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

theorem Hyp.isCyclic_sylow (hd : d.Hyp) (Q : Sylow 2 (centralizer (d.L : Set G))) :
    IsCyclic (Q : Subgroup (centralizer (d.L : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hd.setting.std.cyclic
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (centralizer (d.L : Set G)) S Q
  rw [Sylow.coe_subgroup_smul]
  exact isCyclic_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap
    (S : Subgroup (centralizer (d.L : Set G)))) (MonoidHom.subgroupMap_surjective _ _)

theorem Hyp.kernel (hd : d.Hyp) :
    IsCyclic (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) : Subgroup G) ∧
      (∀ x ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G), orderOf x = 2 →
        x = d.t) ∧
      ((centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)).subgroupOf
        (centralizer ({d.t} : Set G))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tc : centralizer (d.L : Set G) := ⟨d.t, hd.t_mem⟩ with htc
  have htc2 : orderOf tc = 2 := by rw [← orderOf_coe]; exact hd.t_two
  have hz : IsPGroup 2 (zpowers tc) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htc2, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  have htQ : tc ∈ Q := hQ (mem_zpowers _)
  have hQc := hd.isCyclic_sylow Q
  obtain ⟨-, huniq, -, -, -, -, hR, hRn, -⟩ :=
    CFSG.ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel
      hd.standard Q hQc htQ htc2 (hd.setting.std.core d.t hd.t_two)
  have hR' : centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) =
      (Q : Subgroup (centralizer (d.L : Set G))).map (centralizer (d.L : Set G)).subtype := hR
  have hRn' : ((centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G)).subgroupOf
      (centralizer ({d.t} : Set G))).Normal := by
    rw [hR']
    exact hRn
  rw [hR'] at hRn' ⊢
  refine ⟨isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _),
    Q.isPGroup'.map _, ?_, hRn'⟩
  rintro _ ⟨y, hy, rfl⟩ hy2
  rw [Subgroup.subtype_apply, orderOf_coe] at hy2
  exact congrArg Subtype.val (huniq y hy hy2)

theorem Hyp.eq_t_of_mem (hd : d.Hyp) {x : G} (hxT : x ∈ d.T)
    (hxL : x ∈ centralizer (d.L : Set G)) (hx2 : orderOf x = 2) : x = d.t :=
  hd.kernel.2.2.1 x ⟨hxL, hd.T_le_centralizer hxT⟩ hx2

theorem isSylowOf_P (d : Data G h) : IsSylowOf 2 d.P d.L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨Q, hQ⟩, -⟩ := unitary_order_and_Sylow h (r := 2) (ε := 1)
    (by norm_num) (by norm_num)
  have hfinU : Finite (hypPSU h 2 1) := finite_hypPSU h
  have hQcard : Nat.card (Q : Subgroup (hypPSU h 2 1)) = (2 ^ f) ^ 10 := by
    rw [hQ, hypProjUnitriangular, ← card_U (h := h)]
    have hinj : Function.Injective ((hypProj h 2 1).comp (hypUnitriangular h 2 1).subtype) :=
      fun a b hab => Subtype.ext (by
        have := (Usub_inf_scalars (hK := h))
        have h1 : (a : hypSU h 2 1)⁻¹ * b ∈ hypUnitriangular h 2 1 ⊓ hypScalars h 2 1 := by
          refine Subgroup.mem_inf.2 ⟨(hypUnitriangular h 2 1).mul_mem
            ((hypUnitriangular h 2 1).inv_mem a.2) b.2, ?_⟩
          rw [← ker_hypProj h 2 1, MonoidHom.mem_ker, map_mul, map_inv]
          change (hypProj h 2 1 a)⁻¹ * hypProj h 2 1 b = 1
          rw [show hypProj h 2 1 a = hypProj h 2 1 b from hab, inv_mul_cancel]
        rw [this, mem_bot] at h1
        exact inv_mul_eq_one.1 h1)
    have e : hypUnitriangular h 2 1 ≃* (hypUnitriangular h 2 1).map (hypProj h 2 1) :=
      (MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, range_subtype]))
    exact (Nat.card_congr e.toEquiv).symm
  have hL : Nat.card d.L = Nat.card (hypPSU h 2 1) := Nat.card_congr d.e.toEquiv
  refine CFSG.ABGLocalTools.isSylowOf_of_card d.P_le_L ?_
  rw [d.card_P, hL, ← hQcard, Sylow.card_eq_multiplicity]

theorem Hyp.t_not_mem_A₁ (hd : d.Hyp) : d.t ∉ d.A₁ := fun h1 =>
  hd.t_not_mem_L (d.A₁_le_P.trans d.P_le_L h1)

theorem Hyp.A₁_le_T (hd : d.Hyp) : d.A₁ ≤ d.T := d.A₁_le_P.trans hd.P_le

theorem Hyp.A₁_le_centralizer_zpowers (hd : d.Hyp) :
    d.A₁ ≤ centralizer (zpowers d.t : Set G) := by
  intro a ha
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hat : d.t * a = a * d.t :=
    (mem_centralizer_iff.1 hd.t_mem a (d.A₁_le_P.trans d.P_le_L ha)).symm
  exact (Commute.zpow_left hat k).eq

theorem Hyp.isElementaryAbelian_B₁ (hd : d.Hyp) : CFSG.IsElementaryAbelian 2 d.B₁ := by
  have : CFSG.IsElementaryAbelian 2 (zpowers d.t) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [← hd.t_two, pow_orderOf_eq_one])
  have := d.isElementaryAbelian_A₁
  exact CFSG.IsElementaryAbelian.sup_of_le_centralizer hd.A₁_le_centralizer_zpowers

theorem Hyp.card_B₁ (hd : d.Hyp) : Nat.card d.B₁ = 2 * (2 ^ f) ^ 4 := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (zpowers d.t) d.A₁
    fun x hx y hy => (mem_centralizer_iff.1 (hd.A₁_le_centralizer_zpowers hy) x hx)
  have hinf : zpowers d.t ⊓ d.A₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxt, hxA⟩
    rw [mem_bot]
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    have hk : d.t ^ k = d.t ^ (k % 2) := by
      rw [← zpow_mod_orderOf, hd.t_two]
      norm_cast
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [hk, h0, zpow_zero]
    · rw [hk, h1, zpow_one] at hxA
      exact absurd hxA hd.t_not_mem_A₁
  rw [hinf, Subgroup.card_bot, mul_one, hd.card_zpowers_t, d.card_A₁] at hc
  exact hc

theorem Hyp.B₁_le_T (hd : d.Hyp) : d.B₁ ≤ d.T :=
  sup_le ((zpowers_le).2 hd.t_mem_T) hd.A₁_le_T

theorem Hyp.inf_Pi_actImage_T (hd : d.Hyp) : d.actImage d.T ⊓ Pi h = Uh h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_hyp h
  have hUT : Uh h ≤ d.actImage d.T := by
    rw [← d.actImage_P]
    exact Subgroup.map_mono fun x hx => hd.P_le hx
  have h2 : IsPGroup 2 (d.actImage d.T) :=
    (hd.isPGroup_T.comap_subtype (K := normalizer (d.L : Set G))).map _
  exact (isSylow_Uh hd.center_hypPSU).eq_of_le (le_inf hUT Uh_le_Pi) inf_le_right
    (h2.to_inf_left)

end Data

theorem Data.exists_hyp [Finite G] {L : Subgroup G} (hs : U5Setting G L f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 f K) (d : Data G h), d.L = L ∧ d.Hyp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, h, ⟨e⟩⟩ := exists_hypPSU_equiv (by have := hs.two_le; omega) hs.model
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2
    (even_iff_two_dvd.1 hs.std.standard.2.1)
  rw [← orderOf_coe] at ht
  set d₀ : Data G h := ⟨L, e, t, ⊥⟩ with hd₀
  have hLC : L ≤ centralizer ({(t : G)} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 t.2 l hl)
  have hPC : d₀.P ≤ centralizer ({(t : G)} : Set G) := d₀.P_le_L.trans hLC
  obtain ⟨Q, hQ⟩ := (d₀.isPGroup_P.comap_subtype
    (K := centralizer ({(t : G)} : Set G))).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup (centralizer ({(t : G)} : Set G))).map
    (centralizer ({(t : G)} : Set G)).subtype with hT
  have hPT : d₀.P ≤ T := fun x hx => ⟨⟨x, hPC hx⟩, hQ hx, rfl⟩
  exact ⟨K, _, h, ⟨L, e, t, T⟩, rfl,
    { setting := hs
      t_mem := t.2
      t_two := ht
      T_syl := ⟨Q, rfl⟩
      P_le := hPT }⟩

end CFSG.LocalAnalysis.EvenBN.U5
