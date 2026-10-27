module

public import CFSG.LocalAnalysis.EvenBN.G2.NotCentral
public import CFSG.LocalAnalysis.EvenBN.Common.CosetFactorization

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.EvenSmallLie.UnitarySix.YamadaD (oTwo le_oTwo oTwo_le isPGroup_oTwo le_normalizer_oTwo)
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

@[expose] noncomputable def yamadaC₁
    {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K) (t : G) :
    Subgroup G :=
  pCoreOf 2 (normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G))

@[expose] noncomputable def yamadaR₁
    {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K) (t : G) :
    Subgroup G :=
  yamadaC₁ d t ⊔ d.S

theorem yamadaC₁_le {G : Type*}
    [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K) (t : G) :
    yamadaC₁ d t ≤ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

theorem le_normalizer_yamadaC₁
    {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K) (t : G) :
    normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (yamadaC₁ d t : Set G) :=
  LieType.BorelTits.le_normalizer_pCoreOf 2 _

section Generic

variable {G : Type*} [Group G]

theorem pCoreOf_two_eq_oTwo [Finite G] (H : Subgroup G) : pCoreOf 2 H = oTwo H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_antisymm (le_oTwo (LieType.BorelTits.pCoreOf_le 2 H)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 H) (LieType.BorelTits.pCoreOf_isPGroup 2 H))
    (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (oTwo_le H) (le_normalizer_oTwo H)
      (isPGroup_oTwo H))

theorem mem_normalizer_zpowers {g t : G} (hg : g * t = t * g) :
    g ∈ normalizer (zpowers t : Set G) := by
  have key : ∀ k : G, k * t = t * k → ∀ x ∈ zpowers t, k * x * k⁻¹ = x := by
    intro k hk x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
    rw [(Commute.zpow_right (hk : Commute k t) n).eq, mul_inv_cancel_right]
  have hg' : g⁻¹ * t = t * g⁻¹ := by
    calc g⁻¹ * t = g⁻¹ * (t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * t) * g⁻¹ := by rw [hg]
      _ = t * g⁻¹ := by group
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [key g hg x hx]
    exact hx
  · intro hx
    have := key g⁻¹ hg' _ hx
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
    rw [this]
    exact hx

theorem commute_of_mem_zpowers {c t x : G} (hc : c ∈ zpowers t)
    (hx : x ∈ centralizer ({t} : Set G)) : x * c = c * x := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
  exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 hx : Commute x t) n).eq

theorem normalizer_le_normalizer_commutator (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg x hx => ?_
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hg y).1 hy
  have h1 : ⁅H, H⁆.map (MulAut.conj g).toMonoidHom ≤ ⁅H, H⁆ := by
    rw [map_commutator]
    exact commutator_mono hle hle
  exact h1 ⟨x, hx, rfl⟩

end Generic

namespace Model

section Scalars

variable {K : Type} [Field K]
  [CharP K 2]

theorem exists_J₃_scalar [Finite K] (a : Kˣ) :
    ∃ j : ModGL .G2 K, j ∈ Model.J₃ K ∧
      ∀ x : K, j * pinnedX .G2 K g2c x * j⁻¹ = pinnedX .G2 K g2c (a * x) := by
  obtain ⟨s, hs⟩ := exists_units_sq_eq a
  refine ⟨torusElt .G2 K g2ia a * torusElt .G2 K g2ir s,
    Model.mem_torusFix_of (m₁ := -1) (m₂ := 2) isRoot_g2r a s (by decide) (by decide) (by
      rw [zpow_neg_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hs,
        inv_mul_cancel]), fun x => ?_⟩
  rw [Model.torus_conj_of (m₁ := 1) (m₂ := 0) isRoot_g2c a s (by decide) (by decide) x,
    zpow_one, zpow_zero, mul_one]


theorem exists_scalar_of_mem_D_sup_J₃ {g : ModGL .G2 K} (hg : g ∈ Model.D K ⊔ Model.J₃ K) :
    ∃ a : Kˣ, ∀ x : K, g * pinnedX .G2 K g2c x * g⁻¹ = pinnedX .G2 K g2c (a * x) := by
  have hJD : Model.J₃ K ≤ normalizer (Model.D K : Set (ModGL .G2 K)) := fun j hj =>
    Model.borelGroup_le_normalizer_D (mem_sup_left hj.1)
  obtain ⟨d', hd', j, hj, rfl⟩ := Common.exists_mul_of_le_normalizer hJD g hg
  obtain ⟨a, ha⟩ := exists_torus_scale hj.1 isRoot_g2c
  refine ⟨a, fun x => ?_⟩
  have hc : d' * pinnedX .G2 K g2c (a * x) = pinnedX .G2 K g2c (a * x) * d' :=
    Model.commute_of_mem_U (mem_rootSubgroup.2 ⟨_, rfl⟩) (Model.D_le_S hd')
  calc d' * j * pinnedX .G2 K g2c x * (d' * j)⁻¹ =
      d' * (j * pinnedX .G2 K g2c x * j⁻¹) * d'⁻¹ := by group
    _ = pinnedX .G2 K g2c (a * x) := by rw [ha, hc, mul_inv_cancel_right]

end Scalars

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Light


theorem exists_mulEquiv_U :
    ∃ ι : Multiplicative K ≃* d.U, ∀ x : K, (ι (Multiplicative.ofAdd x) : G) =
      d.emb ⟨pinnedX .G2 K g2c x, pinnedX_mem_adjointGroup g2c x⟩ := by
  let φ : Multiplicative K →* d.U :=
    { toFun := fun x => ⟨d.emb ⟨pinnedX .G2 K g2c (Multiplicative.toAdd x),
          pinnedX_mem_adjointGroup g2c _⟩, d.emb_mem_image (mem_rootSubgroup.2 ⟨_, rfl⟩)⟩
      map_one' := Subtype.ext (by
        simp only [toAdd_one, OneMemClass.coe_one]
        rw [← map_one d.emb]
        exact congrArg d.emb (Subtype.ext (pinnedX_zero .G2 K g2c)))
      map_mul' := fun x y => Subtype.ext (by
        simp only [toAdd_mul, MulMemClass.coe_mul]
        rw [← map_mul]
        exact congrArg d.emb (Subtype.ext (pinnedX_add .G2 K g2c _ _))) }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h0 : d.emb ⟨pinnedX .G2 K g2c (Multiplicative.toAdd x), pinnedX_mem_adjointGroup g2c _⟩ =
        d.emb ⟨pinnedX .G2 K g2c (Multiplicative.toAdd y), pinnedX_mem_adjointGroup g2c _⟩ :=
      congrArg (fun z : d.U => (z : G)) hxy
    have h1 := d.emb_injective h0
    have h2 := pinnedX_injective .G2 K g2c (congrArg Subtype.val h1)
    exact Multiplicative.toAdd.injective h2
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, hu⟩
    obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hu
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hg
    exact ⟨Multiplicative.ofAdd c, Subtype.ext (congrArg d.emb (Subtype.ext hc))⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun x => rfl⟩

theorem exists_mem_J₃_scalar [Finite K] [CharP K 2] (ι : Multiplicative K ≃* d.U)
    (hι : ∀ x : K, (ι (Multiplicative.ofAdd x) : G) =
      d.emb ⟨pinnedX .G2 K g2c x, pinnedX_mem_adjointGroup g2c x⟩) {a : K} (ha : a ≠ 0) :
    ∃ e ∈ d.J₃, ∀ x : K,
      e * (ι (Multiplicative.ofAdd x) : G) * e⁻¹ = ι (Multiplicative.ofAdd (a * x)) := by
  obtain ⟨j, hj, hjx⟩ := Model.exists_J₃_scalar (Units.mk0 a ha)
  have hjA := Model.torusFix_le_adjointGroup K g2r hj
  refine ⟨d.emb ⟨j, hjA⟩, d.emb_mem_image hj, fun x => ?_⟩
  rw [hι, hι, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Subtype.ext ?_
  simp only [coe_mul, coe_inv]
  rw [hjx x, Units.val_mk0]

end Light

section Facts

variable
  [Finite K] [CharP K 2]

theorem inf_centralizer_U : L ⊓ centralizer (d.U : Set G) = d.D ⊔ d.leviA := by
  have h1 := d.image_inf_centralizer (adjointGroup .G2 K) (Model.U_le_adjointGroup K)
  rw [d.image_adjointGroup] at h1
  rw [G2Data.U, ← h1, G2Data.D, G2Data.leviA,
    ← d.image_sup Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K)]
  congr 1
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le Model.D_le_adjointGroup
    (Model.leviA_le_adjointGroup K)) Model.D_sup_leviA_le_centralizer_U)
  have hC := (even_G2_highest_long_root_centralizer K).2.2.2.1
  have hx' : x ∈ adjointGroup .G2 K ⊓ centralizer {pinnedX .G2 K g2c 1} :=
    ⟨hx.1, mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact mem_centralizer_iff.1 hx.2 _ (mem_rootSubgroup.2 ⟨1, rfl⟩)⟩
  rw [hC] at hx'
  exact hx'

omit [CharP K 2] in
theorem act_mem_normalizer_inn_iff [Finite G] {H₀ : Subgroup (ModGL .G2 K)} {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    d.act ⟨x, hx⟩ ∈ normalizer (Model.inn H₀ : Set (MulAut (adjointGroup .G2 K))) ↔
      x ∈ normalizer (d.image H₀ : Set G) := by
  rw [Model.mem_normalizer_inn_iff]
  constructor
  · intro h
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hy
    have h1 := d.emb_act_apply ⟨x, hx⟩ g
    change d.emb (d.act ⟨x, hx⟩ g) = x * d.emb g * x⁻¹ at h1
    rw [← h1]
    exact d.emb_mem_image ((h g).2 hg)
  · intro h g
    rw [← d.emb_mem_image_iff, ← d.emb_mem_image_iff (g := g)]
    have h1 := d.emb_act_apply ⟨x, hx⟩ g
    change d.emb (d.act ⟨x, hx⟩ g) = x * d.emb g * x⁻¹ at h1
    rw [h1]
    exact (mem_normalizer_iff.1 h (d.emb g)).symm

end Facts

end G2Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2]
  in
theorem centralizer_inf_normalizer_U_le (_h : Setup G L f t) (d : G2Data L K) :
    centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) ≤
      normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_sup hx.2 (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hx.1))

omit [Finite K] in
theorem mem_D_of_mem_sup (h : Setup G L f t) (d : G2Data L K) {x : G}
    (hx : x ∈ d.D ⊔ zpowers t) (hxL : x ∈ L) : x ∈ d.D := by
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 hx with hD | hD
  · exact hD
  · exfalso
    refine h.t_not_mem_L ?_
    have := mul_mem (d.image_le _ hD) (inv_mem hxL)
    rwa [mul_inv_cancel_right] at this

theorem exists_mul_of_mem_centralizer_U (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) {k : G}
    (hk : k ∈ centralizer ({t} : Set G) ⊓ centralizer (d.U : Set G)) :
    ∃ l ∈ d.D ⊔ d.leviA, ∃ c ∈ zpowers t, k = l * c := by
  obtain ⟨hkC, hkU⟩ := mem_inf.1 hk
  have h1 : k ∈ (L ⊓ centralizer (d.U : Set G)) ⊔ centralizer (L : Set G) :=
    d.yamada_3_19_1_G hK h.two_le isRoot_g2c ⟨h.centralizer_le_normalizer hkC, hkU⟩
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (L ⊓ centralizer (d.U : Set G)) (centralizer (L : Set G))
    fun x hx y hy => mem_centralizer_iff.1 hy x hx.1).2
  have h1' : k ∈ (((L ⊓ centralizer (d.U : Set G)) ⊔ centralizer (L : Set G) : Subgroup G) :
    Set G) := h1
  rw [hset] at h1'
  obtain ⟨l, hl, c, hc, rfl⟩ := h1'
  have hlC : l ∈ centralizer ({t} : Set G) := h.L_le_centralizer hl.1
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem hlC) hkC
    rwa [inv_mul_cancel_left] at this
  have hct : c ∈ zpowers t := by
    rw [← h.centralizer_L_inf]
    exact ⟨hc, hcC⟩
  have hlD : l ∈ d.D ⊔ d.leviA := by
    rw [← d.inf_centralizer_U]
    exact hl
  exact ⟨l, hlD, c, hct, rfl⟩

theorem D_sup_leviA_le_kernel (h : Setup G L f t) (d : G2Data L K) :
    d.D ⊔ d.leviA ≤ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) ⊓ centralizer ({t} : Set G) := by
  intro x hx
  have hxL : x ∈ L := (sup_le (d.image_le _) (d.image_le _)) hx
  have hxU := d.D_sup_leviA_le_centralizer_U hx
  have hxt : x ∈ centralizer ({t} : Set G) := h.L_le_centralizer hxL
  exact ⟨⟨h.centralizer_inf_normalizer_U_le d ⟨hxt, Subgroup.centralizer_le_normalizer _ hxU⟩,
    hxU⟩, hxt⟩

theorem tD_le_kernel (h : Setup G L f t) (d : G2Data L K) :
    d.D ⊔ zpowers t ≤ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) ⊓ centralizer ({t} : Set G) := by
  refine sup_le (le_sup_left.trans (h.D_sup_leviA_le_kernel d)) ((zpowers_le).2 ?_)
  have htU : t ∈ centralizer (d.U : Set G) := mem_centralizer_iff.2 fun u hu =>
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hu))
  exact ⟨⟨h.centralizer_inf_normalizer_U_le d ⟨h.t_mem_centralizer,
    Subgroup.centralizer_le_normalizer _ htU⟩, htU⟩, h.t_mem_centralizer⟩

theorem isPGroup_tD (h : Setup G L f t) (d : G2Data L K) :
    IsPGroup 2 (d.D ⊔ zpowers t : Subgroup G) := by
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  exact (h.isSylowOf_yamadaR d).isPGroup.to_le
    (sup_le (hDS.trans le_sup_left) ((zpowers_le).2 (mem_sup_right h.t_mem_kernel)))

omit
  [Finite K] [CharP K 2] in
theorem inner_le_range_act (h : Setup G L f t) (d : G2Data L K) :
    inner (adjointGroup .G2 K) ≤ (h.act d).range := by
  rintro _ ⟨g, rfl⟩
  exact ⟨⟨d.emb g, h.L_le_centralizer (d.emb_mem g)⟩, h.act_emb d g⟩

theorem pCoreOf_range_act (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    pCoreOf 2 ((h.act d).range ⊓
        normalizer (Model.inn (Model.U K) : Set (MulAut (adjointGroup .G2 K)))) =
      Model.inn (Model.D K) ∧
    pCoreOf 2 ((h.act d).range ⊓
        normalizer (Model.inn (Model.Y K) : Set (MulAut (adjointGroup .G2 K)))) =
      Model.inn (Model.M K) :=
  ⟨(Model.yamada_3_23_1 hK h.two_le (h.inner_le_range_act d)).2.1,
    (Model.yamada_3_23_1 hK h.two_le (h.inner_le_range_act d)).2.2⟩

omit [Finite K] [CharP K 2] in
theorem centralizer_inf_normalizer_le_of_pCoreOf [Finite K] (h : Setup G L f t)
    (d : G2Data L K) {H₀ R₀ : Subgroup (ModGL .G2 K)}
    (hcore : pCoreOf 2 ((h.act d).range ⊓
      normalizer (Model.inn H₀ : Set (MulAut (adjointGroup .G2 K)))) = Model.inn R₀) :
    centralizer ({t} : Set G) ⊓ normalizer (d.image H₀ : Set G) ≤
      normalizer (d.image R₀ : Set G) := by
  rintro x ⟨hxC, hxH⟩
  have hxN := h.centralizer_le_normalizer hxC
  have h1 : h.act d ⟨x, hxC⟩ ∈ (h.act d).range ⊓
      normalizer (Model.inn H₀ : Set (MulAut (adjointGroup .G2 K))) :=
    ⟨⟨_, rfl⟩, (d.act_mem_normalizer_inn_iff hxN).2 hxH⟩
  have h2 := LieType.BorelTits.le_normalizer_pCoreOf 2 _ h1
  rw [hcore] at h2
  exact (d.act_mem_normalizer_inn_iff hxN).1 h2

omit [CharP K 2] in
theorem le_sup_of_pCoreOf (h : Setup G L f t) (d : G2Data L K)
    {H₀ R₀ : Subgroup (ModGL .G2 K)}
    (hcore : pCoreOf 2 ((h.act d).range ⊓
      normalizer (Model.inn H₀ : Set (MulAut (adjointGroup .G2 K)))) = Model.inn R₀)
    {P : Subgroup G} (hPC : P ≤ centralizer ({t} : Set G) ⊓ normalizer (d.image H₀ : Set G))
    (hN : centralizer ({t} : Set G) ⊓ normalizer (d.image H₀ : Set G) ≤ normalizer (P : Set G))
    (hP : IsPGroup 2 P) : P ≤ d.image R₀ ⊔ zpowers t := by
  set C := centralizer ({t} : Set G) with hCdef
  set P' := (P.subgroupOf C).map (h.act d) with hP'
  have hP'B : P' ≤ (h.act d).range ⊓
      normalizer (Model.inn H₀ : Set (MulAut (adjointGroup .G2 K))) := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨⟨r, rfl⟩, (d.act_mem_normalizer_inn_iff _).2 (hPC (mem_subgroupOf.1 hr)).2⟩
  have hBP' : (h.act d).range ⊓
      normalizer (Model.inn H₀ : Set (MulAut (adjointGroup .G2 K))) ≤
        normalizer (P' : Set (MulAut (adjointGroup .G2 K))) := by
    refine le_normalizer_of_conj_mem fun α hα β hβ => ?_
    obtain ⟨⟨x, rfl⟩, hα2⟩ := hα
    obtain ⟨r, hr, rfl⟩ := hβ
    have hxH : (x : G) ∈ normalizer (d.image H₀ : Set G) :=
      (d.act_mem_normalizer_inn_iff _).1 hα2
    have hxP := hN ⟨x.2, hxH⟩
    refine ⟨x * r * x⁻¹, mem_subgroupOf.2 ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (mem_normalizer_iff.1 hxP r).1 (mem_subgroupOf.1 hr)
  have hP'2 : IsPGroup 2 P' := hP.comap_subtype.map _
  have hle := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP'B hBP' hP'2
  rw [hcore] at hle
  intro r hr
  have hrC := (hPC hr).1
  have h1 : h.act d ⟨r, hrC⟩ ∈ Model.inn R₀ := hle ⟨⟨r, hrC⟩, hr, rfl⟩
  have h2 : r ∈ d.image R₀ ⊔ centralizer (L : Set G) :=
    (d.act_mem_inn_iff (h.centralizer_le_normalizer hrC)).1 h1
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (d.image R₀)
    (centralizer (L : Set G)) fun x hx y hy => mem_centralizer_iff.1 hy x (d.image_le _ hx)).2
  have h2' : r ∈ ((d.image R₀ ⊔ centralizer (L : Set G) : Subgroup G) : Set G) := h2
  rw [hset] at h2'
  obtain ⟨a, ha, c, hc, rfl⟩ := h2'
  have haC := h.L_le_centralizer (d.image_le _ ha)
  have hcC : c ∈ C := by
    have := mul_mem (inv_mem haC) hrC
    rwa [inv_mul_cancel_left] at this
  have hct : c ∈ zpowers t := by
    rw [← h.centralizer_L_inf]
    exact ⟨hc, hcC⟩
  exact mul_mem (mem_sup_left ha) (mem_sup_right hct)

theorem centralizer_inf_normalizer_U_le_normalizer_D (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) ≤ normalizer (d.D : Set G) :=
  h.centralizer_inf_normalizer_le_of_pCoreOf d (h.pCoreOf_range_act d hK).1

theorem le_tD_of_isPGroup (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {R : Subgroup G} (hRC : R ≤ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G))
    (hN : centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) ≤ normalizer (R : Set G))
    (hR : IsPGroup 2 R) : R ≤ d.D ⊔ zpowers t :=
  h.le_sup_of_pCoreOf d (h.pCoreOf_range_act d hK).1 hRC hN hR

theorem exists_conj_eq_mul_tU (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    {y : G} (hy : y ∈ d.U) :
    ∃ g ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G), g⁻¹ * t * g = t * y := by
  have hmem : t * y ∈ (fun u => t * u) '' (d.U : Set G) := ⟨y, hy, rfl⟩
  rw [← (h.conj_t_eq_tU d hK).2] at hmem
  obtain ⟨n, hn, hnt⟩ := hmem
  exact ⟨n⁻¹, inv_mem hn, by rw [inv_inv]; exact hnt⟩

theorem normalizer_tU_le_normalizer_U (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (d.U : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg u hu => ?_
  have h1 : g * u * g⁻¹ ∈ d.U ⊔ zpowers t := (mem_normalizer_iff.1 hg u).1 (mem_sup_left hu)
  rcases (h.mem_sup_zpowers_iff (d.image_le _)).1 h1 with h2 | h2
  · exact h2
  · exfalso
    have hmem : g * u * g⁻¹ ∈ (fun u => t * u) '' (d.U : Set G) :=
      ⟨_, h2, by beta_reduce; rw [← mul_assoc, h.t_mul_t, one_mul]⟩
    rw [← (h.conj_t_eq_tU d hK).2] at hmem
    obtain ⟨n, -, hnt⟩ := hmem
    refine h.conj_not_mem_Y d hK (g⁻¹ * n) ?_
    rw [show g⁻¹ * n * t * (g⁻¹ * n)⁻¹ = g⁻¹ * (n * t * n⁻¹) * g by group, hnt,
      show g⁻¹ * (g * u * g⁻¹) * g = u by group]
    exact (d.inclusions).1 hu

theorem cosetData_tU (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    CosetData (normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G)) d.U t :=
  CosetData.of_le_normalizer h.t_mul_t ((d.image_le _).trans h.L_le_centralizer)
    d.isElementaryAbelian.1 (h.normalizer_tU_le_normalizer_U d hK) le_rfl

theorem normalizer_tU_inf_centralizer (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) =
      centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) :=
  le_antisymm (fun _ hx => ⟨hx.2, h.normalizer_tU_le_normalizer_U d hK hx.1⟩)
    fun _ hx => ⟨h.centralizer_inf_normalizer_U_le d hx, hx.1⟩

omit [Finite K] [CharP K 2]
  in
theorem kernel_le (_h : Setup G L f t) (d : G2Data L K) :
    normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer (d.U : Set G) ⊓
        centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) := fun _ hk =>
  ⟨hk.2, Subgroup.centralizer_le_normalizer _ hk.1.2⟩

theorem normalizer_tU_le_normalizer_kernel (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer (d.U : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun _ hg _ hk => (h.cosetData_tU d hK).conj_mem_kernel hg hk

theorem oTwo_kernel (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    oTwo (normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer (d.U : Set G) ⊓
      centralizer ({t} : Set G)) = d.D ⊔ zpowers t := by
  have hHo : normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((oTwo (normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer (d.U : Set G) ⊓ centralizer ({t} : Set G)) : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem fun _ hg _ hy =>
      Common.conj_mem_oTwo_of_mem_normalizer (h.normalizer_tU_le_normalizer_kernel d hK hg) hy
  apply le_antisymm
  · exact h.le_tD_of_isPGroup d hK ((oTwo_le _).trans (h.kernel_le d))
      ((h.centralizer_inf_normalizer_U_le d).trans hHo) (isPGroup_oTwo _)
  · refine le_oTwo (h.tD_le_kernel d) (fun k hk => ?_) (h.isPGroup_tD d)
    have hk' := h.kernel_le d hk
    exact mem_normalizer_sup (h.centralizer_inf_normalizer_U_le_normalizer_D d hK hk')
      (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hk'.1))

theorem normalizer_tU_le_normalizer_tD (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.D ⊔ zpowers t : Subgroup G) : Set G) := by
  rw [← h.oTwo_kernel d hK]
  exact le_normalizer_of_conj_mem fun _ hg _ hy =>
    Common.conj_mem_oTwo_of_mem_normalizer (h.normalizer_tU_le_normalizer_kernel d hK hg) hy

theorem D_sup_leviA_le_normalizer_D (_h : Setup G L f t) (d : G2Data L K) :
    d.D ⊔ d.leviA ≤ normalizer (d.D : Set G) := by
  have h1 := (d.yamada_3_13_2_G).2.1
  exact (sup_le_sup_left le_sup_left _).trans (h1.symm.le.trans inf_le_right)

theorem exists_scalar_of_kernel (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (ι : Multiplicative K ≃* d.U) (hι : ∀ x : K, (ι (Multiplicative.ofAdd x) : G) =
      d.emb ⟨pinnedX .G2 K g2c x, pinnedX_mem_adjointGroup g2c x⟩) {e : G}
    (he : e ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G))
    (hek : ∀ k ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) ⊓ centralizer ({t} : Set G),
        e * k * e⁻¹ * k⁻¹ ∈ d.D ⊔ zpowers t) :
    ∃ a : K, a ≠ 0 ∧ ∀ x : K,
      e * (ι (Multiplicative.ofAdd x) : G) * e⁻¹ = ι (Multiplicative.ofAdd (a * x)) := by
  have heN := h.centralizer_le_normalizer he.2
  have himg : d.image (Model.D K ⊔ Model.leviA K) = d.D ⊔ d.leviA :=
    d.image_sup Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K)
  have h1 : d.act ⟨e, heN⟩ ∈ TwoF4.sectionCentralizer (Model.inn (Model.D K ⊔ Model.leviA K))
      (Model.inn (Model.D K)) := by
    rw [d.act_mem_sectionCentralizer_iff le_sup_left heN]
    intro y hy
    rw [himg] at hy
    have hyL : y ∈ L := sup_le (d.image_le _) (d.image_le _) hy
    have h2 := hek y (h.D_sup_leviA_le_kernel d hy)
    have h2L : e * y * e⁻¹ * y⁻¹ ∈ L := mul_mem ((mem_normalizer_iff.1 heN y).1 hyL) (inv_mem hyL)
    have h3 := (mem_normalizer_iff.1 (inv_mem (h.D_sup_leviA_le_normalizer_D d hy)) _).1
      (h.mem_D_of_mem_sup d h2 h2L)
    rwa [show y⁻¹ * (e * y * e⁻¹ * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * (e * y * e⁻¹) by group] at h3
  rw [(Model.yamada_3_23_3 hK h.two_le).2.1] at h1
  obtain ⟨g, hg, hge⟩ := Model.mem_inn.1 h1
  obtain ⟨a, ha⟩ := Model.exists_scalar_of_mem_D_sup_J₃ hg
  refine ⟨a, a.ne_zero, fun x => ?_⟩
  rw [hι x, hι (a * x)]
  have h4 := d.emb_act_apply ⟨e, heN⟩ ⟨pinnedX .G2 K g2c x, pinnedX_mem_adjointGroup g2c x⟩
  change d.emb (d.act ⟨e, heN⟩ _) = e * _ * e⁻¹ at h4
  rw [← h4, ← hge]
  congr 1
  exact Subtype.ext (ha x)

theorem exists_kernel_of_scalar (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (ι : Multiplicative K ≃* d.U) (hι : ∀ x : K, (ι (Multiplicative.ofAdd x) : G) =
      d.emb ⟨pinnedX .G2 K g2c x, pinnedX_mem_adjointGroup g2c x⟩) {a : K} (ha : a ≠ 0) :
    ∃ e ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G),
      (∀ k ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer (d.U : Set G) ⊓ centralizer ({t} : Set G),
          e * k * e⁻¹ * k⁻¹ ∈ d.D ⊔ zpowers t) ∧
        ∀ x : K, e * (ι (Multiplicative.ofAdd x) : G) * e⁻¹ = ι (Multiplicative.ofAdd (a * x)) := by
  obtain ⟨e, hj, hescal⟩ := d.exists_mem_J₃_scalar ι hι ha
  have himg : d.image (Model.D K ⊔ Model.leviA K) = d.D ⊔ d.leviA :=
    d.image_sup Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K)
  have heC : e ∈ centralizer ({t} : Set G) := h.L_le_centralizer (d.image_le _ hj)
  have heU : e ∈ normalizer (d.U : Set G) := mem_normalizer_of_conj_mem fun u hu => by
    obtain ⟨y, hy⟩ := ι.surjective ⟨u, hu⟩
    have hu' : u = ι y := congrArg Subtype.val hy.symm
    rw [hu', show y = Multiplicative.ofAdd (Multiplicative.toAdd y) from rfl, hescal]
    exact (ι _).2
  refine ⟨e, ⟨h.centralizer_inf_normalizer_U_le d ⟨heC, heU⟩, heC⟩, fun k hk => ?_, hescal⟩
  obtain ⟨l, hl, c, hc, rfl⟩ := h.exists_mul_of_mem_centralizer_U d hK ⟨hk.2, hk.1.2⟩
  have heN := h.centralizer_le_normalizer heC
  have he' : e ∈ d.image (Model.D K ⊔ Model.J₃ K) ⊔ centralizer (L : Set G) :=
    mem_sup_left (d.image_mono le_sup_right hj)
  have h1 := (d.act_sectionCentralizer_eq le_sup_left (Model.yamada_3_23_3 hK h.two_le).2.1
    heN).2 he' l (by rw [himg]; exact hl)
  have hce : c * e⁻¹ = e⁻¹ * c :=
    ((Commute.inv_left (commute_of_mem_zpowers hc heC : Commute e c)).eq).symm
  have e1 : e * (l * c) * e⁻¹ * (l * c)⁻¹ = l * (l⁻¹ * (e * l * e⁻¹)) * l⁻¹ := by
    calc e * (l * c) * e⁻¹ * (l * c)⁻¹ = e * l * (c * e⁻¹) * c⁻¹ * l⁻¹ := by group
      _ = e * l * (e⁻¹ * c) * c⁻¹ * l⁻¹ := by rw [hce]
      _ = l * (l⁻¹ * (e * l * e⁻¹)) * l⁻¹ := by group
  rw [e1]
  exact mem_sup_left ((mem_normalizer_iff.1 (h.D_sup_leviA_le_normalizer_D d hl) _).1 h1)

theorem two_core_C₁ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaC₁ d t ≤ centralizer (d.U : Set G) ∧
      yamadaC₁ d t ⊓ centralizer ({t} : Set G) = d.D ⊔ zpowers t ∧
      (∀ y ∈ d.U, ∃ x ∈ yamadaC₁ d t, x⁻¹ * t * x = t * y) ∧
      ∀ g ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G),
        ∃ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G), ∃ x ∈ yamadaC₁ d t,
          g = c * x := by
  obtain ⟨ι, hι⟩ := d.exists_mulEquiv_U
  have hc := h.cosetData_tU d hK
  have hK2 : 2 < Nat.card K := by
    have := h.four_le
    omega
  have hmax : ∀ R : Subgroup G, R ≤ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer ({t} : Set G) → normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) ≤ normalizer (R : Set G) → IsPGroup 2 R →
          R ≤ d.D ⊔ zpowers t := by
    intro R hR hN hp
    rw [h.normalizer_tU_inf_centralizer d hK] at hR hN
    exact h.le_tD_of_isPGroup d hK hR hN hp
  obtain ⟨h1, h2, h3, h4⟩ := hc.frobenius_two_core hK2 ι
    (fun y hy => h.exists_conj_eq_mul_tU d hK hy) (h.isPGroup_tD d) (h.tD_le_kernel d)
    (h.normalizer_tU_le_normalizer_tD d hK) hmax
    (fun e he hek => h.exists_scalar_of_kernel d hK ι hι he hek)
    (fun a ha => h.exists_kernel_of_scalar d hK ι hι ha)
  rw [yamadaC₁, pCoreOf_two_eq_oTwo]
  refine ⟨h1, h2, h3, fun g hg => ?_⟩
  obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
  rw [h.normalizer_tU_inf_centralizer d hK] at hc
  exact ⟨c, hc, x, hx, rfl⟩

theorem center_sup_zpowers (h : Setup G L f t) {E : Subgroup G} (hEL : E ≤ L) :
    (E ⊔ zpowers t) ⊓ centralizer ((E ⊔ zpowers t : Subgroup G) : Set G) =
      (E ⊓ centralizer (E : Set G)) ⊔ zpowers t := by
  apply le_antisymm
  · rintro z ⟨hzB, hzc⟩
    have hzE : ∀ x ∈ E, x * z = z * x := fun x hx => mem_centralizer_iff.1 hzc x (mem_sup_left hx)
    rcases (h.mem_sup_zpowers_iff hEL).1 hzB with hz | hz
    · exact mem_sup_left ⟨hz, mem_centralizer_iff.2 hzE⟩
    · have h1 : t * z ∈ E ⊓ centralizer (E : Set G) := ⟨hz, mem_centralizer_iff.2 fun x hx => by
        have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hEL hx))
        calc x * (t * z) = t * (x * z) := by rw [← mul_assoc, hxt, mul_assoc]
          _ = t * (z * x) := by rw [hzE x hx]
          _ = t * z * x := by group⟩
      rw [show z = t * (t * z) by rw [← mul_assoc, h.t_mul_t, one_mul]]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)
  · have hZE : E ≤ centralizer ((E ⊓ centralizer (E : Set G) : Subgroup G) : Set G) := by
      rw [← Subgroup.le_centralizer_iff]
      exact inf_le_right
    have htZ : t ∈ centralizer ((E ⊓ centralizer (E : Set G) : Subgroup G) : Set G) :=
      mem_centralizer_iff.2 fun z hz =>
        mem_centralizer_singleton_iff.1 (h.L_le_centralizer (hEL hz.1))
    have hBt : E ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
      sup_le (hEL.trans h.L_le_centralizer) ((zpowers_le).2 h.t_mem_centralizer)
    refine le_inf (sup_le_sup_right inf_le_left _) (sup_le ?_ ?_)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le hZE ((zpowers_le).2 htZ)
    · rw [zpowers_le]
      exact mem_centralizer_iff.2 fun b hb => mem_centralizer_singleton_iff.1 (hBt hb)

omit
  [Finite K] [CharP K 2] in
theorem mem_of_mem_sup_zpowers (h : Setup G L f t) {E X : Subgroup G} (hEL : E ≤ L)
    (hXE : X ≤ centralizer (E : Set G)) {x₀ : G} (hx₀ : x₀ ∈ X) (hx₀t : x₀ * t ≠ t * x₀) {z : G}
    (hz : z ∈ E ⊔ zpowers t) (hzX : z ∈ centralizer (X : Set G)) : z ∈ E := by
  rcases (h.mem_sup_zpowers_iff hEL).1 hz with hz' | hz'
  · exact hz'
  · exfalso
    have huX : (t * z)⁻¹ ∈ centralizer (X : Set G) := by
      rw [← Subgroup.le_centralizer_iff] at hXE
      exact inv_mem (hXE hz')
    have htX : t ∈ centralizer (X : Set G) := by
      have := mul_mem hzX huX
      rwa [show z * (t * z)⁻¹ = t⁻¹ by group, inv_mem_iff] at this
    exact hx₀t (mem_centralizer_iff.1 htX x₀ hx₀)

omit [Finite K] in
theorem center_tD (h : Setup G L f t) (d : G2Data L K) :
    (d.D ⊔ zpowers t) ⊓ centralizer ((d.D ⊔ zpowers t : Subgroup G) : Set G) =
      d.U ⊔ zpowers t := by
  rw [h.center_sup_zpowers (E := d.D) (d.image_le _), (d.yamada_3_12_centers).2.1]

theorem yamada_5_3_1 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) =
        normalizer ((d.D ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) =
        yamadaC₁ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G)) ∧
      ((normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) : Subgroup G) : Set G) =
        (yamadaC₁ d t : Set G) *
          ((centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) : Subgroup G) : Set G) ∧
      normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (d.D : Set G) ∧
      yamadaC₁ d t ⊓ centralizer ({t} : Set G) = d.D ⊔ zpowers t := by
  obtain ⟨-, h2, -, h4⟩ := h.two_core_C₁ d hK
  have hK4 : 4 ≤ Nat.card K := hK ▸ h.four_le
  refine ⟨le_antisymm (h.normalizer_tU_le_normalizer_tD d hK) ?_, le_antisymm (fun g hg => ?_)
    (sup_le (yamadaC₁_le d t) (h.centralizer_inf_normalizer_U_le d)), ?_, ?_, h2⟩
  · refine le_normalizer_of_conj_mem fun n hn x hx => ?_
    rw [← h.center_tD d] at hx ⊢
    obtain ⟨hxB, hxc⟩ := hx
    obtain ⟨h5, h6⟩ := conj_mem_center_of_mem_normalizer hn hxB fun r hr =>
      (mem_centralizer_iff.1 hxc r hr).symm
    exact ⟨h5, mem_centralizer_iff.2 fun r hr => (h6 r hr).symm⟩
  · obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
    exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
  · ext g
    constructor
    · intro hg
      obtain ⟨c, hc, x, hx, rfl⟩ := h4 g hg
      refine ⟨c * x * c⁻¹, (mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t
        (h.centralizer_inf_normalizer_U_le d hc)) x).1 hx, c, hc, by group⟩
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact mul_mem (yamadaC₁_le d t hx) (h.centralizer_inf_normalizer_U_le d hc)
  ·
    set K₀ := normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer (d.U : Set G) ⊓
      centralizer ({t} : Set G) with hK₀
    have hKL : ⁅K₀, K₀⁆ ≤ L := by
      rw [commutator_le]
      intro k₁ hk₁ k₂ hk₂
      obtain ⟨l₁, hl₁, c₁, hc₁, rfl⟩ := h.exists_mul_of_mem_centralizer_U d hK ⟨hk₁.2, hk₁.1.2⟩
      obtain ⟨l₂, hl₂, c₂, hc₂, rfl⟩ := h.exists_mul_of_mem_centralizer_U d hK ⟨hk₂.2, hk₂.1.2⟩
      have hl₁L : l₁ ∈ L := sup_le (d.image_le _) (d.image_le _) hl₁
      have hl₂L : l₂ ∈ L := sup_le (d.image_le _) (d.image_le _) hl₂
      have hc₂C : c₂ ∈ centralizer ({t} : Set G) := (zpowers_le).2 h.t_mem_centralizer hc₂
      rw [commutatorElement_mul_mul_of_commute
        (commute_of_mem_zpowers hc₁ (h.L_le_centralizer hl₂L)).symm
        (commute_of_mem_zpowers hc₁ hc₂C).symm
        (commute_of_mem_zpowers hc₂ (h.L_le_centralizer hl₁L)).symm, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hl₁L hl₂L) (inv_mem hl₁L)) (inv_mem hl₂L)
    have hD : (d.D ⊔ zpowers t) ⊓ ⁅K₀, K₀⁆ = d.D := by
      refine le_antisymm (fun x hx => h.mem_D_of_mem_sup d hx.1 (hKL hx.2)) (le_inf le_sup_left ?_)
      calc d.D ≤ d.D ⊔ d.leviA := le_sup_left
        _ = ⁅d.D ⊔ d.leviA, d.D ⊔ d.leviA⁆ := ((d.yamada_3_13_4_G hK4).2.1).symm
        _ ≤ ⁅K₀, K₀⁆ := commutator_mono (h.D_sup_leviA_le_kernel d) (h.D_sup_leviA_le_kernel d)
    intro g hg
    rw [← hD]
    exact Common.mem_normalizer_inf (h.normalizer_tU_le_normalizer_tD d hK hg)
      (normalizer_le_normalizer_commutator K₀ (h.normalizer_tU_le_normalizer_kernel d hK hg))

theorem yamada_5_3_2 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    {x | ∃ c ∈ yamadaC₁ d t, c * t * c⁻¹ = x} = (fun u => t * u) '' (d.U : Set G) := by
  obtain ⟨-, -, h3, -⟩ := h.two_core_C₁ d hK
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [← (h.conj_t_eq_tU d hK).2]
    exact ⟨c, yamadaC₁_le d t hc, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨c, hc, hct⟩ := h3 u hu
    exact ⟨c⁻¹, inv_mem hc, by rw [inv_inv]; exact hct⟩

omit [Finite K] in
theorem yamadaR_le_centralizer_U (h : Setup G L f t) (d : G2Data L K) :
    yamadaR d t ≤ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G) ⊓
      centralizer (d.U : Set G) := by
  have hSU : d.S ≤ centralizer (d.U : Set G) := by
    rw [Subgroup.le_centralizer_iff, ← (d.yamada_3_12_centers).1]
    exact inf_le_right
  have htU : t ∈ centralizer (d.U : Set G) := mem_centralizer_iff.2 fun u hu =>
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.image_le _ hu))
  have hRU : yamadaR d t ≤ centralizer (d.U : Set G) := by
    rw [h.yamadaR_eq d]
    exact sup_le hSU ((zpowers_le).2 htU)
  exact le_inf (le_inf (h.yamadaR_le_centralizer d)
    (hRU.trans (Subgroup.centralizer_le_normalizer _))) hRU

omit [Finite K] in
theorem tD_le_yamadaR (h : Setup G L f t) (d : G2Data L K) : d.D ⊔ zpowers t ≤ yamadaR d t := by
  obtain ⟨-, -, -, -, -, -, -, hDS, -, -⟩ := d.inclusions
  rw [h.yamadaR_eq d]
  exact sup_le_sup_right hDS _

omit [Finite K] in
theorem normalizer_yamadaR_le (h : Setup G L f t) (d : G2Data L K) :
    normalizer (yamadaR d t : Set G) ≤ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun n hn x hx => ?_
  obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 ((h.center_yamadaR d).ge hx)
  obtain ⟨hnR, hnc⟩ := conj_mem_center_of_mem_normalizer hn hxR fun r hr =>
    (mem_centralizer_iff.1 hxc r hr).symm
  rw [← h.center_yamadaR d]
  exact Subgroup.mem_inf.2 ⟨hnR, mem_centralizer_iff.2 fun r hr => (hnc r hr).symm⟩

theorem yamadaC₁_le_normalizer_yamadaR (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) : yamadaC₁ d t ≤ normalizer (yamadaR d t : Set G) := by
  obtain ⟨hC₁U, hC₁t, -, -⟩ := h.two_core_C₁ d hK
  have hc := h.cosetData_tU d hK
  refine le_normalizer_of_conj_mem fun c hcC₁ r hr => ?_
  obtain ⟨⟨hrC, hrN⟩, hrU⟩ := h.yamadaR_le_centralizer_U d hr
  have hrH : r ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) :=
    h.centralizer_inf_normalizer_U_le d ⟨hrC, hrN⟩
  have hz : r * c⁻¹ * r⁻¹ ∈ yamadaC₁ d t :=
    (mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t hrH) _).1 (inv_mem hcC₁)
  have hcV : c ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) := ⟨yamadaC₁_le d t hcC₁, hC₁U hcC₁⟩
  have hzV : r * c⁻¹ * r⁻¹ ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
      centralizer (d.U : Set G) := ⟨yamadaC₁_le d t hz, hC₁U hz⟩
  have hy : (c⁻¹ * t * c * t)⁻¹ ∈ d.U := inv_mem (hc.crossed_mem_of_mem hcV)
  have h1 : (c * (r * c⁻¹ * r⁻¹))⁻¹ * t * (c * (r * c⁻¹ * r⁻¹)) * t = 1 := by
    rw [hc.crossed_mul_of_mem hcV hzV,
      CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (mem_centralizer_singleton_iff.1 hrC),
      hc.crossed_inv_of_mem hcV, ← mem_centralizer_iff.1 hrU _ hy, mul_inv_cancel_right,
      mul_inv_cancel]
  rw [hc.crossed_eq_iff (one_mem _), mul_one] at h1
  have hwt : c * (r * c⁻¹ * r⁻¹) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc c * (r * c⁻¹ * r⁻¹) * t =
        c * (r * c⁻¹ * r⁻¹) * ((c * (r * c⁻¹ * r⁻¹))⁻¹ * t * (c * (r * c⁻¹ * r⁻¹))) := by
          rw [h1]
      _ = t * (c * (r * c⁻¹ * r⁻¹)) := by group
  have hwB : c * (r * c⁻¹ * r⁻¹) ∈ d.D ⊔ zpowers t := by
    rw [← hC₁t]
    exact ⟨mul_mem hcC₁ hz, hwt⟩
  rw [show c * r * c⁻¹ = c * (r * c⁻¹ * r⁻¹) * r by group]
  exact mul_mem (h.tD_le_yamadaR d hwB) hr

theorem yamada_5_3_3 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    normalizer (yamadaR d t : Set G) =
        yamadaC₁ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) ∧
      ((normalizer (yamadaR d t : Set G) : Subgroup G) : Set G) =
        (yamadaC₁ d t : Set G) *
          ((centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) : Subgroup G) : Set G) ∧
      yamadaR₁ d t < normalizer (yamadaR d t : Set G) := by
  obtain ⟨hC₁U, -, -, h4⟩ := h.two_core_C₁ d hK
  have hSL : d.S ≤ L := d.image_le _
  have hNS : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
      normalizer (yamadaR d t : Set G) := by
    intro x hx
    rw [h.yamadaR_eq d]
    exact mem_normalizer_sup hx.2 (mem_normalizer_zpowers (mem_centralizer_singleton_iff.1 hx.1))
  have heq : normalizer (yamadaR d t : Set G) =
      yamadaC₁ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) := by
    refine le_antisymm (fun n hn => ?_) (sup_le (h.yamadaC₁_le_normalizer_yamadaR d hK) hNS)
    obtain ⟨c, hc, x, hx, rfl⟩ := h4 n (h.normalizer_yamadaR_le d hn)
    have hcR : c ∈ normalizer (yamadaR d t : Set G) := by
      have := mul_mem hn (inv_mem (h.yamadaC₁_le_normalizer_yamadaR d hK hx))
      rwa [mul_inv_cancel_right] at this
    have hcS : c ∈ normalizer (d.S : Set G) := mem_normalizer_of_conj_mem fun s hs => by
      have h1 : c * s * c⁻¹ ∈ yamadaR d t :=
        (mem_normalizer_iff.1 hcR s).1 ((h.yamadaR_eq d).ge (mem_sup_left hs))
      have h2 : c * s * c⁻¹ ∈ L :=
        (mem_normalizer_iff.1 (h.centralizer_le_normalizer hc.1) s).1 (hSL hs)
      rw [h.yamadaR_eq d] at h1
      rcases (h.mem_sup_zpowers_iff hSL).1 h1 with h3 | h3
      · exact h3
      · exfalso
        refine h.t_not_mem_L ?_
        have := mul_mem (hSL h3) (inv_mem h2)
        rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_right ⟨hc.1, hcS⟩) (mem_sup_left hx)
  refine ⟨heq, ?_, lt_of_le_of_ne ?_ fun hR₁ => ?_⟩
  · ext n
    constructor
    · intro hn
      have hNC : centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤
          normalizer (yamadaC₁ d t : Set G) :=
        hNS.trans ((h.normalizer_yamadaR_le d).trans (le_normalizer_yamadaC₁ d t))
      rw [SetLike.mem_coe, heq] at hn
      obtain ⟨x, hx, c, hc, rfl⟩ := Common.exists_mul_of_le_normalizer hNC n hn
      exact ⟨x, hx, c, hc, rfl⟩
    · rintro ⟨x, hx, c, hc, rfl⟩
      exact mul_mem (h.yamadaC₁_le_normalizer_yamadaR d hK hx) (hNS hc)
  · rw [heq]
    exact sup_le_sup_left (le_inf (h.S_le_centralizer d) le_normalizer) _
  · obtain ⟨ι, hι⟩ := d.exists_mulEquiv_U
    obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one (hK ▸ h.four_le : 4 ≤ Nat.card K)
    obtain ⟨e, he, hea⟩ := d.exists_mem_J₃_scalar ι hι ha0
    have heJ : e ∈ L ⊓ normalizer (d.S : Set G) := by
      rw [(d.yamada_3_13_1_G).2.2]
      exact mem_sup_left (d.image_mono inf_le_left he)
    have heR : e ∈ normalizer (yamadaR d t : Set G) :=
      hNS ⟨h.L_le_centralizer heJ.1, heJ.2⟩
    rw [← hR₁] at heR
    have hSU : d.S ≤ centralizer (d.U : Set G) := by
      rw [Subgroup.le_centralizer_iff, ← (d.yamada_3_12_centers).1]
      exact inf_le_right
    have hR₁U : yamadaR₁ d t ≤ centralizer (d.U : Set G) := sup_le hC₁U hSU
    have h1 := mem_centralizer_iff.1 (hR₁U heR) _ (ι (Multiplicative.ofAdd 1)).2
    have h2 := hea 1
    rw [← h1, mul_inv_cancel_right, mul_one] at h2
    exact ha1 (Multiplicative.ofAdd.injective (ι.injective (Subtype.ext h2)).symm)

theorem yamada_5_3_4 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    ∃ _ : ((d.D ⊔ zpowers t).subgroupOf (yamadaC₁ d t)).Normal,
      ∃ φ : yamadaC₁ d t ⧸ (d.D ⊔ zpowers t).subgroupOf (yamadaC₁ d t) ≃* d.U,
        (∀ x : yamadaC₁ d t, (φ (QuotientGroup.mk x) : G) = t * (x : G)⁻¹ * t * x) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer (d.U : Set G), ∀ x : yamadaC₁ d t,
          ∃ hx : c * x * c⁻¹ ∈ yamadaC₁ d t,
            (φ (QuotientGroup.mk ⟨c * x * c⁻¹, hx⟩) : G) = c * φ (QuotientGroup.mk x) * c⁻¹ := by
  obtain ⟨h1, h2, h3, -⟩ := h.two_core_C₁ d hK
  have hc := h.cosetData_tU d hK
  have hN := hc.normal_subgroupOf (yamadaC₁_le d t) h1 h2
  obtain ⟨φ, hφ1, hφ2⟩ := hc.exists_mulEquiv_quotient (yamadaC₁_le d t) h1 h2 h3
  refine ⟨hN, φ, fun x => ?_, fun c hc' x => ?_⟩
  · rw [hφ1]
    have hy := hc.crossed_mem_of_mem ⟨yamadaC₁_le d t x.2, h1 x.2⟩
    have hyt := hc.comm_of_mem hy
    symm
    calc t * (x : G)⁻¹ * t * x = t * ((x : G)⁻¹ * t * x * t) * t⁻¹ := by group
      _ = (x : G)⁻¹ * t * x * t := by rw [hyt, mul_inv_cancel_right]
  · have hcH : c ∈ normalizer ((d.U ⊔ zpowers t : Subgroup G) : Set G) ⊓
        centralizer ({t} : Set G) := by
      rw [h.normalizer_tU_inf_centralizer d hK]
      exact hc'
    have hx : c * x * c⁻¹ ∈ yamadaC₁ d t :=
      (mem_normalizer_iff.1 (le_normalizer_yamadaC₁ d t hcH.1) x).1 x.2
    exact ⟨hx, hφ2 c hcH x hx⟩

theorem yamada_5_3_5 (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) :
    yamadaC₁ d t ⊓ centralizer (yamadaC₁ d t : Set G) = d.U ∧
      yamadaR₁ d t ⊓ centralizer (yamadaR₁ d t : Set G) = d.U := by
  obtain ⟨h1, h2, h3, -⟩ := h.two_core_C₁ d hK
  obtain ⟨hUY, hYX, -, hXF, -, hFD, -⟩ := d.inclusions
  have hUD : d.U ≤ d.D := hUY.trans (hYX.trans (hXF.trans hFD))
  have hBC₁ : d.D ⊔ zpowers t ≤ yamadaC₁ d t := by
    rw [← h2]
    exact inf_le_left
  have hUC₁ : d.U ≤ yamadaC₁ d t := (hUD.trans le_sup_left).trans hBC₁
  have htC₁ : t ∈ yamadaC₁ d t := hBC₁ (mem_sup_right (mem_zpowers t))
  have hSU : d.S ≤ centralizer (d.U : Set G) := by
    rw [Subgroup.le_centralizer_iff, ← (d.yamada_3_12_centers).1]
    exact inf_le_right
  have hR₁U : yamadaR₁ d t ≤ centralizer (d.U : Set G) := sup_le h1 hSU
  obtain ⟨-, -, -, hcU, hc1, -⟩ := d.xv_xc_spec
  obtain ⟨x₀, hx₀, hx₀t⟩ := h3 d.xc hcU
  have hx₀' : x₀ * t ≠ t * x₀ := fun e => hc1 (by
    have e' : x₀⁻¹ * t * x₀ = t := by rw [mul_assoc, ← e, inv_mul_cancel_left]
    rw [e'] at hx₀t
    exact (mul_eq_left.1 hx₀t.symm))
  have hUZ : ∀ X : Subgroup G, d.U ≤ X → X ≤ centralizer (d.U : Set G) →
      d.U ≤ X ⊓ centralizer (X : Set G) := fun X hUX hXU =>
    le_inf hUX (by rw [Subgroup.le_centralizer_iff]; exact hXU)
  constructor
  · refine le_antisymm (fun z hz => ?_) (hUZ _ hUC₁ h1)
    obtain ⟨hzC₁, hzc⟩ := hz
    have hzt : z ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hzc t htC₁).symm
    have hzB : z ∈ d.D ⊔ zpowers t := by
      rw [← h2]
      exact ⟨hzC₁, hzt⟩
    have hzZ : z ∈ d.U ⊔ zpowers t := by
      rw [← h.center_tD d]
      exact ⟨hzB, mem_centralizer_iff.2 fun b hb => mem_centralizer_iff.1 hzc b (hBC₁ hb)⟩
    exact h.mem_of_mem_sup_zpowers (d.image_le _) h1 hx₀ hx₀' hzZ hzc
  · refine le_antisymm (fun z hz => ?_) (hUZ _ (hUC₁.trans le_sup_left) hR₁U)
    obtain ⟨hzR₁, hzc⟩ := hz
    have hzt : z ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hzc t (mem_sup_left htC₁)).symm
    have hSH : d.S ≤ normalizer (yamadaC₁ d t : Set G) := fun s hs =>
      le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_U_le d
        ⟨h.S_le_centralizer d hs, d.S_le_normalizers.1 hs⟩)
    obtain ⟨x, hx, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer hSH z hzR₁
    have hsC := h.S_le_centralizer d hs
    have hxC : x ∈ centralizer ({t} : Set G) := by
      have := mul_mem hzt (inv_mem hsC)
      rwa [mul_inv_cancel_right] at this
    have hxR : x ∈ yamadaR d t := h.tD_le_yamadaR d (by rw [← h2]; exact ⟨hx, hxC⟩)
    have hRR₁ : yamadaR d t ≤ yamadaR₁ d t := by
      rw [h.yamadaR_eq d]
      exact sup_le le_sup_right ((zpowers_le).2 (mem_sup_left htC₁))
    have hzZ : x * s ∈ d.U ⊔ zpowers t := by
      rw [← h.center_yamadaR d]
      refine ⟨mul_mem hxR ((h.yamadaR_eq d).ge (mem_sup_left hs)), mem_centralizer_iff.2
        fun r hr => mem_centralizer_iff.1 hzc r (hRR₁ hr)⟩
    exact h.mem_of_mem_sup_zpowers (d.image_le _) hR₁U (mem_sup_left hx₀) hx₀' hzZ hzc

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
