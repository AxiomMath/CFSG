module

public import CFSG.CGT.Harada80.Singular

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Harada80

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LargeExtraspecial (eq_one_of_fix_orthogonal_of_map_eq_zero)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

private theorem ne_zero_of_isRootElt (hQ : (polarBilin Q).Nondegenerate) {a : V}
    (ha : Q a = 0) {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hE : ∀ g ∈ E, IsRootElt Q a g) (hE1 : E ≠ ⊥) : a ≠ 0 := by
  rintro rfl
  apply hE1
  rw [eq_bot_iff]
  intro e he
  rw [Subgroup.mem_bot]
  refine eq_one_of_forall_sub_mem_span (Q := Q) hQ ha (hE e he).1 ?_
  intro x
  simpa using (hE e he).2.2 x (by simp)

private theorem pointStabilizer_fix {a : V} (ha0 : a ≠ 0) {s : Gom Q}
    (hs : s ∈ pointStabilizer Q a) :
    s.app a = a ∧ ((s : V ≃ₗ[ZMod 2] V))⁻¹ a = a := by
  obtain ⟨c, hc⟩ := mem_pointStabilizer.mp hs
  have hcne : c ≠ 0 := Gom.ne_zero_of_app_eq_smul ha0 hc
  have hc1 : c = 1 := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one c with h0 | h1
    · exact absurd h0 hcne
    · exact h1
  have hsa : s.app a = a := by rw [hc, hc1, one_smul]
  refine ⟨hsa, ?_⟩
  calc ((s : V ≃ₗ[ZMod 2] V))⁻¹ a
      = ((s : V ≃ₗ[ZMod 2] V))⁻¹ (((s : V ≃ₗ[ZMod 2] V)) a) := by
          rw [show (s : V ≃ₗ[ZMod 2] V) a = a from hsa]
    _ = a := by simp

theorem fixed_eq_span_of_isRootElt (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 2) V) {a : V} (ha : Q a = 0)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : ∀ g ∈ E, IsRootElt Q a g) (hE1 : E ≠ ⊥)
    (hN : ∀ g ∈ elementaryGroup Q, g a = a → ∀ e ∈ E, g * e * g⁻¹ ∈ E) {v : V} :
    (∀ e ∈ E, e v = v) ↔ v ∈ (ZMod 2) ∙ a := by
  classical
  let F : Submodule (ZMod 2) V :=
    { carrier := {v | ∀ e ∈ E, e v = v}
      zero_mem' := by intro e _; simp
      add_mem' := by intro x y hx hy e he; simp [map_add, hx e he, hy e he]
      smul_mem' := by intro c x hx e he; simp [map_smul, hx e he] }
  have ha0 : a ≠ 0 := ne_zero_of_isRootElt hQ ha hE hE1
  have hspanF : (ZMod 2) ∙ a ≤ F := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact fun e he => (hE e he).2.1
  have hFperp : F ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ a) := by
    intro v hv
    rw [mem_orth_span_single_iff]
    by_contra hne
    have hne' : polar Q v a ≠ 0 := by rwa [polar_comm]
    obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have hev : e.1 v = v := hv e.1 e.2
    exact he1 (Subtype.ext
      (IsRootElt.eq_one_of_apply_eq hQ ha (hE e.1 e.2) hne' hev))
  have hFinv : ∀ s ∈ pointStabilizer Q a, ∀ x ∈ F, s.app x ∈ F := by
    intro s hs x hx
    obtain ⟨hsa, hsinv_a⟩ := pointStabilizer_fix (Q := Q) ha0 hs
    show ∀ e ∈ E, e (s.app x) = s.app x
    intro e he
    have hconj : ((s : V ≃ₗ[ZMod 2] V))⁻¹ * e * (s : V ≃ₗ[ZMod 2] V) ∈ E :=
      hN ((s : V ≃ₗ[ZMod 2] V))⁻¹ ((elementaryGroup Q).inv_mem s.2) hsinv_a e he
    have hxfix : (((s : V ≃ₗ[ZMod 2] V))⁻¹ * e * (s : V ≃ₗ[ZMod 2] V)) x = x :=
      hx _ hconj
    have h := congrArg (s : V ≃ₗ[ZMod 2] V) hxfix
    change e ((s : V ≃ₗ[ZMod 2] V) x) = (s : V ≃ₗ[ZMod 2] V) x
    simpa [LinearEquiv.mul_apply] using h
  have hcases := eq_span_or_eq_orth (Q := Q) hQ h5 ha F hspanF hFperp hFinv
  change v ∈ F ↔ v ∈ (ZMod 2) ∙ a
  rcases hcases with h | h
  · rw [h]
  · exfalso
    have hbot : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [Subgroup.mem_bot]
      refine eq_one_of_fix_orthogonal_of_map_eq_zero hQ ha (hE e he).1 ?_
      intro x hx
      have hxorth : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ a) :=
        mem_orth_span_single_iff.mpr hx
      rw [← h] at hxorth
      exact hxorth e he
    exact hE1 hbot

theorem mem_span_sub_of_isRootElt (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 2) V) {a : V} (ha : Q a = 0)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : ∀ g ∈ E, IsRootElt Q a g) (hE1 : E ≠ ⊥)
    (hN : ∀ g ∈ elementaryGroup Q, g a = a → ∀ e ∈ E, g * e * g⁻¹ ∈ E) {z : V}
    (hz : polar Q z a = 0) :
    z ∈ (ZMod 2) ∙ a ⊔ Submodule.span (ZMod 2) {x | ∃ e ∈ E, ∃ v, x = e v - v} := by
  classical
  let gens : Set V := {x | ∃ e ∈ E, ∃ v, x = e v - v}
  let X : Submodule (ZMod 2) V := (ZMod 2) ∙ a ⊔ Submodule.span (ZMod 2) gens
  have ha0 : a ≠ 0 := ne_zero_of_isRootElt hQ ha hE hE1
  have hXperp : X ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) ((ZMod 2) ∙ a) := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact mem_orth_span_single_iff.mpr (polar_self_eq_zero ha)
    · rw [Submodule.span_le]
      rintro x ⟨e, he, v, rfl⟩
      have hroot := hE e he
      have h1 : polar Q a (e v) = polar Q a v := by
        calc polar Q a (e v) = polar Q (e a) (e v) := by rw [hroot.2.1]
          _ = polar Q a v := polar_map_of_mem hroot.1 a v
      have hpolar : polar Q a (e v - v) = 0 := by
        rw [polar_sub_right, h1, sub_self]
      exact mem_orth_span_single_iff.mpr hpolar
  have hXinv : ∀ s ∈ pointStabilizer Q a, ∀ x ∈ X, s.app x ∈ X := by
    intro s hs x hx
    obtain ⟨hsa, hsinv_a⟩ := pointStabilizer_fix (Q := Q) ha0 hs
    have hgen : ∀ y ∈ gens, s.app y ∈ Submodule.span (ZMod 2) gens := by
      rintro y ⟨e, he, v, rfl⟩
      have hconj : (s : V ≃ₗ[ZMod 2] V) * e * ((s : V ≃ₗ[ZMod 2] V))⁻¹ ∈ E :=
        hN (s : V ≃ₗ[ZMod 2] V) s.2 hsa e he
      have hy : s.app (e v - v) =
          ((s : V ≃ₗ[ZMod 2] V) * e * ((s : V ≃ₗ[ZMod 2] V))⁻¹) (s.app v) - s.app v := by
        change (s : V ≃ₗ[ZMod 2] V) (e v - v) =
          ((s : V ≃ₗ[ZMod 2] V) * e * ((s : V ≃ₗ[ZMod 2] V))⁻¹)
            ((s : V ≃ₗ[ZMod 2] V) v) - (s : V ≃ₗ[ZMod 2] V) v
        simp [LinearEquiv.mul_apply]
      rw [hy]
      exact Submodule.subset_span ⟨_, hconj, s.app v, rfl⟩
    have hgenA : (s : V ≃ₗ[ZMod 2] V) '' ({a} : Set V) ⊆
        Submodule.span (ZMod 2) ({a} : Set V) := by
      rintro y ⟨y0, hy0, rfl⟩
      rw [Set.mem_singleton_iff] at hy0
      subst hy0
      exact Submodule.subset_span (by rw [Set.mem_singleton_iff]; exact hsa)
    have hmapA : (s : V ≃ₗ[ZMod 2] V) '' ((ZMod 2) ∙ a) ≤ (ZMod 2) ∙ a :=
      (Submodule.image_span_subset_span (s : V ≃ₗ[ZMod 2] V).toLinearMap {a}).trans
        (Submodule.span_le.mpr hgenA)
    have hmapG : (s : V ≃ₗ[ZMod 2] V) '' (Submodule.span (ZMod 2) gens) ≤
        Submodule.span (ZMod 2) gens :=
      (Submodule.image_span_subset_span (s : V ≃ₗ[ZMod 2] V).toLinearMap gens).trans
        (Submodule.span_le.mpr (by rintro y ⟨y0, hy0, rfl⟩; exact hgen y0 hy0))
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    refine Submodule.mem_sup.mpr ⟨s.app u, hmapA ⟨u, hu, rfl⟩,
      s.app w, hmapG ⟨w, hw, rfl⟩, ?_⟩
    exact (map_add (s : V ≃ₗ[ZMod 2] V) u w).symm
  have hcases := eq_span_or_eq_orth (Q := Q) hQ h5 ha X le_sup_left hXperp hXinv
  rcases hcases with h | h
  · exfalso
    have hbot : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [Subgroup.mem_bot]
      refine eq_one_of_forall_sub_mem_span (Q := Q) hQ ha (hE e he).1 ?_
      intro v
      have hmem : e v - v ∈ X := by
        rw [show X = (ZMod 2) ∙ a ⊔ Submodule.span (ZMod 2) gens from rfl]
        exact Submodule.mem_sup_right (Submodule.subset_span ⟨e, he, v, rfl⟩)
      rw [h] at hmem
      simpa using hmem
    exact hE1 hbot
  · change z ∈ X
    rw [h]
    exact mem_orth_span_single_iff.mpr (by rwa [polar_comm])

end CFSG.CGT.Harada80

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LargeExtraspecial (eq_one_of_fix_orthogonal_of_map_eq_zero)

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ}
  {S : Setting G M J m}

private abbrev cenMul (u : ↥(blockU J)) (w : G) : Subgroup G :=
  Subgroup.centralizer ({(u : G) * w} : Set G)

private abbrev coreCen (u : ↥(blockU J)) (w : G) : Subgroup G :=
  pCoreOf 2 (cenMul u w)

private noncomputable abbrev imgCore (S : Setting G M J m) (hZ : blockZ J = ⊥)
    (u : ↥(blockU J)) (w : G) : Subgroup (Vec m ≃ₗ[ZMod 2] Vec m) :=
  ((coreCen u w).subgroupOf M).map (S.lin hZ)

private abbrev gensOf (S : Setting G M J m) (hZ : blockZ J = ⊥)
    (u : ↥(blockU J)) (w : G) : Set (Vec m) :=
  {v | ∃ e ∈ imgCore S hZ u w, ∃ x, v = e x - x}

private abbrev centerCore (u : ↥(blockU J)) (w : G) : Subgroup G :=
  coreCen u w ⊓ Subgroup.centralizer (coreCen u w : Set G)

private noncomputable abbrev Z0Of (u : ↥(blockU J)) (w : G) : Subgroup G :=
  blockW J ⊓ Subgroup.centralizer (coreCen u w : Set G)

private theorem imgCore_isRootElt (hE : BlockCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) (hZ : blockZ J = ⊥) :
    ∀ g ∈ imgCore S hZ u w, IsRootElt (quadQ m) (S.vec u) g := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  have hxR : (x : G) ∈ coreCen u w := Subgroup.mem_subgroupOf.mp hx
  have hxM : (x : G) ∈ M :=
    pCoreOf_centralizer_le_of_singular (S := S) hE hu1 hu hw hxR
  have hxH : (x : G) ∈ cenMul u w :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (cenMul u w) hxR
  refine ⟨S.lin_mem_orthogonalGroup hZ x, ?_, ?_⟩
  · exact (S.lin_vec_eq_iff hZ x u).mpr
      (conj_eq_of_mem_centralizer_mul (S := S) hE hw hxM (by simpa [cenMul] using hxH))
  · intro z hz
    exact S.lin_sub_mem_span_of_singular hZ hu
      (pCoreOf_centralizer_le_of_singular (S := S) hE hu1 hu hw)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cenMul u w))
      (fun t ht => conj_eq_of_mem_centralizer_mul (S := S) hE hw
        (pCoreOf_centralizer_le_of_singular (S := S) hE hu1 hu hw ht)
        (by simpa [cenMul] using CFSG.LieType.BorelTits.pCoreOf_le 2 (cenMul u w) ht))
      (fun ℓ hℓJ hℓu t ht => conj_mem_pCoreOf_centralizer_of_centralizes hw hℓJ hℓu ht)
      hxR hz

private theorem imgCore_normalized (hE : EvenCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) (hZ : blockZ J = ⊥) :
    ∀ g ∈ elementaryGroup (quadQ m), g (S.vec u) = S.vec u →
      ∀ e ∈ imgCore S hZ u w, g * e * g⁻¹ ∈ imgCore S hZ u w := by
  intro g hg hgv e he
  obtain ⟨ℓ, hℓ⟩ := S.exists_lin_eq_of_mem_elementaryGroup hZ hg
  have hℓu : (ℓ : G) * (u : G) * (ℓ : G)⁻¹ = u := by
    apply (S.lin_vec_eq_iff hZ (Subgroup.inclusion S.le ℓ) u).mp
    rw [hℓ]; exact hgv
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
  have hxR : (x : G) ∈ coreCen u w := Subgroup.mem_subgroupOf.mp hx
  have hqR : (ℓ : G) * (x : G) * (ℓ : G)⁻¹ ∈ coreCen u w :=
    conj_mem_pCoreOf_centralizer_of_centralizes hw ℓ.2 hℓu hxR
  let q : ↥M := (Subgroup.inclusion S.le ℓ) * x * (Subgroup.inclusion S.le ℓ)⁻¹
  have hqval : (q : G) = (ℓ : G) * (x : G) * (ℓ : G)⁻¹ := by
    simp [q, Subgroup.inclusion]
  have hqsub : q ∈ (coreCen u w).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (by rw [hqval]; exact hqR)
  refine Subgroup.mem_map.mpr ⟨q, hqsub, ?_⟩
  calc S.lin hZ q = S.lin hZ (Subgroup.inclusion S.le ℓ) * S.lin hZ x *
        (S.lin hZ (Subgroup.inclusion S.le ℓ))⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = g * S.lin hZ x * g⁻¹ := by rw [hℓ]

private theorem le_of_imgCore_eq_bot (hE : EvenCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) (hZ : blockZ J = ⊥)
    (hbot : imgCore S hZ u w = ⊥) : cenMul u w ≤ M := by
  let H : Subgroup G := cenMul u w
  let R : Subgroup G := coreCen u w
  let AW : Subgroup G := pCoreOf 2 M
  have hRleM : R ≤ M :=
    pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw
  have hAWleH : AW ≤ H := pCoreOf_le_centralizer_mul S hE.toBlockCase hw
  have hf_one : ∀ x : ↥(R.subgroupOf M), S.lin hZ x.1 = 1 := by
    intro x
    have hxr : S.lin hZ x.1 ∈ imgCore S hZ u w := Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
    rw [hbot] at hxr
    exact Subgroup.mem_bot.mp hxr
  have hRleAW : R ≤ AW := by
    intro x hx
    have hxM : x ∈ M := hRleM hx
    let xM : ↥M := ⟨x, hxM⟩
    let x' : ↥(R.subgroupOf M) := ⟨xM, Subgroup.mem_subgroupOf.mpr hx⟩
    have hx1 : S.lin hZ xM = 1 := hf_one x'
    exact mem_pCoreOf_of_lin_eq_one (S := S) hE.toBlockCase hZ hRleM
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hx (by simpa using hx1)
  have htAW : ((u : G) * w) ∈ AW := by
    rw [show AW = pCoreOf 2 M from rfl, pCoreOf_eq (S := S) hE.toBlockCase]
    exact Subgroup.mul_mem_sup u.2 hw
  have ht1 : ((u : G) * w) ≠ 1 := fun h1 =>
    mul_notMem_blockW S hZ hu1 hw (h1 ▸ (blockW J).one_mem)
  have hAWleR : AW ≤ R := by
    intro x hx
    exact le_pCoreOf_of_centralizes (S := S) htAW ht1 (hAWleH hx)
      (fun y hy => pCoreOf_comm (S := S) hE.toBlockCase hx (hRleAW hy))
  have hReq : R = AW := le_antisymm hRleAW hAWleR
  have hHleNR : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.le_normalizer (H := H)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (AW : Set G) := by
    rw [← hReq]; exact hHleNR hx
  rw [show AW = pCoreOf 2 M from rfl,
    CFSG.RankThree.PartTwo.Late.normalizer_pCoreOf_of_isMaximalTwoLocal S.maxLocal] at hxN
  exact hxN

private theorem gens_fixed (hE : EvenCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) (hZ : blockZ J = ⊥)
    {z : G} (hzR : z ∈ coreCen u w)
    (hzC : z ∈ Subgroup.centralizer (coreCen u w : Set G)) :
    ∀ v ∈ gensOf S hZ u w,
      S.lin hZ ⟨z, pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw
        hzR⟩ v = v := by
  intro v hv
  rcases hv with ⟨e, he, x, rfl⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
  obtain ⟨a, rfl⟩ := S.vec_surjective x
  have hyR : (y : G) ∈ coreCen u w := Subgroup.mem_subgroupOf.mp hy
  let zM : ↥M := ⟨z, pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw hzR⟩
  let yc : G := (y : G) * (a : G) * (y : G)⁻¹
  have hycA : yc ∈ blockU J := conj_mem_blockU S y.2 a.2
  let cSub : ↥(blockU J) := a⁻¹ * ⟨yc, hycA⟩
  have haH : (a : G) ∈ cenMul u w :=
    pCoreOf_le_centralizer_mul S hE.toBlockCase hw (blockU_le_pCoreOf S a.2)
  have hconjR : (a : G)⁻¹ * (y : G) * (a : G) ∈ coreCen u w := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.le_normalizer (H := cenMul u w)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (cenMul u w))
        ((cenMul u w).inv_mem haH)) (y : G)).mp hyR
    simpa using this
  have hcR : (cSub : G) ∈ coreCen u w := by
    have hEq : (cSub : G) = ((a : G)⁻¹ * (y : G) * (a : G)) * (y : G)⁻¹ := by
      dsimp [cSub, yc]; group
    rw [hEq]
    exact (coreCen u w).mul_mem hconjR ((coreCen u w).inv_mem hyR)
  have hvec : S.vec cSub = S.lin hZ y (S.vec a) - S.vec a := by
    have h1 : S.vec cSub = S.vec a⁻¹ + S.vec ⟨yc, hycA⟩ := by
      dsimp [cSub]; rw [S.vec_mul]
    have h2 : S.vec ⟨yc, hycA⟩ = S.lin hZ y (S.vec a) := by rw [S.lin_vec hZ y a]
    have hneg : S.vec a⁻¹ = S.vec a := by
      have hsum : S.vec a⁻¹ + S.vec a = 0 := by
        have h := S.vec_mul a⁻¹ a
        rw [inv_mul_cancel, S.vec_one] at h
        exact h.symm
      have h' := eq_neg_of_add_eq_zero_left hsum
      rwa [ZModModule.neg_eq_self] at h'
    rw [h1, h2, hneg, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
  have hcz : z * (cSub : G) * z⁻¹ = (cSub : G) := by
    have hcomm : (cSub : G) * z = z * (cSub : G) :=
      (Subgroup.mem_centralizer_iff.mp hzC) (cSub : G) hcR
    calc z * (cSub : G) * z⁻¹ = ((cSub : G) * z) * z⁻¹ := by rw [← hcomm]
      _ = (cSub : G) := by group
  have hfixc : S.lin hZ zM (S.vec cSub) = S.vec cSub :=
    (S.lin_vec_eq_iff hZ zM cSub).mpr hcz
  rw [← hvec]
  simpa [zM] using hfixc

private theorem lin_eq_one_of_mem_center (hE : EvenCase J m) {u : ↥(blockU J)}
    (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J)
    (hZ : blockZ J = ⊥)
    (hNE : ∀ g ∈ elementaryGroup (quadQ m), g (S.vec u) = S.vec u →
      ∀ e ∈ imgCore S hZ u w, g * e * g⁻¹ ∈ imgCore S hZ u w)
    (hEne : imgCore S hZ u w ≠ ⊥) :
    ∀ z (hz : z ∈ centerCore u w),
      S.lin hZ ⟨z, pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw
        (Subgroup.mem_inf.mp hz).1⟩ = 1 := by
  intro z hz
  have hzR : z ∈ coreCen u w := (Subgroup.mem_inf.mp hz).1
  have hzC : z ∈ Subgroup.centralizer (coreCen u w : Set G) :=
    (Subgroup.mem_inf.mp hz).2
  have hzM : z ∈ M :=
    pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw hzR
  let zM : ↥M := ⟨z, hzM⟩
  have hzH : z ∈ cenMul u w :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (cenMul u w) hzR
  have hfixu : S.lin hZ zM (S.vec u) = S.vec u :=
    (S.lin_vec_eq_iff hZ zM u).mpr
      (conj_eq_of_mem_centralizer_mul (S := S) hE.toBlockCase hw hzM
        (by simpa [cenMul] using hzH))
  let Fix : Submodule (ZMod 2) (Vec m) :=
    { carrier := {v | S.lin hZ zM v = v}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        change S.lin hZ zM (x + y) = x + y
        rw [map_add, hx, hy]
      smul_mem' := by
        intro c x hx
        change S.lin hZ zM (c • x) = c • x
        rw [map_smul, hx] }
  let gens : Set (Vec m) := gensOf S hZ u w
  have hgen : ∀ v ∈ gens, v ∈ Fix := by
    intro v hv
    change S.lin hZ zM v = v
    simpa [zM, gens] using gens_fixed (S := S) hE hu1 hu hw hZ hzR hzC v hv
  have hFixspan : (ZMod 2) ∙ S.vec u ⊔ Submodule.span (ZMod 2) gens ≤ Fix := by
    refine sup_le ?_ (Submodule.span_le.mpr hgen)
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hfixu
  have hroot := imgCore_isRootElt (S := S) hE.toBlockCase hu1 hu hw hZ
  have hfixorth : ∀ x, polar (quadQ m) (S.vec u) x = 0 → S.lin hZ zM x = x := by
    intro x hx
    exact hFixspan (mem_span_sub_of_isRootElt (Q := quadQ m) (nondegenerate_quadQ m)
      (by
        rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
        rcases S.m_eq with h | h <;> omega)
      hu hroot hEne hNE (by rwa [polar_comm]))
  exact eq_one_of_fix_orthogonal_of_map_eq_zero (nondegenerate_quadQ m) hu
    (S.lin_mem_orthogonalGroup hZ zM) hfixorth

private theorem mem_center_exists_mul (hE : EvenCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) (hZ : blockZ J = ⊥)
    (hNE : ∀ g ∈ elementaryGroup (quadQ m), g (S.vec u) = S.vec u →
      ∀ e ∈ imgCore S hZ u w, g * e * g⁻¹ ∈ imgCore S hZ u w)
    (hEne : imgCore S hZ u w ≠ ⊥) :
    ∀ z ∈ centerCore u w, ∃ a : ↥(blockU J), ∃ w' : G,
      w' ∈ blockW J ∧ z = (a : G) * w' ∧ (a = 1 ∨ a = u) := by
  intro z hz
  have hzR : z ∈ coreCen u w := (Subgroup.mem_inf.mp hz).1
  have hzC : z ∈ Subgroup.centralizer (coreCen u w : Set G) :=
    (Subgroup.mem_inf.mp hz).2
  have hz1 : S.lin hZ ⟨z, pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase
      hu1 hu hw hzR⟩ = 1 :=
    lin_eq_one_of_mem_center (S := S) hE hu1 hu hw hZ hNE hEne z hz
  obtain ⟨a, ha, w', hw', hzeq⟩ :=
    exists_mul_of_lin_eq_one (S := S) hE.toBlockCase hZ
      (pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cenMul u w)) hzR hz1
  refine ⟨⟨a, ha⟩, w', hw', hzeq, ?_⟩
  have hfixa : ∀ e ∈ imgCore S hZ u w, e (S.vec ⟨a, ha⟩) = S.vec ⟨a, ha⟩ := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp he
    have hyR : (y : G) ∈ coreCen u w := Subgroup.mem_subgroupOf.mp hy
    have hyM : (y : G) ∈ M :=
      pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw hyR
    have hyz : (y : G) * z = z * (y : G) :=
      (Subgroup.mem_centralizer_iff.mp hzC) (y : G) hyR
    have hyconj : (y : G) * z * (y : G)⁻¹ = z := by
      rw [hyz]; group
    have hyconj' : (y : G) * ((a : G) * w') * (y : G)⁻¹ = (a : G) * w' := by
      rw [← hzeq]; exact hyconj
    have hya : (y : G) * (a : G) * (y : G)⁻¹ = a :=
      ((S.conj_mul_eq_iff hE.toBlockCase hyM ha hw').mp hyconj').1
    calc S.lin hZ y (S.vec ⟨a, ha⟩)
        = S.vec ⟨(y : G) * (a : G) * (y : G)⁻¹,
            conj_mem_blockU S hyM ha⟩ := S.lin_vec hZ y _
      _ = S.vec ⟨a, ha⟩ := by
          apply congrArg S.vec
          exact Subtype.ext hya
  have hspan_a : S.vec ⟨a, ha⟩ ∈ (ZMod 2) ∙ S.vec u :=
    (fixed_eq_span_of_isRootElt (Q := quadQ m) (nondegenerate_quadQ m) (by
      rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
      rcases S.m_eq with h | h <;> omega) hu
      (imgCore_isRootElt (S := S) hE.toBlockCase hu1 hu hw hZ) hEne hNE).mp hfixa
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan_a
  rcases CFSG.RankThree.Literature.FSmith.zmod2_eq_zero_or_eq_one c with hc0 | hc1
  · left
    rw [hc0, zero_smul] at hc
    exact (S.vec_eq_zero_iff hZ).mp hc.symm
  · right
    rw [hc1, one_smul] at hc
    exact (S.vec_injective hZ hc).symm

private theorem Z0_le_coreCen (hE : EvenCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) (hZ : blockZ J = ⊥) :
    Z0Of u w ≤ coreCen u w := by
  intro x hx
  have hxW : x ∈ blockW J := hx.1
  have hxC : x ∈ Subgroup.centralizer (coreCen u w : Set G) := hx.2
  have htAW : ((u : G) * w) ∈ pCoreOf 2 M := by
    rw [pCoreOf_eq (S := S) hE.toBlockCase]
    exact Subgroup.mul_mem_sup u.2 hw
  have ht1 : ((u : G) * w) ≠ 1 := fun h1 =>
    mul_notMem_blockW S hZ hu1 hw (h1 ▸ (blockW J).one_mem)
  have hxH : x ∈ cenMul u w := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * ((u : G) * w) = (x * (u : G)) * w := by group
      _ = ((u : G) * x) * w := by rw [commute_blockU_blockW S u.2 hxW]
      _ = (u : G) * (x * w) := by group
      _ = (u : G) * (w * x) := by rw [hE.toBlockCase.comm x hxW w hw]
      _ = ((u : G) * w) * x := by group
  exact le_pCoreOf_of_centralizes (S := S) htAW ht1 hxH (fun y hy => (hxC y hy).symm)

private theorem inf_centralizer_blockW_ne_bot (S : Setting G M J m) (hE : EvenCase J m)
    {R : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 2 ↥R) :
    blockW J ⊓ Subgroup.centralizer (R : Set G) ≠ ⊥ := by
  classical
  have hW2 : IsPGroup 2 ↥(blockW J) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRNW : R ≤ Subgroup.normalizer (blockW J : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact conj_mem_blockW S (hRM hr) hx
    · intro hx
      have hthis := conj_mem_blockW S (hRM (R.inv_mem hr)) hx
      have hEq : r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ = x := by group
      rwa [hEq] at hthis
  let P : Subgroup G := R ⊔ blockW J
  have hP2 : IsPGroup 2 ↥P := hR.to_sup_of_normal_right' hW2 hRNW
  haveI : Group.IsNilpotent ↥P := hP2.isNilpotent
  have hWP : blockW J ≤ P := le_sup_right
  have hNW : P ≤ Subgroup.normalizer (blockW J : Set G) :=
    sup_le hRNW Subgroup.le_normalizer
  have hN : ((blockW J).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWP).mpr hNW
  have hne : ((blockW J).subgroupOf P) ≠ ⊥ := by
    intro hbot
    apply hE.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hWP hx⟩ : ↥P) ∈ (blockW J).subgroupOf P :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  have hcenter := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨xP, hxP⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hcenter
  obtain ⟨hxW, hxc⟩ := Subgroup.mem_inf.1 hxP
  have hxW' : (xP : G) ∈ blockW J := Subgroup.mem_subgroupOf.mp hxW
  have hxC : (xP : G) ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hcenter_r := Subgroup.mem_center_iff.mp hxc
      (⟨r, Subgroup.mem_sup_left hr⟩ : ↥P)
    have hX := congrArg Subtype.val hcenter_r
    simpa using hX
  intro hbot
  have hmem : (xP : G) ∈ blockW J ⊓ Subgroup.centralizer (R : Set G) :=
    Subgroup.mem_inf.mpr ⟨hxW', hxC⟩
  rw [hbot] at hmem
  exact hx1 (Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hmem)))

private theorem centralizer_normalizes_Z0 (hE : EvenCase J m) {u : ↥(blockU J)}
    (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J)
    (hZ : blockZ J = ⊥)
    (hNE : ∀ g ∈ elementaryGroup (quadQ m), g (S.vec u) = S.vec u →
      ∀ e ∈ imgCore S hZ u w, g * e * g⁻¹ ∈ imgCore S hZ u w)
    (hEne : imgCore S hZ u w ≠ ⊥) :
    cenMul u w ≤ Subgroup.normalizer (Z0Of u w : Set G) := by
  have hZ0leR : Z0Of u w ≤ coreCen u w := Z0_le_coreCen (S := S) hE hu1 hu hw hZ
  have hconj_mem : ∀ {x : G}, x ∈ Z0Of u w → ∀ {h : G}, h ∈ cenMul u w →
      h * x * h⁻¹ ∈ Z0Of u w := by
    intro x hx h hh
    have hxW : x ∈ blockW J := hx.1
    have hxC : x ∈ Subgroup.centralizer (coreCen u w : Set G) := hx.2
    have hxR : x ∈ coreCen u w := hZ0leR hx
    have hhN : h ∈ Subgroup.normalizer (coreCen u w : Set G) :=
      (Subgroup.le_normalizer (H := cenMul u w)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (cenMul u w)) hh
    have hzR : h * x * h⁻¹ ∈ coreCen u w :=
      (Subgroup.mem_normalizer_iff.mp hhN x).mp hxR
    have hzC : h * x * h⁻¹ ∈ Subgroup.centralizer (coreCen u w : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have hr' : h⁻¹ * r * h ∈ coreCen u w := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) r).mp hr
        simpa using this
      have hcomm := (Subgroup.mem_centralizer_iff.mp hxC) (h⁻¹ * r * h) hr'
      calc r * (h * x * h⁻¹) = h * ((h⁻¹ * r * h) * x) * h⁻¹ := by group
        _ = h * (x * (h⁻¹ * r * h)) * h⁻¹ := by rw [hcomm]
        _ = (h * x * h⁻¹) * r := by group
    obtain ⟨a, w', hw', hzeq, ha⟩ :=
      mem_center_exists_mul (S := S) hE hu1 hu hw hZ hNE hEne (h * x * h⁻¹)
        (Subgroup.mem_inf.mpr ⟨hzR, hzC⟩)
    rcases ha with ha1 | hau
    · have hzeq' : h * x * h⁻¹ = w' := by simpa [ha1] using hzeq
      exact Subgroup.mem_inf.mpr ⟨by rw [hzeq']; exact hw', hzC⟩
    · exfalso
      have hzeqU : h * x * h⁻¹ = (u : G) * w' := by simpa [hau] using hzeq
      have hx1 : x ≠ 1 := by
        intro hx1
        have huw : (u : G) * w' = 1 := by
          rw [hx1, mul_one, mul_inv_cancel] at hzeqU
          exact hzeqU.symm
        exact mul_notMem_blockW S hZ hu1 hw' (huw ▸ (blockW J).one_mem)
      exact conj_ne_of_singular (S := S) hE.toBlockCase hu1 hu hw' hxW hx1 h hzeqU
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx; exact hconj_mem hx hh
  · intro hx
    have hthis := hconj_mem hx (Subgroup.inv_mem _ hh)
    have hEq : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x := by group
    rwa [hEq] at hthis

theorem centralizer_le_of_singular (hE : EvenCase J m) {u : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu : quadQ m (S.vec u) = 0) {w : G} (hw : w ∈ blockW J) :
    Subgroup.centralizer ({(u : G) * w} : Set G) ≤ M := by
  classical
  have hZ : blockZ J = ⊥ := S.blockZ_eq_bot hE.toBlockCase.h1
  by_cases hbot : imgCore S hZ u w = ⊥
  · have h := le_of_imgCore_eq_bot (S := S) hE hu1 hu hw hZ hbot
    simpa [cenMul] using h
  · have hNE := imgCore_normalized (S := S) hE hu1 hu hw hZ
    have hZ0ne := inf_centralizer_blockW_ne_bot (S := S) hE
      (pCoreOf_centralizer_le_of_singular (S := S) hE.toBlockCase hu1 hu hw)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cenMul u w))
    have hZ0leR : Z0Of u w ≤ coreCen u w := Z0_le_coreCen (S := S) hE hu1 hu hw hZ
    have hZ02 : IsPGroup 2 ↥(Z0Of u w) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (cenMul u w)).to_le hZ0leR
    have hZ0C : Z0Of u w ≤ Subgroup.centralizer (J : Set G) := fun x hx =>
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx.1
    have hNZ0 : Subgroup.normalizer (Z0Of u w : Set G) ≤ M :=
      CFSG.CGT.Hall82.normalizer_le_of_le_centralizer (M := M) (X := J) S.uniq
        hZ0ne hZ02 hZ0C
    intro x hx
    exact hNZ0 (centralizer_normalizes_Z0 (S := S) hE hu1 hu hw hZ hNE hbot hx)

theorem mem_of_conj_eq_of_singular (hE : EvenCase J m) {u u' : ↥(blockU J)} (hu1 : u ≠ 1)
    (hu1' : u' ≠ 1) (hu : quadQ m (S.vec u) = 0) (hu' : quadQ m (S.vec u') = 0) {w w' : G}
    (hw : w ∈ blockW J) (hw' : w' ∈ blockW J) {g : G}
    (hg : g * ((u : G) * w) * g⁻¹ = (u' : G) * w') : g ∈ M :=
  mem_of_conj_eq_of_singular_of_le (S := S) hE.toBlockCase hu1 hu1' hu hu' hw hw'
    (centralizer_le_of_singular (S := S) hE hu1 hu hw) hg

end CFSG.CGT.Harada80.Setting
