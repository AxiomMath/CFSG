module

public import CFSG.CGT.HaradaParrott80.Ortho
public import CFSG.CGT.Harada80.RhoLin

public section

namespace CFSG.CGT.HaradaParrott80

open CFSG CFSG.QuasithinUnique CFSG.CGT.Harada80 QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LargeExtraspecial.OrthoF2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)

theorem vec_inv (u : ↥(blockU J)) : S.vec u⁻¹ = -S.vec u := by
  rw [eq_neg_iff_add_eq_zero, ← S.vec_mul, inv_mul_cancel, S.vec_one]

include S in
theorem blockU_le_M : blockU J ≤ M :=
  (Setting.blockU_le_blockQ S).trans ((Setting.blockQ_le S).trans S.le)

include S in
theorem five_le_finrank : 5 ≤ Module.finrank (ZMod 2) (Vec m) := by
  rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
  rcases S.m_eq with h | h <;> omega

theorem vec_ne_zero (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1) : S.vec a ≠ 0 :=
  fun h => ha1 ((S.vec_eq_zero_iff hZ).mp h)

theorem lin_eq_one_iff_mem (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) (x : ↥M) :
    S.lin hZ x = 1 ↔ (x : G) ∈ blockU J := by
  rw [S.lin_eq_one_iff hZ]
  exact ⟨fun h => S.mem_blockU_of_centralizer hH1 hZ hC x.2 h,
    fun hx w hw => by rw [Setting.blockU_comm S hx hw, mul_inv_cancel_right]⟩

theorem exists_mem_of_mem_pointStabilizer (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    {s : Gom (quadQ m)} (hs : s ∈ pointStabilizer (quadQ m) (S.vec a)) :
    ∃ ℓ : ↥J, (ℓ : G) * (a : G) * (ℓ : G)⁻¹ = a ∧ S.lin hZ (Subgroup.inclusion S.le ℓ) = s := by
  obtain ⟨ℓ, hℓ⟩ := S.exists_lin_eq_of_mem_elementaryGroup hZ s.2
  refine ⟨ℓ, (S.lin_vec_eq_iff hZ (Subgroup.inclusion S.le ℓ) a).mp ?_, hℓ⟩
  rw [hℓ]
  exact app_eq_of_mem_pointStabilizer (vec_ne_zero S hZ ha1) hs

@[expose] def perpSub (a : ↥(blockU J)) : Subgroup G where
  carrier := {g | ∃ h : g ∈ blockU J, polar (quadQ m) (S.vec ⟨g, h⟩) (S.vec a) = 0}
  one_mem' := ⟨(blockU J).one_mem, by
    rw [show (⟨1, (blockU J).one_mem⟩ : ↥(blockU J)) = 1 from rfl, S.vec_one, polar_zero_left]⟩
  mul_mem' := by
    rintro g h ⟨hg, hg0⟩ ⟨hh, hh0⟩
    refine ⟨(blockU J).mul_mem hg hh, ?_⟩
    rw [show (⟨g * h, (blockU J).mul_mem hg hh⟩ : ↥(blockU J)) = ⟨g, hg⟩ * ⟨h, hh⟩ from rfl,
      S.vec_mul, polar_add_left, hg0, hh0, add_zero]
  inv_mem' := by
    rintro g ⟨hg, hg0⟩
    refine ⟨(blockU J).inv_mem hg, ?_⟩
    rw [show (⟨g⁻¹, (blockU J).inv_mem hg⟩ : ↥(blockU J)) = (⟨g, hg⟩ : ↥(blockU J))⁻¹ from rfl,
      vec_inv, polar_neg_left, hg0, neg_zero]

theorem mem_perpSub_iff {a : ↥(blockU J)} (u : ↥(blockU J)) :
    (u : G) ∈ perpSub S a ↔ polar (quadQ m) (S.vec u) (S.vec a) = 0 :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨u.2, h⟩⟩

theorem perpSub_le_blockU (a : ↥(blockU J)) : perpSub S a ≤ blockU J := fun _ ⟨h, _⟩ => h

theorem mem_perpSub_self {a : ↥(blockU J)} (ha : quadQ m (S.vec a) = 0) :
    (a : G) ∈ perpSub S a :=
  (mem_perpSub_iff S a).mpr (polar_self_eq_zero ha)

theorem card_perpSub (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1) :
    Nat.card (perpSub S a) = 2 ^ (2 * m + 1) := by
  have hbij : Function.Bijective (fun g : ↥(perpSub S a) =>
      (⟨S.vec ⟨g, perpSub_le_blockU S a g.2⟩, (mem_perpSub_iff S _).mp g.2⟩ :
        {z : Vec m // polar (quadQ m) z (S.vec a) = 0})) := by
    refine ⟨fun g h hgh => ?_, fun z => ?_⟩
    · have := S.vec_injective hZ (congrArg Subtype.val hgh)
      exact Subtype.ext (congrArg (fun x : ↥(blockU J) => (x : G)) this)
    · obtain ⟨u, hu⟩ := S.vec_surjective z.1
      exact ⟨⟨u, (mem_perpSub_iff S u).mpr (hu ▸ z.2)⟩, Subtype.ext hu⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij),
    card_polar_eq_zero (nondegenerate_quadQ m) (vec_ne_zero S hZ ha1),
    CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.finrank_minus]
  rfl

theorem conj_mem_perpSub (hZ : blockZ J = ⊥) {a : ↥(blockU J)} {x : G} (hx : x ∈ M)
    (hxa : x * (a : G) * x⁻¹ = a) {u : G} (hu : u ∈ perpSub S a) : x * u * x⁻¹ ∈ perpSub S a := by
  obtain ⟨huA, hu0⟩ := hu
  refine ⟨Setting.conj_mem_blockU S hx huA, ?_⟩
  have hfix : S.lin hZ ⟨x, hx⟩ (S.vec a) = S.vec a := (S.lin_vec_eq_iff hZ ⟨x, hx⟩ a).mpr hxa
  rw [← S.lin_vec hZ ⟨x, hx⟩ ⟨u, huA⟩]
  calc polar (quadQ m) (S.lin hZ ⟨x, hx⟩ (S.vec ⟨u, huA⟩)) (S.vec a)
      = polar (quadQ m) (S.lin hZ ⟨x, hx⟩ (S.vec ⟨u, huA⟩)) (S.lin hZ ⟨x, hx⟩ (S.vec a)) := by
        rw [hfix]
    _ = 0 := by rw [S.polar_lin hZ]; exact hu0

theorem mem_blockU_of_centralizer_perpSub (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha : quadQ m (S.vec a) = 0)
    {x : G} (hx : x ∈ M) (hxc : ∀ u ∈ perpSub S a, x * u * x⁻¹ = u) : x ∈ blockU J := by
  refine (lin_eq_one_iff_mem S hH1 hZ hC ⟨x, hx⟩).mp ?_
  refine CFSG.LargeExtraspecial.eq_one_of_fix_orthogonal_of_map_eq_zero (nondegenerate_quadQ m) ha
    (S.lin_mem_orthogonalGroup hZ _) fun z hz => ?_
  obtain ⟨u, rfl⟩ := S.vec_surjective z
  have hu : (u : G) ∈ perpSub S a := (mem_perpSub_iff S u).mpr (by rw [polar_comm]; exact hz)
  rw [S.lin_vec hZ]
  congr 1
  exact Subtype.ext (hxc u hu)

@[expose] noncomputable def rootSub (hZ : blockZ J = ⊥) (a : ↥(blockU J)) : Subgroup G :=
  ((rootGroup (quadQ m) (S.vec a)).comap (S.lin hZ)).map M.subtype

theorem mem_rootSub {hZ : blockZ J = ⊥} {a : ↥(blockU J)} {g : G} :
    g ∈ rootSub S hZ a ↔ ∃ h : g ∈ M, S.lin hZ ⟨g, h⟩ ∈ rootGroup (quadQ m) (S.vec a) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hg⟩
    exact ⟨⟨g, h⟩, hg, rfl⟩

theorem rootSub_le (hZ : blockZ J = ⊥) (a : ↥(blockU J)) : rootSub S hZ a ≤ M :=
  fun _ hg => ((mem_rootSub S).mp hg).1

theorem blockU_le_rootSub (hZ : blockZ J = ⊥) (a : ↥(blockU J)) : blockU J ≤ rootSub S hZ a := by
  intro u hu
  refine (mem_rootSub S).mpr ⟨blockU_le_M S hu, ?_⟩
  have h1 : S.lin hZ ⟨u, blockU_le_M S hu⟩ = 1 := by
    rw [S.lin_eq_one_iff hZ]
    intro w hw
    rw [Setting.blockU_comm S hu hw, mul_inv_cancel_right]
  rw [h1]
  exact (rootGroup _ _).one_mem

theorem rootSub_le_centralizer (hZ : blockZ J = ⊥) (a : ↥(blockU J)) :
    rootSub S hZ a ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
  intro g hg
  obtain ⟨h, hgR⟩ := (mem_rootSub S).mp hg
  obtain ⟨w, -, hw⟩ := mem_rootGroup.mp hgR
  have hfix : S.lin hZ ⟨g, h⟩ (S.vec a) = S.vec a := by rw [← hw, eichler_apply_self]
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (mul_inv_eq_iff_eq_mul.mp ((S.lin_vec_eq_iff hZ ⟨g, h⟩ a).mp hfix))

theorem mul_self_mem_blockU (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} {g : G}
    (hg : g ∈ rootSub S hZ a) : g * g ∈ blockU J := by
  obtain ⟨h, hgR⟩ := (mem_rootSub S).mp hg
  refine (lin_eq_one_iff_mem S hH1 hZ hC ⟨g * g, M.mul_mem h h⟩).mp ?_
  rw [show (⟨g * g, M.mul_mem h h⟩ : ↥M) = ⟨g, h⟩ * ⟨g, h⟩ from rfl, map_mul]
  exact sq_eq_one_of_mem_rootGroup (by decide) hgR

theorem commutator_mem_blockU (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} {g k : G}
    (hg : g ∈ rootSub S hZ a) (hk : k ∈ rootSub S hZ a) : g * k * g⁻¹ * k⁻¹ ∈ blockU J := by
  obtain ⟨hgM, hgR⟩ := (mem_rootSub S).mp hg
  obtain ⟨hkM, hkR⟩ := (mem_rootSub S).mp hk
  have hmem : g * k * g⁻¹ * k⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hgM hkM) (M.inv_mem hgM)) (M.inv_mem hkM)
  refine (lin_eq_one_iff_mem S hH1 hZ hC ⟨_, hmem⟩).mp ?_
  rw [show (⟨g * k * g⁻¹ * k⁻¹, hmem⟩ : ↥M) =
      ⟨g, hgM⟩ * ⟨k, hkM⟩ * (⟨g, hgM⟩ : ↥M)⁻¹ * (⟨k, hkM⟩ : ↥M)⁻¹ from rfl]
  simp only [map_mul, map_inv]
  rw [rootGroup_commute hgR hkR]
  group

theorem isPGroup_rootSub (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) (a : ↥(blockU J)) :
    IsPGroup 2 (rootSub S hZ a) := by
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  have h := S.elemU.2 _ (mul_self_mem_blockU S hH1 hZ hC g.2)
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul,
    pow_two (g : G)]
  exact h

theorem le_rootSub (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup 2 T)
    (hTa : ∀ t ∈ T, t * (a : G) * t⁻¹ = a)
    (hTn : ∀ ℓ ∈ J, ℓ * (a : G) * ℓ⁻¹ = a → ∀ t ∈ T, ℓ * t * ℓ⁻¹ ∈ T) :
    T ≤ rootSub S hZ a := by
  intro t ht
  refine (mem_rootSub S).mpr ⟨hTM ht, ?_⟩
  rw [mem_rootGroup_iff (nondegenerate_quadQ m) ha (vec_ne_zero S hZ ha1)]
  refine ⟨S.lin_mem_orthogonalGroup hZ _, (S.lin_vec_eq_iff hZ ⟨t, hTM ht⟩ a).mpr (hTa t ht),
    fun z hz => ?_⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (S.lin_sub_mem_span_of_singular hZ ha hTM hT hTa hTn ht hz)
  exact ⟨c, hc.symm⟩

theorem perpSub_dichotomy (hZ : blockZ J = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {Y : Subgroup G} (haY : (a : G) ∈ Y)
    (hYA : Y ⊓ blockU J ≤ perpSub S a)
    (hYn : ∀ ℓ ∈ J, ℓ * (a : G) * ℓ⁻¹ = a → ∀ y ∈ Y, ℓ * y * ℓ⁻¹ ∈ Y) :
    (∀ u ∈ Y ⊓ blockU J, u = 1 ∨ u = (a : G)) ∨ perpSub S a ≤ Y := by
  let X : Submodule (ZMod 2) (Vec m) :=
    { carrier := {z | ∃ u : ↥(blockU J), (u : G) ∈ Y ∧ S.vec u = z}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
        exact ⟨u * w, Y.mul_mem hu hw, S.vec_mul u w⟩
      zero_mem' := ⟨1, Y.one_mem, S.vec_one⟩
      smul_mem' := by
        rintro c _ ⟨u, hu, rfl⟩
        rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
        · exact ⟨1, Y.one_mem, by rw [S.vec_one, zero_smul]⟩
        · exact ⟨u, hu, by rw [one_smul]⟩ }
  have hX : ∀ z, z ∈ X ↔ ∃ u : ↥(blockU J), (u : G) ∈ Y ∧ S.vec u = z := fun _ => Iff.rfl
  have hLX : (ZMod 2) ∙ S.vec a ≤ X :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr ((hX _).mpr ⟨a, haY, rfl⟩)
  have hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec a) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := (hX z).mp hz
    rw [mem_orth_span_single_iff, polar_comm]
    exact (mem_perpSub_iff S u).mp (hYA ⟨hu, u.2⟩)
  have hXinv : ∀ s ∈ pointStabilizer (quadQ m) (S.vec a), ∀ x ∈ X, s.app x ∈ X := by
    intro s hs z hz
    obtain ⟨u, hu, rfl⟩ := (hX z).mp hz
    obtain ⟨ℓ, hℓa, hℓ⟩ := exists_mem_of_mem_pointStabilizer S hZ ha1 hs
    refine (hX _).mpr ⟨⟨ℓ * u * (ℓ : G)⁻¹, Setting.conj_mem_blockU S (S.le ℓ.2) u.2⟩,
      hYn ℓ ℓ.2 hℓa u hu, ?_⟩
    have hl := S.lin_vec hZ (Subgroup.inclusion S.le ℓ) u
    rw [hℓ] at hl
    exact hl.symm
  rcases eq_span_or_eq_orth (nondegenerate_quadQ m) (five_le_finrank S) ha X hLX hXP hXinv with
    h | h
  · left
    rintro g ⟨hgY, hgA⟩
    have hmem : S.vec ⟨g, hgA⟩ ∈ (ZMod 2) ∙ S.vec a := by
      rw [← h]
      exact (hX _).mpr ⟨⟨g, hgA⟩, hgY, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · left
      rw [zero_smul] at hc
      exact congrArg Subtype.val ((S.vec_eq_zero_iff hZ).mp hc.symm)
    · right
      rw [one_smul] at hc
      exact congrArg Subtype.val (S.vec_injective hZ hc.symm)
  · right
    rintro g ⟨hgA, hg0⟩
    have hmem : S.vec ⟨g, hgA⟩ ∈ X := by
      rw [h, mem_orth_span_single_iff, polar_comm]
      exact hg0
    obtain ⟨u, hu, huv⟩ := (hX _).mp hmem
    rw [S.vec_injective hZ huv] at hu
    exact hu

theorem rootSub_dichotomy (hH1 : H1Natural m) (hZ : blockZ J = ⊥)
    (hC : Subgroup.centralizer (J : Set G) = ⊥) {a : ↥(blockU J)} (ha1 : a ≠ 1)
    (ha : quadQ m (S.vec a) = 0) {Y : Subgroup G} (hYR : Y ≤ rootSub S hZ a)
    (hYn : ∀ ℓ ∈ J, ℓ * (a : G) * ℓ⁻¹ = a → ∀ y ∈ Y, ℓ * y * ℓ⁻¹ ∈ Y) :
    Y ≤ blockU J ∨
      ∀ g ∈ rootGroup (quadQ m) (S.vec a), ∃ y : ↥M, (y : G) ∈ Y ∧ S.lin hZ y = g := by
  let X : Submodule (ZMod 2) (Vec m) :=
    { carrier := {w | polar (quadQ m) (S.vec a) w = 0 ∧
        ∃ y : ↥M, (y : G) ∈ Y ∧ S.lin hZ y = eichler (quadQ m) (S.vec a) w}
      add_mem' := by
        rintro w w' ⟨hw, y, hy, hyw⟩ ⟨hw', y', hy', hyw'⟩
        refine ⟨by rw [polar_add_right, hw, hw', add_zero], y * y', Y.mul_mem hy hy', ?_⟩
        rw [map_mul, hyw, hyw', eichler_mul hw hw']
      zero_mem' := ⟨polar_zero_right _ _, 1, Y.one_mem, by rw [map_one, eichler_zero_right]⟩
      smul_mem' := by
        rintro c w ⟨hw, y, hy, hyw⟩
        rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
        · exact ⟨by rw [zero_smul, polar_zero_right], 1, Y.one_mem,
            by rw [map_one, zero_smul, eichler_zero_right]⟩
        · exact ⟨by rw [one_smul]; exact hw, y, hy, by rw [one_smul, hyw]⟩ }
  have hX : ∀ w, w ∈ X ↔ polar (quadQ m) (S.vec a) w = 0 ∧
      ∃ y : ↥M, (y : G) ∈ Y ∧ S.lin hZ y = eichler (quadQ m) (S.vec a) w := fun _ => Iff.rfl
  have heich : ∀ c : ZMod 2, eichler (quadQ m) (S.vec a) (c • S.vec a) = 1 := by
    intro c
    have := eichler_add_smul_self (Q := quadQ m) ha 0 c
    rwa [zero_add, eichler_zero_right] at this
  have hLX : (ZMod 2) ∙ S.vec a ≤ X := by
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr
      ((hX _).mpr ⟨polar_self_eq_zero ha, 1, Y.one_mem, ?_⟩)
    rw [map_one, ← heich 1, one_smul]
  have hXP : X ≤ LinearMap.BilinForm.orthogonal (polarBilin (quadQ m)) ((ZMod 2) ∙ S.vec a) :=
    fun w hw => mem_orth_span_single_iff.mpr ((hX w).mp hw).1
  have hXinv : ∀ s ∈ pointStabilizer (quadQ m) (S.vec a), ∀ x ∈ X, s.app x ∈ X := by
    intro s hs w hw
    obtain ⟨hw0, y, hy, hyw⟩ := (hX w).mp hw
    obtain ⟨ℓ, hℓa, hℓ⟩ := exists_mem_of_mem_pointStabilizer S hZ ha1 hs
    have hsv : s.app (S.vec a) = S.vec a := app_eq_of_mem_pointStabilizer (vec_ne_zero S hZ ha1) hs
    have hsO : (s : Vec m ≃ₗ[ZMod 2] Vec m) ∈ TauCeti.QuadraticMap.orthogonalGroup (quadQ m) :=
      elementaryGroup_le_orthogonalGroup _ s.2
    refine (hX _).mpr ⟨?_, Subgroup.inclusion S.le ℓ * y * (Subgroup.inclusion S.le ℓ)⁻¹,
      hYn ℓ ℓ.2 hℓa y hy, ?_⟩
    · calc polar (quadQ m) (S.vec a) (s.app w)
          = polar (quadQ m) (s.app (S.vec a)) (s.app w) := by rw [hsv]
        _ = 0 := by rw [Gom.polar_app]; exact hw0
    · rw [map_mul, map_mul, map_inv, hℓ, hyw, eichler_conj hsO]
      exact congrArg₂ (eichler (quadQ m)) hsv rfl
  rcases eq_span_or_eq_orth (nondegenerate_quadQ m) (five_le_finrank S) ha X hLX hXP hXinv with
    h | h
  · left
    intro y hy
    obtain ⟨hyM, hyR⟩ := (mem_rootSub S).mp (hYR hy)
    obtain ⟨w, hw, hwy⟩ := mem_rootGroup.mp hyR
    have hwX : w ∈ X := (hX w).mpr ⟨hw, ⟨y, hyM⟩, hy, hwy.symm⟩
    rw [h] at hwX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwX
    refine (lin_eq_one_iff_mem S hH1 hZ hC ⟨y, hyM⟩).mp ?_
    rw [← hwy, heich]
  · right
    intro g hg
    obtain ⟨w, hw, rfl⟩ := mem_rootGroup.mp hg
    have hwX : w ∈ X := by
      rw [h]
      exact mem_orth_span_single_iff.mpr hw
    obtain ⟨-, y, hy, hyw⟩ := (hX w).mp hwX
    exact ⟨y, hy, hyw⟩

end CFSG.CGT.HaradaParrott80
