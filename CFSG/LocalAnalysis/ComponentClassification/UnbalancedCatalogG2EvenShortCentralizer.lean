module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate3951

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem g2N_conj_v (A B C D E F x : K) :
    g2N A B C D E F * X g2v x * (g2N A B C D E F)⁻¹ = g2N 0 0 0 x (A * x) (C * x) := by
  rw [g2N_inv]
  simp only [CharTwo.neg_eq, ← mul_assoc]
  rw [g2N_mul_v, g2N_mul_c, g2N_mul_b, g2N_mul_v, g2N_mul_u, g2N_mul_a, g2N_mul_r]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

variable (K) in
@[expose] def g2ShortRadical : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ D E F : K, g = g2N 0 0 0 D E F}
  mul_mem' := by
    rintro _ _ ⟨D, E, F, rfl⟩ ⟨D', E', F', rfl⟩
    refine ⟨D + D', E + E', F + F', ?_⟩
    rw [g2N_zero_mul_g2N_zero]
    refine g2N_eq_g2N rfl ?_ ?_ rfl rfl ?_ <;> ring
  one_mem' := ⟨0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨D, E, F, rfl⟩
    refine ⟨D, E, F, ?_⟩
    rw [g2N_zero_inv]
    refine g2N_eq_g2N rfl rfl rfl rfl rfl ?_
    ring

theorem g2N_mem_g2ShortRadical (D E F : K) : g2N 0 0 0 D E F ∈ g2ShortRadical K :=
  ⟨D, E, F, rfl⟩

theorem g2ShortRadical_le_g2LongRadical : g2ShortRadical K ≤ g2LongRadical K := by
  rintro _ ⟨D, E, F, rfl⟩
  exact g2N_mem_g2LongRadical 0 0 D E F

theorem g2ShortRadical_isElementaryAbelian : CFSG.IsElementaryAbelian 2 (g2ShortRadical K) := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨_, D, E, F, rfl⟩ ⟨_, D', E', F', rfl⟩
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [g2N_zero_mul_g2N_zero, g2N_zero_mul_g2N_zero]
    refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> ring
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
    rintro ⟨_, D, E, F, rfl⟩
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one, sq, g2N_mul_self, ← g2N_zero]
    refine g2N_eq_g2N rfl rfl ?_ ?_ ?_ ?_ <;> char2_ring

variable (K) in
@[expose] def g2ShortParabolicRadical : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ A C D E F : K, g = g2N A 0 C D E F}
  mul_mem' := by
    rintro _ _ ⟨A, C, D, E, F, rfl⟩ ⟨A', C', D', E', F', rfl⟩
    rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]
    exact ⟨_, _, _, _, _, g2N_eq_g2N rfl (by ring) rfl rfl rfl rfl⟩
  one_mem' := ⟨0, 0, 0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨A, C, D, E, F, rfl⟩
    rw [g2N_inv]
    simp only [CharTwo.neg_eq, pinnedX_zero, mul_one]
    rw [pinnedX_c_eq_g2N, g2N_mul_b, g2N_mul_v, g2N_mul_u, g2N_mul_r]
    exact ⟨_, _, _, _, _, g2N_eq_g2N rfl (by ring) rfl rfl rfl rfl⟩

theorem g2N_mem_g2ShortParabolicRadical (A C D E F : K) :
    g2N A 0 C D E F ∈ g2ShortParabolicRadical K :=
  ⟨A, C, D, E, F, rfl⟩

theorem exists_mul_pinnedX_a_of_mem_posUnipotent {u : ModGL .G2 K}
    (hu : u ∈ posUnipotent .G2 K) :
    ∃ q ∈ g2ShortParabolicRadical K, ∃ s : K, u = q * X g2a s := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hu
  refine ⟨g2N A 0 C D E (F + B * E), g2N_mem_g2ShortParabolicRadical _ _ _ _ _, B, ?_⟩
  rw [g2N_mul_a]
  refine g2N_eq_g2N rfl (by ring) rfl rfl rfl ?_
  char2_ring

theorem exists_pinnedX_a_mul_of_mem_posUnipotent {u : ModGL .G2 K}
    (hu : u ∈ posUnipotent .G2 K) :
    ∃ s : K, ∃ q ∈ g2ShortParabolicRadical K, u = X g2a s * q := by
  obtain ⟨q, ⟨A, C, D, E, F, rfl⟩, s, rfl⟩ := exists_mul_pinnedX_a_of_mem_posUnipotent hu
  refine ⟨s, X g2a s * g2N A 0 C D E F * X g2a s, ?_, ?_⟩
  · rw [conj_a]
    exact g2N_mem_g2ShortParabolicRadical _ _ _ _ _
  · simp only [← mul_assoc, pinnedX_mul_self, one_mul]

@[expose] def g2na : Fin Tag.G2.rank → ℤ := ![-1, 0]

theorem isRoot_g2na : IsRoot .G2 g2na := by
  have h : g2na = -g2a := List.ofFn_injective (by decide +kernel)
  rw [h]
  exact IsRoot.neg isRoot_g2a

theorem reflect_a_a : reflect .G2 g2ia g2a = g2na := List.ofFn_injective (by decide +kernel)

theorem g2na_eq_neg_single : g2na = -Pi.single g2ia 1 := List.ofFn_injective (by decide +kernel)

omit [CharP K 2] in
theorem xUnit_g2ia (s : K) : xUnit .G2 K g2ia s = X g2a s := by
  rw [g2a_eq_single, pinnedX_single]

omit [CharP K 2] in
theorem yUnit_g2ia (s : K) : yUnit .G2 K g2ia s = X g2na s := by
  rw [g2na_eq_neg_single, pinnedX_neg_single]

omit [CharP K 2] in
theorem g2RankOne_a_eq :
    g2RankOne K g2ia = Subgroup.closure (Set.range (X g2a) ∪ Set.range (X g2na)) := by
  rw [g2RankOne]
  congr 2
  · exact congrArg Set.range (funext xUnit_g2ia)
  · exact congrArg Set.range (funext yUnit_g2ia)

@[expose] def ActsOnShort (l : ModGL .G2 K) (T : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) : Prop :=
  (∀ x, Commute l (X g2v x)) ∧
    (∀ q ∈ g2ShortParabolicRadical K, l * q * l⁻¹ ∈ g2ShortParabolicRadical K) ∧
    ∀ y : Fin 2 → K, l * g2N 0 0 0 0 (y 0) (y 1) * l⁻¹ = g2N 0 0 0 0 (T y 0) (T y 1)

theorem ActsOnShort.unique {l : ModGL .G2 K} {T T' : (Fin 2 → K) →ₗ[K] (Fin 2 → K)}
    (h : ActsOnShort l T) (h' : ActsOnShort l T') : T = T' := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨-, -, -, -, h0, h1⟩ := g2N_injective ((h.2.2 y).symm.trans (h'.2.2 y))
  funext i
  fin_cases i
  exacts [h0, h1]

theorem ActsOnShort.mul {l l' : ModGL .G2 K} {T T' : (Fin 2 → K) →ₗ[K] (Fin 2 → K)}
    (h : ActsOnShort l T) (h' : ActsOnShort l' T') : ActsOnShort (l * l') (T ∘ₗ T') := by
  refine ⟨fun x => (h.1 x).mul_left (h'.1 x), fun q hq => ?_, fun y => ?_⟩
  · have e : l * l' * q * (l * l')⁻¹ = l * (l' * q * l'⁻¹) * l⁻¹ := by group
    rw [e]
    exact h.2.1 _ (h'.2.1 q hq)
  · have e : l * l' * g2N 0 0 0 0 (y 0) (y 1) * (l * l')⁻¹ =
        l * (l' * g2N 0 0 0 0 (y 0) (y 1) * l'⁻¹) * l⁻¹ := by group
    rw [e, h'.2.2 y, h.2.2 (T' y)]
    rfl

theorem actsOnShort_one : ActsOnShort (1 : ModGL .G2 K) LinearMap.id :=
  ⟨fun x => Commute.one_left _, fun q hq => by simpa using hq, fun y => by simp⟩

@[expose] def shMa (s : K) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun y := ![y 0, y 1 + y 0 * s]
  map_add' x y := by
    funext i
    fin_cases i <;> first | (simp; done) | (simp; ring)
  map_smul' c x := by
    funext i
    fin_cases i <;> first | (simp; done) | (simp; ring)

@[expose] def shSwap : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun y := ![y 1, y 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' c x := by
    funext i
    fin_cases i <;> simp

@[expose] def shDiag (t : Kˣ) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun y := ![((t ^ (-1 : ℤ) : Kˣ) : K) * y 0, ((t ^ (1 : ℤ) : Kˣ) : K) * y 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

theorem actsOnShort_pinnedX_a (s : K) : ActsOnShort (X g2a s) (shMa s) := by
  refine ⟨fun x => commute_a_v s x, fun q hq => ?_, fun y => ?_⟩
  · obtain ⟨A, C, D, E, F, rfl⟩ := hq
    rw [pinnedX_inv_eq, conj_a]
    exact g2N_mem_g2ShortParabolicRadical _ _ _ _ _
  · rw [pinnedX_inv_eq, conj_a]
    refine g2N_eq_g2N rfl rfl ?_ ?_ ?_ ?_ <;> simp [shMa]

theorem weylElt_a_conj_g2N (A C D E F : K) :
    weylElt .G2 K g2ia 1 * g2N A 0 C D E F * (weylElt .G2 K g2ia 1)⁻¹ =
      g2N C 0 A D (A * C ^ 2 + F) (A ^ 2 * C + E) := by
  rw [show g2N A 0 C D E F = X g2r A * X g2u C * X g2v D * X g2b E * X g2c F by
      simp only [g2N, pinnedX_zero, mul_one],
    show weylElt .G2 K g2ia 1 * (X g2r A * X g2u C * X g2v D * X g2b E * X g2c F) *
      (weylElt .G2 K g2ia 1)⁻¹ = MulAut.conj (weylElt .G2 K g2ia 1)
        (X g2r A * X g2u C * X g2v D * X g2b E * X g2c F) from rfl]
  simp only [map_mul, MulAut.conj_apply]
  rw [weylElt_conj g2ia isRoot_g2r, weylElt_conj g2ia isRoot_g2u, weylElt_conj g2ia isRoot_g2v,
    weylElt_conj g2ia isRoot_g2b, weylElt_conj g2ia isRoot_g2c, reflect_a_r, reflect_a_u,
    reflect_a_v, reflect_a_b, reflect_a_c, pinnedX_u_eq_g2N, g2N_mul_r, g2N_mul_v, g2N_mul_c,
    g2N_mul_b]
  refine g2N_eq_g2N ?_ rfl ?_ ?_ ?_ ?_ <;> char2_ring

theorem actsOnShort_weylElt_a : ActsOnShort (weylElt .G2 K g2ia 1) shSwap := by
  refine ⟨fun x => ?_, fun q hq => ?_, fun y => ?_⟩
  · have h := weylElt_conj (K := K) g2ia isRoot_g2v x
    rw [reflect_a_v] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  · obtain ⟨A, C, D, E, F, rfl⟩ := hq
    rw [weylElt_a_conj_g2N]
    exact g2N_mem_g2ShortParabolicRadical _ _ _ _ _
  · rw [weylElt_a_conj_g2N]
    refine g2N_eq_g2N rfl rfl rfl rfl ?_ ?_ <;> simp [shSwap]

theorem pinnedX_na_eq (s : K) :
    X g2na s = weylElt .G2 K g2ia 1 * X g2a s * (weylElt .G2 K g2ia 1)⁻¹ := by
  rw [weylElt_conj g2ia isRoot_g2a, reflect_a_a]

theorem actsOnShort_pinnedX_na (s : K) :
    ActsOnShort (X g2na s) (shSwap ∘ₗ shMa s ∘ₗ shSwap) := by
  rw [pinnedX_na_eq, weylElt_inv]
  exact (actsOnShort_weylElt_a.mul (actsOnShort_pinnedX_a s)).mul actsOnShort_weylElt_a

omit [CharP K 2] in
theorem torus_a_conj (t : Kˣ) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (m : ℤ)
    (hm : ∑ j, Tag.G2.cartan g2ia j * α j = m) (x : K) :
    torusElt .G2 K g2ia t * X α x * (torusElt .G2 K g2ia t)⁻¹ = X α (((t ^ m : Kˣ) : K) * x) := by
  rw [root_torus_conjugation g2ia hα, hm]

theorem mem_g2ShortParabolicRadical_of (A C D E F : K) :
    X g2r A * X g2u C * X g2v D * X g2b E * X g2c F ∈ g2ShortParabolicRadical K :=
  ⟨A, C, D, E, F, by simp only [g2N, pinnedX_zero, mul_one]⟩

theorem actsOnShort_torusElt_a (t : Kˣ) : ActsOnShort (torusElt .G2 K g2ia t) (shDiag t) := by
  have e : ∀ a b : ModGL .G2 K, torusElt .G2 K g2ia t * (a * b) * (torusElt .G2 K g2ia t)⁻¹ =
      (torusElt .G2 K g2ia t * a * (torusElt .G2 K g2ia t)⁻¹) *
        (torusElt .G2 K g2ia t * b * (torusElt .G2 K g2ia t)⁻¹) := fun a b => by group
  refine ⟨fun x => ?_, fun q hq => ?_, fun y => ?_⟩
  · have h := torus_a_conj t isRoot_g2v 0 (by decide) x
    rw [zpow_zero, Units.val_one, one_mul] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  · obtain ⟨A, C, D, E, F, rfl⟩ := hq
    simp only [g2N, pinnedX_zero, mul_one, e]
    rw [torus_a_conj t isRoot_g2r (-1) (by decide), torus_a_conj t isRoot_g2u 1 (by decide),
      torus_a_conj t isRoot_g2v 0 (by decide), torus_a_conj t isRoot_g2b (-1) (by decide),
      torus_a_conj t isRoot_g2c 1 (by decide)]
    exact mem_g2ShortParabolicRadical_of _ _ _ _ _
  · simp only [g2N, pinnedX_zero, one_mul, e]
    rw [torus_a_conj t isRoot_g2b (-1) (by decide), torus_a_conj t isRoot_g2c 1 (by decide)]
    rfl

theorem exists_actsOnShort {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ia) :
    ∃ T, ActsOnShort l T := by
  have key : ∀ l ∈ g2RankOne K g2ia, (∃ T, ActsOnShort l T) ∧ ∃ T', ActsOnShort l⁻¹ T' := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · rw [xUnit_g2ia, pinnedX_inv_eq]
        exact ⟨⟨_, actsOnShort_pinnedX_a s⟩, ⟨_, actsOnShort_pinnedX_a s⟩⟩
      · rw [yUnit_g2ia, pinnedX_inv_eq]
        exact ⟨⟨_, actsOnShort_pinnedX_na s⟩, ⟨_, actsOnShort_pinnedX_na s⟩⟩
    | one => exact ⟨⟨_, actsOnShort_one⟩, ⟨_, by rw [inv_one]; exact actsOnShort_one⟩⟩
    | mul x y _ _ hx hy =>
      exact ⟨⟨_, hx.1.choose_spec.mul hy.1.choose_spec⟩,
        ⟨_, by rw [mul_inv_rev]; exact hy.2.choose_spec.mul hx.2.choose_spec⟩⟩
    | inv x _ hx => exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩
  exact (key l hl).1

theorem commute_of_mem_g2RankOne_a {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ia) (x : K) :
    Commute l (X g2v x) :=
  (exists_actsOnShort hl).choose_spec.1 x

theorem conj_mem_g2ShortParabolicRadical {l q : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ia)
    (hq : q ∈ g2ShortParabolicRadical K) : l * q * l⁻¹ ∈ g2ShortParabolicRadical K :=
  (exists_actsOnShort hl).choose_spec.2.1 q hq

theorem mem_g2ShortRadical_of {B C D E F : K} (hB : B = 0) (hC : C = 0) :
    g2N 0 B C D E F ∈ g2ShortRadical K :=
  ⟨D, E, F, by rw [hB, hC]⟩

theorem conj_mem_g2ShortRadical {l q : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ia)
    (hq : q ∈ g2ShortRadical K) : l * q * l⁻¹ ∈ g2ShortRadical K := by
  obtain ⟨D, E, F, rfl⟩ := hq
  obtain ⟨T, hv, -, hT⟩ := exists_actsOnShort hl
  have e : g2N 0 0 0 D E F = X g2v D * g2N 0 0 0 0 (![E, F] 0) (![E, F] 1) := by
    rw [pinnedX_v_eq_g2N, g2N_zero_mul_g2N_zero]
    refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> simp
  rw [e, show l * (X g2v D * g2N 0 0 0 0 (![E, F] 0) (![E, F] 1)) * l⁻¹ =
      (l * X g2v D * l⁻¹) * (l * g2N 0 0 0 0 (![E, F] 0) (![E, F] 1) * l⁻¹) by group,
    (hv D).eq, mul_inv_cancel_right, hT, pinnedX_v_eq_g2N, g2N_zero_mul_g2N_zero]
  exact mem_g2ShortRadical_of (by ring) (by ring)

@[expose] def shAction (l : g2RankOne K g2ia) : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
  (exists_actsOnShort l.2).choose

theorem shAction_spec (l : g2RankOne K g2ia) : ActsOnShort (l : ModGL .G2 K) (shAction l) :=
  (exists_actsOnShort l.2).choose_spec

theorem shAction_mul (l l' : g2RankOne K g2ia) :
    shAction (l * l') = shAction l ∘ₗ shAction l' :=
  (shAction_spec (l * l')).unique ((shAction_spec l).mul (shAction_spec l'))

theorem shAction_one : shAction (1 : g2RankOne K g2ia) = LinearMap.id :=
  (shAction_spec 1).unique actsOnShort_one

@[expose] def shActionHom : g2RankOne K g2ia →* LinearMap.GeneralLinearGroup K (Fin 2 → K) where
  toFun l := ⟨shAction l, shAction l⁻¹, by
      rw [Module.End.mul_eq_comp, ← shAction_mul, mul_inv_cancel, shAction_one]; rfl, by
      rw [Module.End.mul_eq_comp, ← shAction_mul, inv_mul_cancel, shAction_one]; rfl⟩
  map_one' := Units.ext shAction_one
  map_mul' l l' := Units.ext (shAction_mul l l')

theorem shActionHom_injective [Finite K] : Function.Injective (shActionHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨l, hl⟩ h1
  have hid : shAction ⟨l, hl⟩ = LinearMap.id := congrArg Units.val h1
  have hact : ActsOnShort l LinearMap.id := hid ▸ shAction_spec ⟨l, hl⟩
  obtain ⟨ρ, -, -, -, -, hrange, -, hcell0, hcell⟩ := g2_rank_one (K := K) g2ia
  rw [← hrange] at hl
  obtain ⟨g, rfl⟩ := hl
  refine Subtype.ext ?_
  show ρ g = 1
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [hcell0 g hc, xUnit_g2ia] at hact ⊢
    set a := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc)
    set b := (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0
    have he := ((actsOnShort_torusElt_a a).mul (actsOnShort_pinnedX_a b)).unique hact
    have h1 := congrArg (fun T : (Fin 2 → K) →ₗ[K] (Fin 2 → K) => T ![0, 1] 1) he
    have h0 := congrArg (fun T : (Fin 2 → K) →ₗ[K] (Fin 2 → K) => T ![1, 0] 1) he
    simp [shDiag, shMa] at h0 h1
    rw [h0, h1, torusElt_one, pinnedX_zero, mul_one]
  · exfalso
    rw [hcell g hc, xUnit_g2ia, xUnit_g2ia] at hact
    have he := ((((actsOnShort_pinnedX_a _).mul (actsOnShort_torusElt_a _)).mul
      actsOnShort_weylElt_a).mul (actsOnShort_pinnedX_a _)).unique hact
    have h0 := congrArg (fun T : (Fin 2 → K) →ₗ[K] (Fin 2 → K) => T ![0, 1] 0) he
    simp [shDiag, shMa, shSwap] at h0
    exact hc h0

theorem g2nr_eq_neg : g2nr = -g2r := List.ofFn_injective (by decide +kernel)

omit [CharP K 2] in
theorem g2N_mem_borelGroup (A B C D E F : K) : g2N A B C D E F ∈ borelGroup .G2 K :=
  posUnipotent_le_borelGroup (g2N_mem_posUnipotent A B C D E F)

omit [CharP K 2] in
theorem pinnedX_mem_borelGroup {γ : Fin Tag.G2.rank → ℤ} (hγ : γ = g2r ∨ γ = g2a ∨ γ = g2u ∨
    γ = g2v ∨ γ = g2b ∨ γ = g2c) (x : K) : X γ x ∈ borelGroup .G2 K := by
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pinnedX_r_eq_g2N]; exact g2N_mem_borelGroup _ _ _ _ _ _
  · rw [pinnedX_a_eq_g2N]; exact g2N_mem_borelGroup _ _ _ _ _ _
  · rw [pinnedX_u_eq_g2N]; exact g2N_mem_borelGroup _ _ _ _ _ _
  · rw [pinnedX_v_eq_g2N]; exact g2N_mem_borelGroup _ _ _ _ _ _
  · rw [pinnedX_b_eq_g2N]; exact g2N_mem_borelGroup _ _ _ _ _ _
  · rw [pinnedX_c_eq_g2N]; exact g2N_mem_borelGroup _ _ _ _ _ _

theorem longest_conj_neg_mul {γ δ : Fin Tag.G2.rank → ℤ} (hγ : γ = g2r ∨ γ = g2a ∨ γ = g2u ∨
    γ = g2v ∨ γ = g2b ∨ γ = g2c) (hδ : δ = g2r ∨ δ = g2a ∨ δ = g2u ∨ δ = g2v ∨ δ = g2b ∨
    δ = g2c) (x y : K) (h : X (-γ) x * X (-δ) y = 1) : X γ x * X δ y = 1 := by
  rw [← longest_conj_neg hγ, ← longest_conj_neg hδ]
  calc canonicalRep (coxeterSystem .G2) K g2LongestWeyl * X (-γ) x *
        (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹ *
      (canonicalRep (coxeterSystem .G2) K g2LongestWeyl * X (-δ) y *
        (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹) =
      canonicalRep (coxeterSystem .G2) K g2LongestWeyl * (X (-γ) x * X (-δ) y) *
        (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem longest_conj_neg_mul_mul {γ δ ε : Fin Tag.G2.rank → ℤ} (hγ : γ = g2r ∨ γ = g2a ∨
    γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c) (hδ : δ = g2r ∨ δ = g2a ∨ δ = g2u ∨ δ = g2v ∨
    δ = g2b ∨ δ = g2c) (hε : ε = g2r ∨ ε = g2a ∨ ε = g2u ∨ ε = g2v ∨ ε = g2b ∨ ε = g2c)
    (x y z : K) (h : X (-γ) x * X (-δ) y * X (-ε) z = 1) : X γ x * X δ y * X ε z = 1 := by
  rw [← longest_conj_neg hγ, ← longest_conj_neg hδ, ← longest_conj_neg hε]
  calc canonicalRep (coxeterSystem .G2) K g2LongestWeyl * X (-γ) x *
        (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹ *
      (canonicalRep (coxeterSystem .G2) K g2LongestWeyl * X (-δ) y *
        (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹) *
      (canonicalRep (coxeterSystem .G2) K g2LongestWeyl * X (-ε) z *
        (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹) =
      canonicalRep (coxeterSystem .G2) K g2LongestWeyl * (X (-γ) x * X (-δ) y * X (-ε) z) *
        (canonicalRep (coxeterSystem .G2) K g2LongestWeyl)⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem weyl_eq_of_triple {w : WeylGroup .G2} {l b c m b' c' : K} (hl : l ≠ 0)
    (h : X (w • g2v) l * X (w • g2b) b * X (w • g2c) c = g2N 0 0 0 m b' c') :
    w = 1 ∨ w = simple .G2 g2ia := by
  have hR := g2N_mem_borelGroup (0 : K) 0 0 m b' c'
  have hneg := fun {γ : Fin Tag.G2.rank → ℤ} (hγ : γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨
      γ = g2b ∨ γ = g2c) (x : K) => pinnedX_neg_mem_negUnipotent (K := K) hγ x
  have hzero : ∀ {γ : Fin Tag.G2.rank → ℤ} {x : K}, X γ x = 1 → x = 0 := fun {γ x} hx =>
    pinnedX_injective .G2 K γ (hx.trans (pinnedX_zero .G2 K γ).symm)
  have hcoord : ∀ {A B C D E F : K}, g2N A B C D E F = g2N 0 0 0 m b' c' → A = 0 ∧ C = 0 :=
    fun {A B C D E F} he => ⟨(g2N_injective he).1, (g2N_injective he).2.2.1⟩
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [smul_g2v, smul_g2b, smul_g2c, ha, hr] at h
  · exact Or.inl (eq_one_of_smul ha hr)
  · exact Or.inr (eq_simple_a_of_smul ha hr)
  ·
    rw [show g2b + (-g2r + -g2r) = g2u from List.ofFn_injective (by decide +kernel),
      show g2b + (-g2r + -g2r + -g2r) = g2a from List.ofFn_injective (by decide +kernel),
      show g2b + g2b + (-g2r + -g2r + -g2r) = g2c from List.ofFn_injective (by decide +kernel),
      ← (commute_a_u b l).eq] at h
    have e : X g2a b * X g2u l * X g2c c = g2N 0 b l 0 0 c := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    exact absurd (hcoord (e.symm.trans h)).2 hl
  ·
    rw [show g2c + (-g2u + -g2u) = g2r from List.ofFn_injective (by decide +kernel),
      show g2c + (-g2u + -g2u + -g2u) = -g2a from List.ofFn_injective (by decide +kernel),
      show g2c + g2c + (-g2u + -g2u + -g2u) = g2b from
        List.ofFn_injective (by decide +kernel)] at h
    have h1 : X (-g2a) b = 1 := by
      refine eq_one_of_mem_borel_of_mem_neg ?_ (hneg (Or.inr (Or.inl rfl)) b)
      have e : X (-g2a) b = (X g2r l)⁻¹ * g2N 0 0 0 m b' c' * (X g2b c)⁻¹ := by
        rw [← h]; group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (pinnedX_mem_borelGroup (Or.inl rfl) l)) hR)
        (inv_mem (pinnedX_mem_borelGroup (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) c))
    rw [h1, mul_one] at h
    have e : X g2r l * X g2b c = g2N l 0 0 0 c 0 := by
      simp only [g2N, pinnedX_zero, mul_one]
    exact absurd (hcoord (e.symm.trans h)).1 hl
  ·
    rw [show -g2b + (g2v + g2v) = g2u from List.ofFn_injective (by decide +kernel),
      show -g2b + (g2v + g2v + g2v) = g2c from List.ofFn_injective (by decide +kernel),
      show -g2b + -g2b + (g2v + g2v + g2v) = g2a from List.ofFn_injective (by decide +kernel),
      mul_assoc, ← (commute_a_c c b).eq, ← mul_assoc, ← (commute_a_u c l).eq] at h
    have e : X g2a c * X g2u l * X g2c b = g2N 0 c l 0 0 b := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    exact absurd (hcoord (e.symm.trans h)).2 hl
  ·
    rw [show -g2c + (g2v + g2v) = g2r from List.ofFn_injective (by decide +kernel),
      show -g2c + (g2v + g2v + g2v) = g2b from List.ofFn_injective (by decide +kernel),
      show -g2c + -g2c + (g2v + g2v + g2v) = -g2a from
        List.ofFn_injective (by decide +kernel)] at h
    have h1 : X (-g2a) c = 1 := by
      refine eq_one_of_mem_borel_of_mem_neg ?_ (hneg (Or.inr (Or.inl rfl)) c)
      have e : X (-g2a) c = (X g2r l * X g2b b)⁻¹ * g2N 0 0 0 m b' c' := by
        rw [← h]; group
      rw [e]
      exact mul_mem (inv_mem (mul_mem (pinnedX_mem_borelGroup (Or.inl rfl) l)
        (pinnedX_mem_borelGroup (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) b))) hR
    rw [h1, mul_one] at h
    have e : X g2r l * X g2b b = g2N l 0 0 0 b 0 := by
      simp only [g2N, pinnedX_zero, mul_one]
    exact absurd (hcoord (e.symm.trans h)).1 hl
  ·
    rw [show g2c + (-g2v + -g2v) = -g2r from List.ofFn_injective (by decide +kernel),
      show g2c + (-g2v + -g2v + -g2v) = -g2b from List.ofFn_injective (by decide +kernel),
      show g2c + g2c + (-g2v + -g2v + -g2v) = g2a from
        List.ofFn_injective (by decide +kernel)] at h
    have h1 : X (-g2r) l * X (-g2b) b = 1 := by
      refine eq_one_of_mem_borel_of_mem_neg ?_ (mul_mem (hneg (Or.inl rfl) l)
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) b))
      have e : X (-g2r) l * X (-g2b) b = g2N 0 0 0 m b' c' * (X g2a c)⁻¹ := by
        rw [← h]; group
      rw [e]
      exact mul_mem hR (inv_mem (pinnedX_mem_borelGroup (Or.inr (Or.inl rfl)) c))
    have h2 := longest_conj_neg_mul (Or.inl rfl) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      l b h1
    have e : X g2r l * X g2b b = g2N l 0 0 0 b 0 := by
      simp only [g2N, pinnedX_zero, mul_one]
    rw [e, ← g2N_zero] at h2
    exact absurd (g2N_injective h2).1 hl
  ·
    rw [show -g2c + (g2u + g2u) = -g2r from List.ofFn_injective (by decide +kernel),
      show -g2c + (g2u + g2u + g2u) = g2a from List.ofFn_injective (by decide +kernel),
      show -g2c + -g2c + (g2u + g2u + g2u) = -g2b from
        List.ofFn_injective (by decide +kernel)] at h
    have hc : Commute (X g2a b) (X (-g2r) l) := by
      rw [← g2nr_eq_neg]; exact commute_a_nr b l
    rw [← hc.eq] at h
    have h1 : X (-g2r) l * X (-g2b) c = 1 := by
      refine eq_one_of_mem_borel_of_mem_neg ?_ (mul_mem (hneg (Or.inl rfl) l)
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) c))
      have e : X (-g2r) l * X (-g2b) c = (X g2a b)⁻¹ * g2N 0 0 0 m b' c' := by
        rw [← h]; group
      rw [e]
      exact mul_mem (inv_mem (pinnedX_mem_borelGroup (Or.inr (Or.inl rfl)) b)) hR
    have h2 := longest_conj_neg_mul (Or.inl rfl) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      l c h1
    have e : X g2r l * X g2b c = g2N l 0 0 0 c 0 := by
      simp only [g2N, pinnedX_zero, mul_one]
    rw [e, ← g2N_zero] at h2
    exact absurd (g2N_injective h2).1 hl
  ·
    rw [show g2b + (-g2v + -g2v) = -g2u from List.ofFn_injective (by decide +kernel),
      show g2b + (-g2v + -g2v + -g2v) = -g2c from List.ofFn_injective (by decide +kernel),
      show g2b + g2b + (-g2v + -g2v + -g2v) = -g2a from
        List.ofFn_injective (by decide +kernel)] at h
    have h1 : X (-g2u) l * X (-g2c) b * X (-g2a) c = 1 :=
      eq_one_of_mem_borel_of_mem_neg (h ▸ hR) (mul_mem (mul_mem
        (hneg (Or.inr (Or.inr (Or.inl rfl))) l)
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) b))
        (hneg (Or.inr (Or.inl rfl)) c))
    have h2 := longest_conj_neg_mul_mul (Or.inr (Or.inr (Or.inl rfl)))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (Or.inr (Or.inl rfl)) l b c h1
    rw [mul_assoc, ← (commute_a_c c b).eq, ← mul_assoc, ← (commute_a_u c l).eq] at h2
    have e : X g2a c * X g2u l * X g2c b = g2N 0 c l 0 0 b := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    rw [e, ← g2N_zero] at h2
    exact absurd (g2N_injective h2).2.2.1 hl
  ·
    rw [show -g2b + (g2r + g2r) = -g2u from List.ofFn_injective (by decide +kernel),
      show -g2b + (g2r + g2r + g2r) = -g2a from List.ofFn_injective (by decide +kernel),
      show -g2b + -g2b + (g2r + g2r + g2r) = -g2c from
        List.ofFn_injective (by decide +kernel)] at h
    have h1 : X (-g2u) l * X (-g2a) b * X (-g2c) c = 1 :=
      eq_one_of_mem_borel_of_mem_neg (h ▸ hR) (mul_mem (mul_mem
        (hneg (Or.inr (Or.inr (Or.inl rfl))) l) (hneg (Or.inr (Or.inl rfl)) b))
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) c))
    have h2 := longest_conj_neg_mul_mul (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) l b c h1
    rw [← (commute_a_u b l).eq] at h2
    have e : X g2a b * X g2u l * X g2c c = g2N 0 b l 0 0 c := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    rw [e, ← g2N_zero] at h2
    exact absurd (g2N_injective h2).2.2.1 hl
  ·
    rw [show g2a + (-g2u + -g2u) = -g2v from List.ofFn_injective (by decide +kernel),
      show g2a + (-g2u + -g2u + -g2u) = -g2c from List.ofFn_injective (by decide +kernel),
      show g2a + g2a + (-g2u + -g2u + -g2u) = -g2b from
        List.ofFn_injective (by decide +kernel)] at h
    have h1 : X (-g2v) l * X (-g2c) b * X (-g2b) c = 1 :=
      eq_one_of_mem_borel_of_mem_neg (h ▸ hR) (mul_mem (mul_mem
        (hneg (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) l)
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) b))
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) c))
    have h2 := longest_conj_neg_mul_mul (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) l b c h1
    rw [mul_assoc, ← (commute_b_c c b).eq, ← mul_assoc] at h2
    have e : X g2v l * X g2b c * X g2c b = g2N 0 0 0 l c b := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    rw [e, ← g2N_zero] at h2
    exact absurd (g2N_injective h2).2.2.2.1 hl
  ·
    rw [show -g2a + (-g2r + -g2r) = -g2v from List.ofFn_injective (by decide +kernel),
      show -g2a + (-g2r + -g2r + -g2r) = -g2b from List.ofFn_injective (by decide +kernel),
      show -g2a + -g2a + (-g2r + -g2r + -g2r) = -g2c from
        List.ofFn_injective (by decide +kernel)] at h
    have h1 : X (-g2v) l * X (-g2b) b * X (-g2c) c = 1 :=
      eq_one_of_mem_borel_of_mem_neg (h ▸ hR) (mul_mem (mul_mem
        (hneg (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) l)
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) b))
        (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) c))
    have h2 := longest_conj_neg_mul_mul (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) l b c h1
    have e : X g2v l * X g2b b * X g2c c = g2N 0 0 0 l b c := by
      simp only [g2N, pinnedX_zero, one_mul, mul_one]
    rw [e, ← g2N_zero] at h2
    exact absurd (g2N_injective h2).2.2.2.1 hl

omit [CharP K 2] in
theorem exists_torus_scale_vbc {h : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K) :
    ∃ cv cb cc : Kˣ, ∀ x y z : K,
      h * g2N 0 0 0 x y z * h⁻¹ = g2N 0 0 0 (cv * x) (cb * y) (cc * z) := by
  obtain ⟨cv, hv⟩ := exists_torus_scale hh isRoot_g2v
  obtain ⟨cb, hb⟩ := exists_torus_scale hh isRoot_g2b
  obtain ⟨cc, hc⟩ := exists_torus_scale hh isRoot_g2c
  refine ⟨cv, cb, cc, fun x y z => ?_⟩
  have e : ∀ x y z : K, g2N 0 0 0 x y z = X g2v x * X g2b y * X g2c z := fun x y z => by
    simp only [g2N, pinnedX_zero, one_mul]
  rw [e, e, show h * (X g2v x * X g2b y * X g2c z) * h⁻¹ =
    (h * X g2v x * h⁻¹) * (h * X g2b y * h⁻¹) * (h * X g2c z * h⁻¹) by group, hv, hb, hc]

theorem torus_r_conj_mem_g2ShortParabolicRadical (t : Kˣ) {q : ModGL .G2 K}
    (hq : q ∈ g2ShortParabolicRadical K) :
    torusElt .G2 K g2ir t * q * (torusElt .G2 K g2ir t)⁻¹ ∈ g2ShortParabolicRadical K := by
  obtain ⟨A, C, D, E, F, rfl⟩ := hq
  have e : ∀ a b : ModGL .G2 K, torusElt .G2 K g2ir t * (a * b) * (torusElt .G2 K g2ir t)⁻¹ =
      (torusElt .G2 K g2ir t * a * (torusElt .G2 K g2ir t)⁻¹) *
        (torusElt .G2 K g2ir t * b * (torusElt .G2 K g2ir t)⁻¹) := fun a b => by group
  simp only [g2N, pinnedX_zero, mul_one, e]
  rw [torus_r_conj t isRoot_g2r 2 (by decide), torus_r_conj t isRoot_g2u (-1) (by decide),
    torus_r_conj t isRoot_g2v 1 (by decide), torus_r_conj t isRoot_g2b 3 (by decide),
    torus_r_conj t isRoot_g2c 0 (by decide)]
  exact mem_g2ShortParabolicRadical_of _ _ _ _ _

omit [CharP K 2] in
theorem torus_conj_mem_g2RankOne_a {h l : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K)
    (hl : l ∈ g2RankOne K g2ia) : h * l * h⁻¹ ∈ g2RankOne K g2ia := by
  have key : g2RankOne K g2ia ≤ (g2RankOne K g2ia).comap (MulAut.conj h).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · obtain ⟨c, hc⟩ := exists_torus_scale hh isRoot_g2a
      show h * xUnit .G2 K g2ia s * h⁻¹ ∈ g2RankOne K g2ia
      rw [xUnit_g2ia, hc, ← xUnit_g2ia]
      exact xUnit_mem_g2RankOne g2ia _
    · obtain ⟨c, hc⟩ := exists_torus_scale hh isRoot_g2na
      show h * yUnit .G2 K g2ia s * h⁻¹ ∈ g2RankOne K g2ia
      rw [yUnit_g2ia, hc, ← yUnit_g2ia]
      exact yUnit_mem_g2RankOne g2ia _
  exact key hl

theorem exists_mem_mul_of_commute_v {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K)
    (hgt : g * X g2v 1 = X g2v 1 * g) :
    ∃ q ∈ g2ShortRadical K, ∃ l ∈ g2RankOne K g2ia, g = q * l := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_bruhat hg
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := exists_torus_mul_of_mem_borel hb₁
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := exists_torus_mul_of_mem_borel hb₂
  set n := canonicalRep (coxeterSystem .G2) K w with hn
  have hgt' : h₁ * u₁ * n * (h₂ * u₂) * X g2v 1 * (h₁ * u₁ * n * (h₂ * u₂))⁻¹ = X g2v 1 := by
    rw [hgt, mul_inv_cancel_right]
  obtain ⟨A₂, B₂, C₂, D₂, E₂, F₂, hu₂e⟩ := exists_g2N_of_mem_posUnipotent hu₂
  obtain ⟨cv, cb, cc, hc⟩ := exists_torus_scale_vbc hh₂
  have hconj₂ : h₂ * u₂ * X g2v 1 * (h₂ * u₂)⁻¹ =
      g2N 0 0 0 ((cv : K) * 1) ((cb : K) * (A₂ * 1)) ((cc : K) * (C₂ * 1)) := by
    rw [← hc, ← g2N_conj_v A₂ B₂ C₂ D₂ E₂ F₂ 1, hu₂e]
    group
  obtain ⟨A₁, B₁, C₁, D₁, E₁, F₁, hu₁e⟩ := exists_g2N_of_mem_posUnipotent (inv_mem hu₁)
  obtain ⟨cv', hcv'⟩ := exists_torus_scale (inv_mem hh₁) isRoot_g2v
  have hconj₁ : (h₁ * u₁)⁻¹ * X g2v 1 * (h₁ * u₁) =
      g2N 0 0 0 ((cv' : K) * 1) (A₁ * ((cv' : K) * 1)) (C₁ * ((cv' : K) * 1)) := by
    rw [← g2N_conj_v A₁ B₁ C₁ D₁ E₁ F₁, hu₁e, ← hcv', inv_inv]
    group
  have hW : X (w • g2v) ((cv : K) * 1) * X (w • g2b) ((cb : K) * (A₂ * 1)) *
      X (w • g2c) ((cc : K) * (C₂ * 1)) =
        g2N 0 0 0 ((cv' : K) * 1) (A₁ * ((cv' : K) * 1)) (C₁ * ((cv' : K) * 1)) := by
    rw [← canonicalRep_conj w isRoot_g2v, ← canonicalRep_conj w isRoot_g2b,
      ← canonicalRep_conj w isRoot_g2c, ← hn, ← hconj₁]
    have e : g2N 0 0 0 ((cv : K) * 1) ((cb : K) * (A₂ * 1)) ((cc : K) * (C₂ * 1)) =
        X g2v ((cv : K) * 1) * X g2b ((cb : K) * (A₂ * 1)) * X g2c ((cc : K) * (C₂ * 1)) := by
      simp only [g2N, pinnedX_zero, one_mul]
    calc n * X g2v ((cv : K) * 1) * n⁻¹ * (n * X g2b ((cb : K) * (A₂ * 1)) * n⁻¹) *
          (n * X g2c ((cc : K) * (C₂ * 1)) * n⁻¹) =
        n * (X g2v ((cv : K) * 1) * X g2b ((cb : K) * (A₂ * 1)) *
          X g2c ((cc : K) * (C₂ * 1))) * n⁻¹ := by group
      _ = n * (h₂ * u₂ * X g2v 1 * (h₂ * u₂)⁻¹) * n⁻¹ := by rw [← e, hconj₂]
      _ = (h₁ * u₁)⁻¹ * (h₁ * u₁ * n * (h₂ * u₂) * X g2v 1 *
            (h₁ * u₁ * n * (h₂ * u₂))⁻¹) * (h₁ * u₁) := by group
      _ = (h₁ * u₁)⁻¹ * X g2v 1 * (h₁ * u₁) := by rw [hgt']
  have hnL : n ∈ g2RankOne K g2ia := by
    rcases weyl_eq_of_triple (by simp) hW with rfl | rfl
    · rw [hn, canonicalRep_one]
      exact one_mem _
    · rw [hn, canonicalRep_simple]
      exact weylElt_mem_g2RankOne g2ia 1
  have hl₁ : h₁ * n * h₁⁻¹ ∈ g2RankOne K g2ia := torus_conj_mem_g2RankOne_a hh₁ hnL
  obtain ⟨t₁, t₂, hh⟩ := exists_eq_torusElt_mul (mul_mem hh₁ hh₂)
  obtain ⟨q₁, hq₁, s₁, hu₁'⟩ :=
    exists_mul_pinnedX_a_of_mem_posUnipotent (torus_conj_mem_posUnipotent hh₁ hu₁)
  obtain ⟨s₂, q₂, hq₂, rfl⟩ := exists_pinnedX_a_mul_of_mem_posUnipotent hu₂
  have hu₁e : u₁ = h₁⁻¹ * (q₁ * X g2a s₁) * h₁ := by rw [← hu₁']; group
  subst hu₁e
  set d₁ := torusElt .G2 K g2ia t₁
  set d₂ := torusElt .G2 K g2ir t₂
  have hs₃ := torus_r_conj t₂ isRoot_g2a (-3) (by decide) s₂
  set s₃ := ((t₂ ^ (-3 : ℤ) : Kˣ) : K) * s₂
  have hq₂' : d₂ * q₂ * d₂⁻¹ ∈ g2ShortParabolicRadical K :=
    torus_r_conj_mem_g2ShortParabolicRadical t₂ hq₂
  have haL : ∀ s : K, X g2a s ∈ g2RankOne K g2ia := fun s => by
    rw [← xUnit_g2ia]; exact xUnit_mem_g2RankOne g2ia s
  set l₂ := X g2a s₁ * (h₁ * n * h₁⁻¹) * d₁ * X g2a s₃ with hl₂
  have hl₂L : l₂ ∈ g2RankOne K g2ia :=
    mul_mem (mul_mem (mul_mem (haL s₁) hl₁) (torusElt_mem_g2RankOne g2ia t₁)) (haL s₃)
  set q := q₁ * (l₂ * (d₂ * q₂ * d₂⁻¹) * l₂⁻¹) with hq
  have hqQ : q ∈ g2ShortParabolicRadical K :=
    mul_mem hq₁ (conj_mem_g2ShortParabolicRadical hl₂L hq₂')
  have hg : h₁ * (h₁⁻¹ * (q₁ * X g2a s₁) * h₁) * n * (h₂ * (X g2a s₂ * q₂)) = q * l₂ * d₂ := by
    calc h₁ * (h₁⁻¹ * (q₁ * X g2a s₁) * h₁) * n * (h₂ * (X g2a s₂ * q₂)) =
        q₁ * X g2a s₁ * (h₁ * n * h₁⁻¹) * (h₁ * h₂) * X g2a s₂ * q₂ := by group
      _ = q₁ * X g2a s₁ * (h₁ * n * h₁⁻¹) * d₁ * (d₂ * X g2a s₂ * d₂⁻¹) *
          (d₂ * q₂ * d₂⁻¹) * d₂ := by rw [hh]; group
      _ = q * l₂ * d₂ := by rw [hs₃, hq, hl₂]; group
  rw [hg] at hgt'
  obtain ⟨A, C, D, E, F, hqe⟩ := hqQ
  have ht : X g2v 1 = g2N 0 0 0 ((t₂ : K) * 1) (A * ((t₂ : K) * 1)) (C * ((t₂ : K) * 1)) := by
    rw [← hgt', ← g2N_conj_v A 0 C D E F, ← hqe, ← torus_r_v t₂ 1]
    rw [show q * l₂ * d₂ * X g2v 1 * (q * l₂ * d₂)⁻¹ =
      q * (l₂ * (d₂ * X g2v 1 * d₂⁻¹) * l₂⁻¹) * q⁻¹ by group]
    rw [torus_r_v t₂ 1, (commute_of_mem_g2RankOne_a hl₂L _).eq, mul_inv_cancel_right]
  rw [pinnedX_v_eq_g2N] at ht
  obtain ⟨-, -, -, h1, hA, hC⟩ := g2N_injective ht
  have ht₂ : (t₂ : K) = 1 := by simpa using h1.symm
  rw [ht₂, mul_one, mul_one] at hA hC
  have hd₂ : d₂ = 1 := by
    show torusElt .G2 K g2ir t₂ = 1
    rw [show t₂ = 1 from Units.ext ht₂, torusElt_one]
  refine ⟨q, ?_, l₂, hl₂L, by rw [hg, hd₂, mul_one]⟩
  rw [hqe, ← hA, ← hC]
  exact g2N_mem_g2ShortRadical D E F

theorem g2ShortRadical_le_g2ShortParabolicRadical :
    g2ShortRadical K ≤ g2ShortParabolicRadical K := by
  rintro _ ⟨D, E, F, rfl⟩
  exact g2N_mem_g2ShortParabolicRadical 0 0 D E F

theorem commute_of_mem_g2ShortRadical {g g' : ModGL .G2 K} (hg : g ∈ g2ShortRadical K)
    (hg' : g' ∈ g2ShortRadical K) : Commute g g' :=
  congrArg Subtype.val
    ((g2ShortRadical_isElementaryAbelian (K := K)).toIsMulCommutative.is_comm.comm
      ⟨g, hg⟩ ⟨g', hg'⟩)

theorem pinnedX_v_mem_g2ShortRadical (x : K) : X g2v x ∈ g2ShortRadical K :=
  ⟨x, 0, 0, pinnedX_v_eq_g2N x⟩

theorem g2ShortRadical_inf_g2RankOne [Finite K] : g2ShortRadical K ⊓ g2RankOne K g2ia = ⊥ := by
  refine eq_bot_iff.2 fun l hl => ?_
  obtain ⟨hlA, hlL⟩ := Subgroup.mem_inf.1 hl
  have hact : ActsOnShort l LinearMap.id := by
    refine ⟨fun x => commute_of_mem_g2ShortRadical hlA (pinnedX_v_mem_g2ShortRadical x),
      fun q hq => mul_mem (mul_mem (g2ShortRadical_le_g2ShortParabolicRadical hlA) hq)
        (inv_mem (g2ShortRadical_le_g2ShortParabolicRadical hlA)), fun y => ?_⟩
    rw [(commute_of_mem_g2ShortRadical hlA (g2N_mem_g2ShortRadical 0 (y 0) (y 1))).eq,
      mul_inv_cancel_right]
    rfl
  have h1 : shAction ⟨l, hlL⟩ = LinearMap.id := (shAction_spec ⟨l, hlL⟩).unique hact
  have h2 : shActionHom ⟨l, hlL⟩ = 1 := Units.ext h1
  rw [← map_one shActionHom] at h2
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (shActionHom_injective h2))

theorem g2RankOne_a_le_normalizer :
    g2RankOne K g2ia ≤ Subgroup.normalizer (g2ShortRadical K : Set (ModGL .G2 K)) := by
  intro l hl
  refine Subgroup.mem_normalizer_iff.2 fun q => ⟨fun hq => conj_mem_g2ShortRadical hl hq,
    fun hq => ?_⟩
  have h := conj_mem_g2ShortRadical (inv_mem hl) hq
  rwa [inv_inv, show l⁻¹ * (l * q * l⁻¹) * l = q by group] at h

@[expose] def g2ShortCoordHom : Multiplicative (Fin 2 → K) →* ModGL .G2 K where
  toFun x := g2N 0 0 0 0 (x.toAdd 0) (x.toAdd 1)
  map_one' := g2N_zero
  map_mul' x y := by
    rw [g2N_zero_mul_g2N_zero]
    refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> simp

theorem g2ShortCoordHom_injective : Function.Injective (g2ShortCoordHom (K := K)) := by
  intro x y h
  obtain ⟨-, -, -, -, h0, h1⟩ := g2N_injective h
  refine Multiplicative.toAdd.injective ?_
  funext i
  fin_cases i
  exacts [h0, h1]

theorem even_G2_highest_short_root_centralizer (K : Type) [Field K] [Finite K] [CharP K 2] :
    g2RankOne K g2ia =
        Subgroup.closure (Set.range (pinnedX .G2 K g2a) ∪ Set.range (pinnedX .G2 K g2na)) ∧
      g2ShortRadical K ≤ adjointGroup .G2 K ∧ CFSG.IsElementaryAbelian 2 (g2ShortRadical K) ∧
      adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} =
        g2ShortRadical K ⊔ g2RankOne K g2ia ∧
      ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1} :
          Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) =
        (g2ShortRadical K : Set (ModGL .G2 K)) * (g2RankOne K g2ia : Set (ModGL .G2 K)) ∧
      g2RankOne K g2ia ≤ Subgroup.normalizer (g2ShortRadical K : Set (ModGL .G2 K)) ∧
      g2ShortRadical K ⊓ g2RankOne K g2ia = ⊥ ∧
      (∃ ρ : SL2 K →* ModGL .G2 K, (∀ s, ρ (uSL s) = pinnedX .G2 K g2a s) ∧
        (∀ s, ρ (vSL s) = pinnedX .G2 K g2na s) ∧ ρ.range = g2RankOne K g2ia ∧
        Function.Injective ρ) ∧
      (∀ l ∈ g2RankOne K g2ia, ∀ x : K, Commute l (pinnedX .G2 K g2v x)) ∧
      ∃ θ : Multiplicative (Fin 2 → K) →* ModGL .G2 K, Function.Injective θ ∧
        (∀ y : Fin 2 → K, θ (Multiplicative.ofAdd y) =
          pinnedX .G2 K g2b (y 0) * pinnedX .G2 K g2c (y 1)) ∧
        ∃ ψ : g2RankOne K g2ia →* LinearMap.GeneralLinearGroup K (Fin 2 → K),
          Function.Injective ψ ∧ ∀ (l : g2RankOne K g2ia) (y : Fin 2 → K),
            (l : ModGL .G2 K) * θ (Multiplicative.ofAdd y) * (l : ModGL .G2 K)⁻¹ =
              θ (Multiplicative.ofAdd ((ψ l : (Fin 2 → K) →ₗ[K] (Fin 2 → K)) y)) := by
  have hAC : g2ShortRadical K ≤ adjointGroup .G2 K ⊓
      Subgroup.centralizer {pinnedX .G2 K g2v 1} := fun q hq =>
    Subgroup.mem_inf.2 ⟨g2LongRadical_le_adjointGroup (g2ShortRadical_le_g2LongRadical hq),
      Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (commute_of_mem_g2ShortRadical (pinnedX_v_mem_g2ShortRadical 1) hq).eq⟩
  have hLC : g2RankOne K g2ia ≤ adjointGroup .G2 K ⊓
      Subgroup.centralizer {pinnedX .G2 K g2v 1} := fun l hl =>
    Subgroup.mem_inf.2 ⟨g2RankOne_le_adjointGroup g2ia hl, Subgroup.mem_centralizer_iff.2
      fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (commute_of_mem_g2RankOne_a hl 1).eq.symm⟩
  have hsub : ∀ g ∈ adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2v 1},
      ∃ q ∈ g2ShortRadical K, ∃ l ∈ g2RankOne K g2ia, g = q * l := fun g hg => by
    obtain ⟨hgC, hgt⟩ := Subgroup.mem_inf.1 hg
    exact exists_mem_mul_of_commute_v hgC
      ((Subgroup.mem_centralizer_iff.1 hgt _ (Set.mem_singleton _)).symm)
  obtain ⟨ρ, hu, hv, -, -, hrange, hinj, -, -⟩ := g2_rank_one (K := K) g2ia
  refine ⟨g2RankOne_a_eq, fun q hq => (hAC hq).1, g2ShortRadical_isElementaryAbelian,
    le_antisymm (fun g hg => ?_) (sup_le hAC hLC), Set.Subset.antisymm (fun g hg => ?_) ?_,
    g2RankOne_a_le_normalizer, g2ShortRadical_inf_g2RankOne,
    ⟨ρ, fun s => by rw [hu, xUnit_g2ia], fun s => by rw [hv, yUnit_g2ia], hrange, hinj⟩,
    fun l hl x => commute_of_mem_g2RankOne_a hl x,
    ⟨g2ShortCoordHom, g2ShortCoordHom_injective, fun y => ?_, shActionHom,
      shActionHom_injective, fun l y => (shAction_spec l).2.2 y⟩⟩
  · obtain ⟨q, hq, l, hl, rfl⟩ := hsub g hg
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hl)
  · obtain ⟨q, hq, l, hl, rfl⟩ := hsub g hg
    exact Set.mul_mem_mul hq hl
  · rintro _ ⟨q, hq, l, hl, rfl⟩
    exact mul_mem (hAC hq) (hLC hl)
  · show g2N 0 0 0 0 (y 0) (y 1) = _
    simp only [g2N, pinnedX_zero, one_mul]

end CFSG.ComponentClassification.UnbalancedCatalog
