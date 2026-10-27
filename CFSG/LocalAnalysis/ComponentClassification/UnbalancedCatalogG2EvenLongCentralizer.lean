module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenRankOne
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

omit [CharP K 2] in
theorem g2N_inv (A B C D E F : K) :
    (g2N A B C D E F)⁻¹ = X g2c (-F) * X g2b (-E) * X g2v (-D) * X g2u (-C) * X g2a (-B) *
      X g2r (-A) := by
  simp only [g2N, mul_inv_rev, pinnedX_neg, mul_assoc]

theorem g2N_zero_mul_g2N_zero (B C D E F B' C' D' E' F' : K) :
    g2N 0 B C D E F * g2N 0 B' C' D' E' F' =
      g2N 0 (B + B') (C + C') (D + D') (E + E') (F + B' * E + C' * D + F') := by
  rw [mul_g2N, pinnedX_zero, mul_one, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]

theorem g2N_zero_inv (B C D E F : K) :
    (g2N 0 B C D E F)⁻¹ = g2N 0 B C D E (F + C * D + B * E) := by
  rw [g2N_inv]
  simp only [CharTwo.neg_eq, pinnedX_zero, mul_one]
  rw [pinnedX_c_eq_g2N, g2N_mul_b, g2N_mul_v, g2N_mul_u, g2N_mul_a]
  refine g2N_eq_g2N rfl ?_ ?_ ?_ ?_ ?_ <;> char2_ring

variable (K) in
@[expose] def g2LongRadical : Subgroup (ModGL .G2 K) where
  carrier := {g | ∃ B C D E F : K, g = g2N 0 B C D E F}
  mul_mem' := by
    rintro _ _ ⟨B, C, D, E, F, rfl⟩ ⟨B', C', D', E', F', rfl⟩
    exact ⟨_, _, _, _, _, g2N_zero_mul_g2N_zero B C D E F B' C' D' E' F'⟩
  one_mem' := ⟨0, 0, 0, 0, 0, g2N_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨B, C, D, E, F, rfl⟩
    exact ⟨_, _, _, _, _, g2N_zero_inv B C D E F⟩

theorem mem_g2LongRadical {g : ModGL .G2 K} :
    g ∈ g2LongRadical K ↔ ∃ B C D E F : K, g = g2N 0 B C D E F :=
  Iff.rfl

theorem g2N_mem_g2LongRadical (B C D E F : K) : g2N 0 B C D E F ∈ g2LongRadical K :=
  ⟨B, C, D, E, F, rfl⟩

theorem g2LongRadical_le_posUnipotent : g2LongRadical K ≤ posUnipotent .G2 K := by
  rintro _ ⟨B, C, D, E, F, rfl⟩
  exact g2N_mem_posUnipotent 0 B C D E F

theorem pinnedX_c_mem_g2LongRadical (y : K) : X g2c y ∈ g2LongRadical K :=
  ⟨0, 0, 0, 0, y, pinnedX_c_eq_g2N y⟩

theorem commute_pinnedX_c_g2N (y A B C D E F : K) : Commute (X g2c y) (g2N A B C D E F) := by
  have h := conj_c y A B C D E F
  calc X g2c y * g2N A B C D E F = X g2c y * g2N A B C D E F * X g2c y * X g2c y := by
        rw [mul_assoc _ (X g2c y), pinnedX_mul_self, mul_one]
    _ = g2N A B C D E F * X g2c y := by rw [h]

theorem commute_pinnedX_c_of_mem_posUnipotent (y : K) {u : ModGL .G2 K}
    (hu : u ∈ posUnipotent .G2 K) : Commute (X g2c y) u := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hu
  exact commute_pinnedX_c_g2N y A B C D E F

theorem exists_pinnedX_r_mul_of_mem_posUnipotent {u : ModGL .G2 K} (hu : u ∈ posUnipotent .G2 K) :
    ∃ s : K, ∃ q ∈ g2LongRadical K, u = X g2r s * q := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := exists_g2N_of_mem_posUnipotent hu
  refine ⟨A, g2N 0 B C D E F, g2N_mem_g2LongRadical B C D E F, ?_⟩
  simp only [g2N, pinnedX_zero, one_mul, mul_assoc]

@[expose] def ActsOnRadical (l : ModGL .G2 K) (T : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) : Prop :=
  (∀ y, Commute l (X g2c y)) ∧ ∀ (x : Fin 4 → K) (F : K), ∃ F' : K,
    l * g2N 0 (x 0) (x 1) (x 2) (x 3) F * l⁻¹ = g2N 0 (T x 0) (T x 1) (T x 2) (T x 3) F'

omit [CharP K 2] in
theorem ActsOnRadical.unique {l : ModGL .G2 K} {T T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K)}
    (h : ActsOnRadical l T) (h' : ActsOnRadical l T') : T = T' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨F, hF⟩ := h.2 x 0
  obtain ⟨F', hF'⟩ := h'.2 x 0
  obtain ⟨-, h0, h1, h2, h3, -⟩ := g2N_injective (hF.symm.trans hF')
  funext i
  fin_cases i
  exacts [h0, h1, h2, h3]

omit [CharP K 2] in
theorem ActsOnRadical.mul {l l' : ModGL .G2 K} {T T' : (Fin 4 → K) →ₗ[K] (Fin 4 → K)}
    (h : ActsOnRadical l T) (h' : ActsOnRadical l' T') : ActsOnRadical (l * l') (T ∘ₗ T') := by
  refine ⟨fun y => (h.1 y).mul_left (h'.1 y), fun x F => ?_⟩
  obtain ⟨F₁, hF₁⟩ := h'.2 x F
  obtain ⟨F₂, hF₂⟩ := h.2 (T' x) F₁
  refine ⟨F₂, ?_⟩
  rw [mul_inv_rev, show l * l' * g2N 0 (x 0) (x 1) (x 2) (x 3) F * (l'⁻¹ * l⁻¹) =
    l * (l' * g2N 0 (x 0) (x 1) (x 2) (x 3) F * l'⁻¹) * l⁻¹ by group, hF₁, hF₂]
  rfl

omit [CharP K 2] in
theorem actsOnRadical_one : ActsOnRadical (1 : ModGL .G2 K) LinearMap.id :=
  ⟨fun y => Commute.one_left _, fun x F => ⟨F, by simp⟩⟩

@[expose] def radMr (s : K) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun x := ![x 0, x 1 + x 0 * s, x 2 + x 0 * s ^ 2, x 3 + x 0 * s ^ 3 + x 1 * s ^ 2 + x 2 * s]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

@[expose] def radSwap : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun x := ![x 3, x 2, x 1, x 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' c x := by
    funext i
    fin_cases i <;> simp

@[expose] def radDiag (t : Kˣ) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) where
  toFun x := ![((t ^ (-3 : ℤ) : Kˣ) : K) * x 0, ((t ^ (-1 : ℤ) : Kˣ) : K) * x 1,
    ((t ^ (1 : ℤ) : Kˣ) : K) * x 2, ((t ^ (3 : ℤ) : Kˣ) : K) * x 3]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

theorem actsOnRadical_pinnedX_r (s : K) : ActsOnRadical (X g2r s) (radMr s) := by
  refine ⟨fun y => commute_r_c s y, fun x F => ?_⟩
  rw [pinnedX_inv_eq, conj_r]
  exact ⟨_, rfl⟩

theorem weylElt_r_conj_g2N (B C D E F : K) :
    weylElt .G2 K g2ir 1 * g2N 0 B C D E F * (weylElt .G2 K g2ir 1)⁻¹ =
      g2N 0 E D C B (D * C + E * B + F) := by
  rw [show g2N 0 B C D E F = X g2a B * X g2u C * X g2v D * X g2b E * X g2c F by
      simp only [g2N, pinnedX_zero, one_mul],
    show weylElt .G2 K g2ir 1 * (X g2a B * X g2u C * X g2v D * X g2b E * X g2c F) *
      (weylElt .G2 K g2ir 1)⁻¹ = MulAut.conj (weylElt .G2 K g2ir 1)
        (X g2a B * X g2u C * X g2v D * X g2b E * X g2c F) from rfl]
  simp only [map_mul, MulAut.conj_apply]
  rw [weylElt_conj g2ir isRoot_g2a, weylElt_conj g2ir isRoot_g2u, weylElt_conj g2ir isRoot_g2v,
    weylElt_conj g2ir isRoot_g2b, weylElt_conj g2ir isRoot_g2c, reflect_r_a, reflect_r_u,
    reflect_r_v, reflect_r_b, reflect_r_c, pinnedX_b_eq_g2N, g2N_mul_v, g2N_mul_u, g2N_mul_a,
    g2N_mul_c]
  refine g2N_eq_g2N rfl ?_ ?_ ?_ rfl ?_ <;> char2_ring

theorem commute_weylElt_r_pinnedX_c (y : K) : Commute (weylElt .G2 K g2ir 1) (X g2c y) := by
  have h := weylElt_conj (K := K) g2ir isRoot_g2c y
  rw [reflect_r_c] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem actsOnRadical_weylElt_r : ActsOnRadical (weylElt .G2 K g2ir 1) radSwap := by
  refine ⟨commute_weylElt_r_pinnedX_c, fun x F => ?_⟩
  rw [weylElt_r_conj_g2N]
  exact ⟨_, rfl⟩

theorem pinnedX_nr_eq (s : K) :
    X g2nr s = weylElt .G2 K g2ir 1 * X g2r s * (weylElt .G2 K g2ir 1)⁻¹ := by
  rw [weylElt_conj g2ir isRoot_g2r, reflect_r_r]

theorem actsOnRadical_pinnedX_nr (s : K) :
    ActsOnRadical (X g2nr s) (radSwap ∘ₗ radMr s ∘ₗ radSwap) := by
  rw [pinnedX_nr_eq, weylElt_inv]
  exact (actsOnRadical_weylElt_r.mul (actsOnRadical_pinnedX_r s)).mul actsOnRadical_weylElt_r

omit [CharP K 2] in
theorem torus_r_conj (t : Kˣ) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (m : ℤ)
    (hm : ∑ j, Tag.G2.cartan g2ir j * α j = m) (x : K) :
    torusElt .G2 K g2ir t * X α x * (torusElt .G2 K g2ir t)⁻¹ = X α (((t ^ m : Kˣ) : K) * x) := by
  rw [root_torus_conjugation g2ir hα, hm]

omit [CharP K 2] in
theorem actsOnRadical_torusElt_r (t : Kˣ) : ActsOnRadical (torusElt .G2 K g2ir t) (radDiag t) := by
  have e : ∀ a b : ModGL .G2 K, torusElt .G2 K g2ir t * (a * b) * (torusElt .G2 K g2ir t)⁻¹ =
      (torusElt .G2 K g2ir t * a * (torusElt .G2 K g2ir t)⁻¹) *
        (torusElt .G2 K g2ir t * b * (torusElt .G2 K g2ir t)⁻¹) := fun a b => by group
  refine ⟨fun y => ?_, fun x F => ⟨((t ^ (0 : ℤ) : Kˣ) : K) * F, ?_⟩⟩
  · have h := torus_r_conj t isRoot_g2c 0 (by decide) y
    rw [zpow_zero, Units.val_one, one_mul] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  · simp only [g2N, pinnedX_zero, one_mul, e]
    rw [torus_r_conj t isRoot_g2a (-3) (by decide), torus_r_conj t isRoot_g2u (-1) (by decide),
      torus_r_conj t isRoot_g2v 1 (by decide), torus_r_conj t isRoot_g2b 3 (by decide),
      torus_r_conj t isRoot_g2c 0 (by decide)]
    rfl

theorem g2nr_eq_neg_single : g2nr = -Pi.single g2ir 1 := List.ofFn_injective (by decide +kernel)

omit [CharP K 2] in
theorem xUnit_g2ir (s : K) : xUnit .G2 K g2ir s = X g2r s := by
  rw [g2r_eq_single, pinnedX_single]

omit [CharP K 2] in
theorem yUnit_g2ir (s : K) : yUnit .G2 K g2ir s = X g2nr s := by
  rw [g2nr_eq_neg_single, pinnedX_neg_single]

omit [CharP K 2] in
theorem g2RankOne_r_eq :
    g2RankOne K g2ir = Subgroup.closure (Set.range (X g2r) ∪ Set.range (X g2nr)) := by
  rw [g2RankOne]
  congr 2
  · exact congrArg Set.range (funext xUnit_g2ir)
  · exact congrArg Set.range (funext yUnit_g2ir)

theorem exists_actsOnRadical {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ir) :
    ∃ T, ActsOnRadical l T := by
  have key : ∀ l ∈ g2RankOne K g2ir, (∃ T, ActsOnRadical l T) ∧ ∃ T', ActsOnRadical l⁻¹ T' := by
    intro l hl
    induction hl using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · rw [xUnit_g2ir, pinnedX_inv_eq]
        exact ⟨⟨_, actsOnRadical_pinnedX_r s⟩, ⟨_, actsOnRadical_pinnedX_r s⟩⟩
      · rw [yUnit_g2ir, pinnedX_inv_eq]
        exact ⟨⟨_, actsOnRadical_pinnedX_nr s⟩, ⟨_, actsOnRadical_pinnedX_nr s⟩⟩
    | one => exact ⟨⟨_, actsOnRadical_one⟩, ⟨_, by rw [inv_one]; exact actsOnRadical_one⟩⟩
    | mul x y _ _ hx hy =>
      exact ⟨⟨_, hx.1.choose_spec.mul hy.1.choose_spec⟩,
        ⟨_, by rw [mul_inv_rev]; exact hy.2.choose_spec.mul hx.2.choose_spec⟩⟩
    | inv x _ hx => exact ⟨hx.2, by rw [inv_inv]; exact hx.1⟩
  exact (key l hl).1

theorem commute_of_mem_g2RankOne_r {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ir) (y : K) :
    Commute l (X g2c y) :=
  (exists_actsOnRadical hl).choose_spec.1 y

theorem conj_mem_g2LongRadical {l q : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ir)
    (hq : q ∈ g2LongRadical K) : l * q * l⁻¹ ∈ g2LongRadical K := by
  obtain ⟨B, C, D, E, F, rfl⟩ := hq
  obtain ⟨T, -, hT⟩ := exists_actsOnRadical hl
  obtain ⟨F', hF'⟩ := hT ![B, C, D, E] F
  rw [show g2N 0 B C D E F = g2N 0 (![B, C, D, E] 0) (![B, C, D, E] 1) (![B, C, D, E] 2)
    (![B, C, D, E] 3) F from rfl, hF']
  exact g2N_mem_g2LongRadical _ _ _ _ _

@[expose] def radAction (l : g2RankOne K g2ir) : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
  (exists_actsOnRadical l.2).choose

theorem radAction_spec (l : g2RankOne K g2ir) : ActsOnRadical (l : ModGL .G2 K) (radAction l) :=
  (exists_actsOnRadical l.2).choose_spec

theorem radAction_mul (l l' : g2RankOne K g2ir) :
    radAction (l * l') = radAction l ∘ₗ radAction l' :=
  (radAction_spec (l * l')).unique ((radAction_spec l).mul (radAction_spec l'))

theorem radAction_one : radAction (1 : g2RankOne K g2ir) = LinearMap.id :=
  (radAction_spec 1).unique actsOnRadical_one

@[expose] def radActionHom : g2RankOne K g2ir →* LinearMap.GeneralLinearGroup K (Fin 4 → K) where
  toFun l := ⟨radAction l, radAction l⁻¹, by
      rw [Module.End.mul_eq_comp, ← radAction_mul, mul_inv_cancel, radAction_one]; rfl, by
      rw [Module.End.mul_eq_comp, ← radAction_mul, inv_mul_cancel, radAction_one]; rfl⟩
  map_one' := Units.ext radAction_one
  map_mul' l l' := Units.ext (radAction_mul l l')

theorem coe_radActionHom (l : g2RankOne K g2ir) :
    ((radActionHom l : LinearMap.GeneralLinearGroup K (Fin 4 → K)) :
      (Fin 4 → K) →ₗ[K] (Fin 4 → K)) = radAction l :=
  rfl

theorem radActionHom_injective [Finite K] : Function.Injective (radActionHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨l, hl⟩ h1
  have hid : radAction ⟨l, hl⟩ = LinearMap.id := congrArg Units.val h1
  have hact : ActsOnRadical l LinearMap.id := hid ▸ radAction_spec ⟨l, hl⟩
  obtain ⟨ρ, -, -, -, -, hrange, -, hcell0, hcell⟩ := g2_rank_one (K := K) g2ir
  rw [← hrange] at hl
  obtain ⟨g, rfl⟩ := hl
  refine Subtype.ext ?_
  show ρ g = 1
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [hcell0 g hc, xUnit_g2ir] at hact ⊢
    set a := Units.mk0 _ (SL2_apply_zero_zero_ne_zero hc)
    set b := (g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0
    have he := ((actsOnRadical_torusElt_r a).mul (actsOnRadical_pinnedX_r b)).unique hact
    have h2 := congrArg (fun T : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T ![0, 0, 1, 0] 2) he
    have h3 := congrArg (fun T : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T ![0, 0, 1, 0] 3) he
    simp [radDiag, radMr] at h2 h3
    rw [h2, h3, torusElt_one, pinnedX_zero, mul_one]
  · exfalso
    rw [hcell g hc, xUnit_g2ir, xUnit_g2ir] at hact
    have he := ((((actsOnRadical_pinnedX_r _).mul (actsOnRadical_torusElt_r _)).mul
      actsOnRadical_weylElt_r).mul (actsOnRadical_pinnedX_r _)).unique hact
    have h0 := congrArg (fun T : (Fin 4 → K) →ₗ[K] (Fin 4 → K) => T ![0, 0, 0, 1] 0) he
    simp [radDiag, radMr, radSwap] at h0
    exact hc h0

omit [CharP K 2] in
theorem weyl_eq_of_pinnedX_c {w : WeylGroup .G2} {l m : K} (hl : l ≠ 0) (hm : m ≠ 0)
    (h : X (w • g2c) l = X g2c m) : w = 1 ∨ w = simple .G2 g2ir := by
  have hX : ∀ {γ : Fin Tag.G2.rank → ℤ}, (γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨
      γ = g2c) → X (-γ) l = X g2c m → False := fun hγ he => by
    have h1 : X g2c m = 1 :=
      eq_one_of_mem_borel_of_mem_neg (posUnipotent_le_borelGroup
        (by rw [pinnedX_c_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _))
        (he ▸ pinnedX_neg_mem_negUnipotent hγ l)
    exact hm (pinnedX_injective .G2 K _ (h1.trans (pinnedX_zero .G2 K _).symm))
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [smul_g2c, ha, hr] at h
  · exact Or.inl (eq_one_of_smul ha hr)
  · rw [show -g2a + -g2a + (g2u + g2u + g2u) = g2b from List.ofFn_injective (by decide +kernel),
      pinnedX_b_eq_g2N, pinnedX_c_eq_g2N] at h
    exact absurd (g2N_injective h).2.2.2.2.1 hl
  · exact Or.inr (eq_simple_r_of_smul ha hr)
  · rw [show g2c + g2c + (-g2u + -g2u + -g2u) = g2b from List.ofFn_injective (by decide +kernel),
      pinnedX_b_eq_g2N, pinnedX_c_eq_g2N] at h
    exact absurd (g2N_injective h).2.2.2.2.1 hl
  · rw [show -g2b + -g2b + (g2v + g2v + g2v) = g2a from List.ofFn_injective (by decide +kernel),
      pinnedX_a_eq_g2N, pinnedX_c_eq_g2N] at h
    exact absurd (g2N_injective h).2.1 hl
  · rw [show -g2c + -g2c + (g2v + g2v + g2v) = -g2a from
      List.ofFn_injective (by decide +kernel)] at h
    exact (hX (Or.inr (Or.inl rfl)) h).elim
  · rw [show g2c + g2c + (-g2v + -g2v + -g2v) = g2a from List.ofFn_injective (by decide +kernel),
      pinnedX_a_eq_g2N, pinnedX_c_eq_g2N] at h
    exact absurd (g2N_injective h).2.1 hl
  · rw [show -g2c + -g2c + (g2u + g2u + g2u) = -g2b from
      List.ofFn_injective (by decide +kernel)] at h
    exact (hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h).elim
  · rw [show g2b + g2b + (-g2v + -g2v + -g2v) = -g2a from
      List.ofFn_injective (by decide +kernel)] at h
    exact (hX (Or.inr (Or.inl rfl)) h).elim
  · rw [show -g2b + -g2b + (g2r + g2r + g2r) = -g2c from
      List.ofFn_injective (by decide +kernel)] at h
    exact (hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h).elim
  · rw [show g2a + g2a + (-g2u + -g2u + -g2u) = -g2b from
      List.ofFn_injective (by decide +kernel)] at h
    exact (hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h).elim
  · rw [show -g2a + -g2a + (-g2r + -g2r + -g2r) = -g2c from
      List.ofFn_injective (by decide +kernel)] at h
    exact (hX (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h).elim

omit [CharP K 2] in
theorem torus_scale_c {h : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K) :
    ∃ c : Kˣ, (∀ y, h * X g2c y * h⁻¹ = X g2c (c * y)) ∧ (c = 1 → h ∈ g2RankOne K g2ir) := by
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  refine ⟨t₁, fun y => ?_, fun h1 => ?_⟩
  · rw [torus_conj isRoot_g2c]
    have e1 : ∑ j, Tag.G2.cartan g2ia j * g2c j = 1 := by decide
    have e2 : ∑ j, Tag.G2.cartan g2ir j * g2c j = 0 := by decide
    rw [e1, e2, zpow_one, zpow_zero, mul_one]
  · rw [h1, torusElt_one, one_mul]
    exact torusElt_mem_g2RankOne g2ir t₂

omit [CharP K 2] in
theorem torus_conj_mem_g2RankOne_r {h l : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K)
    (hl : l ∈ g2RankOne K g2ir) : h * l * h⁻¹ ∈ g2RankOne K g2ir := by
  have key : g2RankOne K g2ir ≤ (g2RankOne K g2ir).comap (MulAut.conj h).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · obtain ⟨c, hc⟩ := exists_torus_scale hh isRoot_g2r
      show h * xUnit .G2 K g2ir s * h⁻¹ ∈ g2RankOne K g2ir
      rw [xUnit_g2ir, hc, ← xUnit_g2ir]
      exact xUnit_mem_g2RankOne g2ir _
    · obtain ⟨c, hc⟩ := exists_torus_scale hh isRoot_g2nr
      show h * yUnit .G2 K g2ir s * h⁻¹ ∈ g2RankOne K g2ir
      rw [yUnit_g2ir, hc, ← yUnit_g2ir]
      exact yUnit_mem_g2RankOne g2ir _
  exact key hl

theorem exists_mem_mul_of_commute_c {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K)
    (hgz : g * X g2c 1 = X g2c 1 * g) :
    ∃ q ∈ g2LongRadical K, ∃ l ∈ g2RankOne K g2ir, g = q * l := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_bruhat hg
  obtain ⟨h₁, hh₁, u₁, hu₁, rfl⟩ := exists_torus_mul_of_mem_borel hb₁
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ := exists_torus_mul_of_mem_borel hb₂
  obtain ⟨c₁, hc₁, -⟩ := torus_scale_c hh₁
  obtain ⟨c₂, hc₂, -⟩ := torus_scale_c hh₂
  set n := canonicalRep (coxeterSystem .G2) K w with hn
  have hu₁c : ∀ y, u₁ * X g2c y = X g2c y * u₁ := fun y =>
    (commute_pinnedX_c_of_mem_posUnipotent y hu₁).eq.symm
  have hu₂c : ∀ y, u₂ * X g2c y = X g2c y * u₂ := fun y =>
    (commute_pinnedX_c_of_mem_posUnipotent y hu₂).eq.symm
  have hgz' : h₁ * u₁ * n * (h₂ * u₂) * X g2c 1 * (h₁ * u₁ * n * (h₂ * u₂))⁻¹ = X g2c 1 := by
    rw [hgz, mul_inv_cancel_right]
  have hconj₂ : h₂ * u₂ * X g2c 1 * (h₂ * u₂)⁻¹ = X g2c (c₂ * 1) := by
    calc h₂ * u₂ * X g2c 1 * (h₂ * u₂)⁻¹ = h₂ * (u₂ * X g2c 1) * u₂⁻¹ * h₂⁻¹ := by group
      _ = X g2c (c₂ * 1) := by rw [hu₂c, mul_assoc h₂, mul_inv_cancel_right, hc₂]
  have hconj₁ : (h₁ * u₁)⁻¹ * X g2c 1 * (h₁ * u₁) = X g2c (c₁⁻¹ * 1) := by
    have e := hc₁ (c₁⁻¹ * 1)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at e
    calc (h₁ * u₁)⁻¹ * X g2c 1 * (h₁ * u₁) = u₁⁻¹ * (h₁⁻¹ * X g2c 1 * h₁) * u₁ := by group
      _ = u₁⁻¹ * (h₁⁻¹ * (h₁ * X g2c (c₁⁻¹ * 1) * h₁⁻¹) * h₁) * u₁ := by rw [e]
      _ = u₁⁻¹ * (X g2c (c₁⁻¹ * 1) * u₁) := by group
      _ = X g2c (c₁⁻¹ * 1) := by rw [← hu₁c, inv_mul_cancel_left]
  have hW : X (w • g2c) (c₂ * 1) = X g2c (c₁⁻¹ * 1) := by
    rw [← canonicalRep_conj w isRoot_g2c, ← hn, ← hconj₂, ← hconj₁]
    calc n * (h₂ * u₂ * X g2c 1 * (h₂ * u₂)⁻¹) * n⁻¹ =
        (h₁ * u₁)⁻¹ * (h₁ * u₁ * n * (h₂ * u₂) * X g2c 1 *
          (h₁ * u₁ * n * (h₂ * u₂))⁻¹) * (h₁ * u₁) := by group
      _ = (h₁ * u₁)⁻¹ * X g2c 1 * (h₁ * u₁) := by rw [hgz']
  have hnL : n ∈ g2RankOne K g2ir := by
    rcases weyl_eq_of_pinnedX_c (by simp) (by simp) hW with rfl | rfl
    · rw [hn, canonicalRep_one]
      exact one_mem _
    · rw [hn, canonicalRep_simple]
      exact weylElt_mem_g2RankOne g2ir 1
  have hc12 : X g2c ((c₁ * c₂ : Kˣ) * 1) = X g2c 1 := by
    rw [← hgz']
    calc X g2c ((c₁ * c₂ : Kˣ) * 1) = h₁ * X g2c (c₂ * 1) * h₁⁻¹ := by
          rw [hc₁, Units.val_mul, mul_assoc]
      _ = h₁ * (u₁ * (n * X g2c (c₂ * 1) * n⁻¹) * u₁⁻¹) * h₁⁻¹ := by
          rw [(commute_of_mem_g2RankOne_r hnL _).eq, mul_inv_cancel_right, hu₁c,
            mul_inv_cancel_right]
      _ = _ := by rw [← hconj₂]; group
  obtain ⟨c, hc, hcL⟩ := torus_scale_c (mul_mem hh₁ hh₂)
  have hc1 : c = 1 := by
    have e : X g2c ((c : K) * 1) = X g2c 1 := by
      rw [← hc]
      calc h₁ * h₂ * X g2c 1 * (h₁ * h₂)⁻¹ = h₁ * (h₂ * X g2c 1 * h₂⁻¹) * h₁⁻¹ := by group
        _ = X g2c ((c₁ * c₂ : Kˣ) * 1) := by rw [hc₂, hc₁, Units.val_mul, mul_assoc]
        _ = X g2c 1 := hc12
    have e' := pinnedX_injective .G2 K _ e
    exact Units.ext (by simpa using e')
  have hl₂ : h₁ * h₂ ∈ g2RankOne K g2ir := hcL hc1
  have hl₁ : h₁ * n * h₁⁻¹ ∈ g2RankOne K g2ir := torus_conj_mem_g2RankOne_r hh₁ hnL
  obtain ⟨s₁, q₁, hq₁, hu₁'⟩ :=
    exists_pinnedX_r_mul_of_mem_posUnipotent (torus_conj_mem_posUnipotent hh₁ hu₁)
  obtain ⟨s₂, q₂, hq₂, rfl⟩ := exists_pinnedX_r_mul_of_mem_posUnipotent hu₂
  have hu₁e : u₁ = h₁⁻¹ * (X g2r s₁ * q₁) * h₁ := by rw [← hu₁']; group
  subst hu₁e
  have hxL : ∀ s : K, X g2r s ∈ g2RankOne K g2ir := fun s => by
    rw [← xUnit_g2ir]; exact xUnit_mem_g2RankOne g2ir s
  set l₃ := X g2r s₁ * (h₁ * n * h₁⁻¹) * (h₁ * h₂) * X g2r s₂ with hl₃
  have hl₃L : l₃ ∈ g2RankOne K g2ir :=
    mul_mem (mul_mem (mul_mem (hxL s₁) hl₁) hl₂) (hxL s₂)
  refine ⟨X g2r s₁ * q₁ * (X g2r s₁)⁻¹ * (l₃ * q₂ * l₃⁻¹),
    mul_mem (conj_mem_g2LongRadical (hxL s₁) hq₁) (conj_mem_g2LongRadical hl₃L hq₂), l₃, hl₃L, ?_⟩
  rw [hl₃]
  group

theorem g2LongRadical_isPGroup : IsPGroup 2 (g2LongRadical K) := by
  rintro ⟨_, B, C, D, E, F, rfl⟩
  refine ⟨2, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 2 = 2 * 2 from rfl, pow_mul, sq, sq,
    g2N_mul_self, g2N_mul_self, ← g2N_zero]
  refine g2N_eq_g2N rfl rfl ?_ ?_ ?_ ?_ <;> char2_ring

theorem g2LongRadical_le_adjointGroup : g2LongRadical K ≤ adjointGroup .G2 K :=
  g2LongRadical_le_posUnipotent.trans (posUnipotent_le_borelGroup.trans
    ((triangular_borel_structure.{0, 0} .G2 K).2.2.2.2.2.2.2.2.2.2.2 K).1)

theorem exists_radCoord {q : ModGL .G2 K} (hq : q ∈ g2LongRadical K) :
    ∃ x : Fin 4 → K, ∃ F : K, q = g2N 0 (x 0) (x 1) (x 2) (x 3) F := by
  obtain ⟨B, C, D, E, F, rfl⟩ := hq
  exact ⟨![B, C, D, E], F, rfl⟩

@[expose] def radCoord (q : g2LongRadical K) : Fin 4 → K := (exists_radCoord q.2).choose

theorem radCoord_spec (q : g2LongRadical K) : ∃ F : K, (q : ModGL .G2 K) =
    g2N 0 (radCoord q 0) (radCoord q 1) (radCoord q 2) (radCoord q 3) F :=
  (exists_radCoord q.2).choose_spec

theorem radCoord_eq {q : g2LongRadical K} {B C D E F : K}
    (h : (q : ModGL .G2 K) = g2N 0 B C D E F) :
    radCoord q = ![B, C, D, E] := by
  obtain ⟨F', hF'⟩ := radCoord_spec q
  obtain ⟨-, h0, h1, h2, h3, -⟩ := g2N_injective (hF'.symm.trans h)
  funext i
  fin_cases i
  exacts [h0, h1, h2, h3]

@[expose] def radCoordHom : g2LongRadical K →* Multiplicative (Fin 4 → K) where
  toFun q := Multiplicative.ofAdd (radCoord q)
  map_one' := by
    rw [radCoord_eq (show ((1 : g2LongRadical K) : ModGL .G2 K) = g2N 0 0 0 0 0 0 from
      g2N_zero.symm)]
    funext i
    fin_cases i <;> rfl
  map_mul' q q' := by
    obtain ⟨F, hF⟩ := radCoord_spec q
    obtain ⟨F', hF'⟩ := radCoord_spec q'
    have h : ((q * q' : g2LongRadical K) : ModGL .G2 K) =
        g2N 0 (radCoord q 0 + radCoord q' 0) (radCoord q 1 + radCoord q' 1)
          (radCoord q 2 + radCoord q' 2) (radCoord q 3 + radCoord q' 3)
          (F + radCoord q' 0 * radCoord q 3 + radCoord q' 1 * radCoord q 2 + F') := by
      rw [Subgroup.coe_mul, hF, hF', g2N_zero_mul_g2N_zero]
    show Multiplicative.ofAdd (radCoord (q * q')) =
      Multiplicative.ofAdd (radCoord q) * Multiplicative.ofAdd (radCoord q')
    rw [radCoord_eq h, ← ofAdd_add]
    refine congrArg Multiplicative.ofAdd ?_
    funext i
    fin_cases i <;> rfl

theorem radCoordHom_g2N (B C D E F : K) (h : g2N 0 B C D E F ∈ g2LongRadical K) :
    radCoordHom ⟨g2N 0 B C D E F, h⟩ = Multiplicative.ofAdd ![B, C, D, E] :=
  congrArg Multiplicative.ofAdd (radCoord_eq rfl)

theorem radCoordHom_surjective : Function.Surjective (radCoordHom (K := K)) := by
  intro x
  refine ⟨⟨g2N 0 (x.toAdd 0) (x.toAdd 1) (x.toAdd 2) (x.toAdd 3) 0,
    g2N_mem_g2LongRadical _ _ _ _ _⟩, ?_⟩
  rw [radCoordHom_g2N]
  refine congrArg Multiplicative.ofAdd ?_
  funext i
  fin_cases i <;> rfl

theorem radCoordHom_ker :
    (radCoordHom (K := K)).ker = (rootSubgroup .G2 K g2c).subgroupOf (g2LongRadical K) := by
  ext q
  obtain ⟨B, C, D, E, F, hqe⟩ := q.2
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_rootSubgroup, hqe]
  show Multiplicative.ofAdd (radCoord q) = 1 ↔ _
  rw [radCoord_eq hqe]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, toAdd_one] at h'
    have hB := congrFun h' 0
    have hC := congrFun h' 1
    have hD := congrFun h' 2
    have hE := congrFun h' 3
    simp at hB hC hD hE
    subst hB hC hD hE
    exact ⟨F, pinnedX_c_eq_g2N F⟩
  · rintro ⟨c, hc⟩
    rw [pinnedX_c_eq_g2N] at hc
    obtain ⟨-, hB, hC, hD, hE, -⟩ := g2N_injective hc
    subst hB hC hD hE
    refine congrArg Multiplicative.ofAdd ?_
    funext i
    fin_cases i <;> rfl

theorem actsOnRadical_of_mem {q : ModGL .G2 K} (hq : q ∈ g2LongRadical K) :
    ActsOnRadical q LinearMap.id := by
  obtain ⟨B, C, D, E, F, rfl⟩ := hq
  refine ⟨fun y => (commute_pinnedX_c_g2N y 0 B C D E F).symm, fun x F₀ => ?_⟩
  rw [g2N_zero_inv, g2N_zero_mul_g2N_zero, g2N_zero_mul_g2N_zero]
  refine ⟨_, g2N_eq_g2N rfl ?_ ?_ ?_ ?_ rfl⟩ <;> simp only [LinearMap.id_apply] <;> char2_ring

theorem g2LongRadical_inf_g2RankOne [Finite K] : g2LongRadical K ⊓ g2RankOne K g2ir = ⊥ := by
  refine eq_bot_iff.2 fun l hl => ?_
  obtain ⟨hlQ, hlL⟩ := Subgroup.mem_inf.1 hl
  have h1 : radAction ⟨l, hlL⟩ = LinearMap.id :=
    (radAction_spec ⟨l, hlL⟩).unique (actsOnRadical_of_mem hlQ)
  have h2 : radActionHom ⟨l, hlL⟩ = 1 := Units.ext h1
  rw [← map_one radActionHom] at h2
  exact Subgroup.mem_bot.2 (congrArg Subtype.val (radActionHom_injective h2))

theorem g2RankOne_r_le_normalizer :
    g2RankOne K g2ir ≤ Subgroup.normalizer (g2LongRadical K : Set (ModGL .G2 K)) := by
  intro l hl
  refine Subgroup.mem_normalizer_iff.2 fun q => ⟨fun hq => conj_mem_g2LongRadical hl hq,
    fun hq => ?_⟩
  have h := conj_mem_g2LongRadical (inv_mem hl) hq
  rwa [inv_inv, show l⁻¹ * (l * q * l⁻¹) * l = q by group] at h

theorem even_G2_highest_long_root_centralizer (K : Type) [Field K] [Finite K] [CharP K 2] :
    g2RankOne K g2ir =
        Subgroup.closure (Set.range (pinnedX .G2 K g2r) ∪ Set.range (pinnedX .G2 K g2nr)) ∧
      g2LongRadical K ≤ adjointGroup .G2 K ∧ IsPGroup 2 (g2LongRadical K) ∧
      adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} =
        g2LongRadical K ⊔ g2RankOne K g2ir ∧
      ((adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1} :
          Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) =
        (g2LongRadical K : Set (ModGL .G2 K)) * (g2RankOne K g2ir : Set (ModGL .G2 K)) ∧
      g2RankOne K g2ir ≤ Subgroup.normalizer (g2LongRadical K : Set (ModGL .G2 K)) ∧
      g2LongRadical K ⊓ g2RankOne K g2ir = ⊥ ∧
      (∃ ρ : SL2 K →* ModGL .G2 K, (∀ c, ρ (uSL c) = pinnedX .G2 K g2r c) ∧
        (∀ c, ρ (vSL c) = pinnedX .G2 K g2nr c) ∧ ρ.range = g2RankOne K g2ir ∧
        Function.Injective ρ) ∧
      (∀ y : K, pinnedX .G2 K g2c y ∈ g2LongRadical K ∧
        ∀ q ∈ g2LongRadical K, Commute (pinnedX .G2 K g2c y) q) ∧
      (∃ π : g2LongRadical K →* Multiplicative (Fin 4 → K),
        π.ker = (rootSubgroup .G2 K g2c).subgroupOf (g2LongRadical K) ∧ Function.Surjective π ∧
        ∀ (B C D E F : K) (h : g2N 0 B C D E F ∈ g2LongRadical K),
          π ⟨g2N 0 B C D E F, h⟩ = Multiplicative.ofAdd ![B, C, D, E]) ∧
      (∃ ψ : g2RankOne K g2ir →* LinearMap.GeneralLinearGroup K (Fin 4 → K),
        Function.Injective ψ ∧ ∀ (l : g2RankOne K g2ir) (x : Fin 4 → K) (F : K), ∃ F' : K,
          (l : ModGL .G2 K) * g2N 0 (x 0) (x 1) (x 2) (x 3) F * (l : ModGL .G2 K)⁻¹ =
            g2N 0 ((ψ l : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) x 0)
              ((ψ l : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) x 1)
              ((ψ l : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) x 2)
              ((ψ l : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) x 3) F') ∧
      ∀ l ∈ g2RankOne K g2ir, ∀ y : K, Commute l (pinnedX .G2 K g2c y) := by
  have hQC : g2LongRadical K ≤ adjointGroup .G2 K ⊓
      Subgroup.centralizer {pinnedX .G2 K g2c 1} := fun q hq =>
    Subgroup.mem_inf.2 ⟨g2LongRadical_le_adjointGroup hq, Subgroup.mem_centralizer_iff.2
      fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (commute_pinnedX_c_of_mem_posUnipotent 1 (g2LongRadical_le_posUnipotent hq)).eq⟩
  have hLC : g2RankOne K g2ir ≤ adjointGroup .G2 K ⊓
      Subgroup.centralizer {pinnedX .G2 K g2c 1} := fun l hl =>
    Subgroup.mem_inf.2 ⟨g2RankOne_le_adjointGroup g2ir hl, Subgroup.mem_centralizer_iff.2
      fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (commute_of_mem_g2RankOne_r hl 1).eq.symm⟩
  have hsub : ∀ g ∈ adjointGroup .G2 K ⊓ Subgroup.centralizer {pinnedX .G2 K g2c 1},
      ∃ q ∈ g2LongRadical K, ∃ l ∈ g2RankOne K g2ir, g = q * l := fun g hg => by
    obtain ⟨hgC, hgz⟩ := Subgroup.mem_inf.1 hg
    exact exists_mem_mul_of_commute_c hgC
      ((Subgroup.mem_centralizer_iff.1 hgz _ (Set.mem_singleton _)).symm)
  obtain ⟨ρ, hu, hv, -, -, hrange, hinj, -, -⟩ := g2_rank_one (K := K) g2ir
  refine ⟨g2RankOne_r_eq, g2LongRadical_le_adjointGroup, g2LongRadical_isPGroup,
    le_antisymm (fun g hg => ?_) (sup_le hQC hLC), Set.Subset.antisymm (fun g hg => ?_) ?_,
    g2RankOne_r_le_normalizer, g2LongRadical_inf_g2RankOne,
    ⟨ρ, fun c => by rw [hu, xUnit_g2ir], fun c => by rw [hv, yUnit_g2ir], hrange, hinj⟩,
    fun y => ⟨pinnedX_c_mem_g2LongRadical y, fun q hq =>
      commute_pinnedX_c_of_mem_posUnipotent y (g2LongRadical_le_posUnipotent hq)⟩,
    ⟨radCoordHom, radCoordHom_ker, radCoordHom_surjective, radCoordHom_g2N⟩,
    ⟨radActionHom, radActionHom_injective, fun l x F => (radAction_spec l).2 x F⟩,
    fun l hl y => commute_of_mem_g2RankOne_r hl y⟩
  · obtain ⟨q, hq, l, hl, rfl⟩ := hsub g hg
    exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right hl)
  · obtain ⟨q, hq, l, hl, rfl⟩ := hsub g hg
    exact Set.mul_mem_mul hq hl
  · rintro _ ⟨q, hq, l, hl, rfl⟩
    exact mul_mem (hQC hq) (hLC hl)

end CFSG.ComponentClassification.UnbalancedCatalog
