module

public import CFSG.FeitThompson.Local.UnipotentPlaneTransitiveLines
public import CFSG.FeitThompson.Local.PrimePowerPlaneActionUnipotent
public import CFSG.FeitThompson.Local.HighRankCentralTorsionLine
public import CFSG.FeitThompson.Local.MaximalPlaneCentralizerPrimeTorsion
public import CFSG.FeitThompson.OddOrder.PGroupNormalizerCondition
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Submodule Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ}

private theorem finrank_eq_of_natCard_eq_pow [Fact p.Prime] {d : ℕ} (V : Type*) [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (h : Nat.card V = p ^ d) : finrank (ZMod p) V = d := by
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have h1 : Nat.card V = p ^ finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_zmod]
  rw [h] at h1
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm

section Line

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] {Q : Type*} [Group Q] [Fact p.Prime]

theorem exists_map_eq_of_fixed_line (hV : finrank (ZMod p) V = 2) (hQ : IsPGroup p Q)
    (ρ : Q →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hne : ∃ (q : Q) (v : V), (ρ q : Module.End (ZMod p) V) v ≠ v)
    {L₀ : Submodule (ZMod p) V} (hL₀ : finrank (ZMod p) L₀ = 1)
    (hfix : ∀ q : Q, ∀ v ∈ L₀, (ρ q : Module.End (ZMod p) V) v = v)
    {M₁ M₂ : Submodule (ZMod p) V} (h₁ : finrank (ZMod p) M₁ = 1)
    (h₂ : finrank (ZMod p) M₂ = 1) (hne₁ : M₁ ≠ L₀) (hne₂ : M₂ ≠ L₀) :
    ∃ q : Q, M₁.map (ρ q : Module.End (ZMod p) V) = M₂ := by
  have hfd : FiniteDimensional (ZMod p) V := .of_finrank_eq_succ hV
  rcases card_range_eq_one_or_eq_prime hV hQ ρ with h | h
  ·
    obtain ⟨q, v, hqv⟩ := hne
    have hbot : ρ.range = ⊥ := Subgroup.card_eq_one.mp h
    have hq1 : ρ q = 1 := by
      have hmem : ρ q ∈ ρ.range := ⟨q, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    rw [hq1] at hqv
    exact absurd (by simp) hqv
  obtain ⟨N, hN0, hN2, hrange⟩ := exists_sq_eq_zero_range_coe_eq hV ρ h
  have hN2' : N ^ 2 = 0 := by rw [pow_two]; exact hN2
  have hker : LinearMap.ker N = L₀ := by
    obtain ⟨q₁, hq₁⟩ : (1 + (1 : ZMod p) • N) ∈
        Set.range fun q : Q => (ρ q : Module.End (ZMod p) V) := hrange ▸ ⟨1, rfl⟩
    have hq₁' : ((ρ q₁ : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)
        = 1 + (1 : ZMod p) • N := hq₁
    refine (Submodule.eq_of_le_of_finrank_eq (fun v hv => ?_) ?_).symm
    · have hvv := hfix q₁ v hv
      rw [hq₁'] at hvv
      have hv' : v + N v = v := by simpa using hvv
      simpa [LinearMap.mem_ker] using hv'
    · rw [hL₀, finrank_ker_eq_one_of_mul_self_eq_zero hV hN0 hN2]
  obtain ⟨u, hu, huM⟩ := exists_mem_oneAddSMulGroup_smul_eq hV hN0 hN2' h₁ h₂
    (by rw [hker]; exact hne₁) (by rw [hker]; exact hne₂)
  obtain ⟨c, hc⟩ := mem_oneAddSMulGroup_iff.1 hu
  obtain ⟨q, hq⟩ : (1 + c • N) ∈ Set.range fun q : Q => (ρ q : Module.End (ZMod p) V) :=
    hrange ▸ ⟨c, rfl⟩
  have hq' : ((ρ q : LinearMap.GeneralLinearGroup (ZMod p) V) : Module.End (ZMod p) V)
      = 1 + c • N := hq
  exact ⟨q, by rw [← huM, smul_submodule_eq_map, hq', hc]⟩

end Line

section Glue

variable {A : Type*} [CommGroup A] [Module (ZMod p) (Additive A)]

def mulAutToLinearAut : MulAut A →* (Additive A ≃ₗ[ZMod p] Additive A) where
  toFun φ := { MulEquiv.toAdditive φ with map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive φ) c x }
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

def mulAutToGL : MulAut A →* LinearMap.GeneralLinearGroup (ZMod p) (Additive A) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive A)).symm :
    (Additive A ≃ₗ[ZMod p] Additive A) →* _).comp mulAutToLinearAut

@[simp] theorem mulAutToGL_apply (φ : MulAut A) (x : Additive A) :
    ((mulAutToGL (p := p) φ : LinearMap.GeneralLinearGroup (ZMod p) (Additive A)) :
      Module.End (ZMod p) (Additive A)) x = Additive.ofMul (φ (Additive.toMul x)) := (rfl)

def subgroupOrderIsoSubmodule (p : ℕ) (A : Type*) [CommGroup A] [Module (ZMod p) (Additive A)] :
    Subgroup A ≃o Submodule (ZMod p) (Additive A) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)

@[simp] theorem mem_subgroupOrderIsoSubmodule {L : Subgroup A} {x : Additive A} :
    x ∈ subgroupOrderIsoSubmodule p A L ↔ Additive.toMul x ∈ L := Iff.rfl

def subgroupEquivSubmodule (L : Subgroup A) : L ≃ ↥(subgroupOrderIsoSubmodule p A L) where
  toFun x := ⟨Additive.ofMul x.1, x.2⟩
  invFun x := ⟨Additive.toMul x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_subgroupOrderIsoSubmodule (L : Subgroup A) :
    Nat.card ↥(subgroupOrderIsoSubmodule p A L) = Nat.card L :=
  (Nat.card_congr (subgroupEquivSubmodule L)).symm

theorem finrank_subgroupOrderIsoSubmodule [Fact p.Prime] [Finite A] {d : ℕ} (L : Subgroup A)
    (hL : Nat.card L = p ^ d) : finrank (ZMod p) ↥(subgroupOrderIsoSubmodule p A L) = d := by
  have : Finite (Additive A) := ‹Finite A›
  exact finrank_eq_of_natCard_eq_pow _ (by rw [natCard_subgroupOrderIsoSubmodule, hL])

theorem map_mulAutToGL_subgroupOrderIsoSubmodule (φ : MulAut A) (L : Subgroup A) :
    Submodule.map ((mulAutToGL (p := p) φ : LinearMap.GeneralLinearGroup (ZMod p) (Additive A)) :
        Module.End (ZMod p) (Additive A)) (subgroupOrderIsoSubmodule p A L)
      = subgroupOrderIsoSubmodule p A (L.map φ) := by
  ext x
  simp only [Submodule.mem_map, mem_subgroupOrderIsoSubmodule, mulAutToGL_apply, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Additive.toMul y, hy, rfl⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨Additive.ofMul a, ha, by simpa using congrArg Additive.ofMul hax⟩

private theorem exists_map_eq_of_fixed_subgroup_aux [Fact p.Prime] [Finite A]
    {Q : Type*} [Group Q] (hQ : IsPGroup p Q) (σ : Q →* MulAut A)
    (hcard : Nat.card A = p ^ 2) (hne : ∃ (q : Q) (a : A), σ q a ≠ a)
    {Z : Subgroup A} (hZ : Nat.card Z = p) (hZfix : ∀ (q : Q), ∀ z ∈ Z, σ q z = z)
    {L₁ L₂ : Subgroup A} (h₁ : Nat.card L₁ = p) (h₂ : Nat.card L₂ = p)
    (hne₁ : L₁ ≠ Z) (hne₂ : L₂ ≠ Z) :
    ∃ q : Q, L₁.map (σ q) = L₂ := by
  have hfin' : Finite (Additive A) := ‹Finite A›
  have hV : finrank (ZMod p) (Additive A) = 2 :=
    finrank_eq_of_natCard_eq_pow _ (by rw [← hcard]; exact Nat.card_congr Additive.toMul)
  obtain ⟨q, hq⟩ := exists_map_eq_of_fixed_line hV hQ (mulAutToGL.comp σ)
    (by
      obtain ⟨q, a, ha⟩ := hne
      exact ⟨q, Additive.ofMul a, fun h => ha (Additive.ofMul.injective (by simpa using h))⟩)
    (finrank_subgroupOrderIsoSubmodule Z (by rw [hZ, pow_one]))
    (fun q v hv => by
      have hfix := hZfix q (Additive.toMul v) (mem_subgroupOrderIsoSubmodule.1 hv)
      simp only [MonoidHom.comp_apply, mulAutToGL_apply, hfix]
      rfl)
    (finrank_subgroupOrderIsoSubmodule L₁ (by rw [h₁, pow_one]))
    (finrank_subgroupOrderIsoSubmodule L₂ (by rw [h₂, pow_one]))
    (fun h => hne₁ ((subgroupOrderIsoSubmodule p A).injective h))
    (fun h => hne₂ ((subgroupOrderIsoSubmodule p A).injective h))
  refine ⟨q, (subgroupOrderIsoSubmodule p A).injective ?_⟩
  rw [← map_mulAutToGL_subgroupOrderIsoSubmodule (σ q) L₁]
  exact hq

end Glue

theorem exists_map_eq_of_fixed_subgroup {A : Type*} [CommGroup A] (hp : p.Prime)
    {Q : Type*} [Group Q] (hQ : IsPGroup p Q) (σ : Q →* MulAut A)
    (hcard : Nat.card A = p ^ 2) (hexp : ∀ a : A, a ^ p = 1)
    (hne : ∃ (q : Q) (a : A), σ q a ≠ a)
    {Z : Subgroup A} (hZ : Nat.card Z = p) (hZfix : ∀ (q : Q), ∀ z ∈ Z, σ q z = z)
    {L₁ L₂ : Subgroup A} (h₁ : Nat.card L₁ = p) (h₂ : Nat.card L₂ = p)
    (hne₁ : L₁ ≠ Z) (hne₂ : L₂ ≠ Z) :
    ∃ q : Q, L₁.map (σ q) = L₂ := by
  have := Fact.mk hp
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  let _inst : Module (ZMod p) (Additive A) := AddCommGroup.zmodModule (n := p) fun x => by
    calc p • x = Additive.ofMul ((Additive.toMul x) ^ p) := by simp
      _ = 0 := by rw [hexp]; rfl
  exact exists_map_eq_of_fixed_subgroup_aux hQ σ hcard hne hZ hZfix h₁ h₂ hne₁ hne₂

section Main

variable {R : Type*} [Group R] {E : Subgroup R}

theorem isMulCommutative_of_isMulCommutative_top {G : Type*} [Group G]
    (h : IsMulCommutative (⊤ : Subgroup G)) : IsMulCommutative G :=
  ⟨⟨fun x y => setLike_mul_comm (s := (⊤ : Subgroup G)) (Subgroup.mem_top x)
    (Subgroup.mem_top y)⟩⟩

theorem mem_iff_mem_centralizer_and_pow_eq_one_of_maximal
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E) (y : R) :
    y ∈ E ↔ (y ∈ centralizer (E : Set R) ∧ y ^ p = 1) := by
  have hEcomm := hE.prop.1
  refine ⟨fun hy => ⟨Subgroup.le_centralizer E hy, hE.prop.2 y hy⟩, fun hy => ?_⟩
  exact (setOf_pow_eq_one_centralizer_of_maximal hE).subset hy

theorem normalizer_centralizer_le_normalizer_of_maximal
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E) :
    normalizer ((centralizer (E : Set R) : Subgroup R) : Set R) ≤ normalizer (E : Set R) := by
  intro g hg
  rw [mem_normalizer_iff] at hg ⊢
  intro h
  rw [mem_iff_mem_centralizer_and_pow_eq_one_of_maximal hE,
    mem_iff_mem_centralizer_and_pow_eq_one_of_maximal hE]
  refine ⟨fun hy => ⟨(hg h).1 hy.1, ?_⟩, fun hy => ⟨(hg h).2 hy.1, ?_⟩⟩
  · rw [conj_pow, hy.2]; group
  · have h2 := hy.2; rw [conj_pow] at h2; simpa using h2

theorem exists_mem_normalizer_notMem_centralizer [Finite R] [Fact p.Prime] (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hCcomm : IsMulCommutative (centralizer (E : Set R)))
    (hRnonabelian : ¬ IsMulCommutative R) :
    ∃ g ∈ normalizer (E : Set R), g ∉ centralizer (E : Set R) := by
  have hClt : centralizer (E : Set R) < ⊤ :=
    lt_top_iff_ne_top.2 fun h =>
      hRnonabelian (isMulCommutative_of_isMulCommutative_top (h ▸ hCcomm))
  obtain ⟨g, hgN, hgC⟩ :=
    SetLike.exists_of_lt (normalizerCondition_of_isPGroup (p := p) hRp _ hClt)
  exact ⟨g, normalizer_centralizer_le_normalizer_of_maximal hE hgN, hgC⟩

theorem map_subtype_map_normalizerMonoidHom (x : ↥(normalizer (E : Set R)))
    {L : Subgroup R} (hL : L ≤ E) :
    Subgroup.map E.subtype ((L.subgroupOf E).map (E.normalizerMonoidHom x))
      = L.map (MulAut.conj (x : R)) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨(a : R), ha, by simp [MulAut.conj]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨E.normalizerMonoidHom x ⟨b, hL hb⟩, ⟨⟨b, hL hb⟩, hb, rfl⟩, by simp [MulAut.conj]⟩

theorem subgroupOf_ne_of_ne {L Z : Subgroup R} (hL : L ≤ E) (hZ : Z ≤ E) (h : L ≠ Z) :
    L.subgroupOf E ≠ Z.subgroupOf E := fun hcon => by
  rw [Subgroup.subgroupOf_inj, inf_eq_left.2 hL, inf_eq_left.2 hZ] at hcon
  exact h hcon

theorem exists_mem_normalizer_map_conj_eq [Finite R] (hp : p.Prime) (hRp : IsPGroup p R)
    (hE : Maximal (fun A : Subgroup R => IsMulCommutative A ∧ ∀ x ∈ A, x ^ p = 1) E)
    (hplane : Nat.card E = p ^ 2) (hRnonabelian : ¬ IsMulCommutative R)
    (hCcomm : IsMulCommutative (centralizer (E : Set R)))
    (hZ0 : Nat.card (centerTorsionBy R p) = p)
    {L₁ L₂ : Subgroup R} (hL₁ : L₁ ≤ E) (hL₂ : L₂ ≤ E)
    (hc₁ : Nat.card L₁ = p) (hc₂ : Nat.card L₂ = p)
    (hne₁ : L₁ ≠ centerTorsionBy R p) (hne₂ : L₂ ≠ centerTorsionBy R p) :
    ∃ g ∈ normalizer (E : Set R), L₁.map (MulAut.conj g) = L₂ := by
  have := Fact.mk hp
  have hEcomm := hE.prop.1
  let _ : CommGroup ↥E := IsMulCommutative.instCommGroup
  have hZle : centerTorsionBy R p ≤ E := centerTorsionBy_le_of_maximal hE
  obtain ⟨g₀, hg₀N, hg₀C⟩ := exists_mem_normalizer_notMem_centralizer hRp hE hCcomm hRnonabelian
  obtain ⟨q, hq⟩ := exists_map_eq_of_fixed_subgroup (A := ↥E) hp
    (Q := ↥(normalizer (E : Set R))) (hRp.to_subgroup _) E.normalizerMonoidHom
    hplane (fun a => Subtype.ext (hE.prop.2 a.1 a.2))
    (by
      refine ⟨⟨g₀, hg₀N⟩, ?_⟩
      by_contra hcon
      rw [not_exists] at hcon
      refine hg₀C (mem_centralizer_iff.2 fun h hh => ?_)
      have h1 := congrArg Subtype.val (not_ne_iff.1 (hcon ⟨h, hh⟩))
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      simp only at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm)
    (Z := (centerTorsionBy R p).subgroupOf E)
    (by rw [natCard_subgroupOf_of_le hZle, hZ0])
    (fun x z hz => by
      refine Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hzc : (z : R) ∈ center R := (mem_centerTorsionBy.1 (mem_subgroupOf.1 hz)).1
      rw [(mem_center_iff.1 hzc) (x : R)]
      group)
    (L₁ := L₁.subgroupOf E) (L₂ := L₂.subgroupOf E)
    (by rw [natCard_subgroupOf_of_le hL₁, hc₁])
    (by rw [natCard_subgroupOf_of_le hL₂, hc₂])
    (subgroupOf_ne_of_ne hL₁ hZle hne₁) (subgroupOf_ne_of_ne hL₂ hZle hne₂)
  refine ⟨(q : R), q.2, ?_⟩
  rw [← map_subtype_map_normalizerMonoidHom q hL₁, hq, Subgroup.map_subgroupOf_eq_of_le hL₂]

end Main

end

end CFSG.FeitThompson
