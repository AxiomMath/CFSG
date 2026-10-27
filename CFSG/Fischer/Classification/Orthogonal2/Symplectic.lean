module

public import CFSG.Fischer.Classification.Recognition.SymOOrth
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightTorBase
public import CFSG.Fischer.Classification.Recognition.CaseR3

public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module CFSG.LargeExtraspecial
open scoped commutatorElement

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

@[expose] noncomputable def spT (hf : f.IsAlt) (a : U) : TauCeti.BilinForm.isometryGroup f :=
  ⟨spTransvection f hf a, spTransvection_mem_isometryGroup hf a⟩

theorem spT_apply (hf : f.IsAlt) (a x : U) :
    ((spT hf a : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x = x + f x a • a :=
  rfl

theorem spT_mul_self (hf : f.IsAlt) (a : U) : spT hf a * spT hf a = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  change (x + f x a • a) + f (x + f x a • a) a • a = x
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hf.self_eq_zero,
    smul_zero, add_zero, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem spT_conj (hf : f.IsAlt) (σ : TauCeti.BilinForm.isometryGroup f) (a : U) :
    σ * spT hf a * σ⁻¹ = spT hf ((σ : U ≃ₗ[ZMod 2] U) a) := by
  refine Subtype.ext (LinearEquiv.ext fun x => ?_)
  have hσ := TauCeti.BilinForm.mem_isometryGroup_iff.mp σ.2
  change (σ : U ≃ₗ[ZMod 2] U) (((σ : U ≃ₗ[ZMod 2] U)⁻¹ x) +
      f ((σ : U ≃ₗ[ZMod 2] U)⁻¹ x) a • a) = x + f x ((σ : U ≃ₗ[ZMod 2] U) a) •
        (σ : U ≃ₗ[ZMod 2] U) a
  have h1 : f ((σ : U ≃ₗ[ZMod 2] U)⁻¹ x) a = f x ((σ : U ≃ₗ[ZMod 2] U) a) := by
    have := hσ ((σ : U ≃ₗ[ZMod 2] U)⁻¹ x) a
    rw [CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply'] at this
    exact this.symm
  rw [map_add, map_smul, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply', h1]

theorem eq_of_spT_eq (hf : f.IsAlt) (hnd : f.Nondegenerate) {a b : U} (ha : a ≠ 0)
    (h : spT hf a = spT hf b) : a = b := by
  obtain ⟨x, hx⟩ : ∃ x, f x a ≠ 0 := by
    by_contra! h'
    exact ha (hnd.2 a h')
  have hx1 : f x a = 1 := CFSG.ClassicalGroups.Orthogonal.zmod_two_eq_one_of_ne_zero hx
  have key := congrArg (fun σ : TauCeti.BilinForm.isometryGroup f =>
    (σ : U ≃ₗ[ZMod 2] U) x) h
  simp only [spT_apply, hx1, one_smul] at key
  have key' := add_left_cancel key
  rcases Recognition.SymO.zmod_two_eq_zero_or_eq_one (f x b) with h0 | h1
  · rw [h0, zero_smul] at key'
    exact absurd key' ha
  · rwa [h1, one_smul] at key'

theorem spT_mul_spT_mul_spT (hf : f.IsAlt) {a b : U} (hab : f a b = 1) :
    spT hf a * spT hf b * spT hf a = spT hf (a + b) := by
  have h := spT_conj hf (spT hf a) b
  rw [show (spT hf a)⁻¹ = spT hf a from inv_eq_of_mul_eq_one_left (spT_mul_self hf a)] at h
  rw [h, spT_apply, OrthoF2.isAlt_symm hf, hab, one_smul, add_comm]

theorem center_isometryGroup_eq_bot (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    Subgroup.center (TauCeti.BilinForm.isometryGroup f) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  refine Subtype.ext (LinearEquiv.ext fun a => ?_)
  by_cases ha : a = 0
  · rw [ha, map_zero, map_zero]
  have hc : σ * spT hf a * σ⁻¹ = spT hf a := by
    rw [(Subgroup.mem_center_iff.mp hσ (spT hf a)).symm, mul_inv_cancel_right]
  rw [spT_conj] at hc
  have hσa := eq_of_spT_eq hf hnd
    (by
      intro h0
      apply ha
      exact (LinearEquiv.map_eq_zero_iff _).mp h0) hc
  rw [hσa]
  rfl

theorem spT_mul_spT_mem_commutator (hf : f.IsAlt) {a b : U} (hab : f a b = 1) :
    spT hf a * spT hf b ∈ commutator (TauCeti.BilinForm.isometryGroup f) := by
  have hinv : ∀ c : U, (spT hf c)⁻¹ = spT hf c := fun c =>
    inv_eq_of_mul_eq_one_left (spT_mul_self hf c)
  have hba : f b a = 1 := by rw [OrthoF2.isAlt_symm hf]; exact hab
  have h3 : (spT hf a * spT hf b) ^ 3 = 1 := by
    have e1 := spT_mul_spT_mul_spT hf hab
    have e2 := spT_mul_spT_mul_spT hf hba
    rw [add_comm] at e2
    calc (spT hf a * spT hf b) ^ 3 = (spT hf a * spT hf b * spT hf a) *
          (spT hf b * spT hf a * spT hf b) := by
            rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, sq]
            simp only [mul_assoc]
      _ = 1 := by rw [e1, e2, spT_mul_self]
  have h2 : (spT hf a * spT hf b) ^ 2 = ⁅spT hf a, spT hf b⁆ := by
    rw [commutatorElement_def, hinv, hinv]
    simp only [sq, mul_assoc]
  have hmem : (spT hf a * spT hf b) ^ 2 ∈ commutator (TauCeti.BilinForm.isometryGroup f) := by
    rw [h2, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hx : spT hf a * spT hf b = ((spT hf a * spT hf b) ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  rw [hx]
  exact Subgroup.pow_mem _ hmem 2

theorem exists_spT_chain [FiniteDimensional (ZMod 2) U] (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) U) :
    ∃ a b c : U, f a b = 1 ∧ f b c = 1 ∧ f a c = 0 ∧ a ≠ c := by
  have hpos : 0 < finrank (ZMod 2) U := by omega
  obtain ⟨a, ha⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  obtain ⟨⟨b, hab⟩, hsplit⟩ :=
    CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting hf hnd ha
  obtain ⟨-, -, hperp, -, -, hdim⟩ := hsplit b hab
  have hpos' : 0 < finrank (ZMod 2) (f.orthogonal (Submodule.span (ZMod 2) {a, b})) := by
    omega
  obtain ⟨e, he⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos'
  have hea : f e a = 0 := (hperp e).mp e.2 a (Submodule.subset_span (by simp))
  have heb : f e b = 0 := (hperp e).mp e.2 b (Submodule.subset_span (by simp))
  have he0 : (e : U) ≠ 0 := fun h => he (Subtype.ext h)
  refine ⟨a, b, a + e, hab, ?_, ?_, ?_⟩
  · rw [map_add, OrthoF2.isAlt_symm hf b a, hab, OrthoF2.isAlt_symm hf b e, heb, add_zero]
  · rw [map_add, hf.self_eq_zero, OrthoF2.isAlt_symm hf a e, hea, add_zero]
  · intro h
    apply he0
    have := congrArg (fun x => x - a) h
    simpa using this.symm

theorem spT_apply_of_eq_zero (hf : f.IsAlt) {a x : U} (h : f x a = 0) :
    ((spT hf a : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x = x := by
  rw [spT_apply, h, zero_smul, add_zero]

theorem spT_apply_of_eq_one (hf : f.IsAlt) {a x : U} (h : f x a = 1) :
    ((spT hf a : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) x = x + a := by
  rw [spT_apply, h, one_smul]

theorem nonabelian_commutator_isometryGroup [FiniteDimensional (ZMod 2) U] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) (h4 : 4 ≤ finrank (ZMod 2) U) :
    ∃ x y : commutator (TauCeti.BilinForm.isometryGroup f), x * y ≠ y * x := by
  obtain ⟨a, b, c, hab, hbc, hac, hne⟩ := exists_spT_chain hf hnd h4
  refine ⟨⟨_, spT_mul_spT_mem_commutator hf hab⟩, ⟨_, spT_mul_spT_mem_commutator hf hbc⟩, ?_⟩
  intro h
  have h' := congrArg (fun z : commutator (TauCeti.BilinForm.isometryGroup f) =>
    (z : TauCeti.BilinForm.isometryGroup f)) h
  simp only [Subgroup.coe_mul] at h'
  have hba : f b a = 1 := by rw [OrthoF2.isAlt_symm hf]; exact hab
  have hxy : spT hf a * spT hf b * (spT hf b * spT hf c) = spT hf a * spT hf c := by
    rw [mul_assoc, ← mul_assoc (spT hf b), spT_mul_self, one_mul]
  have hyx : spT hf b * spT hf c * (spT hf a * spT hf b) =
      spT hf (b + c) * spT hf (b + a) := by
    rw [← spT_mul_spT_mul_spT hf hbc, ← spT_mul_spT_mul_spT hf hba]
    calc spT hf b * spT hf c * (spT hf a * spT hf b)
        = spT hf b * spT hf c * (spT hf b * spT hf b) * spT hf a * spT hf b := by
          rw [spT_mul_self, mul_one]; group
      _ = spT hf b * spT hf c * spT hf b * (spT hf b * spT hf a * spT hf b) := by group
  rw [hxy, hyx] at h'
  have h2 := congrArg (fun z : TauCeti.BilinForm.isometryGroup f => (z : U ≃ₗ[ZMod 2] U) a) h'
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply] at h2
  have hz : ∀ z : U, z + z = 0 := fun z => by
    rw [← two_smul (ZMod 2) z, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have e1 := spT_apply_of_eq_zero hf hac
  have e2 := spT_apply_of_eq_zero hf (hf.self_eq_zero a)
  have e3 : ((spT hf (b + a) : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) a = b := by
    rw [spT_apply_of_eq_one hf (a := b + a) (x := a)
        (by rw [map_add, hf.self_eq_zero, add_zero]; exact hab),
      add_comm b a, ← add_assoc, hz, zero_add]
  have e4 : ((spT hf (b + c) : TauCeti.BilinForm.isometryGroup f) : U ≃ₗ[ZMod 2] U) b = c := by
    rw [spT_apply_of_eq_one hf (a := b + c) (x := b)
        (by rw [map_add, hf.self_eq_zero, zero_add]; exact hbc),
      ← add_assoc, hz, zero_add]
  rw [e1, e2, e3, e4] at h2
  exact hne h2

theorem isSimpleGroup_commutator_isometryGroup [FiniteDimensional (ZMod 2) U] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) {k : ℕ} (hk : finrank (ZMod 2) U = 2 * k) (hk2 : 2 ≤ k) :
    IsSimpleGroup (commutator (TauCeti.BilinForm.isometryGroup f)) := by
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · obtain rfl : k = 2 := by omega
    obtain ⟨k', b, hk', hb⟩ :=
      CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis f hf hnd
    obtain rfl : k' = 2 := by omega
    let e : TauCeti.BilinForm.isometryGroup f ≃* CFSG.Assembly.LowTwoRank.StatedSp 2 (ZMod 2) :=
      (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b f
        hb).trans
        (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm)
    haveI : IsSimpleGroup (commutator (CFSG.Assembly.LowTwoRank.StatedSp 2 (ZMod 2))) :=
      CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_commutator_statedSp_two
        (Nat.card_zmod 2)
    exact Recognition.R3.isSimpleGroup_commutator_of_mulEquiv e.symm
  · haveI hS : IsSimpleGroup (TauCeti.BilinForm.isometryGroup f) :=
      Recognition.SymO.isSimpleGroup_isometryGroup f hf hnd hk hge
    have htop : commutator (TauCeti.BilinForm.isometryGroup f) = ⊤ := by
      refine (hS.eq_bot_or_eq_top_of_normal _).resolve_left fun hbot => ?_
      obtain ⟨x, y, hxy⟩ := nonabelian_commutator_isometryGroup hf hnd (by omega)
      have h1 : ∀ z : commutator (TauCeti.BilinForm.isometryGroup f), z = 1 := fun z =>
        Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ z.2))
      exact hxy (by rw [h1 x, h1 y])
    exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup

end CFSG.Fischer.Classification.Orth2
