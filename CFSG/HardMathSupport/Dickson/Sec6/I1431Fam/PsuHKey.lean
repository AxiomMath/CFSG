module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHRank
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHModel

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

section Component

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem t6psuh_conj_eq (H : UnitaryPrimaryData hK.bar B x) {O : Set K[X]}
    {y g : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x)
    (hg : g ∈ supportedUnitary B x O)
    (hgy : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) c,
        (g : Module.End K V) v = (y : Module.End K V) v)
    {m : LinearMap.GeneralLinearGroup K V} (hm : m ∈ supportedUnitary B x O) :
    y * m * y⁻¹ = g * m * g⁻¹ := by
  have hsq := H.squarefree
  obtain ⟨u, hu⟩ : ∃ u : LinearMap.GeneralLinearGroup K V, u = g⁻¹ * y := ⟨_, rfl⟩
  have huc : Commute (u : Module.End K V) (x : Module.End K V) := by
    rw [hu]
    exact mem_gl_centralizer.mp (mul_mem (inv_mem hg.1.2) hy.2)
  have hmc : Commute (m : Module.End K V) (x : Module.End K V) := mem_gl_centralizer.mp hm.1.2
  have hinv : ∀ w, ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      ((g : Module.End K V) w) = w := fun w => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  have hucomm : u * m = m * u := by
    refine Units.ext (ext_primaryComponent hsq fun c hc v hv => ?_)
    change (u : Module.End K V) ((m : Module.End K V) v) =
      (m : Module.End K V) ((u : Module.End K V) v)
    by_cases hcO : c ∈ O
    · have hu1 : ∀ w ∈ primaryComponent (x : Module.End K V) c, (u : Module.End K V) w = w := by
        intro w hw
        rw [hu, Units.val_mul, Module.End.mul_apply, ← hgy c hc hcO w hw, hinv]
      have hmv : (m : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
        apply_mem_primaryComponent hmc hv
      rw [hu1 _ hmv, hu1 v hv]
    · have hm1 : ∀ w ∈ primaryComponent (x : Module.End K V) c, (m : Module.End K V) w = w :=
        fun w hw => hm.2 c hc hcO w hw
      have huv : (u : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
        apply_mem_primaryComponent huc hv
      rw [hm1 v hv, hm1 _ huv]
  have hy_eq : y = g * u := by rw [hu]; simp
  calc y * m * y⁻¹ = g * (u * m * u⁻¹) * g⁻¹ := by rw [hy_eq]; group
    _ = g * m * g⁻¹ := by rw [hucomm]; group

theorem t6psuh_component_pow_three (H : UnitaryPrimaryData hK.bar B x) {O : Set K[X]}
    {y g : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x)
    (hg : g ∈ supportedUnitary B x O)
    (hgy : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) c,
        (g : Module.End K V) v = (y : Module.End K V) v)
    (hy3 : y ^ 3 = 1) : g ^ 3 = 1 := by
  have hsq := H.squarefree
  have hyc : Commute (y : Module.End K V) (x : Module.End K V) := (mem_unitaryCentralizer.mp hy).2
  have hpowa : ∀ k : ℕ, ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O →
      ∀ w ∈ primaryComponent (x : Module.End K V) c,
        ((g ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w =
          ((y ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w := by
    intro k
    induction k with
    | zero => intro c _ _ w _; rfl
    | succ k ih =>
      intro c hc hcO w hw
      have hbw : ((y ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w ∈
          primaryComponent (x : Module.End K V) c := by
        have hck : Commute (((y ^ k : LinearMap.GeneralLinearGroup K V)) : Module.End K V)
            (x : Module.End K V) := by
          rw [Units.val_pow_eq_pow_val]
          exact hyc.pow_left k
        exact apply_mem_primaryComponent hck hw
      rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih c hc hcO w hw, pow_succ',
        Units.val_mul, Module.End.mul_apply]
      exact hgy c hc hcO _ hbw
  have hpowo : ∀ k : ℕ, ∀ c ∈ primaryFactors (x : Module.End K V), c ∉ O →
      ∀ w ∈ primaryComponent (x : Module.End K V) c,
        ((g ^ k : LinearMap.GeneralLinearGroup K V) : Module.End K V) w = w := by
    intro k
    induction k with
    | zero => intro c _ _ w _; rfl
    | succ k ih =>
      intro c hc hcO w hw
      rw [pow_succ', Units.val_mul, Module.End.mul_apply, ih c hc hcO w hw]
      exact hg.2 c hc hcO w hw
  refine eq_one_of_forall_apply_eq hsq fun c hc w hw => ?_
  by_cases hcO : c ∈ O
  · rw [hpowa 3 c hc hcO w hw, hy3]
    rfl
  · exact hpowo 3 c hc hcO w hw

end Component

section Key

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem t6psuh_key_block (H : UnitaryPrimaryData hK.bar B x)
    (b : primaryFactors (x : Module.End K V))
    (hm2 : primaryMultiplicity (x : Module.End K V) (b : K[X]) = 2)
    {y : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x) (hy3 : y ^ 3 = 1) :
    ∃ s ∈ specialBlock B x (b : K[X]),
      ∀ m ∈ specialBlock B x (b : K[X]), y * m * y⁻¹ = s * m * s⁻¹ := by
  have hO : ∀ c ∈ primaryFactors (x : Module.End K V),
      c ∈ ({(b : K[X]), dualPoly hK.bar (b : K[X])} : Set K[X]) →
        dualPoly hK.bar c ∈ ({(b : K[X]), dualPoly hK.bar (b : K[X])} : Set K[X]) := by
    intro c hc hcO
    rcases hcO with rfl | hcO
    · exact Or.inr rfl
    · rw [Set.mem_singleton_iff] at hcO
      subst hcO
      exact Or.inl (dualPoly_dualPoly_of_mem H b.2)
  obtain ⟨g, hg, hgy⟩ := exists_component H hO hy
  have hg3 : g ^ 3 = 1 := t6psuh_component_pow_three H hy hg hgy hy3
  have hgF : g ∈ orbitFactor B x (b : K[X]) := hg
  have hsq : ∀ g ∈ orbitFactor B x (b : K[X]), ∃ n ∈ specialBlock B x (b : K[X]),
      ∃ z ∈ orbitFactor B x (b : K[X]), (∀ m ∈ orbitFactor B x (b : K[X]), z * m = m * z) ∧
        g ^ 2 = n * z := fun g hg => t6psuh_sq_mem H b hm2 hg
  have hb3F : ∀ m ∈ orbitFactor B x (b : K[X]), g ^ 3 * m = m * g ^ 3 := fun m _ => by
    rw [hg3, one_mul, mul_one]
  obtain ⟨s, hs, hsm⟩ := key_of_sq_mem (F := orbitFactor B x (b : K[X]))
    (N := specialBlock B x (b : K[X])) (b := g) specialBlock_le_orbitFactor hsq hgF hb3F
  refine ⟨s, hs, fun m hm => ?_⟩
  have hmF : m ∈ supportedUnitary B x {(b : K[X]), dualPoly hK.bar (b : K[X])} :=
    specialBlock_le_orbitFactor hm
  rw [t6psuh_conj_eq H hy hg hgy hmF]
  exact hsm m hm

end Key

section Blocks

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem psuBlock_key (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hℓ3 : ℓ ≠ 3) (a : ↥(gramSU h (idGram K n))) (ha3 : a ^ 3 = 1) (i : PsuIdx h n a) {q : ℕ}
    (hq : 10 ≤ q) (hT : IsTypeL2 q ↥(psuBlock h n a i)) :
    ∀ b ∈ Subgroup.centralizer ({a} : Set ↥(gramSU h (idGram K n))), b ^ 3 = 1 →
      ∃ s ∈ psuBlock h n a i, ∀ m ∈ psuBlock h n a i, b * m * b⁻¹ = s * m * s⁻¹ := by
  intro b hb hb3
  have H := t6psuh_primaryData hℓ3 a ha3
  have e : ↥(psuBlock h n a i) ≃*
      ↥(specialBlock (idForm h n) (t6psuh_toLinSU h n a) (i.1 : K[X])) :=
    (Subgroup.equivMapOfInjective (psuBlock h n a i) (t6psuh_toLinSU h n)
      t6psuh_toLinSU_injective).trans (MulEquiv.subgroupCongr (t6psuh_map_psuBlock hℓ3 a ha3 i))
  have hm2 := t6psuh_rank_two hO H (t6psuh_hq h) i.1 i.2 hq (p6_isTypeL2_of_equiv e hT)
  have hy := t6psuh_toLinSU_mem_unitaryCentralizer a hb
  have hy3 : (t6psuh_toLinSU h n b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  obtain ⟨s', hs', hsm'⟩ := t6psuh_key_block H i.1 hm2 hy hy3
  obtain ⟨s, rfl⟩ := t6psuh_specialBlock_le_range hℓ3 a ha3 i hs'
  refine ⟨s, Subgroup.mem_comap.mpr hs', fun m hm => ?_⟩
  apply t6psuh_toLinSU_injective
  rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  exact hsm' _ (Subgroup.mem_comap.mp hm)

end Blocks

end CFSG.HardMathSupport.Dickson.Sec6.I1431
