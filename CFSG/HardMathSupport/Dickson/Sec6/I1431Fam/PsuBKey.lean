module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHKey

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

theorem t6psub_component_cube_central (H : UnitaryPrimaryData hK.bar B x) {O : Set K[X]}
    {y g : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x)
    (hg : g ∈ supportedUnitary B x O)
    (hgy : ∀ c ∈ primaryFactors (x : Module.End K V), c ∈ O →
      ∀ v ∈ primaryComponent (x : Module.End K V) c,
        (g : Module.End K V) v = (y : Module.End K V) v)
    {ν : K} (hy3 : ∀ v, ((y ^ 3 : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = ν • v)
    {m : LinearMap.GeneralLinearGroup K V} (hm : m ∈ supportedUnitary B x O) :
    g ^ 3 * m = m * g ^ 3 := by
  have hsq := H.squarefree
  have hyc : Commute (y : Module.End K V) (x : Module.End K V) := (mem_unitaryCentralizer.mp hy).2
  have hmc : Commute (m : Module.End K V) (x : Module.End K V) := mem_gl_centralizer.mp hm.1.2
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
  refine Units.ext (ext_primaryComponent hsq fun c hc v hv => ?_)
  change ((g ^ 3 : LinearMap.GeneralLinearGroup K V) : Module.End K V)
      ((m : Module.End K V) v) =
    (m : Module.End K V) (((g ^ 3 : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
  have hmv : (m : Module.End K V) v ∈ primaryComponent (x : Module.End K V) c :=
    apply_mem_primaryComponent hmc hv
  by_cases hcO : c ∈ O
  · rw [hpowa 3 c hc hcO _ hmv, hpowa 3 c hc hcO v hv, hy3, hy3, map_smul]
  · rw [hpowo 3 c hc hcO _ hmv, hpowo 3 c hc hcO v hv]

end Component

section Key

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem t6psub_key_block (H : UnitaryPrimaryData hK.bar B x)
    (b : primaryFactors (x : Module.End K V))
    (hm2 : primaryMultiplicity (x : Module.End K V) (b : K[X]) = 2)
    {y : LinearMap.GeneralLinearGroup K V} (hy : y ∈ unitaryCentralizer B x) {ν : K}
    (hy3 : ∀ v, ((y ^ 3 : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = ν • v) :
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
  have hgF : g ∈ orbitFactor B x (b : K[X]) := hg
  have hsq : ∀ g ∈ orbitFactor B x (b : K[X]), ∃ n ∈ specialBlock B x (b : K[X]),
      ∃ z ∈ orbitFactor B x (b : K[X]), (∀ m ∈ orbitFactor B x (b : K[X]), z * m = m * z) ∧
        g ^ 2 = n * z := fun g hg => t6psuh_sq_mem H b hm2 hg
  have hb3F : ∀ m ∈ orbitFactor B x (b : K[X]), g ^ 3 * m = m * g ^ 3 := fun m hm =>
    t6psub_component_cube_central H hy hg hgy hy3 hm
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

theorem t6psub_block_key (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (B : primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B)) (i : t6psub_Idx h n B) {q : ℕ}
    (hq : 10 ≤ q) (hT : IsTypeL2 q ↥(t6psub_block B i))
    {B' : primeFormUnitary h (idGram K n)} (hcomm : (B' : GL (Fin n) K) * B = B * B')
    {ν : Kˣ} (h3 : (B' : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) ν) :
    ∃ s ∈ t6psub_block B i, ∀ m ∈ t6psub_block B i, t6psub_actSU h n B' m = s * m * s⁻¹ := by
  have e : ↥(t6psub_block B i) ≃*
      ↥(specialBlock (idForm h n) (t6psub_toLin B) (i.1 : K[X])) :=
    (Subgroup.equivMapOfInjective (t6psub_block B i) (t6psuh_toLinSU h n)
      t6psuh_toLinSU_injective).trans (MulEquiv.subgroupCongr (t6psub_map_block B H i))
  have hm2 := t6psuh_rank_two hO H (t6psuh_hq h) i.1 i.2 hq (p6_isTypeL2_of_equiv e hT)
  have hHc : t6psub_toLin B' ∈ gl_centralizer (t6psub_toLin B) := by
    show t6psub_toLin B' ∈ Subgroup.centralizer ({t6psub_toLin B} : Set _)
    rw [Subgroup.mem_centralizer_singleton_iff]
    unfold t6psub_toLin
    rw [← map_mul, ← map_mul, hcomm]
  have hy : t6psub_toLin B' ∈ unitaryCentralizer (idForm h n) (t6psub_toLin B) :=
    Subgroup.mem_inf.mpr ⟨(toLin_mem_sesqUnitaryGroup_iff _).mpr B'.2, hHc⟩
  have hy3 : ∀ v, (((t6psub_toLin B') ^ 3 : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = (ν : K) • v := by
    intro v
    have : (t6psub_toLin B') ^ 3 = Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.scalar (Fin n) ν) := by
      unfold t6psub_toLin
      rw [← map_pow, h3]
    rw [this]
    exact t6psub_glA_scalar_apply ν v
  obtain ⟨s', hs', hsm'⟩ := t6psub_key_block H i.1 hm2 hy hy3
  obtain ⟨s, rfl⟩ := t6psub_specialBlock_le_range B H i hs'
  refine ⟨s, Subgroup.mem_comap.mpr hs', fun m hm => ?_⟩
  apply t6psuh_toLinSU_injective
  have hk := hsm' _ (Subgroup.mem_comap.mp hm)
  rw [map_mul, map_mul, map_inv, ← hk]
  show Matrix.GeneralLinearGroup.toLin ((B' : GL (Fin n) K) * (m : GL (Fin n) K) *
    (B' : GL (Fin n) K)⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

end Blocks

end CFSG.HardMathSupport.Dickson.Sec6.I1431
