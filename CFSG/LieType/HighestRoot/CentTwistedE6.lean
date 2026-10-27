module

public import CFSG.LieType.HighestRoot.CentIsogenyE6E7
public import CFSG.LieType.Steinberg.TwistedE6.RankOne
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import CFSG.LieType.Steinberg.Exceptional.Fields
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.CurtisTits MinData.Valid

abbrev e6one : Fin (Tag.rank .E6) := ⟨1, by decide⟩

@[expose] def witE6one : List ℕ :=
  [8948104, 0, 8947849, 0, 9996424, 9013384, 8948104, 8947849, 0, 0, 8947849, 0, 0, 0, 9996424,
    9013384, 9013384, 8947849, 0, 0, 0, 0, 0, 0, 0, 0, 9013384, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 8947849, 0, 0, 0, 0, 8947849, 0, 8947849, 0, 8947849, 8947849, 0, 8948104,
    8947849, 8947849, 8947849, 8948104, 8947849, 8948104, 8947849, 8947849, 8948104, 8947849,
    8948104, 8948104, 0, 0, 0, 0]

theorem isolatedCheck_E6_one : isolatedCheck .E6 e6one witE6one = true := by decide +kernel

theorem rhoPerm_e6one : rhoPerm e6one = e6one := rfl

theorem orbitMap_e6one : orbitMap e6one = ⟨0, by decide⟩ := rfl

variable {k : Type} [Field k] (θ : k →+* k)

noncomputable abbrev rankOneE6one
    (k : Type) [Field k] :
    Subgroup (e6Data_valid.minGroup k) :=
  rankOne (e6Data_valid.rootGroup k) e6one

theorem slHom_injective
    (i : Fin (Tag.rank .E6)) :
    Function.Injective (e6Data_valid.slHom k i) := by
  intro M N h
  have h' := congrArg Units.val h
  rw [slHom_val, slHom_val] at h'
  exact Subtype.ext (e6Data_valid.blockOp_injective k i h')

theorem slHom_sl2Upper
    (c : k) :
    e6Data_valid.slHom k e6one (CFSG.LieType.Steinberg.sl2Upper c) =
      (e6Data_valid.xm k (Pi.single e6one 1) c : e6Data_valid.minGroup k) := by
  refine Units.ext ?_
  rw [slHom_val, CFSG.LieType.Steinberg.coe_sl2Upper, e6Data_valid.blockOp_upper]
  exact (e6Data_valid.endo_xm k _ c).symm

theorem slHom_sl2Lower
    (c : k) :
    e6Data_valid.slHom k e6one (CFSG.LieType.Steinberg.sl2Lower c) =
      (e6Data_valid.xm k (-Pi.single e6one 1) c : e6Data_valid.minGroup k) := by
  refine Units.ext ?_
  rw [slHom_val, CFSG.LieType.Steinberg.coe_sl2Lower, e6Data_valid.blockOp_lower]
  exact (e6Data_valid.endo_xm k _ c).symm

theorem exists_slHom_sigma
    {y : e6Data_valid.minGroup k} (hy : y ∈ rankOneE6one k) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) k,
      (y : (Module.End k (Fin e6Data.d →₀ k))ˣ) = e6Data_valid.slHom k e6one M ∧
        ((sigma k θ y : e6Data_valid.minGroup k) : (Module.End k (Fin e6Data.d →₀ k))ˣ) =
          e6Data_valid.slHom k e6one (Matrix.SpecialLinearGroup.map θ M) := by
  set S : Subgroup (e6Data_valid.minGroup k) :=
    { carrier := {y | ∃ M : Matrix.SpecialLinearGroup (Fin 2) k,
        (y : (Module.End k (Fin e6Data.d →₀ k))ˣ) = e6Data_valid.slHom k e6one M ∧
          ((sigma k θ y : e6Data_valid.minGroup k) : (Module.End k (Fin e6Data.d →₀ k))ˣ) =
            e6Data_valid.slHom k e6one (Matrix.SpecialLinearGroup.map θ M)}
      mul_mem' := by
        rintro a b ⟨M, hM, hσM⟩ ⟨N, hN, hσN⟩
        exact ⟨M * N, by rw [Subgroup.coe_mul, hM, hN, map_mul],
          by rw [map_mul, Subgroup.coe_mul, hσM, hσN, map_mul, map_mul]⟩
      one_mem' := ⟨1, by rw [map_one]; rfl, by rw [map_one, map_one, map_one]; rfl⟩
      inv_mem' := by
        rintro a ⟨M, hM, hσM⟩
        exact ⟨M⁻¹, by rw [Subgroup.coe_inv, hM, map_inv],
          by rw [map_inv, Subgroup.coe_inv, hσM, map_inv, map_inv]⟩ }
  have hle : rankOneE6one k ≤ S := by
    refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
      refine ⟨CFSG.LieType.Steinberg.sl2Upper c, (slHom_sl2Upper c).symm, ?_⟩
      rw [sigma_xm_single, rhoPerm_e6one]
      have e : Matrix.SpecialLinearGroup.map θ (CFSG.LieType.Steinberg.sl2Upper c) =
          CFSG.LieType.Steinberg.sl2Upper (θ c) := by
        ext p q
        fin_cases p <;> fin_cases q <;> simp [CFSG.LieType.Steinberg.coe_sl2Upper]
      rw [e, slHom_sl2Upper]
    · intro x hx
      obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hx
      refine ⟨CFSG.LieType.Steinberg.sl2Lower c, (slHom_sl2Lower c).symm, ?_⟩
      rw [sigma_xm_neg_single, rhoPerm_e6one]
      have e : Matrix.SpecialLinearGroup.map θ (CFSG.LieType.Steinberg.sl2Lower c) =
          CFSG.LieType.Steinberg.sl2Lower (θ c) := by
        ext p q
        fin_cases p <;> fin_cases q <;> simp [CFSG.LieType.Steinberg.coe_sl2Lower]
      rw [e, slHom_sl2Lower]
  exact hle hy

noncomputable abbrev rankOneTwE6
    (k : Type) [Field k] (θ : k →+* k) :
    Subgroup (fixedGroup k θ) :=
  rankOne (twistedRootGroup k θ) ⟨0, by decide⟩

theorem exists_xm_single_mem_rankOneTwE6
    {c : k} (hc : θ c = c) :
    ∃ u ∈ rankOneTwE6 k θ,
      (u : e6Data_valid.minGroup k) = e6Data_valid.xm k (Pi.single e6one 1) c := by
  have hfix : rho (Pi.single e6one 1) = Pi.single e6one 1 := by rw [rho_single, rhoPerm_e6one]
  have hmem := xFixed_mem θ (isRoot_single _ e6one) hfix c hc
  have hp : twistedRootGroup k θ (proj (Pi.single e6one 1)) =
      twistedRootGroup k θ (Pi.single ⟨0, by decide⟩ 1) := by
    rw [proj_single, orbitMap_e6one]
  rw [hp] at hmem
  exact ⟨_, Subgroup.mem_sup_left hmem, rfl⟩

theorem exists_xm_neg_single_mem_rankOneTwE6
    {c : k} (hc : θ c = c) :
    ∃ u ∈ rankOneTwE6 k θ,
      (u : e6Data_valid.minGroup k) = e6Data_valid.xm k (-Pi.single e6one 1) c := by
  have hfix : rho (-Pi.single e6one 1) = -Pi.single e6one 1 := by
    rw [rho_neg_single, rhoPerm_e6one]
  have hmem := xFixed_mem θ (isRoot_neg_single _ e6one) hfix c hc
  have hp : twistedRootGroup k θ (proj (-Pi.single e6one 1)) =
      twistedRootGroup k θ (-Pi.single ⟨0, by decide⟩ 1) := by
    rw [proj_neg_single, orbitMap_e6one]
  rw [hp] at hmem
  exact ⟨_, Subgroup.mem_sup_right hmem, rfl⟩

theorem mem_rankOneTwE6_of_mem
    {g : fixedGroup k θ}
    (hg : (g : e6Data_valid.minGroup k) ∈ rankOneE6one k) : g ∈ rankOneTwE6 k θ := by
  obtain ⟨M, hM, hσM⟩ := exists_slHom_sigma θ hg
  have hfixM : Matrix.SpecialLinearGroup.map θ M = M := by
    apply slHom_injective e6one
    rw [← hσM, ← hM, (mem_fixedGroup θ).1 g.2]
  have hent : ∀ p q, θ ((M : Matrix (Fin 2) (Fin 2) k) p q) = (M : Matrix (Fin 2) (Fin 2) k) p q :=
    fun p q => congrArg (fun N : Matrix.SpecialLinearGroup (Fin 2) k =>
      (N : Matrix (Fin 2) (Fin 2) k) p q) hfixM
  let M' : Matrix (Fin 2) (Fin 2) (CFSG.LieType.Steinberg.TwistedD4.fixedField θ) := fun p q =>
    ⟨(M : Matrix (Fin 2) (Fin 2) k) p q, hent p q⟩
  have hdet : M'.det = 1 := by
    apply Subtype.ext
    have h1 : ((M'.det : CFSG.LieType.Steinberg.TwistedD4.fixedField θ) : k) =
        (M : Matrix (Fin 2) (Fin 2) k).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]
      rfl
    rw [h1, M.2]
    rfl
  set M'' : Matrix.SpecialLinearGroup (Fin 2) (CFSG.LieType.Steinberg.TwistedD4.fixedField θ) :=
    ⟨M', hdet⟩ with hM''
  have hmap : Matrix.SpecialLinearGroup.map
      (CFSG.LieType.Steinberg.TwistedD4.fixedField θ).subtype M'' = M := by
    ext p q
    rfl
  obtain ⟨e, a, b, c, he⟩ := CFSG.LieType.Steinberg.Adjoint.sl2_eq_prod M''
  have hU : ∀ d : CFSG.LieType.Steinberg.TwistedD4.fixedField θ,
      Matrix.SpecialLinearGroup.map (CFSG.LieType.Steinberg.TwistedD4.fixedField θ).subtype
        (CFSG.LieType.Steinberg.sl2Upper d) = CFSG.LieType.Steinberg.sl2Upper (d : k) := by
    intro d
    ext p q
    fin_cases p <;> fin_cases q <;> simp [CFSG.LieType.Steinberg.coe_sl2Upper]
  have hL : ∀ d : CFSG.LieType.Steinberg.TwistedD4.fixedField θ,
      Matrix.SpecialLinearGroup.map (CFSG.LieType.Steinberg.TwistedD4.fixedField θ).subtype
        (CFSG.LieType.Steinberg.sl2Lower d) = CFSG.LieType.Steinberg.sl2Lower (d : k) := by
    intro d
    ext p q
    fin_cases p <;> fin_cases q <;> simp [CFSG.LieType.Steinberg.coe_sl2Lower]
  obtain ⟨ue, hue, hue'⟩ := exists_xm_neg_single_mem_rankOneTwE6 θ e.2
  obtain ⟨ua, hua, hua'⟩ := exists_xm_single_mem_rankOneTwE6 θ a.2
  obtain ⟨ub, hub, hub'⟩ := exists_xm_neg_single_mem_rankOneTwE6 θ b.2
  obtain ⟨uc, huc, huc'⟩ := exists_xm_single_mem_rankOneTwE6 θ c.2
  have hg' : g = ue * ua * ub * uc := by
    apply Subtype.ext
    apply Subtype.ext
    have h := hM
    rw [← hmap, he] at h
    simp only [map_mul, hU, hL, slHom_sl2Upper, slHom_sl2Lower] at h
    simp only [Subgroup.coe_mul, hue', hua', hub', huc']
    exact h
  rw [hg']
  exact mul_mem (mul_mem (mul_mem hue hua) hub) huc

theorem coe_mem_rankOneE6one
    {u : fixedGroup k θ} (hu : u ∈ rankOneTwE6 k θ) :
    (u : e6Data_valid.minGroup k) ∈ rankOneE6one k := by
  have hle : rankOneTwE6 k θ ≤ (rankOneE6one k).comap (fixedGroup k θ).subtype := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · have hfix : rho (Pi.single e6one 1) = Pi.single e6one 1 := by
        rw [rho_single, rhoPerm_e6one]
      obtain ⟨c, -, hxc⟩ := (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ e6one)
        (by rw [proj_single, orbitMap_e6one]) hfix x).1 hx
      rw [Subgroup.mem_comap, Subgroup.coe_subtype, hxc]
      exact Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup k _ _)
    · have hfix : rho (-Pi.single e6one 1) = -Pi.single e6one 1 := by
        rw [rho_neg_single, rhoPerm_e6one]
      obtain ⟨c, -, hxc⟩ := (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ e6one)
        (by rw [proj_neg_single, orbitMap_e6one]) hfix x).1 hx
      rw [Subgroup.mem_comap, Subgroup.coe_subtype, hxc]
      exact Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup k _ _)
  exact hle hu

theorem centralizer_le_normalizer_twistedE6
    [Finite k] (hK : ringChar k ≠ 2)
    {z : fixedGroup k θ} (hz : z ∈ rankOneTwE6 k θ) (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (fixedGroup k θ)) ≤
      Subgroup.normalizer (rankOneTwE6 k θ : Set (fixedGroup k θ)) := by
  have h2' : orderOf (z : e6Data_valid.minGroup k) = 2 := by rwa [Subgroup.orderOf_coe]
  have hCZ := (centralizerCondition_e6_of_check k hK isolatedCheck_E6_one
    (z : e6Data_valid.minGroup k) (coe_mem_rankOneE6one θ hz) h2').1
  intro g hg
  have hg' : (g : e6Data_valid.minGroup k) ∈
      Subgroup.centralizer ({(z : e6Data_valid.minGroup k)} : Set (e6Data_valid.minGroup k)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have hN := hCZ hg'
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    refine mem_rankOneTwE6_of_mem θ ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 hN _).1 (coe_mem_rankOneE6one θ hu)
  · intro hu
    have h := coe_mem_rankOneE6one θ hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact mem_rankOneTwE6_of_mem θ ((Subgroup.mem_normalizer_iff.1 hN _).2 h)

end CFSG.LieType.HighestRoot
