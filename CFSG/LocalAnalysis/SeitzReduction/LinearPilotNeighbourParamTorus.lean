module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.RankThree.PartOne (linearSubfieldInclusion)

section Descend

variable {E Q : Type*} [Group E] [Group Q]

theorem ker_eq_center_of_surjective_of_center_eq_bot {p : E →* Q} (hp : Function.Surjective p)
    (hpker : p.ker ≤ center E) (hQ : center Q = ⊥) : p.ker = center E := by
  refine le_antisymm hpker fun z hz => ?_
  have hpz : p z ∈ center Q := by
    rw [mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := hp q
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]
  rw [hQ, mem_bot] at hpz
  exact hpz

@[expose] noncomputable def descendCenterHom (p : E →* Q) (hp : Function.Surjective p) (γ : E →* E)
    (hγ : p.ker ≤ (p.comp γ).ker) : Q →* Q :=
  p.liftOfSurjective hp ⟨p.comp γ, hγ⟩

theorem descendCenterHom_apply (p : E →* Q) (hp : Function.Surjective p) (γ : E →* E)
    (hγ : p.ker ≤ (p.comp γ).ker) (y : E) : descendCenterHom p hp γ hγ (p y) = p (γ y) :=
  p.liftOfRightInverse_comp_apply _ _ ⟨p.comp γ, hγ⟩ y

theorem ker_le_ker_comp_of_eq_center (p : E →* Q) (hker : p.ker = center E) (γ : MulAut E) :
    p.ker ≤ (p.comp γ.toMonoidHom).ker := by
  intro z hz
  rw [hker, mem_center_iff] at hz
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker,
    hker, mem_center_iff]
  intro w
  obtain ⟨w', rfl⟩ := γ.surjective w
  rw [← map_mul, ← map_mul, hz w']

@[expose] noncomputable def descendCenterAut (p : E →* Q) (hp : Function.Surjective p)
    (hker : p.ker = center E) (γ : MulAut E) : MulAut Q where
  toFun := descendCenterHom p hp γ.toMonoidHom (ker_le_ker_comp_of_eq_center p hker γ)
  invFun := descendCenterHom p hp γ.symm.toMonoidHom (ker_le_ker_comp_of_eq_center p hker γ.symm)
  left_inv q := by
    obtain ⟨y, rfl⟩ := hp q
    rw [descendCenterHom_apply, descendCenterHom_apply]
    simp
  right_inv q := by
    obtain ⟨y, rfl⟩ := hp q
    rw [descendCenterHom_apply, descendCenterHom_apply]
    simp
  map_mul' := map_mul _

theorem descendCenterAut_apply (p : E →* Q) (hp : Function.Surjective p) (hker : p.ker = center E)
    (γ : MulAut E) (y : E) : descendCenterAut p hp hker γ (p y) = p (γ y) :=
  descendCenterHom_apply p hp γ.toMonoidHom (ker_le_ker_comp_of_eq_center p hker γ) y

@[expose] noncomputable def descendCenterMulAut (p : E →* Q) (hp : Function.Surjective p)
    (hker : p.ker = center E) : MulAut E →* MulAut Q where
  toFun := descendCenterAut p hp hker
  map_one' := by
    ext q
    obtain ⟨y, rfl⟩ := hp q
    rw [descendCenterAut_apply]
    rfl
  map_mul' γ₁ γ₂ := by
    ext q
    obtain ⟨y, rfl⟩ := hp q
    rw [MulAut.mul_apply, descendCenterAut_apply, MulAut.mul_apply, descendCenterAut_apply,
      descendCenterAut_apply]

theorem descendCenterMulAut_apply (p : E →* Q) (hp : Function.Surjective p)
    (hker : p.ker = center E) (γ : MulAut E) (y : E) :
    descendCenterMulAut p hp hker γ (p y) = p (γ y) :=
  descendCenterAut_apply p hp hker γ y

end Descend

section Matrix

variable {n : ℕ} {K : Type*} [Field K] {F : Type*} [Field F]

theorem exists_proj_map_eq_of_mem_range {m : ℕ} (ι : K →+* F) {z : LinearFlag.projectiveSL m F}
    (hz : z ∈ (linearSubfieldInclusion m ι.fieldRange).range) :
    ∃ x : SpecialLinearGroup (Fin m) K, LinearFlag.proj m F (SpecialLinearGroup.map ι x) = z := by
  obtain ⟨g, hg, rfl⟩ := CFSG.RankThree.PartOne.mem_range_linearSubfieldInclusion.1 hz
  choose a ha using fun i j => RingHom.mem_fieldRange.1 (hg i j)
  have hmap : ι.mapMatrix (Matrix.of a) = (g : Matrix (Fin m) (Fin m) F) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ha]
  have hA : (Matrix.of a).det = 1 := by
    apply ι.injective
    rw [map_one, RingHom.map_det, hmap]
    exact g.2
  let x : SpecialLinearGroup (Fin m) K := ⟨Matrix.of a, hA⟩
  have hx : ((SpecialLinearGroup.map ι x : SpecialLinearGroup (Fin m) F) :
      Matrix (Fin m) (Fin m) F) = (g : Matrix (Fin m) (Fin m) F) := by
    rw [SpecialLinearGroup.map_apply_coe]
    exact hmap
  exact ⟨x, congrArg (LinearFlag.proj m F) (Subtype.ext hx)⟩

theorem unitDiagGL_pow {m : ℕ} (d : Fin m → Fˣ) (k : ℕ) :
    unitDiagGL d ^ k = unitDiagGL (d ^ k) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_unitDiagGL, coe_unitDiagGL, diagonal_pow]
  congr 1

theorem unitDiagGL_one {m : ℕ} : unitDiagGL (1 : Fin m → Fˣ) = 1 := by
  apply Units.ext
  rw [coe_unitDiagGL]
  simp

theorem map_slConjugation_unitDiagGL {m : ℕ} (ι : K →+* F) (d : Fin m → Kˣ)
    (x : SpecialLinearGroup (Fin m) K) :
    SpecialLinearGroup.map ι
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m K
          (unitDiagGL d) x) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m F
        (unitDiagGL fun a => Units.map ι.toMonoidHom (d a)) (SpecialLinearGroup.map ι x) := by
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    LinearFlag.coe_slConjugation, coe_unitDiagGL, coe_unitDiagGL_inv, mul_diagonal, diagonal_mul]
  simp

theorem specialLinear_map_id (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.map (RingHom.id K) g = g := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  exact Matrix.map_id _

theorem torusDiagSL_mul_blockSLEquiv_mul_inv (N : Finset (Fin n)) {m : ℕ} (eN : N ≃ Fin m)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (x : SpecialLinearGroup (Fin m) K) :
    torusDiagSL c * ((blockSLEquiv N eN x : blockSpecialLinear (K := K) N) :
        SpecialLinearGroup (Fin n) K) * (torusDiagSL c)⁻¹ =
      ((blockSLEquiv N eN (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        m K (unitDiagGL (torusBlockUnits (RingHom.id K) eN c)) x) : blockSpecialLinear (K := K) N) :
          SpecialLinearGroup (Fin n) K) := by
  have h := congrArg (fun y : blockSpecialLinear (K := K) N => (y : SpecialLinearGroup (Fin n) K))
    (conjDiag_blockSLEquiv (RingHom.id K) N eN c x)
  simp only [coe_conjDiag_apply, specialLinear_map_id] at h
  exact h

end Matrix

section Torus

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem proj_normalizerMonoidHom_torus_eq [Finite G] [Finite K] [CharP K 2] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) (ι : K →+* F) {σ : F ≃+* F} (hσ : σ * σ = 1)
    (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {X : Subgroup G} {N : Finset (Fin n)} {m : ℕ}
    (eN : N ≃ Fin m) (hm : 3 ≤ m) (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m F)
    (hp : Function.Surjective p) (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : SpecialLinearGroup (Fin m) K,
      p ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n)))
    (hg : ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈
      normalizer (centralizerPerfectCore X : Set G))
    (y : centralizerPerfectCore X) :
    p ((centralizerPerfectCore X).normalizerMonoidHom ⟨_, hg⟩ y) =
      LinearFlag.conjAut m F (unitDiagGL (torusBlockUnits ι eN c)) (p y) := by
  set g : G := ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) with hgdef
  have hker : p.ker = center (centralizerPerfectCore X) :=
    ker_eq_center_of_surjective_of_center_eq_bot hp hpker
      (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hm)
  set γ : MulAut (centralizerPerfectCore X) :=
    (centralizerPerfectCore X).normalizerMonoidHom ⟨g, hg⟩ with hγ
  set γb : MulAut (LinearFlag.projectiveSL m F) := descendCenterMulAut p hp hker γ with hγb
  set β : MulAut (LinearFlag.projectiveSL m F) :=
    LinearFlag.conjAut m F (unitDiagGL (torusBlockUnits ι eN c)) with hβ
  have hagree : ∀ x : SpecialLinearGroup (Fin m) K,
      γb (LinearFlag.proj m F (SpecialLinearGroup.map ι x)) =
        β (LinearFlag.proj m F (SpecialLinearGroup.map ι x)) := by
    intro x
    have hconj : γ ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m K
            (unitDiagGL (torusBlockUnits (RingHom.id K) eN c)) x))) : L) : G),
          hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN
            (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m K
              (unitDiagGL (torusBlockUnits (RingHom.id K) eN c)) x)).2))⟩ := by
      apply Subtype.ext
      change g * ((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G) * g⁻¹ =
        ((e.symm (LinearFlag.proj n K (blockSLEquiv N eN
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m K
            (unitDiagGL (torusBlockUnits (RingHom.id K) eN c)) x))) : L) : G)
      rw [← torusDiagSL_mul_blockSLEquiv_mul_inv N eN c x]
      simp only [hgdef, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    conv_lhs => rw [← h1 x]
    have hu : (fun a => Units.map ι.toMonoidHom (torusBlockUnits (RingHom.id K) eN c a)) =
        torusBlockUnits ι eN c := by
      funext a
      apply Units.ext
      simp [torusBlockUnits]
    rw [hγb, descendCenterMulAut_apply, hconj, h1, map_slConjugation_unitDiagGL, hβ,
      LinearFlag.conjAut_proj, hu]
  have hk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [RingHom.mem_fieldRange, hfix x, Set.mem_range]
  have hmem : β⁻¹ * γb ∈ zpowers (LinearFlag.fieldAut m F σ) := by
    rw [← CFSG.RankThree.PartOne.fixingSubgroup_range_linearSubfieldInclusion hk hm,
      mem_fixingSubgroup_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := exists_proj_map_eq_of_mem_range ι hz
    rw [MulAut.smul_def, MulAut.mul_apply, hagree x, ← MulAut.mul_apply, inv_mul_cancel,
      MulAut.one_apply]
  set β' := β⁻¹ * γb with hβ'
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
  have hf2 : LinearFlag.fieldAut m F σ ^ 2 = 1 := by rw [sq, ← map_mul, hσ, map_one]
  have hβ'2 : β' ^ 2 = 1 := by
    rw [← hj, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hf2,
      _root_.one_zpow]
  have hσD : GeneralLinearGroup.map (σ : F →+* F) (unitDiagGL (torusBlockUnits ι eN c)) =
      unitDiagGL (torusBlockUnits ι eN c) := by
    apply Units.ext
    ext a b
    rw [GeneralLinearGroup.map_apply, coe_unitDiagGL]
    by_cases hab : a = b
    · subst hab
      rw [diagonal_apply_eq]
      exact (hfix _).2 ⟨_, rfl⟩
    · rw [diagonal_apply_ne _ hab, map_zero]
  have hcomm : Commute β (LinearFlag.fieldAut m F σ) := by
    have h := LinearFlag.fieldAut_mul_conjAut σ (unitDiagGL (torusBlockUnits ι eN c))
    rw [hσD] at h
    exact h.symm
  have hcomm' : Commute β β' := hj ▸ hcomm.zpow_right j
  set r := Nat.card Kˣ with hr
  have hrodd : Odd r := by
    rw [hr, Nat.card_units]
    exact odd_natCard_sub_one
  have hcr : c ^ r = 1 := by
    apply Subtype.ext
    funext i
    change (c.1 i) ^ r = 1
    exact pow_card_eq_one'
  have hγr : γb ^ r = 1 := by
    have hgr : (⟨g, hg⟩ : normalizer (centralizerPerfectCore X : Set G)) ^ r = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      change g ^ r = 1
      rw [hgdef, ← Subgroup.coe_pow, ← map_pow, ← map_pow, ← map_pow, hcr, map_one, map_one,
        map_one, OneMemClass.coe_one]
    rw [hγb, ← map_pow, hγ, ← map_pow, hgr, map_one, map_one]
  have hβr : β ^ r = 1 := by
    have hu : torusBlockUnits ι eN c ^ r = 1 := by
      funext a
      change (Units.map ι.toMonoidHom (c.1 ((eN.symm a : N) : Fin n))) ^ r = 1
      rw [← map_pow, pow_card_eq_one', map_one]
    rw [hβ, ← map_pow, unitDiagGL_pow, hu, unitDiagGL_one, map_one]
  have hγβ : γb = β * β' := by rw [hβ', mul_inv_cancel_left]
  have hβ'r : β' ^ r = 1 := by
    have h := hcomm'.mul_pow r
    rw [← hγβ, hγr, hβr, one_mul] at h
    exact h.symm
  have hβ'1 : β' = 1 := by
    obtain ⟨s, hs⟩ := hrodd
    rw [hs, pow_succ, pow_mul, hβ'2, one_pow, one_mul] at hβ'r
    exact hβ'r
  rw [← descendCenterMulAut_apply p hp hker γ y, ← hγb, hγβ, hβ'1, mul_one]

end Torus

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K] {F : Type}
  [Field F]

theorem nonempty_fieldNeighbourParam_of_proj_of_fixedField [Finite G] [Finite K] [CharP K 2]
    [Finite F] (e : L ≃* LinearFlag.projectiveSL n K) (t : G) (ι : K →+* F) {σ : F ≃+* F}
    (hσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) {X : Subgroup G}
    {N : Finset (Fin n)} {m : ℕ} (eN : N ≃ Fin m) (hm : 3 ≤ m) (hF : 5 ≤ Nat.card F)
    (p : centralizerPerfectCore X →* LinearFlag.projectiveSL m F) (hp : Function.Surjective p)
    (hpker : p.ker ≤ center (centralizerPerfectCore X))
    (hD : modelToG e (blockSL (K := K) N) ≤ centralizerPerfectCore X)
    (h1 : ∀ x : SpecialLinearGroup (Fin m) K,
      p ⟨((e.symm (LinearFlag.proj n K (blockSLEquiv N eN x)) : L) : G),
        hD (symm_mem_modelToG e (proj_mem_blockSL (blockSLEquiv N eN x).2))⟩ =
        LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (ht : t ∈ normalizer (centralizerPerfectCore X : Set G))
    (h3 : ∀ y, p ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, ht⟩ y) =
      LinearFlag.fieldAut m F σ (p y))
    (hg : ∀ c : blockTorusParam (K := K) (∅ : Finset (Fin n)),
      ((e.symm (LinearFlag.proj n K (torusDiagSL c)) : L) : G) ∈
        normalizer (centralizerPerfectCore X : Set G)) :
    Nonempty (FieldNeighbourParam e t ι σ X N) :=
  nonempty_fieldNeighbourParam_of_proj e t ι σ eN hm hF p hp hpker hD h1 ht h3 hg
    fun c y => proj_normalizerMonoidHom_torus_eq e ι hσ hfix eN hm p hp hpker hD h1 c (hg c) y

theorem proj_torusDiagSL_mem_normalizer_torus (Nb : Neighbour n)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) :
    LinearFlag.proj n K (torusDiagSL c) ∈
      normalizer (Nb.torus K : Set (LinearFlag.projectiveSL n K)) := by
  refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_)
  obtain ⟨c', -, rfl⟩ := mem_blockTorus.1 (Nb.torus_le_blockTorus subset_rfl hx)
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm c' c]

theorem nonempty_fieldNeighbourParam_neighbour [Finite G] [Finite K] [CharP K 2] [Finite F]
    (e : L ≃* LinearFlag.projectiveSL n K) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ι : K →+* F) {σ : F ≃+* F} (hσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (Nb : Neighbour n) {m : ℕ} (eN : Nb.index ≃ Fin m) (hm : 3 ≤ m) (hF : 5 ≤ Nat.card F)
    (p : neighbourCore e Nb →* LinearFlag.projectiveSL m F) (hp : Function.Surjective p)
    (hpker : p.ker ≤ center (neighbourCore e Nb))
    (h1 : ∀ (x : SpecialLinearGroup (Fin m) K)
      (hx : ((e.symm (LinearFlag.proj n K (blockSLEquiv Nb.index eN x)) : L) : G) ∈
        neighbourCore e Nb),
      p ⟨_, hx⟩ = LinearFlag.proj m F (SpecialLinearGroup.map ι x))
    (h3 : ∀ y, p ((neighbourCore e Nb).normalizerMonoidHom ⟨t, le_normalizer_neighbourCore e htL Nb⟩
      y) = LinearFlag.fieldAut m F σ (p y)) :
    Nonempty (FieldNeighbourParam e t ι σ (modelToG e (Nb.torus K)) Nb.index) := by
  have hcard : 3 ≤ Nb.index.card := by
    rw [← Fintype.card_coe, Fintype.card_congr eN, Fintype.card_fin]
    exact hm
  exact nonempty_fieldNeighbourParam_of_proj_of_fixedField e t ι hσ hfix eN hm hF p hp hpker
    (modelToG_blockSL_index_le_neighbourCore e Nb (commutator_blockSL_eq_of_three_le hcard))
    (fun x => h1 x _) (le_normalizer_neighbourCore e htL Nb) h3
    fun c => symm_mem_normalizer_neighbourCore e (proj_torusDiagSL_mem_normalizer_torus Nb c)

end Param

end CFSG.SeitzReduction.LinearPilot
