module

public import CFSG.Quasithin.Background.FFC3Unitri
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphGL4
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
import CFSG.Quasithin.EmptyFaithful.SBdK36Abs
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.Exceptional

open Matrix CFSG.Quasithin.FFC CFSG.SeitzReduction.F4Pilot

theorem gl4T0_mem_centralizer_UT :
    gl4T0 ∈ Subgroup.centralizer (UT 4 : Set (GL (Fin 4) (ZMod 2))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hU : h ∈ UT 4 := hh
  have hl := mem_UT.1 hU
  have h00 := UT_diag hU 0
  have h33 := UT_diag hU 3
  have h10 := hl 1 0 (by decide)
  have h20 := hl 2 0 (by decide)
  have h30 := hl 3 0 (by decide)
  have h31 := hl 3 1 (by decide)
  have h32 := hl 3 2 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gl4T0, gl4T0M, Matrix.mul_apply, Fin.sum_univ_four, h00, h33, h10, h20, h30, h31, h32,
      add_comm]

theorem mem_centralizer_UT_four_iff {g : GL (Fin 4) (ZMod 2)} :
    g ∈ Subgroup.centralizer (UT 4 : Set (GL (Fin 4) (ZMod 2))) ↔ g = 1 ∨ g = gl4T0 := by
  refine ⟨fun hg => ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.K1.eq_smul_one_add_single_of_commute
      (by norm_num) (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) fun i j hij => by
        have hlt : i < j := Fin.lt_def.2 (by omega)
        have h := congrArg Units.val (Subgroup.mem_centralizer_iff.1 hg _ (elemTv_mem_UT hlt))
        simp only [Units.val_mul, elemTv_val, add_mul, mul_add, one_mul, mul_one] at h
        exact (add_left_cancel h).symm
    have hab' : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = a • 1 + b • single 0 3 1 := hab
    have hdet : IsUnit (g : Matrix (Fin 4) (Fin 4) (ZMod 2)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases two a with ha | ha
    · refine absurd hdet ?_
      rw [Matrix.det_eq_zero_of_row_eq_zero 1 fun j => by simp [hab', ha, Matrix.single_apply]]
      exact not_isUnit_zero
    rcases two b with hb | hb
    · exact Or.inl (Units.ext (by rw [hab', ha, hb, Units.val_one]; simp))
    · refine Or.inr (Units.ext ?_)
      rw [hab', ha, hb, one_smul, one_smul]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gl4T0, gl4T0M, Matrix.one_apply, Matrix.single_apply]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact gl4T0_mem_centralizer_UT

theorem gl4T0_ne_one : gl4T0 ≠ 1 :=
  fun h => absurd (congrArg Units.val h) (by change gl4T0M ≠ 1; decide)

theorem normalizer_centralizer_UT_four :
    Subgroup.normalizer (Subgroup.centralizer (UT 4 : Set (GL (Fin 4) (ZMod 2))) :
      Set (GL (Fin 4) (ZMod 2))) = Subgroup.centralizer {gl4T0} := by
  ext n
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hn
    have h := (Subgroup.mem_normalizer_iff.1 hn gl4T0).1 gl4T0_mem_centralizer_UT
    rcases mem_centralizer_UT_four_iff.1 h with h1 | h1
    · exact absurd (by simpa using h1) gl4T0_ne_one
    · exact mul_inv_eq_iff_eq_mul.1 h1
  · intro hn
    have hct : n * gl4T0 * n⁻¹ = gl4T0 := by rw [hn, mul_inv_cancel_right]
    refine Subgroup.mem_normalizer_iff.2 fun h => ?_
    rw [mem_centralizer_UT_four_iff, mem_centralizer_UT_four_iff]
    constructor
    · rintro (rfl | rfl)
      · simp
      · exact Or.inr hct
    · rintro (h1 | h1)
      · exact Or.inl (by simpa using h1)
      · exact Or.inr (by rw [← hct] at h1; simpa using h1)

private theorem isSolvable_GL_two_zmod_two : Group.IsSolvable (GL (Fin 2) (ZMod 2)) := by
  let ua : GL (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], !![1, 1; 0, 1], by decide, by decide⟩
  let ub : GL (Fin 2) (ZMod 2) := ⟨!![1, 0; 1, 1], !![1, 0; 1, 1], by decide, by decide⟩
  have hab : ua * ub ≠ ub * ua := fun h => absurd (congrArg Units.val h) (by decide)
  have h6 : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by rw [Matrix.card_GL_field]; decide
  obtain ⟨e⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6 ⟨ua, ub, hab⟩
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem isSolvable_centralizer_gl4T0 :
    Group.IsSolvable (Subgroup.centralizer ({gl4T0} : Set (GL (Fin 4) (ZMod 2)))) := by
  have : Group.IsSolvable (GL (Fin 2) (ZMod 2)) := isSolvable_GL_two_zmod_two
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 gl4RhoT.ker :=
    IsPGroup.of_card (n := 5) (by rw [gl4_card_ker_rhoT]; norm_num)
  have : Group.IsNilpotent gl4RhoT.ker := hker.isNilpotent
  exact Group.isSolvable_of_ker_le_range gl4RhoT.ker.subtype gl4RhoT
    (by rw [Subgroup.range_subtype])

private def gl4SwapM : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

private def gl4E12M : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem normalizer_centralizer_UT_four_not_le :
    ¬ Subgroup.normalizer (Subgroup.centralizer (UT 4 : Set (GL (Fin 4) (ZMod 2))) :
      Set (GL (Fin 4) (ZMod 2))) ≤ Subgroup.normalizer (UT 4 : Set (GL (Fin 4) (ZMod 2))) := by
  intro hle
  let s : GL (Fin 4) (ZMod 2) := gl4Mk gl4SwapM gl4SwapM (by decide)
  let u : GL (Fin 4) (ZMod 2) := gl4Mk gl4E12M gl4E12M (by decide)
  have hs : s ∈ Subgroup.centralizer ({gl4T0} : Set (GL (Fin 4) (ZMod 2))) :=
    Subgroup.mem_centralizer_singleton_iff.2 (Units.ext (by
      change gl4SwapM * gl4T0M = gl4T0M * gl4SwapM
      decide))
  have hu : u ∈ UT 4 := mem_UT.2 fun i j hij => by
    change gl4E12M i j = 0
    fin_cases i <;> fin_cases j <;> simp_all [gl4E12M]
  have hs' : s ∈ Subgroup.normalizer (Subgroup.centralizer (UT 4 : Set (GL (Fin 4) (ZMod 2))) :
      Set (GL (Fin 4) (ZMod 2))) := by
    rw [normalizer_centralizer_UT_four]
    exact hs
  have hsu := (Subgroup.mem_normalizer_iff.1 (hle hs') u).1 hu
  have h21 := mem_UT.1 hsu 2 1 (by decide)
  exact absurd h21 (by change (gl4SwapM * gl4E12M * gl4SwapM) 2 1 ≠ 0; decide)

theorem centralizer_comap_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (U : Subgroup H) :
    Subgroup.centralizer (U.comap (φ : G →* H) : Set G) =
      (Subgroup.centralizer (U : Set H)).comap (φ : G →* H) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx u hu
    have hp : φ.symm u ∈ U.comap (φ : G →* H) := by
      rw [Subgroup.mem_comap]
      simpa using hu
    simpa using congrArg φ (hx _ hp)
  · intro hx p hp
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hp
    exact φ.injective (by simpa using hx _ hp)

theorem normalizer_centralizer_comap_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (U : Subgroup H) :
    Subgroup.normalizer (Subgroup.centralizer (U.comap (φ : G →* H) : Set G) : Set G) =
      (Subgroup.normalizer (Subgroup.centralizer (U : Set H) : Set H)).comap (φ : G →* H) := by
  rw [centralizer_comap_mulEquiv,
    ← Subgroup.comap_normalizer_eq_of_surjective _ (f := (φ : G →* H)) φ.surjective]

theorem normalizer_centralizer_sylow_of_mulEquiv {Q : Type*} [Group Q]
    (e : Q ≃* GL (Fin 4) (ZMod 2)) {P : Subgroup Q} (hP : IsPGroup 2 P) (hi : ¬ 2 ∣ P.index) :
    Group.IsSolvable (Subgroup.normalizer (Subgroup.centralizer (P : Set Q) : Set Q)) ∧
      ¬ Subgroup.normalizer (Subgroup.centralizer (P : Set Q) : Set Q) ≤
        Subgroup.normalizer (P : Set Q) := by
  obtain ⟨h, hh⟩ := exists_conj_UT (hP.map (e : Q →* GL (Fin 4) (ZMod 2)))
    (by rwa [Subgroup.index_map_equiv])
  let φ : Q ≃* GL (Fin 4) (ZMod 2) := e.trans (MulAut.conj h⁻¹)
  have hφq : ∀ q, φ q = h⁻¹ * e q * h := fun q => by simp [φ, MulAut.conj_apply]
  have hP' : P = (UT 4).comap (φ : Q →* GL (Fin 4) (ZMod 2)) := by
    ext q
    change q ∈ P ↔ φ q ∈ UT 4
    rw [hφq, ← hh]
    refine ⟨fun hq => Subgroup.mem_map_of_mem _ hq, fun hq => ?_⟩
    obtain ⟨p, hp, hpq⟩ := Subgroup.mem_map.1 hq
    exact e.injective hpq ▸ hp
  have hN : Subgroup.normalizer (Subgroup.centralizer (P : Set Q) : Set Q) =
      (Subgroup.centralizer ({gl4T0} : Set (GL (Fin 4) (ZMod 2)))).comap
        (φ : Q →* GL (Fin 4) (ZMod 2)) := by
    rw [hP', normalizer_centralizer_comap_mulEquiv, normalizer_centralizer_UT_four]
  refine ⟨?_, fun hle => normalizer_centralizer_UT_four_not_le fun s hs => ?_⟩
  · rw [hN]
    have := isSolvable_centralizer_gl4T0
    exact Group.isSolvable_of_isSolvable_injective
      ((φ : Q →* GL (Fin 4) (ZMod 2)).subgroupComap_injective _ φ.injective)
  · have hq : φ.symm s ∈ Subgroup.normalizer (Subgroup.centralizer (P : Set Q) : Set Q) := by
      rw [hN, Subgroup.mem_comap]
      simpa [normalizer_centralizer_UT_four] using hs
    have h2 := hle hq
    rw [hP', ← Subgroup.comap_normalizer_eq_of_surjective _ (f := (φ : Q →* GL (Fin 4) (ZMod 2)))
      φ.surjective, Subgroup.mem_comap] at h2
    simpa using h2

theorem normalizer_centralizer_sylow_of_alt_eight {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 8)) {P : Subgroup Q} (hP : IsPGroup 2 P)
    (hi : ¬ 2 ∣ P.index) :
    Group.IsSolvable (Subgroup.normalizer (Subgroup.centralizer (P : Set Q) : Set Q)) ∧
      ¬ Subgroup.normalizer (Subgroup.centralizer (P : Set Q) : Set Q) ≤
        Subgroup.normalizer (P : Set Q) :=
  normalizer_centralizer_sylow_of_mulEquiv (e.trans alternatingEightEquivGLFourTwo) hP hi

end CFSG.GH74.Exceptional
