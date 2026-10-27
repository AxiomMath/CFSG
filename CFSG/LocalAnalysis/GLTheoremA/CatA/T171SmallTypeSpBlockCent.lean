module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpBlockBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpBlockScalar
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentGrp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
public import CFSG.GroupTheory.Commutator.SupNormalizer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (comSp fixSp mem_comSp mem_fixSp e_mem_comSp)
open CFSG.RankThree.PartOne.KCOrthogonal (exists_coe_add_of_isCompl)
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable {B : LinearMap.BilinForm (ZMod 2) V}

private noncomputable def restrictLinearEquiv (g : V ≃ₗ[ZMod 2] V) {P : Submodule (ZMod 2) V}
    (hg : ∀ x ∈ P, g x ∈ P) : P ≃ₗ[ZMod 2] P :=
  LinearEquiv.ofInjectiveEndo
    { toFun := fun x => ⟨g x, hg x x.2⟩
      map_add' := fun x y => Subtype.ext (map_add g x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul g c x.1) }
    (fun x y h => Subtype.ext (g.injective (congrArg Subtype.val h)))

private theorem coe_restrictLinearEquiv (g : V ≃ₗ[ZMod 2] V) {P : Submodule (ZMod 2) V}
    (hg : ∀ x ∈ P, g x ∈ P) (x : P) :
    ((restrictLinearEquiv g hg x : P) : V) = g x := rfl

private theorem coe_restrictLinearEquiv_pow (g : V ≃ₗ[ZMod 2] V) {P : Submodule (ZMod 2) V}
    (hg : ∀ x ∈ P, g x ∈ P) (k : ℕ) (x : P) :
    (((restrictLinearEquiv g hg) ^ k) x : V) = (g ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, LinearEquiv.mul_apply, ih, coe_restrictLinearEquiv, pow_succ,
        LinearEquiv.mul_apply]

theorem maps_plane_of_mem_centralizer
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    {g : ↥(linIsometryGroup B)}
    (hg : g ∈ Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))) :
    ∀ p ∈ P, (g : V ≃ₗ[ZMod 2] V) p ∈ P := by
  have hgcomm : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgVcomm : (g : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V) =
      (y : V ≃ₗ[ZMod 2] V) * (g : V ≃ₗ[ZMod 2] V) :=
    congrArg (fun z : ↥(linIsometryGroup B) => (z : V ≃ₗ[ZMod 2] V)) hgcomm
  intro p hp
  have hp' : p ∈ comSp (y : V ≃ₗ[ZMod 2] V) := by rwa [← hP] at hp
  obtain ⟨v, rfl⟩ := mem_comSp.mp hp'
  rw [← hP]
  refine mem_comSp.mpr ⟨(g : V ≃ₗ[ZMod 2] V) v, ?_⟩
  rw [map_sub]
  have h := congrArg (fun z : V ≃ₗ[ZMod 2] V => z v) hgVcomm
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  rw [h]

theorem exists_zpow_mul_mem_pointwiseStab
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2)
    {g : ↥(linIsometryGroup B)}
    (hg : g ∈ Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B))) :
    ∃ k : ℕ, k < 3 ∧ ∃ d ∈ pointwiseStab (linIsometryGroup B) P,
      (g : ↥(linIsometryGroup B)) = d * y ^ k := by
  classical
  have hy3V : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 :=
    congrArg (fun z : ↥(linIsometryGroup B) => (z : V ≃ₗ[ZMod 2] V)) hy3
  have hcompl : IsCompl P (B.orthogonal P) := isCompl_orthogonal_of_nondegenerate hB hPnd
  have hyfix : ∀ q ∈ B.orthogonal P, (y : V ≃ₗ[ZMod 2] V) q = q := by
    intro q hq
    exact (mem_fixSp (e := (y : V ≃ₗ[ZMod 2] V))).mp (hfix ▸ hq)
  have hyP : ∀ p ∈ P, (y : V ≃ₗ[ZMod 2] V) p ∈ P := by
    intro p hp
    have hmem : (y : V ≃ₗ[ZMod 2] V) p ∈ comSp (y : V ≃ₗ[ZMod 2] V) :=
      e_mem_comSp (by rwa [← hP] at hp)
    rwa [hP] at hmem
  have hy_inv_maps : ∀ p ∈ P, (y : V ≃ₗ[ZMod 2] V)⁻¹ p ∈ P := by
    have h2 : (y : V ≃ₗ[ZMod 2] V)⁻¹ = (y : V ≃ₗ[ZMod 2] V) ^ 2 := by
      have hm : (y : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V) ^ 2 = 1 := by
        rw [← pow_succ']
        rw [show 2 + 1 = 3 by norm_num, hy3V]
      exact inv_eq_of_mul_eq_one_right hm
    intro p hp
    rw [h2]
    exact hyP _ (hyP p hp)
  have hvarith : ∀ j : ℕ, ∀ p ∈ P, ((y : V ≃ₗ[ZMod 2] V) ^ j) p ∈ P := by
    intro j
    induction j with
    | zero => intro p hp; simpa using hp
    | succ j ih =>
        intro p hp
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hyP _ (ih p hp)

  have hgcomm : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgVcomm : (g : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V) =
      (y : V ≃ₗ[ZMod 2] V) * (g : V ≃ₗ[ZMod 2] V) :=
    congrArg (fun z : ↥(linIsometryGroup B) => (z : V ≃ₗ[ZMod 2] V)) hgcomm
  have hgP : ∀ p ∈ P, (g : V ≃ₗ[ZMod 2] V) p ∈ P := by
    intro p hp
    have hp' : p ∈ comSp (y : V ≃ₗ[ZMod 2] V) := by rwa [← hP] at hp
    obtain ⟨v, rfl⟩ := mem_comSp.mp hp'
    rw [← hP]
    refine mem_comSp.mpr ⟨(g : V ≃ₗ[ZMod 2] V) v, ?_⟩
    rw [map_sub]
    have h := congrArg (fun z : V ≃ₗ[ZMod 2] V => z v) hgVcomm
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    rw [h]
  have hginvP : ∀ p ∈ P, (g : V ≃ₗ[ZMod 2] V)⁻¹ p ∈ P := by
    have hginv : g⁻¹ ∈ Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)) :=
      Subgroup.inv_mem _ hg
    have hginvcomm : g⁻¹ * y = y * g⁻¹ :=
      Subgroup.mem_centralizer_singleton_iff.mp hginv
    have hginvVcomm : (g : V ≃ₗ[ZMod 2] V)⁻¹ * (y : V ≃ₗ[ZMod 2] V) =
        (y : V ≃ₗ[ZMod 2] V) * (g : V ≃ₗ[ZMod 2] V)⁻¹ :=
      congrArg (fun z : ↥(linIsometryGroup B) => (z : V ≃ₗ[ZMod 2] V)) hginvcomm
    intro p hp
    have hp' : p ∈ comSp (y : V ≃ₗ[ZMod 2] V) := by rwa [← hP] at hp
    obtain ⟨v, rfl⟩ := mem_comSp.mp hp'
    rw [← hP]
    refine mem_comSp.mpr ⟨(g : V ≃ₗ[ZMod 2] V)⁻¹ v, ?_⟩
    rw [map_sub]
    have h := congrArg (fun z : V ≃ₗ[ZMod 2] V => z v) hginvVcomm
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    rw [h]
  let yP : P ≃ₗ[ZMod 2] P := restrictLinearEquiv (y : V ≃ₗ[ZMod 2] V) hyP
  let gP : P ≃ₗ[ZMod 2] P := restrictLinearEquiv (g : V ≃ₗ[ZMod 2] V) hgP
  have hyP3 : yP ^ 3 = 1 := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [coe_restrictLinearEquiv_pow, hy3V]
    rfl
  have hyP1 : yP ≠ 1 := by
    intro h
    have hbot : P = ⊥ := by
      rw [eq_bot_iff]
      intro p hp
      have hpy : (y : V ≃ₗ[ZMod 2] V) p = p := by
        have h' := congrArg (fun f : P ≃ₗ[ZMod 2] P => ((f ⟨p, hp⟩ : P) : V)) h
        rw [coe_restrictLinearEquiv] at h'
        simpa [yP] using h'
      have horth : p ∈ B.orthogonal P := by
        rw [← hfix]
        exact (mem_fixSp (e := (y : V ≃ₗ[ZMod 2] V))).mpr hpy
      have hmem : p ∈ P ⊓ B.orthogonal P := Submodule.mem_inf.mpr ⟨hp, horth⟩
      rw [hcompl.disjoint.eq_bot] at hmem
      simpa using hmem
    rw [hbot] at hP2
    simp at hP2
  have hgPcomm : gP * yP = yP * gP := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, coe_restrictLinearEquiv,
      coe_restrictLinearEquiv, coe_restrictLinearEquiv, coe_restrictLinearEquiv]
    exact congrArg (fun z : V ≃ₗ[ZMod 2] V => z (x : V)) hgVcomm
  obtain ⟨k, hk3, hyPk⟩ := linearEquiv_centralizer_zpowers_nat hP2 hyP3 hyP1 hgPcomm
  have hg_apply : ∀ p : P, (g : V ≃ₗ[ZMod 2] V) (p : V) =
      ((y : V ≃ₗ[ZMod 2] V) ^ k) (p : V) := by
    intro p
    have h := congrArg (fun f : P ≃ₗ[ZMod 2] P => ((f p : P) : V)) hyPk
    rw [coe_restrictLinearEquiv_pow] at h
    simpa [gP, coe_restrictLinearEquiv] using h.symm
  have hy_inv : (y : V ≃ₗ[ZMod 2] V)⁻¹ = (y : V ≃ₗ[ZMod 2] V) ^ 2 := by
    have hm : (y : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V) ^ 2 = 1 := by
      rw [← pow_succ']
      rw [show 2 + 1 = 3 by norm_num, hy3V]
    exact inv_eq_of_mul_eq_one_right hm
  have hy_inv_pow_maps : ∀ j : ℕ, ∀ p ∈ P,
      (((y : V ≃ₗ[ZMod 2] V) ^ j)⁻¹) p ∈ P := by
    intro j p hp
    rw [← inv_pow, hy_inv, ← pow_mul]
    exact hvarith (2 * j) p hp
  have hd_fixes : ∀ p ∈ P,
      ((g : V ≃ₗ[ZMod 2] V) * ((y : V ≃ₗ[ZMod 2] V) ^ k)⁻¹) p = p := by
    intro p hp
    have hq : (((y : V ≃ₗ[ZMod 2] V) ^ k)⁻¹) p ∈ P := hy_inv_pow_maps k p hp
    rw [LinearEquiv.mul_apply, hg_apply ⟨_, hq⟩]
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  let dH : ↥(linIsometryGroup B) := g * (y ^ k)⁻¹
  have hdD : dH ∈ pointwiseStab (linIsometryGroup B) P := by
    rw [mem_pointwiseStab]
    intro p hp
    change ((g : V ≃ₗ[ZMod 2] V) * ((y : V ≃ₗ[ZMod 2] V) ^ k)⁻¹) p = p
    exact hd_fixes p hp
  refine ⟨k, hk3, ?_⟩
  refine ⟨dH, hdD, ?_⟩
  · apply Subtype.ext
    change (g : V ≃ₗ[ZMod 2] V) =
      ((g : V ≃ₗ[ZMod 2] V) * ((y : V ≃ₗ[ZMod 2] V) ^ k)⁻¹) *
        ((y : V ≃ₗ[ZMod 2] V) ^ k)
    rw [mul_assoc, inv_mul_cancel, mul_one]

theorem centralizer_eq_zpowers_sup_pointwiseStab
    (hB : B.IsAlt) (hBn : B.Nondegenerate)
    (y : ↥(linIsometryGroup B)) (hy3 : y ^ 3 = 1)
    (P : Submodule (ZMod 2) V) (hPnd : (B.restrict P).Nondegenerate)
    (hP : comSp (y : V ≃ₗ[ZMod 2] V) = P)
    (hfix : fixSp (y : V ≃ₗ[ZMod 2] V) = B.orthogonal P)
    (hP2 : Module.finrank (ZMod 2) P = 2) :
    Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)) =
      Subgroup.zpowers y ⊔ pointwiseStab (linIsometryGroup B) P := by
  classical
  have hcompl : IsCompl P (B.orthogonal P) := isCompl_orthogonal_of_nondegenerate hB hPnd
  have hy3V : (y : V ≃ₗ[ZMod 2] V) ^ 3 = 1 :=
    congrArg (fun z : ↥(linIsometryGroup B) => (z : V ≃ₗ[ZMod 2] V)) hy3
  have hyfix : ∀ q ∈ B.orthogonal P, (y : V ≃ₗ[ZMod 2] V) q = q := by
    intro q hq
    exact (mem_fixSp (e := (y : V ≃ₗ[ZMod 2] V))).mp (hfix ▸ hq)
  have hyP : ∀ p ∈ P, (y : V ≃ₗ[ZMod 2] V) p ∈ P := by
    intro p hp
    have hmem : (y : V ≃ₗ[ZMod 2] V) p ∈ comSp (y : V ≃ₗ[ZMod 2] V) :=
      e_mem_comSp (by rwa [← hP] at hp)
    rwa [hP] at hmem
  have hy_inv_maps : ∀ p ∈ P, (y : V ≃ₗ[ZMod 2] V)⁻¹ p ∈ P := by
    have h2 : (y : V ≃ₗ[ZMod 2] V)⁻¹ = (y : V ≃ₗ[ZMod 2] V) ^ 2 := by
      have hm : (y : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V) ^ 2 = 1 := by
        rw [← pow_succ']
        rw [show 2 + 1 = 3 by norm_num, hy3V]
      exact inv_eq_of_mul_eq_one_right hm
    intro p hp
    rw [h2]
    exact hyP _ (hyP p hp)
  have hvarith : ∀ j : ℕ, ∀ p ∈ P, ((y : V ≃ₗ[ZMod 2] V) ^ j) p ∈ P := by
    intro j
    induction j with
    | zero => intro p hp; simpa using hp
    | succ j ih =>
        intro p hp
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hyP _ (ih p hp)
  have hD_le : pointwiseStab (linIsometryGroup B) P ≤
      Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    obtain ⟨p, q, hpq⟩ := exists_coe_add_of_isCompl hcompl v
    have hdfix : ∀ x ∈ P, (d : V ≃ₗ[ZMod 2] V) x = x := mem_pointwiseStab.mp hd
    have hdp : (d : V ≃ₗ[ZMod 2] V) (p : V) = p := hdfix p p.2
    have hyq : (y : V ≃ₗ[ZMod 2] V) (q : V) = q := hyfix q q.2
    have hdq : (d : V ≃ₗ[ZMod 2] V) (q : V) ∈ B.orthogonal P := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro p' hp'
      have hiso := mem_linIsometryGroup.mp d.2 p' (q : V)
      rw [hdfix p' hp'] at hiso
      have hzero : B p' (q : V) = 0 :=
        (LinearMap.BilinForm.mem_orthogonal_iff.mp q.2) p' hp'
      rw [hiso, hzero]
    have hdqf : (y : V ≃ₗ[ZMod 2] V) ((d : V ≃ₗ[ZMod 2] V) (q : V)) =
        (d : V ≃ₗ[ZMod 2] V) (q : V) := hyfix _ hdq
    have hdyp : (d : V ≃ₗ[ZMod 2] V) ((y : V ≃ₗ[ZMod 2] V) (p : V)) =
        (y : V ≃ₗ[ZMod 2] V) (p : V) := hdfix _ (hyP p p.2)
    calc ((d : V ≃ₗ[ZMod 2] V) * (y : V ≃ₗ[ZMod 2] V)) v
        = (d : V ≃ₗ[ZMod 2] V) ((y : V ≃ₗ[ZMod 2] V) ((p : V) + (q : V))) := by
          rw [LinearEquiv.mul_apply, hpq]
      _ = (d : V ≃ₗ[ZMod 2] V) ((y : V ≃ₗ[ZMod 2] V) (p : V) +
            (y : V ≃ₗ[ZMod 2] V) (q : V)) := by rw [map_add]
      _ = (y : V ≃ₗ[ZMod 2] V) (p : V) + (d : V ≃ₗ[ZMod 2] V) (q : V) := by
          rw [map_add, hdyp, hyq]
      _ = (y : V ≃ₗ[ZMod 2] V) ((d : V ≃ₗ[ZMod 2] V) ((p : V) + (q : V))) := by
          rw [map_add, hdp, map_add, hdqf]
      _ = ((y : V ≃ₗ[ZMod 2] V) * (d : V ≃ₗ[ZMod 2] V)) v := by
          rw [LinearEquiv.mul_apply, hpq]
  have h_factor : ∀ g : ↥(linIsometryGroup B),
      g ∈ Subgroup.centralizer ({y} : Set ↥(linIsometryGroup B)) →
      ∃ k : ℕ, k < 3 ∧ ∃ d ∈ pointwiseStab (linIsometryGroup B) P,
        (g : ↥(linIsometryGroup B)) = d * y ^ k :=
    fun g hg => exists_zpow_mul_mem_pointwiseStab hB hBn y hy3 P hPnd hP hfix hP2 hg
  refine le_antisymm ?_ (sup_le ?_ hD_le)
  · intro g hg
    obtain ⟨k, -, d, hd, hgd⟩ := h_factor g hg
    rw [hgd]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hd)
      (Subgroup.mem_sup_left
        (Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) k))
  · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
