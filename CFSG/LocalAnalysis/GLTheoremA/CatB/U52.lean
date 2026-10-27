module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.GLTheoremB.BarXTools
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs96
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model
public import CFSG.LargeExtraspecial.S9FiveB
public import CFSG.LargeExtraspecial.Transport
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import all CFSG.Fischer.F4
public import CFSG.Sporadic.Suz.Setup
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Blueprint.LieModelAPI
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6Four
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LargeExtraspecial.S9FourD
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Models.Transport
public import CFSG.Sporadic.Suz.W64Spec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.Fischer Matrix
open scoped commutatorElement

namespace U52

theorem su52_exists_order3_normalizes_two : ∃ y : SU52, orderOf y = 3 ∧
    ∃ W : Subgroup SU52, IsPGroup 2 W ∧ W ≠ ⊥ ∧ y ∈ Subgroup.normalizer (W : Set SU52) := by
  have hv2 : vSU ^ 2 = 1 := by
    have := pow_orderOf_eq_one vSU
    rwa [orderOf_vSU] at this
  have hv1 : vSU ≠ 1 := by
    intro h
    have := orderOf_vSU
    rw [h, orderOf_one] at this
    omega
  have hc : Commute e₂SU vSU := ext_mat (by rw [mat_mul, mat_mul, mat_e₂SU, mat_vSU]; decide)
  refine ⟨e₂SU, orderOf_e₂SU, Subgroup.zpowers vSU, isPGroup_zpowers_of_pow_eq_one hv2, ?_,
    mem_normalizer_zpowers_of_commute hc⟩
  intro h
  have : vSU ∈ (⊥ : Subgroup SU52) := h ▸ Subgroup.mem_zpowers vSU
  exact hv1 (Subgroup.mem_bot.1 this)

def Acoord (a c d e : F4) : Matrix (Fin 5) (Fin 5) F4 := x₂Mat a * x₃Mat c * x₄Mat d e

theorem Acoord_mul (a c d e a' c' d' e' : F4) :
    Acoord a c d e * Acoord a' c' d' e' =
      Acoord (a + a') (c + c') (d + d') (e + e' + bar d * d' + a' * bar c + bar a' * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Acoord, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]
  all_goals linear_combination (-(bar a' * c)) * CFSG.Fischer.F4.two_eq_zero

theorem Acoord_entries (a c d e : F4) :
    Acoord a c d e 1 0 = a ∧ Acoord a c d e 3 0 = c ∧ Acoord a c d e 2 0 = d ∧
      Acoord a c d e 4 0 = e + bar a * c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Acoord, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five]
  all_goals ring

theorem Acoord_inj {a c d e a' c' d' e' : F4}
    (h : Acoord a c d e = Acoord a' c' d' e') : a = a' ∧ c = c' ∧ d = d' ∧ e = e' := by
  obtain ⟨h1, h3, h2, h4⟩ := Acoord_entries a c d e
  obtain ⟨h1', h3', h2', h4'⟩ := Acoord_entries a' c' d' e'
  have ea : a = a' := by rw [← h1, ← h1', h]
  have ec : c = c' := by rw [← h3, ← h3', h]
  have ed : d = d' := by rw [← h2, ← h2', h]
  refine ⟨ea, ec, ed, ?_⟩
  have h4'' : e + bar a * c = e' + bar a' * c' := by rw [← h4, ← h4', h]
  rw [← ea, ← ec] at h4''
  exact add_right_cancel h4''

theorem A₁_coord {g : SU52} (hg : g ∈ A₁sub) :
    ∃ a c d e : F4, d * bar d = e + bar e ∧ mat g = Acoord a c d e := by
  obtain ⟨hgS, h0, h1⟩ := mem_A₁sub.1 hg
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, k₁, l₁, -⟩ :=
    exists_eq_nf_coord hgS
  rw [h0] at k₁
  rw [h1] at l₁
  rw [← k₁, ← l₁] at e₁
  have hg₁ := eq_one_of_x₁ e₁
  refine ⟨a₂, a₃, a₄, b₄, x₄_coord_rel e₄, ?_⟩
  rw [hg₁, one_mul, mat_mul, mat_mul, e₂, e₃, e₄]
  rfl

noncomputable def thetaA : ↥A₁sub →* Multiplicative (F4 × F4 × F4) where
  toFun g := Multiplicative.ofAdd (mat (g : SU52) 1 0, mat (g : SU52) 3 0, mat (g : SU52) 2 0)
  map_one' := by
    show Multiplicative.ofAdd (mat (1 : SU52) 1 0, mat (1 : SU52) 3 0, mat (1 : SU52) 2 0) = 1
    rw [mat_one]
    rfl
  map_mul' g h := by
    obtain ⟨a, c, d, e, -, hg⟩ := A₁_coord g.2
    obtain ⟨a', c', d', e', -, hh⟩ := A₁_coord h.2
    have hgh : mat ((g * h : ↥A₁sub) : SU52) =
        Acoord (a + a') (c + c') (d + d') (e + e' + bar d * d' + a' * bar c + bar a' * c) := by
      rw [Subgroup.coe_mul, mat_mul, hg, hh, Acoord_mul]
    show Multiplicative.ofAdd (mat ((g * h : ↥A₁sub) : SU52) 1 0, mat ((g * h : ↥A₁sub) : SU52) 3 0,
        mat ((g * h : ↥A₁sub) : SU52) 2 0) =
      Multiplicative.ofAdd (mat (g : SU52) 1 0, mat (g : SU52) 3 0, mat (g : SU52) 2 0) *
        Multiplicative.ofAdd (mat (h : SU52) 1 0, mat (h : SU52) 3 0, mat (h : SU52) 2 0)
    rw [hgh, hg, hh, (Acoord_entries (a + a') _ _ _).1, (Acoord_entries (a + a') (c + c') _ _).2.1,
      (Acoord_entries (a + a') (c + c') (d + d') _).2.2.1, (Acoord_entries a _ _ _).1,
      (Acoord_entries a c _ _).2.1, (Acoord_entries a c d _).2.2.1,
      (Acoord_entries a' _ _ _).1, (Acoord_entries a' c' _ _).2.1,
      (Acoord_entries a' c' d' _).2.2.1]
    rfl

theorem thetaA_apply_coord {g : ↥A₁sub} {a c d e : F4} (hg : mat (g : SU52) = Acoord a c d e) :
    thetaA g = Multiplicative.ofAdd (a, c, d) := by
  show Multiplicative.ofAdd (mat (g : SU52) 1 0, mat (g : SU52) 3 0, mat (g : SU52) 2 0) = _
  rw [hg, (Acoord_entries a _ _ _).1, (Acoord_entries a c _ _).2.1,
    (Acoord_entries a c d _).2.2.1]

noncomputable def ZA : Subgroup ↥A₁sub := ZX₄sub.subgroupOf A₁sub

theorem mem_ZA_iff {g : ↥A₁sub} : g ∈ ZA ↔ ∃ e : F4, e + bar e = 0 ∧ mat (g : SU52) = x₄Mat 0 e := by
  rw [ZA, Subgroup.mem_subgroupOf, ZX₄sub, mem_x₄Sub]
  constructor
  · rintro ⟨a, b, ha, hab⟩
    subst ha
    refine ⟨b, ?_, hab⟩
    have := x₄_coord_rel hab
    simpa using this.symm
  · rintro ⟨e, he, hg⟩
    exact ⟨0, e, rfl, hg⟩

theorem thetaA_ker : thetaA.ker = ZA := by
  ext g
  rw [MonoidHom.mem_ker, mem_ZA_iff]
  obtain ⟨a, c, d, e, hrel, hg⟩ := A₁_coord g.2
  rw [thetaA_apply_coord hg]
  constructor
  · intro h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, toAdd_one, Prod.mk_eq_zero] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    refine ⟨e, ?_, ?_⟩
    · simpa using hrel.symm
    · rw [hg, Acoord, x₂Mat_zero, x₃Mat_zero, one_mul, one_mul]
  · rintro ⟨e', he', hg'⟩
    have h1 := (Acoord_entries a c d e).1
    have h3 := (Acoord_entries a c d e).2.1
    have h2 := (Acoord_entries a c d e).2.2.1
    rw [← hg, hg'] at h1 h3 h2
    have e1 : x₄Mat 0 e' 1 0 = 0 := by simp [x₄Mat]
    have e3 : x₄Mat 0 e' 3 0 = 0 := by simp [x₄Mat]
    have e2 : x₄Mat 0 e' 2 0 = 0 := by simp [x₄Mat]
    rw [e1] at h1
    rw [e3] at h3
    rw [e2] at h2
    subst h1 h3 h2
    rfl

theorem Acoord_x₄ (e : F4) : Acoord 0 0 0 e = x₄Mat 0 e := by
  rw [Acoord, x₂Mat_zero, x₃Mat_zero, one_mul, one_mul]

theorem Acoord_x₂ (t : F4) : Acoord t 0 0 0 = x₂Mat t := by
  rw [Acoord, x₃Mat_zero, x₄Mat_zero, mul_one, mul_one]

theorem Acoord_x₃ (t : F4) : Acoord 0 t 0 0 = x₃Mat t := by
  rw [Acoord, x₂Mat_zero, x₄Mat_zero, one_mul, mul_one]

theorem Acoord_x₄' (t s : F4) : Acoord 0 0 t s = x₄Mat t s := by
  rw [Acoord, x₂Mat_zero, x₃Mat_zero, one_mul, one_mul]

theorem A₁_zA_central {z : ↥A₁sub} (hz : z ∈ ZA) (g : ↥A₁sub) : g * z = z * g := by
  obtain ⟨e', -, hze⟩ := mem_ZA_iff.1 hz
  obtain ⟨a, c, d, e, -, hg⟩ := A₁_coord g.2
  rw [← Acoord_x₄] at hze
  apply Subtype.ext
  apply ext_mat
  rw [Subgroup.coe_mul, Subgroup.coe_mul, mat_mul, mat_mul, hg, hze, Acoord_mul, Acoord_mul]
  have : bar (0 : F4) = 0 := map_zero bar
  simp only [this]
  congr 1 <;> ring

theorem x₂SU_mem_A₁ (t : F4) : x₂SU t ∈ A₁sub :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (x₂SU_mem t))

theorem x₃SU_mem_A₁ (t : F4) : x₃SU t ∈ A₁sub :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (x₃SU_mem t))

theorem x₄SU_mem_A₁ (t s : F4) (h : t * bar t = s + bar s) : x₄SU t s h ∈ A₁sub :=
  Subgroup.mem_sup_right (x₄SU_mem t s h)

theorem F4_aux₁ : ∀ c : F4, (∀ t : F4, t * bar c + bar t * c = 0) → c = 0 := by decide
theorem F4_aux₂ : ∀ a : F4, (∀ t : F4, a * bar t + bar a * t = 0) → a = 0 := by decide
theorem F4_aux₃ : ∀ d : F4, (∀ t : F4, bar d * t + bar t * d = 0) → d = 0 := by decide
theorem F4_aux₄ : ∀ t : F4, ∃ s : F4, t * bar t = s + bar s := by decide
theorem F4_pow_two (w : Multiplicative (F4 × F4 × F4)) : w ^ 2 = 1 := by
  revert w
  decide

theorem card_ZA : Nat.card ZA = 2 := by
  have hle : ZX₄sub ≤ A₁sub := ZX₄sub_le_X₄sub.trans le_sup_right
  rw [ZA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_ZX₄sub]

theorem isExtraspecial_A₁ : CFSG.IsExtraspecialPGroup 2 ↥A₁sub := by
  haveI : Finite ↥A₁sub := inferInstance
  have hP : IsPGroup 2 ↥A₁sub := IsPGroup.of_card (n := 7) card_A₁sub
  have hZc : ZA ≤ Subgroup.center ↥A₁sub := fun z hz =>
    Subgroup.mem_center_iff.2 fun g => A₁_zA_central hz g
  have hcomm : ∀ x y : ↥A₁sub, ⁅x, y⁆ ∈ ZA := by
    intro x y
    rw [← thetaA_ker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hsq : ∀ x : ↥A₁sub, x ^ 2 ∈ ZA := by
    intro x
    rw [← thetaA_ker, MonoidHom.mem_ker, map_pow]
    exact F4_pow_two _
  have hnab : ∃ x : ↥A₁sub, x ∉ ZA := by
    refine ⟨⟨x₂SU 1, x₂SU_mem_A₁ 1⟩, fun h => ?_⟩
    obtain ⟨e, -, he⟩ := mem_ZA_iff.1 h
    have := congrFun (congrFun he 1) 0
    simp [x₂Mat, x₄Mat] at this
  have hcent : ∀ x : ↥A₁sub, (∀ y : ↥A₁sub, x * y = y * x) → x ∈ ZA := by
    intro x hx
    obtain ⟨a, c, d, e, hrel, hxm⟩ := A₁_coord x.2
    have key : ∀ (y : SU52) (hy : y ∈ A₁sub) (a' c' d' e' : F4), mat y = Acoord a' c' d' e' →
        Acoord a c d e * Acoord a' c' d' e' = Acoord a' c' d' e' * Acoord a c d e := by
      intro y hy a' c' d' e' hym
      have := congrArg (fun g : ↥A₁sub => mat (g : SU52)) (hx ⟨y, hy⟩)
      simpa only [Subgroup.coe_mul, mat_mul, hxm, hym] using this
    have t2 : ∀ t : F4, t * bar c + bar t * c = 0 := by
      intro t
      have h := key (x₂SU t) (x₂SU_mem_A₁ t) t 0 0 0 (by rw [mat_x₂SU, Acoord_x₂])
      rw [Acoord_mul, Acoord_mul] at h
      obtain ⟨-, -, -, h4⟩ := Acoord_inj h
      rw [map_zero] at h4
      linear_combination h4
    have t3 : ∀ t : F4, a * bar t + bar a * t = 0 := by
      intro t
      have h := key (x₃SU t) (x₃SU_mem_A₁ t) 0 t 0 0 (by rw [mat_x₃SU, Acoord_x₃])
      rw [Acoord_mul, Acoord_mul] at h
      obtain ⟨-, -, -, h4⟩ := Acoord_inj h
      rw [map_zero] at h4
      linear_combination (-1 : F4) * h4
    have t4 : ∀ t : F4, bar d * t + bar t * d = 0 := by
      intro t
      obtain ⟨s, hs⟩ := F4_aux₄ t
      have h := key (x₄SU t s hs) (x₄SU_mem_A₁ t s hs) 0 0 t s (by rw [mat_x₄SU, Acoord_x₄'])
      rw [Acoord_mul, Acoord_mul] at h
      obtain ⟨-, -, -, h4⟩ := Acoord_inj h
      rw [map_zero] at h4
      linear_combination h4 + (bar t * d) * CFSG.Fischer.F4.two_eq_zero
    have hc0 := F4_aux₁ c t2
    have ha0 := F4_aux₂ a t3
    have hd0 := F4_aux₃ d t4
    subst hc0 ha0 hd0
    rw [mem_ZA_iff]
    refine ⟨e, ?_, ?_⟩
    · simpa using hrel.symm
    · rw [hxm, Acoord_x₄]
  exact CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center hP card_ZA hZc hcomm hsq hcent
    hnab

theorem A₁_central_mem_ZA : ∀ x : ↥A₁sub, (∀ y : ↥A₁sub, x * y = y * x) → x ∈ ZA := by
  intro x hx
  obtain ⟨a, c, d, e, hrel, hxm⟩ := A₁_coord x.2
  have key : ∀ (y : SU52) (hy : y ∈ A₁sub) (a' c' d' e' : F4), mat y = Acoord a' c' d' e' →
      Acoord a c d e * Acoord a' c' d' e' = Acoord a' c' d' e' * Acoord a c d e := by
    intro y hy a' c' d' e' hym
    have := congrArg (fun g : ↥A₁sub => mat (g : SU52)) (hx ⟨y, hy⟩)
    simpa only [Subgroup.coe_mul, mat_mul, hxm, hym] using this
  have t2 : ∀ t : F4, t * bar c + bar t * c = 0 := by
    intro t
    have h := key (x₂SU t) (x₂SU_mem_A₁ t) t 0 0 0 (by rw [mat_x₂SU, Acoord_x₂])
    rw [Acoord_mul, Acoord_mul] at h
    obtain ⟨-, -, -, h4⟩ := Acoord_inj h
    rw [map_zero] at h4
    linear_combination h4
  have t3 : ∀ t : F4, a * bar t + bar a * t = 0 := by
    intro t
    have h := key (x₃SU t) (x₃SU_mem_A₁ t) 0 t 0 0 (by rw [mat_x₃SU, Acoord_x₃])
    rw [Acoord_mul, Acoord_mul] at h
    obtain ⟨-, -, -, h4⟩ := Acoord_inj h
    rw [map_zero] at h4
    linear_combination (-1 : F4) * h4
  have t4 : ∀ t : F4, bar d * t + bar t * d = 0 := by
    intro t
    obtain ⟨s, hs⟩ := F4_aux₄ t
    have h := key (x₄SU t s hs) (x₄SU_mem_A₁ t s hs) 0 0 t s (by rw [mat_x₄SU, Acoord_x₄'])
    rw [Acoord_mul, Acoord_mul] at h
    obtain ⟨-, -, -, h4⟩ := Acoord_inj h
    rw [map_zero] at h4
    linear_combination h4 + (bar t * d) * CFSG.Fischer.F4.two_eq_zero
  have hc0 := F4_aux₁ c t2
  have ha0 := F4_aux₂ a t3
  have hd0 := F4_aux₃ d t4
  subst hc0 ha0 hd0
  rw [mem_ZA_iff]
  refine ⟨e, ?_, ?_⟩
  · simpa using hrel.symm
  · rw [hxm, Acoord_x₄]

theorem X₂sub_isElemAbelian : IsElemAbelian 2 X₂sub := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, hs⟩ := mem_X₂sub.1 a.2
    obtain ⟨t, ht⟩ := mem_X₂sub.1 b.2
    apply Subtype.ext
    apply ext_mat
    change mat ((a : SU52) * b) = mat ((b : SU52) * a)
    rw [mat_mul, mat_mul, hs, ht, x₂Mat_mul, x₂Mat_mul, add_comm]
  · obtain ⟨s, hs⟩ := mem_X₂sub.1 hx
    apply ext_mat
    rw [mat_pow_two, hs, x₂Mat_mul, CharTwo.add_self_eq_zero, x₂Mat_zero, mat_one]

theorem X₂sub_le_A₁sub : X₂sub ≤ A₁sub := le_sup_left.trans le_sup_left

theorem X₂sub_inf_center :
    X₂sub ⊓ (A₁sub ⊓ Subgroup.centralizer (A₁sub : Set SU52)) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg2, hgA, hgc⟩
  have hcent : ∀ y : ↥A₁sub, (⟨g, hgA⟩ : ↥A₁sub) * y = y * ⟨g, hgA⟩ := fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.1 hgc y y.2).symm
  obtain ⟨e, -, he⟩ := mem_ZA_iff.1 (A₁_central_mem_ZA ⟨g, hgA⟩ hcent)
  obtain ⟨s, hs⟩ := mem_X₂sub.1 hg2
  have h10 := congrFun (congrFun (hs.symm.trans he) 1) 0
  simp [x₂Mat, x₄Mat] at h10
  subst h10
  exact Subgroup.mem_bot.2 (eq_one_of_x₂ hs)

theorem su52_exists_extraspecial_four : ∃ T U : Subgroup SU52,
    CFSG.IsExtraspecialPGroup 2 ↥T ∧ Nat.card T = 2 ^ (2 * 3 + 1) ∧ U ≤ T ∧ IsElemAbelian 2 U ∧
      Nat.card U = 4 ∧ U ⊓ (T ⊓ Subgroup.centralizer (T : Set SU52)) = ⊥ :=
  ⟨A₁sub, X₂sub, isExtraspecial_A₁, by rw [card_A₁sub], X₂sub_le_A₁sub, X₂sub_isElemAbelian,
    card_X₂sub, X₂sub_inf_center⟩

end U52

open U52

section Centre

variable {G : Type} [Group G] [Finite G]

theorem center_pQuot_eq_bot_u5two (hGA : CFSG.Open.GriessAllModelsStatement) {J : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 J)) (h : catalogIs (PSimple 3 J) S9.isU5two) :
    Subgroup.center (PQuot 3 J) = ⊥ := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isU5two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' 4 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hq hm (a := 1) (b := 1) (c := 1) (d := 1)
    (by decide) (by decide) (by norm_num)
  by_contra hne
  haveI : Nontrivial (Subgroup.center (PQuot 3 J)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact false_of_pGroup_dvd Nat.prime_three
    (CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three J) hdvd
    (by norm_num)

end Centre

theorem extraspecialU5At_holds (G : Type) [Group G] [Finite G] :
    ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
      Odd (Nat.card (GLAPPrimeCoreOf 3 L)) →
      (catalogIs (PSimple 3 L) S9.isU5two → ∃ T : Subgroup G, T ≤ L ∧ IsExtraspecialTwo T 3 ∧
        ∃ U : Subgroup G, U ≤ T ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
          U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) = ⊥) := by
  intro X L hX hL hodd hcat
  obtain ⟨e⟩ := bridge_u5two hcat
  obtain ⟨π, hπs, hkc⟩ := exists_hom_of_simple_equiv e
  have hk2 : ¬ 2 ∣ Nat.card π.ker := odd_card_ker L hkc hodd
  obtain ⟨Tb, Ub, hT, hTc, hUT, hUe, hUc, hUz⟩ := U52.su52_exists_extraspecial_four
  exact lift_extraspecial_four π hk2
    (by rw [MonoidHom.range_eq_top_of_surjective π hπs]; exact le_top) hT hTc hUT hUe hUc hUz

theorem extraspecialU5D4At_of_halves {G : Type} [Group G] [Finite G]
    (hU5 : ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
      Odd (Nat.card (GLAPPrimeCoreOf 3 L)) →
      (catalogIs (PSimple 3 L) S9.isU5two → ∃ T : Subgroup G, T ≤ L ∧ IsExtraspecialTwo T 3 ∧
        ∃ U : Subgroup G, U ≤ T ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
          U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) = ⊥))
    (hTD4 : ∀ (X L : Subgroup G), CFSG.Open.IsKGroup ↥X → GLAPComponent 3 X L →
      Odd (Nat.card (GLAPPrimeCoreOf 3 L)) →
      (catalogIs (PSimple 3 L) S9.isTD4two → ∃ T : Subgroup G, T ≤ L ∧ IsExtraspecialTwo T 4 ∧
        ∃ t ∈ T, t ^ 2 = 1 ∧ t ∉ T ⊓ Subgroup.centralizer (T : Set G))) :
    ExtraspecialU5D4At G :=
  fun X L hX hL hodd => ⟨hU5 X L hX hL hodd, hTD4 X L hX hL hodd⟩

theorem exists_component_of_layer_lift {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) {M : Type} [Group M] (π : ↥L →* M)
    (hπ : Function.Surjective π) (hker : π.ker = GLAPPrimeCore 3 ↥L) {y : ↥L} (hy3 : y ^ 3 = 1)
    {Kb : Subgroup M} (hKc : Kb ≤ Subgroup.centralizer ({π y} : Set M))
    (hKC : Subgroup.centralizer ({π y} : Set M) = Kb ⊔ Subgroup.zpowers (π y))
    (hKz : Kb ⊓ Subgroup.zpowers (π y) = ⊥) (hKs : IsSimpleGroup ↥Kb)
    (hKn : ¬ IsMulCommutative ↥Kb) (hK3 : 3 ∣ Nat.card Kb) :
    ∃ J : Subgroup G, GLAPComponent 3 (L ⊓ S9.cx (y : G)) J ∧ Nonempty (PSimple 3 J ≃* Kb) ∧
      GLAPPrimeCoreOf 3 J ≤ GLAPPrimeCoreOf 3 L := by
  classical
  haveI : Finite M := Finite.of_surjective π hπ
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hker]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  set H : Subgroup G := L ⊓ S9.cx (y : G) with hH
  have hHL : H ≤ L := inf_le_left
  let φ : ↥H →* M := π.comp (Subgroup.inclusion hHL)
  have hφrange : φ.range = Subgroup.centralizer ({π y} : Set M) := by
    apply le_antisymm
    · rintro _ ⟨h, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc : (h : G) * (y : G) = (y : G) * h :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h.2).2
      have : (Subgroup.inclusion hHL h) * y = y * (Subgroup.inclusion hHL h) := Subtype.ext hc
      show π (Subgroup.inclusion hHL h) * π y = π y * π (Subgroup.inclusion hHL h)
      rw [← map_mul, ← map_mul, this]
    · intro m hm
      have hmc : m * π y = π y * m := Subgroup.mem_centralizer_singleton_iff.1 hm
      obtain ⟨h, hhy, hhm⟩ := exists_mem_centralizer_lift Nat.prime_three π hk3 hy3
        (by rw [MonoidHom.range_eq_top_of_surjective π hπ]; exact Subgroup.mem_top _) hmc
      have hhH : (h : G) ∈ H := Subgroup.mem_inf.2 ⟨h.2,
        Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hhy)⟩
      exact ⟨⟨h, hhH⟩, hhm⟩
  have hy3' : (π y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hker_le : φ.ker ≤ GLAPPrimeCore 3 ↥H := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    refine le_sSup ⟨inferInstance, ?_⟩
    have hdvd : Nat.card φ.ker ∣ Nat.card π.ker := by
      have h1 : φ.ker.map (Subgroup.inclusion hHL) ≤ π.ker := by
        rintro _ ⟨k, hk, rfl⟩
        exact hk
      rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hHL) (K := φ.ker)]
      exact Subgroup.card_dvd_of_le h1
    exact Nat.Coprime.coprime_dvd_right hdvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hk3)
  have hle_ker : GLAPPrimeCore 3 ↥H ≤ φ.ker := by
    set N := GLAPPrimeCore 3 ↥H with hN
    have hN3 : ¬ 3 ∣ Nat.card (N.map φ) := by
      have hdvd : Nat.card (N.map φ) ∣ Nat.card N := Subgroup.card_map_dvd N φ
      intro h3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
        (h3.trans hdvd)
    have hmem : ∀ p ∈ Kb ⊔ Subgroup.zpowers (π y), ∃ h : ↥H, φ h = p := by
      intro p hp
      have : p ∈ φ.range := by rw [hφrange, hKC]; exact hp
      exact this
    have hbot : N.map φ = ⊥ := by
      refine normal_threePrime_eq_bot hy3' hKs hKn hK3 hKc ?_ ?_ hN3
      · rw [← hKC, ← hφrange]
        exact Subgroup.map_le_range φ N
      · intro p hp n hn
        obtain ⟨h, rfl⟩ := hmem p hp
        obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.1 hn
        refine Subgroup.mem_map.2 ⟨h * n₀ * h⁻¹, ?_, by simp [map_mul, map_inv]⟩
        exact (inferInstance : N.Normal).conj_mem n₀ hn₀ h
    intro n hn
    have : φ n ∈ N.map φ := Subgroup.mem_map_of_mem φ hn
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hφker : φ.ker = GLAPPrimeCore 3 ↥H := le_antisymm hker_le hle_ker
  let θ : (↥H ⧸ GLAPPrimeCore 3 ↥H) ≃* ↥φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hKr : Kb ≤ φ.range := by rw [hφrange]; exact hKc
  let Kt : Subgroup ↥φ.range := Kb.subgroupOf φ.range
  have hKtn : Kt.Normal := by
    refine ⟨fun k hk p => ?_⟩
    have hp : (p : M) ∈ Kb ⊔ Subgroup.zpowers (π y) := by
      rw [← hKC, ← hφrange]
      exact p.2
    have hk' : (k : M) ∈ Kb := hk
    have := kb_conj_mem hKc (p : M) hp (k : M) hk'
    exact (show ((p * k * p⁻¹ : ↥φ.range) : M) ∈ Kb from by simpa using this)
  let K : Subgroup (↥H ⧸ GLAPPrimeCore 3 ↥H) := Kt.map θ.symm.toMonoidHom
  have hKn' : K.Normal := hKtn.map θ.symm.toMonoidHom θ.symm.surjective
  let eKb : ↥K ≃* ↥Kb :=
    (Kt.equivMapOfInjective θ.symm.toMonoidHom θ.symm.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hKr)
  have hqs : CFSG.Open.IsQuasisimple ↥K :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eKb.symm
      (isQuasisimple_of_simple_nonabelian hKn)
  have hcomp : IsComponentOf K ⊤ :=
    ⟨le_top, IsSubnormal.step le_top (Subgroup.normal_subgroupOf) (IsSubnormal.refl _), hqs⟩
  obtain ⟨J, hJ, hJbar⟩ := exists_glaPComponent_barX_eq H hcomp
  have hJH : J ≤ H := hJ.1
  have hJsn : IsSubnormal J H := hJ.2.1
  let eP : PQuot 3 J ≃* ↥Kb :=
    ((quotEquivBarX Nat.prime_three hJH hJsn).trans (MulEquiv.subgroupCongr hJbar)).trans eKb
  refine ⟨J, hJ, ⟨?_⟩, ?_⟩
  · exact (QuotientGroup.congr _ _ eP (Subgroup.map_center_eq eP)).trans
      ((QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hKn)).trans
        QuotientGroup.quotientBot)
  · intro x hx
    have h1 : x ∈ J ⊓ GLAPPrimeCoreOf 3 H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hJsn]
      exact hx
    have h2 : x ∈ (GLAPPrimeCore 3 ↥H).map H.subtype := (Subgroup.mem_inf.1 h1).2
    rw [← hφker] at h2
    obtain ⟨k, hk, rfl⟩ := h2
    have hk' : Subgroup.inclusion hHL k ∈ π.ker := hk
    rw [hker] at hk'
    exact ⟨Subgroup.inclusion hHL k, hk', rfl⟩

section Rows

variable {G : Type} [Group G] [Finite G]

theorem i81U5At_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) : I81U5At G := by
  intro X L hX hL hcat
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  have hZ := center_pQuot_eq_bot_u5two hGA hq hcat
  obtain ⟨e⟩ := bridge_u5two hcat
  obtain ⟨π, hπs, hker⟩ := exists_hom_ker_eq_of_center_bot (e.trans U52Layer.equivM5) hZ
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hker]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨Kb, hKc, hKC, hKz, hKs, hKn, hK3, hKcat⟩ := U52Layer.m5_u4_layer
  obtain ⟨y, hy, hyπ⟩ := exists_pow_lift Nat.prime_three π hk3
    (by rw [MonoidHom.range_eq_top_of_surjective π hπs]; exact Subgroup.mem_top _)
    U52Layer.yM5_pow_three
  rw [← hyπ] at hKc hKC hKz
  obtain ⟨J, hJ, ⟨ε⟩, hJO⟩ := exists_component_of_layer_lift hL π hπs hker hy hKc hKC hKz hKs hKn
    hK3
  refine ⟨(y : G), y.2, congrArg Subtype.val hy, ?_, J, hJ, ?_, hJO⟩
  · intro h1
    apply U52Layer.yM5_ne_one
    rw [← hyπ, show y = 1 from Subtype.ext h1, map_one]
  · exact (catalogIs_congr ε).2 hKcat

end Rows

section Holds

theorem i81U5At_holds (G : Type) [Group G] [Finite G] : I81U5At G :=
  i81U5At_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end Holds

end CFSG.LocalAnalysis.GLTheoremA.CatB
