module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTu
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4MAct
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4MDelta
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Sec4FSetup {G : Type} [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G)
    (A B : Subgroup G) (φ : (Fin 7 → ZMod 2) → G) : Prop where
  inputs : Sec4FInputs
  ctx : Sec4Ctx G t L S z
  data : Sec4AData t L S z A B φ
  not_tz : ¬ ∃ h : G, h⁻¹ * t * h = t * z
  tu6 : ∀ u : G, u ∈ L → orderOf u = 2 → InducesTypeSome L u 7 1 6 (-1) →
    ∃ h : G, t * u = h⁻¹ * t * h
  weak : conjClassIn ⊤ t ∩ (A : Set G) = conjClassIn (normalizer (A : Set G)) t

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4F_mem_sup_comm {X Y : Subgroup G} (hc : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) {x : G}
    (hx : x ∈ X ⊔ Y) : ∃ a ∈ X, ∃ b ∈ Y, x = a * b := by
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ X, ∃ b ∈ Y, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', X.mul_mem ha ha', b * b', Y.mul_mem hb hb', ?_⟩
        have h1 : b * a' = a' * b := (hc a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [h1]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, X.one_mem, 1, Y.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, X.inv_mem ha, b⁻¹, Y.inv_mem hb, ?_⟩
        have h1 : b * a = a * b := (hc a ha b hb).symm
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h1]
          _ = a⁻¹ * b⁻¹ := by group }
  have hle : X ⊔ Y ≤ T :=
    sup_le (fun a ha => ⟨a, ha, 1, Y.one_mem, by simp⟩)
      (fun b hb => ⟨1, X.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem sec4FSetup_of_data (I : Sec4FInputs) (hctx : Sec4Ctx G t L S z)
    (hnot : ¬ ∃ h : G, h⁻¹ * t * h = t * z) (hD : Sec4AData t L S z A B φ) :
    Sec4FSetup t L S z A B φ :=
  ⟨I, hctx, hD, hnot, fun _ hu hu2 hu6 => sec4F_tu_conj I hctx hnot hu hu2 hu6,
    (I.h46b G t L S z hctx A hD.isMax).2⟩

theorem Sec4FSetup.omega7 (h : Sec4FSetup t L S z A B φ) : IsOmega7Group L :=
  sec4_isOmega7Group h.ctx.toSec4Setting

theorem Sec4FSetup.t_sq (h : Sec4FSetup t L S z A B φ) : t * t = 1 := by
  rw [← pow_two, ← h.ctx.involution, pow_orderOf_eq_one]

theorem Sec4FSetup.t_mem_A (h : Sec4FSetup t L S z A B φ) : t ∈ A := by
  rw [h.data.A_eq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem Sec4FSetup.t_cent_L (h : Sec4FSetup t L S z A B φ) {l : G} (hl : l ∈ L) :
    t * l = l * t :=
  (Subgroup.mem_centralizer_iff.mp
    (sec4_t_mem_centralizer h.ctx.toSec4Setting.toSec3SettingLB.toSec3Setting) l hl).symm

theorem Sec4FSetup.t_mem_cent (h : Sec4FSetup t L S z A B φ) : t ∈ centralizer (L : Set G) :=
  sec4_t_mem_centralizer h.ctx.toSec4Setting.toSec3SettingLB.toSec3Setting

theorem Sec4FSetup.A_comm (h : Sec4FSetup t L S z A B φ) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a := by
  haveI : IsMulCommutative ↥A := h.data.isMax.2.1.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

theorem Sec4FSetup.A_sq (h : Sec4FSetup t L S z A B φ) {a : G} (ha : a ∈ A) : a * a = 1 := by
  simpa [pow_two] using h.data.isMax.2.1.2 a ha

theorem Sec4FSetup.B_le_A (h : Sec4FSetup t L S z A B φ) : B ≤ A := by
  rw [← h.data.B_eq]
  exact inf_le_left

theorem Sec4FSetup.B_le_L (h : Sec4FSetup t L S z A B φ) : B ≤ L := by
  rw [← h.data.B_eq]
  exact inf_le_right

theorem Sec4FSetup.cent_le_normalizer (h : Sec4FSetup t L S z A B φ) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) : c ∈ normalizer (L : Set G) :=
  sec4_mem_normalizer h.inputs.h36 h.ctx.toSec4Setting.toSec3SettingLB c hc

theorem Sec4FSetup.mem_cent_t_of_mem_A (h : Sec4FSetup t L S z A B φ) {a : G} (ha : a ∈ A) :
    a ∈ centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h.A_comm ha h.t_mem_A

theorem Sec4FSetup.mem_A_cases (h : Sec4FSetup t L S z A B φ) {x : G} (hx : x ∈ A) :
    ∃ b ∈ B, x = b ∨ x = b * t := by
  rw [h.data.A_eq] at hx
  have hcomm : ∀ b ∈ B, ∀ c ∈ Subgroup.zpowers t, b * c = c * b := by
    intro b hb c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_left (h.t_cent_L (h.B_le_L hb)) k).eq.symm
  obtain ⟨b, hb, c, hc, rfl⟩ := sec4F_mem_sup_comm hcomm hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  refine ⟨b, hb, ?_⟩
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact h.t_sq
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    have : t ^ (j + j) = 1 := by
      rw [← two_mul, zpow_mul]
      simp [ht2]
    rw [this, mul_one]
  · right
    have : t ^ (2 * j + 1) = t := by
      rw [zpow_add, zpow_mul]
      simp [ht2]
    rw [this]

end CFSG.OddStandard.SmallF3.Omega
