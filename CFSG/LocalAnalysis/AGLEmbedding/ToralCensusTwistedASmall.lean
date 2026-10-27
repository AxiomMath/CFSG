module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAFactors
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryInvariant

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.LinearGroups Polynomial Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem det_restrict_eq_of_sup {x : Module.End K V} {W P Q : Submodule K V} (hPW : P ≤ W)
    (hQW : Q ≤ W) (hPQ : P ⊓ Q = ⊥) (hsup : P ⊔ Q = W) {ν ν' : K}
    (hP : ∀ v ∈ P, x v = ν • v) (hQ : ∀ v ∈ Q, x v = ν' • v) (hWx : ∀ w ∈ W, x w ∈ W) :
    LinearMap.det (x.restrict hWx) = ν ^ finrank K P * ν' ^ finrank K Q := by
  set P' : Submodule K W := P.comap W.subtype
  set Q' : Submodule K W := Q.comap W.subtype
  have hc : IsCompl P' Q' := by
    refine ⟨Submodule.disjoint_def.mpr fun w hwP hwQ => ?_, codisjoint_iff.mpr ?_⟩
    · have hw : (w : V) ∈ P ⊓ Q := Submodule.mem_inf.mpr ⟨hwP, hwQ⟩
      rw [hPQ, Submodule.mem_bot] at hw
      exact Subtype.ext hw
    · refine eq_top_iff.mpr fun w _ => ?_
      have hw : (w : V) ∈ P ⊔ Q := by rw [hsup]; exact w.2
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hw
      have hw' : w = ⟨a, hPW ha⟩ + ⟨b, hQW hb⟩ := Subtype.ext (by simp [hab])
      rw [hw']
      exact Submodule.add_mem_sup ha hb
  set T := x.restrict hWx
  have hTP : ∀ w ∈ P', T w ∈ P' := by
    intro w hw
    change x w ∈ P
    rw [hP (w : V) hw]
    exact P.smul_mem ν hw
  have hTQ : ∀ w ∈ Q', T w ∈ Q' := by
    intro w hw
    change x w ∈ Q
    rw [hQ (w : V) hw]
    exact Q.smul_mem ν' hw
  have h1 : T.restrict hTP = ν • LinearMap.id := by
    ext w
    change x w = ν • (w : V)
    exact hP _ w.2
  have h2 : T.restrict hTQ = ν' • LinearMap.id := by
    ext w
    change x w = ν' • (w : V)
    exact hQ _ w.2
  rw [det_eq_mul_det_of_isCompl hc T hTP hTQ, h1, h2, LinearMap.det_smul, LinearMap.det_smul,
    LinearMap.det_id, LinearMap.det_id, mul_one, mul_one,
    (Submodule.comapSubtypeEquivOfLe hPW).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hQW).finrank_eq]

omit [FiniteDimensional K V] in
theorem mem_primaryComponent_X_sub_C_iff {x : Module.End K V} {ν : K} {v : V} :
    v ∈ primaryComponent x (X - C ν) ↔ x v = ν • v := by
  rw [mem_primaryComponent, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
    Module.algebraMap_end_apply, sub_eq_zero]

theorem eq_one_of_pow_eq_one_of_le_two [CharP K 2] {ν : K} {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d ≤ 2)
    (h : ν ^ d = 1) : ν = 1 := by
  interval_cases d
  · simpa using h
  · have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : (ν - 1) ^ 2 = 0 := by linear_combination h - (ν - 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

variable {f : ℕ} (hK : UnitaryFieldData 2 f K) [Finite K]
include hK

theorem false_of_finrank_le_two {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
    {x : LinearMap.GeneralLinearGroup K V} (H : UnitaryPrimaryData hK.bar B x)
    (hdet : LinearMap.det (x : Module.End K V) = 1) {m : ℕ} (hm : m.Prime)
    (hmq : m ∣ 2 ^ f - 1) (hx : aeval (x : Module.End K V) (X ^ m - C (1 : K)) = 0)
    {W : Submodule K V} (hWt : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hC : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B →
      Commute (g : Module.End K V) (x : Module.End K V) → ∀ w ∈ W, (g : Module.End K V) w ∈ W)
    (hW0 : W ≠ ⊥) (hdim : finrank K W ≤ 2) (hWx : ∀ w ∈ W, (x : Module.End K V) w ∈ W)
    (hWdet : LinearMap.det ((x : Module.End K V).restrict hWx) = 1) : False := by
  have : CharP K 2 := hK.charP
  have hdecomp := eq_iSup_primaryComponent_of_forall_commute hK H hdet hWt hC
  have hcomp : ∀ a ∈ primaryFactors (x : Module.End K V),
      primaryComponent (x : Module.End K V) a ≤ W →
      ∃ ν : K, a = X - C ν ∧ ν ≠ 1 ∧ dualPoly hK.bar a = X - C ν⁻¹ := by
    intro a ha hle
    obtain ⟨ν, rfl, -, hd⟩ := exists_dualPoly_eq_of_dvd_sub_one hK hm hmq hx ha
    refine ⟨ν, rfl, fun hν1 => ?_, hd⟩
    subst hν1
    have hbot := inf_primaryComponent_eq_bot_of_selfDual hK H hWt hC hWx ha
      (by rw [hd, inv_one])
    rw [inf_eq_right.mpr hle] at hbot
    exact primaryComponent_ne_bot H.squarefree ha hbot
  obtain ⟨a, ha, hle⟩ : ∃ a ∈ primaryFactors (x : Module.End K V),
      primaryComponent (x : Module.End K V) a ≤ W := by
    by_contra! hno
    refine hW0 (hdecomp.trans (eq_bot_iff.mpr (iSup₂_le fun b hb => iSup_le fun hbW => ?_)))
    exact absurd hbW (hno b hb)
  obtain ⟨ν, rfl, hν1, hdν⟩ := hcomp _ ha hle
  have hWpos : 1 ≤ finrank K W := by
    by_contra h0
    exact hW0 (Submodule.finrank_eq_zero.mp (by omega))
  by_cases hWa : primaryComponent (x : Module.End K V) (X - C ν) = W
  ·
    have h1 : (x : Module.End K V).restrict hWx = ν • LinearMap.id := by
      ext w
      have hw : (w : V) ∈ primaryComponent (x : Module.End K V) (X - C ν) := by
        rw [hWa]
        exact w.2
      exact mem_primaryComponent_X_sub_C_iff.mp hw
    rw [h1, LinearMap.det_smul, LinearMap.det_id, mul_one] at hWdet
    exact hν1 (eq_one_of_pow_eq_one_of_le_two hWpos hdim hWdet)
  ·
    obtain ⟨b, hb, hbW, hba⟩ : ∃ b ∈ primaryFactors (x : Module.End K V),
        primaryComponent (x : Module.End K V) b ≤ W ∧ b ≠ X - C ν := by
      by_contra! hno
      refine hWa (le_antisymm hle ?_)
      refine hdecomp.le.trans (iSup₂_le fun c hc => iSup_le fun hcW => ?_)
      rw [hno c hc hcW]
    obtain ⟨ν', rfl, hν'1, -⟩ := hcomp _ hb hbW
    have hνν' : ν ≠ ν' := fun h => hba (by rw [h])
    set P := primaryComponent (x : Module.End K V) (X - C ν)
    set Q := primaryComponent (x : Module.End K V) (X - C ν')
    have hPQ : P ⊓ Q = ⊥ := by
      refine eq_bot_iff.mpr fun v hv => ?_
      obtain ⟨hvP, hvQ⟩ := Submodule.mem_inf.mp hv
      have h1 := (mem_primaryComponent_X_sub_C_iff.mp hvP).symm.trans
        (mem_primaryComponent_X_sub_C_iff.mp hvQ)
      rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
      exact (Submodule.mem_bot K).mpr (h1.resolve_left (sub_ne_zero.mpr hνν'))
    have hPpos : 1 ≤ finrank K P := by
      by_contra h0
      exact primaryComponent_ne_bot H.squarefree ha
        (Submodule.finrank_eq_zero.mp (show finrank K P = 0 by omega))
    have hQpos : 1 ≤ finrank K Q := by
      by_contra h0
      exact primaryComponent_ne_bot H.squarefree hb
        (Submodule.finrank_eq_zero.mp (show finrank K Q = 0 by omega))
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hPQ, finrank_bot, add_zero] at hsum
    have hsupW : P ⊔ Q ≤ W := sup_le hle hbW
    have hle2 := Submodule.finrank_mono hsupW
    have hP1 : finrank K P = 1 := by omega
    have hQ1 : finrank K Q = 1 := by omega
    have hsup : P ⊔ Q = W := Submodule.eq_of_le_of_finrank_eq hsupW (by omega)
    have hdetW := det_restrict_eq_of_sup hle hbW hPQ hsup
      (fun v hv => mem_primaryComponent_X_sub_C_iff.mp hv)
      (fun v hv => mem_primaryComponent_X_sub_C_iff.mp hv) hWx
    rw [hWdet, hP1, hQ1, pow_one, pow_one] at hdetW
    have hν' : ν' = ν⁻¹ := eq_inv_of_mul_eq_one_right hdetW.symm
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot H.squarefree ha)
    refine hv0 (eq_zero_of_perfect_left H ha hb (by rw [hdν, hν']) hv fun w hw => ?_)
    exact hWt v (hle hv) w (hbW hw)

end CFSG.AGLEmbedding.ToralCensus
