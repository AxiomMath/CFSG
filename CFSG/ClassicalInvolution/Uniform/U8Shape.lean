module

public import CFSG.ClassicalInvolution.Uniform.U8Twin
public import CFSG.ClassicalInvolution.Uniform.U3Thm7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.ModelFacts (Gen3 gen3_of_equiv_sl2)
open scoped MatrixGroups commutatorElement


open CFSG.LocalAnalysis.ComponentInitial in
theorem sl2_exists_not_comm (F : Type) [Field F] : ¬ ∀ a b : SL(2, F), a * b = b * a := by
  intro h
  have h00 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h (sl2Upper F 1) (sl2Lower F 1))
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

section Layer

@[expose] def HasLayer3 (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ R₀ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D,
    ∃ L : Subgroup (modelUniv t n 3 1 Fact.out).K, CFSG.Open.IsQuasisimple ↥L ∧
      L ≤ Subgroup.centralizer (R₀ : Set (modelUniv t n 3 1 Fact.out).K) ∧
      (∀ x ∈ Subgroup.centralizer (R₀ : Set (modelUniv t n 3 1 Fact.out).K), x ^ 3 = 1 → x ∈ L) ∧
      L ∉ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D

@[expose] def ExcLayer3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) →
    StatedLieAdmissible t n 3 1 → HasLayer3 t n

theorem noTwinClass3_of_layer3 {t : StatedLieTag} {n a : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hlayer : HasLayer3 t n) (ha : 2 ≤ a) : ¬ ModelTwinClass 3 t n 1 a := by
  intro h
  obtain ⟨R₀, R₁, hR₀, hR₁, hne, hc, htw⟩ :=
    ((modelTwinClass_iff t n 1 a).mp h).exists_two ha
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hgen3 : ∀ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D, Gen3 R := by
    intro R hR
    obtain ⟨φ⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm hG2 hD4 hR
    exact gen3_of_equiv_sl2 φ
  have hnab : ∀ R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D,
      ¬ ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    intro R hR hab
    obtain ⟨φ⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups
      hp2 hfund hadm hG2 hD4 hR
    apply sl2_exists_not_comm (GaloisField 3 1)
    intro A B
    apply φ.symm.injective
    rw [map_mul, map_mul]
    exact Subtype.ext (hab _ (φ.symm A).2 _ (φ.symm B).2)
  obtain ⟨L, hLqs, hLC, hL3, hLfund⟩ := hlayer R₀ hR₀
  have hR₁C : R₁ ≤ Subgroup.centralizer (R₀ : Set (modelUniv t n 3 1 Fact.out).K) :=
    fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx y hy
  have hR₁L : R₁ ≤ L := by
    obtain ⟨S, hSR, hS3, hRS⟩ := hgen3 R₁ hR₁
    exact hRS.trans ((Subgroup.closure_le _).2 fun s hs => hL3 s (hR₁C (hSR hs)) (hS3 s hs))
  obtain ⟨g, hgL, hg1, hg2⟩ := exists_conj_not_commutes_of_le hLqs hR₁L (hnab R₁ hR₁)
    (fun hLR => hLfund (le_antisymm hLR hR₁L ▸ hR₁))
  have hS : conjSub g R₁ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D :=
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hR₁ g
  have hSL : conjSub g R₁ ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact L.mul_mem (L.mul_mem hgL (hR₁L hy)) (L.inv_mem hgL)
  have hSR₀ : conjSub g R₁ ≠ R₀ := by
    intro heq
    apply hnab R₀ hR₀
    intro x hx y hy
    have hxS : x ∈ conjSub g R₁ := heq ▸ hx
    exact (Subgroup.mem_centralizer_iff.mp (hLC (hSL hxS)) y hy).symm
  have hcS : Commutes (conjSub g R₁) R₀ := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hLC (hSL hx)) y hy).symm
  exact hg2 ((htw _ hS hSR₀ hg1).mp hcS)

end Layer

section Shape

theorem ih8TwinShapeU_of_layer (h : ExcLayer3) : Ih8TwinShapeU := by
  intro G _ _ _ Ω hΩ hA htrans t k e M hG2 hD4 hK
  obtain ⟨K, hK, K', hK', hne'⟩ := hK
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  obtain ⟨R, hR, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨R', hR', rfl⟩ := (M.mem_iff K').mp hK'Ω
  have hRR' : R ≠ R' := fun h => hne' (by rw [h])
  have hmtc := modelTwinClass_two3 M hΩ ⟨_, hK⟩ hG2 hD4 hR hR' hRR' hzK hzK'
  have he := ih8Model_exp_eq_one M hD4
  subst he
  have hadm := M.admissible
  have hfund := M.isFundTag
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  cases t
  ·
    have hk3 : 3 ≤ k := by
      have h1 := hadm.2.2.1
      have h2 : k ≠ 2 := fun hk => hadm.2.2.2.2 (by simp [hk])
      omega
    obtain ⟨hk4, -⟩ := modelTwinClass_psl hp2 hk3 le_rfl hmtc
    exact ⟨6, true, by norm_num, Or.inr (Or.inl ⟨rfl, rfl, rfl, hk4⟩)⟩
  ·
    obtain ⟨hk4, -⟩ := modelTwinClass_psu hp2 hadm le_rfl hmtc
    exact ⟨6, false, by norm_num, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hk4⟩))⟩
  ·
    obtain ⟨hk2, -⟩ := modelTwinClass_psp hp2 hadm le_rfl hmtc
    exact ⟨5, true, by norm_num, Or.inl ⟨rfl, rfl, hk2⟩⟩
  ·
    have hk3 : 3 ≤ k := hadm.2.2.1
    exact ⟨2 * k + 1, true, by omega, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by omega, by omega, rfl, rfl⟩)))⟩
  ·
    have hk4 : 4 ≤ k := hadm.2.2
    exact ⟨2 * k, true, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by omega, by omega, rfl, rfl, rfl⟩))))⟩
  ·
    have hk4 : 4 ≤ k := hadm.2.2
    exact ⟨2 * k, false, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨by omega, by omega, rfl, rfl, rfl⟩))))⟩
  · exact absurd rfl hG2
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (h _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (h _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (h _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (h _ k (by simp) hadm) le_rfl)
  · exact absurd hmtc (noTwinClass3_of_layer3 hfund hadm hG2 hD4 (h _ k (by simp) hadm) le_rfl)
  · exact absurd rfl hD4
  all_goals exact absurd hfund (by simp [IsFundTag])

end Shape

end CFSG.ClassicalInvolution.Uniform
