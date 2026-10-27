module

public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralBridge
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryThree
public import CFSG.ClassicalInvolution.RouteD.LocalTwin

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped commutatorElement

@[expose] def ModelTwinClass (p : ℕ) [Fact p.Prime] (t : StatedLieTag) (n e a : ℕ) : Prop :=
  ∃ F : Fin a → Subgroup (modelUniv t n p e Fact.out).K,
    (∀ i, F i ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) ∧ Function.Injective F ∧
    (∀ i j, i ≠ j → Commutes (F i) (F j)) ∧
    ∀ i j, ∀ S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      (S = F i ∨ Commutes S (F i)) ↔ (S = F j ∨ Commutes S (F j))

section Model

variable {p : ℕ} [Fact p.Prime] {t : StatedLieTag} {n e : ℕ}

theorem fundamentalSubgroups_ne_bot (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) : R ≠ ⊥ := by
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    cases t <;> trivial
  obtain ⟨g, γ, hγ, rfl⟩ := CFSG.ClassicalInvolution.ModelFacts.mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨_, _, _, hext⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum t n p e Fact.out hfund' hadm
  have hne : (modelUniv t n p e Fact.out).D.rootGroup γ ≠ ⊥ := hext.ne_bot γ hγ
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  intro hbot
  have hmem : g * (x : (modelUniv t n p e Fact.out).K) * g⁻¹ ∈
      ((modelUniv t n p e Fact.out).D.rootGroup γ ⊔
        (modelUniv t n p e Fact.out).D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom :=
    ⟨x, Subgroup.mem_sup_left x.2, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  apply hx1
  apply Subtype.ext
  have := mul_inv_eq_one.mp hmem
  simpa using this

theorem normal_le_center_or_sup_eq_top {K : Type*} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    (N : Subgroup K) [N.Normal] : N ≤ Subgroup.center K ∨ N ⊔ Subgroup.center K = ⊤ := by
  obtain ⟨-, hsimple⟩ := hK
  have hnorm : (N.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center K)))
    with h | h
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center K) x ∈ N.map (QuotientGroup.mk' (Subgroup.center K)) :=
      ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · right
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) N
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm

theorem exists_fund_not_commuting (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hnA1 : ¬ (t = .PSL ∧ n = 2)) {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    ∃ S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, S ≠ R ∧ ¬ Commutes S R := by
  classical
  by_contra hcon
  push Not at hcon
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    cases t <;> trivial
  have hqs : CFSG.Open.IsQuasisimple (modelUniv t n p e Fact.out).K :=
    CFSG.ClassicalInvolution.ModelFacts.isQuasisimple_modelUniv t n p e Fact.out hfund' hadm
  have hRne : R ≠ ⊥ := fundamentalSubgroups_ne_bot hfund hadm hR
  have hRtop : R ≠ ⊤ :=
    (CFSG.ClassicalInvolution.ModelFacts.fundamentalIsWhole_modelUniv t n p e Fact.out hfund'
      hadm).2 hnA1 R hR
  have hRZ : ∀ r ∈ R, r ∈ Subgroup.center (modelUniv t n p e Fact.out).K → r = 1 :=
    fun r hr hrc =>
      CFSG.ClassicalInvolution.RouteD.Gaps.fundNoncentral p t n e hfund hadm hnA1 R hR r hr
        (fun y => by
          have h1 := Subgroup.mem_center_iff.mp hrc y
          rw [← h1]
          simp)
  have hRle : ¬ R ≤ Subgroup.center (modelUniv t n p e Fact.out).K := fun hle =>
    hRne (eq_bot_iff.mpr fun r hr => (hRZ r hr (hle hr)) ▸ Subgroup.one_mem _)
  have hperf : (⊤ : Subgroup (modelUniv t n p e Fact.out).K) ≤
      ⁅(⊤ : Subgroup (modelUniv t n p e Fact.out).K),
        (⊤ : Subgroup (modelUniv t n p e Fact.out).K)⁆ := by
    have := hqs.1
    rw [commutator_def] at this
    exact this.ge
  have hnorm : Subgroup.normalClosure (R : Set (modelUniv t n p e Fact.out).K) ≤
      Subgroup.normalizer (R : Set (modelUniv t n p e Fact.out).K) := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    obtain ⟨b, hb, hbc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hbc
    have hS : R.map (MulAut.conj c).toMonoidHom ∈
        fundamentalSubgroups t (modelUniv t n p e Fact.out).D :=
      CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hR c
    have hyS : y ∈ R.map (MulAut.conj c).toMonoidHom := ⟨b, hb, by simpa using hc⟩
    by_cases hSR : R.map (MulAut.conj c).toMonoidHom = R
    · rw [hSR] at hyS
      exact Subgroup.le_normalizer hyS
    · have hc : ∀ r ∈ R, y * r = r * y := (hcon _ hS hSR) y hyS
      have hc' : ∀ r ∈ R, y⁻¹ * r = r * y⁻¹ :=
        (hcon _ hS hSR) y⁻¹ (Subgroup.inv_mem _ hyS)
      rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        have : y * r * y⁻¹ = r := by rw [mul_inv_eq_iff_eq_mul]; exact hc r hr
        rw [this]
        exact hr
      · intro hr
        have h1 : y⁻¹ * (y * r * y⁻¹) * y = r := by group
        have h2 : y⁻¹ * (y * r * y⁻¹) * y = y * r * y⁻¹ := by
          rw [mul_assoc, ← mul_assoc y⁻¹, hc' _ hr]
          group
        rw [← h1, h2]
        exact hr
  have : (Subgroup.normalClosure (R : Set (modelUniv t n p e Fact.out).K)).Normal :=
    Subgroup.normalClosure_normal
  rcases normal_le_center_or_sup_eq_top hqs
      (Subgroup.normalClosure (R : Set (modelUniv t n p e Fact.out).K)) with h | h
  · exact hRle ((Subgroup.subset_normalClosure).trans h)
  · have htop : (⊤ : Subgroup (modelUniv t n p e Fact.out).K) ≤
        Subgroup.normalClosure (R : Set (modelUniv t n p e Fact.out).K) :=
      CFSG.ClassicalInvolution.RouteD.le_of_perfect_of_le_sup_center
        (Z := Subgroup.center (modelUniv t n p e Fact.out).K) le_rfl hperf h.ge
    have : R.Normal := Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp (htop.trans hnorm))
    rcases normal_le_center_or_sup_eq_top hqs R with h' | h'
    · exact hRle h'
    · exact hRtop (top_le_iff.mp
        (CFSG.ClassicalInvolution.RouteD.le_of_perfect_of_le_sup_center
          (Z := Subgroup.center (modelUniv t n p e Fact.out).K) le_rfl hperf h'.ge))

end Model

end CFSG.ClassicalInvolution.RouteD.Exotic
