module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z2
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.Asc77.AscExactDBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace T7Z


theorem center_eq_map_center {U Q : Type} [Group U] [Group Q] [Group.IsPerfect U]
    (ψ : U →* Q) (hs : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center U) :
    Subgroup.center Q = (Subgroup.center U).map ψ := by
  apply le_antisymm
  · intro x hx
    have hU : (⊤ : Subgroup U) ≤ ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆ := by
      have := Group.IsPerfect.commutator_eq_top (G := U)
      rw [_root_.commutator_def] at this
      exact this.ge
    obtain ⟨ε, hε, hεx⟩ := exists_central_lift ψ hker hU
      (MonoidHom.mem_range.mpr (hs x)) (fun y hy => by
        obtain ⟨y', rfl⟩ := MonoidHom.mem_range.mp hy
        exact (Subgroup.mem_center_iff.mp hx (ψ y')).symm)
    exact ⟨ε, hε, hεx⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := hs q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]

theorem le_center_of_noncentral {Y : Type} [Group Y] [Finite Y] (hperf : Group.IsPerfect Y)
    (N : Subgroup Y) [N.Normal] (hodd : Odd (Nat.card N))
    (hsimple : IsSimpleGroup ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)))
    {t : Y} (ht : ∀ n ∈ N, n * t = t * n)
    (htc : (QuotientGroup.mk t : Y ⧸ N) ∉ Subgroup.center (Y ⧸ N)) :
    N ≤ Subgroup.center Y := by
  classical
  set Q := Y ⧸ N with hQ
  have hQperf : Group.IsPerfect Q := inferInstance
  set C : Subgroup Y := Subgroup.centralizer (N : Set Y) with hC
  set H : Subgroup Y := Subgroup.normalClosure {t} with hH
  have htC : t ∈ C := Subgroup.mem_centralizer_iff.mpr ht
  have hHC : H ≤ C := Subgroup.normalClosure_le_normal (by simpa using htC)
  set π : Y →* Q := QuotientGroup.mk' N with hπ
  set M : Subgroup Q := H.map π with hM
  have : M.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
  have hMZ : ¬ M ≤ Subgroup.center Q := by
    intro h
    exact htc (h ⟨t, Subgroup.subset_normalClosure rfl, rfl⟩)
  have hMtop : M = ⊤ := by
    set Z : Subgroup Q := Subgroup.center Q with hZ
    set S : Subgroup (Q ⧸ Z) := M.map (QuotientGroup.mk' Z) with hS
    have : S.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
    · exfalso
      apply hMZ
      intro m hm
      have : (QuotientGroup.mk' Z m) ∈ S := Subgroup.mem_map_of_mem _ hm
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    · have hcomm : commutator Q ≤ M := by
        rw [commutator, Subgroup.commutator_le]
        intro q₁ _ q₂ _
        have h1 : (QuotientGroup.mk' Z q₁) ∈ S := by rw [h]; trivial
        have h2 : (QuotientGroup.mk' Z q₂) ∈ S := by rw [h]; trivial
        obtain ⟨m₁, hm₁, hm₁q⟩ := Subgroup.mem_map.mp h1
        obtain ⟨m₂, hm₂, hm₂q⟩ := Subgroup.mem_map.mp h2
        have hz₁ : m₁⁻¹ * q₁ ∈ Z := QuotientGroup.eq.mp hm₁q
        have hz₂ : m₂⁻¹ * q₂ ∈ Z := QuotientGroup.eq.mp hm₂q
        have e₁ : q₁ = m₁ * (m₁⁻¹ * q₁) := by group
        have e₂ : q₂ = m₂ * (m₂⁻¹ * q₂) := by group
        set a := m₁⁻¹ * q₁
        set b := m₂⁻¹ * q₂
        have hca : ∀ x : Q, x * a = a * x := fun x => (Subgroup.mem_center_iff.mp hz₁ x)
        have hcb : ∀ x : Q, x * b = b * x := fun x => (Subgroup.mem_center_iff.mp hz₂ x)
        have : ⁅q₁, q₂⁆ = ⁅m₁, m₂⁆ := by
          rw [e₁, e₂]
          simp only [commutatorElement_def]
          calc m₁ * a * (m₂ * b) * (m₁ * a)⁻¹ * (m₂ * b)⁻¹
              = m₁ * (a * (m₂ * b)) * a⁻¹ * m₁⁻¹ * b⁻¹ * m₂⁻¹ := by group
            _ = m₁ * ((m₂ * b) * a) * a⁻¹ * m₁⁻¹ * b⁻¹ * m₂⁻¹ := by rw [← hca (m₂ * b)]
            _ = m₁ * m₂ * (b * (a * a⁻¹) ) * m₁⁻¹ * b⁻¹ * m₂⁻¹ := by group
            _ = m₁ * m₂ * b * m₁⁻¹ * b⁻¹ * m₂⁻¹ := by group
            _ = m₁ * m₂ * (b * m₁⁻¹) * b⁻¹ * m₂⁻¹ := by group
            _ = m₁ * m₂ * (m₁⁻¹ * b) * b⁻¹ * m₂⁻¹ := by rw [hcb m₁⁻¹]
            _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by group
        rw [this]
        exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
      rw [Group.IsPerfect.commutator_eq_top] at hcomm
      exact top_le_iff.mp hcomm
  have hcov : (⊤ : Subgroup Y) ≤ ((⊤ : Subgroup Y) ⊓ C) ⊔ N := by
    intro y _
    have hy : π y ∈ M := by rw [hMtop]; trivial
    obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hy
    have hn : h⁻¹ * y ∈ N := QuotientGroup.eq.mp hπh
    have : y = h * (h⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨trivial, hHC hh⟩) (Subgroup.mem_sup_right hn)
  have hperf' : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ := by
    have := Group.IsPerfect.commutator_eq_top (G := Y)
    rwa [_root_.commutator_def] at this
  have hMN : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (N : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  have := ExactD.le_centralizer_of_perfect_of_cover hperf'
    le_top hMN hodd hcov
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Subgroup.mem_centralizer_iff.mp (this (Subgroup.mem_top y)) n hn).symm


@[expose] def OddCenterClassical : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    ∀ (t : StatedLieTag) (n p f : ℕ), p.Prime → p ≠ 2 → 5 ≤ p ^ f →
      ((t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4) ∨ (t = .PSp ∧ n = 2)) →
      StatedClassicalModel (L ⧸ Subgroup.center L) t n p f →
      ∀ N : Subgroup L, N ≤ Subgroup.center L → Odd (Nat.card N) → N = ⊥

variable {p f : ℕ} [Fact p.Prime]


theorem oddCore_eq_bot_of_lie (hodd : OddCenterClassical) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {Y : Type} [Group Y] [Finite Y] (hperf : Group.IsPerfect Y)
    {Φ : Set (Subgroup (Y ⧸ classicalInvolutionOddCore Y))}
    (D : LieSystemData p f (Y ⧸ classicalInvolutionOddCore Y) Φ) (hcard : D.card = 1)
    (i : Fin D.card)
    (ht : (D.tag i = .PSL ∧ D.rank i = 4) ∨ (D.tag i = .PSU ∧ D.rank i = 4) ∨
      (D.tag i = .PSp ∧ D.rank i = 2))
    {t : Y} (htN : ∀ n ∈ classicalInvolutionOddCore Y, n * t = t * n)
    (htc : (QuotientGroup.mk t : Y ⧸ classicalInvolutionOddCore Y) ∉
      Subgroup.center (Y ⧸ classicalInvolutionOddCore Y)) :
    classicalInvolutionOddCore Y = ⊥ := by
  classical
  set N := classicalInvolutionOddCore Y with hN
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card Y
  have hexp : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exfalso
      rcases ht with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
  have hfund := D.isFundTag i
  have hadm := D.admissible i
  have hcz := ModelFacts.modelClauseZero (D.tag i) (D.rank i) p (D.exp i) Fact.out hfund hadm
  set K := (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K with hK
  have hKq : CFSG.Open.IsQuasisimple K := hcz.1
  have hKperf : Group.IsPerfect K := ⟨hKq.1⟩
  have hKsimp : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq.2
  have hmodelK : StatedClassicalModel (K ⧸ Subgroup.center K) (D.tag i) (D.rank i) p (D.exp i) := by
    rcases hcz.2 with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals
      exfalso
      rcases ht with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨-, h'⟩ <;> rw [h'] at h0 <;> cases h0
  have hj : ∀ j : Fin D.card, j = i := fun j => Fin.ext (by
    have := j.2
    have := i.2
    omega)
  have hψsurj : Function.Surjective (D.hom i) := by
    have h1 : (⨆ j, (D.hom j).range) = (D.hom i).range := by
      apply le_antisymm
      · exact iSup_le fun j => by rw [hj j]
      · exact le_iSup (fun j => (D.hom j).range) i
    have h2 := D.generate
    rw [h1] at h2
    exact MonoidHom.range_eq_top.mp h2
  have hker : (D.hom i).ker ≤ Subgroup.center K := D.ker_le_center i
  have hZψ := center_eq_map_center (D.hom i) hψsurj hker
  let e₁ := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective (D.hom i) hψsurj hker hZψ
  have hsimple : IsSimpleGroup ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)) := e₁.symm.isSimpleGroup
  have hcen : N ≤ Subgroup.center Y := le_center_of_noncentral hperf N hNodd hsimple htN htc
  let π : Y →* (Y ⧸ N) := QuotientGroup.mk' N
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπker : π.ker ≤ Subgroup.center Y := by
    rw [QuotientGroup.ker_mk']
    exact hcen
  have hZπ := center_eq_map_center π hπsurj hπker
  let e₂ := CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective π hπsurj hπker hZπ
  let e := e₂.trans e₁.symm
  have hYq : CFSG.Open.IsQuasisimple Y := ⟨hperf.commutator_eq_top, e.isSimpleGroup⟩
  have hmodelY : StatedClassicalModel (Y ⧸ Subgroup.center Y) (D.tag i) (D.rank i) p (D.exp i) :=
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm hmodelK
  have hq' : 5 ≤ p ^ D.exp i := by rw [hexp]; exact hq
  exact hodd Y hYq (D.tag i) (D.rank i) p (D.exp i) Fact.out hp2 hq' ht hmodelY N hcen hNodd

end T7Z

end CFSG.ClassicalInvolution.Asc77
