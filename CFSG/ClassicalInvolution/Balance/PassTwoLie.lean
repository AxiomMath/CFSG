module

public import CFSG.ClassicalInvolution.Balance.ToralBalanceModel
public import CFSG.ClassicalInvolution.Generic.Induction

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def FundamentalWholeA1 : Prop :=
  ∀ (t : StatedLieTag) (n p f : ℕ) (hp : p.Prime), IsFundTag t → StatedLieAdmissible t n p f →
    (t = .PSL ∧ n = 2) → ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f hp).D, R = ⊤

structure LieDecomposition {X : Type} [Group X] (Ψ : Set (Subgroup X)) (Y : Subgroup X) where
  ι : Type
  Q : ι → Subgroup X
  quasisimple : ∀ i, CFSG.Open.IsQuasisimple (Q i)
  commute : ∀ i j, i ≠ j → Commutes (Q i) (Q j)
  iSup_eq : ⨆ i, Q i = Y
  exists_le : ∀ L ∈ Ψ, ∃ i, L ≤ Q i
  rankOne_or_lie : ∀ i, ((∃ L ∈ Ψ, L = Q i) ∧ (∀ L ∈ Ψ, L ≤ Q i → L = Q i)) ∨
    IsOddLieComponent (Q i)

section Abstract

variable {p f : ℕ} [Fact p.Prime]

theorem isFundTag_mem_tags {t : StatedLieTag} (h : IsFundTag t) :
    t ∈ classicalTags ∨ t ∈ chevalleyExceptionalTags := by
  cases t <;> simp_all [IsFundTag, classicalTags, chevalleyExceptionalTags]

theorem lieDecomposition_of_lieSystemData (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) {X Yb : Type} [Group X] [Group Yb] {Φ : Set (Subgroup Yb)}
    (D : LieSystemData p f Yb Φ) (θ : Yb →* X) (hθ : Function.Injective θ)
    (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb) :
    Nonempty (LieDecomposition (Subgroup.map θ '' Φ) θ.range) := by
  let Q : Fin D.card → Subgroup X := fun i => (θ.comp (D.hom i)).range
  have hQmap : ∀ i, Q i = (D.hom i).range.map θ := fun i => MonoidHom.range_comp θ (D.hom i)
  have hK : ∀ i, CFSG.Open.IsQuasisimple (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K :=
    fun i => (h0 _ _ _ _ _ (D.isFundTag i) (D.admissible i)).1
  have hker : ∀ i, (θ.comp (D.hom i)).ker ≤ Subgroup.center _ := fun i x hx => by
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hθ (by simpa using hx)
  have hmem : ∀ L ∈ Φ, ∃ j R, R ∈ fundamentalSubgroups (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D ∧ L = R.map (D.hom j) :=
    fun L hL => D.fundamental L hL
  refine ⟨{ ι := Fin D.card
            Q := Q
            quasisimple := ?_
            commute := ?_
            iSup_eq := ?_
            exists_le := ?_
            rankOne_or_lie := ?_ }⟩
  · intro i
    have hq := Quasisimple.central_quotient (hK i) (θ.comp (D.hom i)).ker (hker i)
    exact Components.quasisimple_of_equiv
      (QuotientGroup.quotientKerEquivRange (θ.comp (D.hom i))).symm hq
  · rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, D.commute i j hij a b]
  · show ⨆ i, Q i = θ.range
    simp_rw [hQmap]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
  · rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, -, rfl⟩ := hmem L hL
    exact ⟨i, (hQmap i).symm ▸ Subgroup.map_mono (Subgroup.map_le_range _ _)⟩
  · intro i
    by_cases hr : D.tag i = .PSL ∧ D.rank i = 2
    · left
      have hA := hA1 (D.tag i) (D.rank i) p (D.exp i) Fact.out (D.isFundTag i) (D.admissible i) hr
      refine ⟨⟨(D.hom i).range.map θ, ⟨(D.hom i).range, ?_, rfl⟩, (hQmap i).symm⟩, ?_⟩
      · obtain ⟨R, hR, hmem'⟩ := D.meets i
        rwa [hA R hR, Subgroup.map_top] at hmem'
      · rintro _ ⟨L₁, hL₁, rfl⟩ hle
        rw [hQmap i] at hle ⊢
        have hle' : L₁ ≤ (D.hom i).range := (Subgroup.map_le_map_iff_of_injective hθ).mp hle
        obtain ⟨j, R', hR', hL₁eq⟩ := hmem L₁ hL₁
        by_cases hji : j = i
        · subst hji
          have hA' := hA1 (D.tag j) (D.rank j) p (D.exp j) Fact.out (D.isFundTag j)
            (D.admissible j) hr
          rw [hA' R' hR', Subgroup.map_top] at hL₁eq
          rw [hL₁eq]
        · refine absurd ?_ (hnc L₁ hL₁)
          have hL₁j : L₁ ≤ (D.hom j).range := hL₁eq ▸ Subgroup.map_le_range _ _
          intro x hx
          have hxi := hle' hx
          have hxj := hL₁j hx
          rw [Subgroup.mem_center_iff]
          intro g
          have hg : g ∈ (⨆ k, (D.hom k).range : Subgroup Yb) := by rw [D.generate]; trivial
          have hcen : ∀ k, (D.hom k).range ≤ Subgroup.centralizer ({x} : Set Yb) := by
            rintro k _ ⟨y, rfl⟩
            rw [Subgroup.mem_centralizer_singleton_iff]
            by_cases hki : k = i
            · subst hki
              obtain ⟨z, rfl⟩ := hxj
              exact (D.commute j k hji z y).symm
            · obtain ⟨z, rfl⟩ := hxi
              exact (D.commute i k (Ne.symm hki) z y).symm
          exact Subgroup.mem_centralizer_singleton_iff.mp ((iSup_le hcen) hg)
    · right
      have hadm := D.admissible i
      have hn : D.tag i = .PSL → 3 ≤ D.rank i := by
        intro h
        have h2 : 2 ≤ D.rank i := by
          have := hadm.2.2
          rw [h] at this
          exact this.1
        have h3 : D.rank i ≠ 2 := fun h' => hr ⟨h, h'⟩
        omega
      obtain ⟨-, hmodel⟩ := h0 _ _ _ _ _ (D.isFundTag i) hadm
      have hψ1 : ∃ x, (θ.comp (D.hom i)).rangeRestrict x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hall : ∀ x, x ∈ Subgroup.center
            (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K := fun x => by
          apply hker i
          rw [MonoidHom.mem_ker]
          have := hcon x
          rw [← Subtype.coe_inj] at this
          simpa using this
        have hsimple := (hK i).2
        obtain ⟨a, b, hab⟩ := exists_pair_ne
          ((modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K ⧸ Subgroup.center
            (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        exact hab (QuotientGroup.eq.mpr (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hall a'))
          (hall b')) |> fun h => by simpa using h)
      exact isOddLieComponent_of_surjective (hK i) (θ.comp (D.hom i)).rangeRestrict
        (MonoidHom.rangeRestrict_surjective _) hψ1 hp2 hn (isFundTag_mem_tags (D.isFundTag i))
        hmodel

end Abstract

theorem LieDecomposition.congr {X : Type} [Group X] {Ψ Ψ' : Set (Subgroup X)}
    {Y Y' : Subgroup X} (hΨ : Ψ = Ψ') (hY : Y = Y') :
    Nonempty (LieDecomposition Ψ Y) → Nonempty (LieDecomposition Ψ' Y') := by
  subst hΨ
  subst hY
  exact id

section Components

variable {X : Type} [Group X] [Finite X] {Ψ : Set (Subgroup X)} {Y : Subgroup X}

namespace LieDecomposition

variable (D : LieDecomposition Ψ Y)

omit [Finite X] in
theorem le_join (i : D.ι) : D.Q i ≤ Y := (le_iSup D.Q i).trans D.iSup_eq.le

omit [Finite X] in
theorem normal_subgroupOf (i : D.ι) : ((D.Q i).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (D.le_join i)]
  have key : ∀ g ∈ (⨆ j, D.Q j : Subgroup X), ∀ n ∈ D.Q i, g * n * g⁻¹ ∈ D.Q i := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact (D.Q k).mul_mem ((D.Q k).mul_mem hy hn) ((D.Q k).inv_mem hy)
      · have := D.commute k i hki y hy n hn
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  intro q y hq hy
  exact key y (D.iSup_eq.ge hy) q hq

omit [Finite X] in
theorem isComponentOf [hY : Y.Normal] (i : D.ι) : IsComponentOf (D.Q i) ⊤ := by
  refine ⟨le_top, ?_, D.quasisimple i⟩
  refine IsSubnormal.step (D.le_join i) (D.normal_subgroupOf i) ?_
  exact isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf

theorem eq_or_commutes_of_isComponentOf [Y.Normal] {L : Subgroup X} (hL : IsComponentOf L ⊤) :
    (∃ i, L = D.Q i) ∨ Commutes L Y := by
  by_cases h : ∃ i, L = D.Q i
  · exact Or.inl h
  · right
    push Not at h
    have hle : Y ≤ Subgroup.centralizer (L : Set X) := by
      rw [← D.iSup_eq]
      refine iSup_le fun i => ?_
      have hc := LocalComponents.commute_of_ne L (D.Q i) hL (D.isComponentOf i) (h i)
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rwa [Subgroup.commutator_comm]))
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy)) x hx

end LieDecomposition

end Components

end CFSG.ClassicalInvolution.Balance
