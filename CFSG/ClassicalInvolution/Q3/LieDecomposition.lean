module

public import CFSG.ClassicalInvolution.Q3.Tight
public import CFSG.ClassicalInvolution.Balance.LayerGenerationField

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

@[expose] def IsOddLieComponent3 {X : Type} [Group X] (L : Subgroup X) : Prop :=
  ∃ (t : StatedLieTag) (n : ℕ), (t = .PSL → 3 ≤ n) ∧
    (t ∈ CFSG.Blueprint.classicalTags ∨ t ∈ CFSG.Blueprint.chevalleyExceptionalTags) ∧
    CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) t n 3 1

structure LieDecomposition3 {X : Type} [Group X] (Ψ : Set (Subgroup X)) (Y : Subgroup X) where
  ι : Type
  Q : ι → Subgroup X
  commute : ∀ i j, i ≠ j → Commutes (Q i) (Q j)
  iSup_eq : ⨆ i, Q i = Y
  exists_le : ∀ L ∈ Ψ, ∃ i, L ≤ Q i
  kind : ∀ i, ((∃ L ∈ Ψ, L = Q i) ∧ (∀ L ∈ Ψ, L ≤ Q i → L = Q i) ∧ Group.IsSolvable (Q i)) ∨
    (CFSG.Open.IsQuasisimple (Q i) ∧ IsOddLieComponent3 (Q i)) ∨
    (CFSG.Open.IsQuasisimple (Q i) ∧ Nonempty (↥(Q i) ≃* ↥CFSG.Blueprint.NativeSporadic.M11))

theorem LieDecomposition3.congr {X : Type} [Group X] {Ψ Ψ' : Set (Subgroup X)}
    {Y Y' : Subgroup X} (hΨ : Ψ = Ψ') (hY : Y = Y') :
    Nonempty (LieDecomposition3 Ψ Y) → Nonempty (LieDecomposition3 Ψ' Y') := by
  subst hΨ
  subst hY
  exact id

section Abstract

variable {X Yb : Type} [Group X] [Group Yb] {Φ : Set (Subgroup Yb)} {ι : Type}

theorem range_model3 (h0 : ModelClauseZero) {c : CompData} {t : StatedLieTag} {n : ℕ}
    (ht : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hc : c = CompData.model t n)
    (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G) (hψ1 : ∃ x, ψ x ≠ 1) :
    CFSG.Open.IsQuasisimple ↥ψ.range ∧ IsOddLieComponent3 ψ.range := by
  subst hc
  obtain ⟨hK, hmodel⟩ := h0 t n 3 1 Nat.prime_three ht hadm
  have hq := Quasisimple.central_quotient hK ψ.ker hker
  refine ⟨Components.quasisimple_of_equiv (QuotientGroup.quotientKerEquivRange ψ).symm hq, ?_⟩
  have hn : t = .PSL → 3 ≤ n := by
    intro h
    subst h
    have h2 : 2 ≤ n := hadm.2.2.1
    have h3 : (n, 3 ^ 1) ≠ (2, 3) := hadm.2.2.2.2
    have : n ≠ 2 := fun h => h3 (by simp [h])
    omega
  have hψ1' : ∃ x, ψ.rangeRestrict x ≠ 1 := by
    obtain ⟨x, hx⟩ := hψ1
    exact ⟨x, fun h => hx (congrArg Subtype.val h)⟩
  exact ⟨t, n, hn, isFundTag_mem_tags ht,
    lieModel_of_surjective hK ψ.rangeRestrict ψ.rangeRestrict_surjective hψ1' hmodel⟩

theorem range_m11 (hM : M11Facts) {c : CompData} (hc : c = CompData.m11) (ψ : c.G →* X)
    (hψ1 : ∃ x, ψ x ≠ 1) :
    CFSG.Open.IsQuasisimple ↥ψ.range ∧
      Nonempty (↥ψ.range ≃* ↥CFSG.Blueprint.NativeSporadic.M11) := by
  subst hc
  obtain ⟨hsimple, hcard⟩ := hM
  have hker : ψ.ker = ⊥ := by
    rcases (MonoidHom.normal_ker ψ).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx⟩ := hψ1
      exact hx (by
        have : x ∈ ψ.ker := by rw [h]; trivial
        exact this)
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  let e : ↥CFSG.Blueprint.NativeSporadic.M11 ≃* ↥ψ.range := MonoidHom.ofInjective hinj
  have hnab : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M11, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcomm : Std.Commutative (α := ↥CFSG.Blueprint.NativeSporadic.M11) (· * ·) :=
      ⟨fun a b => hcon a b⟩
    have : IsMulCommutative ↥CFSG.Blueprint.NativeSporadic.M11 := ⟨hcomm⟩
    have hp := IsSimpleGroup.prime_card (α := ↥CFSG.Blueprint.NativeSporadic.M11)
    rw [hcard] at hp
    norm_num at hp
  have hq : CFSG.Open.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M11 := by
    have := hsimple
    obtain ⟨a, b, hab⟩ := hnab
    have hcenter : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11 = ⊥ := by
      rcases (inferInstance : (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M11).Normal
        ).eq_bot_or_eq_top with h | h
      · exact h
      · exact (hab (Subgroup.mem_center_iff.mp (by rw [h]; trivial : a ∈ _) b).symm).elim
    have hcomm : commutator ↥CFSG.Blueprint.NativeSporadic.M11 = ⊤ := by
      rcases (inferInstance : (commutator ↥CFSG.Blueprint.NativeSporadic.M11).Normal
        ).eq_bot_or_eq_top with h | h
      · exfalso
        have h1 : ⁅a, b⁆ ∈ commutator ↥CFSG.Blueprint.NativeSporadic.M11 :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact hab h1
      · exact h
    exact ⟨hcomm, ((QuotientGroup.quotientMulEquivOfEq hcenter).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  exact ⟨Components.quasisimple_of_equiv e.symm hq, ⟨e.symm⟩⟩

theorem fund_eq_top_of_sl23 {c : CompData} (hc : c = CompData.sl23) :
    ∀ R ∈ c.fund, R = (⊤ : Subgroup c.G) := by
  subst hc
  intro R hR
  exact hR

theorem isSolvable_range_of_sl23 {c : CompData} (hc : c = CompData.sl23) (ψ : c.G →* X) :
    Group.IsSolvable ↥ψ.range := by
  subst hc
  have := isSolvable_sl2Three
  exact Group.isSolvable_of_surjective ψ.rangeRestrict_surjective

theorem lieDecomposition3_of_lieSystemData3 (h0 : ModelClauseZero) (hM : M11Facts)
    (D : LieSystemData3 ι Yb Φ) (θ : Yb →* X) (hθ : Function.Injective θ)
    (hnc : ∀ L ∈ Φ, ¬ L ≤ Subgroup.center Yb) :
    Nonempty (LieDecomposition3 (Subgroup.map θ '' Φ) θ.range) := by
  let Q : ι → Subgroup X := fun i => (θ.comp (D.hom i)).range
  have hQmap : ∀ i, Q i = (D.hom i).range.map θ := fun i => MonoidHom.range_comp θ (D.hom i)
  have hker : ∀ i, (θ.comp (D.hom i)).ker ≤ Subgroup.center _ := fun i x hx => by
    apply D.ker_le_center i
    rw [MonoidHom.mem_ker] at hx ⊢
    exact hθ (by simpa using hx)
  have hmem : ∀ L ∈ Φ, ∃ j R, R ∈ (D.kind j).fund ∧ L = R.map (D.hom j) :=
    fun L hL => D.fundamental L hL
  have hnt : ∀ i, ∃ x, (θ.comp (D.hom i)) x ≠ 1 := by
    intro i
    obtain ⟨R, -, hmeet⟩ := D.meets i
    have h24 := D.card_eq _ hmeet
    obtain ⟨m, hm, hm1⟩ : ∃ m ∈ R.map (D.hom i), m ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : R.map (D.hom i) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
      rw [hbot, Subgroup.card_bot] at h24
      omega
    obtain ⟨r, -, rfl⟩ := hm
    exact ⟨r, fun h => hm1 (hθ (by simpa using h))⟩
  refine ⟨{ ι := ι, Q := Q, commute := ?_, iSup_eq := ?_, exists_le := ?_, kind := ?_ }⟩
  · rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, D.commute i j hij a b]
  · show ⨆ i, Q i = θ.range
    simp_rw [hQmap]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
  · rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, -, rfl⟩ := D.fundamental L hL
    exact ⟨i, (hQmap i).symm ▸ Subgroup.map_mono (Subgroup.map_le_range _ _)⟩
  · intro i
    obtain ⟨t, n, ht, hadm, hc⟩ | hc | hc := D.valid i
    · exact Or.inr (Or.inl (range_model3 h0 ht hadm hc (θ.comp (D.hom i)) (hker i) (hnt i)))
    · left
      have hfund : ∀ R ∈ (D.kind i).fund, R = ⊤ := fund_eq_top_of_sl23 hc
      refine ⟨?_, ?_, isSolvable_range_of_sl23 hc (θ.comp (D.hom i))⟩
      · obtain ⟨R, hR, hmeet⟩ := D.meets i
        rw [hfund R hR, Subgroup.map_top] at hmeet
        exact ⟨(D.hom i).range.map θ, ⟨(D.hom i).range, hmeet, rfl⟩, (hQmap i).symm⟩
      · rintro _ ⟨L₁, hL₁, rfl⟩ hle
        rw [hQmap i] at hle ⊢
        have hle' : L₁ ≤ (D.hom i).range := (Subgroup.map_le_map_iff_of_injective hθ).mp hle
        obtain ⟨j, R', hR', hL₁eq⟩ := hmem L₁ hL₁
        by_cases hji : j = i
        · subst hji
          rw [hfund R' hR', Subgroup.map_top] at hL₁eq
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
    · exact Or.inr (Or.inr (range_m11 hM hc (θ.comp (D.hom i)) (hnt i)))

end Abstract

section Components

variable {X : Type} [Group X] {Ψ : Set (Subgroup X)} {Y : Subgroup X}

namespace LieDecomposition3

variable (D : LieDecomposition3 Ψ Y)

theorem le_join (i : D.ι) : D.Q i ≤ Y := (le_iSup D.Q i).trans D.iSup_eq.le

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

theorem isSubnormal_top [Y.Normal] (i : D.ι) : IsSubnormal (D.Q i) ⊤ :=
  IsSubnormal.step (D.le_join i) (D.normal_subgroupOf i)
    (isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf)

theorem isComponentOf [Y.Normal] (i : D.ι) (hq : CFSG.Open.IsQuasisimple (D.Q i)) :
    IsComponentOf (D.Q i) ⊤ :=
  ⟨le_top, D.isSubnormal_top i, hq⟩

theorem eq_or_commutes_of_isComponentOf [Finite X] [Y.Normal] {L : Subgroup X}
    (hL : IsComponentOf L ⊤) : (∃ i, L = D.Q i) ∨ Commutes L Y := by
  by_cases h : ∃ i, L = D.Q i
  · exact Or.inl h
  · right
    push Not at h
    have hle : Y ≤ Subgroup.centralizer (L : Set X) := by
      rw [← D.iSup_eq]
      refine iSup_le fun i => ?_
      have hc : ⁅L, D.Q i⁆ = ⊥ := by
        rcases D.kind i with ⟨-, -, hsolv⟩ | ⟨hq, -⟩ | ⟨hq, -⟩
        · have := hsolv
          exact LocalComponents.commutes_with_solvable_subnormal L (D.Q i) hL
            (D.isSubnormal_top i)
        · exact LocalComponents.commute_of_ne L (D.Q i) hL (D.isComponentOf i hq) (h i)
        · exact LocalComponents.commute_of_ne L (D.Q i) hL (D.isComponentOf i hq) (h i)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rwa [Subgroup.commutator_comm])
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy)) x hx

end LieDecomposition3

end Components

section Local

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem not_le_center_of_mem3 (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ centMembers Ω a) :
    ¬ (K.subgroupOf (centLayer Ω a)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centLayer Ω a))) ≤
      Subgroup.center (↥(centLayer Ω a) ⧸ classicalInvolutionOddCore ↥(centLayer Ω a)) := by
  obtain ⟨z, hz⟩ := hΩ.classical K hK.1
  exact (hz.subgroupOf (le_centLayer hK)).map_oddQuotient.not_le_center

theorem lieDecomposition3_memberImages (h0 : ModelClauseZero) (hM : M11Facts) (hΩ : InClass3 Ω)
    (hIH : LocalLieSystems3 Ω) (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) :
    Nonempty (LieDecomposition3 (memberImages Ω a) (memberJoin Ω a)) := by
  obtain ⟨ι, -, ⟨D⟩⟩ := hIH {a} ha
  have hθ := layerQuotientHom_injective (a := a) hΩ.conjInvariant
  have h := lieDecomposition3_of_lieSystemData3 h0 hM D (layerQuotientHom hΩ.conjInvariant a) hθ
    (by
      rintro _ ⟨_, ⟨K, hK, hKY, rfl⟩, rfl⟩
      exact not_le_center_of_mem3 hΩ hK)
  have hΨ : Subgroup.map (layerQuotientHom hΩ.conjInvariant a) ''
      oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a})) =
      memberImages Ω a := map_layerQuotientHom_family hΩ.conjInvariant
  exact LieDecomposition3.congr hΨ (range_layerQuotientHom hΩ.conjInvariant) h

theorem omegaFreeAt_or_isOddLieComponent3_or_isM11_le_join (h0 : ModelClauseZero)
    (hM : M11Facts) (hΩ : InClass3 Ω) (hIH : LocalLieSystems3 Ω)
    (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) {L : Subgroup (OddQuot a)}
    (hL : CFSG.IsComponent L) :
    OmegaFreeAt Ω a L ∨ ((IsOddLieComponent3 L ∨
      Nonempty (↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M11)) ∧ L ≤ memberJoin Ω a) := by
  obtain ⟨D⟩ := lieDecomposition3_memberImages h0 hM hΩ hIH ha
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · rcases D.kind i with ⟨-, -, hsolv⟩ | ⟨-, hlie⟩ | ⟨-, hm⟩
    · exfalso
      have hq := hL'.2.2
      have hsimple : IsSimpleGroup (↥(D.Q i) ⧸ Subgroup.center ↥(D.Q i)) := hq.2
      have hnt : Nontrivial ↥(D.Q i) := by
        by_contra hcon
        rw [not_nontrivial_iff_subsingleton] at hcon
        have : Subsingleton (↥(D.Q i) ⧸ Subgroup.center ↥(D.Q i)) := inferInstance
        exact (not_nontrivial_iff_subsingleton.mpr this) hsimple.toNontrivial
      have := hsolv
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne hq.1
    · exact Or.inr ⟨Or.inl hlie, D.le_join i⟩
    · exact Or.inr ⟨Or.inr hm, D.le_join i⟩
  · left
    intro K hKΩ hKC x hx y hy
    have hxY : x ∈ memberJoin Ω a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K
        ⟨hKΩ, hKC⟩ hx
    exact (hcomm y hy x hxY).symm

end Local

@[expose] def LieLocallyTwoBalanced3 : Prop :=
  ∀ (Y : Type) [Group Y] (t : StatedLieTag) (n : ℕ), (t = .PSL → 3 ≤ n) →
    (t ∈ CFSG.Blueprint.classicalTags ∨ t ∈ CFSG.Blueprint.chevalleyExceptionalTags) →
    CFSG.Blueprint.LieModel Y t n 3 1 → IsLocallyTwoBalanced Y

@[expose] def M11LocallyTwoBalanced : Prop :=
  ∀ (L : Type) [Group L], Nonempty (L ≃* ↥CFSG.Blueprint.NativeSporadic.M11) →
    IsLocallyTwoBalanced (L ⧸ Subgroup.center L)

section Balance

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem componentBalanceAt_of_localLieSystems3 (h0 : ModelClauseZero) (hM : M11Facts)
    (hKG1 : LieLocallyTwoBalanced3) (hM11 : M11LocallyTwoBalanced) (hΩ : InClass3 Ω)
    (hIH : LocalLieSystems3 Ω) (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G) :
    ComponentBalanceAt Ω a := by
  intro L hL
  rcases omegaFreeAt_or_isOddLieComponent3_or_isM11_le_join h0 hM hΩ hIH ha hL with
    h | ⟨⟨t, n, hn, ht, hmodel⟩ | e, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr (hKG1 _ t n hn ht hmodel))
  · exact Or.inr (Or.inr (hM11 ↥L e))

end Balance

end CFSG.ClassicalInvolution.Q3
