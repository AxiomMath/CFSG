module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2Defs

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

set_option linter.unusedSectionVars false


namespace G2Part1

abbrev InPsi (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  γ = g2a ∨ γ = g2u ∨ γ = g2v ∨ γ = g2b ∨ γ = g2c

theorem height_le_five {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot .G2 γ) : height γ ≤ 5 := by
  rcases g2_root_cases hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> decide

theorem inPsi_of_two_le_height {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ)
    (h2 : 2 ≤ height δ) : InPsi δ := by
  rcases g2_root_cases hδ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd h2 (by decide)
  · exact absurd h2 (by decide)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  all_goals exact absurd h2 (by decide)

theorem not_isRoot_comb_c {β : Fin Tag.G2.rank → ℤ} (hβ : 0 < height β) {a b : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ¬ IsRoot .G2 (a • g2c + b • β) := by
  intro hr
  have h5 := height_le_five hr
  rw [height_nsmul_add_nsmul] at h5
  have hc : height g2c = 5 := by decide
  rw [hc] at h5
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem comb_eq_c {α β γ : Fin Tag.G2.rank → ℤ} (hα : InPsi α) (hβ : InPsi β) (hne : α ≠ β)
    (hγ : IsRoot .G2 γ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : γ = a • α + b • β) :
    γ = g2c := by
  have hp := g2Pair_mem_of_isRoot hγ
  have h0 : γ g2ia = a * α g2ia + b * β g2ia := by rw [h]; simp
  have h1 : γ g2ir = a * α g2ir + b * β g2ir := by rw [h]; simp
  refine eq_of_g2Pair ?_
  have e0 : g2Pair γ = (γ g2ia, γ g2ir) := rfl
  rw [e0] at hp
  rw [e0, g2Pair_g2c]
  have ca0 : g2a g2ia = 1 := rfl
  have ca1 : g2a g2ir = 0 := rfl
  have cu0 : g2u g2ia = 1 := rfl
  have cu1 : g2u g2ir = 1 := rfl
  have cv0 : g2v g2ia = 1 := rfl
  have cv1 : g2v g2ir = 2 := rfl
  have cb0 : g2b g2ia = 1 := rfl
  have cb1 : g2b g2ir = 3 := rfl
  have cc0 : g2c g2ia = 2 := rfl
  have cc1 : g2c g2ir = 3 := rfl
  simp only [g2RootPairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  rcases hα with rfl | rfl | rfl | rfl | rfl <;> rcases hβ with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hne | skip
  all_goals
    simp only [ca0, ca1, cu0, cu1, cv0, cv1, cb0, cb1, cc0, cc1] at h0 h1
    simp only [Prod.mk.injEq]
    omega

theorem isRoot_of_inPsi {γ : Fin Tag.G2.rank → ℤ} (h : InPsi γ) : IsRoot .G2 γ := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  exacts [isRoot_g2a, isRoot_g2u, isRoot_g2v, isRoot_g2b, isRoot_g2c]

theorem height_pos_of_inPsi {γ : Fin Tag.G2.rank → ℤ} (h : InPsi γ) : 0 < height γ := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem one_le_height_of_inPsi {γ : Fin Tag.G2.rank → ℤ} (h : InPsi γ) : 1 ≤ height γ :=
  height_pos_of_inPsi h

theorem g2r_ne_of_inPsi {γ : Fin Tag.G2.rank → ℤ} (h : InPsi γ) : g2r ≠ γ := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem inPsi_reflect {γ : Fin Tag.G2.rank → ℤ} (h : InPsi γ) : InPsi (reflect .G2 g2ir γ) := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · rw [reflect_r_a]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · rw [reflect_r_u]; exact Or.inr (Or.inr (Or.inl rfl))
  · rw [reflect_r_v]; exact Or.inr (Or.inl rfl)
  · rw [reflect_r_b]; exact Or.inl rfl
  · rw [reflect_r_c]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem simple_smul_image :
    (fun α : Fin Tag.G2.rank → ℤ => simple .G2 g2ir • α) '' {γ | InPsi γ} = {γ | InPsi γ} := by
  ext γ
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    show InPsi (simple .G2 g2ir • δ)
    rw [simple_smul]
    exact inPsi_reflect hδ
  · intro hγ
    refine ⟨reflect .G2 g2ir γ, inPsi_reflect hγ, ?_⟩
    show simple .G2 g2ir • reflect .G2 g2ir γ = γ
    rw [simple_smul, reflect_reflect]

open scoped commutatorElement

variable {K : Type} [Field K]

theorem commutator_le_of_comb {α β : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (hβ : IsRoot .G2 β)
    (hαp : 0 < height α) (hβp : 0 < height β) (hne : α ≠ β) {S : Subgroup (ModGL .G2 K)}
    (hS : ∀ γ, IsRoot .G2 γ → ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → γ = a • α + b • β →
      rootSubgroup .G2 K γ ≤ S) :
    ⁅rootSubgroup .G2 K α, rootSubgroup .G2 K β⁆ ≤ S :=
  (commutator_rootSubgroup_le K hα hβ hαp hβp hne).trans
    (iSup₂_le fun γ hγ => by
      obtain ⟨hγr, a, b, ha, hb, hγe⟩ := hγ
      exact hS γ hγr a b ha hb hγe)

theorem pinnedX_mem_rootSubgroup (α : Fin Tag.G2.rank → ℤ) (x : K) :
    pinnedX .G2 K α x ∈ rootSubgroup .G2 K α := Subgroup.subset_closure ⟨x, rfl⟩

theorem commute_pinnedX_of_no_comb {α β : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (hβ : IsRoot .G2 β) (hαp : 0 < height α) (hβp : 0 < height β) (hne : α ≠ β)
    (hno : ∀ γ, IsRoot .G2 γ → ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → γ ≠ a • α + b • β) (x y : K) :
    Commute (pinnedX .G2 K α x) (pinnedX .G2 K β y) := by
  have h : ⁅rootSubgroup .G2 K α, rootSubgroup .G2 K β⁆ ≤ ⊥ :=
    commutator_le_of_comb hα hβ hαp hβp hne fun γ hγ a b ha hb he => absurd he (hno γ hγ a b ha hb)
  have h1 := h (Subgroup.commutator_mem_commutator (pinnedX_mem_rootSubgroup α x)
    (pinnedX_mem_rootSubgroup β y))
  exact commutatorElement_eq_one_iff_commute.1 (Subgroup.mem_bot.1 h1)

theorem commutator_iSup_le {G : Type*} [Group G] {ι : Sort*} (H : ι → Subgroup G)
    (Z : Subgroup G) (hZ : ∀ i, ∀ x ∈ H i, ∀ z ∈ Z, x * z = z * x)
    (hcomm : ∀ i j, ⁅H i, H j⁆ ≤ Z) : ⁅⨆ i, H i, ⨆ i, H i⁆ ≤ Z := by
  have hQZ : ∀ x ∈ ⨆ i, H i, ∀ z ∈ Z, x * z = z * x := by
    intro x hx z hz
    refine Subgroup.iSup_induction H (C := fun x => x * z = z * x) hx
      (fun i x hx => hZ i x hx z hz) (by simp) ?_
    intro x y hx hy
    rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  have step1 : ∀ i, ∀ x ∈ H i, ∀ y ∈ ⨆ i, H i, ⁅x, y⁆ ∈ Z := by
    intro i x hx y hy
    refine Subgroup.iSup_induction' H (C := fun y _ => ⁅x, y⁆ ∈ Z) (fun j y hy => ?_) ?_ ?_ hy
    · exact Subgroup.commutator_le.1 (hcomm i j) x hx y hy
    · simp [one_mem]
    · intro y1 y2 h1 h2 c1 c2
      have e : y1 * (⁅x, y2⁆ * y1⁻¹) = ⁅x, y2⁆ := by
        rw [← mul_assoc, hQZ y1 h1 _ c2, mul_assoc, mul_inv_cancel, mul_one]
      rw [commutatorElement_mul_right_eq_mul_conj]
      simp only [mul_assoc]
      rw [e]
      exact mul_mem c1 c2
  rw [Subgroup.commutator_le]
  intro x hx y hy
  refine Subgroup.iSup_induction' H (C := fun x _ => ⁅x, y⁆ ∈ Z)
    (fun i x hx => step1 i x hx y hy) ?_ ?_ hx
  · simp [one_mem]
  · intro x1 x2 h1 h2 c1 c2
    have e : x1 * ⁅x2, y⁆ * x1⁻¹ = ⁅x2, y⁆ := by
      rw [hQZ x1 h1 _ c2, mul_inv_cancel_right]
    rw [commutatorElement_mul_left_eq_conj_mul, e]
    exact mul_mem c2 c1

theorem conj_mem_g2Q_of_gens (g : ModGL .G2 K)
    (h : ∀ γ, InPsi γ → ∀ s : K, g * pinnedX .G2 K γ s * g⁻¹ ∈ g2Q K) :
    ∀ q ∈ g2Q K, g * q * g⁻¹ ∈ g2Q K := by
  have hle : g2Q K ≤ (g2Q K).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨s, rfl⟩
    exact h γ hγ s
  exact fun q hq => hle hq

theorem pinnedX_mem_g2Q {γ : Fin Tag.G2.rank → ℤ} (hγ : InPsi γ) (t : K) :
    pinnedX .G2 K γ t ∈ g2Q K :=
  pinnedX_mem_rootSpan (S := {γ | InPsi γ}) hγ t

theorem conj_pinnedX_r_mem {γ : Fin Tag.G2.rank → ℤ} (hγ : InPsi γ) (s t : K) :
    pinnedX .G2 K g2r s * pinnedX .G2 K γ t * (pinnedX .G2 K g2r s)⁻¹ ∈ g2Q K := by
  have hle : ⁅rootSubgroup .G2 K g2r, rootSubgroup .G2 K γ⁆ ≤ g2Q K := by
    refine commutator_le_of_comb isRoot_g2r (isRoot_of_inPsi hγ) (by decide)
      (height_pos_of_inPsi hγ) (g2r_ne_of_inPsi hγ) fun δ hδ a b ha hb he => ?_
    have hδ2 : 2 ≤ height δ := by
      rw [he, height_nsmul_add_nsmul]
      have h1 := one_le_height_of_inPsi hγ
      have hr : height g2r = 1 := by decide
      rw [hr]
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    exact le_iSup₂_of_le δ (inPsi_of_two_le_height hδ hδ2) le_rfl
  have hmem := hle (Subgroup.commutator_mem_commutator (pinnedX_mem_rootSubgroup g2r s)
    (pinnedX_mem_rootSubgroup γ t))
  have e : pinnedX .G2 K g2r s * pinnedX .G2 K γ t * (pinnedX .G2 K g2r s)⁻¹ =
      ⁅pinnedX .G2 K g2r s, pinnedX .G2 K γ t⁆ * pinnedX .G2 K γ t := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hmem (pinnedX_mem_g2Q hγ t)

theorem pinnedX_r_mem_normalizer (s : K) :
    pinnedX .G2 K g2r s ∈ Subgroup.normalizer (g2Q K : Set (ModGL .G2 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ s : K, ∀ q ∈ g2Q K,
      pinnedX .G2 K g2r s * q * (pinnedX .G2 K g2r s)⁻¹ ∈ g2Q K := fun s =>
    conj_mem_g2Q_of_gens _ fun γ hγ t => conj_pinnedX_r_mem hγ s t
  refine ⟨hconj s h, fun hh => ?_⟩
  have h2 := hconj (-s) _ hh
  have e : pinnedX .G2 K g2r (-s) * (pinnedX .G2 K g2r s * h * (pinnedX .G2 K g2r s)⁻¹) *
      (pinnedX .G2 K g2r (-s))⁻¹ = h := by
    rw [← pinnedX_neg .G2 K g2r s, inv_inv]
    group
  rwa [e] at h2

theorem weylElt_map_g2Q :
    (g2Q K).map (MulAut.conj (weylElt .G2 K g2ir 1)).toMonoidHom = g2Q K := by
  have h := (canonical_weyl_root_transport .G2 K).1 (simple .G2 g2ir) {γ | InPsi γ}
    (fun γ hγ => isRoot_of_inPsi hγ)
  rw [canonicalRep_simple, simple_smul_image] at h
  exact h

theorem weylElt_mem_normalizer :
    weylElt .G2 K g2ir 1 ∈ Subgroup.normalizer (g2Q K : Set (ModGL .G2 K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact weylElt_map_g2Q

theorem pinnedX_nr_eq_conj (s : K) :
    ∃ t : K, pinnedX .G2 K g2nr s =
      weylElt .G2 K g2ir 1 * pinnedX .G2 K g2r t * (weylElt .G2 K g2ir 1)⁻¹ := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K g2ir isRoot_g2r
  exact ⟨ε * s, by rw [h, reflect_r_r, ← mul_assoc, hε, one_mul]⟩

theorem weylElt_conj_pinnedX_c (y : K) :
    ∃ y' : K, weylElt .G2 K g2ir 1 * pinnedX .G2 K g2c y' * (weylElt .G2 K g2ir 1)⁻¹ =
      pinnedX .G2 K g2c y := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K g2ir isRoot_g2c
  exact ⟨ε * y, by rw [h, reflect_r_c, ← mul_assoc, hε, one_mul]⟩

theorem g2RankOne_le_normalizer :
    g2RankOne K g2ir ≤ Subgroup.normalizer (g2Q K : Set (ModGL .G2 K)) := by
  rw [g2RankOne_r_eq, Subgroup.closure_le]
  rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · exact pinnedX_r_mem_normalizer s
  · obtain ⟨t, ht⟩ := pinnedX_nr_eq_conj (K := K) s
    rw [SetLike.mem_coe, ht]
    exact mul_mem (mul_mem weylElt_mem_normalizer (pinnedX_r_mem_normalizer _))
      (inv_mem weylElt_mem_normalizer)

end G2Part1

variable {K : Type} [Field K]

local notation "X" => pinnedX Tag.G2 K

theorem g2Q_le_posUnipotent : g2Q K ≤ posUnipotent .G2 K :=
  rootSpan_le_posUnipotent fun γ hγ =>
    ⟨G2Part1.isRoot_of_inPsi hγ, G2Part1.height_pos_of_inPsi hγ⟩

theorem g2Q_le_adjointGroup : g2Q K ≤ adjointGroup .G2 K :=
  iSup₂_le fun γ _ => rootSubgroup_le_adjointGroup γ

theorem g2Q_isPGroup [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] : IsPGroup p (g2Q K) :=
  IsPGroup.to_le (CFSG.SignalizerFunctorTheorem.NonLocalExc.isPGroup_posUnipotent p)
    g2Q_le_posUnipotent

theorem commute_pinnedX_c_posUnipotent (y : K) {u : ModGL .G2 K} (hu : u ∈ posUnipotent .G2 K) :
    Commute (X g2c y) u := by
  have key : ∀ α, IsRoot .G2 α → 0 < height α → ∀ s : K, Commute (X g2c y) (X α s) := by
    intro α hα hαp s
    by_cases hαc : α = g2c
    · subst hαc
      exact (pinnedX_add .G2 K g2c y s).symm.trans ((congrArg (X g2c) (add_comm y s)).trans
        (pinnedX_add .G2 K g2c s y))
    · exact G2Part1.commute_pinnedX_of_no_comb isRoot_g2c hα (by decide) hαp (Ne.symm hαc)
        (fun γ hγ a b ha hb h => G2Part1.not_isRoot_comb_c hαp ha hb (h ▸ hγ)) y s
  have hle : posUnipotent .G2 K ≤ Subgroup.centralizer {X g2c y} := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨s, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (key α hα.1 hα.2 s).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm

theorem g2Q_commutator_le : ⁅g2Q K, g2Q K⁆ ≤ g2Z K := by
  have hQ : g2Q K = ⨆ i : {γ : Fin Tag.G2.rank → ℤ // G2Part1.InPsi γ},
      rootSubgroup .G2 K i.1 :=
    le_antisymm (iSup₂_le fun γ hγ =>
      le_iSup (fun i : {γ : Fin Tag.G2.rank → ℤ // G2Part1.InPsi γ} => rootSubgroup .G2 K i.1)
        ⟨γ, hγ⟩)
      (iSup_le fun i => le_iSup₂_of_le i.1 i.2 le_rfl)
  rw [hQ]
  refine G2Part1.commutator_iSup_le _ (g2Z K) ?_ ?_
  · intro i x hx z hz
    obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hz
    exact (commute_pinnedX_c_posUnipotent y
      (g2Q_le_posUnipotent
        ((show rootSubgroup .G2 K i.1 ≤ g2Q K from le_iSup₂_of_le i.1 i.2 le_rfl) hx))).symm.eq
  · intro i j
    by_cases hij : i = j
    · subst hij
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      rw [(commutatorElement_eq_one_iff_commute).2 (rootSubgroup_mul_comm K ha hb)]
      exact one_mem _
    · refine G2Part1.commutator_le_of_comb (G2Part1.isRoot_of_inPsi i.2)
        (G2Part1.isRoot_of_inPsi j.2) (G2Part1.height_pos_of_inPsi i.2)
        (G2Part1.height_pos_of_inPsi j.2) (fun h => hij (Subtype.ext h)) ?_
      intro γ hγ a b ha hb he
      rw [G2Part1.comb_eq_c i.2 j.2 (fun h => hij (Subtype.ext h)) hγ ha hb he]
      exact le_rfl

theorem g2RankOne_normalizes_g2Q {l q : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ir)
    (hq : q ∈ g2Q K) : l * q * l⁻¹ ∈ g2Q K :=
  (Subgroup.mem_normalizer_iff.1 (G2Part1.g2RankOne_le_normalizer hl) q).1 hq

theorem commute_g2RankOne_pinnedX_c {l : ModGL .G2 K} (hl : l ∈ g2RankOne K g2ir) (y : K) :
    Commute l (X g2c y) := by
  have hr : ∀ (t y : K), Commute (X g2r t) (X g2c y) := fun t y =>
    (G2Part1.commute_pinnedX_of_no_comb isRoot_g2c isRoot_g2r (by decide) (by decide)
      (by decide) (fun γ hγ a b ha hb h => G2Part1.not_isRoot_comb_c (by decide) ha hb (h ▸ hγ))
      y t).symm
  have hle : g2RankOne K g2ir ≤ Subgroup.centralizer {X g2c y} := by
    rw [g2RankOne_r_eq, Subgroup.closure_le]
    rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hr s y).eq
    · obtain ⟨t, ht⟩ := G2Part1.pinnedX_nr_eq_conj (K := K) s
      obtain ⟨y', hy'⟩ := G2Part1.weylElt_conj_pinnedX_c y
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      rw [ht, ← hy']
      calc _ = weylElt .G2 K g2ir 1 * (X g2r t * X g2c y') * (weylElt .G2 K g2ir 1)⁻¹ := by
            group
        _ = weylElt .G2 K g2ir 1 * (X g2c y' * X g2r t) * (weylElt .G2 K g2ir 1)⁻¹ := by
            rw [(hr t y').eq]
        _ = _ := by group
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hl)

theorem commute_g2Q_pinnedX_c {q : ModGL .G2 K} (hq : q ∈ g2Q K) (y : K) :
    Commute q (X g2c y) :=
  (commute_pinnedX_c_posUnipotent y (g2Q_le_posUnipotent hq)).symm

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
