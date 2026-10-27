module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily)
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e7ClassUF4NeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

@[expose] def uOrbitWord : Fin 4 → List (Fin Tag.E7.rank) := ![[1], [3], [2, 4], [0, 5]]

theorem uFixed_check : ∀ i ∈ ([1, 3] : List (Fin Tag.E7.rank)), ∀ β ∈ uFrame,
    isRootB .E7 (Pi.single i 1 + β) = false ∧ isRootB .E7 (-Pi.single i 1 + β) = false := by
  decide +kernel

@[expose] def uPairB (a b : Fin Tag.E7.rank → ℤ) : Bool :=
  uFrame.any fun β₀ => uFrame.any fun β₁ =>
    isRootB .E7 (a + β₀) &&
      (uFrame.all fun β => β == β₀ || !isRootB .E7 (a + β)) &&
      isRootB .E7 (b + β₁) &&
      (uFrame.all fun β => β == β₁ || !isRootB .E7 (b + β)) &&
      (a + β₀ == b + β₁) &&
      !isRootB .E7 (a + (a + β₀))

theorem uPairB_check : ∀ p ∈ ([(2, 4), (0, 5)] : List (Fin Tag.E7.rank × Fin Tag.E7.rank)),
    uPairB (Pi.single p.1 1) (Pi.single p.2 1) = true ∧
      uPairB (-Pi.single p.1 1) (-Pi.single p.2 1) = true := by
  decide +kernel

theorem uPair_check {a b : Fin Tag.E7.rank → ℤ} (h : uPairB a b = true) :
    ∃ β₀ ∈ uFrame, ∃ β₁ ∈ uFrame, isRootB .E7 (a + β₀) = true ∧
      (∀ β ∈ uFrame, β ≠ β₀ → isRootB .E7 (a + β) = false) ∧
      isRootB .E7 (b + β₁) = true ∧
      (∀ β ∈ uFrame, β ≠ β₁ → isRootB .E7 (b + β) = false) ∧
      a + β₀ = b + β₁ ∧ isRootB .E7 (a + (a + β₀)) = false := by
  simp only [uPairB, List.any_eq_true, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨β₀, h₀, β₁, h₁, ⟨⟨⟨⟨⟨hr0, hu0⟩, hr1⟩, hu1⟩, hs⟩, hn⟩⟩ := h
  refine ⟨β₀, h₀, β₁, h₁, hr0, fun β hβ hne => ?_, hr1, fun β hβ hne => ?_, hs, hn⟩
  · rcases hu0 β hβ with h | h
    · exact absurd h hne
    · exact h
  · rcases hu1 β hβ with h | h
    · exact absurd h hne
    · exact h

theorem uLevel_single_check : ∀ i : Fin Tag.E7.rank, i ≠ 6 →
    uLevel (Pi.single i 1) = 0 ∧ uLevel (-Pi.single i 1) = 0 := by
  decide

variable {K : Type} [Field K]


theorem ne_of_uLevel_zero {a β : Fin Tag.E7.rank → ℤ} (ha0 : uLevel a = 0) (hβ : β ∈ uPsi) :
    a ≠ β ∧ a ≠ -β := by
  have h1 := level_of_mem_uPsi hβ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at ha0
    omega
  · rw [h, uLevel_neg] at ha0
    omega

theorem conj_list_prod_pinnedX_uPsi [CharP K 2] {F : List (Fin Tag.E7.rank → ℤ)}
    (hF : ∀ β ∈ F, β ∈ uPsi) (hnd : F.Nodup) {a β₀ : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (ha0 : uLevel a = 0) (hβ₀ : β₀ ∈ uPsi) (hab : IsRoot .E7 (a + β₀))
    (huniq : ∀ β ∈ F, β ≠ β₀ → ¬IsRoot .E7 (a + β)) (t : K) :
    pinnedX .E7 K a t * (F.map fun β => pinnedX .E7 K β 1).prod * (pinnedX .E7 K a t)⁻¹ =
      (if β₀ ∈ F then pinnedX .E7 K (a + β₀) t else 1) * (F.map fun β => pinnedX .E7 K β 1).prod := by
  have hρΨ : a + β₀ ∈ uPsi := mem_uPsi_of_level hab (by
    rw [uLevel_add, ha0, zero_add, level_of_mem_uPsi hβ₀])
  induction F with
  | nil => simp
  | cons β F ih =>
    rw [List.nodup_cons] at hnd
    have hβΨ := hF β List.mem_cons_self
    have ih' := ih (fun γ hγ => hF γ (List.mem_cons_of_mem _ hγ)) hnd.2
      (fun γ hγ hne => huniq γ (List.mem_cons_of_mem _ hγ) hne)
    have hsplit : pinnedX .E7 K a t * ((β :: F).map fun β => pinnedX .E7 K β 1).prod *
        (pinnedX .E7 K a t)⁻¹ =
        (pinnedX .E7 K a t * pinnedX .E7 K β 1 * (pinnedX .E7 K a t)⁻¹) *
          (pinnedX .E7 K a t * (F.map fun β => pinnedX .E7 K β 1).prod * (pinnedX .E7 K a t)⁻¹) := by
      rw [List.map_cons, List.prod_cons]
      group
    rw [hsplit, ih', List.map_cons, List.prod_cons]
    by_cases hβ : β = β₀
    · subst hβ
      have hcomm := CFSG.SeitzReduction.commutatorElement_pinnedX_of_oddDerivLaced
        CharTwo.two_eq_zero
        (CFSG.SeitzReduction.oddDerivLacedCheck_of_simplyLaced (Or.inr (Or.inr (Or.inl rfl))))
        ha (isRoot_of_mem_uPsi hβΨ)
        (ne_of_uLevel_zero ha0 hβΨ).1 (ne_of_uLevel_zero ha0 hβΨ).2 hab t (1 : K)
      rw [mul_one, commutatorElement_def] at hcomm
      have e : pinnedX .E7 K a t * pinnedX .E7 K β 1 * (pinnedX .E7 K a t)⁻¹ =
          pinnedX .E7 K (a + β) t * pinnedX .E7 K β 1 := by
        rw [← hcomm]
        group
      rw [e, ite_eq_right hnd.1, ite_eq_left List.mem_cons_self, one_mul, mul_assoc]
    · have hc : Commute (pinnedX .E7 K a t) (pinnedX .E7 K β 1) :=
        CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv ha (isRoot_of_mem_uPsi hβΨ)
          (ne_of_uLevel_zero ha0 hβΨ).2 (huniq β List.mem_cons_self hβ) t 1
      rw [hc.eq, mul_inv_cancel_right]
      have hmem : (β₀ ∈ β :: F) ↔ β₀ ∈ F := by
        rw [List.mem_cons]
        exact ⟨fun h => h.resolve_left (Ne.symm hβ), Or.inr⟩
      by_cases h₀ : β₀ ∈ F
      · rw [ite_eq_left h₀, ite_eq_left (hmem.2 h₀), ← mul_assoc, ← mul_assoc,
          (uPsi_comm β hβΨ (a + β₀) hρΨ 1 t).eq]
      · rw [ite_eq_right h₀, ite_eq_right (fun h => h₀ (hmem.1 h)), one_mul, one_mul]

theorem uAS_eq_prod : uAS K = (uFrame.map fun β => pinnedX .E7 K β 1).prod := rfl

theorem conj_uAS_of_unique [CharP K 2] {a β₀ : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (ha0 : uLevel a = 0) (hβ₀ : β₀ ∈ uFrame) (hab : IsRoot .E7 (a + β₀))
    (huniq : ∀ β ∈ uFrame, β ≠ β₀ → ¬IsRoot .E7 (a + β)) (t : K) :
    pinnedX .E7 K a t * uAS K * (pinnedX .E7 K a t)⁻¹ = pinnedX .E7 K (a + β₀) t * uAS K := by
  rw [uAS_eq_prod, conj_list_prod_pinnedX_uPsi (fun β hβ => mem_uPsi_of_mem_uFrame hβ)
    uFrame_pairwise.1 ha ha0 (mem_uPsi_of_mem_uFrame hβ₀) hab huniq t, ite_eq_left hβ₀]

theorem commute_uAS_of_forall {a : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (ha0 : uLevel a = 0) (h : ∀ β ∈ uFrame, ¬IsRoot .E7 (a + β)) (t : K) :
    Commute (pinnedX .E7 K a t) (uAS K) := by
  rw [uAS_eq_prod]
  exact Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
    exact CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv ha
      (isRoot_of_mem_uPsi (mem_uPsi_of_mem_uFrame hβ))
      (ne_of_uLevel_zero ha0 (mem_uPsi_of_mem_uFrame hβ)).2 (h β hβ) t 1

theorem commute_pair_uAS [CharP K 2] {a b : Fin Tag.E7.rank → ℤ} (ha : IsRoot .E7 a)
    (hb : IsRoot .E7 b) (ha0 : uLevel a = 0) (hb0 : uLevel b = 0) (h : uPairB a b = true)
    (t : K) : Commute (pinnedX .E7 K a t * pinnedX .E7 K b t) (uAS K) := by
  obtain ⟨β₀, h₀, β₁, h₁, hr0, hu0, hr1, hu1, hs, hn⟩ := uPair_check h
  have notroot : ∀ {γ : Fin Tag.E7.rank → ℤ}, isRootB .E7 γ = false → ¬IsRoot .E7 γ :=
    fun h hr => by rw [← isRootB_iff, h] at hr; exact Bool.false_ne_true hr
  have e1 := conj_uAS_of_unique (K := K) hb hb0 h₁ (isRootB_iff.1 hr1)
    (fun β hβ hne => notroot (hu1 β hβ hne)) t
  have e2 := conj_uAS_of_unique (K := K) ha ha0 h₀ (isRootB_iff.1 hr0)
    (fun β hβ hne => notroot (hu0 β hβ hne)) t
  rw [← hs] at e1
  have hρΨ : a + β₀ ∈ uPsi := mem_uPsi_of_level (isRootB_iff.1 hr0) (by
    rw [uLevel_add, ha0, zero_add, level_of_mem_uPsi (mem_uPsi_of_mem_uFrame h₀)])
  have e3 : Commute (pinnedX .E7 K a t) (pinnedX .E7 K (a + β₀) t) :=
    CFSG.SeitzReduction.commute_pinnedX_of_oddDeriv ha (isRootB_iff.1 hr0)
      (ne_of_uLevel_zero ha0 hρΨ).2 (notroot hn) t t
  have key : (pinnedX .E7 K a t * pinnedX .E7 K b t) * uAS K *
      (pinnedX .E7 K a t * pinnedX .E7 K b t)⁻¹ = uAS K := by
    calc (pinnedX .E7 K a t * pinnedX .E7 K b t) * uAS K *
          (pinnedX .E7 K a t * pinnedX .E7 K b t)⁻¹ =
          pinnedX .E7 K a t * (pinnedX .E7 K b t * uAS K * (pinnedX .E7 K b t)⁻¹) *
            (pinnedX .E7 K a t)⁻¹ := by group
      _ = pinnedX .E7 K (a + β₀) t * (pinnedX .E7 K a t * uAS K * (pinnedX .E7 K a t)⁻¹) := by
          rw [e1, ← mul_assoc, e3.eq]
          group
      _ = pinnedX .E7 K (a + β₀) (t + t) * uAS K := by
          rw [e2, ← mul_assoc, ← pinnedX_add]
      _ = uAS K := by
          rw [CharTwo.add_self_eq_zero, pinnedX_zero, one_mul]
  calc (pinnedX .E7 K a t * pinnedX .E7 K b t) * uAS K =
        ((pinnedX .E7 K a t * pinnedX .E7 K b t) * uAS K *
          (pinnedX .E7 K a t * pinnedX .E7 K b t)⁻¹) *
            (pinnedX .E7 K a t * pinnedX .E7 K b t) := by group
    _ = uAS K * (pinnedX .E7 K a t * pinnedX .E7 K b t) := by rw [key]

variable (K) in
@[expose] noncomputable def uOrbitX (j : Fin 4) (c : K) : ModGL .E7 K :=
  ((uOrbitWord j).map fun i => pinnedX .E7 K (Pi.single i 1) c).prod

variable (K) in
@[expose] noncomputable def uOrbitY (j : Fin 4) (c : K) : ModGL .E7 K :=
  ((uOrbitWord j).map fun i => pinnedX .E7 K (-Pi.single i 1) c).prod

theorem uOrbitX_mem_adjointGroup (j : Fin 4) (c : K) : uOrbitX K j c ∈ adjointGroup .E7 K :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_adjointGroup _ c

theorem uOrbitY_mem_adjointGroup (j : Fin 4) (c : K) : uOrbitY K j c ∈ adjointGroup .E7 K :=
  list_prod_mem fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact pinnedX_mem_adjointGroup _ c

theorem uOrbitX_eq (c : K) :
    uOrbitX K 0 c = pinnedX .E7 K (Pi.single 1 1) c ∧
      uOrbitX K 1 c = pinnedX .E7 K (Pi.single 3 1) c ∧
      uOrbitX K 2 c = pinnedX .E7 K (Pi.single 2 1) c * pinnedX .E7 K (Pi.single 4 1) c ∧
      uOrbitX K 3 c = pinnedX .E7 K (Pi.single 0 1) c * pinnedX .E7 K (Pi.single 5 1) c := by
  refine ⟨mul_one _, mul_one _, ?_, ?_⟩
  · change _ * (_ * 1) = _
    rw [mul_one]
  · change _ * (_ * 1) = _
    rw [mul_one]

theorem uOrbitY_eq (c : K) :
    uOrbitY K 0 c = pinnedX .E7 K (-Pi.single 1 1) c ∧
      uOrbitY K 1 c = pinnedX .E7 K (-Pi.single 3 1) c ∧
      uOrbitY K 2 c = pinnedX .E7 K (-Pi.single 2 1) c * pinnedX .E7 K (-Pi.single 4 1) c ∧
      uOrbitY K 3 c = pinnedX .E7 K (-Pi.single 0 1) c * pinnedX .E7 K (-Pi.single 5 1) c := by
  refine ⟨mul_one _, mul_one _, ?_, ?_⟩
  · change _ * (_ * 1) = _
    rw [mul_one]
  · change _ * (_ * 1) = _
    rw [mul_one]

theorem not_isRoot_of_isRootB_false {γ : Fin Tag.E7.rank → ℤ} (h : isRootB .E7 γ = false) :
    ¬IsRoot .E7 γ := fun hr => by
  rw [← isRootB_iff, h] at hr
  exact Bool.false_ne_true hr

theorem commute_fixed_uAS {i : Fin Tag.E7.rank} (hi : i ∈ ([1, 3] : List (Fin Tag.E7.rank)))
    (c : K) : Commute (pinnedX .E7 K (Pi.single i 1) c) (uAS K) ∧
      Commute (pinnedX .E7 K (-Pi.single i 1) c) (uAS K) := by
  have hi6 : i ≠ 6 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  obtain ⟨h0, h0'⟩ := uLevel_single_check i hi6
  exact ⟨commute_uAS_of_forall (isRoot_single .E7 i) h0
      (fun β hβ => not_isRoot_of_isRootB_false (uFixed_check i hi β hβ).1) c,
    commute_uAS_of_forall (isRoot_neg_single .E7 i) h0'
      (fun β hβ => not_isRoot_of_isRootB_false (uFixed_check i hi β hβ).2) c⟩

theorem commute_pairs_uAS [CharP K 2] {p : Fin Tag.E7.rank × Fin Tag.E7.rank}
    (hp : p ∈ ([(2, 4), (0, 5)] : List (Fin Tag.E7.rank × Fin Tag.E7.rank))) (c : K) :
    Commute (pinnedX .E7 K (Pi.single p.1 1) c * pinnedX .E7 K (Pi.single p.2 1) c) (uAS K) ∧
      Commute (pinnedX .E7 K (-Pi.single p.1 1) c * pinnedX .E7 K (-Pi.single p.2 1) c)
        (uAS K) := by
  have h6 : p.1 ≠ 6 ∧ p.2 ≠ 6 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide
  obtain ⟨a0, a0'⟩ := uLevel_single_check p.1 h6.1
  obtain ⟨b0, b0'⟩ := uLevel_single_check p.2 h6.2
  exact ⟨commute_pair_uAS (isRoot_single .E7 _) (isRoot_single .E7 _) a0 b0
      (uPairB_check p hp).1 c,
    commute_pair_uAS (isRoot_neg_single .E7 _) (isRoot_neg_single .E7 _) a0' b0'
      (uPairB_check p hp).2 c⟩

theorem commute_uOrbit_uAS [CharP K 2] (j : Fin 4) (c : K) :
    Commute (uOrbitX K j c) (uAS K) ∧ Commute (uOrbitY K j c) (uAS K) := by
  obtain ⟨x0, x1, x2, x3⟩ := uOrbitX_eq (K := K) c
  obtain ⟨y0, y1, y2, y3⟩ := uOrbitY_eq (K := K) c
  fin_cases j
  · rw [show ((⟨0, by decide⟩ : Fin 4)) = 0 from rfl, x0, y0]
    exact commute_fixed_uAS (by decide) c
  · rw [show ((⟨1, by decide⟩ : Fin 4)) = 1 from rfl, x1, y1]
    exact commute_fixed_uAS (by decide) c
  · rw [show ((⟨2, by decide⟩ : Fin 4)) = 2 from rfl, x2, y2]
    exact commute_pairs_uAS (p := (2, 4)) (by decide) c
  · rw [show ((⟨3, by decide⟩ : Fin 4)) = 3 from rfl, x3, y3]
    exact commute_pairs_uAS (p := (0, 5)) (by decide) c

variable (K) in
@[expose] noncomputable def uF4AS : Subgroup (adjointGroup .E7 K) :=
  closure {g | ∃ (j : Fin 4) (c : K),
    (g : ModGL .E7 K) = uOrbitX K j c ∨ (g : ModGL .E7 K) = uOrbitY K j c}

theorem uF4AS_le_centralizer [CharP K 2] :
    uF4AS K ≤ centralizer ({e7ASRep K 3} : Set (adjointGroup .E7 K)) := by
  refine (closure_le _).2 ?_
  rintro g ⟨j, c, h | h⟩
  · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h, coe_e7ASRep_three]
    exact (commute_uOrbit_uAS j c).1.eq
  · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h, coe_e7ASRep_three]
    exact (commute_uOrbit_uAS j c).2.eq

theorem e7RepPreHigh_three : e7RepPreHigh 3 = Pi.single 3 1 := by
  decide +kernel

theorem rootSL2_alpha4_le_uF4AS :
    rootSubgroup .E7 K (e7RepPreHigh 3) ⊔ rootSubgroup .E7 K (-e7RepPreHigh 3) ≤
      (uF4AS K).map (adjointGroup .E7 K).subtype := by
  have x1 : ∀ c : K, uOrbitX K 1 c = pinnedX .E7 K (Pi.single 3 1) c := fun c =>
    (uOrbitX_eq c).2.1
  have y1 : ∀ c : K, uOrbitY K 1 c = pinnedX .E7 K (-Pi.single 3 1) c := fun c =>
    (uOrbitY_eq c).2.1
  rw [e7RepPreHigh_three]
  refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨c, rfl⟩
    exact ⟨⟨uOrbitX K 1 c, uOrbitX_mem_adjointGroup 1 c⟩,
      subset_closure ⟨1, c, Or.inl rfl⟩, x1 c⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨⟨uOrbitY K 1 c, uOrbitY_mem_adjointGroup 1 c⟩,
      subset_closure ⟨1, c, Or.inr rfl⟩, y1 c⟩

theorem uOrbitWord_ne_six : ∀ j : Fin 4, ∀ i ∈ uOrbitWord j, i ≠ 6 := by
  decide

theorem uF4AS_le_parabolicLevi :
    uF4AS K ≤ (parabolicLevi .E7 K uNodes).subgroupOf (adjointGroup .E7 K) := by
  have hgen : ∀ i : Fin Tag.E7.rank, i ≠ 6 → ∀ c : K,
      pinnedX .E7 K (Pi.single i 1) c ∈ parabolicLevi .E7 K uNodes ∧
        pinnedX .E7 K (-Pi.single i 1) c ∈ parabolicLevi .E7 K uNodes := by
    intro i hi c
    rw [pinnedX_single, pinnedX_neg_single]
    exact ⟨mem_sup_right (subset_closure ⟨i, hi, c, Or.inl rfl⟩),
      mem_sup_right (subset_closure ⟨i, hi, c, Or.inr rfl⟩)⟩
  refine (closure_le _).2 ?_
  rintro g ⟨j, c, h | h⟩
  · rw [SetLike.mem_coe, mem_subgroupOf, h]
    exact list_prod_mem fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact (hgen i (uOrbitWord_ne_six j i hi) c).1
  · rw [SetLike.mem_coe, mem_subgroupOf, h]
    exact list_prod_mem fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact (hgen i (uOrbitWord_ne_six j i hi) c).2

variable (K) in
@[expose] noncomputable def uF4 : Subgroup (adjointGroup .E7 K) :=
  (uF4AS K).map (MulAut.conj (e7RepConj K 3)).toMonoidHom

theorem uF4_le_centralizer [CharP K 2] :
    uF4 K ≤ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) := by
  rintro _ ⟨l, hl, rfl⟩
  have hl' := mem_centralizer_singleton_iff.1 (uF4AS_le_centralizer hl)
  rw [mem_centralizer_singleton_iff, ← e7RepConj_mul_e7ASRep_mul_inv (K := K) 3]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc e7RepConj K 3 * l * (e7RepConj K 3)⁻¹ *
        (e7RepConj K 3 * e7ASRep K 3 * (e7RepConj K 3)⁻¹) =
        e7RepConj K 3 * (l * e7ASRep K 3) * (e7RepConj K 3)⁻¹ := by group
    _ = e7RepConj K 3 * (e7ASRep K 3 * l) * (e7RepConj K 3)⁻¹ := by rw [hl']
    _ = e7RepConj K 3 * e7ASRep K 3 * (e7RepConj K 3)⁻¹ *
        (e7RepConj K 3 * l * (e7RepConj K 3)⁻¹) := by group

theorem highRootSL2_le_uF4 :
    (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) ≤ uF4 K := by
  intro h hh
  rw [mem_subgroupOf, ← map_conj_e7RepConj_rootSL2_preHigh (K := K) 3] at hh
  obtain ⟨y, hy, hyh⟩ := hh
  obtain ⟨l, hl, rfl⟩ := rootSL2_alpha4_le_uF4AS hy
  refine ⟨l, hl, Subtype.ext ?_⟩
  rw [← hyh]
  rfl

theorem uF4_le_leviU : uF4 K ≤ leviU K :=
  Subgroup.map_mono uF4AS_le_parabolicLevi

theorem uF4_le_leviU_inf_centralizer [CharP K 2] :
    uF4 K ≤ leviU K ⊓ centralizer ({e7Rep K 3} : Set (adjointGroup .E7 K)) :=
  le_inf uF4_le_leviU uF4_le_centralizer

end CFSG.SeitzReduction.E7Pilot
