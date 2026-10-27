module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcSub
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction
open Subgroup
open scoped commutatorElement

variable {K : Type} [Field K]

noncomputable abbrev e8RootElt
    (γ : Fin Tag.E8.rank → ℤ) : adjointGroup .E8 K :=
  ⟨pinnedX .E8 K γ 1, pinnedX_mem_adjointGroup _ _⟩

theorem e8Frames_facts : ∀ F ∈ [e8FrameX, e8FrameY, e8FrameZ, e8FrameU],
    F ≠ [] ∧ F.Nodup ∧ F.Pairwise fun σ σ' => iform σ σ' = 0 := by
  decide +kernel

theorem e8FramePt_mul_self
    [CharP K 2] {F : List (Fin Tag.E8.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot .E8 σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) :
    e8FramePt K F * e8FramePt K F = 1 := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  apply Subtype.ext
  show (F.map fun σ => pinnedX .E8 K σ 1).prod * (F.map fun σ => pinnedX .E8 K σ 1).prod = 1
  induction F with
  | nil => simp
  | cons a F ih =>
    rw [List.pairwise_cons] at horth
    have ha := hF a List.mem_cons_self
    have hcomm : Commute (pinnedX .E8 K a 1) (F.map fun σ => pinnedX .E8 K σ 1).prod :=
      Commute.list_prod_right _ _ fun y hy => by
        obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hy
        exact classD4_commute_pinnedX hτ ha (hF σ (List.mem_cons_of_mem _ hσ))
          (horth.1 σ hσ).ge 1 1
    simp only [List.map_cons, List.prod_cons]
    calc pinnedX .E8 K a 1 * (F.map fun σ => pinnedX .E8 K σ 1).prod *
          (pinnedX .E8 K a 1 * (F.map fun σ => pinnedX .E8 K σ 1).prod)
        = pinnedX .E8 K a 1 * pinnedX .E8 K a 1 *
            ((F.map fun σ => pinnedX .E8 K σ 1).prod *
              (F.map fun σ => pinnedX .E8 K σ 1).prod) := by
          rw [mul_assoc, ← mul_assoc _ (pinnedX .E8 K a 1), ← hcomm.eq]
          group
      _ = 1 := by
          rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero, one_mul,
            ih (fun σ hσ => hF σ (List.mem_cons_of_mem _ hσ)) horth.2]

theorem e8FramePt_ne_one
    {F : List (Fin Tag.E8.rank → ℤ)}
    (hne : F ≠ []) (hnd : F.Nodup) (hF : ∀ σ ∈ F, IsRoot .E8 σ ∧ 0 < height σ) :
    e8FramePt K F ≠ 1 := by
  intro h1
  have h := congrArg Subtype.val h1
  have h0 : (F.map fun σ => pinnedX .E8 K σ ((fun _ => (1 : K)) σ)).prod =
      (F.map fun σ => pinnedX .E8 K σ ((fun _ => (0 : K)) σ)).prod := by
    simp only [pinnedX_zero, List.map_const', List.prod_replicate, one_pow]
    exact h
  obtain ⟨σ, hσ⟩ := List.exists_mem_of_ne_nil F hne
  exact one_ne_zero (pinnedX_list_prod_injective F hnd hF _ _ h0 σ hσ)

theorem involution_e8Reps
    [CharP K 2] : ∀ x ∈ e8Reps K, x * x = 1 ∧ x ≠ 1 := by
  have hroots : ∀ F : List (Fin Tag.E8.rank → ℤ),
      (∀ σ ∈ F, σ ∈ e8FrameX ++ e8FrameY ++ e8FrameZ ++ e8FrameU) →
      ∀ σ ∈ F, IsRoot .E8 σ ∧ 0 < height σ := fun F hF σ hσ =>
    ⟨(isRoot_of_mem_e8Frames σ (hF σ hσ)).1, (isRoot_of_mem_e8Frames σ (hF σ hσ)).2.2⟩
  have hfacts := e8Frames_facts
  intro x hx
  simp only [e8Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := hfacts e8FrameX (by simp)
    have hr := hroots e8FrameX (fun σ hσ => by simp_all)
    exact ⟨e8FramePt_mul_self (fun σ hσ => (hr σ hσ).1) h3, e8FramePt_ne_one h1 h2 hr⟩
  · obtain ⟨h1, h2, h3⟩ := hfacts e8FrameY (by simp)
    have hr := hroots e8FrameY (fun σ hσ => by simp_all)
    exact ⟨e8FramePt_mul_self (fun σ hσ => (hr σ hσ).1) h3, e8FramePt_ne_one h1 h2 hr⟩
  · obtain ⟨h1, h2, h3⟩ := hfacts e8FrameZ (by simp)
    have hr := hroots e8FrameZ (fun σ hσ => by simp_all)
    exact ⟨e8FramePt_mul_self (fun σ hσ => (hr σ hσ).1) h3, e8FramePt_ne_one h1 h2 hr⟩
  · obtain ⟨h1, h2, h3⟩ := hfacts e8FrameU (by simp)
    have hr := hroots e8FrameU (fun σ hσ => by simp_all)
    exact ⟨e8FramePt_mul_self (fun σ hσ => (hr σ hσ).1) h3, e8FramePt_ne_one h1 h2 hr⟩

theorem charTwo_e8Reps
    [Finite K] [CharP K 2] : ∀ x ∈ e8Reps K, Exc.CharTwo x := by
  intro x hx
  obtain ⟨hx2, hx1⟩ := involution_e8Reps x hx
  exact EvenOddRadical.charTwo_of_involution (.ordinary .E8) (x := x) hx2 hx1

theorem map_closure_odd_le_e8 {C : Type*} [Group C] (α : MulAut C) (x : C) :
    (closure {c | c * x = x * c ∧ Odd (orderOf c)}).map α.toMonoidHom ≤
      closure {c | c * α x = α x * c ∧ Odd (orderOf c)} := by
  rw [MonoidHom.map_closure]
  refine closure_mono ?_
  rintro _ ⟨c, ⟨hc, hodd⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, hc, map_mul]
  · simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] using hodd

theorem residualMem_conj_of_witness {C : Type*} [Group C] {x : C} {P : Subgroup C}
    (hP : IsPGroup 2 P) (hPx : P ≤ closure {c | c * x = x * c ∧ Odd (orderOf c)})
    (hx : x ∈ ⁅P, P⁆) (g : C) : Exc.ResidualMem (g * x * g⁻¹) := by
  have hg : g * x * g⁻¹ = MulAut.conj g x := (MulAut.conj_apply g x).symm
  rw [hg]
  have h1 : closure {c : C | c * MulAut.conj g x = MulAut.conj g x * c ∧ Odd (orderOf c)} ≤
      AS76b.oUpperTwo (Exc.cent (MulAut.conj g x)) :=
    closure_mono fun c hc => ⟨mem_centralizer_singleton_iff.2 hc.1, hc.2⟩
  have hP' := (map_mono hPx).trans (map_closure_odd_le_e8 (MulAut.conj g) x)
  refine commutator_le_admResidual_of_isPGroup (hP'.trans (h1.trans le_sup_left)) (hP.map _) ?_
  rw [← map_commutator]
  exact mem_map_of_mem _ hx

theorem e8FramePt_eq_prod
    (F : List (Fin Tag.E8.rank → ℤ)) :
    e8FramePt K F = (F.map fun σ => (e8RootElt σ : adjointGroup .E8 K)).prod := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  rfl

theorem oddCommWitness_of_pairs
    [Finite K] [CharP K 2]
    {t : adjointGroup .E8 K} (D : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)))
    (hD : ∀ p ∈ D, (IsRoot .E8 p.1 ∧ 0 < height p.1) ∧ (IsRoot .E8 p.2 ∧ 0 < height p.2) ∧
      p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧ IsRoot .E8 (p.1 + p.2))
    (ht : t = e8FramePt K (D.map fun p => p.1 + p.2))
    (hodd : ∀ p ∈ D, (e8RootElt p.1 : adjointGroup .E8 K) ∈
        closure {c | c * t = t * c ∧ Odd (orderOf c)} ∧
      (e8RootElt p.2 : adjointGroup .E8 K) ∈ closure {c | c * t = t * c ∧ Odd (orderOf c)}) :
    ∃ P : Subgroup (adjointGroup .E8 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * t = t * c ∧ Odd (orderOf c)} ∧ t ∈ ⁅P, P⁆ := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set (adjointGroup .E8 K) :=
    {g | ∃ p ∈ D, g = e8RootElt p.1 ∨ g = e8RootElt p.2} with hSdef
  refine ⟨closure S, ?_, ?_, ?_⟩
  · refine ((isPGroup_posUnipotent (K := K) 2 .E8).comap_subtype
      (K := adjointGroup .E8 K)).to_le ?_
    rw [closure_le]
    rintro _ ⟨p, hp, rfl | rfl⟩
    · exact pinnedX_mem_rootSpan (S := {α | IsRoot .E8 α ∧ 0 < height α}) (hD p hp).1 1
    · exact pinnedX_mem_rootSpan (S := {α | IsRoot .E8 α ∧ 0 < height α}) (hD p hp).2.1 1
  · rw [closure_le]
    rintro _ ⟨p, hp, rfl | rfl⟩
    exacts [(hodd p hp).1, (hodd p hp).2]
  · rw [ht, e8FramePt_eq_prod, List.map_map]
    refine list_prod_mem fun g hg => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1, h2, hne, hne', hab⟩ := hD p hp
    have hc : (e8RootElt (p.1 + p.2) : adjointGroup .E8 K) =
        ⁅(e8RootElt p.1 : adjointGroup .E8 K), e8RootElt p.2⁆ := by
      refine Subtype.ext ?_
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [EvenOddRadical.pinnedX_conj_of_isRoot hτ CharTwo.two_eq_zero h1.1 h2.1 hne hne' hab 1 1,
        mul_one, mul_inv_cancel_right]
    show (e8RootElt (p.1 + p.2) : adjointGroup .E8 K) ∈ _
    rw [hc]
    exact commutator_mem_commutator (subset_closure ⟨p, hp, Or.inl rfl⟩)
      (subset_closure ⟨p, hp, Or.inr rfl⟩)

@[expose] def e8PairsX : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![2, 3, 4, 6, 5, 4, 3, 1], ![0, 0, 0, 0, 0, 0, 0, 1])]

@[expose] def e8PairsY : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![1, 0, 1, 0, 0, 0, 0, 0], ![1, 2, 3, 5, 4, 3, 2, 1]),
    (![1, 0, 0, 0, 0, 0, 0, 0], ![1, 3, 3, 5, 4, 3, 2, 1])]

@[expose] def e8PairsZ : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![0, 0, 0, 0, 0, 0, 1, 0], ![2, 2, 3, 4, 3, 2, 1, 1]),
    (![0, 0, 0, 0, 0, 1, 1, 0], ![1, 2, 3, 4, 3, 2, 1, 1]),
    (![0, 0, 0, 0, 1, 1, 1, 0], ![1, 2, 2, 4, 3, 2, 1, 1])]

@[expose] def e8PairsU : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![1, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 3, 2, 1, 0]),
    (![0, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 3, 2, 1, 1]),
    (![0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 2, 3, 3, 3, 2, 1]),
    (![0, 1, 0, 1, 0, 0, 0, 0], ![1, 1, 2, 3, 3, 2, 2, 1])]

theorem e8Pairs_check : ∀ D ∈ [e8PairsX, e8PairsY, e8PairsZ, e8PairsU], ∀ p ∈ D,
    (List.ofFn p.1 ∈ Tag.artifactRoots .E8 ∧ 0 < height p.1) ∧
      (List.ofFn p.2 ∈ Tag.artifactRoots .E8 ∧ 0 < height p.2) ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧
        List.ofFn (p.1 + p.2) ∈ Tag.artifactRoots .E8 := by
  decide +kernel

theorem e8Pairs_map : e8PairsX.map (fun p => p.1 + p.2) = [highRoot .E8] ∧
    e8PairsY.map (fun p => p.1 + p.2) = oddDerivE8YFrame ∧
    e8PairsZ.map (fun p => p.1 + p.2) = oddDerivE8ZFrame ∧
    e8PairsU.map (fun p => p.1 + p.2) = oddDerivE8UFrame := by
  decide +kernel

theorem e8Pairs_mem_S₂ :
    (∀ p ∈ e8PairsY, p.1 ∈ oddDerivE8YDeriv.map Prod.fst ∧ p.2 ∈ oddDerivE8YDeriv.map Prod.fst) ∧
    (∀ p ∈ e8PairsZ, p.1 ∈ oddDerivE8ZDeriv.map Prod.fst ∧ p.2 ∈ oddDerivE8ZDeriv.map Prod.fst) ∧
    ∀ p ∈ e8PairsU, p.1 ∈ oddDerivE8UDeriv.map Prod.fst ∧ p.2 ∈ oddDerivE8UDeriv.map Prod.fst := by
  decide +kernel

theorem e8Pairs_roots
    {D : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ))}
    (hD : D ∈ [e8PairsX, e8PairsY, e8PairsZ, e8PairsU]) :
    ∀ p ∈ D, (IsRoot .E8 p.1 ∧ 0 < height p.1) ∧ (IsRoot .E8 p.2 ∧ 0 < height p.2) ∧
      p.1 ≠ p.2 ∧ p.1 ≠ -p.2 ∧ IsRoot .E8 (p.1 + p.2) := by
  intro p hp
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7⟩ := e8Pairs_check D hD p hp
  exact ⟨⟨isRoot_iff_mem_artifactRoots.2 h1, h2⟩, ⟨isRoot_iff_mem_artifactRoots.2 h3, h4⟩, h5, h6,
    isRoot_iff_mem_artifactRoots.2 h7⟩

theorem residual_witness_e8_x
    [Finite K] [CharP K 2]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    ∃ P : Subgroup (adjointGroup .E8 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * e8FramePt K [highRoot .E8] = e8FramePt K [highRoot .E8] * c ∧
        Odd (orderOf c)} ∧ e8FramePt K [highRoot .E8] ∈ ⁅P, P⁆ := by
  have hτ : Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 := Or.inr (Or.inr rfl)
  have ht : ((e8FramePt K [highRoot .E8] : adjointGroup .E8 K) : ModGL .E8 K) =
      pinnedX .E8 K (highRoot .E8) 1 := by
    simp [e8FramePt]
  have hD := e8Pairs_roots (D := e8PairsX) (by simp)
  have hodd : ∀ γ, IsRoot .E8 γ → 0 < height γ → (e8RootElt γ : adjointGroup .E8 K) ∈
      closure {c | c * e8FramePt K [highRoot .E8] = e8FramePt K [highRoot .E8] * c ∧
        Odd (orderOf c)} := by
    intro γ hγ hγp
    rcases (show m = 1 ∨ 2 ≤ m by omega) with h1 | hf
    · exact posUnipotent_le_closure_odd_E_two hτ (by rw [hK, h1, pow_one]) ht
        (pinnedX_mem_rootSpan (S := {α | IsRoot .E8 α ∧ 0 < height α}) ⟨hγ, hγp⟩ 1)
    · exact pinnedX_mem_closure_odd_E hτ hf hK ht hγ hγp 1
  exact oddCommWitness_of_pairs e8PairsX hD (by rw [e8Pairs_map.1]) fun p hp =>
    ⟨hodd _ (hD p hp).1.1 (hD p hp).1.2, hodd _ (hD p hp).2.1.1 (hD p hp).2.1.2⟩

theorem residual_witness_e8_y
    [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E8 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * e8FramePt K oddDerivE8YFrame = e8FramePt K oddDerivE8YFrame * c ∧
        Odd (orderOf c)} ∧ e8FramePt K oddDerivE8YFrame ∈ ⁅P, P⁆ := by
  have hD := e8Pairs_roots (D := e8PairsY) (by simp)
  refine oddCommWitness_of_pairs e8PairsY hD (by rw [e8Pairs_map.2.1]) fun p hp => ⟨?_, ?_⟩
  · exact rootSpan_le_closure_odd_E8_y (t := e8FramePt K oddDerivE8YFrame) rfl _
      (pinnedX_mem_rootSpan (e8Pairs_mem_S₂.1 p hp).1 1)
  · exact rootSpan_le_closure_odd_E8_y (t := e8FramePt K oddDerivE8YFrame) rfl _
      (pinnedX_mem_rootSpan (e8Pairs_mem_S₂.1 p hp).2 1)

theorem residual_witness_e8_z
    [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E8 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * e8FramePt K oddDerivE8ZFrame = e8FramePt K oddDerivE8ZFrame * c ∧
        Odd (orderOf c)} ∧ e8FramePt K oddDerivE8ZFrame ∈ ⁅P, P⁆ := by
  have hD := e8Pairs_roots (D := e8PairsZ) (by simp)
  refine oddCommWitness_of_pairs e8PairsZ hD (by rw [e8Pairs_map.2.2.1]) fun p hp => ⟨?_, ?_⟩
  · exact rootSpan_le_closure_odd_E8_z (t := e8FramePt K oddDerivE8ZFrame) rfl _
      (pinnedX_mem_rootSpan (e8Pairs_mem_S₂.2.1 p hp).1 1)
  · exact rootSpan_le_closure_odd_E8_z (t := e8FramePt K oddDerivE8ZFrame) rfl _
      (pinnedX_mem_rootSpan (e8Pairs_mem_S₂.2.1 p hp).2 1)

theorem residual_witness_e8_u
    [Finite K] [CharP K 2] :
    ∃ P : Subgroup (adjointGroup .E8 K), IsPGroup 2 P ∧
      P ≤ closure {c | c * e8FramePt K oddDerivE8UFrame = e8FramePt K oddDerivE8UFrame * c ∧
        Odd (orderOf c)} ∧ e8FramePt K oddDerivE8UFrame ∈ ⁅P, P⁆ := by
  have hD := e8Pairs_roots (D := e8PairsU) (by simp)
  refine oddCommWitness_of_pairs e8PairsU hD (by rw [e8Pairs_map.2.2.2]) fun p hp => ⟨?_, ?_⟩
  · exact rootSpan_le_closure_odd_E8_u (t := e8FramePt K oddDerivE8UFrame) rfl _
      (pinnedX_mem_rootSpan (e8Pairs_mem_S₂.2.2 p hp).1 1)
  · exact rootSpan_le_closure_odd_E8_u (t := e8FramePt K oddDerivE8UFrame) rfl _
      (pinnedX_mem_rootSpan (e8Pairs_mem_S₂.2.2 p hp).2 1)

theorem isConj_e8FramePt_inner
    [CharP K 2] :
    IsConj (e8FramePt K [highRoot .E8]) (e8FramePt K e8FrameX) ∧
      IsConj (e8FramePt K oddDerivE8YFrame) (e8FramePt K e8FrameY) ∧
      IsConj (e8FramePt K oddDerivE8ZFrame) (e8FramePt K e8FrameZ) ∧
      IsConj (e8FramePt K oddDerivE8UFrame) (e8FramePt K e8FrameU) := by
  have hr : ∀ F : List (Fin Tag.E8.rank → ℤ),
      (∀ σ ∈ F, σ ∈ [highRoot .E8] ++ oddDerivE8YFrame ++ oddDerivE8ZFrame ++ oddDerivE8UFrame) →
        ∀ σ ∈ F, IsRoot .E8 σ := fun F hF σ hσ => isRoot_of_mem_innerFrames σ (hF σ hσ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := frameProdConj_word (K := K) e8WordX (F := [highRoot .E8])
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordX_map] at h
    exact isConj_e8FramePt_of_frameProdConj h
  · have h := frameProdConj_word (K := K) e8WordY (F := oddDerivE8YFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordY_map] at h
    exact isConj_e8FramePt_of_frameProdConj h
  · have h := frameProdConj_word (K := K) e8WordZ (F := oddDerivE8ZFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordZ_map] at h
    exact isConj_e8FramePt_of_frameProdConj h
  · have h := frameProdConj_word (K := K) e8WordU (F := oddDerivE8UFrame)
      (hr _ fun σ hσ => by simp_all)
    rw [e8WordU_map] at h
    exact isConj_e8FramePt_of_frameProdConj h

theorem residualMem_e8Reps
    [Finite K] [CharP K 2]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) : ∀ x ∈ e8Reps K, Exc.ResidualMem x := by
  obtain ⟨cX, cY, cZ, cU⟩ := isConj_e8FramePt_inner (K := K)
  intro x hx
  simp only [e8Reps, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · obtain ⟨g, hg⟩ := isConj_iff.1 cX
    obtain ⟨P, hP, hPx, hxP⟩ := residual_witness_e8_x hm hK
    rw [← hg]
    exact residualMem_conj_of_witness hP hPx hxP g
  · obtain ⟨g, hg⟩ := isConj_iff.1 cY
    obtain ⟨P, hP, hPx, hxP⟩ := residual_witness_e8_y (K := K)
    rw [← hg]
    exact residualMem_conj_of_witness hP hPx hxP g
  · obtain ⟨g, hg⟩ := isConj_iff.1 cZ
    obtain ⟨P, hP, hPx, hxP⟩ := residual_witness_e8_z (K := K)
    rw [← hg]
    exact residualMem_conj_of_witness hP hPx hxP g
  · obtain ⟨g, hg⟩ := isConj_iff.1 cU
    obtain ⟨P, hP, hPx, hxP⟩ := residual_witness_e8_u (K := K)
    rw [← hg]
    exact residualMem_conj_of_witness hP hPx hxP g

end CFSG.ComponentClassification.RankTwoExceptional.E8
