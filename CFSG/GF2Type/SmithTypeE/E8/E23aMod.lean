module

public import CFSG.GF2Type.SmithTypeE.E8.ModAct
public import CFSG.GF2Type.SmithTypeE.E8.LeadFilt
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Neighbour
public import CFSG.GF2Type.SmithTypeE.E8.PairNF

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot

theorem rootOp_apply_shift {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (v : Fin e7Data.d →₀ ZMod 2) {a : Fin e7Data.d} (ha : e7Data.wt a ⬝ᵥ β = -1) :
    (e7Data.rootOp (ZMod 2) β v) (e7Shift β a) = v a := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single a' c =>
    have e : Finsupp.single a' c = c • Finsupp.single a' (1 : ZMod 2) := by simp
    rw [e, map_smul]
    rcases rootOp_single_cases (K := ZMod 2) hβ a' with ⟨h1, h2⟩ | ⟨h1, b, hb, h2⟩
    · rw [h2]
      have hne : a' ≠ a := fun h => h1 (h ▸ ha)
      simp [Finsupp.single_apply, hne]
    · rw [h2, ← wt_e7Shift hb]
      by_cases haa : a' = a
      · subst haa
        simp
      · have hne : e7Shift β a' ≠ e7Shift β a := by
          intro h
          apply haa
          have h1' := wt_e7Shift_of_dotProduct hβ h1
          have h2' := wt_e7Shift_of_dotProduct hβ ha
          rw [h] at h1'
          exact e7Data_valid.wt_injective (add_right_cancel (h1'.symm.trans h2'))
        simp [Finsupp.single_apply, hne, haa]

theorem rootOp_apply_of_not_shift {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (v : Fin e7Data.d →₀ ZMod 2) {b : Fin e7Data.d}
    (hb : ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ β = -1 → e7Shift β a ≠ b) :
    (e7Data.rootOp (ZMod 2) β v) b = 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single a' c =>
    have e : Finsupp.single a' c = c • Finsupp.single a' (1 : ZMod 2) := by simp
    rw [e, map_smul]
    rcases rootOp_single_cases (K := ZMod 2) hβ a' with ⟨h1, h2⟩ | ⟨h1, b', hb', h2⟩
    · rw [h2]; simp
    · rw [h2, ← wt_e7Shift hb']
      have hne := hb a' h1
      simp [Finsupp.single_apply, hne]

theorem rootOp_eq_zero_iff {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (v : Fin e7Data.d →₀ ZMod 2) :
    e7Data.rootOp (ZMod 2) β v = 0 ↔ ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ β = -1 → v a = 0 := by
  constructor
  · intro h a ha
    have := rootOp_apply_shift hβ v ha
    rw [h] at this
    simpa using this.symm
  · intro h
    ext b
    by_cases hb : ∃ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ β = -1 ∧ e7Shift β a = b
    · obtain ⟨a, ha, rfl⟩ := hb
      rw [rootOp_apply_shift hβ v ha, h a ha]
      rfl
    · push Not at hb
      rw [rootOp_apply_of_not_shift hβ v hb]
      rfl

set_option maxRecDepth 20000 in
theorem rep_pinnedElt_eq_self_iff {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (v : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) v = v ↔ ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ β = -1 → v a = 0 := by
  rw [e7Rep56_pinnedElt_apply hβ, one_smul, add_eq_left]
  exact rootOp_eq_zero_iff hβ v

@[expose] def zeroIdx : Finset (Fin e7Data.d) :=
  Finset.univ.filter fun a => e7Data.wt a ⬝ᵥ highRoot .E7 = 0

theorem mem_zeroIdx {a : Fin e7Data.d} : a ∈ zeroIdx ↔ e7Data.wt a ⬝ᵥ highRoot .E7 = 0 := by
  simp [zeroIdx]

theorem wt_dot_highRoot_cases : ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = -1 ∨
    e7Data.wt a ⬝ᵥ highRoot .E7 = 0 ∨ e7Data.wt a ⬝ᵥ highRoot .E7 = 1 := by
  decide +kernel

theorem card_zeroIdx : zeroIdx.card = 32 := by
  decide +kernel

@[expose] def xT : ↥(adjointGroup .E7 (ZMod 2)) := pinnedElt .E7 (highRoot .E7) 1

@[expose] def xTn : ↥(adjointGroup .E7 (ZMod 2)) := pinnedElt .E7 (-highRoot .E7) 1

@[expose] def V0 : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) (zeroIdx : Set (Fin e7Data.d))

set_option maxRecDepth 20000 in
theorem mem_V0_iff (v : Fin e7Data.d →₀ ZMod 2) :
    v ∈ V0 ↔ e7Rep56 (ZMod 2) xT v = v ∧ e7Rep56 (ZMod 2) xTn v = v := by
  have hθ := isRoot_highRoot .E7
  have hnθ : IsRoot .E7 (-highRoot .E7) := IsRoot.neg hθ
  rw [xT, xTn, rep_pinnedElt_eq_self_iff hθ, rep_pinnedElt_eq_self_iff hnθ, V0,
    Finsupp.mem_supported']
  constructor
  · intro h
    refine ⟨fun a ha => h a ?_, fun a ha => h a ?_⟩
    · rw [Finset.mem_coe, mem_zeroIdx, ha]; decide
    · rw [Finset.mem_coe, mem_zeroIdx]
      rw [dotProduct_neg] at ha
      omega
  · rintro ⟨h1, h2⟩ a ha
    rw [Finset.mem_coe, mem_zeroIdx] at ha
    rcases wt_dot_highRoot_cases a with h | h | h
    · exact h1 a h
    · exact absurd h ha
    · exact h2 a (by rw [dotProduct_neg, h])

theorem finrank_V0 : Module.finrank (ZMod 2) V0 = 32 := by
  rw [V0, LinearEquiv.finrank_eq (Finsupp.supportedEquivFinsupp (M := ZMod 2) (R := ZMod 2)
    (zeroIdx : Set (Fin e7Data.d))), Module.finrank_finsupp_self]
  simpa using card_zeroIdx

theorem reach_single (N : ℕ) : ∀ a ∈ reachIter e7Data 0 N, ∃ h : a < e7Data.d,
    ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
      e7Rep56 (ZMod 2) g (Finsupp.single (⟨0, by decide⟩ : Fin e7Data.d) 1) =
        Finsupp.single (⟨a, h⟩ : Fin e7Data.d) 1 := by
  induction N with
  | zero =>
    intro a ha
    simp only [reachIter, List.mem_singleton] at ha
    subst ha
    exact ⟨by decide, 1, by rw [map_one]; rfl⟩
  | succ N ih =>
    intro a ha
    simp only [reachIter, reachStep, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and] at ha
    rcases ha with ha | ⟨b, hb, i, rfl⟩
    · exact ih a ha
    · obtain ⟨hbd, g, hg⟩ := ih b hb
      have hlt : e7Data.weyl b i < e7Data.d :=
        (e7Data_valid.sRefl_val i ⟨b, hbd⟩) ▸ (e7Data_valid.sRefl i ⟨b, hbd⟩).2
      refine ⟨hlt, nC .E7 (ZMod 2) i * g, ?_⟩
      have e : (⟨e7Data.weyl b i, hlt⟩ : Fin e7Data.d) = e7Data_valid.sRefl i ⟨b, hbd⟩ :=
        Fin.ext (e7Data_valid.sRefl_val i ⟨b, hbd⟩).symm
      rw [e, map_mul, Module.End.mul_apply, hg, e7Rep56_nC_single]

theorem single_mem_weightVec (a : Fin e7Data.d) : Finsupp.single a (1 : ZMod 2) ∈ weightVec := by
  have h := e7_reach
  simp only [reachCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨hlt, g, hg⟩ := reach_single 30 a.1 (h a.1 a.2)
  exact ⟨g, hg⟩

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem rootSubgroup_le_centralizer_of_commute (β : Fin (Tag.rank .E7) → ℤ)
    (g : ModGL .E7 (ZMod 2)) (h : pinnedX .E7 (ZMod 2) β 1 * g = g * pinnedX .E7 (ZMod 2) β 1) :
    rootSubgroup .E7 (ZMod 2) β ≤ Subgroup.centralizer ({g} : Set (ModGL .E7 (ZMod 2))) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases zmod_two_cases c with rfl | rfl
  · rw [pinnedX_zero, one_mul, mul_one]
  · exact h

theorem pinnedX_highRoot_mem_highRootSL2 :
    pinnedX .E7 (ZMod 2) (highRoot .E7) 1 ∈ highRootSL2 .E7 (ZMod 2) :=
  rootSubgroup_highRoot_le_highRootSL2 (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨1, rfl⟩)

theorem pinnedX_neg_highRoot_mem_highRootSL2 :
    pinnedX .E7 (ZMod 2) (-highRoot .E7) 1 ∈ highRootSL2 .E7 (ZMod 2) :=
  (le_sup_right : rootSubgroup .E7 (ZMod 2) (-highRoot .E7) ≤ highRootSL2 .E7 (ZMod 2))
    (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨1, rfl⟩)

theorem highRootSL2_le_centralizer_of_commute (g : ModGL .E7 (ZMod 2))
    (h1 : pinnedX .E7 (ZMod 2) (highRoot .E7) 1 * g = g * pinnedX .E7 (ZMod 2) (highRoot .E7) 1)
    (h2 : pinnedX .E7 (ZMod 2) (-highRoot .E7) 1 * g =
      g * pinnedX .E7 (ZMod 2) (-highRoot .E7) 1) :
    highRootSL2 .E7 (ZMod 2) ≤ Subgroup.centralizer ({g} : Set (ModGL .E7 (ZMod 2))) :=
  sup_le (rootSubgroup_le_centralizer_of_commute _ g h1)
    (rootSubgroup_le_centralizer_of_commute _ g h2)

theorem coe_xT : ((xT : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) =
    pinnedX .E7 (ZMod 2) (highRoot .E7) 1 := rfl

theorem coe_xTn : ((xTn : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) =
    pinnedX .E7 (ZMod 2) (-highRoot .E7) 1 := rfl

set_option maxRecDepth 20000 in
theorem commute_xT_xTn_iff (g : ↥(adjointGroup .E7 (ZMod 2))) :
    (g * xT = xT * g ∧ g * xTn = xTn * g) ↔ g ∈ perpLevi .E7 (ZMod 2) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hle := highRootSL2_le_centralizer_of_commute (g : ModGL .E7 (ZMod 2))
      (by rw [← coe_xT]; exact congrArg Subtype.val h1.symm)
      (by rw [← coe_xTn]; exact congrArg Subtype.val h2.symm)
    rw [← CFSG.SeitzReduction.E7Pilot.centralizer_highRootSL2_subgroupOf_E7_of_charTwo,
      Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_subgroupOf.1 hy)))
  · intro hg
    have hle := CFSG.SeitzReduction.E7Pilot.perpLevi_le_centralizer_highRootSL2_E7_of_charTwo
      (K := ZMod 2) hg
    rw [Subgroup.mem_centralizer_iff] at hle
    exact ⟨(hle xT (Subgroup.mem_subgroupOf.2 pinnedX_highRoot_mem_highRootSL2)).symm,
      (hle xTn (Subgroup.mem_subgroupOf.2 pinnedX_neg_highRoot_mem_highRootSL2)).symm⟩

theorem pinnedElt_mul_self {γ : Fin (Tag.rank .E7) → ℤ} :
    pinnedElt .E7 γ (1 : ZMod 2) * pinnedElt .E7 γ (1 : ZMod 2) = 1 := by
  refine Subtype.ext (Units.ext ?_)
  have h := pinnedX_add (τ := .E7) (R := ZMod 2) γ 1 1
  rw [show (1 : ZMod 2) + 1 = 0 by decide, pinnedX_zero] at h
  have h' := congrArg Units.val h
  exact h'.symm

theorem perpLevi_le_of_forall_mem (I : Subgroup ↥(adjointGroup .E7 (ZMod 2)))
    (h : ∀ γ ∈ perpRoots .E7, pinnedElt .E7 γ (1 : ZMod 2) ∈ I) :
    perpLevi .E7 (ZMod 2) ≤ I := by
  have hsp : rootSpan .E7 (ZMod 2) (perpRoots .E7) ≤ I.map (adjointGroup .E7 (ZMod 2)).subtype := by
    refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rcases zmod_two_cases c with rfl | rfl
    · rw [pinnedX_zero]
      exact one_mem _
    · exact ⟨_, h γ hγ, rfl⟩
  intro d hd
  obtain ⟨z, hz, hzd⟩ := hsp (Subgroup.mem_subgroupOf.1 hd)
  have : z = d := Subtype.ext hzd
  rwa [this] at hz

theorem perpLevi_le_normalizer (N : Subgroup ↥(adjointGroup .E7 (ZMod 2)))
    (hnorm : ∀ γ ∈ perpRoots .E7, ∀ n ∈ N,
      pinnedElt .E7 γ (1 : ZMod 2) * n * (pinnedElt .E7 γ (1 : ZMod 2))⁻¹ ∈ N) :
    perpLevi .E7 (ZMod 2) ≤ Subgroup.normalizer (N : Set ↥(adjointGroup .E7 (ZMod 2))) := by
  refine perpLevi_le_of_forall_mem _ fun γ hγ => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact hnorm γ hγ n hn
  · intro hn
    have h2 := hnorm γ hγ _ hn
    have hinv : (pinnedElt .E7 γ (1 : ZMod 2))⁻¹ = pinnedElt .E7 γ (1 : ZMod 2) :=
      inv_eq_of_mul_eq_one_right pinnedElt_mul_self
    rw [hinv] at h2
    have e : pinnedElt .E7 γ (1 : ZMod 2) * (pinnedElt .E7 γ (1 : ZMod 2) * n *
        pinnedElt .E7 γ (1 : ZMod 2)) * pinnedElt .E7 γ (1 : ZMod 2) = n := by
      calc _ = (pinnedElt .E7 γ (1 : ZMod 2) * pinnedElt .E7 γ (1 : ZMod 2)) * n *
            (pinnedElt .E7 γ (1 : ZMod 2) * pinnedElt .E7 γ (1 : ZMod 2)) := by group
        _ = n := by rw [pinnedElt_mul_self, one_mul, mul_one]
    rwa [e] at h2

theorem eq_bot_of_normal_pgroup_perpLevi :
    ∀ N : Subgroup (EPilot.perpLevi .E7 (ZMod 2)), N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hNp
  have hs := CFSG.SeitzReduction.E7Pilot.isSimpleGroup_perpLevi_E7 (K := ZMod 2)
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hDp : IsPGroup 2 (EPilot.perpLevi .E7 (ZMod 2)) := by
      rw [h] at hNp
      exact hNp.of_equiv Subgroup.topEquiv
    have : Finite (EPilot.perpLevi .E7 (ZMod 2)) := by
      have := finite_modGL (τ := .E7) (K := ZMod 2)
      infer_instance
    have : Nontrivial (EPilot.perpLevi .E7 (ZMod 2)) := hs.toNontrivial
    have hnt := hDp.center_nontrivial
    rw [CFSG.SeitzReduction.E7Pilot.center_perpLevi_E7_eq_bot] at hnt
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt rfl

theorem eq_bot_of_normalized_pgroup (N : Subgroup ↥(adjointGroup .E7 (ZMod 2)))
    (hND : N ≤ perpLevi .E7 (ZMod 2))
    (hnorm : ∀ γ ∈ perpRoots .E7, ∀ n ∈ N,
      pinnedElt .E7 γ (1 : ZMod 2) * n * (pinnedElt .E7 γ (1 : ZMod 2))⁻¹ ∈ N)
    (hp : IsPGroup 2 N) : N = ⊥ := by
  have hle := perpLevi_le_normalizer N hnorm
  have hN : (N.subgroupOf (perpLevi .E7 (ZMod 2))).Normal := by
    refine ⟨fun n hn d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hle d.2) (n : ↥(adjointGroup .E7 (ZMod 2)))).1 hn
    exact this
  have hp' : IsPGroup 2 (N.subgroupOf (perpLevi .E7 (ZMod 2))) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hND).symm
  have hbot := eq_bot_of_normal_pgroup_perpLevi _ hN hp'
  refine eq_bot_iff.2 fun n hn => ?_
  have hn' : (⟨n, hND hn⟩ : ↥(perpLevi .E7 (ZMod 2))) ∈ N.subgroupOf (perpLevi .E7 (ZMod 2)) :=
    hn
  rw [hbot, Subgroup.mem_bot] at hn'
  exact congrArg Subtype.val hn'

theorem rep_mem_V0 {d : ↥(adjointGroup .E7 (ZMod 2))} (hd : d ∈ perpLevi .E7 (ZMod 2))
    {v : Fin e7Data.d →₀ ZMod 2} (hv : v ∈ V0) : e7Rep56 (ZMod 2) d v ∈ V0 := by
  obtain ⟨h1, h2⟩ := (commute_xT_xTn_iff d).2 hd
  rw [mem_V0_iff] at hv ⊢
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [← rep_mul_apply, ← h1, rep_mul_apply, hv1]
  · rw [← rep_mul_apply, ← h2, rep_mul_apply, hv2]

@[expose] def fixV0 : Subgroup ↥(perpLevi .E7 (ZMod 2)) where
  carrier := {d | ∀ v ∈ V0, e7Rep56 (ZMod 2) (d : ↥(adjointGroup .E7 (ZMod 2))) v = v}
  one_mem' := fun v _ => by
    show e7Rep56 (ZMod 2) (1 : ↥(adjointGroup .E7 (ZMod 2))) v = v
    exact rep_one_apply v
  mul_mem' := fun {a b} ha hb v hv => by
    show e7Rep56 (ZMod 2) ((a : ↥(adjointGroup .E7 (ZMod 2))) * (b : ↥(adjointGroup .E7 (ZMod 2)))) v
      = v
    rw [rep_mul_apply, hb v hv, ha v hv]
  inv_mem' := fun {a} ha v hv => by
    have hw : e7Rep56 (ZMod 2) ((a⁻¹ : ↥(perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))) v
        ∈ V0 := rep_mem_V0 (a⁻¹).2 hv
    have h1 := ha _ hw
    show e7Rep56 (ZMod 2) ((a : ↥(adjointGroup .E7 (ZMod 2)))⁻¹) v = v
    have h2 : e7Rep56 (ZMod 2) (a : ↥(adjointGroup .E7 (ZMod 2))) (e7Rep56 (ZMod 2)
        ((a : ↥(adjointGroup .E7 (ZMod 2)))⁻¹) v) = v := by
      rw [← rep_mul_apply, mul_inv_cancel, rep_one_apply]
    exact h1.symm.trans h2

theorem fixV0_normal : fixV0.Normal := ⟨fun n hn g v hv => by
  have hw : e7Rep56 (ZMod 2) ((g⁻¹ : ↥(perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))) v
      ∈ V0 := rep_mem_V0 (g⁻¹).2 hv
  have h1 := hn _ hw
  show e7Rep56 (ZMod 2) ((g : ↥(adjointGroup .E7 (ZMod 2))) * (n : ↥(adjointGroup .E7 (ZMod 2))) *
    (g : ↥(adjointGroup .E7 (ZMod 2)))⁻¹) v = v
  rw [rep_mul_apply, rep_mul_apply]
  have h1' : e7Rep56 (ZMod 2) (n : ↥(adjointGroup .E7 (ZMod 2))) (e7Rep56 (ZMod 2)
      ((g : ↥(adjointGroup .E7 (ZMod 2)))⁻¹) v) = e7Rep56 (ZMod 2)
      ((g : ↥(adjointGroup .E7 (ZMod 2)))⁻¹) v := h1
  rw [h1', ← rep_mul_apply, mul_inv_cancel, rep_one_apply]⟩

abbrev e7n2 : Fin (Tag.rank .E7) := ⟨1, by decide⟩

theorem eq_one_of_fix_V0 {g : ↥(adjointGroup .E7 (ZMod 2))} (hg : g ∈ perpLevi .E7 (ZMod 2))
    (hfix : ∀ v ∈ V0, e7Rep56 (ZMod 2) g v = v) : g = 1 := by
  haveI := CFSG.SeitzReduction.E7Pilot.isSimpleGroup_perpLevi_E7 (K := ZMod 2)
  haveI := fixV0_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal fixV0 with h | h
  · have hm : (⟨g, hg⟩ : ↥(perpLevi .E7 (ZMod 2))) ∈ fixV0 := hfix
    rw [h, Subgroup.mem_bot] at hm
    exact congrArg Subtype.val hm
  · exfalso
    have hj : (Pi.single e7n2 1 : Fin (Tag.rank .E7) → ℤ) ∈ perpRoots .E7 :=
      single_mem_perpRoots (by decide)
    have hd : (⟨pinnedElt .E7 (Pi.single e7n2 1) (1 : ZMod 2),
        pinnedElt_mem_perpLevi hj 1⟩ : ↥(perpLevi .E7 (ZMod 2))) ∈ fixV0 := by
      rw [h]; trivial
    obtain ⟨a, ha1, ha0⟩ : ∃ a : Fin e7Data.d,
        e7Data.wt a ⬝ᵥ (Pi.single e7n2 1 : Fin (Tag.rank .E7) → ℤ) = -1 ∧
        e7Data.wt a ⬝ᵥ highRoot .E7 = 0 := by decide +kernel
    have hmem : Finsupp.single a (1 : ZMod 2) ∈ V0 :=
      Finsupp.single_mem_supported (ZMod 2) _ (by rw [Finset.mem_coe, mem_zeroIdx]; exact ha0)
    have h1 : e7Rep56 (ZMod 2) (pinnedElt .E7 (Pi.single e7n2 1) (1 : ZMod 2))
        (Finsupp.single a 1) = Finsupp.single a 1 := hd _ hmem
    rw [rep_pinnedElt_eq_self_iff hj.1] at h1
    have := h1 a ha1
    simp at this

theorem nWC_mul_pinnedElt_mul_inv (w : WeylGroup .E7) {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : IsRoot .E7 β) :
    nWC .E7 (ZMod 2) w * pinnedElt .E7 β (1 : ZMod 2) * (nWC .E7 (ZMod 2) w)⁻¹ =
      pinnedElt .E7 (w • β) (1 : ZMod 2) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv (ZMod 2) w hβ
  have hε1 : ε = 1 := by
    have key : ∀ e : ZMod 2, e * e = 1 → e = 1 := by decide
    exact key ε hε
  refine Subtype.ext ?_
  have h1 := h 1
  rw [hε1, one_mul] at h1
  exact h1

theorem isRootInvol_pinnedElt {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    IsRootInvol (pinnedElt .E7 γ (1 : ZMod 2)) := by
  obtain ⟨w, rfl⟩ := exists_smul_highRoot_eq (τ := .E7) (Or.inr (Or.inl rfl)) hγ
  exact isConj_iff.2 ⟨nWC .E7 (ZMod 2) w, nWC_mul_xtheta_mul_inv w⟩

theorem orderOf_ne_three_of_pos {β γ : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (hβp : 0 < height β) (hγ : IsRoot .E7 γ) (hγp : 0 < height γ) :
    orderOf (pinnedElt .E7 β (1 : ZMod 2) * pinnedElt .E7 γ (1 : ZMod 2)) ≠ 3 := by
  intro h3
  have hmem : ((pinnedElt .E7 β (1 : ZMod 2) * pinnedElt .E7 γ (1 : ZMod 2) :
      ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) :=
    mul_mem (CFSG.GF2Type.SmithTypeE.E8.Lead.rootSubgroup_le_posUnipotent ⟨hβ, hβp⟩
        (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨1, rfl⟩))
      (CFSG.GF2Type.SmithTypeE.E8.Lead.rootSubgroup_le_posUnipotent ⟨hγ, hγp⟩
        (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hp := CFSG.SignalizerFunctorTheorem.NonLocalExc.isPGroup_posUnipotent
    (τ := .E7) (K := ZMod 2) 2
  obtain ⟨k, hk⟩ := hp ⟨_, hmem⟩
  have hk' : (pinnedElt .E7 β (1 : ZMod 2) * pinnedElt .E7 γ (1 : ZMod 2)) ^ 2 ^ k = 1 := by
    refine Subtype.ext ?_
    have := congrArg Subtype.val hk
    simpa using this
  have hd := orderOf_dvd_of_pow_eq_one hk'
  rw [h3] at hd
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hd
  omega

theorem exists_conj_opposite {r r' : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    (hr' : IsRootInvol r') (h3 : orderOf (r * r') = 3) :
    ∃ g : ↥(adjointGroup .E7 (ZMod 2)), g * r * g⁻¹ = xT ∧ g * r' * g⁻¹ = xTn := by
  obtain ⟨g₀, β, hβ, hrg, hr'g⟩ := pair_normal_form_involutions hr hr'
  have hβ' : β = -highRoot .E7 := by
    by_contra hne
    obtain ⟨v, hv1, hv2⟩ := exists_height_smul_highRoot_pos hβ hne
    refine orderOf_ne_three_of_pos (IsRoot.smul (isRoot_highRoot .E7) v) hv1
      (IsRoot.smul hβ v) hv2 ?_
    have e : pinnedElt .E7 (v • highRoot .E7) (1 : ZMod 2) * pinnedElt .E7 (v • β) (1 : ZMod 2) =
        MulAut.conj (nWC .E7 (ZMod 2) v * g₀⁻¹) (r * r') := by
      rw [MulAut.conj_apply, hrg, hr'g, ← nWC_mul_xtheta_mul_inv v,
        ← nWC_mul_pinnedElt_mul_inv v hβ]
      group
    rw [e, MulEquiv.orderOf_eq]
    exact h3
  subst hβ'
  refine ⟨g₀⁻¹, ?_, ?_⟩
  · rw [hrg]
    show _ = pinnedElt .E7 (highRoot .E7) (1 : ZMod 2)
    group
  · rw [hr'g]
    show _ = pinnedElt .E7 (-highRoot .E7) (1 : ZMod 2)
    group

end CFSG.GF2Type.SmithTypeE.E8
