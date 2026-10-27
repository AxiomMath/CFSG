module

public import CFSG.GF2Type.SmithTypeE.E8.FactsGrp
public import CFSG.GF2Type.SmithTypeE.E8.ModW0
public import CFSG.GF2Type.SmithTypeE.E8.PairNF

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8.F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot


theorem tw_dot_self {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    MinData.toWeight γ ⬝ᵥ γ = 2 :=
  forall_root_of_listed (P := fun γ => MinData.toWeight γ ⬝ᵥ γ = 2) tw_dot_self_listed hγ

theorem two_wt_ne {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (a : Fin e7Data.d) :
    e7Data.wt a + e7Data.wt a + MinData.toWeight γ ≠ 0 :=
  forall_root_of_listed (P := fun γ => ∀ a : Fin e7Data.d,
    e7Data.wt a + e7Data.wt a + MinData.toWeight γ ≠ 0) two_wt_ne_listed hγ a

theorem siegel_irr {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h : e8fTh ⬝ᵥ γ = 0)
    (a : Fin e7Data.d) : e7Data.wt a + e7Data.wt a + MinData.toWeight γ ≠ e8fTh :=
  forall_root_of_listed (P := fun γ => e8fTh ⬝ᵥ γ = 0 → ∀ a : Fin e7Data.d,
    e7Data.wt a + e7Data.wt a + MinData.toWeight γ ≠ e8fTh) siegel_irr_listed hγ h a

theorem triv {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h : 1 ≤ e8fTh ⬝ᵥ γ)
    (a : Fin e7Data.d) (ha : e7Data.wt a ⬝ᵥ highRoot .E7 = 1) : e7Data.wt a ⬝ᵥ γ ≠ -1 :=
  forall_root_of_listed (P := fun γ => 1 ≤ e8fTh ⬝ᵥ γ → ∀ a : Fin e7Data.d,
    e7Data.wt a ⬝ᵥ highRoot .E7 = 1 → e7Data.wt a ⬝ᵥ γ ≠ -1) triv_listed hγ h a ha

theorem tw_dot_th {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    MinData.toWeight γ ⬝ᵥ highRoot .E7 = e8fTh ⬝ᵥ γ :=
  forall_root_of_listed (P := fun γ => MinData.toWeight γ ⬝ᵥ highRoot .E7 = e8fTh ⬝ᵥ γ)
    tw_dot_th_listed hγ

theorem th_cases {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (hpos : 0 < height γ) :
    e8fTh ⬝ᵥ γ = 0 ∨ e8fTh ⬝ᵥ γ = 1 ∨ e8fTh ⬝ᵥ γ = 2 :=
  forall_root_of_listed (P := fun γ => 0 < height γ →
    e8fTh ⬝ᵥ γ = 0 ∨ e8fTh ⬝ᵥ γ = 1 ∨ e8fTh ⬝ᵥ γ = 2) th_cases_listed hγ hpos

theorem unshift_exists : ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 →
    ∃ a' : Fin e7Data.d, e7Data.wt a' = e7Data.wt a - e8fTh := by decide +kernel

theorem grade_zero : e8fGrade ⟨0, by decide⟩ = 3 := by decide +kernel

theorem coord_rho_sub {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (v : Fin e7Data.d →₀ ZMod 2) (b : Fin e7Data.d) :
    (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v - v) b =
      ∑ a : Fin e7Data.d, if (e7Data.wt a ⬝ᵥ β = -1 ∧
        e7Data.wt b = e7Data.wt a + MinData.toWeight β) then v a else 0 := by
  rw [e7Rep56_pinnedElt_apply hβ, one_smul, add_sub_cancel_left, rootOp_apply_eq_sum,
    Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.smul_apply, rootOp_single_coord hβ]
  split_ifs <;> simp

theorem coord_rho {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (v : Fin e7Data.d →₀ ZMod 2) (b : Fin e7Data.d) :
    (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v) b =
      v b + ∑ a : Fin e7Data.d, if (e7Data.wt a ⬝ᵥ β = -1 ∧
        e7Data.wt b = e7Data.wt a + MinData.toWeight β) then v a else 0 := by
  have h : (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v) b - v b =
      ∑ a : Fin e7Data.d, if (e7Data.wt a ⬝ᵥ β = -1 ∧
        e7Data.wt b = e7Data.wt a + MinData.toWeight β) then v a else 0 :=
    coord_rho_sub hβ v b
  linear_combination h

theorem wt_dot_shift {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) {a b : Fin e7Data.d}
    (ha : e7Data.wt a ⬝ᵥ β = -1) (hb : e7Data.wt b = e7Data.wt a + MinData.toWeight β) :
    e7Data.wt b ⬝ᵥ β = 1 := by
  rw [hb, add_dotProduct, ha]
  linarith [tw_dot_self hβ]

theorem exists_shift {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) {a : Fin e7Data.d}
    (ha : e7Data.wt a ⬝ᵥ β = -1) :
    ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight β :=
  CFSG.GF2Type.SmithTypeE.E8.exists_wt_eq_of_dotProduct hβ ha

theorem coord_rho_sub_ne_zero {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (v : Fin e7Data.d →₀ ZMod 2) {b : Fin e7Data.d}
    (hb : (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v - v) b ≠ 0) :
    e7Data.wt b ⬝ᵥ β = 1 := by
  rw [coord_rho_sub hβ v b] at hb
  by_contra hne
  refine hb (Finset.sum_eq_zero fun a _ => ?_)
  by_cases h : e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt b = e7Data.wt a + MinData.toWeight β
  · exact absurd (wt_dot_shift hβ h.1 h.2) hne
  · rw [if_neg h]

theorem mem_weightVec_iff {w : Fin e7Data.d →₀ ZMod 2} :
    w ∈ weightVec ↔ ∃ g : ↥(adjointGroup .E7 (ZMod 2)), e7Rep56 (ZMod 2) g e7Y56 = w := Iff.rfl

theorem e7Y56_mem_weightVec : (e7Y56 : Fin e7Data.d →₀ ZMod 2) ∈ weightVec := by
  refine mem_weightVec_iff.2 ⟨1, ?_⟩
  rw [map_one, Module.End.one_apply]

theorem rep_mem_weightVec {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec)
    (g : ↥(adjointGroup .E7 (ZMod 2))) : e7Rep56 (ZMod 2) g w ∈ weightVec := by
  obtain ⟨h, rfl⟩ := mem_weightVec_iff.1 hw
  refine mem_weightVec_iff.2 ⟨g * h, ?_⟩
  rw [map_mul, Module.End.mul_apply]

private theorem rep_inv_mul (g : ↥(adjointGroup .E7 (ZMod 2))) (w : Fin e7Data.d →₀ ZMod 2) :
    e7Rep56 (ZMod 2) g⁻¹ (e7Rep56 (ZMod 2) g w) = w := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rep_mem_weightVec_iff (g : ↥(adjointGroup .E7 (ZMod 2))) {w : Fin e7Data.d →₀ ZMod 2} :
    e7Rep56 (ZMod 2) g w ∈ weightVec ↔ w ∈ weightVec := by
  refine ⟨fun hw => ?_, fun hw => rep_mem_weightVec hw g⟩
  have h := rep_mem_weightVec hw g⁻¹
  rwa [rep_inv_mul] at h

private theorem reach_single_aux : ∀ N : ℕ, ∀ a ∈ reachIter e7Data 0 N, ∃ h : a < e7Data.d,
    (Finsupp.single (⟨a, h⟩ : Fin e7Data.d) (1 : ZMod 2) : Fin e7Data.d →₀ ZMod 2) ∈ weightVec := by
  intro N
  induction N with
  | zero =>
    intro a ha
    simp only [reachIter, List.mem_singleton] at ha
    subst ha
    exact ⟨by decide, e7Y56_mem_weightVec⟩
  | succ N ih =>
    intro a ha
    simp only [reachIter, reachStep, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
      List.mem_map, List.mem_finRange, true_and] at ha
    rcases ha with ha | ⟨b, hb, i, rfl⟩
    · exact ih a ha
    · obtain ⟨hbd, hbs⟩ := ih b hb
      have hval : e7Data.weyl b i = (e7Data_valid.sRefl i ⟨b, hbd⟩).val :=
        (e7Data_valid.sRefl_val i ⟨b, hbd⟩).symm
      have hlt : e7Data.weyl b i < e7Data.d := by
        rw [hval]
        exact (e7Data_valid.sRefl i ⟨b, hbd⟩).2
      refine ⟨hlt, ?_⟩
      have hm := rep_mem_weightVec hbs (nC .E7 (ZMod 2) i)
      rw [e7Rep56_nC_single] at hm
      have e : (⟨e7Data.weyl b i, hlt⟩ : Fin e7Data.d) = e7Data_valid.sRefl i ⟨b, hbd⟩ :=
        Fin.ext hval
      rw [e]
      exact hm

theorem single_mem_weightVec (a : Fin e7Data.d) :
    (Finsupp.single a 1 : Fin e7Data.d →₀ ZMod 2) ∈ weightVec := by
  have hN := e7_reach
  simp only [reachCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hN
  obtain ⟨_, hm⟩ := reach_single_aux 30 a (hN a a.2)
  exact hm

private theorem reach_sound_aux (J : List (Fin (Tag.rank .E7))) (a₀ : Fin e7Data.d) (N : ℕ) :
    ∀ a ∈ e8fReach J a₀ N, ∃ h : a < e7Data.d, ∃ l : List (Fin (Tag.rank .E7)),
      (∀ i ∈ l, i ∈ J) ∧ l.foldr (fun i c => e7Data_valid.sRefl i c) a₀ = ⟨a, h⟩ := by
  induction N with
  | zero =>
    intro a ha
    simp only [e8fReach, List.mem_singleton] at ha
    subst ha
    exact ⟨a₀.2, [], by simp, rfl⟩
  | succ N ih =>
    intro a ha
    simp only [e8fReach, e8fStep, List.mem_eraseDups, List.mem_append, List.mem_flatMap,
      List.mem_map] at ha
    rcases ha with ha | ⟨b, hb, i, hi, rfl⟩
    · exact ih a ha
    · obtain ⟨hbd, l, hlJ, hl⟩ := ih b hb
      have hval : e7Data.weyl b i = (e7Data_valid.sRefl i ⟨b, hbd⟩).val :=
        (e7Data_valid.sRefl_val i ⟨b, hbd⟩).symm
      have hlt : e7Data.weyl b i < e7Data.d := by
        rw [hval]
        exact (e7Data_valid.sRefl i ⟨b, hbd⟩).2
      refine ⟨hlt, i :: l, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hi
        · exact hlJ x hx
      · rw [List.foldr_cons, hl]
        exact Fin.ext hval.symm

theorem reach_sound (J : List (Fin (Tag.rank .E7))) (a₀ : Fin e7Data.d) (N : ℕ)
    (b : Fin e7Data.d) (hb : (b : ℕ) ∈ e8fReach J a₀ N) :
    ∃ l : List (Fin (Tag.rank .E7)), (∀ i ∈ l, i ∈ J) ∧
      l.foldr (fun i c => e7Data_valid.sRefl i c) a₀ = b := by
  obtain ⟨_, l, hl, hfold⟩ := reach_sound_aux J a₀ N b hb
  exact ⟨l, hl, hfold⟩

theorem sum_single_mem_weightVec (T : Finset (Fin e7Data.d)) (hne : T.Nonempty)
    (hT : ∀ μ ∈ T, ∀ l ∈ T, μ ≠ l → ∃ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β ∧
      e7Data.wt l = e7Data.wt μ + MinData.toWeight β ∧ e7Data.wt μ ⬝ᵥ β = -1 ∧
      ∀ ν ∈ T, ν ≠ μ → ν ≠ l → e7Data.wt ν ⬝ᵥ β ≠ -1) :
    (∑ b ∈ T, (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2)) ∈ weightVec := by
  revert hne hT
  induction T using Finset.strongInduction with
  | H T ih =>
    intro hne hT
    obtain ⟨l, hl⟩ := hne
    rcases (T.erase l).eq_empty_or_nonempty with h0 | h0
    · rw [← Finset.sum_erase_add T _ hl, h0, Finset.sum_empty, zero_add]
      exact single_mem_weightVec l
    · have h0' := h0
      obtain ⟨μ, hμ⟩ := h0'
      have hμl : μ ≠ l := (Finset.mem_erase.1 hμ).1
      have hμT : μ ∈ T := (Finset.mem_erase.1 hμ).2
      obtain ⟨β, hβ, hwl, hwμ, hfix⟩ := hT μ hμT l hl hμl
      have hT' : ∀ μ' ∈ T.erase l, ∀ l' ∈ T.erase l, μ' ≠ l' → ∃ β' : Fin (Tag.rank .E7) → ℤ,
          IsRoot .E7 β' ∧ e7Data.wt l' = e7Data.wt μ' + MinData.toWeight β' ∧
            e7Data.wt μ' ⬝ᵥ β' = -1 ∧
            ∀ ν ∈ T.erase l, ν ≠ μ' → ν ≠ l' → e7Data.wt ν ⬝ᵥ β' ≠ -1 := by
        intro μ' hμ' l' hl' hne'
        obtain ⟨β', hβ', h1, h2, h3⟩ :=
          hT μ' (Finset.mem_of_mem_erase hμ') l' (Finset.mem_of_mem_erase hl') hne'
        exact ⟨β', hβ', h1, h2, fun ν hν => h3 ν (Finset.mem_of_mem_erase hν)⟩
      have hS : (∑ b ∈ T.erase l, (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2)) ∈ weightVec :=
        ih (T.erase l) (Finset.erase_ssubset hl) h0 hT'
      have key : ∀ b ∈ T.erase l,
          e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) =
            (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) +
              if b = μ then (Finsupp.single l 1 : Fin e7Data.d →₀ ZMod 2) else 0 := by
        intro b hb
        obtain ⟨hbl, hbT⟩ := Finset.mem_erase.1 hb
        rw [e7Rep56_pinnedElt_single (K := ZMod 2) hβ b]
        by_cases hbμ : b = μ
        · rw [hbμ, if_pos hwμ, if_pos (rfl : μ = μ), wt_e7Shift hwl]
        · rw [if_neg (hfix b hbT hbμ hbl), if_neg hbμ, add_zero]
      have hμmem : μ ∈ T.erase l := Finset.mem_erase.2 ⟨hμl, hμT⟩
      have hsum : e7Rep56 (ZMod 2) (pinnedElt .E7 β 1)
          (∑ b ∈ T.erase l, (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2)) =
            ∑ b ∈ T, (Finsupp.single b 1 : Fin e7Data.d →₀ ZMod 2) := by
        rw [map_sum, Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_ite_eq',
          if_pos hμmem, ← Finset.sum_erase_add T _ hl]
      rw [← hsum]
      exact rep_mem_weightVec hS (pinnedElt .E7 β 1)

theorem single_e7Y56 : (e7Y56 : Fin e7Data.d →₀ ZMod 2) = Finsupp.single ⟨0, by decide⟩ 1 := rfl

theorem wt_ne_zero_core {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) : w ≠ 0 := by
  obtain ⟨g, rfl⟩ := hw
  intro h
  have h2 := congrArg (e7Rep56 (ZMod 2) g⁻¹) h
  rw [rep_inv_apply', map_zero] at h2
  exact e7Y56_ne_zero h2

theorem single_mem_W0 {b : Fin e7Data.d} (hb : 0 < wgrade b) :
    (Finsupp.single b (1 : ZMod 2) : Fin e7Data.d →₀ ZMod 2) ∈ W0 := by
  rw [mem_W0]
  intro b' hb'
  have hne : b' ≠ b := fun h => by subst h; omega
  simp [Finsupp.single_apply, hne.symm]

theorem exists_adj_core {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) :
    ∃ w' ∈ weightVec, w' ∈ collSpace w ∧ w' ≠ w := by
  obtain ⟨g, rfl⟩ := hw
  obtain ⟨b, hb⟩ := exists_grade_one
  have hb' : 0 < wgrade b := by
    change 0 < e8fGrade b
    omega
  refine ⟨e7Rep56 (ZMod 2) g (Finsupp.single b 1), rep_mem_weightVec (single_mem_weightVec b) g,
    ?_, ?_⟩
  · rw [mem_collSpace_iff, rep_inv_apply']
    exact single_mem_W0 hb'
  · intro h
    have h2 := congrArg (e7Rep56 (ZMod 2) g⁻¹) h
    rw [rep_inv_apply', rep_inv_apply', single_e7Y56] at h2
    have h3 := Finsupp.single_left_inj (one_ne_zero (α := ZMod 2)) |>.1 h2
    subst h3
    have : e8fGrade (⟨0, by decide⟩ : Fin e7Data.d) = 3 := grade_zero
    omega

theorem zero_shift_grade {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (h : e7Data.wt 0 ⬝ᵥ β = -1) {b : Fin e7Data.d}
    (hb : e7Data.wt b = e7Data.wt 0 + MinData.toWeight β) : 0 < e8fGrade b :=
  forall_root_of_listed (P := fun β => e7Data.wt 0 ⬝ᵥ β = -1 → ∀ b : Fin e7Data.d,
    e7Data.wt b = e7Data.wt 0 + MinData.toWeight β → 0 < e8fGrade b)
    zero_shift_grade_listed hβ h b hb

theorem rho_pinned_e7Y56_mem_W0 {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) e7Y56 ∈ W0 := by
  rw [single_e7Y56, e7Rep56_pinnedElt_single hβ]
  have h0 : (Finsupp.single (⟨0, by decide⟩ : Fin e7Data.d) (1 : ZMod 2)) ∈ W0 :=
    single_mem_W0 (by change 0 < e8fGrade _; rw [grade_zero]; omega)
  by_cases h : e7Data.wt 0 ⬝ᵥ β = -1
  · rw [if_pos h]
    refine add_mem h0 (single_mem_W0 ?_)
    obtain ⟨b, hb⟩ := exists_shift hβ (a := ⟨0, by decide⟩) h
    rw [wt_e7Shift hb]
    exact zero_shift_grade hβ h hb
  · rw [if_neg h, add_zero]
    exact h0

theorem tv_wt_core {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) :
    e7Rep56 (ZMod 2) r w ∈ weightVec ∧ e7Rep56 (ZMod 2) r w ∈ collSpace w := by
  obtain ⟨g₁, hg₁⟩ := hw
  obtain ⟨g, β, hβ, hwg, hrg⟩ := pair_normal_form_weight_involution ⟨g₁, hg₁.symm⟩ hr
  subst hwg
  subst hrg
  have e : e7Rep56 (ZMod 2) (g * pinnedElt .E7 β (1 : ZMod 2) * g⁻¹)
      (e7Rep56 (ZMod 2) g e7Y56) =
      e7Rep56 (ZMod 2) g (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) e7Y56) := by
    rw [rep_mul_apply, rep_mul_apply, rep_inv_apply']
  rw [e]
  refine ⟨⟨g * pinnedElt .E7 β (1 : ZMod 2),
    rep_mul_apply g (pinnedElt .E7 β (1 : ZMod 2)) e7Y56⟩, ?_⟩
  rw [mem_collSpace_iff, rep_inv_apply']
  exact rho_pinned_e7Y56_mem_W0 hβ

end CFSG.GF2Type.SmithTypeE.E8.F
