module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import Certificates.Certificate13614

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T Timmesfeld.Co1Leaf

set_option linter.unusedSectionVars false

section WeylTest

open Native


theorem e6Om3_getD (i : Fin Tag.E6.rank) :
    e6Om3.getD i.val 0 = CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3 i := by
  fin_cases i <;> rfl

theorem e6WeylTest_imgTuple (w : WeylGroup .E6) : e6WeylTest (imgTuple w) = true := by
  rw [e6WeylTest, List.all_eq_true]
  intro j _
  rw [beq_iff_eq]
  have h1 : ∀ i : Fin Tag.E6.rank,
      e6Om3.getD i.val 0 * ((imgTuple w).getD i.val []).getD j.val 0 =
        CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3 i *
          (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j := by
    intro i
    rw [e6Om3_getD, getD_imgTuple w i, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have h2 : CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3 =
      ∑ i, CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3 i •
        (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    conv_lhs => rw [← Finset.univ_sum_single CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hsum : ((List.finRange Tag.E6.rank).map fun i =>
      e6Om3.getD i.val 0 * ((imgTuple w).getD i.val []).getD j.val 0).sum =
        (w • CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Omega3) j := by
    rw [← Fin.sum_univ_def, Finset.sum_congr rfl fun i _ => h1 i]
    conv_rhs => rw [h2, Finset.smul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm, Pi.smul_apply, smul_eq_mul]
  rw [hsum, e6Om3_getD]
  exact Int.emod_eq_zero_of_dvd
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.three_dvd_smul_e6Omega3_sub w j)

variable {K : Type} [Field K] {ω : Kˣ} {kb : List (List ℕ)}

theorem famData_of_famOKW (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = Tag.E6.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3)
    (h : famOKW (gramL .E6) (rootsN .E6) (simpleL .E6)
      ((simpleL .E6).map fun e => formB (gramL .E6) e e) kb = true) :
    (familyKernel (famV (τ := .E6) ω kb) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := .E6) ω kb), w = 1) ∨
      ∃ α, IsRoot .E6 α ∧ familyKernel (famV (τ := .E6) ω kb) = {α, -α} ∧
        ∀ w ∈ familyStabilizer (famV (τ := .E6) ω kb), w = 1 ∨ w = rootReflection α := by
  have hT := fun {w : WeylGroup .E6} (hw : w ∈ familyStabilizer (famV (τ := .E6) ω kb)) =>
    List.mem_filter.2 ⟨imgTuple_mem_tuplesL hω hlen hlt hw, e6WeylTest_imgTuple w⟩
  have hker : ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ familyKernel (famV (τ := .E6) ω kb) ↔
      List.ofFn γ ∈ kerRootsL (fibRoots (rootsN .E6) kb) (kb.map fun _ => 0) ∧
        IsRoot .E6 γ := by
    intro γ
    rw [mem_familyKernel_famV hω hlen hlt, kerRootsL, List.mem_map]
    constructor
    · rintro ⟨hγ, hf⟩
      refine ⟨⟨(List.ofFn γ, iform γ γ, fibL kb (List.ofFn γ)),
        List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩, hγ⟩
      · rw [fibRoots, List.mem_map]
        exact ⟨_, mem_rootsN hγ, rfl⟩
      · simpa using hf
    · rintro ⟨⟨p, hp, hpγ⟩, hγ⟩
      rw [List.mem_filter, fibRoots, List.mem_map] at hp
      obtain ⟨⟨q, hq, rfl⟩, hz⟩ := hp
      refine ⟨hγ, ?_⟩
      simp only at hpγ hz
      rw [← hpγ]
      simpa using hz
  have hkerRoot : ∀ x ∈ kerRootsL (fibRoots (rootsN .E6) kb) (kb.map fun _ => 0),
      ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot .E6 γ ∧ x = List.ofFn γ := by
    intro x hx
    rw [kerRootsL, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [List.mem_filter, fibRoots, List.mem_map] at hp
    obtain ⟨⟨q, hq, rfl⟩, -⟩ := hp
    obtain ⟨γ, hγ, rfl⟩ := isRoot_of_mem_rootsN hq
    exact ⟨γ, hγ, rfl⟩
  unfold famOKW at h
  simp only at h
  split at h
  · rename_i hK
    left
    refine ⟨Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_, fun w hw => ?_⟩
    · have := ((hker γ).1 hγ).1
      rw [hK] at this
      exact List.not_mem_nil this
    · rw [List.all_eq_true] at h
      have h1 := h _ (hT hw)
      rw [beq_iff_eq] at h1
      exact eq_of_imgTuple_eq (h1.trans imgTuple_one.symm)
  · rename_i α' β' hK
    rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨hβ, hall⟩ := h
    obtain ⟨α, hα, rfl⟩ := hkerRoot α' (by rw [hK]; exact List.mem_cons_self)
    have hβ' : β' = List.ofFn (-α) := by
      rw [hβ, List.map_ofFn]
      rfl
    right
    refine ⟨α, hα, Set.ext fun γ => ?_, fun w hw => ?_⟩
    · rw [hker γ, hK, Set.mem_insert_iff, Set.mem_singleton_iff, List.mem_cons, List.mem_cons,
        hβ']
      constructor
      · rintro ⟨h1 | h1 | h1, -⟩
        · exact Or.inl (List.ofFn_injective h1)
        · exact Or.inr (List.ofFn_injective h1)
        · exact absurd h1 List.not_mem_nil
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, hα⟩
        · exact ⟨Or.inr (Or.inl rfl), IsRoot.neg hα⟩
    · have h1 := hall _ (hT hw)
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h1
      rcases h1 with h1 | h1
      · exact Or.inl (eq_of_imgTuple_eq (h1.trans imgTuple_one.symm))
      · exact Or.inr (eq_of_imgTuple_eq (h1.trans (imgTuple_rootReflection hα).symm))
  · exact absurd h (by simp)

theorem famData0_of_famOK0W (hω : orderOf ω = 3) (hlen : ∀ b ∈ kb, b.length = Tag.E6.rank)
    (hlt : ∀ b ∈ kb, ∀ x ∈ b, x < 3)
    (h : famOK0W (gramL .E6) (rootsN .E6) (simpleL .E6)
      ((simpleL .E6).map fun e => formB (gramL .E6) e e) kb = true) :
    familyKernel (famV (τ := .E6) ω kb) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := .E6) ω kb), w = 1 := by
  unfold famOK0W at h
  simp only [Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hK, hall⟩ := h
  refine ⟨Set.eq_empty_iff_forall_notMem.2 fun γ hγ => ?_, fun w hw => ?_⟩
  · rw [mem_familyKernel_famV hω hlen hlt] at hγ
    have hmem : List.ofFn γ ∈ kerRootsL (fibRoots (rootsN .E6) kb) (kb.map fun _ => 0) := by
      rw [kerRootsL, List.mem_map]
      refine ⟨(List.ofFn γ, iform γ γ, fibL kb (List.ofFn γ)), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
      · rw [fibRoots, List.mem_map]
        exact ⟨_, mem_rootsN hγ.1, rfl⟩
      · simpa using hγ.2
    rw [hK] at hmem
    exact List.not_mem_nil hmem
  · exact eq_of_imgTuple_eq ((hall _ (List.mem_filter.2 ⟨imgTuple_mem_tuplesL hω hlen hlt hw,
      e6WeylTest_imgTuple w⟩)).trans imgTuple_one.symm)

end WeylTest

section Inner


variable {K : Type} [Field K]

theorem zpow_val_intCast {M : Type*} [Group M] {x : M} (hx : x ^ 3 = 1) (n : ℤ) :
    x ^ ((n : ZMod 3).val) = x ^ n := by
  have h : (((n : ZMod 3).val : ℕ) : ℤ) = n % 3 := ZMod.val_intCast n
  rw [← zpow_natCast, h]
  conv_rhs => rw [← Int.emod_add_mul_ediv n 3]
  rw [zpow_add, zpow_mul, zpow_ofNat, hx, one_zpow, mul_one]

theorem cartan_E6_symm (i j : Fin Tag.E6.rank) : Tag.E6.cartan i j = Tag.E6.cartan j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem dV_e6InnerVec {ω : Kˣ} (hω : ω ^ 3 = 1) (i : Fin 5) :
    dV ω (e6InnerVec i) = torusElt .E6 K ⟨i.val, by have := i.2; decide +revert⟩ ω := by
  rw [torusElt_eq_rootDiagUnit, dV]
  congr 1
  funext j
  rw [torV, e6InnerVec, zpow_val_intCast hω, cartan_E6_symm]

theorem dV_e6InnerVec_mem {ω : Kˣ} (hω : ω ^ 3 = 1) (i : Fin 5) :
    dV ω (e6InnerVec i) ∈ adjointGroup .E6 K := by
  rw [dV_e6InnerVec hω]
  exact torusElt_mem_adjointGroup _ _

theorem subLin_e6InnerVec_apply (d : Fin 5 → ZMod 3) (j : Fin Tag.E6.rank) :
    subLin (τ := .E6) e6InnerVec d j = d 0 * e6InnerVec 0 j + d 1 * e6InnerVec 1 j +
      d 2 * e6InnerVec 2 j + d 3 * e6InnerVec 3 j + d 4 * e6InnerVec 4 j := by
  simp only [subLin, Finset.sum_apply, Fin.sum_univ_five, Pi.smul_apply, smul_eq_mul]

theorem subLin_e6InnerVec_injective : Function.Injective (subLin (τ := .E6) e6InnerVec) := by
  have hker : ∀ d : Fin 5 → ZMod 3, subLin (τ := .E6) e6InnerVec d = 0 → d = 0 := by
    intro d hd
    have h : ∀ j, subLin (τ := .E6) e6InnerVec d j = 0 := fun j => by rw [hd]; rfl
    have h0 := h 0
    have h1 := h 1
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    obtain ⟨a0, a1, a2, a3, a4⟩ : e6InnerVec 0 0 = -1 ∧ e6InnerVec 1 0 = 0 ∧
        e6InnerVec 2 0 = -1 ∧ e6InnerVec 3 0 = 0 ∧ e6InnerVec 4 0 = 0 := by decide
    obtain ⟨b0, b1, b2, b3, b4⟩ : e6InnerVec 0 1 = 0 ∧ e6InnerVec 1 1 = -1 ∧
        e6InnerVec 2 1 = 0 ∧ e6InnerVec 3 1 = -1 ∧ e6InnerVec 4 1 = 0 := by decide
    obtain ⟨c0, c1, c2, c3, c4⟩ : e6InnerVec 0 3 = 0 ∧ e6InnerVec 1 3 = -1 ∧
        e6InnerVec 2 3 = -1 ∧ e6InnerVec 3 3 = -1 ∧ e6InnerVec 4 3 = -1 := by decide
    obtain ⟨d0, d1, d2, d3, d4⟩ : e6InnerVec 0 4 = 0 ∧ e6InnerVec 1 4 = 0 ∧
        e6InnerVec 2 4 = 0 ∧ e6InnerVec 3 4 = -1 ∧ e6InnerVec 4 4 = -1 := by decide
    obtain ⟨f0, f1, f2, f3, f4⟩ : e6InnerVec 0 5 = 0 ∧ e6InnerVec 1 5 = 0 ∧
        e6InnerVec 2 5 = 0 ∧ e6InnerVec 3 5 = 0 ∧ e6InnerVec 4 5 = -1 := by decide
    rw [subLin_e6InnerVec_apply, a0, a1, a2, a3, a4] at h0
    rw [subLin_e6InnerVec_apply, b0, b1, b2, b3, b4] at h1
    rw [subLin_e6InnerVec_apply, c0, c1, c2, c3, c4] at h3
    rw [subLin_e6InnerVec_apply, d0, d1, d2, d3, d4] at h4
    rw [subLin_e6InnerVec_apply, f0, f1, f2, f3, f4] at h5
    have key : ∀ a b c e f : ZMod 3, a * -1 + b * 0 + c * -1 + e * 0 + f * 0 = 0 →
        a * 0 + b * -1 + c * 0 + e * -1 + f * 0 = 0 →
        a * 0 + b * -1 + c * -1 + e * -1 + f * -1 = 0 →
        a * 0 + b * 0 + c * 0 + e * -1 + f * -1 = 0 →
        a * 0 + b * 0 + c * 0 + e * 0 + f * -1 = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 ∧ f = 0 := by decide
    obtain ⟨hd0, hd1, hd2, hd3, hd4⟩ := key _ _ _ _ _ h0 h1 h3 h4 h5
    funext i
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
    · exact hd3
    · exact hd4
  intro y z hyz
  have h1 : subLin (τ := .E6) e6InnerVec (y - z) = 0 := by
    have e1 : y - z + z = y := sub_add_cancel y z
    have e2 := subLin_add (τ := .E6) e6InnerVec (y - z) z
    rw [e1, hyz] at e2
    have := congrArg (fun v => v - subLin (τ := .E6) e6InnerVec z) e2
    simpa using this.symm
  exact sub_eq_zero.1 (hker _ h1)

end Inner

section Core


variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def dE6 {ω : Kˣ} (hω : ω ^ 3 = 1) (y : Fin 5 → ZMod 3) :
    adjointGroup .E6 K :=
  dS hω (dV_e6InnerVec_mem (K := K) hω) y

theorem coe_dE6 {ω : Kˣ} (hω : ω ^ 3 = 1) (y : Fin 5 → ZMod 3) :
    (dE6 hω y : ModGL .E6 K) = dV ω (subLin e6InnerVec y) := rfl

theorem gLAPPrimeCoreOf_centralizer_dS_E6_four
    (hK : Nat.card K = 4) {ω : Kˣ} (hω : orderOf ω = 3) {y : Fin 5 → ZMod 3} (hy : y ≠ 0) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer {dE6 (pow_three_of_orderOf hω) y}) = ⊥ := by
  have : Finite (ModGL .E6 K) := finite_modGL
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  have hcert := Certificates.certificate13614
  unfold Native.e6FourCoreCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨⟨hhyp, hstd0⟩, hfull⟩ := hcert
  have hX3 : ∀ g ∈ adjointGroup .E6 K, g ∈ torusGroup .E6 K → g ^ 3 = 1 :=
    fun g _ hg => pow_three_of_mem_torusGroup hK hg
  have hstd : familyKernel (famV (τ := .E6) ω (Native.stdBasis Tag.E6.rank)) = ∅ ∧
      ∀ w ∈ familyStabilizer (famV (τ := .E6) ω (Native.stdBasis Tag.E6.rank)), w = 1 :=
    famData0_of_famOK0 hω length_of_mem_stdBasis lt_of_mem_stdBasis hfull
  have htor : ∀ g ∈ adjointGroup .E6 K, (∀ x, Commute (dV (τ := .E6) ω x) g) →
      g ∈ torusGroup .E6 K := fun g hg h =>
    mem_torusGroup_of_mem_familyCentralizer_std hstd (mem_familyCentralizer_std hg h)
  have hlenL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec),
      b.length = Tag.E6.rank := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact length_liftL _ _
  have hltL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec), ∀ x ∈ b, x < 3 := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact lt_of_mem_liftL _ _
  have hleaf : ∀ fl ∈ normVecs 3 5, GLAPPrimeCoreOf 3 (famCentS ω (adjointGroup .E6 K)
      ((kerBasis 3 fl).map (liftL (τ := .E6) e6InnerVec))) = ⊥ := by
    intro fl hfl
    refine gLAPPrimeCoreOf_leafS le_rfl hX3 ?_
    rcases famData_of_famOKW hω (hlenL _) (hltL _) (hhyp fl hfl) with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · refine Or.inr ⟨α, hα, hker, hW, fun g _ hg => ?_, fun N hNL hnorm hcop => ?_⟩
      · refine pow_three_mem_of_mem_sup hK ?_ hg
        exact torusGroup_le_normalizer_rootSpan fun β hβ => by
          rcases hβ with rfl | rfl
          · exact hα
          · exact IsRoot.neg hα
      · refine eq_bot_of_le_rootSpan hK hω
          (χ := familyChar (famV (τ := .E6) ω ((kerBasis 3 fl).map (liftL e6InnerVec)))) hα
          (by rw [kernelRoots_familyChar, hker]) htor N hNL hnorm hcop
  have hstdS : GLAPPrimeCoreOf 3 (famCentS ω (adjointGroup .E6 K)
      ((Native.stdBasis 5).map (liftL (τ := .E6) e6InnerVec))) = ⊥ :=
    gLAPPrimeCoreOf_leafS le_rfl hX3 (Or.inl (famData0_of_famOK0W hω (hlenL _) (hltL _) hstd0))
  exact gLAPPrimeCoreOf_centralizer_subS hω (dV_e6InnerVec_mem hω3) subLin_e6InnerVec_injective
    hleaf hstdS hy

end Core

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
