module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Exc3CoreWDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.Sec6.Up34Exc


theorem exc3core_posRow_testBit {τ : Tag} {k : ℕ} (hk : k < τ.artifactRoots.length) (l : ℕ) :
    (exc3core_posRow τ k).testBit l = decide (l < τ.artifactRoots.length ∧
      iform (RD.rt τ l) (RD.rt τ k) % 3 = 1) := by
  have hR : ∀ r ∈ τ.artifactRoots, r.length ≤ τ.rank := fun r hr =>
    (length_of_mem_artifactRoots hr).le
  have hlt : ∀ r ∈ exc3core_posRows τ, r < 2 ^ τ.artifactRoots.length := by
    intro r hr
    rw [exc3core_posRows] at hr
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    have hst := RD.accum_spec τ.rank τ.artifactRoots (RD.digs3 w) (fun _ => 0) (0, 0) hR
      (RD.digs3_lt w) (fun _ => ⟨le_rfl, by norm_num⟩) ⟨fun _ => by simp, fun _ => by simp⟩
    rw [hst.bit1 i]
    simp [show ¬ i < τ.artifactRoots.length by omega]
  have hfetch : RD.fetchT (RD.tblOf (2 ^ τ.artifactRoots.length) (exc3core_posRows τ))
      (2 ^ τ.artifactRoots.length) k = (exc3core_posRows τ).getD k 0 :=
    RD.fetchT_tblOf (by positivity) _ hlt k
  have hget : (exc3core_posRows τ).getD k 0 =
      (RD.accum (2 ^ τ.artifactRoots.length - 1) (RD.colsOf τ.rank τ.artifactRoots)
        (RD.digs3 ((RD.bRoots τ).getD k [])) (0, 0)).1 :=
    RD.getD_map_lt (fun w => (RD.accum (2 ^ τ.artifactRoots.length - 1)
        (RD.colsOf τ.rank τ.artifactRoots) (RD.digs3 w) (0, 0)).1) (RD.bRoots τ)
      (by simpa [RD.bRoots] using hk) [] 0
  have hrow : exc3core_posRow τ k =
      (RD.accum (2 ^ τ.artifactRoots.length - 1) (RD.colsOf τ.rank τ.artifactRoots)
        (RD.digs3 ((RD.bRoots τ).getD k [])) (0, 0)).1 := by
    rw [exc3core_posRow, exc3core_posTbl, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
      Nat.land_eq, Nat.and_two_pow_sub_one_eq_mod,
      show 2 ^ (τ.artifactRoots.length * k) = (2 ^ τ.artifactRoots.length) ^ k by rw [pow_mul]]
    exact hfetch.trans hget
  rw [hrow]
  have hst := RD.accum_spec τ.rank τ.artifactRoots (RD.digs3 ((RD.bRoots τ).getD k []))
    (fun _ => 0) (0, 0) hR (RD.digs3_lt _) (fun _ => ⟨le_rfl, by norm_num⟩)
    ⟨fun _ => by simp, fun _ => by simp⟩
  rw [hst.bit1 l]
  by_cases hl : l < τ.artifactRoots.length
  · have h1 : (0 + RD.dotR (τ.artifactRoots.getD l [])
        ((RD.digs3 ((RD.bRoots τ).getD k [])).map Int.ofNat)) % 3
        = iform (RD.rt τ l) (RD.rt τ k) % 3 := by
      rw [zero_add, RD.map_ofNat_digs3, RD.bRoots_getD hk, RD.dotR_map_mod3, RD.iform_rt_rt hl hk]
      simp only [RD.rl]
    rw [h1]
  · simp [hl]

theorem exc3core_expMasks_testBit {τ : Tag} {d : List ℕ} (hd : ∀ x ∈ d, x < 3) (l : ℕ) :
    ((exc3core_expMasks τ d).1.testBit l = decide (l < τ.artifactRoots.length ∧
        RD.digDot (RD.rl τ l) d % 3 = 1)) ∧
      ((exc3core_expMasks τ d).2.testBit l = decide (l < τ.artifactRoots.length ∧
        RD.digDot (RD.rl τ l) d % 3 = 2)) := by
  have hR : ∀ r ∈ τ.artifactRoots, r.length ≤ τ.rank := fun r hr =>
    (length_of_mem_artifactRoots hr).le
  have hst := RD.accum_spec τ.rank τ.artifactRoots d (fun _ => 0) (0, 0) hR hd
    (fun _ => ⟨le_rfl, by norm_num⟩) ⟨fun _ => by simp, fun _ => by simp⟩
  constructor
  · rw [exc3core_expMasks, hst.bit1 l, decide_eq_decide]
    simp [RD.digDot, RD.rl, zero_add]
  · rw [exc3core_expMasks, hst.bit2 l, decide_eq_decide]
    simp [RD.digDot, RD.rl, zero_add]

theorem exc3core_class_extract {τ : Tag} (hτ : NoG2 τ) (cap : ℕ) (u w : ℕ → Bool)
    (h : ∀ d ∈ RD.allVecs τ.rank, exc3core_eCheck τ cap u w d = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (ω₀ : Lˣ) (e : Fin τ.rank → ℕ) (V b k : ℕ) (hkκ : RD.rt τ k ∈ kernelRoots (rootCharHom a)),
      ω₀ ^ 3 = 1 ∧ (∀ j, e j < 3) ∧ (∀ j, a j = ω₀ ^ e j) ∧ (ω₀ = 1 → ∀ j, e j = 0) ∧
      i = Quotient.mk (kernelRootSetoid (rootCharHom a)) ⟨RD.rt τ k, hkκ⟩ ∧ V.testBit k = true ∧
      RD.IsComp (RD.rowOf τ) (RD.kerMaskFast τ (List.ofFn e)) V b ∧
      exc3core_okC τ cap u w (List.ofFn e) V = true ∧
      RD.Spec (rootCharHom a) (RD.rowOf τ) (RD.kerMaskFast τ (List.ofFn e)) := by
  obtain ⟨ω₀, e, hω₀, he3, hae, he0⟩ := RD.exists_exps a ha
  have hprim : ω₀ ≠ 1 ∨ ∀ j, e j = 0 := by
    by_cases h1 : ω₀ = 1
    · exact Or.inr (he0 h1)
    · exact Or.inl h1
  have hdig : ∀ x ∈ List.ofFn e, x < 3 := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact he3 j
  have hSpec : RD.Spec (rootCharHom a) (RD.rowOf τ) (RD.kerMaskFast τ (List.ofFn e)) :=
    ⟨RD.rowOf_spec, fun l => by
      rw [RD.kerMaskFast_eq _ hdig]
      exact RD.kerMask_spec a ω₀ e hω₀ hae hprim l⟩
  induction i using Quotient.inductionOn with
  | _ x =>
    obtain ⟨α, hα⟩ := x
    obtain ⟨k, hk, rfl⟩ := RD.isRoot_iff_exists_rt.1 hα.1
    have hKk : (RD.kerMaskFast τ (List.ofFn e)).testBit k = true := (hSpec.K_iff k).2 ⟨hk, hα⟩
    have hd := h _ (RD.ofFn_mem_allVecs _ e he3)
    obtain ⟨V, b, hkV, hV, hok⟩ := RD.compLoop2_sound (fun x => RD.rowM2_pow hτ x) _ _ _ _ _ hd
      (fun x hx => hx) k hKk
    exact ⟨ω₀, e, V, b, k, hα, hω₀, he3, hae, he0, rfl, hkV, hV, hok, hSpec⟩

private theorem exc3core_ker_lt_of_check_aux1 {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {K : ℕ} (hSpec : RD.Spec χ (RD.rowOf τ) K) :
    (kernelRoots χ).ncard = (RD.bitsSet K).ncard := by
  have himg : kernelRoots χ = RD.rt τ '' RD.bitsSet K := by
    ext β
    refine ⟨fun hβ => ?_, fun hβ => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := RD.isRoot_iff_exists_rt.1 hβ.1
      exact ⟨j, (hSpec.K_iff j).2 ⟨hj, hβ⟩, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := hβ
      exact ((hSpec.K_iff j).1 hj).2
  rw [himg]
  exact Set.InjOn.ncard_image (fun x hx y hy hxy =>
    RD.rt_injOn ((hSpec.K_iff x).1 hx).1 ((hSpec.K_iff y).1 hy).1 hxy)

theorem exc3core_ker_lt_of_check {τ : Tag} (hτ : NoG2 τ) (cap : ℕ) (u w : ℕ → Bool)
    (hcap : τ.artifactRoots.length < cap)
    (h : ∀ d ∈ RD.allVecs τ.rank, exc3core_eCheck τ cap u w d = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hu : u (componentRoots (rootCharHom a) i).ncard = true) :
    (kernelRoots (rootCharHom a)).ncard < 2 * (componentRoots (rootCharHom a) i).ncard := by
  obtain ⟨ω₀, e, V, b, k, hkκ, -, -, -, -, rfl, hkV, hV, hok, hSpec⟩ :=
    exc3core_class_extract hτ cap u w h a ha i
  have hn := RD.ncard_componentRoots_eq hSpec hV hkV hkκ
  have hcard : (RD.bitsSet V).ncard ≤ τ.artifactRoots.length := by
    have hsub : RD.bitsSet V ⊆ (Finset.range τ.artifactRoots.length : Set ℕ) := fun x hx =>
      Finset.mem_range.mpr ((hSpec.K_iff x).1 (hV.reach x hx).1).1
    simpa using Set.ncard_le_ncard hsub
  obtain ⟨hcnt1, hcnt2⟩ := RD.cnt2_spec cap V
  have hlt : RD.cnt2 cap V < cap := by
    by_contra hle
    have hEq : RD.cnt2 cap V = cap := le_antisymm (RD.cnt2_le cap V) (not_lt.1 hle)
    have := hcnt1 hEq
    omega
  have hnv : (RD.bitsSet V).ncard = RD.cnt2 cap V := hcnt2 hlt
  have hu' : u (RD.cnt2 cap V) = true := by rw [← hnv, ← hn]; exact hu
  have hok' : exc3core_wUniq τ cap (List.ofFn e) V = true := by
    have hh := hok
    simp only [exc3core_okC, hu', Bool.not_true, Bool.false_or, Bool.and_eq_true] at hh
    exact hh.1
  have hwn : RD.cnt2 (2 * RD.cnt2 cap V) (RD.kerMaskFast τ (List.ofFn e)) <
      2 * RD.cnt2 cap V := by
    simpa only [exc3core_wUniq, decide_eq_true_eq] using hok'
  have hKlt : (RD.bitsSet (RD.kerMaskFast τ (List.ofFn e))).ncard < 2 * RD.cnt2 cap V := by
    rw [(RD.cnt2_spec (2 * RD.cnt2 cap V) (RD.kerMaskFast τ (List.ofFn e))).2 hwn]
    exact hwn
  have hker := exc3core_ker_lt_of_check_aux1 (rootCharHom a) hSpec
  rw [hker, hn, hnv]
  exact hKlt

private theorem exc3core_wobs_of_check_aux1 {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) (ω₀ : Lˣ) (e : Fin τ.rank → ℕ)
    (hae : ∀ j, a j = ω₀ ^ e j) {l : ℕ} (hl : l < τ.artifactRoots.length) :
    (rootCharHom a) (Multiplicative.ofAdd (RD.rt τ l)) =
      ω₀ ^ RD.digDot (RD.rl τ l) (List.ofFn e) := by
  rw [RD.digDot_ofFn hl e]
  exact RD.rootChar_eq_zpow_sum a ω₀ e hae (RD.rt τ l)

private theorem exc3core_wobs_of_check_aux2 {τ : Tag} {L : Type} [Field L]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) {K V b k cap : ℕ}
    (hS : RD.Spec χ (RD.rowOf τ) K) (hV : RD.IsComp (RD.rowOf τ) K V b)
    (hk : V.testBit k = true) (hkκ : RD.rt τ k ∈ kernelRoots χ)
    (hcap : τ.artifactRoots.length < cap) :
    (componentRoots χ (Quotient.mk (kernelRootSetoid χ) ⟨RD.rt τ k, hkκ⟩)).ncard =
      RD.cnt2 cap V := by
  rw [RD.ncard_componentRoots_eq hS hV hk hkκ]
  have hKsub : RD.bitsSet K ⊆ (((Finset.range τ.artifactRoots.length : Finset ℕ)) : Set ℕ) :=
    fun x hx => Finset.mem_range.2 ((hS.K_iff x).1 hx).1
  have hcard_le : (RD.bitsSet V).ncard ≤ τ.artifactRoots.length :=
    calc (RD.bitsSet V).ncard ≤ (RD.bitsSet K).ncard :=
          Set.ncard_le_ncard (fun x hx => (hV.reach x hx).1) (RD.bitsSet_finite K)
      _ ≤ (((Finset.range τ.artifactRoots.length : Finset ℕ)) : Set ℕ).ncard :=
          Set.ncard_le_ncard hKsub (Finset.finite_toSet _)
      _ = τ.artifactRoots.length := by simp
  have hVlt : (RD.bitsSet V).ncard < cap := lt_of_le_of_lt hcard_le hcap
  have hcnt_lt : RD.cnt2 cap V < cap := by
    rcases lt_or_eq_of_le (RD.cnt2_le cap V) with hlt | heq
    · exact hlt
    · exfalso
      have := (RD.cnt2_spec cap V).1 heq
      omega
  exact (RD.cnt2_spec cap V).2 hcnt_lt

private theorem exc3core_wobs_of_check_aux3 {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) {ω₀ : Lˣ} {e : Fin τ.rank → ℕ}
    (hae : ∀ j, a j = ω₀ ^ e j) (hω₀ : ω₀ ^ 3 = 1) (hωne : ω₀ ≠ 1)
    {k₁ l : ℕ} (hk₁ : k₁ < τ.artifactRoots.length) (hl : l < τ.artifactRoots.length)
    (hpow1 : ω₀ ^ RD.digDot (RD.rl τ k₁) (List.ofFn e) = ω₀ ^ (1:ℤ))
    (hχinv : (rootCharHom a) (Multiplicative.ofAdd (RD.rt τ l)) =
      ((rootCharHom a) (Multiplicative.ofAdd (RD.rt τ k₁)))⁻¹) :
    RD.digDot (RD.rl τ l) (List.ofFn e) % 3 = 2 := by
  have ho : orderOf ω₀ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hω₀ hωne
  have hEl_eq : ω₀ ^ RD.digDot (RD.rl τ l) (List.ofFn e) =
      (ω₀ ^ RD.digDot (RD.rl τ k₁) (List.ofFn e))⁻¹ := by
    rw [← exc3core_wobs_of_check_aux1 a ω₀ e hae hl,
      ← exc3core_wobs_of_check_aux1 a ω₀ e hae hk₁]
    exact hχinv
  have hEl_neg : ω₀ ^ RD.digDot (RD.rl τ l) (List.ofFn e) = ω₀ ^ (-1:ℤ) := by
    rw [hpow1] at hEl_eq
    rw [hEl_eq, zpow_one, ← zpow_neg_one]
  have h1 : RD.digDot (RD.rl τ l) (List.ofFn e) % 3 = (-1:ℤ) % 3 := by
    have h2 := zpow_eq_zpow_iff_modEq.1 hEl_neg
    rw [ho] at h2
    exact h2
  rw [h1]
  norm_num

private theorem exc3core_wobs_of_check_aux4 {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)}
    (V l k : ℕ) (hΨ : Ψ = RD.rt τ '' RD.bitsSet V)
    (hl : l < τ.artifactRoots.length) (hk : k < τ.artifactRoots.length)
    (hno : ∀ β ∈ Ψ, iform (RD.rt τ l) β = iform (RD.rt τ k) β) :
    exc3core_sig τ V l = exc3core_sig τ V k := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [exc3core_sig, exc3core_sig, Nat.land_eq, Nat.land_eq,
    Nat.testBit_and, Nat.testBit_and]
  by_cases hj : V.testBit j = true
  · have hmemj : RD.rt τ j ∈ Ψ := by
      rw [hΨ]
      exact ⟨j, hj, rfl⟩
    have hif : iform (RD.rt τ j) (RD.rt τ l) = iform (RD.rt τ j) (RD.rt τ k) := by
      rw [iform_comm (RD.rt τ j) (RD.rt τ l), iform_comm (RD.rt τ j) (RD.rt τ k)]
      exact hno (RD.rt τ j) hmemj
    rw [hj, Bool.and_true, Bool.and_true,
      exc3core_posRow_testBit hl j, exc3core_posRow_testBit hk j, hif]
  · have hj' : V.testBit j = false := by simpa using hj
    rw [hj']
    simp

private theorem exc3core_wobs_of_check_aux5 {τ : Tag} (V l k₁ : ℕ) (d : List ℕ)
    (hdig : ∀ x ∈ d, x < 3) (hl : l < τ.artifactRoots.length)
    (hEl : RD.digDot (RD.rl τ l) d % 3 = 2)
    (hall : (exc3core_sigs τ V (exc3core_expMasks τ d).2).all
      (fun s => s != exc3core_sig τ V k₁) = true) :
    exc3core_sig τ V l ≠ exc3core_sig τ V k₁ := by
  have hmem : exc3core_sig τ V l ∈ exc3core_sigs τ V (exc3core_expMasks τ d).2 := by
    rw [exc3core_sigs, List.mem_map]
    refine ⟨l, ?_, rfl⟩
    rw [List.mem_filter, List.mem_range]
    refine ⟨hl, ?_⟩
    rw [(exc3core_expMasks_testBit hdig l).2]
    exact decide_eq_true ⟨hl, hEl⟩
  intro hEq
  have hthis := List.all_eq_true.1 hall (exc3core_sig τ V l) hmem
  rw [hEq] at hthis
  simpa using hthis

private theorem exc3core_wobs_of_check_aux6 {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) (ω₀ : Lˣ) (e : Fin τ.rank → ℕ) (V k₁ : ℕ)
    (Ψ : Set (Fin τ.rank → ℤ))
    (hae : ∀ j, a j = ω₀ ^ e j) (hω₀ : ω₀ ^ 3 = 1)
    (he0 : ω₀ = 1 → ∀ j, e j = 0)
    (hdig : ∀ x ∈ List.ofFn e, x < 3)
    (hΨ : Ψ = RD.rt τ '' RD.bitsSet V)
    (hk₁ : k₁ < τ.artifactRoots.length)
    (hE1 : RD.digDot (RD.rl τ k₁) (List.ofFn e) % 3 = 1)
    (hall : (exc3core_sigs τ V (exc3core_expMasks τ (List.ofFn e)).2).all
      (fun s => s != exc3core_sig τ V k₁) = true) :
    exc3core_WObs τ (rootCharHom a) Ψ := by
  have hωne : ω₀ ≠ 1 := by
    intro h1
    have hE0 : RD.digDot (RD.rl τ k₁) (List.ofFn e) = 0 := by
      rw [RD.digDot_ofFn hk₁ e]
      simp [he0 h1]
    rw [hE0] at hE1
    norm_num at hE1
  have ho : orderOf ω₀ = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hω₀ hωne
  have hE1mod : RD.digDot (RD.rl τ k₁) (List.ofFn e) % 3 = (1:ℤ) % 3 := by
    rw [hE1]
    norm_num
  have hpow1 : ω₀ ^ RD.digDot (RD.rl τ k₁) (List.ofFn e) = ω₀ ^ (1:ℤ) := by
    rw [zpow_eq_zpow_iff_modEq, ho]
    exact hE1mod
  have hchi1 : (rootCharHom a) (Multiplicative.ofAdd (RD.rt τ k₁)) = ω₀ := by
    rw [exc3core_wobs_of_check_aux1 a ω₀ e hae hk₁]
    exact hpow1.trans (zpow_one ω₀)
  unfold exc3core_WObs
  refine ⟨RD.rt τ k₁, RD.isRoot_rt hk₁, ?_, ?_⟩
  · rw [hchi1]
    exact hωne
  · intro γ' hγ' hχinv
    obtain ⟨l, hl, rfl⟩ := RD.isRoot_iff_exists_rt.1 hγ'
    by_contra hcon
    have hno : ∀ β ∈ Ψ, iform (RD.rt τ l) β = iform (RD.rt τ k₁) β := by
      intro β hβ
      by_contra hne
      exact hcon ⟨β, hβ, hne⟩
    have hEl := exc3core_wobs_of_check_aux3 a hae hω₀ hωne hk₁ hl hpow1 hχinv
    exact (exc3core_wobs_of_check_aux5 V l k₁ (List.ofFn e) hdig hl hEl hall)
      (exc3core_wobs_of_check_aux4 V l k₁ hΨ hl hk₁ hno)

theorem exc3core_wobs_of_check {τ : Tag} (hτ : NoG2 τ) (cap : ℕ) (u w : ℕ → Bool)
    (hcap : τ.artifactRoots.length < cap)
    (h : ∀ d ∈ RD.allVecs τ.rank, exc3core_eCheck τ cap u w d = true)
    {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (ha : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hu : u (componentRoots (rootCharHom a) i).ncard = true)
    (hw : w (componentRoots (rootCharHom a) i).ncard = true) :
    exc3core_WObs τ (rootCharHom a) (componentRoots (rootCharHom a) i) := by
  obtain ⟨ω₀, e, V, b, k, hkκ, hω₀, he3, hae, he0, hi, hkV, hV, hok, hS⟩ :=
    exc3core_class_extract hτ cap u w h a ha i
  have hdig : ∀ x ∈ List.ofFn e, x < 3 := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
    exact he3 j
  have hΨ : componentRoots (rootCharHom a) i = RD.rt τ '' RD.bitsSet V := by
    rw [hi]
    exact RD.componentRoots_eq_image hS hV hkV hkκ
  have hnc : (componentRoots (rootCharHom a) i).ncard = RD.cnt2 cap V := by
    rw [hi]
    exact exc3core_wobs_of_check_aux2 (rootCharHom a) hS hV hkV hkκ hcap
  have huc : u (RD.cnt2 cap V) = true := by
    rw [← hnc]
    exact hu
  have hwc : w (RD.cnt2 cap V) = true := by
    rw [← hnc]
    exact hw
  have hwobs : exc3core_wObs τ (List.ofFn e) V = true := by
    have h1 : (exc3core_wUniq τ cap (List.ofFn e) V &&
        (!(w (RD.cnt2 cap V)) || exc3core_wObs τ (List.ofFn e) V)) = true := by
      simpa only [exc3core_okC, huc, Bool.not_true, Bool.false_or] using hok
    simp only [Bool.and_eq_true] at h1
    have h2 := h1.2
    simpa only [hwc, Bool.not_true, Bool.false_or] using h2
  obtain ⟨k₁, hk₁mem, hk₁prop⟩ := List.any_eq_true.1 hwobs
  have hk₁ : k₁ < τ.artifactRoots.length := List.mem_range.1 hk₁mem
  have hk₁' := hk₁prop
  simp only [Bool.and_eq_true] at hk₁'
  have hbit1 : (exc3core_expMasks τ (List.ofFn e)).1.testBit k₁ = true := hk₁'.1
  have hall : (exc3core_sigs τ V (exc3core_expMasks τ (List.ofFn e)).2).all
      (fun s => s != exc3core_sig τ V k₁) = true := hk₁'.2
  have hE1 : RD.digDot (RD.rl τ k₁) (List.ofFn e) % 3 = 1 := by
    rw [(exc3core_expMasks_testBit hdig k₁).1] at hbit1
    exact (of_decide_eq_true hbit1).2
  exact exc3core_wobs_of_check_aux6 a ω₀ e V k₁ (componentRoots (rootCharHom a) i)
    hae hω₀ he0 hdig hΨ hk₁ hE1 hall

theorem exc3core_all_of_chunks {α : Type} (vs : List α) (f : α → Bool) (c k : ℕ) (hc : 0 < c)
    (hl : vs.length ≤ c * k)
    (h : ∀ j < k, ((vs.drop (c * j)).take c).all f = true) : vs.all f = true := by
  have key : ∀ k, ∀ vs : List α, vs.length ≤ c * k →
      (∀ j < k, ((vs.drop (c * j)).take c).all f = true) → vs.all f = true := by
    intro k
    induction k with
    | zero =>
        intro vs hl h
        cases vs with
        | nil => rfl
        | cons a t => simp at hl
    | succ k ih =>
        intro vs hl h
        have h0 : (vs.take c).all f = true := by
          simpa using h 0 (Nat.succ_pos k)
        have hl' : (vs.drop c).length ≤ c * k := by
          rw [List.length_drop]
          have hs := hl
          rw [Nat.mul_succ] at hs
          omega
        have h' : ∀ j < k, (((vs.drop c).drop (c * j)).take c).all f = true := by
          intro j hj
          have hh := h (j + 1) (by omega)
          rw [Nat.mul_succ] at hh
          rwa [List.drop_drop, Nat.add_comm]
        have ihh := ih (vs.drop c) hl' h'
        rw [← List.take_append_drop c vs, List.all_append]
        simp [h0, ihh]
  exact key k vs hl h

theorem exc3core_unique_of_ker_lt {τ : Tag} {L : Type} [Field L]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (h : (kernelRoots χ).ncard < 2 * (componentRoots χ i).ncard) :
    ∀ i' : KernelComponent χ,
      (componentRoots χ i').ncard = (componentRoots χ i).ncard → i' = i := by
  intro i' hi'
  by_contra hne
  have hdisj : Disjoint (componentRoots χ i) (componentRoots χ i') :=
    Set.disjoint_left.2 fun a ha ha' => by
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨ha1', ha2'⟩ := ha'
      have hs : (⟨a, ha1⟩ : kernelRoots χ) = ⟨a, ha1'⟩ := Subtype.ext rfl
      exact hne (by rw [← ha2, hs, ha2'])
  have hfin : (kernelRoots χ).Finite :=
    (finite_setOf_isRoot τ).subset fun a ha => ha.1
  have hfinA : (componentRoots χ i).Finite :=
    hfin.subset fun a ha => by obtain ⟨h, _⟩ := ha; exact h
  have hfinB : (componentRoots χ i').Finite :=
    hfin.subset fun a ha => by obtain ⟨h, _⟩ := ha; exact h
  have hun := Set.ncard_union_eq hdisj hfinA hfinB
  have hsub : componentRoots χ i ∪ componentRoots χ i' ⊆ kernelRoots χ :=
    Set.union_subset (fun a ha => by obtain ⟨h, _⟩ := ha; exact h)
      (fun a ha => by obtain ⟨h, _⟩ := ha; exact h)
  have hle := Set.ncard_le_ncard hsub hfin
  rw [hun, hi'] at hle
  omega

end CFSG.LocalAnalysis.GLTheoremA.I167

end
