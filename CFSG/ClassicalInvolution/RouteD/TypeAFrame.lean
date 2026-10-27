module

public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models Module Matrix
open scoped MatrixGroups


section Involution

variable {F : Type} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

theorem pow_sub_smul_one_apply {f : Module.End F V} {w : V} {c : F} (hw : f w = c • w) (μ : F)
    (k : ℕ) : ((f - μ • (1 : Module.End F V)) ^ k) w = (c - μ) ^ k • w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    simp only [LinearMap.sub_apply, map_smul, hw, LinearMap.smul_apply, Module.End.one_apply]
    rw [← sub_smul, smul_smul, pow_succ]

theorem mem_maxGenEigenspace_of_mul_self (h2 : (2 : F) ≠ 0) {f : Module.End F V} (hf : f * f = 1)
    {μ : F} {v : V} (hv : v ∈ f.maxGenEigenspace μ) :
    (μ = 1 ∧ f v = v) ∨ (μ = -1 ∧ f v = -v) ∨ v = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ v).mp hv
  have hff : ∀ w, f (f w) = w := fun w => by simpa using LinearMap.congr_fun hf w
  set vp : V := (2 : F)⁻¹ • (v + f v) with hvp
  set vm : V := (2 : F)⁻¹ • (v - f v) with hvm
  have hsum : v = vp + vm := by
    rw [hvp, hvm, ← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul, inv_mul_cancel₀ h2,
      one_smul]
  have hp : f vp = (1 : F) • vp := by
    rw [hvp]; simp only [map_smul, map_add, hff]; module
  have hm : f vm = (-1 : F) • vm := by
    rw [hvm]; simp only [map_smul, map_sub, hff]; module
  have e : (1 - μ) ^ k • vp + (-1 - μ) ^ k • vm = 0 := by
    have := hk
    rw [hsum, map_add, pow_sub_smul_one_apply hp, pow_sub_smul_one_apply hm] at this
    exact this
  have e' : (1 - μ) ^ k • vp - (-1 - μ) ^ k • vm = 0 := by
    have := congrArg f e
    simp only [map_add, map_smul, hp, hm, map_zero] at this
    have h3 : (1 - μ) ^ k • vp + (-1 - μ) ^ k • (-1 : F) • vm = 0 := by
      simpa [smul_smul] using this
    simpa [sub_eq_add_neg, smul_smul] using h3
  have e1 : (1 - μ) ^ k • vp = 0 := by
    have : (2 : F) • ((1 - μ) ^ k • vp) = 0 := by
      rw [two_smul]
      calc (1 - μ) ^ k • vp + (1 - μ) ^ k • vp
          = ((1 - μ) ^ k • vp + (-1 - μ) ^ k • vm) + ((1 - μ) ^ k • vp - (-1 - μ) ^ k • vm) := by
            abel
        _ = 0 := by rw [e, e', add_zero]
    exact (smul_eq_zero.mp this).resolve_left h2
  have e2 : (-1 - μ) ^ k • vm = 0 := by
    have := e
    rw [e1, zero_add] at this
    exact this
  by_cases hμ1 : μ = 1
  · left
    refine ⟨hμ1, ?_⟩
    have hm0 : vm = 0 := by
      have hne : (-1 - μ) ^ k ≠ 0 := by
        apply pow_ne_zero
        rw [hμ1]
        intro h
        apply h2
        linear_combination -h
      exact (smul_eq_zero.mp e2).resolve_left hne
    have : v = vp := by rw [hsum, hm0, add_zero]
    rw [this]
    simpa using hp
  · by_cases hμ2 : μ = -1
    · right; left
      refine ⟨hμ2, ?_⟩
      have hp0 : vp = 0 := by
        have hne : (1 - μ) ^ k ≠ 0 := by
          apply pow_ne_zero
          rw [hμ2]
          intro h
          apply h2
          linear_combination h
        exact (smul_eq_zero.mp e1).resolve_left hne
      have : v = vm := by rw [hsum, hp0, zero_add]
      rw [this]
      simpa using hm
    · right; right
      have hp0 : vp = 0 := by
        have hne : (1 - μ) ^ k ≠ 0 := by
          apply pow_ne_zero
          intro h
          exact hμ1 (by linear_combination -h)
        exact (smul_eq_zero.mp e1).resolve_left hne
      have hm0 : vm = 0 := by
        have hne : (-1 - μ) ^ k ≠ 0 := by
          apply pow_ne_zero
          intro h
          exact hμ2 (by linear_combination -h)
        exact (smul_eq_zero.mp e2).resolve_left hne
      rw [hsum, hp0, hm0, add_zero]

end Involution


section Chain

variable {F : Type} [Field F] {N : ℕ}

@[expose] def chainSign (F : Type) [Field F] (a j : ℕ) : F := if j = a ∨ j = a + 1 then -1 else 1

theorem exists_chainSep {k j l : ℕ} (hk : 2 ≤ k) (hj : j ≤ k) (hl : l ≤ k) (hjl : j ≠ l) :
    ∃ a, a < k ∧ ¬ ((j = a ∨ j = a + 1) ↔ (l = a ∨ l = a + 1)) := by
  by_contra h
  push Not at h
  rcases lt_or_gt_of_ne hjl with hlt | hlt
  · have h1 := h (l - 1) (by omega)
    have h2 := h (j - 1) (by omega)
    have h3 := h 1 (by omega)
    omega
  · have h1 := h (j - 1) (by omega)
    have h2 := h (l - 1) (by omega)
    have h3 := h 1 (by omega)
    omega

theorem exists_chainNeg {k j : ℕ} (hk : 1 ≤ k) (hj : j ≤ k) : ∃ a, a < k ∧ (j = a ∨ j = a + 1) := by
  by_cases h : j < k
  · exact ⟨j, h, Or.inl rfl⟩
  · exact ⟨j - 1, by omega, Or.inr (by omega)⟩


structure IsInvChain (I : ℕ → Matrix (Fin N) (Fin N) F) (k : ℕ) : Prop where
  sq : ∀ a < k, I a * I a = 1
  comm : ∀ a < k, ∀ b < k, I a * I b = I b * I a
  dim : ∀ a < k, finrank F (eigSpace (I a) (-1)) = 2
  far : ∀ a < k, ∀ b < k, a + 2 ≤ b → eigSpace (I a) (-1) ⊓ eigSpace (I b) (-1) = ⊥
  adj : ∀ a, a + 1 < k → eigSpace (I a) (-1) ⊓ eigSpace (I (a + 1)) (-1) ≠ ⊥
  ne : ∀ a, a + 1 < k → I a ≠ I (a + 1)

variable {I : ℕ → Matrix (Fin N) (Fin N) F} {k : ℕ}

theorem mulVec_mem_eigSpace_of_comm {A B : Matrix (Fin N) (Fin N) F} (hAB : A * B = B * A)
    {c : F} {v : Fin N → F} (hv : v ∈ eigSpace B c) : A *ᵥ v ∈ eigSpace B c := by
  rw [mem_eigSpace] at hv ⊢
  rw [mulVec_mulVec, ← hAB, ← mulVec_mulVec, hv, Matrix.mulVec_smul]

theorem IsInvChain.pair_profile (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) {a : ℕ} (ha : a + 1 < k) :
    finrank F (eigSpace (I a) (-1) ⊓ eigSpace (I (a + 1)) (-1) : Submodule F (Fin N → F)) = 1 ∧
    finrank F (eigSpace (I a) (-1) ⊓ eigSpace (I (a + 1)) 1 : Submodule F (Fin N → F)) = 1 ∧
    finrank F (eigSpace (I a) 1 ⊓ eigSpace (I (a + 1)) (-1) : Submodule F (Fin N → F)) = 1 := by
  have hf := toLin'_mul_self (hI.sq a (by omega))
  have hg := toLin'_mul_self (hI.sq (a + 1) ha)
  have hfg := toLin'_mul_comm (hI.comm a (by omega) (a + 1) ha)
  set d : Bool × Bool → ℕ := fun s => finrank F (jointEig (I a) (I (a + 1)) s) with hd
  have E1 : 2 = d (false, true) + d (false, false) := by
    rw [← hI.dim a (by omega)]
    exact finrank_eigenspace_eq h2 hg hfg false
  have E2 : 2 = d (true, false) + d (false, false) := by
    rw [← hI.dim (a + 1) ha]
    exact finrank_eigenspace_eq' h2 hf hfg false
  have h0 : d (false, false) ≠ 0 := by
    intro h
    apply hI.adj a ha
    exact Submodule.finrank_eq_zero.mp h
  have h2' : d (false, false) ≠ 2 := by
    intro h
    have hz1 : jointEig (I a) (I (a + 1)) (true, false) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by change d (true, false) = 0; omega)
    have hz2 : jointEig (I a) (I (a + 1)) (false, true) = ⊥ :=
      Submodule.finrank_eq_zero.mp (by change d (false, true) = 0; omega)
    have := eq_of_jointEigenspace_mixed_eq_bot h2 hf hg hfg hz1 hz2
    exact hI.ne a ha (Matrix.toLin'.injective this)
  refine ⟨?_, ?_, ?_⟩
  · change d (false, false) = 1
    omega
  · change d (false, true) = 1
    omega
  · change d (true, false) = 1
    omega


theorem line_le_eigSpace {A : Matrix (Fin N) (Fin N) F} (hA : A * A = 1)
    {ℓ : Submodule F (Fin N → F)} (hℓ : finrank F ℓ = 1) (hinv : ∀ v ∈ ℓ, A *ᵥ v ∈ ℓ) :
    ℓ ≤ eigSpace A 1 ∨ ℓ ≤ eigSpace A (-1) := by
  obtain ⟨u, hu0, hu⟩ := finrank_eq_one_iff'.mp hℓ
  obtain ⟨c, hc⟩ := hu ⟨A *ᵥ (u : Fin N → F), hinv _ u.2⟩
  have hc' : A *ᵥ (u : Fin N → F) = c • (u : Fin N → F) := by
    simpa using (congrArg Subtype.val hc).symm
  have hu0' : (u : Fin N → F) ≠ 0 := by simpa using hu0
  have hcc : c * c = 1 := by
    have h1 : A *ᵥ (A *ᵥ (u : Fin N → F)) = (u : Fin N → F) := by
      rw [mulVec_mulVec, hA, Matrix.one_mulVec]
    rw [hc', Matrix.mulVec_smul, hc', smul_smul] at h1
    have h2 : (c * c - 1) • (u : Fin N → F) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    have := (smul_eq_zero.mp h2).resolve_right hu0'
    linear_combination this
  have hall : ∀ w ∈ ℓ, A *ᵥ w = c • w := by
    intro w hw
    obtain ⟨d, hd⟩ := hu ⟨w, hw⟩
    have hw' : w = d • (u : Fin N → F) := by simpa using (congrArg Subtype.val hd).symm
    rw [hw', Matrix.mulVec_smul, hc', smul_comm]
  rcases mul_self_eq_one_iff.mp hcc with h | h
  · left
    intro w hw
    rw [mem_eigSpace_one, hall w hw, h, one_smul]
  · right
    intro w hw
    rw [mem_eigSpace_neg_one, hall w hw, h, neg_one_smul]

@[expose] def chainEig (I : ℕ → Matrix (Fin N) (Fin N) F) (k j : ℕ) : Submodule F (Fin N → F) :=
  ⨅ a : Fin k, eigSpace (I a) (chainSign F a j)

theorem mem_chainEig {j : ℕ} {v : Fin N → F} :
    v ∈ chainEig I k j ↔ ∀ a : Fin k, I a *ᵥ v = chainSign F a j • v := by
  simp only [chainEig, Submodule.mem_iInf, mem_eigSpace]

theorem chainEig_le_eigSpace {j : ℕ} {a : ℕ} (ha : a < k) :
    chainEig I k j ≤ eigSpace (I a) (chainSign F a j) :=
  iInf_le (fun b : Fin k => eigSpace (I b) (chainSign F b j)) ⟨a, ha⟩

theorem IsInvChain.line_le (hI : IsInvChain I k)
    {ℓ : Submodule F (Fin N → F)} (hℓ : finrank F ℓ = 1) {c : ℕ} (hc : c < k)
    (hℓc : ℓ ≤ eigSpace (I c) (-1)) {b : ℕ} (hb : b < k) (hfar : c + 2 ≤ b ∨ b + 2 ≤ c)
    (hinv : ∀ v ∈ ℓ, I b *ᵥ v ∈ ℓ) : ℓ ≤ eigSpace (I b) 1 := by
  rcases line_le_eigSpace (hI.sq b hb) hℓ hinv with h | h
  · exact h
  · exfalso
    have hbot : eigSpace (I c) (-1) ⊓ eigSpace (I b) (-1) = ⊥ := by
      rcases hfar with hf | hf
      · exact hI.far c hc b hb hf
      · rw [inf_comm]; exact hI.far b hb c hc hf
    have : ℓ ≤ ⊥ := hbot ▸ le_inf hℓc h
    have h0 : finrank F ℓ = 0 := by
      rw [le_bot_iff.mp this]; simp
    omega


theorem chainSign_of_mem {a j : ℕ} (h : j = a ∨ j = a + 1) : chainSign F a j = -1 := by
  unfold chainSign; simp [h]

theorem chainSign_of_not_mem {a j : ℕ} (h : ¬ (j = a ∨ j = a + 1)) : chainSign F a j = 1 := by
  unfold chainSign; simp [h]

theorem IsInvChain.finrank_chainEig (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k)
    {j : ℕ} (hj : j ≤ k) : finrank F (chainEig I k j) = 1 := by
  have hinvV : ∀ b < k, ∀ c < k, ∀ s : F, ∀ v ∈ eigSpace (I c) s, I b *ᵥ v ∈ eigSpace (I c) s :=
    fun b hb c hc s v hv => mulVec_mem_eigSpace_of_comm (hI.comm b hb c hc) hv
  have hinv2 : ∀ b < k, ∀ c < k, ∀ d < k, ∀ s t : F, ∀ v ∈ (eigSpace (I c) s ⊓ eigSpace (I d) t :
      Submodule F (Fin N → F)), I b *ᵥ v ∈ (eigSpace (I c) s ⊓ eigSpace (I d) t :
      Submodule F (Fin N → F)) := fun b hb c hc d hd s t v hv =>
    ⟨hinvV b hb c hc s v hv.1, hinvV b hb d hd t v hv.2⟩
  rcases (by omega : j = 0 ∨ (1 ≤ j ∧ j < k) ∨ j = k) with h0 | ⟨hj1, hjk⟩ | hjk
  ·
    subst h0
    have hprof := (hI.pair_profile h2 (a := 0) (by omega)).2.1
    set ℓ : Submodule F (Fin N → F) := eigSpace (I 0) (-1) ⊓ eigSpace (I (0 + 1)) 1 with hℓ
    have hle : ∀ b < k, ℓ ≤ eigSpace (I b) (chainSign F b 0) := by
      intro b hb
      by_cases hb0 : b = 0
      · subst hb0
        rw [chainSign_of_mem (Or.inl rfl)]
        exact inf_le_left
      · by_cases hb1 : b = 1
        · subst hb1
          rw [chainSign_of_not_mem (by omega)]
          exact inf_le_right
        · rw [chainSign_of_not_mem (by omega)]
          exact hI.line_le hprof (c := 0) (by omega) inf_le_left hb (Or.inl (by omega))
            (hinv2 b hb 0 (by omega) (0 + 1) (by omega) _ _)
    have hge : chainEig I k 0 ≤ ℓ := by
      refine le_inf ?_ ?_
      · have := chainEig_le_eigSpace (I := I) (k := k) (j := 0) (a := 0) (by omega)
        rwa [chainSign_of_mem (Or.inl rfl)] at this
      · have := chainEig_le_eigSpace (I := I) (k := k) (j := 0) (a := 1) (by omega)
        rwa [chainSign_of_not_mem (by omega)] at this
    have : chainEig I k 0 = ℓ :=
      le_antisymm hge (le_iInf fun b => hle b b.2)
    rw [this]
    exact hprof
  ·
    obtain ⟨a, rfl⟩ : ∃ a, j = a + 1 := ⟨j - 1, by omega⟩
    have hprof := (hI.pair_profile h2 (a := a) (by omega)).1
    set ℓ : Submodule F (Fin N → F) := eigSpace (I a) (-1) ⊓ eigSpace (I (a + 1)) (-1) with hℓ
    have hle : ∀ b < k, ℓ ≤ eigSpace (I b) (chainSign F b (a + 1)) := by
      intro b hb
      by_cases hba : b = a
      · subst hba
        rw [chainSign_of_mem (Or.inr rfl)]
        exact inf_le_left
      · by_cases hba1 : b = a + 1
        · subst hba1
          rw [chainSign_of_mem (Or.inl rfl)]
          exact inf_le_right
        · rw [chainSign_of_not_mem (by omega)]
          by_cases hlt : a + 2 ≤ b
          · exact hI.line_le hprof (c := a) (by omega) inf_le_left hb (Or.inl hlt)
              (hinv2 b hb a (by omega) (a + 1) (by omega) _ _)
          · exact hI.line_le hprof (c := a + 1) hjk inf_le_right hb (Or.inr (by omega))
              (hinv2 b hb a (by omega) (a + 1) (by omega) _ _)
    have hge : chainEig I k (a + 1) ≤ ℓ := by
      refine le_inf ?_ ?_
      · have := chainEig_le_eigSpace (I := I) (k := k) (j := a + 1) (a := a) (by omega)
        rwa [chainSign_of_mem (Or.inr rfl)] at this
      · have := chainEig_le_eigSpace (I := I) (k := k) (j := a + 1) (a := a + 1) hjk
        rwa [chainSign_of_mem (Or.inl rfl)] at this
    have : chainEig I k (a + 1) = ℓ :=
      le_antisymm hge (le_iInf fun b => hle b b.2)
    rw [this]
    exact hprof
  ·
    subst hjk
    obtain ⟨a, rfl⟩ : ∃ a, j = a + 2 := ⟨j - 2, by omega⟩
    have hprof := (hI.pair_profile h2 (a := a) (by omega)).2.2
    set ℓ : Submodule F (Fin N → F) := eigSpace (I a) 1 ⊓ eigSpace (I (a + 1)) (-1) with hℓ
    have hle : ∀ b < a + 2, ℓ ≤ eigSpace (I b) (chainSign F b (a + 2)) := by
      intro b hb
      by_cases hba : b = a + 1
      · subst hba
        rw [chainSign_of_mem (Or.inr rfl)]
        exact inf_le_right
      · by_cases hba0 : b = a
        · subst hba0
          rw [chainSign_of_not_mem (by omega)]
          exact inf_le_left
        · rw [chainSign_of_not_mem (by omega)]
          exact hI.line_le hprof (c := a + 1) (by omega) inf_le_right hb (Or.inr (by omega))
            (hinv2 b hb a (by omega) (a + 1) (by omega) _ _)
    have hge : chainEig I (a + 2) (a + 2) ≤ ℓ := by
      refine le_inf ?_ ?_
      · have := chainEig_le_eigSpace (I := I) (k := a + 2) (j := a + 2) (a := a) (by omega)
        rwa [chainSign_of_not_mem (by omega)] at this
      · have := chainEig_le_eigSpace (I := I) (k := a + 2) (j := a + 2) (a := a + 1) (by omega)
        rwa [chainSign_of_mem (Or.inr rfl)] at this
    have : chainEig I (a + 2) (a + 2) = ℓ :=
      le_antisymm hge (le_iInf fun b => hle b b.2)
    rw [this]
    exact hprof


@[expose] def chainFix (I : ℕ → Matrix (Fin N) (Fin N) F) (k : ℕ) : Submodule F (Fin N → F) :=
  ⨅ a : Fin k, eigSpace (I a) 1

theorem mem_chainFix {v : Fin N → F} : v ∈ chainFix I k ↔ ∀ a : Fin k, I a *ᵥ v = v := by
  simp only [chainFix, Submodule.mem_iInf, mem_eigSpace_one]

@[expose] def chainFam (I : ℕ → Matrix (Fin N) (Fin N) F) (k : ℕ) :
    Option (Fin (k + 1)) → Submodule F (Fin N → F)
  | none => chainFix I k
  | some j => chainEig I k j

theorem iSup_maxGenEigenspace_eq_top_of_mul_self {V : Type*} [AddCommGroup V] [Module F V]
    (h2 : (2 : F) ≠ 0) {f : Module.End F V} (hf : f * f = 1) : ⨆ μ, f.maxGenEigenspace μ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hff : ∀ w, f (f w) = w := fun w => by simpa using LinearMap.congr_fun hf w
  have hsum : v = (2 : F)⁻¹ • (v + f v) + (2 : F)⁻¹ • (v - f v) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hsum]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.mem_iSup_of_mem 1 (Module.End.eigenspace_le_maxGenEigenspace ?_)
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_smul, map_add, hff, one_smul]; module
  · refine Submodule.mem_iSup_of_mem (-1) (Module.End.eigenspace_le_maxGenEigenspace ?_)
    rw [Module.End.mem_eigenspace_iff]
    simp only [map_smul, map_sub, hff, neg_one_smul]; module


@[expose] def chainChar (F : Type) [Field F] (k : ℕ) : Option (Fin (k + 1)) → (Fin k → F)
  | none => fun _ => 1
  | some j => fun a => chainSign F a j

theorem chainChar_injective (h2 : (2 : F) ≠ 0) (hk : 2 ≤ k) :
    Function.Injective (chainChar F k) := by
  have hne : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  rintro (_ | j) (_ | l) h
  · rfl
  · exfalso
    obtain ⟨a, ha, hja⟩ := exists_chainNeg (k := k) (j := l) (by omega) (by omega)
    have := congr_fun h ⟨a, ha⟩
    simp only [chainChar] at this
    rw [chainSign_of_mem hja] at this
    exact hne this.symm
  · exfalso
    obtain ⟨a, ha, hja⟩ := exists_chainNeg (k := k) (j := j) (by omega) (by omega)
    have := congr_fun h ⟨a, ha⟩
    simp only [chainChar] at this
    rw [chainSign_of_mem hja] at this
    exact hne this
  · by_contra hjl
    have hjl' : (j : ℕ) ≠ l := fun e => hjl (by rw [Fin.ext e])
    obtain ⟨a, ha, hsep⟩ := exists_chainSep hk (by omega : (j : ℕ) ≤ k) (by omega : (l : ℕ) ≤ k) hjl'
    have h' := congr_fun h ⟨a, ha⟩
    simp only [chainChar] at h'
    by_cases hjm : ((j : ℕ) = a ∨ (j : ℕ) = a + 1)
    · have hlm : ¬ ((l : ℕ) = a ∨ (l : ℕ) = a + 1) := fun hl => hsep ⟨fun _ => hl, fun _ => hjm⟩
      rw [chainSign_of_mem hjm, chainSign_of_not_mem hlm] at h'
      exact hne h'
    · have hlm : ((l : ℕ) = a ∨ (l : ℕ) = a + 1) := by
        by_contra hl
        exact hsep ⟨fun hj => absurd hj hjm, fun hl' => absurd hl' hl⟩
      rw [chainSign_of_not_mem hjm, chainSign_of_mem hlm] at h'
      exact hne h'.symm

theorem IsInvChain.iSupIndep (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k) :
    iSupIndep (chainFam I k) := by
  set f : Fin k → Module.End F (Fin N → F) := fun a => Matrix.toLin' (I a) with hf
  have hcomm : ∀ i j : Fin k, Commute (f i) (f j) := fun i j =>
    toLin'_mul_comm (hI.comm i i.2 j j.2)
  have hmaps : ∀ i j φ, Set.MapsTo (f i) ((f j).maxGenEigenspace φ) ((f j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f hmaps
  have hle : chainFam I k ≤
      (fun χ : Fin k → F => ⨅ a, (f a).maxGenEigenspace (χ a)) ∘ chainChar F k := by
    rintro (_ | j)
    · exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
    · exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace
  exact (hind.comp (chainChar_injective h2 hk)).mono hle


theorem IsInvChain.eigSpace_le_sup (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k) {a : ℕ}
    (ha : a < k) :
    eigSpace (I a) (-1) ≤ chainFam I k (some ⟨a, by omega⟩) ⊔ chainFam I k (some ⟨a + 1, by omega⟩) := by
  have hind := hI.iSupIndep h2 hk
  have hA : chainEig I k a ≤ eigSpace (I a) (-1) := by
    have := chainEig_le_eigSpace (I := I) (k := k) (j := a) (a := a) ha
    rwa [chainSign_of_mem (Or.inl rfl)] at this
  have hB : chainEig I k (a + 1) ≤ eigSpace (I a) (-1) := by
    have := chainEig_le_eigSpace (I := I) (k := k) (j := a + 1) (a := a) ha
    rwa [chainSign_of_mem (Or.inr rfl)] at this
  have hdisj : Disjoint (chainEig I k a) (chainEig I k (a + 1)) := by
    have hne : (some ⟨a, by omega⟩ : Option (Fin (k + 1))) ≠ some ⟨a + 1, by omega⟩ := by
      simp [Fin.ext_iff]
    exact hind.pairwiseDisjoint hne
  have hsup : chainEig I k a ⊔ chainEig I k (a + 1) ≤ eigSpace (I a) (-1) := sup_le hA hB
  have hfin : finrank F (chainEig I k a ⊔ chainEig I k (a + 1) : Submodule F (Fin N → F)) = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (chainEig I k a) (chainEig I k (a + 1))
    rw [hdisj.eq_bot, finrank_bot, hI.finrank_chainEig h2 hk (by omega),
      hI.finrank_chainEig h2 hk (by omega)] at h
    omega
  have hEq := Submodule.eq_of_le_of_finrank_eq hsup (by rw [hfin, hI.dim a ha])
  exact hEq.ge

theorem IsInvChain.iSup_eq_top (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k) :
    ⨆ o, chainFam I k o = ⊤ := by
  set f : Fin k → Module.End F (Fin N → F) := fun a => Matrix.toLin' (I a) with hf
  have hcomm : ∀ i j : Fin k, Commute (f i) (f j) := fun i j =>
    toLin'_mul_comm (hI.comm i i.2 j j.2)
  have hsq : ∀ a : Fin k, f a * f a = 1 := fun a => toLin'_mul_self (hI.sq a a.2)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    f (fun i j _ => hcomm i j) (fun a => iSup_maxGenEigenspace_eq_top_of_mul_self h2 (hsq a))
  rw [eq_top_iff, ← htop]
  refine iSup_le fun χ v hv => ?_
  rw [Submodule.mem_iInf] at hv
  have hform : v = 0 ∨ ∀ a : Fin k, I a *ᵥ v = v ∨ I a *ᵥ v = -v := by
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      intro a
      rcases mem_maxGenEigenspace_of_mul_self h2 (hsq a) (hv a) with h | h | h
      · left; simpa [hf] using h.2
      · right; simpa [hf] using h.2
      · exact absurd h hv0
  rcases hform with h0 | hall
  · rw [h0]; exact Submodule.zero_mem _
  · by_cases hfix : ∀ a : Fin k, I a *ᵥ v = v
    · exact Submodule.mem_iSup_of_mem none (mem_chainFix.mpr hfix)
    · push Not at hfix
      obtain ⟨a, ha⟩ := hfix
      have hneg : v ∈ eigSpace (I a) (-1) := by
        rw [mem_eigSpace_neg_one]
        exact (hall a).resolve_left ha
      have := hI.eigSpace_le_sup h2 hk a.2 hneg
      rcases Submodule.mem_sup.mp this with ⟨x, hx, y, hy, rfl⟩
      exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem (some ⟨a, by omega⟩) hx)
        (Submodule.mem_iSup_of_mem (some ⟨a + 1, by omega⟩) hy)

theorem IsInvChain.isInternal (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k) :
    DirectSum.IsInternal (chainFam I k) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨hI.iSupIndep h2 hk, hI.iSup_eq_top h2 hk⟩


@[expose] def negTail (F : Type) [Field F] (N k : ℕ) : Matrix (Fin N) (Fin N) F :=
  Matrix.diagonal fun j => if k < j.val then -1 else 1

theorem IsInvChain.finrank_chainFix (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k) :
    k + 1 ≤ N ∧ finrank F (chainFix I k) = N - (k + 1) := by
  have hint := hI.isInternal h2 hk
  have hsum := finrank_eq_sum_of_isInternal (chainFam I k) hint
  rw [Module.finrank_fin_fun, Fintype.sum_option] at hsum
  have h1 : ∀ j : Fin (k + 1), finrank F (chainFam I k (some j)) = 1 := fun j =>
    hI.finrank_chainEig h2 hk (by omega)
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  have : finrank F (chainFam I k none) = finrank F (chainFix I k) := rfl
  omega

theorem IsInvChain.exists_frame (h2 : (2 : F) ≠ 0) (hI : IsInvChain I k) (hk : 2 ≤ k) :
    k + 1 ≤ N ∧ ∃ P : SL(N, F),
      (∀ a < k, I a * (P : Matrix (Fin N) (Fin N) F) = P * negBlock F N a) ∧
      ∀ J : Matrix (Fin N) (Fin N) F, J * J = 1 → (∀ a < k, J * I a = I a * J) →
        eigSpace J (-1) ≤ chainFix I k → finrank F (eigSpace J (-1)) = N - (k + 1) →
          J * (P : Matrix (Fin N) (Fin N) F) = P * negTail F N k := by
  obtain ⟨hkN, hfix⟩ := hI.finrank_chainFix h2 hk
  refine ⟨hkN, ?_⟩
  have hint := hI.isInternal h2 hk
  let ε : Fin N → Option (Fin (k + 1)) := fun j =>
    if h : j.val < k + 1 then some ⟨j.val, h⟩ else none
  have hε : ∀ s, Nat.card {j // ε j = s} = finrank F (chainFam I k s) := by
    rintro (_ | l)
    · have e : {j : Fin N // ε j = none} ≃ {j : Fin N // k + 1 ≤ j.val} :=
        Equiv.subtypeEquivRight fun j => by
          simp only [ε]
          split_ifs with h <;> simp <;> omega
      rw [Nat.card_congr e, card_fin_val_ge hkN]
      exact hfix.symm
    · have e : {j : Fin N // ε j = some l} ≃ {j : Fin N // j.val = l.val} :=
        Equiv.subtypeEquivRight fun j => by
          simp only [ε]
          split_ifs with h
          · simp [Fin.ext_iff]
          · simp only [false_iff]
            omega
      rw [Nat.card_congr e, card_fin_val_eq (by omega)]
      exact (hI.finrank_chainEig h2 hk (by omega)).symm
  obtain ⟨P, hP⟩ := exists_sl_adapted (by omega) (chainFam I k) hint ε hε
  let col : Fin N → (Fin N → F) := fun j a => (P : Matrix (Fin N) (Fin N) F) a j
  have hcol : ∀ j, col j ∈ chainFam I k (ε j) := hP
  have hcol0 : ∀ j, col j ≠ 0 := by
    intro j h0
    have hinv := coe_inv_mul_coe P
    have hmv : (P : Matrix (Fin N) (Fin N) F) *ᵥ (Pi.single j (1 : F)) = col j := by
      ext a; simp [col]
    have h1 : (((P⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F) * (P : Matrix (Fin N) (Fin N) F)) *ᵥ
        (Pi.single j (1 : F)) = 0 := by
      rw [← mulVec_mulVec, hmv, h0, Matrix.mulVec_zero]
    rw [hinv, Matrix.one_mulVec] at h1
    have := congr_fun h1 j
    simp at this
  have hact : ∀ a < k, ∀ j : Fin N, I a *ᵥ col j = chainSign F a j.val • col j := by
    intro a ha j
    by_cases hj : j.val < k + 1
    · have h1 : col j ∈ chainEig I k j.val := by
        have := hcol j
        simp only [ε, hj, dite_true] at this
        exact this
      exact mem_chainEig.mp h1 ⟨a, ha⟩
    · have h1 : col j ∈ chainFix I k := by
        have := hcol j
        simp only [ε, hj, dite_false] at this
        exact this
      rw [mem_chainFix.mp h1 ⟨a, ha⟩, chainSign_of_not_mem (by omega), one_smul]
  refine ⟨P, ?_, ?_⟩
  · intro a ha
    ext x j
    have := congr_fun (hact a ha j) x
    rw [Matrix.mulVec] at this
    rw [negBlock_eq_diagonal, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, col] at this
    rw [this]
    unfold chainSign
    by_cases hj : (j : ℕ) = a ∨ (j : ℕ) = a + 1
    · have h1 : a ≤ (j : ℕ) ∧ (j : ℕ) < a + 2 := by omega
      simp only [hj, h1, and_self, ↓reduceIte]; ring
    · have h1 : ¬ (a ≤ (j : ℕ) ∧ (j : ℕ) < a + 2) := by omega
      simp only [hj, h1, ↓reduceIte]; ring
  · intro J hJ hcomm hneg hdim
    have hinvJ : ∀ j : Fin N, ∀ v ∈ chainFam I k (ε j), J *ᵥ v ∈ chainFam I k (ε j) := by
      intro j v hv
      by_cases hj : j.val < k + 1
      · have hv' : v ∈ chainEig I k j.val := by
          simp only [ε, hj, dite_true] at hv
          exact hv
        have : J *ᵥ v ∈ chainEig I k j.val := by
          rw [mem_chainEig] at hv' ⊢
          intro a
          rw [mulVec_mulVec, ← hcomm a a.2, ← mulVec_mulVec, hv' a, Matrix.mulVec_smul]
        simp only [ε, hj, dite_true]
        exact this
      · have hv' : v ∈ chainFix I k := by
          simp only [ε, hj, dite_false] at hv
          exact hv
        have : J *ᵥ v ∈ chainFix I k := by
          rw [mem_chainFix] at hv' ⊢
          intro a
          rw [mulVec_mulVec, ← hcomm a a.2, ← mulVec_mulVec, hv' a]
        simp only [ε, hj, dite_false]
        exact this
    have hJcol : ∀ j : Fin N, J *ᵥ col j = (if k < j.val then (-1 : F) else 1) • col j := by
      intro j
      by_cases hj : j.val < k + 1
      ·
        have hline : finrank F (chainEig I k j.val) = 1 := hI.finrank_chainEig h2 hk (by omega)
        have hmem : col j ∈ chainEig I k j.val := by
          have := hcol j
          simp only [ε, hj, dite_true] at this
          exact this
        have hinv : ∀ v ∈ chainEig I k j.val, J *ᵥ v ∈ chainEig I k j.val := by
          intro v hv
          have := hinvJ j v (by simp only [ε, hj, dite_true]; exact hv)
          simp only [ε, hj, dite_true] at this
          exact this
        rcases line_le_eigSpace hJ hline hinv with h | h
        · have h1 := mem_eigSpace_one.mp (h hmem)
          have hk' : ¬ k < j.val := by omega
          rw [h1]; simp [hk']
        · exfalso
          have h1 : col j ∈ chainFix I k := hneg (h hmem)
          obtain ⟨a, ha, hja⟩ := exists_chainNeg (k := k) (j := j.val) (by omega) (by omega)
          have e1 := mem_chainEig.mp hmem ⟨a, ha⟩
          have e2 := mem_chainFix.mp h1 ⟨a, ha⟩
          have e3 : col j = -col j := by
            have := e1
            simp only at this e2
            rw [e2, chainSign_of_mem hja, neg_one_smul] at this
            exact this
          apply hcol0 j
          have h2' : (2 : F) • col j = 0 := by
            rw [two_smul]
            nth_rewrite 1 [e3]
            exact neg_add_cancel _
          exact (smul_eq_zero.mp h2').resolve_left h2
      · have heq : eigSpace J (-1) = chainFix I k :=
          Submodule.eq_of_le_of_finrank_eq hneg (by rw [hdim, hfix])
        have hmem : col j ∈ chainFix I k := by
          have := hcol j
          simp only [ε, hj, dite_false] at this
          exact this
        rw [← heq] at hmem
        have hk' : k < j.val := by omega
        rw [mem_eigSpace_neg_one.mp hmem]; simp [hk']
    ext x j
    have := congr_fun (hJcol j) x
    rw [Matrix.mulVec] at this
    rw [negTail, Matrix.mul_diagonal]
    simp only [Matrix.mul_apply]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, col] at this
    rw [this]
    split_ifs <;> ring

end Chain

end CFSG.ClassicalInvolution.RouteD
