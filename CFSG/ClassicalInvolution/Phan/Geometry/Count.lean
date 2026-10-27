module

public import CFSG.ClassicalInvolution.Phan.Geometry.Points

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module

variable {K : Type*} [Field K] {σ : K ≃+* K} {m : ℕ}

section FieldCount

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem card_eq_card_fixed_sq [Finite K] :
    Nat.card K = Nat.card {c : K // σ c = c} ^ 2 := by
  obtain ⟨ω, hω⟩ := hσ.exists_ne
  have hω' : ω - σ ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω)
  let Φ : {c : K // σ c = c} × {c : K // σ c = c} → K := fun p => p.1 + p.2 * ω
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    simp only [Φ] at h
    have h2 := congrArg σ h
    simp only [map_add, map_mul, ha, hb, ha', hb'] at h2
    have h3 : (b - b') * (ω - σ ω) = 0 := by linear_combination h - h2
    have hbb : b = b' := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact sub_eq_zero.mp h4
      · exact absurd h4 hω'
    subst hbb
    have : a = a' := by linear_combination h
    subst this
    rfl
  have hsurj : Function.Surjective Φ := by
    intro x
    have hb : σ ((x - σ x) / (ω - σ ω)) = (x - σ x) / (ω - σ ω) := by
      rw [map_div₀, map_sub, map_sub, hσ.invol, hσ.invol]
      rw [← neg_sub x, ← neg_sub ω, neg_div_neg_eq]
    refine ⟨(⟨x - (x - σ x) / (ω - σ ω) * ω, ?_⟩, ⟨(x - σ x) / (ω - σ ω), hb⟩), ?_⟩
    · rw [map_sub, map_mul, hb]
      have : (x - σ x) / (ω - σ ω) * (ω - σ ω) = x - σ x := div_mul_cancel₀ _ hω'
      linear_combination this
    · simp only [Φ]
      ring
  rw [sq, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

theorem card_fixed_eq [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Nat.card {c : K // σ c = c} = q := by
  have h := card_eq_card_fixed_sq hσ (K := K)
  rw [hK] at h
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h).symm

theorem card_norm_fibre_eq [Finite K] {c d : K} (hc : σ c = c) (hc0 : c ≠ 0) (hd : σ d = d)
    (hd0 : d ≠ 0) :
    Nat.card {μ : K // σ μ * μ = c} = Nat.card {μ : K // σ μ * μ = d} := by
  have hfix : σ (d / c) = d / c := by rw [map_div₀, hc, hd]
  obtain ⟨ν, hν⟩ := hσ.exists_norm hfix
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hν
    exact div_ne_zero hd0 hc0 hν.symm
  have key : ∀ μ : K, σ (μ * ν) * (μ * ν) = (σ μ * μ) * (d / c) := by
    intro μ
    rw [map_mul]
    calc σ μ * σ ν * (μ * ν) = (σ μ * μ) * (σ ν * ν) := by ring
      _ = _ := by rw [hν]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight₀ ν hν0) fun μ => ?_)
  change σ μ * μ = c ↔ σ (μ * ν) * (μ * ν) = d
  rw [key]
  have hdc : d / c ≠ 0 := div_ne_zero hd0 hc0
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    have : (σ μ * μ) * (d / c) = c * (d / c) := by rw [h]; field_simp
    exact mul_right_cancel₀ hdc this

omit hσ in
theorem card_ne_zero_aux {α : Type*} [Zero α] [Finite α] :
    Nat.card {x : α // x ≠ 0} = Nat.card α - 1 := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

theorem card_norm_fibre [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) {c : K} (hc : σ c = c)
    (hc0 : c ≠ 0) : Nat.card {μ : K // σ μ * μ = c} = q + 1 := by
  classical
  have hF := card_fixed_eq hσ hK
  have hq1 : 1 < q := by
    have : Nontrivial {c : K // σ c = c} :=
      ⟨⟨⟨0, map_zero σ⟩, ⟨1, map_one σ⟩, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
    have := Finite.one_lt_card (α := {c : K // σ c = c})
    omega
  let e : {x : K // x ≠ 0} ≃
      Σ d : {d : {c : K // σ c = c} // d.1 ≠ 0}, {μ : K // σ μ * μ = d.1.1} :=
    { toFun := fun x => ⟨⟨⟨σ x.1 * x.1, hσ.norm_fixed x.1⟩,
        mul_ne_zero ((map_ne_zero σ).mpr x.2) x.2⟩, ⟨x.1, rfl⟩⟩
      invFun := fun y => ⟨y.2.1, by
        intro h0
        have := y.2.2
        rw [h0, map_zero, zero_mul] at this
        exact y.1.2 this.symm⟩
      left_inv := fun x => rfl
      right_inv := fun y => by
        obtain ⟨⟨⟨d, hd⟩, hd0⟩, ⟨μ, hμ⟩⟩ := y
        simp only at hμ
        subst hμ
        rfl }
  have hcard := Nat.card_congr e
  have hFix : Nat.card {d : {c : K // σ c = c} // d.1 ≠ 0} = q - 1 := by
    let _ : Fintype {c : K // σ c = c} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card, hF]
    have h1 : Fintype.card {d : {c : K // σ c = c} // d.1 = 0} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨⟨0, map_zero σ⟩, rfl⟩, fun x => Subtype.ext (Subtype.ext x.2)⟩
    rw [h1]
  rw [card_ne_zero_aux, hK] at hcard
  let _ : Fintype {d : {c : K // σ c = c} // d.1 ≠ 0} := Fintype.ofFinite _
  rw [Nat.card_sigma] at hcard
  have hterm : ∀ d : {d : {c : K // σ c = c} // d.1 ≠ 0},
      Nat.card {μ : K // σ μ * μ = d.1.1} = Nat.card {μ : K // σ μ * μ = c} :=
    fun d => card_norm_fibre_eq hσ d.1.2 d.2 hc hc0
  simp_rw [hterm] at hcard
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hFix, smul_eq_mul] at hcard
  have hq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [hq1.le, Nat.one_le_pow 2 q (by omega)]
    ring
  rw [hq] at hcard
  exact (Nat.eq_of_mul_eq_mul_left (by omega) hcard).symm

end FieldCount

section Plane

variable (hσ : IsUnitaryInvolution σ) {s t : Fin m → K}

@[expose] def pairPt (s t : Fin m → K) (μ : K) : Submodule K (Fin m → K) := K ∙ (s + μ • t)

include hσ in
theorem herm_pair (hst : herm σ s t = 0) (μ : K) :
    herm σ (s + μ • t) (s + μ • t) = herm σ s s + σ μ * μ * herm σ t t := by
  have hts : herm σ t s = 0 := (herm_eq_zero_iff hσ _ _).mp hst
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hst, hts]
  ring

theorem pairPt_injective (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) (ht : t ≠ 0) :
    Function.Injective (pairPt s t) := by
  intro μ ν h
  have h1 : s + ν • t ∈ K ∙ (s + μ • t) := by
    unfold pairPt at h
    rw [h]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  have h2 := congrArg (herm σ s) hc
  simp only [herm_add_right, herm_smul_right, hst, mul_zero, add_zero] at h2
  have hc1 : c = 1 := by
    have : (c - 1) * herm σ s s = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hs
  subst hc1
  have h3 : (μ - ν) • t = 0 := by
    rw [one_smul] at hc
    rw [sub_smul, sub_eq_zero]
    exact add_left_cancel hc
  rcases smul_eq_zero.mp h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h ht

theorem herm_add_smul_ne_zero (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) (μ : K) :
    s + μ • t ≠ 0 := by
  intro h
  have := congrArg (herm σ s) h
  rw [herm_add_right, herm_smul_right, hst, mul_zero, add_zero, herm_zero_right] at this
  exact hs this

theorem pts_pair (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) (ht : t ≠ 0) :
    pts (K ∙ s ⊔ K ∙ t) = insert (K ∙ t) (Set.range (pairPt s t)) := by
  ext L
  constructor
  · intro hL
    obtain ⟨v, hv0, hvP, rfl⟩ := mem_pts_iff.mp hL
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hvP
    obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.mp hw
    by_cases hx : x = 0
    · subst hx
      left
      have hy : y ≠ 0 := by
        rintro rfl
        simp at hv0
      simp only [zero_smul, zero_add]
      exact Submodule.span_singleton_smul_eq (IsUnit.mk0 y hy) t
    · right
      refine ⟨y / x, ?_⟩
      unfold pairPt
      have : x • s + y • t = x • (s + (y / x) • t) := by
        rw [smul_add, smul_smul, mul_div_cancel₀ _ hx]
      rw [this]
      exact (Submodule.span_singleton_smul_eq (IsUnit.mk0 x hx) _).symm
  · rintro (rfl | ⟨μ, rfl⟩)
    · exact span_singleton_mem_pts ht
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self t))
    · exact span_singleton_mem_pts (herm_add_smul_ne_zero hs hst μ)
        (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self s))
          (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self t))))

theorem span_notMem_range_pairPt (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) :
    K ∙ t ∉ Set.range (pairPt s t) := by
  rintro ⟨μ, hμ⟩
  have h1 : s + μ • t ∈ K ∙ t := by
    unfold pairPt at hμ
    rw [← hμ]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  have h2 := congrArg (herm σ s) hc
  rw [herm_smul_right, hst, mul_zero, herm_add_right, herm_smul_right, hst, mul_zero,
    add_zero] at h2
  exact hs h2.symm

include hσ in
theorem isoPts_pair_of_ne (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) (ht : t ≠ 0)
    (hβ : herm σ t t ≠ 0) :
    isoPts σ (K ∙ s ⊔ K ∙ t) =
      pairPt s t '' {μ | σ μ * μ = -(herm σ s s / herm σ t t)} := by
  ext L
  constructor
  · intro hL
    have hLp : L ∈ pts (K ∙ s ⊔ K ∙ t) := ⟨hL.1, hL.2.1⟩
    rw [pts_pair hs hst ht] at hLp
    rcases hLp with rfl | ⟨μ, rfl⟩
    · exact absurd (nondeg_span_singleton hβ) hL.2.2
    · refine ⟨μ, ?_, rfl⟩
      show σ μ * μ = -(herm σ s s / herm σ t t)
      have hzero : herm σ (s + μ • t) (s + μ • t) = 0 := by
        by_contra h
        exact hL.2.2 (nondeg_span_singleton h)
      rw [herm_pair hσ hst] at hzero
      field_simp
      linear_combination hzero
  · rintro ⟨μ, hμ, rfl⟩
    refine span_singleton_mem_isoPts (herm_add_smul_ne_zero hs hst μ) ?_
      (Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self s))
        (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self t))))
    rw [herm_pair hσ hst]
    have hμ' : σ μ * μ = -(herm σ s s / herm σ t t) := hμ
    rw [hμ']
    field_simp
    ring

include hσ in
theorem isoPts_pair_of_eq_zero (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) (ht : t ≠ 0)
    (hβ : herm σ t t = 0) : isoPts σ (K ∙ s ⊔ K ∙ t) = {K ∙ t} := by
  ext L
  constructor
  · intro hL
    have hLp : L ∈ pts (K ∙ s ⊔ K ∙ t) := ⟨hL.1, hL.2.1⟩
    rw [pts_pair hs hst ht] at hLp
    rcases hLp with rfl | ⟨μ, rfl⟩
    · rfl
    · exfalso
      have hzero : herm σ (s + μ • t) (s + μ • t) = 0 := by
        by_contra h
        exact hL.2.2 (nondeg_span_singleton h)
      rw [herm_pair hσ hst, hβ, mul_zero, add_zero] at hzero
      exact hs hzero
  · rintro rfl
    exact span_singleton_mem_isoPts ht hβ
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self t))

section Count

variable [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
include hK

theorem ncard_pts_pair (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) (ht : t ≠ 0) :
    (pts (K ∙ s ⊔ K ∙ t)).ncard = q ^ 2 + 1 := by
  rw [pts_pair hs hst ht, Set.ncard_insert_of_notMem (span_notMem_range_pairPt hs hst),
    ← Set.image_univ, Set.ncard_image_of_injective _ (pairPt_injective hs hst ht), Set.ncard_univ,
    hK]

include hσ in
theorem ncard_isoPts_pair_of_ne (hs : herm σ s s ≠ 0) (hst : herm σ s t = 0) (ht : t ≠ 0)
    (hβ : herm σ t t ≠ 0) : (isoPts σ (K ∙ s ⊔ K ∙ t)).ncard = q + 1 := by
  rw [isoPts_pair_of_ne hσ hs hst ht hβ,
    Set.ncard_image_of_injective _ (pairPt_injective hs hst ht)]
  have hfix : σ (-(herm σ s s / herm σ t t)) = -(herm σ s s / herm σ t t) := by
    rw [map_neg, map_div₀, herm_self_fixed σ hσ.invol, herm_self_fixed σ hσ.invol]
  have hne : -(herm σ s s / herm σ t t) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hs hβ)
  rw [← Nat.card_coe_set_eq]
  exact card_norm_fibre hσ hK hfix hne

end Count

end Plane

section Pair

variable (hσ : IsUnitaryInvolution σ)
include hσ

theorem exists_orth_pair {P : Submodule K (Fin m → K)} (hP : finrank K P ≤ 2) {s : Fin m → K}
    (hsP : s ∈ P) (hs : herm σ s s ≠ 0) :
    ∃ t : Fin m → K, herm σ s t = 0 ∧ P = K ∙ s ⊔ K ∙ t ∧ (finrank K P = 2 → t ≠ 0) := by
  have hfin := finrank_eq_inf_perp_add_one hσ hsP hs
  have hle : finrank K ↥(P ⊓ perp σ (K ∙ s)) ≤ 1 := by omega
  obtain ⟨t, ht⟩ := ((Submodule.finrank_le_one_iff_isPrincipal _).mp hle).principal
  have htP' : t ∈ P ⊓ perp σ (K ∙ s) := by rw [ht]; exact Submodule.mem_span_singleton_self t
  refine ⟨t, ?_, ?_, ?_⟩
  · exact (herm_eq_zero_iff hσ _ _).mp (mem_perp_span_singleton.mp htP'.2)
  · rw [← ht, span_sup_inf_perp hσ hsP hs]
  · intro h2 h0
    subst h0
    rw [Submodule.span_zero_singleton] at ht
    rw [ht, finrank_bot] at hfin
    omega

theorem ncard_isoPts_of_degenerate_plane {P : Submodule K (Fin m → K)} (hP : finrank K P = 2)
    (hdeg : ¬ Nondeg σ P) (hne : ∃ v ∈ P, herm σ v v ≠ 0) : (isoPts σ P).ncard = 1 := by
  obtain ⟨s, hsP, hs⟩ := hne
  obtain ⟨t, hst, hPeq, ht⟩ := exists_orth_pair hσ hP.le hsP hs
  have ht0 := ht hP
  have hβ : herm σ t t = 0 := by
    by_contra h
    rw [hPeq] at hdeg
    exact hdeg (Nondeg.sup_of_orth hσ (nondeg_span_singleton hs) (nondeg_span_singleton h)
      fun u hu w hw => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
        obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [herm_smul_left, herm_smul_right, hst, mul_zero, mul_zero])
  subst hPeq
  rw [isoPts_pair_of_eq_zero hσ hs hst ht0 hβ]
  simp

section Count

variable [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
include hK

theorem ncard_isoPts_le {P : Submodule K (Fin m → K)} (hP : finrank K P ≤ 2)
    (hne : ∃ v ∈ P, herm σ v v ≠ 0) : (isoPts σ P).ncard ≤ q + 1 := by
  obtain ⟨s, hsP, hs⟩ := hne
  obtain ⟨t, hst, hPeq, -⟩ := exists_orth_pair hσ hP hsP hs
  subst hPeq
  by_cases ht : t = 0
  · subst ht
    have : isoPts σ (K ∙ s ⊔ K ∙ (0 : Fin m → K)) = ∅ := by
      ext L
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨hLP, hL1, hnd⟩
      rw [Submodule.span_zero_singleton, sup_bot_eq] at hLP
      have hfs : finrank K (K ∙ s) = 1 := finrank_span_singleton (fun h => hs (by rw [h]; simp))
      have : L = K ∙ s := Submodule.eq_of_le_of_finrank_eq hLP (by rw [hL1, hfs])
      exact hnd (this ▸ nondeg_span_singleton hs)
    rw [this]
    simp
  · by_cases hβ : herm σ t t = 0
    · rw [isoPts_pair_of_eq_zero hσ hs hst ht hβ]
      simp
    · rw [ncard_isoPts_pair_of_ne hσ hK hs hst ht hβ]

theorem ncard_isoPts_of_nondeg_plane {P : Submodule K (Fin m → K)} (hP : finrank K P = 2)
    (hnd : Nondeg σ P) : (isoPts σ P).ncard = q + 1 := by
  have hne : P ≠ ⊥ := fun h => by rw [h, finrank_bot] at hP; omega
  obtain ⟨s, hsP, hs⟩ := exists_aniso_of_nondeg hσ hnd hne
  obtain ⟨t, hst, hPeq, ht⟩ := exists_orth_pair hσ hP.le hsP hs
  have ht0 := ht hP
  have hts : herm σ t s = 0 := (herm_eq_zero_iff hσ _ _).mp hst
  have hβ : herm σ t t ≠ 0 := by
    intro h0
    refine ht0 (hnd t (hPeq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self t))
      fun u hu => ?_)
    rw [hPeq] at hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu₁
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hu₂
    rw [herm_add_right, herm_smul_right, herm_smul_right, hts, h0, mul_zero, mul_zero, add_zero]
  subst hPeq
  exact ncard_isoPts_pair_of_ne hσ hK hs hst ht0 hβ

theorem ncard_pts_of_plane {P : Submodule K (Fin m → K)} (hP : finrank K P = 2)
    (hne : ∃ v ∈ P, herm σ v v ≠ 0) : (pts P).ncard = q ^ 2 + 1 := by
  obtain ⟨s, hsP, hs⟩ := hne
  obtain ⟨t, hst, hPeq, ht⟩ := exists_orth_pair hσ hP.le hsP hs
  subst hPeq
  exact ncard_pts_pair hK hs hst (ht hP)

theorem ncard_nsPts_of_nondeg_plane {P : Submodule K (Fin m → K)} (hP : finrank K P = 2)
    (hnd : Nondeg σ P) : (nsPts σ P).ncard = q ^ 2 - q := by
  have hne : P ≠ ⊥ := fun h => by rw [h, finrank_bot] at hP; omega
  have h1 := ncard_pts_of_plane hσ hK hP (exists_aniso_of_nondeg hσ hnd hne)
  have h2 := ncard_isoPts_of_nondeg_plane hσ hK hP hnd
  rw [pts_eq_union (σ := σ), Set.ncard_union_eq disjoint_nsPts_isoPts (Set.toFinite _)
    (Set.toFinite _), h2] at h1
  omega

end Count

end Pair

end CFSG.ClassicalInvolution.Phan
