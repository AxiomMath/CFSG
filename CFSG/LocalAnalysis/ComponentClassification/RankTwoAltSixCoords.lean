module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSixAut

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

section Act

variable {G : Type*} [Group G] {H : Subgroup G} {n : ℕ}

@[expose] noncomputable def actAut (ψ : H ≃* alternatingGroup (Fin n)) :
    normalizer (H : Set G) →* MulAut (alternatingGroup (Fin n)) :=
  (MulAut.congr ψ).toMonoidHom.comp H.normalizerMonoidHom

theorem actAut_apply (ψ : H ≃* alternatingGroup (Fin n)) (y : normalizer (H : Set G)) (h : H) :
    actAut ψ y (ψ h) =
      ψ ⟨(y : G) * h * (y : G)⁻¹, (mem_normalizer_iff.mp y.2 h).mp h.2⟩ := by
  simp only [actAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem actAut_eq_one_iff (ψ : H ≃* alternatingGroup (Fin n)) (y : normalizer (H : Set G)) :
    actAut ψ y = 1 ↔ (y : G) ∈ centralizer (H : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro b hb
    have hs := actAut_apply ψ y ⟨b, hb⟩
    rw [h1, MulAut.one_apply] at hs
    have h2 : (y : G) * b * (y : G)⁻¹ = b := (congrArg Subtype.val (ψ.injective hs)).symm
    calc b * (y : G) = ((y : G) * b * (y : G)⁻¹) * y := by rw [h2]
      _ = y * b := by group
  · intro h1
    refine MulEquiv.ext fun z => ?_
    obtain ⟨b, rfl⟩ := ψ.surjective z
    rw [actAut_apply, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    show (y : G) * b * (y : G)⁻¹ = b
    rw [← mem_centralizer_iff.mp h1 _ b.2, mul_inv_cancel_right]

theorem actAut_of_mem (ψ : H ≃* alternatingGroup (Fin n)) {y : normalizer (H : Set G)}
    (hy : (y : G) ∈ H) : actAut ψ y = MulAut.conj (ψ ⟨y, hy⟩) := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨b, rfl⟩ := ψ.surjective z
  rw [actAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Group G] in
theorem conj_eq_conjPerm (z : alternatingGroup (Fin n)) :
    MulAut.conj z = conjPerm n (z : Perm (Fin n)) := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [conjPerm_apply, MulAut.conj_apply]
  rfl

end Act

theorem odd_card_commutator_outer_six {L : Type*} [Group L] (e : L ≃* alternatingGroup (Fin 6)) :
    Odd (Nat.card (commutator (outerAutomorphismGroup L))) := by
  have hcomm := CatalogueSchreierAlternating.DegreeSix.outer_commutative
  have hL : IsMulCommutative (OuterAutomorphisms.Outer L) :=
    ⟨⟨fun a b => (OuterAutomorphisms.equivalence e).injective (by
      rw [map_mul, map_mul]
      exact hcomm.is_comm.comm _ _)⟩⟩
  have h : commutator (OuterAutomorphisms.Outer L) = ⊥ := (commutator_eq_bot_iff _).mpr hL
  show Odd (Nat.card (commutator (OuterAutomorphisms.Outer L)))
  rw [h, Subgroup.card_bot]
  exact odd_one

theorem eq_one_of_fix_four {c : Perm (Fin 6)} (hs : sign c = 1) (h0 : c 0 = 0) (h1 : c 1 = 1)
    (h2 : c 2 = 2) (h3 : c 3 = 3) : c = 1 := by
  have hv : ∀ v : Fin 6, v ≠ 0 → v ≠ 1 → v ≠ 2 → v ≠ 3 → v = 4 ∨ v = 5 := by decide
  have hc : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 3 → c i = 4 ∨ c i = 5 := by
    intro i hi0 hi1 hi2 hi3
    have e0 : c i ≠ c 0 := c.injective.ne hi0
    have e1 : c i ≠ c 1 := c.injective.ne hi1
    have e2 : c i ≠ c 2 := c.injective.ne hi2
    have e3 : c i ≠ c 3 := c.injective.ne hi3
    rw [h0] at e0
    rw [h1] at e1
    rw [h2] at e2
    rw [h3] at e3
    exact hv _ e0 e1 e2 e3
  have hc4 := hc 4 (by decide) (by decide) (by decide) (by decide)
  have hc5 := hc 5 (by decide) (by decide) (by decide) (by decide)
  have h45 : c 4 ≠ c 5 := c.injective.ne (by decide)
  rcases hc4 with h4 | h4
  · have h5 : c 5 = 5 := by
      rcases hc5 with h5 | h5
      · exact absurd (h4.trans h5.symm) h45
      · exact h5
    refine Equiv.ext fun i => ?_
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · have h5 : c 5 = 4 := by
      rcases hc5 with h5 | h5
      · exact h5
      · exact absurd (h4.trans h5.symm) h45
    have hsw : c = swap 4 5 := by
      refine Equiv.ext fun i => ?_
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
    rw [hsw, sign_swap (by decide)] at hs
    exact absurd hs (by decide)

theorem eq_one_or_inV0_of_commute {c : Perm (Fin 6)} (hs : sign c = 1)
    (h1 : c * (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 * c)
    (h2 : c * (swap 0 2 * swap 1 3) = swap 0 2 * swap 1 3 * c) : c = 1 ∨ InV0 c := by
  have h46 : 4 ≤ 6 := by decide
  have e1 : (viaEmbeddingHom (fourEmb h46) (swap 0 1 * swap 2 3) : Perm (Fin 6)) =
      swap 0 1 * swap 2 3 := by
    rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    rfl
  have e2 : (viaEmbeddingHom (fourEmb h46) (swap 0 2 * swap 1 3) : Perm (Fin 6)) =
      swap 0 2 * swap 1 3 := by
    rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap]
    rfl
  obtain ⟨k, hk, hck⟩ := exists_kleinFour_of_commute (fourEmb h46) (φ := c)
    (by rw [Commute, SemiconjBy, e1]; exact h1) (by rw [Commute, SemiconjBy, e2]; exact h2)
  set v := viaEmbeddingHom (fourEmb h46) k with hv
  have hvV : v ∈ rootVP 6 := by
    rw [rootVP_eq h46]
    exact ⟨k, hk, rfl⟩
  have hfix : ∀ j : Fin 4, (v⁻¹ * c) (fourEmb h46 j) = fourEmb h46 j := by
    intro j
    rw [Perm.mul_apply, hck, Perm.inv_eq_iff_eq, hv, viaEmbeddingHom_apply_image]
  have hsv : sign v = 1 := by
    rw [hv, sign_viaEmbeddingHom]
    exact kleinFour_le_alternatingGroup hk
  have hone : v⁻¹ * c = 1 := eq_one_of_fix_four
    (by rw [Perm.sign_mul, Perm.sign_inv, hsv, hs]; rfl) (hfix 0) (hfix 1) (hfix 2) (hfix 3)
  rw [← (inv_mul_eq_one.mp hone)]
  exact mem_rootVP_six_iff.mp hvV

theorem mem_rootV_six_iff {z : alternatingGroup (Fin 6)} :
    z ∈ rootV 6 ↔ (z : Perm (Fin 6)) = 1 ∨ InV0 (z : Perm (Fin 6)) := by
  rw [← mem_rootVP_six_iff, rootVP_eq (by decide), mem_rootV_iff (by decide), Subgroup.mem_map]

theorem exists_two_ne_one {M : Type*} [Group M] {E : Subgroup M} (hE : 4 ≤ Nat.card E) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype E := Fintype.ofFinite E
  have hcard : 4 ≤ Fintype.card E := by rw [← Nat.card_eq_fintype_card]; exact hE
  obtain ⟨a, ha⟩ : ∃ a : E, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card E ≤ 1 := Fintype.card_le_one_iff.mpr fun x y => by rw [h x, h y]
    omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : E, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset E) ⊆ {1, a} := fun x _ => by
      by_cases hx : x = 1
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h2' := Finset.card_insert_le (1 : E) {a}
    rw [Finset.card_singleton] at h2'
    omega
  exact ⟨a, a.2, b, b.2, fun h => ha (Subtype.ext h), fun h => hb1 (Subtype.ext h),
    fun h => hba (Subtype.ext h).symm⟩

section PartB

variable {G : Type} [Group G] {A R T : Subgroup G} {g : G}

theorem eq_one_of_mem_centralizer_six (e : ↥A ≃* alternatingGroup (Fin 6)) {z : G} (hz : z ∈ A)
    (hzc : z ∈ Subgroup.centralizer (A : Set G)) : z = 1 := by
  have hcen : e ⟨z, hz⟩ ∈ center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff]
    intro w
    obtain ⟨a, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.mp hzc a a.2
  rw [CatalogueSchreierAlternating.DegreeSix.center_eq_bot, mem_bot] at hcen
  have := e.injective (hcen.trans (map_one e).symm)
  exact congrArg Subtype.val this

variable [Finite G]

theorem exists_coords_six (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (h2 : Asc76Theorem2) (e : ↥A ≃* alternatingGroup (Fin 6)) :
    T ≤ A ∧ ∃ ψ : ↥A ≃* alternatingGroup (Fin 6), ∀ a : ↥A, (a : G) ∈ T ↔ ψ a ∈ rootV 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hTab, hT4, -, -⟩, -, -, -⟩ := Lemma39.lemma39_three h4 h32 h34 h2 hc.hyp
    hc.not_mem hc.sylowT hc.le_normalizer (odd_card_commutator_outer_six e)
  have hRK := R_le_centralizer hc
  have hcommAR : ∀ {p r : G}, p ∈ A → r ∈ R → p * r = r * p := fun hp hr =>
    mem_centralizer_iff.mp (hRK hr) _ hp
  have huniq : ∀ (p p' : ↥A) {r r' : G}, r ∈ R → r' ∈ R → (p : G) * r = p' * r' → p = p' := by
    intro p p' r r' hr hr' h
    have hz : (p' : G)⁻¹ * p = r' * r⁻¹ := by
      calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * r) * r⁻¹ := by group
        _ = (p' : G)⁻¹ * (p' * r') * r⁻¹ := by rw [h]
        _ = r' * r⁻¹ := by group
    have h1 := eq_one_of_mem_centralizer_six e (mul_mem (inv_mem p'.2) p.2)
      (by rw [hz]; exact hRK (mul_mem hr' (inv_mem hr)))
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hpart : ∀ t : ↥T, ∃ p : ↥A, ∃ r ∈ R, (t : G) = p * r := fun t => by
    obtain ⟨p, hp, r, hr, he⟩ := exists_mul_of_mem_T hc h32 h4 h34 t.2
    exact ⟨⟨p, hp⟩, r, hr, he⟩
  choose pf rf hrf hpf using hpart
  let π : ↥T →* ↥A :=
    { toFun := pf
      map_one' := huniq _ _ (hrf 1) (one_mem R) (by rw [← hpf]; simp)
      map_mul' := fun t t' => huniq _ _ (hrf (t * t')) (mul_mem (hrf t) (hrf t')) (by
        calc ((pf (t * t') : ↥A) : G) * rf (t * t') = (t : G) * t' := by rw [← hpf]; rfl
          _ = (pf t : G) * (rf t * (pf t' : G)) * rf t' := by rw [hpf t, hpf t']; group
          _ = (pf t : G) * ((pf t' : G) * rf t) * rf t' := by
            rw [← hcommAR (pf t').2 (hrf t)]
          _ = ((pf t * pf t' : ↥A) : G) * (rf t * rf t') := by
            simp only [Subgroup.coe_mul]
            group) }
  have hπ : ∀ t : ↥T, (t : G) = π t * rf t := hpf
  have hπinj : Function.Injective π := (injective_iff_map_eq_one π).mpr fun t ht => by
    have h1 : (t : G) = rf t := by rw [hπ t, ht]; simp
    have hmem : (t : G) ∈ R ⊓ T := Subgroup.mem_inf.mpr ⟨by rw [h1]; exact hrf t, t.2⟩
    rw [hc.inf_eq_bot, mem_bot] at hmem
    exact Subtype.ext hmem
  set φ : ↥T →* alternatingGroup (Fin 6) := e.toMonoidHom.comp π with hφ
  have hφinj : Function.Injective φ := e.injective.comp hπinj
  have hPcard : 4 ≤ Nat.card φ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
    exact hT4
  have hP2 : ∀ z ∈ φ.range, z * z = 1 := by
    rintro _ ⟨t, rfl⟩
    rw [← map_mul]
    have : t * t = 1 := Subtype.ext (by have := hTab.2 _ t.2; rwa [sq] at this)
    rw [this, map_one]
  have hPcomm : ∀ x ∈ φ.range, ∀ y ∈ φ.range, x * y = y * x := by
    rintro _ ⟨t, rfl⟩ _ ⟨t', rfl⟩
    rw [← map_mul, ← map_mul, hTab.1.is_comm.comm t t']
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two_ne_one hPcard
  obtain ⟨φ0, hφa, hφb⟩ := exists_mulAut_pair (hP2 a ha) (hP2 b hb) ha1 hb1 hab
    (hPcomm a ha b hb)
  set ψ := e.trans φ0 with hψ
  have hψπ : ∀ t : ↥T, ψ (π t) = φ0 (φ t) := fun t => rfl
  have hne : (φ0 a : Perm (Fin 6)) ≠ φ0 b := fun h => hab (φ0.injective (Subtype.ext h))
  have hPV : ∀ z ∈ φ.range, (φ0 z : Perm (Fin 6)) = 1 ∨ InV0 (φ0 z : Perm (Fin 6)) := by
    intro z hz
    have hcz : ∀ w ∈ φ.range, (φ0 z : Perm (Fin 6)) * φ0 w = φ0 w * φ0 z := fun w hw => by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hPcomm z hz w hw]
    have hcu : ∀ u, InV0 u → (φ0 z : Perm (Fin 6)) * u = u * φ0 z := by
      intro u hu
      rcases inV0_cover hφa hφb hne hu with rfl | rfl | rfl
      · exact hcz a ha
      · exact hcz b hb
      · rw [← Subgroup.coe_mul, ← map_mul]
        exact hcz _ (mul_mem ha hb)
    exact eq_one_or_inV0_of_commute (mem_alternatingGroup.mp (φ0 z).2) (hcu _ (Or.inl rfl))
      (hcu _ (Or.inr (Or.inl rfl)))
  have hVP : ∀ u, InV0 u → ∃ z ∈ φ.range, (φ0 z : Perm (Fin 6)) = u := by
    intro u hu
    rcases inV0_cover hφa hφb hne hu with h | h | h
    · exact ⟨a, ha, h.symm⟩
    · exact ⟨b, hb, h.symm⟩
    · exact ⟨a * b, mul_mem ha hb, by rw [map_mul]; exact h.symm⟩
  have hu1 : InV0 (swap 0 1 * swap 2 3 : Perm (Fin 6)) := Or.inl rfl
  have hu2 : InV0 (swap 0 2 * swap 1 3 : Perm (Fin 6)) := Or.inr (Or.inl rfl)
  obtain ⟨_, ⟨t₁, rfl⟩, ht₁⟩ := hVP _ hu1
  obtain ⟨_, ⟨t₂, rfl⟩, ht₂⟩ := hVP _ hu2
  rw [← hψπ] at ht₁ ht₂
  set p₁ := π t₁ with hp₁
  set p₂ := π t₂ with hp₂
  set x₁ := ψ.symm ⟨swap 0 1 * swap 4 5, mem_alternatingGroup.mpr (by decide)⟩ with hx₁
  set x₂ := ψ.symm ⟨swap 0 2 * swap 4 5, mem_alternatingGroup.mpr (by decide)⟩ with hx₂
  have hψx₁ : (ψ x₁ : Perm (Fin 6)) = swap 0 1 * swap 4 5 := by
    rw [hx₁, MulEquiv.apply_symm_apply]
  have hψx₂ : (ψ x₂ : Perm (Fin 6)) = swap 0 2 * swap 4 5 := by
    rw [hx₂, MulEquiv.apply_symm_apply]
  have hrel : ∀ (x y z : ↥A), (ψ x : Perm (Fin 6)) * ψ y * (ψ x : Perm (Fin 6))⁻¹ = ψ z →
      (x : G) * y * (x : G)⁻¹ = z := by
    intro x y z h
    have : x * y * x⁻¹ = z := ψ.injective (Subtype.ext (by simpa [map_mul, map_inv] using h))
    exact congrArg Subtype.val this
  have c11 : (x₁ : G) * p₁ * (x₁ : G)⁻¹ = p₁ := hrel _ _ _ (by
    rw [hψx₁, ht₁]
    decide)
  have c12 : (x₁ : G) * p₂ * (x₁ : G)⁻¹ = p₁ * p₂ := by
    have := hrel x₁ p₂ (p₁ * p₂) (by
      rw [hψx₁, map_mul, Subgroup.coe_mul, ht₁, ht₂]
      decide)
    rw [this, Subgroup.coe_mul]
  have c22 : (x₂ : G) * p₂ * (x₂ : G)⁻¹ = p₂ := hrel _ _ _ (by
    rw [hψx₂, ht₂]
    decide)
  have c21 : (x₂ : G) * p₁ * (x₂ : G)⁻¹ = p₂ * p₁ := by
    have := hrel x₂ p₁ (p₂ * p₁) (by
      rw [hψx₂, map_mul, Subgroup.coe_mul, ht₁, ht₂]
      decide)
    rw [this, Subgroup.coe_mul]
  have hne1 : ∀ t : ↥T, (ψ (π t) : Perm (Fin 6)) ≠ 1 → (t : G) ≠ 1 := by
    intro t h ht
    apply h
    rw [show t = 1 from Subtype.ext ht, map_one, map_one]
    rfl
  have ht₁1 := hne1 t₁ (by rw [ht₁]; decide)
  have ht₂1 := hne1 t₂ (by rw [ht₂]; decide)
  have hr₁ := eq_one_of_conj hc h32 t₁.2 t₂.2 (hrf t₁) (hrf t₂) (hπ t₁) (hπ t₂) x₁.2 c11 c12 ht₁1
  have hr₂ := eq_one_of_conj hc h32 t₂.2 t₁.2 (hrf t₂) (hrf t₁) (hπ t₂) (hπ t₁) x₂.2 c22 c21 ht₂1
  have hp₁T : (p₁ : G) ∈ T := by
    have h := hπ t₁
    rw [hr₁, mul_one] at h
    rw [← h]
    exact t₁.2
  have hp₂T : (p₂ : G) ∈ T := by
    have h := hπ t₂
    rw [hr₂, mul_one] at h
    rw [← h]
    exact t₂.2
  have hπT : ∀ t : ↥T, ((π t : ↥A) : G) ∈ T := by
    intro t
    rcases hPV (φ t) ⟨t, rfl⟩ with h | h
    · rw [← hψπ] at h
      have : π t = 1 := ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
      rw [this]
      exact one_mem T
    · rw [← hψπ] at h
      have h12 : (swap 0 1 * swap 2 3 : Perm (Fin 6)) ≠ swap 0 2 * swap 1 3 := by decide
      rcases inV0_cover hu1 hu2 h12 h with h' | h' | h'
      · rw [← ht₁] at h'
        rw [ψ.injective (Subtype.ext h')]
        exact hp₁T
      · rw [← ht₂] at h'
        rw [ψ.injective (Subtype.ext h')]
        exact hp₂T
      · rw [← ht₁, ← ht₂, ← Subgroup.coe_mul, ← map_mul] at h'
        rw [ψ.injective (Subtype.ext h'), Subgroup.coe_mul]
        exact mul_mem hp₁T hp₂T
  have hTA : T ≤ A := by
    intro t ht
    have hr1 : rf ⟨t, ht⟩ = 1 := by
      have hmem : rf ⟨t, ht⟩ ∈ R ⊓ T := Subgroup.mem_inf.mpr ⟨hrf _, by
        have e' : rf ⟨t, ht⟩ = ((π ⟨t, ht⟩ : ↥A) : G)⁻¹ * t := by
          rw [eq_inv_mul_iff_mul_eq]
          exact (hπ ⟨t, ht⟩).symm
        rw [e']
        exact mul_mem (inv_mem (hπT _)) ht⟩
      rwa [hc.inf_eq_bot, mem_bot] at hmem
    have e' : t = ((π ⟨t, ht⟩ : ↥A) : G) := by
      have := hπ ⟨t, ht⟩
      rw [hr1, mul_one] at this
      exact this
    rw [e']
    exact (π ⟨t, ht⟩).2
  have hπself : ∀ t : ↥T, ((π t : ↥A) : G) = t := by
    intro t
    have := huniq (π t) ⟨t, hTA t.2⟩ (hrf t) (one_mem R) (by rw [← hπ t, mul_one])
    rw [this]
  refine ⟨hTA, ψ, fun a => ⟨fun haT => ?_, fun haV => ?_⟩⟩
  · have h1 : π ⟨a, haT⟩ = a := Subtype.ext (hπself ⟨a, haT⟩)
    rw [mem_rootV_six_iff, ← h1, hψπ]
    exact hPV _ ⟨_, rfl⟩
  · rw [mem_rootV_six_iff] at haV
    rcases haV with h | h
    · have : a = 1 := ψ.injective (Subtype.ext (by rw [h, map_one]; rfl))
      rw [this]
      exact one_mem T
    · obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hVP _ h
      rw [← hψπ] at ht
      have : π t = a := ψ.injective (Subtype.ext ht)
      rw [← this, hπself t]
      exact t.2

end PartB

section Pair

variable {G : Type} [Group G]

@[expose] def conjEquiv (A : Subgroup G) (g : G) : ↥(rightConjugate A g) ≃* ↥A where
  toFun b := ⟨g * b * g⁻¹, (mem_rightConjugate_iff A g b).mp b.2⟩
  invFun a := ⟨g⁻¹ * a * g, (mem_rightConjugate_iff A g _).mpr (by
    rw [show g * (g⁻¹ * (a : G) * g) * g⁻¹ = a by group]
    exact a.2)⟩
  left_inv b := Subtype.ext (show g⁻¹ * (g * (b : G) * g⁻¹) * g = b by group)
  right_inv a := Subtype.ext (show g * (g⁻¹ * (a : G) * g) * g⁻¹ = a by group)
  map_mul' x y := Subtype.ext
    (show g * ((x : G) * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group)

theorem conjEquiv_apply (A : Subgroup G) (g : G) (b : ↥(rightConjugate A g)) :
    ((conjEquiv A g b : ↥A) : G) = g * b * g⁻¹ :=
  rfl

theorem conjEquiv_symm_apply (A : Subgroup G) (g : G) (a : ↥A) :
    (((conjEquiv A g).symm a : ↥(rightConjugate A g)) : G) = g⁻¹ * a * g :=
  rfl

structure SixPair (A R T : Subgroup G) (g : G) where
  ψA : ↥A ≃* alternatingGroup (Fin 6)
  ψB : ↥(rightConjugate A g) ≃* alternatingGroup (Fin 6)
  le_A : T ≤ A
  le_B : R ≤ rightConjugate A g
  mem_T : ∀ a : ↥A, (a : G) ∈ T ↔ ψA a ∈ rootV 6
  mem_R : ∀ b : ↥(rightConjugate A g), (b : G) ∈ R ↔ ψB b ∈ rootV 6

variable {A R T : Subgroup G} {g : G}

theorem exists_sixPair [Finite G] (hc : Sec3 A R T g)
    (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) (h2 : Asc76Theorem2)
    (e : ↥A ≃* alternatingGroup (Fin 6)) : Nonempty (SixPair A R T g) := by
  obtain ⟨hTA, ψ₁, h₁⟩ := exists_coords_six hc h32 h4 h34 h2 e
  obtain ⟨hRA, ψ₂, h₂⟩ := exists_coords_six hc.swap h32 h4 h34 h2 e
  refine ⟨⟨ψ₁, (conjEquiv A g).trans ψ₂, hTA, fun r hr => ?_, h₁, fun b => ?_⟩⟩
  · rw [mem_rightConjugate_iff]
    apply hRA
    rw [mem_rightConjugate_iff, show g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r by group]
    exact hr
  · rw [MulEquiv.trans_apply, ← h₂, conjEquiv_apply, mem_rightConjugate_iff,
      show g⁻¹ * (g * (b : G) * g⁻¹) * g⁻¹⁻¹ = b by group]

namespace SixPair

@[expose] def swap (np : SixPair A R T g) :
    SixPair A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) g⁻¹ where
  ψA := (conjEquiv A g).symm.trans np.ψB
  ψB := (conjEquiv A g⁻¹).trans np.ψA
  le_A := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have := (mem_rightConjugate_iff A g _).mp (np.le_B hx)
    rwa [show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group] at this
  le_B := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx ⊢
    exact np.le_A hx
  mem_T a := by
    rw [MulEquiv.trans_apply, ← np.mem_R, conjEquiv_symm_apply, mem_rightConjugate_iff, inv_inv]
  mem_R b := by
    rw [MulEquiv.trans_apply, ← np.mem_T, conjEquiv_apply, mem_rightConjugate_iff]

theorem swap_ψA (np : SixPair A R T g) (a : ↥A) :
    np.swap.ψA a = np.ψB ((conjEquiv A g).symm a) :=
  rfl

theorem swap_ψB (np : SixPair A R T g) (b : ↥(rightConjugate A g⁻¹)) :
    np.swap.ψB b = np.ψA (conjEquiv A g⁻¹ b) :=
  rfl

end SixPair

end Pair

end CFSG.ComponentClassification.RankTwoAlt
