module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13L32Set

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
  CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inv_mul_mul_mem_oddCoreIn {D : Subgroup G} {o v : G} (ho : o ∈ oddCoreIn D)
    (hv : v ∈ D) : v⁻¹ * o * v ∈ oddCoreIn D := by
  have h := (mem_normalizer_iff.mp (le_normalizer_map_subtype' (pPrimeCore 2 ↥D) (inv_mem hv))
    o).mp ho
  rwa [inv_inv] at h

theorem kStarKernel_le_normalizer {N K₀ : Subgroup G} (hK₀ : K₀ ∈ kStarComponents N) :
    kStarKernel N ≤ normalizer (K₀ : Set G) := by
  intro g hg
  obtain ⟨hgN, hgQ⟩ := mem_inf.mp hg
  have hK₀D : K₀ ≤ solomonKStarOf N := le_iSup₂_of_le K₀ hK₀ le_rfl
  have hK₀c : IsTwoComponentIn K₀ (solomonKStarOf N) :=
    isTwoComponentIn_of_le hK₀.1 hK₀D (solomonKStarOf_le N)
  have hOD : oddCoreIn K₀ ≤ oddCoreIn (solomonKStarOf N) := oddCoreIn_le_of_isTwoComponentIn hK₀c
  by_contra hgK
  have hNφ : N.map (MulAut.conj g⁻¹).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer (inv_mem hgN))
  have hK₁ : K₀.map (MulAut.conj g⁻¹).toMonoidHom ∈ kStarComponents N := by
    have h := isTwoComponentIn_map (MulAut.conj g⁻¹) hK₀.1
    rw [hNφ] at h
    exact ⟨h, map_mem_solomonKStar _ hK₀.2⟩
  have hne : K₀ ≠ K₀.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro h
    apply hgK
    have h1 : g⁻¹ ∈ normalizer (K₀ : Set G) := mem_normalizer_iff_map_conj_eq.mpr h.symm
    simpa using inv_mem h1
  have hK₁Q : K₀.map (MulAut.conj g⁻¹).toMonoidHom ≤ coreActionKernel K₀ :=
    GSThmB.B5a.le_coreActionKernel_of_ne hK₀.1.1 hK₁.1.1 hK₀.1.2 hK₁.1.2 hne
  have hcomm : ⁅K₀, K₀⁆ ≤ oddCoreIn K₀ := by
    refine commutator_le.mpr fun a ha c hc => ?_
    have hoD : (c⁻¹)⁻¹ * g⁻¹ * c⁻¹ * g ∈ oddCoreIn (solomonKStarOf N) :=
      hgQ.2 c⁻¹ (hK₀D (inv_mem hc))
    have hy : g⁻¹ * c⁻¹ * g ∈ K₀.map (MulAut.conj g⁻¹).toMonoidHom :=
      ⟨c⁻¹, inv_mem hc, by simp⟩
    have h1 : (a⁻¹)⁻¹ * (g⁻¹ * c⁻¹ * g)⁻¹ * a⁻¹ * (g⁻¹ * c⁻¹ * g) ∈
        oddCoreIn (solomonKStarOf N) := hOD ((hK₁Q hy).2 a⁻¹ (inv_mem ha))
    have h2 : ⁅a, c⁆ = ((a⁻¹)⁻¹ * ((c⁻¹)⁻¹ * g⁻¹ * c⁻¹ * g) * a⁻¹) *
        ((a⁻¹)⁻¹ * (g⁻¹ * c⁻¹ * g)⁻¹ * a⁻¹ * (g⁻¹ * c⁻¹ * g)) *
        ((c⁻¹)⁻¹ * g⁻¹ * c⁻¹ * g)⁻¹ := by
      rw [commutatorElement_def]
      group
    have h3 : ⁅a, c⁆ ∈ oddCoreIn (solomonKStarOf N) := by
      rw [h2]
      exact mul_mem (mul_mem (inv_mul_mul_mem_oddCoreIn hoD (hK₀D (inv_mem ha))) h1)
        (inv_mem hoD)
    have h4 : ⁅a, c⁆ ∈ K₀ := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hc) (inv_mem ha)) (inv_mem hc)
    exact oddCoreIn_inf_le hK₀D (mem_inf.mpr ⟨h3, h4⟩)
  have hperf : ⁅K₀, K₀⁆ = K₀ := UnbalancedCorr.commutator_eq_of_isPComponent hK₀.1.1 hK₀.1.2
  obtain ⟨t, htK, ht2⟩ := exists_orderOf_eq_two_of_pRank
    ((by norm_num : 1 ≤ 2).trans (two_le_pRank_of_mem_solomonKStar hK₀.2))
  have htK' : t ∈ ⁅K₀, K₀⁆ := by rw [hperf]; exact htK
  have h1 := orderOf_dvd_natCard (⟨t, hcomm htK'⟩ : oddCoreIn K₀)
  rw [Subgroup.orderOf_mk, ht2] at h1
  exact absurd (Nat.Coprime.eq_one_of_dvd (coprime_card_oddCoreIn K₀) h1) (by norm_num)

theorem kStarKernel_le_coreActionKernel {N K₀ : Subgroup G} (hK₀ : K₀ ∈ kStarComponents N) :
    kStarKernel N ≤ coreActionKernel K₀ := fun _ hg =>
  FooteLit.mem_coreActionKernel_of_le (le_iSup₂_of_le K₀ hK₀ le_rfl)
    (kStarKernel_le_normalizer hK₀ hg) (mem_inf.mp hg).2

theorem le_normalizer_kStarKernel (N : Subgroup G) :
    N ≤ normalizer (kStarKernel N : Set G) := by
  intro s hs
  have hNs : N.map (MulAut.conj s).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer hs)
  rw [mem_normalizer_iff_map_conj_eq]
  change (kStarKernel N).map (MulAut.conj s).toMonoidHom = kStarKernel N
  rw [kStarKernel, Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective,
    map_coreActionKernel (MulAut.conj s), map_solomonKStarOf (MulAut.conj s), hNs]

theorem mem_coreActionKernel_solomonKStarOf {C : Subgroup G} {s : G} (hsC : s ∈ C)
    (hs : ∀ M ∈ kStarComponents C, s ∈ coreActionKernel M) :
    s ∈ coreActionKernel (solomonKStarOf C) := by
  refine ⟨le_normalizer_solomonKStarOf C hsC, fun v hv => ?_⟩
  let Q : Subgroup G :=
    { carrier := {v | v ∈ solomonKStarOf C ∧ v⁻¹ * s⁻¹ * v * s ∈ oddCoreIn (solomonKStarOf C)}
      one_mem' := ⟨one_mem _, by
        rw [inv_one, one_mul, mul_one, inv_mul_cancel]
        exact one_mem _⟩
      mul_mem' := by
        rintro x z ⟨hx, h₁⟩ ⟨hz, h₂⟩
        refine ⟨mul_mem hx hz, ?_⟩
        rw [show (x * z)⁻¹ * s⁻¹ * (x * z) * s =
          z⁻¹ * (x⁻¹ * s⁻¹ * x * s) * z * (z⁻¹ * s⁻¹ * z * s) by group]
        exact mul_mem (inv_mul_mul_mem_oddCoreIn h₁ hz) h₂
      inv_mem' := by
        rintro x ⟨hx, h₁⟩
        refine ⟨inv_mem hx, ?_⟩
        rw [show x⁻¹⁻¹ * s⁻¹ * x⁻¹ * s = x⁻¹⁻¹ * (x⁻¹ * s⁻¹ * x * s)⁻¹ * x⁻¹ by group]
        exact inv_mul_mul_mem_oddCoreIn (inv_mem h₁) (inv_mem hx) }
  have hDQ : solomonKStarOf C ≤ Q := by
    rw [solomonKStarOf_eq_sSup C]
    refine sSup_le fun M hM m hm => ?_
    have hMD : M ≤ solomonKStarOf C := le_iSup₂_of_le M hM le_rfl
    exact (show m ∈ solomonKStarOf C ∧ m⁻¹ * s⁻¹ * m * s ∈ oddCoreIn (solomonKStarOf C) from
      ⟨hMD hm, oddCoreIn_le_of_isTwoComponentIn
        (isTwoComponentIn_of_le hM.1 hMD (solomonKStarOf_le C)) ((hs M hM).2 m hm)⟩)
  exact (hDQ hv).2

omit [Finite G] in
theorem relIndex_normalizer_le_two {Y A₁ A₂ : Subgroup G} (hA : A₁ ≠ A₂)
    (hY : ∀ g ∈ Y, ∀ A : Subgroup G, (A = A₁ ∨ A = A₂) →
      (A.map (MulAut.conj g).toMonoidHom = A₁ ∨ A.map (MulAut.conj g).toMonoidHom = A₂)) :
    (normalizer (A₁ : Set G)).relIndex Y ≤ 2 := by
  by_cases hle : Y ≤ normalizer (A₁ : Set G)
  · rw [relIndex_eq_one.mpr hle]
    norm_num
  obtain ⟨a, haY, haN⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hmul : ∀ (g h : G) (A : Subgroup G), A.map (MulAut.conj (g * h)).toMonoidHom =
      (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    intro g h A
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hinj : ∀ (g : G) {A B : Subgroup G}, A.map (MulAut.conj g).toMonoidHom =
      B.map (MulAut.conj g).toMonoidHom → A = B := fun g _ _ h =>
    Subgroup.map_injective (MulAut.conj g).injective h
  have ha1 : A₁.map (MulAut.conj a).toMonoidHom = A₂ := by
    rcases hY a haY A₁ (Or.inl rfl) with h | h
    · exact absurd (mem_normalizer_iff_map_conj_eq.mpr h) haN
    · exact h
  have ha2 : A₂.map (MulAut.conj a).toMonoidHom = A₁ := by
    rcases hY a haY A₂ (Or.inr rfl) with h | h
    · exact h
    · exact absurd (hinj a (ha1.trans h.symm)) hA
  refine le_of_eq (relIndex_eq_two_iff'.mpr ⟨a, haY, fun b hb => ?_⟩)
  by_cases hbN : b ∈ normalizer (A₁ : Set G)
  · refine Or.inr ⟨hbN, fun h => hA ?_⟩
    have h2 : A₁.map (MulAut.conj (a * b)).toMonoidHom = A₁ := mem_normalizer_iff_map_conj_eq.mp h
    have hb1 : A₁.map (MulAut.conj b).toMonoidHom = A₁ := mem_normalizer_iff_map_conj_eq.mp hbN
    rw [hmul, hb1, ha1] at h2
    exact h2.symm
  · refine Or.inl ⟨?_, hbN⟩
    have hb1 : A₁.map (MulAut.conj b).toMonoidHom = A₂ := by
      rcases hY b hb A₁ (Or.inl rfl) with h | h
      · exact absurd (mem_normalizer_iff_map_conj_eq.mpr h) hbN
      · exact h
    exact mem_normalizer_iff_map_conj_eq.mpr
      (show A₁.map (MulAut.conj (a * b)).toMonoidHom = A₁ by rw [hmul, hb1, ha2])

theorem pRank_le_pRank_inf_add_one {P H : Subgroup G} (h2 : H.relIndex P ≤ 2) :
    CFSG.Open.pRank 2 P ≤ CFSG.Open.pRank 2 (P ⊓ H) + 1 := by
  obtain ⟨E, hEP, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) P
  have hne : H.relIndex P ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos (relIndex_dvd_card H P) Nat.card_pos)
  have hrel : H.relIndex E ≤ 2 := (relIndex_le_of_le_right hEP hne).trans h2
  have hmul : H.relIndex E * Nat.card ↥(H ⊓ E) = Nat.card E := relIndex_mul_card H E
  have hdvd : Nat.card ↥(H ⊓ E) ∣ 2 ^ CFSG.Open.pRank 2 P := hcard ▸ card_dvd_of_le inf_le_right
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hle : CFSG.Open.pRank 2 P ≤ j + 1 := by
    have h1 : 2 ^ CFSG.Open.pRank 2 P ≤ 2 ^ (j + 1) := by
      rw [← hcard, ← hmul, hj, pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ hrel
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hHE : CFSG.Open.IsElemAbelian 2 (H ⊓ E) := by
    have := hE.1
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hE.2 x hx.2⟩
    have h := congrArg Subtype.val (mul_comm' (⟨a, a.2.2⟩ : E) ⟨b, b.2.2⟩)
    exact h
  have h3 := SectionRank.le_pRank (by norm_num) (le_inf (inf_le_right.trans hEP) inf_le_left)
    hHE hj
  omega

theorem map_conj_mem_pumpSet {K' C M : Subgroup G} {g : G} (hgC : g ∈ normalizer (C : Set G))
    (hgK : g ∈ normalizer (K' : Set G)) (hM : M ∈ pumpSet K' C) :
    M.map (MulAut.conj g).toMonoidHom ∈ pumpSet K' C := by
  have hC : C.map (MulAut.conj g).toMonoidHom = C := mem_normalizer_iff_map_conj_eq.mp hgC
  have hK : K'.map (MulAut.conj g).toMonoidHom = K' := mem_normalizer_iff_map_conj_eq.mp hgK
  have hKC : (K' ⊓ C).map (MulAut.conj g).toMonoidHom = K' ⊓ C := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hK, hC]
  refine ⟨?_, fun h => hM.2 ?_⟩
  · have h := isTwoComponentIn_map (MulAut.conj g) hM.1.1
    rw [hC] at h
    exact ⟨h, map_mem_solomonKStar _ hM.1.2⟩
  · rw [← map_coreActionKernel (MulAut.conj g) M, ← hKC, ← map_twoLayerIn (MulAut.conj g)] at h
    exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp h

end CFSG.ComponentClassification.Sol76T13
