module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagCGen

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Adapted

variable [CharP K 2] {s : V ≃ₗ[K] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
  (hss : s * s = 1)

include hs hss in
theorem lagAdapted_reflect {a : V} (ha : Q (omegaInvNil s a) = 1) :
    LagAdapted Q s (reflect Q (omegaInvNil s a)) ∧
      omegaInvSpace (reflect Q (omegaInvNil s a)) = K ∙ omegaInvNil s a ∧
      finrank K (omegaInvSpace (reflect Q (omegaInvNil s a))) = 1 := by
  set n := omegaInvNil s a with hn
  have hQn : Q n ≠ 0 := by rw [ha]; exact one_ne_zero
  have hNr : ∀ x, omegaInvNil (reflect Q n) x = polar Q n x • n := fun x => by
    rw [omegaInvNil_apply, reflect_apply hQn, ha, div_one, sub_sub_cancel_left,
      omegaInv_neg_eq K]
  have hna : polar Q n a = 1 := by rw [hn, polar_omegaInvNil_self hs, ← hn, ha]
  have hspan : omegaInvSpace (reflect Q n) = K ∙ n := by
    apply le_antisymm
    · intro v hv
      obtain ⟨x, rfl⟩ := mem_omegaInvSpace_iff.1 hv
      rw [hNr]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self n)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_omegaInvSpace_iff.2 ⟨a, by rw [hNr, hna, one_smul]⟩
  have hn0 : n ≠ 0 := fun h => hQn (by rw [h, QuadraticMap.map_zero])
  refine ⟨⟨reflect_mem_orthogonalGroup Q n, reflect_mul_self Q n, ?_, fun v hv => ?_⟩, hspan,
    by rw [hspan, finrank_span_singleton hn0]⟩
  · rw [hspan, Submodule.span_le, Set.singleton_subset_iff]
    exact omegaInvNil_mem_omegaInvSpace s a
  · rw [hspan] at hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hv
    rw [hNr, hn, polar_omegaInvNil_left hs hss, ← hc, polar_smul_right_eq, ← hn, polar_comm,
      hna, mul_one, hn]

include hs hss in
theorem mem_omegaInvSpace_mul_of_forall [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s' g : V ≃ₗ[K] V} (h : LagAdapted Q s s')
    (hg : LagAdapted Q s g) (hgs' : omegaInvSpace g ≤ omegaInvSpace s') {u : V}
    (hu : u ∈ omegaInvSpace s')
    (horth : ∀ b, omegaInvNil s b ∈ omegaInvSpace g → polar Q u b = 0) :
    u ∈ omegaInvSpace (s' * g) := by
  obtain ⟨-, hN, -⟩ := lagAdapted_mul hQ hs hss h hg hgs'
  obtain ⟨v, rfl⟩ := mem_omegaInvSpace_iff.1 (h.2.2.1 hu)
  have hv : omegaInvNil s' v = omegaInvNil s v := h.2.2.2 v hu
  have hgv : omegaInvNil g v = 0 := by
    refine (omegaInvNil_eq_zero_iff hQ hg.1 hg.2.1).2 fun w hw => ?_
    obtain ⟨c, rfl⟩ := mem_omegaInvSpace_iff.1 (hg.2.2.1 hw)
    rw [← polar_omegaInvNil_left hs hss]
    exact horth c hw
  exact mem_omegaInvSpace_iff.2 ⟨v, by rw [hN, hv, hgv, add_zero]⟩

omit [CharP K 2] in
theorem exists_normalized_of_lagAdapted [Finite K] [CharP K 2] {s' : V ≃ₗ[K] V}
    (h : LagAdapted Q s s')
    {u : V} (hu : u ∈ omegaInvSpace s') (hQu : Q u ≠ 0) :
    ∃ a, omegaInvNil s a ∈ omegaInvSpace s' ∧ Q (omegaInvNil s a) = 1 := by
  obtain ⟨y, rfl⟩ := mem_omegaInvSpace_iff.1 (h.2.2.1 hu)
  obtain ⟨d, hd⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q (omegaInvNil s y))
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hd
    exact hQu hd
  refine ⟨d⁻¹ • y, by rw [map_smul]; exact (omegaInvSpace s').smul_mem _ hu, ?_⟩
  rw [map_smul, map_smul_eq_sq, hd]
  field_simp

include hs hss in
theorem polar_omegaInvNil_eq_zero_of_mem_reflect {x c b' : V} (hQx : Q (omegaInvNil s x) = 1)
    (hxc : polar Q (omegaInvNil s x) c = 0)
    (hb' : omegaInvNil s b' ∈ omegaInvSpace (reflect Q (omegaInvNil s x))) :
    polar Q (omegaInvNil s c) b' = 0 := by
  rw [(lagAdapted_reflect hs hss hQx).2.1] at hb'
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hb'
  rw [polar_omegaInvNil_left hs hss, ← hd, polar_smul_right_eq,
    polar_comm Q c (omegaInvNil s x), hxc, mul_zero]

include hs hss in
theorem lagAdapted_mul_reflect_pair [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {s' : V ≃ₗ[K] V} (h : LagAdapted Q s s') {a b : V} (ha : omegaInvNil s a ∈ omegaInvSpace s')
    (hb : omegaInvNil s b ∈ omegaInvSpace s') (hQa : Q (omegaInvNil s a) = 1)
    (hQb : Q (omegaInvNil s b) = 1) (hab : polar Q (omegaInvNil s a) b = 0) :
    LagAdapted Q s (s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b)) ∧
      finrank K (omegaInvSpace (s' * reflect Q (omegaInvNil s a) *
        reflect Q (omegaInvNil s b))) + 2 = finrank K (omegaInvSpace s') ∧
      omegaInvSpace (s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b)) ≤
        omegaInvSpace s' ∧
      (∀ v, omegaInvNil s v ∈ omegaInvSpace (s' * reflect Q (omegaInvNil s a) *
          reflect Q (omegaInvNil s b)) →
        polar Q (omegaInvNil s a) v = 0 ∧ polar Q (omegaInvNil s b) v = 0) ∧
      (∀ c, omegaInvNil s c ∈ omegaInvSpace s' → polar Q (omegaInvNil s a) c = 0 →
        polar Q (omegaInvNil s b) c = 0 → omegaInvNil s c ∈ omegaInvSpace (s' *
          reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b))) ∧
      s' = (s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b)) *
        (reflect Q (omegaInvNil s b) * reflect Q (omegaInvNil s a)) := by
  have hcomm := polar_omegaInvNil_comm hs hss
  obtain ⟨hra, hspa, hda⟩ := lagAdapted_reflect hs hss hQa
  obtain ⟨hrb, hspb, hdb⟩ := lagAdapted_reflect hs hss hQb
  have hsing : ∀ {x : V} {U : Submodule K V}, x ∈ U → K ∙ x ≤ U := fun hx => by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx
  have haR : omegaInvNil s a ∈ omegaInvSpace (reflect Q (omegaInvNil s a)) := by
    rw [hspa]
    exact Submodule.mem_span_singleton_self _
  have hbR : omegaInvNil s b ∈ omegaInvSpace (reflect Q (omegaInvNil s b)) := by
    rw [hspb]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨hs₁, -, horth₁, hle₁, hdim₁, he₁⟩ := lagAdapted_mul hQ hs hss h hra (hspa ▸ hsing ha)
  have hb₁ : omegaInvNil s b ∈ omegaInvSpace (s' * reflect Q (omegaInvNil s a)) :=
    mem_omegaInvSpace_mul_of_forall hs hss hQ h hra (hspa ▸ hsing ha) hb fun b' hb' =>
      polar_omegaInvNil_eq_zero_of_mem_reflect hs hss hQa hab hb'
  obtain ⟨hs₂, -, horth₂, hle₂, hdim₂, he₂⟩ := lagAdapted_mul hQ hs hss hs₁ hrb (hspb ▸ hsing hb₁)
  refine ⟨hs₂, by rw [← hdim₁, ← hdim₂, hda, hdb], hle₂.trans hle₁, fun v hv => ⟨?_, ?_⟩,
    fun c hc hac hbc => ?_, ?_⟩
  · rw [hcomm]
    exact horth₁ _ (hle₂ hv) a haR
  · rw [hcomm]
    exact horth₂ _ hv b hbR
  · have hc₁ : omegaInvNil s c ∈ omegaInvSpace (s' * reflect Q (omegaInvNil s a)) :=
      mem_omegaInvSpace_mul_of_forall hs hss hQ h hra (hspa ▸ hsing ha) hc fun b' hb' =>
        polar_omegaInvNil_eq_zero_of_mem_reflect hs hss hQa hac hb'
    exact mem_omegaInvSpace_mul_of_forall hs hss hQ hs₁ hrb (hspb ▸ hsing hb₁) hc₁ fun b' hb' =>
      polar_omegaInvNil_eq_zero_of_mem_reflect hs hss hQb hbc hb'
  · calc s' = s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s a) := he₁
      _ = (s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b) *
          reflect Q (omegaInvNil s b)) * reflect Q (omegaInvNil s a) := by rw [← he₂]
      _ = _ := by group

include hs hss in
theorem lagAdapted_normalized_or_hyperbolic [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {s' : V ≃ₗ[K] V} (h : LagAdapted Q s s') (hne : omegaInvSpace s' ≠ ⊥) :
    (∃ c, omegaInvNil s c ∈ omegaInvSpace s' ∧ Q (omegaInvNil s c) = 1) ∨
      ∃ z u, omegaInvNil s z ∈ omegaInvSpace s' ∧ omegaInvNil s u ∈ omegaInvSpace s' ∧
        polar Q (omegaInvNil s z) u = 1 ∧ Q (omegaInvNil s z) = 0 ∧ Q (omegaInvNil s u) = 0 := by
  by_cases hex : ∃ w ∈ omegaInvSpace s', Q w ≠ 0
  · obtain ⟨w, hw, hQw⟩ := hex
    exact Or.inl (exists_normalized_of_lagAdapted h hw hQw)
  · push Not at hex
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_of_lagAdapted hQ hs hss h hne
    exact Or.inr ⟨x, y, hx, hy, hxy, hex _ hx, hex _ hy⟩

include hs hss in
theorem lagOrthonormal_add_hyperbolic {a z u : V} (hQa : Q (omegaInvNil s a) = 1)
    (hzu : polar Q (omegaInvNil s z) u = 1) (hQz : Q (omegaInvNil s z) = 0)
    (hQu : Q (omegaInvNil s u) = 0) (haz : polar Q (omegaInvNil s a) z = 0)
    (hau : polar Q (omegaInvNil s a) u = 0) :
    Q (omegaInvNil s (a + z)) = 1 ∧ Q (omegaInvNil s (a + u)) = 1 ∧
      polar Q (omegaInvNil s (a + z)) (a + u) = 0 := by
  have hcomm := polar_omegaInvNil_comm hs hss
  refine ⟨by rw [map_omegaInvNil_add hs hss, hQa, hQz, add_zero],
    by rw [map_omegaInvNil_add hs hss, hQa, hQu, add_zero], ?_⟩
  rw [map_add, polar_add_left, polar_add_right, polar_add_right, polar_omegaInvNil_self hs, hQa,
    hau, hcomm z a, haz, hzu, add_zero, zero_add]
  exact CharTwo.add_self_eq_zero 1

include hs hss in
theorem exists_lagOrthonormal_pair [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s' : V ≃ₗ[K] V} (h : LagAdapted Q s s')
    (hw : ∃ w ∈ omegaInvSpace s', Q w ≠ 0) (h2 : 2 ≤ finrank K (omegaInvSpace s')) :
    ∃ a b, omegaInvNil s a ∈ omegaInvSpace s' ∧ omegaInvNil s b ∈ omegaInvSpace s' ∧
      Q (omegaInvNil s a) = 1 ∧ Q (omegaInvNil s b) = 1 ∧ polar Q (omegaInvNil s a) b = 0 := by
  have hcomm := polar_omegaInvNil_comm hs hss
  obtain ⟨w, hw, hQw⟩ := hw
  obtain ⟨a, ha, hQa⟩ := exists_normalized_of_lagAdapted h hw hQw
  obtain ⟨hra, hspa, hda⟩ := lagAdapted_reflect hs hss hQa
  have hle : omegaInvSpace (reflect Q (omegaInvNil s a)) ≤ omegaInvSpace s' := by
    rw [hspa, Submodule.span_le, Set.singleton_subset_iff]
    exact ha
  have haR : omegaInvNil s a ∈ omegaInvSpace (reflect Q (omegaInvNil s a)) := by
    rw [hspa]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨hs₁, -, horth₁, hle₁, hdim₁, -⟩ := lagAdapted_mul hQ hs hss h hra hle
  have hne : omegaInvSpace (s' * reflect Q (omegaInvNil s a)) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hdim₁
    omega
  have horth : ∀ v, omegaInvNil s v ∈ omegaInvSpace (s' * reflect Q (omegaInvNil s a)) →
      polar Q (omegaInvNil s a) v = 0 := fun v hv => by
    rw [hcomm]
    exact horth₁ _ hv a haR
  rcases lagAdapted_normalized_or_hyperbolic hs hss hQ hs₁ hne with ⟨c, hc, hQc⟩ |
    ⟨z, u, hz, hu, hzu, hQz, hQu⟩
  · exact ⟨a, c, ha, hle₁ hc, hQa, hQc, horth c hc⟩
  · obtain ⟨e1, e2, e3⟩ := lagOrthonormal_add_hyperbolic hs hss hQa hzu hQz hQu (horth z hz)
      (horth u hu)
    exact ⟨a + z, a + u, by rw [map_add]; exact (omegaInvSpace s').add_mem ha (hle₁ hz),
      by rw [map_add]; exact (omegaInvSpace s').add_mem ha (hle₁ hu), e1, e2, e3⟩

include hs hss in
theorem exists_lagOrthonormal_triple [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s' : V ≃ₗ[K] V} (h : LagAdapted Q s s')
    (hw : ∃ w ∈ omegaInvSpace s', Q w ≠ 0) (h3 : 3 ≤ finrank K (omegaInvSpace s')) :
    ∃ a b c, omegaInvNil s a ∈ omegaInvSpace s' ∧ omegaInvNil s b ∈ omegaInvSpace s' ∧
      omegaInvNil s c ∈ omegaInvSpace s' ∧ Q (omegaInvNil s a) = 1 ∧ Q (omegaInvNil s b) = 1 ∧
      Q (omegaInvNil s c) = 1 ∧ polar Q (omegaInvNil s a) b = 0 ∧
      polar Q (omegaInvNil s a) c = 0 ∧ polar Q (omegaInvNil s b) c = 0 := by
  obtain ⟨a, b, ha, hb, hQa, hQb, hab⟩ := exists_lagOrthonormal_pair hs hss hQ h hw (by omega)
  obtain ⟨hs₂, hdim₂, hle₂, horth₂, -, -⟩ :=
    lagAdapted_mul_reflect_pair hs hss hQ h ha hb hQa hQb hab
  have hne : omegaInvSpace (s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b)) ≠
      ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hdim₂
    omega
  rcases lagAdapted_normalized_or_hyperbolic hs hss hQ hs₂ hne with ⟨c, hc, hQc⟩ |
    ⟨z, u, hz, hu, hzu, hQz, hQu⟩
  · exact ⟨a, b, c, ha, hb, hle₂ hc, hQa, hQb, hQc, hab, (horth₂ c hc).1, (horth₂ c hc).2⟩
  · obtain ⟨e1, e2, e3⟩ := lagOrthonormal_add_hyperbolic hs hss hQb hzu hQz hQu (horth₂ z hz).2
      (horth₂ u hu).2
    refine ⟨a, b + z, b + u, ha, by rw [map_add]; exact (omegaInvSpace s').add_mem hb (hle₂ hz),
      by rw [map_add]; exact (omegaInvSpace s').add_mem hb (hle₂ hu), hQa, e1, e2, ?_, ?_, e3⟩
    · rw [polar_add_right, hab, (horth₂ z hz).1, add_zero]
    · rw [polar_add_right, hab, (horth₂ u hu).1, add_zero]

include hs hss in
theorem mem_omegaO2Cent_of_lagAdapted_typeC [Finite K] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (r : ℕ) :
    ∀ s' : V ≃ₗ[K] V, LagAdapted Q s s' → finrank K (omegaInvSpace s') = 2 * (r + 1) →
      (∃ w ∈ omegaInvSpace s', Q w ≠ 0) →
      (r = 0 → ∃ z, Q (omegaInvNil s z) = 1 ∧ ∀ u ∈ omegaInvSpace s', polar Q u z = 0) →
      s' ∈ omegaO2Cent Q s := by
  have hcomm := polar_omegaInvNil_comm hs hss
  induction r with
  | zero =>
    intro s' h hr hw hz
    obtain ⟨z, hQz, hzo⟩ := hz rfl
    obtain ⟨a, b, ha, hb, hQa, hQb, hab⟩ := exists_lagOrthonormal_pair hs hss hQ h hw (by omega)
    obtain ⟨-, hdim₂, -, -, -, he⟩ := lagAdapted_mul_reflect_pair hs hss hQ h ha hb hQa hQb hab
    have h1 : s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b) = 1 :=
      eq_one_of_finrank_omegaInvSpace_eq_zero (by omega)
    rw [he, h1, one_mul]
    exact reflect_mul_reflect_mem_omegaO2Cent hs hss hQb hQa hQz (by rw [hcomm, hab])
      (hzo _ hb) (hzo _ ha)
  | succ r ih =>
    intro s' h hr hw _
    obtain ⟨a, b, c, ha, hb, hc, hQa, hQb, hQc, hab, hac, hbc⟩ :=
      exists_lagOrthonormal_triple hs hss hQ h hw (by omega)
    obtain ⟨hs₂, hdim₂, -, horth₂, hmem₂, he⟩ :=
      lagAdapted_mul_reflect_pair hs hss hQ h ha hb hQa hQb hab
    have hc₂ := hmem₂ c hc hac hbc
    have hmem : s' * reflect Q (omegaInvNil s a) * reflect Q (omegaInvNil s b) ∈
        omegaO2Cent Q s := by
      refine ih _ hs₂ (by omega) ⟨_, hc₂, by rw [hQc]; exact one_ne_zero⟩
        fun _ => ⟨a, hQa, fun u hu => ?_⟩
      obtain ⟨v, rfl⟩ := mem_omegaInvSpace_iff.1 (hs₂.2.2.1 hu)
      rw [hcomm]
      exact (horth₂ v hu).1
    rw [he]
    exact mul_mem hmem (reflect_mul_reflect_mem_omegaO2Cent hs hss hQb hQa hQc
      (by rw [hcomm, hab]) hbc hac)

end Adapted

theorem mem_omegaO2Cent_of_typeC_four_le [Finite K] [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hss : s * s = 1)
    (hw : ∃ w ∈ omegaInvSpace s, Q w ≠ 0) (hev : Even (finrank K (omegaInvSpace s)))
    (h4 : 4 ≤ finrank K (omegaInvSpace s)) : s ∈ omegaO2Cent Q s := by
  obtain ⟨j, hj⟩ := hev
  exact mem_omegaO2Cent_of_lagAdapted_typeC hs hss hQ (j - 1) s (lagAdapted_self hs hss)
    (by omega) hw fun h0 => absurd h0 (by omega)

end CFSG.SeitzReduction.SymplecticPilot
