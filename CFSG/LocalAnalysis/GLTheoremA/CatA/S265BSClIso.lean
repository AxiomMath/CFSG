module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.HyperBlocks

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_invariant_isotropic_of_normalizes_two_group (hF : Nat.card F = 2)
    {f : LinearMap.BilinForm F V} (hnd : f.Nondegenerate) {A T : Subgroup (V ≃ₗ[F] V)}
    (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hTf : ∀ t ∈ T, ∀ u v, f (t u) (t v) = f u v) (hAf : ∀ a ∈ A, ∀ u v, f (a u) (a v) = f u v)
    (hAT : A ≤ Subgroup.normalizer (T : Set (V ≃ₗ[F] V))) :
    ∃ R : Submodule F V, R ≠ ⊥ ∧ (∀ a ∈ A, ∀ v ∈ R, a v ∈ R) ∧ ∀ u ∈ R, ∀ v ∈ R, f u v = 0 := by
  haveI : Finite V := Module.finite_of_finite F
  let C : Submodule F V := ⨅ t : T, fixedByEnd (t : V ≃ₗ[F] V)
  have hCmem : ∀ v, v ∈ C ↔ ∀ t ∈ T, t v = v := fun v => by
    simp only [C, Submodule.mem_iInf, mem_fixedByEnd, Subtype.forall]
  have hCA : ∀ a ∈ A, ∀ c ∈ C, a c ∈ C := by
    intro a ha c hc
    rw [hCmem] at hc ⊢
    intro t ht
    have hat : a⁻¹ * t * a ∈ T := by
      simpa using (Subgroup.mem_normalizer_iff.1 (hAT (A.inv_mem ha)) t).1 ht
    have h1 : t * a = a * (a⁻¹ * t * a) := by group
    rw [← LinearEquiv.mul_apply, h1, LinearEquiv.mul_apply, hc _ hat]
  have hCperp : ∀ t ∈ T, ∀ x ∈ f.orthogonal C, t x ∈ f.orthogonal C := by
    intro t ht x hx c hc
    have h := hTf t ht c x
    rw [(hCmem c).1 hc t ht] at h
    rw [h]
    exact hx c hc
  have hCpA : ∀ a ∈ A, ∀ x ∈ f.orthogonal C, a x ∈ f.orthogonal C := by
    intro a ha x hx c hc
    have hc' : a⁻¹ c ∈ C := hCA _ (A.inv_mem ha) c hc
    have h := hAf a ha (a⁻¹ c) x
    have hac : a (a⁻¹ c) = c := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
    rw [hac] at h
    rw [h]
    exact hx _ hc'
  have hfix : ∀ U : Submodule F V, (∀ t ∈ T, ∀ u ∈ U, t u ∈ U) → U ≠ ⊥ →
      ∃ u ∈ U, u ≠ 0 ∧ ∀ t ∈ T, t u = u := fun U hU hne => by
    obtain ⟨u, hu, hu0, hufix⟩ := exists_fixed_ne_zero_of_card_two hF hT T.subtype (U := U)
      (fun x v hv => hU x x.2 v hv) hne
    exact ⟨u, hu, hu0, fun t ht => hufix ⟨t, ht⟩⟩
  obtain ⟨t₀, ht₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hT1
  obtain ⟨v₀, hv₀⟩ : ∃ v, (t₀ : V ≃ₗ[F] V) v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact ht₀ (Subtype.ext (LinearEquiv.ext hcon))
  haveI : Nontrivial V := ⟨⟨_, _, hv₀⟩⟩
  have hCtop : C ≠ ⊤ := fun htop =>
    hv₀ ((hCmem v₀).1 (htop ▸ Submodule.mem_top) t₀ t₀.2)
  have hperp : f.orthogonal C ≠ ⊥ := by
    intro hbot
    have h := LinearMap.BilinForm.finrank_orthogonal hnd C
    rw [hbot, finrank_bot] at h
    exact hCtop (Submodule.eq_top_of_finrank_eq (by have := Submodule.finrank_le C; omega))
  obtain ⟨u, hu, hu0, hufix⟩ := hfix (f.orthogonal C) hCperp hperp
  exact ⟨C ⊓ f.orthogonal C, (Submodule.ne_bot_iff _).2 ⟨u, ⟨(hCmem u).2 hufix, hu⟩, hu0⟩,
    fun a ha v hv => ⟨hCA a ha v hv.1, hCpA a ha v hv.2⟩, fun u hu v hv => hv.2 u hu.1⟩

omit [Finite F] in
theorem false_of_invariant_isotropic (hF : Nat.card F = 2) {f : LinearMap.BilinForm F V}
    (halt : f.IsAlt) (hnd : f.Nondegenerate) {A : Subgroup (V ≃ₗ[F] V)} [Fintype A]
    (hA : IsElemAbelian 3 A) (hAf : InvariantBilin A f) (hC : fixedSpaceOf A = ⊥)
    (hblk : ∀ D : Hyperplane A 3, Module.finrank F ↥(blockSpace A D.1) ≤ 2)
    {R : Submodule F V} (hR0 : R ≠ ⊥) (hRA : ∀ a ∈ A, ∀ v ∈ R, a v ∈ R)
    (hRiso : ∀ u ∈ R, ∀ v ∈ R, f u v = 0) : False := by
  classical
  have hpF := cast_three_ne_zero_of_card_two (F := F) hF
  have h3 := Nat.prime_three
  obtain ⟨r, hrR, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR0
  have hall := sup_fixedSpaceOf_iSup_blockSpace A h3 hpF hA
  have hdec : ∀ x ∈ (⨆ D : Hyperplane A 3, blockSpace A D.1),
      x = ∑ D : Hyperplane A 3, projBlock A h3 hpF hA D x := fun x hx => by
    refine Submodule.iSup_induction (fun D : Hyperplane A 3 => blockSpace A D.1)
      (motive := fun x => x = ∑ D : Hyperplane A 3, projBlock A h3 hpF hA D x) hx
      (fun E y hy => ?_) (by simp) (fun y z hy hz => ?_)
    · rw [Finset.sum_eq_single E (fun D _ hDE => projBlock_apply_of_mem_block A h3 hpF hA
        (Ne.symm hDE) hy) (fun h => absurd (Finset.mem_univ E) h),
        projBlock_apply_of_mem A h3 hpF hA E hy]
    · simp only [map_add, Finset.sum_add_distrib]
      rw [← hy, ← hz]
  obtain ⟨D, hD⟩ : ∃ D : Hyperplane A 3, projBlock A h3 hpF hA D r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hr0 ((hdec r ?_).trans (Finset.sum_eq_zero fun D _ => hcon D))
    rw [hC, bot_sup_eq] at hall
    rw [hall]
    exact Submodule.mem_top
  have hwV : projBlock A h3 hpF hA D r ∈ blockSpace A D.1 := projBlock_apply_mem A h3 hpF hA D r
  have hwR : projBlock A h3 hpF hA D r ∈ R := by
    have hsum : ∀ H : Subgroup ↥A, sumOp (actionEnd A) H r ∈ R := fun H => by
      unfold sumOp
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun a _ => hRA _ (a : ↥A).2 r hrR
    rw [projBlock_apply_eq]
    exact R.sub_mem (R.smul_mem _ (hsum _)) (R.smul_mem _ (hsum _))
  generalize projBlock A h3 hpF hA D r = w at hD hwV hwR
  obtain ⟨x, hx⟩ : ∃ x : ↥A, x ∉ D.1 := by
    by_contra hcon
    push Not at hcon
    have htop : D.1 = ⊤ := eq_top_iff.2 fun y _ => hcon y
    have := D.2
    rw [htop, Subgroup.index_top] at this
    omega
  have hw'V : (x : V ≃ₗ[F] V) w ∈ blockSpace A D.1 := blockSpace_invariant A h3 hpF hA hwV
  have hw'0 : (x : V ≃ₗ[F] V) w ≠ 0 := fun h => hD (by simpa using h)
  have hww' : w ≠ (x : V ≃ₗ[F] V) w := fun h =>
    hD (eq_zero_of_fixed_mem_blockSpace A h3 hpF hA hx hwV h.symm)
  have hfin : Module.finrank F ↥(blockSpace A D.1) = 2 := by
    have halt' : (LinearMap.BilinForm.restrict f (blockSpace A D.1)).IsAlt := fun u => by
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      exact halt _
    obtain ⟨k, hk⟩ := halt'.even_finrank (blockSpace_nondegenerate A h3 hpF hA halt hAf hnd D)
    have hpos : 0 < Module.finrank F ↥(blockSpace A D.1) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨w, hwV⟩, by simpa using hD⟩
    have := hblk D
    omega
  have hfw : ∀ v ∈ blockSpace A D.1, f w v = 0 := fun v hv => by
    rcases eq_zero_or_eq_or_eq_add_of_finrank_two hF hfin hwV hw'V hD hw'0 hww' hv with
      h | h | h | h <;> rw [h]
    · simp
    · exact halt w
    · exact hRiso w hwR _ (hRA _ x.2 w hwR)
    · rw [map_add, halt w, hRiso w hwR _ (hRA _ x.2 w hwR), add_zero]
  have hle : fixedSpaceOf A ⊔ (⨆ E : Hyperplane A 3, blockSpace A E.1) ≤ LinearMap.ker (f w) := by
    refine sup_le (by rw [hC]; exact bot_le) (iSup_le fun E v hv => ?_)
    by_cases hED : E = D
    · subst hED
      exact hfw v hv
    · exact blockSpace_bilinear_orthogonal A h3 hpF hA f hAf (Ne.symm hED) hwV hv
  exact hD (hnd.1 w fun v => hle (hall ▸ Submodule.mem_top : v ∈ _))

theorem two_group_eq_bot_of_small_blocks (hF : Nat.card F = 2) {f : LinearMap.BilinForm F V}
    (halt : f.IsAlt) (hnd : f.Nondegenerate) {A T : Subgroup (V ≃ₗ[F] V)} [Fintype A]
    (hA : IsElemAbelian 3 A) (hAf : InvariantBilin A f) (hC : fixedSpaceOf A = ⊥)
    (hblk : ∀ D : Hyperplane A 3, Module.finrank F ↥(blockSpace A D.1) ≤ 2)
    (hT : IsPGroup 2 T) (hTf : ∀ t ∈ T, ∀ u v, f (t u) (t v) = f u v)
    (hAT : A ≤ Subgroup.normalizer (T : Set (V ≃ₗ[F] V))) : T = ⊥ := by
  by_contra hT1
  obtain ⟨R, hR0, hRA, hRiso⟩ := exists_invariant_isotropic_of_normalizes_two_group hF hnd hT hT1
    hTf (fun a ha => hAf ⟨a, ha⟩) hAT
  exact false_of_invariant_isotropic hF halt hnd hA hAf hC hblk hR0 hRA hRiso

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
