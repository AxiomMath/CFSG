module

public import CFSG.LargeExtraspecial.S2SpLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def SpInvariant (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))
    (F : Submodule (ZMod 2) V) (N : Submodule (ZMod 2) M) : Prop :=
  ∀ g : TauCeti.BilinForm.isometryGroup f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    ∀ v ∈ N, ρ g v ∈ N

@[expose] def SpRadDecomp (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))
    (F : Submodule (ZMod 2) V) (N : Submodule (ZMod 2) M) (p p₁ : V) : Prop :=
  (N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) ⊔
      (N ⊓ fixOf ρ (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V))) = N ∧
    (N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) ⊓
      (N ⊓ fixOf ρ (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V))) = ⊥

omit [FiniteDimensional (ZMod 2) V] in
theorem SpRadDecomp.symm {ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M)}
    {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M} {p p₁ : V}
    (h : SpRadDecomp ρ F N p p₁) : SpRadDecomp ρ F N p₁ p :=
  ⟨by rw [sup_comm]; exact h.1, by rw [inf_comm]; exact h.2⟩

variable [FiniteDimensional (ZMod 2) M] (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

omit [FiniteDimensional (ZMod 2) V] in
theorem map_eq_of_spInvariant {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    (hN : SpInvariant ρ F N) (g : TauCeti.BilinForm.isometryGroup f)
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) : N.map (ρ g : M →ₗ[ZMod 2] M) = N :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact hN g hg v hv)
    (LinearEquiv.finrank_map_eq (ρ g) N)

omit [FiniteDimensional (ZMod 2) V] in
theorem map_inf_fixOf_spRadFix (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M} (hN : SpInvariant ρ F N)
    (g : TauCeti.BilinForm.isometryGroup f) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) {p : V}
    (hpF : p ∈ spPerp f F) (hp0 : p ≠ 0) :
    (N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))).map (ρ g : M →ₗ[ZMod 2] M) =
      N ⊓ fixOf ρ (spRadFix f F ((g : V ≃ₗ[ZMod 2] V) p) : Set (V ≃ₗ[ZMod 2] V)) := by
  rw [Submodule.map_inf _ (ρ g).injective, map_eq_of_spInvariant ρ hN g hg,
    map_fixOf_conj ρ g (fun x => map_conj_spRadFix hf hnd hp0 hpF g.2 hg x)]

omit [FiniteDimensional (ZMod 2) V] in
theorem spRadDecomp_apply (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    {N : Submodule (ZMod 2) M} (hN : SpInvariant ρ F N) {p p₁ : V} (hpF : p ∈ spPerp f F)
    (hp₁F : p₁ ∈ spPerp f F) (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0) (hD : SpRadDecomp ρ F N p p₁)
    (g : TauCeti.BilinForm.isometryGroup f) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    SpRadDecomp ρ F N ((g : V ≃ₗ[ZMod 2] V) p) ((g : V ≃ₗ[ZMod 2] V) p₁) := by
  have h1 := map_inf_fixOf_spRadFix ρ hf hnd hN g hg hpF hp0
  have h2 := map_inf_fixOf_spRadFix ρ hf hnd hN g hg hp₁F hp₁0
  constructor
  · rw [← h1, ← h2, ← Submodule.map_sup, hD.1, map_eq_of_spInvariant ρ hN g hg]
  · rw [← h1, ← h2, ← Submodule.map_inf _ (ρ g).injective, hD.2, Submodule.map_bot]

theorem spRadDecomp_of_pair (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {N : Submodule (ZMod 2) M} (hN : SpInvariant ρ F N)
    {p p₁ p' p₁' : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F)
    (hp'F : p' ∈ spPerp f F) (hp₁'F : p₁' ∈ spPerp f F) (hpp₁ : f p p₁ = 1)
    (hpp₁' : f p' p₁' = 1) (hD : SpRadDecomp ρ F N p p₁) : SpRadDecomp ρ F N p' p₁' := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  obtain ⟨hp'0, -, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁')
  obtain ⟨g, hg, hgp, hgp₁⟩ := exists_mem_spRadGen_apply_eq_pair hf hnd hF hpF hp₁F hp'F hp₁'F
    hp0 hp'0 hpp₁ hpp₁'
  have hgS := spRadGen_le_spFix F hg
  have := spRadDecomp_apply ρ hf hnd hN hpF hp₁F hp0 hp₁0 hD ⟨g, hgS.1⟩ hgS.2
  rwa [← hgp, ← hgp₁]

theorem sp_finrank_eq_two_mul (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {N : Submodule (ZMod 2) M}
    (hN : SpInvariant ρ F N) {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F)
    (hpp₁ : f p p₁ = 1) (hD : SpRadDecomp ρ F N p p₁) :
    finrank (ZMod 2) ↥(N ⊓ fixOf ρ (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V))) =
        finrank (ZMod 2) ↥(N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) ∧
      finrank (ZMod 2) N =
        2 * finrank (ZMod 2) ↥(N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  obtain ⟨g, hg, hgp⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hpF hp₁F hp0 hp₁0
  have hgS := spRadGen_le_spFix F hg
  have h1 := map_inf_fixOf_spRadFix ρ hf hnd hN ⟨g, hgS.1⟩ hgS.2 hpF hp0
  have hdim : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V))) =
      finrank (ZMod 2) ↥(N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) := by
    rw [← hgp]
    rw [show (g : V ≃ₗ[ZMod 2] V) =
      ((⟨g, hgS.1⟩ : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V) from rfl, ← h1]
    exact LinearEquiv.finrank_map_eq _ _
  refine ⟨hdim, ?_⟩
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)))
    (N ⊓ fixOf ρ (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V)))
  rw [hD.1, hD.2, finrank_bot, add_zero] at h2
  omega

theorem sp_timmesfeld_2_1_b0 (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {m : ℕ} (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m)
    {N : Submodule (ZMod 2) M} (hN : SpInvariant ρ F N) {p p₁ : V} (hpF : p ∈ spPerp f F)
    (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) (hD : SpRadDecomp ρ F N p p₁)
    (x : TauCeti.BilinForm.isometryGroup f) (hx : (x : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p₁)
    (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) (hxa : ¬ IsSpTypeA f x 2) :
    N ⊓ fixSpace (ρ x) = N ⊓ fixOf ρ (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V)) ∧
      N.map ((ρ x : M →ₗ[ZMod 2] M) - 1) =
        N ⊓ fixOf ρ (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V)) := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hgen : (spRadFix f F p₁ : Set (V ≃ₗ[ZMod 2] V)) ⊆
      Subgroup.closure (insert (x : V ≃ₗ[ZMod 2] V) (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) := by
    rw [← spFix_eq_closure_insert hf hnd hF hdim hpF hp₁F hpp₁ hx hx1 hxa]
    exact fun t ht => spRadFix_le_spFix F p₁ ht
  have hLX : (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ⊆ TauCeti.BilinForm.isometryGroup f :=
    fun t ht => (spRadFix_le_spFix F p ht).1
  have h1 := inf_fixSpace_eq_of_compl ρ hD.1 hD.2 hLX x hx hgen
  refine ⟨h1, ?_⟩
  obtain ⟨u, -, hp₁u, hxu⟩ := exists_eq_spSiegel_one_of_not_isSpTypeA hf hnd hp₁F hp₁0 hx hx1 hxa
  have hxx : ρ x * ρ x = 1 := by
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by
      change (x : V ≃ₗ[ZMod 2] V) * x = 1
      rw [hxu]
      exact spSiegel_mul_self hf hp₁u 1)
    rw [this, map_one]
  have hdims := sp_finrank_eq_two_mul ρ hf hnd hF hN hpF hp₁F hpp₁ hD
  rw [← h1]
  refine map_sub_one_eq_inf_fixSpace hxx (fun v hv => hN x hx.2 v hv) ?_
  rw [h1, hdims.1, hdims.2]

omit [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) M] in
theorem spInvariant_inf_fixOf (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    {N : Submodule (ZMod 2) M} (hN : SpInvariant ρ F N) {p p₁ : V} (hpF : p ∈ spPerp f F)
    (hp0 : p ≠ 0) :
    SpInvariant ρ (F ⊔ Submodule.span (ZMod 2) {p, p₁})
      (N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) := by
  intro g hgK v hv
  obtain ⟨hgF, hgp, -⟩ := mem_fixGroup_sup_span_pair.mp hgK
  have hmap := map_fixOf_conj ρ g (fun x => map_conj_spRadFix hf hnd hp0 hpF g.2 hgF x)
  rw [hgp] at hmap
  refine ⟨hN g hgF v hv.1, ?_⟩
  rw [← hmap]
  exact ⟨v, hv.2, rfl⟩

theorem sp_timmesfeld_2_1_b2 (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ spPerp f F = ⊥) {m : ℕ} (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m)
    {N : Submodule (ZMod 2) M} (hN : SpInvariant ρ F N) {p p₁ : V} (hpF : p ∈ spPerp f F)
    (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1) (hD : SpRadDecomp ρ F N p p₁) {p' p₁' : V}
    (hp'K : p' ∈ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁}))
    (hp₁'K : p₁' ∈ spPerp f (F ⊔ Submodule.span (ZMod 2) {p, p₁})) (hpp₁' : f p' p₁' = 1) :
    SpInvariant ρ (F ⊔ Submodule.span (ZMod 2) {p, p₁})
        (N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) ∧
      SpRadDecomp ρ (F ⊔ Submodule.span (ZMod 2) {p, p₁})
        (N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) p' p₁' := by
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  set W := N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) with hWdef
  obtain ⟨hp0, -, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  obtain ⟨hp'0, hp₁'0, -⟩ :=
    linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁')
  have hW : SpInvariant ρ K W := spInvariant_inf_fixOf ρ hf hnd hN hpF hp0
  refine ⟨hW, ?_⟩
  have hp'F : p' ∈ spPerp f F := spPerp_sup_span_pair_le hp'K
  have hp₁'F : p₁' ∈ spPerp f F := spPerp_sup_span_pair_le hp₁'K
  have hp₁'p' : f p₁' p' = 1 := by rw [isAlt_symm hf, hpp₁']
  have hzero : ∀ {a : V}, f a 0 = 0 := fun {a} => map_zero _
  have haR : spSiegel f hf p' 0 1 ∈ spRadFix f K p' :=
    (mem_spRadFix_iff hf hnd hp'0 hp'K).mpr ⟨0, Submodule.zero_mem _, hzero, 1, rfl⟩
  have hbR : spSiegel f hf p₁' 0 1 ∈ spRadFix f K p₁' :=
    (mem_spRadFix_iff hf hnd hp₁'0 hp₁'K).mpr ⟨0, Submodule.zero_mem _, hzero, 1, rfl⟩
  have hne1 : ∀ {a : V}, a ≠ 0 → spSiegel f hf a 0 1 ≠ 1 := fun {a} ha0 h =>
    one_ne_zero ((spSiegel_eq_one_iff hf hnd ha0 hzero 1).mp h).2
  set a : TauCeti.BilinForm.isometryGroup f := ⟨spSiegel f hf p' 0 1, haR.1.1⟩ with ha
  set b : TauCeti.BilinForm.isometryGroup f := ⟨spSiegel f hf p₁' 0 1, hbR.1.1⟩ with hb
  have hD' := spRadDecomp_of_pair ρ hf hnd hF hN hpF hp₁F hp'F hp₁'F hpp₁ hpp₁' hD
  have hDa := (sp_timmesfeld_2_1_b0 ρ hf hnd hF hdim hN hp₁'F hp'F hp₁'p' hD'.symm a
    (spRadFix_anti le_sup_left p' haR) (hne1 hp'0) (not_isSpTypeA_spSiegel_one hf hnd hp'0 hzero)).1
  have hDb := (sp_timmesfeld_2_1_b0 ρ hf hnd hF hdim hN hp'F hp₁'F hpp₁' hD' b
    (spRadFix_anti le_sup_left p₁' hbR) (hne1 hp₁'0)
    (not_isSpTypeA_spSiegel_one hf hnd hp₁'0 hzero)).1
  have haa : ρ a * ρ a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext (spSiegel_mul_self hf hzero 1), map_one]
  have hbb : ρ b * ρ b = 1 := by
    rw [← map_mul, show b * b = 1 from Subtype.ext (spSiegel_mul_self hf hzero 1), map_one]
  have haW : ∀ w ∈ W, ρ a w ∈ W := hW a haR.2
  have hbW : ∀ w ∈ W, ρ b w ∈ W := hW b hbR.2
  have hWN : W ≤ N := inf_le_left
  have hab : W ⊓ fixSpace (ρ a) ⊓ fixSpace (ρ b) = ⊥ := by
    rw [eq_bot_iff, ← hD'.2]
    rintro v ⟨⟨hvW, hva⟩, hvb⟩
    have h1 : v ∈ N ⊓ fixSpace (ρ a) := ⟨hWN hvW, hva⟩
    have h2 : v ∈ N ⊓ fixSpace (ρ b) := ⟨hWN hvW, hvb⟩
    rw [hDa] at h1
    rw [hDb] at h2
    exact ⟨h1, h2⟩
  have hsum := sup_inf_fixSpace_eq haa hbb haW hbW hab
  have hWa : W ⊓ fixSpace (ρ a) = W ⊓ fixOf ρ (spRadFix f K p' : Set (V ≃ₗ[ZMod 2] V)) := by
    refine le_antisymm (fun v hv => ⟨hv.1, ?_⟩)
      (fun v hv => ⟨hv.1, mem_fixSpace.mpr (hv.2 a haR)⟩)
    have h1 : v ∈ N ⊓ fixSpace (ρ a) := ⟨hWN hv.1, hv.2⟩
    rw [hDa] at h1
    exact fixOf_anti ρ (fun t ht => spRadFix_anti le_sup_left p' ht) h1.2
  have hWb : W ⊓ fixSpace (ρ b) = W ⊓ fixOf ρ (spRadFix f K p₁' : Set (V ≃ₗ[ZMod 2] V)) := by
    refine le_antisymm (fun v hv => ⟨hv.1, ?_⟩)
      (fun v hv => ⟨hv.1, mem_fixSpace.mpr (hv.2 b hbR)⟩)
    have h1 : v ∈ N ⊓ fixSpace (ρ b) := ⟨hWN hv.1, hv.2⟩
    rw [hDb] at h1
    exact fixOf_anti ρ (fun t ht => spRadFix_anti le_sup_left p₁' ht) h1.2
  refine ⟨by rw [← hWa, ← hWb]; exact hsum, ?_⟩
  rw [← hWa, ← hWb, eq_bot_iff, ← hab]
  rintro v ⟨⟨hvW, hva⟩, -, hvb⟩
  exact ⟨⟨hvW, hva⟩, hvb⟩

theorem sp_timmesfeld_2_1_b_dvd (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    ∀ (m : ℕ) {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M} {p p₁ : V},
      F ⊓ spPerp f F = ⊥ → 1 ≤ m → finrank (ZMod 2) (spPerp f F) = 2 * m →
      SpInvariant ρ F N → p ∈ spPerp f F → p₁ ∈ spPerp f F → f p p₁ = 1 →
      SpRadDecomp ρ F N p p₁ → 2 ^ m ∣ finrank (ZMod 2) N := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F N p p₁ hF hm hdim hN hpF hp₁F hpp₁ hD
  have htwo := (sp_finrank_eq_two_mul ρ hf hnd hF hN hpF hp₁F hpp₁ hD).2
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · rw [show m = 1 by omega, pow_one, htwo]
    exact dvd_mul_right _ _
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ spPerp f K = ⊥ := sup_span_pair_inf_spPerp_eq_bot hf hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (spPerp f K) + 2 = finrank (ZMod 2) (spPerp f F) :=
    finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
  have hne : spPerp f K ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hKdim
    omega
  obtain ⟨p', hp'K, hp'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨p₁', hp₁'K, hpp₁'⟩ := sp_exists_partner hf hnd hK hp'K hp'0
  obtain ⟨hW, hDW⟩ := sp_timmesfeld_2_1_b2 ρ hf hnd hF hdim hN hpF hp₁F hpp₁ hD hp'K hp₁'K hpp₁'
  have := ih (m - 1) (by omega) hK (by omega) (by omega) hW hp'K hp₁'K hpp₁' hDW
  rw [htwo, show m = (m - 1) + 1 by omega, pow_succ, mul_comm]
  exact mul_dvd_mul_left 2 this

theorem sp_timmesfeld_2_1_b_dvd_sp (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hc : IsCompl (fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)))) :
    2 ^ m ∣ finrank (ZMod 2) M := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ spPerp f ⊥ = ⊥ := bot_inf_eq _
  have hD : SpRadDecomp ρ ⊥ ⊤ p p₁ := by
    rw [SpRadDecomp, spRadFix_bot, spRadFix_bot, top_inf_eq, top_inf_eq]
    exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩
  have h := sp_timmesfeld_2_1_b_dvd ρ hf hnd m hF hm (by rw [spPerp_bot, finrank_top]; exact hdim)
    (fun g _ v _ => Submodule.mem_top) (by rw [spPerp_bot]; exact Submodule.mem_top)
    (by rw [spPerp_bot]; exact Submodule.mem_top) hpp₁ hD
  rwa [finrank_top] at h

end S2

end CFSG.LargeExtraspecial
