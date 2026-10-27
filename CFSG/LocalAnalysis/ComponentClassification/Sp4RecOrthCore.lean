module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecOrthFact
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPairTwo
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSymp

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup Module

theorem isPComponent_map_of_injective_normal {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (φ : X →* Y) (hφ : Function.Injective φ) [φ.range.Normal] {L : Subgroup X}
    (hL : IsPComponent 2 L) : IsPComponent 2 (L.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e := MonoidHom.ofInjective hφ
  have h1 := CatalogueBAlternating.pComponent_of_normal_subgroup 2 φ.range (L.map e.toMonoidHom)
    (CatalogueBAlternating.pComponent_map_equiv 2 e L hL)
  have h2 : (L.map e.toMonoidHom).map φ.range.subtype = L.map φ := by
    rw [map_map]
    rfl
  rwa [h2] at h1

theorem commutator_prod' {G G' : Type*} [Group G] [Group G'] :
    commutator (G × G') = (commutator G).prod (commutator G') := by
  rw [_root_.commutator_def, _root_.commutator_def, _root_.commutator_def, ← top_prod_top,
    commutator_prod_prod]

theorem map_commutator_equiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') :
    (commutator G).map e.toMonoidHom = commutator G' := by
  rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
    map_top_of_surjective _ e.surjective]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
theorem mem_commutator_orthogonal {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (ht : t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    ∃ t' ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q), (t' : V ≃ₗ[K] V) = t := by
  rw [← map_subtype_commutator] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact ⟨t', ht', rfl⟩

theorem orth_left_false (hodd : Odd (Nat.card K)) {Q : QuadraticForm K V}
    {P : Type*} [Group P] [Finite P] {x : P} {K₁ K₂ : Subgroup P} (hc : PairConfig P x K₁ K₂)
    {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] (π : X →* P) (κ : X →* Y)
    (hκ : Function.Injective κ) [κ.range.Normal] (ι : Y →* (V ≃ₗ[K] V))
    (hcomm : commutator Y ≤ κ.range) {M₁ M₂ : Subgroup X} (hM₁ : IsPComponent 2 M₁)
    (hM₂ : IsPComponent 2 M₂) (hne : M₁ ≠ M₂)
    (hK₁ : ∀ y ∈ M₁, π y ∈ K₁) (hs₁ : ∀ k ∈ K₁, ∃ y ∈ M₁, π y = k)
    (hs₂ : ∀ k ∈ K₂, ∃ y ∈ M₂, π y = k) (hx : ∀ y, π y * x = x * π y)
    (hone : ∀ y, π y = 1 → ∃ c : K, ∀ v, ι (κ y) v = c • v) {A : V ≃ₗ[K] V}
    (hxfib : ∀ y, π y = x → ∃ c : K, ∀ v, A v = c • ι (κ y) v)
    {W₁ W₂ : Submodule K V} (hW : IsCompl W₁ W₂) (hW₁ : W₁ ≠ ⊥) (hW₂ : W₂ ≠ ⊥)
    (hdim : 7 ≤ finrank K V)
    (hnd₁ : (Q.comp W₁.subtype).polarBilin.Nondegenerate)
    (hnd₂ : (Q.comp W₂.subtype).polarBilin.Nondegenerate)
    (E : Y ≃* TauCeti.QuadraticMap.orthogonalGroup (Q.comp W₁.subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp W₂.subtype))
    (hact₁ : ∀ (y : Y) (v : W₁), ι y v = (((E y).1 : W₁ ≃ₗ[K] W₁) v : V))
    (hact₂ : ∀ (y : Y) (v : W₂), ι y v = (((E y).2 : W₂ ≃ₗ[K] W₂) v : V))
    {b : K} (hb : b ≠ 0) (hA₁ : ∀ v ∈ W₁, A v = b • v) (hA₂ : ∀ v ∈ W₂, A v = (-b) • v)
    (hleft : (M₁.map κ).map E.toMonoidHom =
      (((M₁.map κ).map E.toMonoidHom).map (MonoidHom.fst _ _)).prod ⊥) : False := by
  classical
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  set N₁ := (M₁.map κ).map E.toMonoidHom with hN₁def
  set N₂ := (M₂.map κ).map E.toMonoidHom with hN₂def
  have hN₁ : IsPComponent 2 N₁ := CatalogueBAlternating.pComponent_map_equiv 2 E _
    (isPComponent_map_of_injective_normal κ hκ hM₁)
  have hN₂ : IsPComponent 2 N₂ := CatalogueBAlternating.pComponent_map_equiv 2 E _
    (isPComponent_map_of_injective_normal κ hκ hM₂)
  have hNne : N₁ ≠ N₂ := fun h => hne (map_injective hκ (map_injective E.injective h))
  have hL₁ := isPComponent_fst hN₁ hleft
  set L₁ := N₁.map (MonoidHom.fst _ _) with hL₁def
  obtain ⟨u₁, hu₁W, hu₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₁
  obtain ⟨u₂, hu₂W, hu₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₂
  have hlift : ∀ (g₁ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W₁.subtype))
      (g₂ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W₂.subtype)),
      g₁ ∈ commutator _ → g₂ ∈ commutator _ → ∃ y : X, E (κ y) = (g₁, g₂) := by
    intro g₁ g₂ h₁ h₂
    have hp : (g₁, g₂) ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup (Q.comp W₁.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp W₂.subtype)) := by
      rw [commutator_prod']
      exact ⟨h₁, h₂⟩
    have hY : E.symm (g₁, g₂) ∈ commutator Y := by
      rw [← map_commutator_equiv E.symm]
      exact mem_map_of_mem _ hp
    obtain ⟨y, hy⟩ := hcomm hY
    exact ⟨y, by rw [hy, MulEquiv.apply_symm_apply]⟩
  have hleftmem : ∀ m ∈ M₁, (E (κ m)).1 ∈ L₁ ∧ (E (κ m)).2 = 1 := by
    intro m hm
    have h1 : E (κ m) ∈ N₁ := ⟨κ m, mem_map_of_mem κ hm, rfl⟩
    rw [hleft] at h1
    exact ⟨h1.1, h1.2⟩
  have hcommute : ∀ y m : X, E (κ y) * E (κ m) = E (κ m) * E (κ y) → y * m = m * y := by
    intro y m h
    apply hκ
    apply E.injective
    rw [map_mul, map_mul, map_mul, map_mul, h]
  have hsc : ∀ (c : K) {v w : V}, v ≠ 0 → w ≠ 0 → c • v = -v → c • w = w → False := by
    intro c v w hv hw h₁ h₂
    have e₁ : c = -1 := eq_of_smul_eq hv (h₁.trans (neg_one_smul K v).symm)
    have e₂ : c = 1 := eq_of_smul_eq hw (h₂.trans (one_smul K w).symm)
    apply h2
    have : (1 : K) = -1 := e₂.symm.trans e₁
    linear_combination this
  rcases orth_pComponent_cases hodd hnd₁ hL₁ with hi | ⟨h4, j, hj, hjj, hjL⟩
  ·
    have h3 : 3 ≤ finrank K W₁ := by
      by_contra hlt
      exact CatalogueBOrthogonal.orthogonal_small_no_pComponent _ h2 hnd₁ (by omega) 2 _ hL₁
    obtain ⟨t, ht, htt, v₁, v₂, hv₁, hv₂, htv₁, htv₂⟩ := exists_plane_reflection hodd hnd₁ h3
    obtain ⟨t', ht', rfl⟩ := mem_commutator_orthogonal ht
    have htN : (t', (1 : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W₂.subtype))) ∈ N₁ := by
      rw [hleft, hi]
      exact ⟨ht', one_mem _⟩
    obtain ⟨_, ⟨m, hm, rfl⟩, hmE⟩ := htN
    have hmE' : E (κ m) = (t', 1) := hmE
    have hm2 : m * m = 1 := by
      apply hκ
      apply E.injective
      rw [map_mul, map_mul, hmE', Prod.mk_mul_mk, one_mul, map_one, map_one]
      have : t' * t' = 1 := Subtype.ext htt
      rw [this]
      rfl
    have hπ2 : π m ^ 2 = 1 := by rw [pow_two, ← map_mul, hm2, map_one]
    have hπ1 : π m ≠ 1 := by
      intro h
      obtain ⟨c, hcv⟩ := hone m h
      refine hsc c (v := (v₁ : V)) (w := u₂) (fun h0 => hv₁ (Subtype.ext h0)) hu₂0 ?_ ?_
      · rw [← hcv, hact₁ _ v₁, hmE']
        exact congrArg Subtype.val htv₁
      · have := hact₂ (κ m) ⟨u₂, hu₂W⟩
        rw [hmE'] at this
        exact (hcv u₂).symm.trans this
    have hord : orderOf (π m) = 2 := orderOf_eq_prime hπ2 hπ1
    have hmx := hc.involution_K _ (hK₁ m hm) hord
    obtain ⟨c, hcv⟩ := hxfib m hmx
    have e₁ : b • (v₁ : V) = c • -(v₁ : V) := by
      rw [← hA₁ _ v₁.2, hcv, hact₁ _ v₁, hmE']
      exact congrArg (c • ·) (congrArg Subtype.val htv₁)
    have e₂ : b • (v₂ : V) = c • (v₂ : V) := by
      rw [← hA₁ _ v₂.2, hcv, hact₁ _ v₂, hmE']
      exact congrArg (c • ·) (congrArg Subtype.val htv₂)
    rw [smul_neg, ← neg_smul] at e₁
    have hb₁ := eq_of_smul_eq (fun h0 => hv₁ (Subtype.ext h0)) e₁
    have hb₂ := eq_of_smul_eq (fun h0 => hv₂ (Subtype.ext h0)) e₂
    apply hb
    have : (2 : K) * b = 0 := by linear_combination hb₁ + hb₂
    exact (mul_eq_zero.mp this).resolve_left h2
  ·
    rcases CatalogueBProjectiveInvolutionProduct.pComponent_eq_left_or_right_factor 2 N₂ hN₂ with
      hl₂ | hr₂
    ·
      have hsum := Submodule.finrank_add_eq_of_isCompl hW
      have h3 : 3 ≤ finrank K W₂ := by omega
      obtain ⟨t, ht, htt, v₁, v₂, hv₁, hv₂, htv₁, htv₂⟩ := exists_plane_reflection hodd hnd₂ h3
      obtain ⟨t', ht', rfl⟩ := mem_commutator_orthogonal ht
      obtain ⟨y, hy⟩ := hlift 1 t' (one_mem _) ht'
      have hleftmem₂ : ∀ m ∈ M₂, (E (κ m)).2 = 1 := by
        intro m hm
        have h1 : E (κ m) ∈ N₂ := ⟨κ m, mem_map_of_mem κ hm, rfl⟩
        rw [hl₂] at h1
        exact h1.2
      have hyc : ∀ m : X, (E (κ m)).2 = 1 → y * m = m * y := by
        intro m hm
        apply hcommute
        rw [hy, Prod.ext_iff]
        simp only [Prod.fst_mul, Prod.snd_mul, hm, one_mul, mul_one, and_self]
      have hy2 : y * y = 1 := by
        apply hκ
        apply E.injective
        rw [map_mul, map_mul, hy, Prod.mk_mul_mk, one_mul, map_one, map_one]
        have : t' * t' = 1 := Subtype.ext htt
        rw [this]
        rfl
      refine hc.false_of_klein (z := π y) (by rw [pow_two, ← map_mul, hy2, map_one]) ?_ ?_
        (hx y) ?_ ?_
      · intro h
        obtain ⟨c, hcv⟩ := hone y h
        refine hsc c (v := (v₁ : V)) (w := u₁) (fun h0 => hv₁ (Subtype.ext h0)) hu₁0 ?_ ?_
        · rw [← hcv, hact₂ _ v₁, hy]
          exact congrArg Subtype.val htv₁
        · have := hact₁ (κ y) ⟨u₁, hu₁W⟩
          rw [hy] at this
          exact (hcv u₁).symm.trans this
      · intro h
        obtain ⟨c, hcv⟩ := hxfib y h
        have e₁ : (-b) • (v₁ : V) = c • -(v₁ : V) := by
          rw [← hA₂ _ v₁.2, hcv, hact₂ _ v₁, hy]
          exact congrArg (c • ·) (congrArg Subtype.val htv₁)
        have e₂ : (-b) • (v₂ : V) = c • (v₂ : V) := by
          rw [← hA₂ _ v₂.2, hcv, hact₂ _ v₂, hy]
          exact congrArg (c • ·) (congrArg Subtype.val htv₂)
        rw [smul_neg, ← neg_smul] at e₁
        have hb₁ := eq_of_smul_eq (fun h0 => hv₁ (Subtype.ext h0)) e₁
        have hb₂ := eq_of_smul_eq (fun h0 => hv₂ (Subtype.ext h0)) e₂
        apply hb
        have : (2 : K) * b = 0 := by linear_combination -hb₁ - hb₂
        exact (mul_eq_zero.mp this).resolve_left h2
      · intro k hk
        obtain ⟨m, hm, rfl⟩ := hs₁ k hk
        rw [← map_mul, ← map_mul, hyc m (hleftmem m hm).2]
      · intro k hk
        obtain ⟨m, hm, rfl⟩ := hs₂ k hk
        rw [← map_mul, ← map_mul, hyc m (hleftmem₂ m hm)]
    ·
      obtain ⟨y, hy⟩ := hlift j 1 hj (one_mem _)
      have hrightmem₂ : ∀ m ∈ M₂, (E (κ m)).1 = 1 := by
        intro m hm
        have h1 : E (κ m) ∈ N₂ := ⟨κ m, mem_map_of_mem κ hm, rfl⟩
        rw [hr₂] at h1
        exact h1.1
      have hjj' : j * j * (j * j) = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro v
        change (j : W₁ ≃ₗ[K] W₁) ((j : W₁ ≃ₗ[K] W₁) ((j : W₁ ≃ₗ[K] W₁) ((j : W₁ ≃ₗ[K] W₁) v))) = v
        rw [hjj, hjj, neg_neg]
      refine hc.false_of_order_four (z := π y) ?_ ?_ ?_ ?_
      · have hy4 : y ^ 4 = 1 := by
          apply hκ
          apply E.injective
          rw [map_pow, map_pow, hy, map_one, map_one]
          rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two, Prod.mk_mul_mk,
            Prod.mk_mul_mk, one_mul, one_mul, hjj']
          rfl
        rw [← map_pow, hy4, map_one]
      · intro h
        rw [pow_two, ← map_mul] at h
        obtain ⟨c, hcv⟩ := hone (y * y) h
        have hyy : E (κ (y * y)) = (j * j, 1) := by
          rw [map_mul, map_mul, hy, Prod.mk_mul_mk, one_mul]
        refine hsc c (v := u₁) (w := u₂) hu₁0 hu₂0 ?_ ?_
        · rw [← hcv, hact₁ _ ⟨u₁, hu₁W⟩, hyy]
          change (((j : W₁ ≃ₗ[K] W₁) ((j : W₁ ≃ₗ[K] W₁) ⟨u₁, hu₁W⟩) : W₁) : V) = -u₁
          rw [hjj]
          rfl
        · have := hact₂ (κ (y * y)) ⟨u₂, hu₂W⟩
          rw [hyy] at this
          exact (hcv u₂).symm.trans this
      · intro k hk
        obtain ⟨m, hm, rfl⟩ := hs₁ k hk
        rw [← map_mul, ← map_mul]
        congr 1
        apply hcommute
        obtain ⟨hmL, hm1⟩ := hleftmem m hm
        rw [hy, Prod.ext_iff]
        simp only [Prod.fst_mul, Prod.snd_mul, hm1, mul_one, and_true]
        exact (hjL _ hmL).symm
      · intro k hk
        obtain ⟨m, hm, rfl⟩ := hs₂ k hk
        rw [← map_mul, ← map_mul]
        congr 1
        apply hcommute
        rw [hy, Prod.ext_iff]
        simp only [Prod.fst_mul, Prod.snd_mul, hrightmem₂ m hm, one_mul, mul_one, and_self]

end CFSG.ComponentClassification.Sp4Rec
