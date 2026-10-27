module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.QuasithinUnique.Setup.X1

section TwoMax

@[expose] def TwoMaxOver (K : Type*) [Group K] (R : Subgroup K) : Prop :=
  ∃ U₁ U₂ : Subgroup K, R ≤ U₁ ∧ R ≤ U₂ ∧ IsCoatom U₁ ∧ IsCoatom U₂ ∧
    Nat.card U₁ ≠ Nat.card U₂ ∧ ∀ M : Subgroup K, R ≤ M → IsCoatom M → M = U₁ ∨ M = U₂

variable {K K' : Type*} [Group K] [Group K']

theorem isCoatom_map' (f : K ≃* K') {U : Subgroup K} :
    IsCoatom (U.map f.toMonoidHom) ↔ IsCoatom U :=
  OrderIso.isCoatom_iff (f.mapSubgroup) U

theorem TwoMaxOver.map {R : Subgroup K} (h : TwoMaxOver K R) (f : K ≃* K') :
    TwoMaxOver K' (R.map f.toMonoidHom) := by
  obtain ⟨U₁, U₂, h1, h2, c1, c2, hne, hall⟩ := h
  refine ⟨U₁.map f.toMonoidHom, U₂.map f.toMonoidHom, Subgroup.map_mono h1,
    Subgroup.map_mono h2, (isCoatom_map' f).2 c1, (isCoatom_map' f).2 c2, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective f.injective, Subgroup.card_map_of_injective f.injective]
  · intro M hM hMc
    have hM' : R ≤ M.map f.symm.toMonoidHom := by
      intro x hx
      exact ⟨f x, hM ⟨x, hx, rfl⟩, by simp⟩
    have hc : IsCoatom (M.map f.symm.toMonoidHom) := (isCoatom_map' f.symm).2 hMc
    have hMeq : M = (M.map f.symm.toMonoidHom).map f.toMonoidHom := by
      rw [Subgroup.map_map]
      ext x
      simp
    rcases hall _ hM' hc with h | h
    · left; rw [hMeq, h]
    · right; rw [hMeq, h]

theorem TwoMaxOver.of_sylow [Finite K] {R R' : Subgroup K} (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.index) (hR' : IsPGroup 2 R') (hR'i : ¬ 2 ∣ R'.index)
    (h : TwoMaxOver K R) : TwoMaxOver K R' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 K := hR.toSylow hRi
  let S' : Sylow 2 K := hR'.toSylow hR'i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S S'
  have hconj : (R.map (MulAut.conj g).toMonoidHom) = R' := by
    have := congrArg (fun T : Sylow 2 K => (T : Subgroup K)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
    exact this
  rw [← hconj]
  exact h.map (MulAut.conj g)

end TwoMax

section Extension

variable {X : Type*} [Group X] (T K : Subgroup X) [K.Normal]

theorem conj_stable_of_twoMaxOver (U₁ U₂ : Subgroup K)
    (h1 : (T ⊓ K).subgroupOf K ≤ U₁) (h2 : (T ⊓ K).subgroupOf K ≤ U₂)
    (c1 : IsCoatom U₁) (c2 : IsCoatom U₂) (hcard : Nat.card U₁ ≠ Nat.card U₂)
    (hall : ∀ M : Subgroup K, (T ⊓ K).subgroupOf K ≤ M → IsCoatom M → M = U₁ ∨ M = U₂)
    {t : X} (ht : t ∈ T) (U : Subgroup K) (hU : U = U₁ ∨ U = U₂) :
    U.map (MulAut.conjNormal t : MulAut K).toMonoidHom = U := by
  have hRU : (T ⊓ K).subgroupOf K ≤ U := by rcases hU with rfl | rfl <;> assumption
  have hcU : IsCoatom U := by rcases hU with rfl | rfl <;> assumption
  have hR : (T ⊓ K).subgroupOf K ≤ U.map (MulAut.conjNormal t : MulAut K).toMonoidHom := by
    intro x hx
    have hx' : (x : X) ∈ T := (Subgroup.mem_inf.1 hx).1
    have hy : ((MulAut.conjNormal t⁻¹ : MulAut K) x : K) ∈ (T ⊓ K).subgroupOf K := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨?_, ((MulAut.conjNormal t⁻¹ : MulAut K) x).2⟩
      rw [MulAut.conjNormal_apply]
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hx') (by simpa using ht)
    refine ⟨(MulAut.conjNormal t⁻¹ : MulAut K) x, hRU hy, ?_⟩
    show (MulAut.conjNormal t : MulAut K) ((MulAut.conjNormal t⁻¹ : MulAut K) x) = x
    rw [← MulAut.mul_apply, ← map_mul]
    simp
  have hc : IsCoatom (U.map (MulAut.conjNormal t : MulAut K).toMonoidHom) :=
    (isCoatom_map' (MulAut.conjNormal t : MulAut K)).2 hcU
  have hcard' : Nat.card (U.map (MulAut.conjNormal t : MulAut K).toMonoidHom) = Nat.card U :=
    Subgroup.card_map_of_injective (MulAut.conjNormal t : MulAut K).injective
  rcases hall _ hR hc with h | h
  · rcases hU with rfl | rfl
    · exact h
    · rw [h] at hcard'
      exact absurd hcard' hcard
  · rcases hU with rfl | rfl
    · rw [h] at hcard'
      exact absurd hcard'.symm hcard
    · exact h

theorem exists_coatom_of_stable (hKT : K ⊔ T = ⊤) (U : Subgroup K)
    (hRU : (T ⊓ K).subgroupOf K ≤ U) (hcU : IsCoatom U)
    (hstab : ∀ {t : X}, t ∈ T → U.map (MulAut.conjNormal t : MulAut K).toMonoidHom = U) :
    ∃ V : Subgroup X, T ≤ V ∧ IsCoatom V ∧ V ⊓ K = U.map K.subtype := by
  set U' : Subgroup X := U.map K.subtype with hU'
  have hU'K : U' ≤ K := Subgroup.map_subtype_le U
  have hfwd : ∀ {t : X}, t ∈ T → ∀ x ∈ U', t * x * t⁻¹ ∈ U' := by
    intro t ht x hx
    obtain ⟨u, hu, rfl⟩ := hx
    have : (MulAut.conjNormal t : MulAut K) u ∈
        U.map (MulAut.conjNormal t : MulAut K).toMonoidHom := ⟨u, hu, rfl⟩
    rw [hstab ht] at this
    exact ⟨_, this, by simp [MulAut.conjNormal_apply]⟩
  have hnorm : T ≤ Subgroup.normalizer (U' : Set X) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hfwd ht x hx, fun hx => ?_⟩
    have := hfwd (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hmul : (↑(U' ⊔ T) : Set X) = (U' : Set X) * T :=
    Subgroup.coe_mul_of_right_le_normalizer_left U' T hnorm
  have hVK : (U' ⊔ T) ⊓ K = U' := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxV, hxK⟩ := hx
      have hxV' : x ∈ (↑(U' ⊔ T) : Set X) := hxV
      rw [hmul] at hxV'
      obtain ⟨u, hu, t, ht, rfl⟩ := hxV'
      have htK : t ∈ K := by
        have : u⁻¹ * (u * t) ∈ K := K.mul_mem (K.inv_mem (hU'K hu)) hxK
        simpa using this
      have htU : t ∈ U' := by
        have : (⟨t, htK⟩ : K) ∈ (T ⊓ K).subgroupOf K := Subgroup.mem_inf.2 ⟨ht, htK⟩
        exact ⟨⟨t, htK⟩, hRU this, rfl⟩
      exact U'.mul_mem hu htU
    · exact le_inf le_sup_left hU'K
  refine ⟨U' ⊔ T, le_sup_right, ⟨?_, ?_⟩, hVK⟩
  ·
    intro htop
    apply hcU.1
    rw [eq_top_iff]
    intro k _
    have hkK : (k : X) ∈ (U' ⊔ T) ⊓ K := ⟨htop ▸ Subgroup.mem_top _, k.2⟩
    rw [hVK] at hkK
    obtain ⟨u, hu, hue⟩ := hkK
    have : u = k := Subtype.ext hue
    exact this ▸ hu
  · intro Y hY
    by_contra hYtop
    have hTY : T ≤ Y := le_trans le_sup_right hY.le
    have hUY : U ≤ Y.subgroupOf K := by
      intro u hu
      exact hY.le (Subgroup.mem_sup_left ⟨u, hu, rfl⟩)
    rcases hcU.le_iff.1 hUY with h | h
    ·
      apply hYtop
      rw [eq_top_iff, ← hKT]
      refine sup_le (fun k hk => ?_) hTY
      have : (⟨k, hk⟩ : K) ∈ Y.subgroupOf K := h ▸ Subgroup.mem_top _
      exact this
    ·
      have hYK : Y ⊓ K ≤ U' := by
        intro x hx
        have : (⟨x, hx.2⟩ : K) ∈ Y.subgroupOf K := hx.1
        rw [h] at this
        exact ⟨_, this, rfl⟩
      have hYle : Y ≤ U' ⊔ T := by
        intro y hy
        have hyk : y ∈ (↑(K ⊔ T) : Set X) := by rw [hKT]; exact Subgroup.mem_top y
        rw [Subgroup.normal_mul] at hyk
        obtain ⟨k, hk, t, ht, rfl⟩ := hyk
        have hkY : k ∈ Y ⊓ K := ⟨by
          have : k * t * t⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem (hTY ht))
          simpa using this, hk⟩
        have hkU : k ∈ (↑(U' ⊔ T) : Set X) := by
          rw [hmul]
          exact ⟨k, hYK hkY, 1, T.one_mem, by simp⟩
        exact (U' ⊔ T).mul_mem hkU (Subgroup.mem_sup_right ht)
      exact absurd hYle (not_le_of_gt hY)

theorem exists_two_coatoms_of_twoMaxOver (hKT : K ⊔ T = ⊤)
    (h : TwoMaxOver ↥K ((T ⊓ K).subgroupOf K)) :
    ∃ V₁ V₂ : Subgroup X, V₁ ≠ V₂ ∧ IsCoatom V₁ ∧ IsCoatom V₂ ∧ T ≤ V₁ ∧ T ≤ V₂ := by
  obtain ⟨U₁, U₂, h1, h2, c1, c2, hcard, hall⟩ := h
  have hstab : ∀ {t : X}, t ∈ T → ∀ U : Subgroup K, (U = U₁ ∨ U = U₂) →
      U.map (MulAut.conjNormal t : MulAut K).toMonoidHom = U :=
    fun ht U hU => conj_stable_of_twoMaxOver T K U₁ U₂ h1 h2 c1 c2 hcard hall ht U hU
  obtain ⟨V₁, hT1, hc1, hV1⟩ := exists_coatom_of_stable T K hKT U₁ h1 c1
    (fun ht => hstab ht U₁ (Or.inl rfl))
  obtain ⟨V₂, hT2, hc2, hV2⟩ := exists_coatom_of_stable T K hKT U₂ h2 c2
    (fun ht => hstab ht U₂ (Or.inr rfl))
  refine ⟨V₁, V₂, fun hne => ?_, hc1, hc2, hT1, hT2⟩
  have : U₁.map K.subtype = U₂.map K.subtype := by rw [← hV1, ← hV2, hne]
  have hU : U₁ = U₂ := Subgroup.map_injective K.subtype_injective this
  exact hcard (by rw [hU])

theorem index_inf_subgroupOf_eq [Finite X] (hKT : K ⊔ T = ⊤) :
    ((T ⊓ K).subgroupOf K).index = T.index := by
  have hq : K.relIndex T = K.index := by
    have h1 := Subgroup.relIndex_sup_right (H := T) (K := K)
    rw [sup_comm, hKT] at h1
    rw [← h1, Subgroup.relIndex_top_right]
  have hX : Nat.card K * K.index = Nat.card X := Subgroup.card_mul_index K
  have hT1 : Nat.card (K.subgroupOf T) * K.relIndex T = Nat.card T := by
    have := Subgroup.card_mul_index (K.subgroupOf T)
    exact this
  have hT2 : Nat.card (K.subgroupOf T) = Nat.card (T ⊓ K : Subgroup X) := by
    rw [← Subgroup.inf_subgroupOf_right K T,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K ⊓ T ≤ T)).toEquiv, inf_comm]
  have hK1 : Nat.card ((T ⊓ K).subgroupOf K) * ((T ⊓ K).subgroupOf K).index = Nat.card K :=
    Subgroup.card_mul_index _
  have hK2 : Nat.card ((T ⊓ K).subgroupOf K) = Nat.card (T ⊓ K : Subgroup X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).toEquiv
  have hT3 : Nat.card T * T.index = Nat.card X := Subgroup.card_mul_index T
  rw [hT2, hq] at hT1
  rw [hK2] at hK1
  have hpos : 0 < Nat.card (T ⊓ K : Subgroup X) * K.index :=
    Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card (T ⊓ K : Subgroup X) * K.index * ((T ⊓ K).subgroupOf K).index
      = Nat.card (T ⊓ K : Subgroup X) * ((T ⊓ K).subgroupOf K).index * K.index := by ring
    _ = Nat.card K * K.index := by rw [hK1]
    _ = Nat.card X := hX
    _ = Nat.card T * T.index := hT3.symm
    _ = Nat.card (T ⊓ K : Subgroup X) * K.index * T.index := by rw [← hT1]

theorem twoExtension_of_model {S : Type} [Group S] [Finite S] {R₀ : Subgroup S}
    (hR0 : IsPGroup 2 R₀) (hR0i : ¬ 2 ∣ R₀.index) (hmodel : TwoMaxOver S R₀)
    (X : Type) [Group X] [Finite X] (T K : Subgroup X) [K.Normal] (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hKT : K ⊔ T = ⊤) (e : ↥K ≃* S) :
    ∃ U₁ U₂ : Subgroup X, U₁ ≠ U₂ ∧ IsCoatom U₁ ∧ IsCoatom U₂ ∧ T ≤ U₁ ∧ T ≤ U₂ := by
  have hR1 : IsPGroup 2 ((T ⊓ K).subgroupOf K) :=
    (hT.to_le (inf_le_left : T ⊓ K ≤ T)).comap_subtype
  have hR1i : ¬ 2 ∣ ((T ⊓ K).subgroupOf K).index := by
    rw [index_inf_subgroupOf_eq T K hKT]; exact hTi
  have hmap : IsPGroup 2 (((T ⊓ K).subgroupOf K).map e.toMonoidHom) := hR1.map e.toMonoidHom
  have hmapi : ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map e.toMonoidHom).index := by
    have h' : (Subgroup.map e.toMonoidHom ((T ⊓ K).subgroupOf K)).index =
        ((T ⊓ K).subgroupOf K).index := Subgroup.index_map_equiv _ e
    rw [h']; exact hR1i
  have h1 : TwoMaxOver S (((T ⊓ K).subgroupOf K).map e.toMonoidHom) :=
    TwoMaxOver.of_sylow hR0 hR0i hmap hmapi hmodel
  have h2 := h1.map e.symm
  have : (((T ⊓ K).subgroupOf K).map e.toMonoidHom).map e.symm.toMonoidHom =
      (T ⊓ K).subgroupOf K := by
    rw [Subgroup.map_map]
    ext x
    simp
  rw [this] at h2
  exact exists_two_coatoms_of_twoMaxOver T K hKT h2

theorem twoExtension_of_model_of_equiv {S₁ S₂ : Type} [Group S₁] [Finite S₁] [Group S₂]
    (f : S₁ ≃* S₂) {R₁ : Subgroup S₁} (hR1 : IsPGroup 2 R₁) (hR1i : ¬ 2 ∣ R₁.index)
    (hmodel : TwoMaxOver S₁ R₁) (X : Type) [Group X] [Finite X] (T K : Subgroup X) [K.Normal]
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hKT : K ⊔ T = ⊤) (e : ↥K ≃* S₂) :
    ∃ U₁ U₂ : Subgroup X, U₁ ≠ U₂ ∧ IsCoatom U₁ ∧ IsCoatom U₂ ∧ T ≤ U₁ ∧ T ≤ U₂ := by
  have : Finite S₂ := Finite.of_equiv S₁ f.toEquiv
  have hi : (R₁.map f.toMonoidHom).index = R₁.index := Subgroup.index_map_equiv R₁ f
  refine twoExtension_of_model (R₀ := R₁.map f.toMonoidHom) (hR1.map f.toMonoidHom)
    (by rw [hi]; exact hR1i) (hmodel.map f) X T K hT hTi hKT e

end Extension


end CFSG.QuasithinUnique.Setup.X1
