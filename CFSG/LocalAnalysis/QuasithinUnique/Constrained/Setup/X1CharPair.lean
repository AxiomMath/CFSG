module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TwoExt

public section

open scoped Pointwise

namespace CFSG.QuasithinUnique.Setup.X1

section Char

variable {G G' : Type*} [Group G] [Group G']

theorem characteristic_map_equiv {H : Subgroup G} (hH : H.Characteristic) (ψ : G ≃* G') :
    (H.map ψ.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hσ := Subgroup.characteristic_iff_map_eq.1 hH ((ψ.trans φ).trans ψ.symm)
  rw [Subgroup.map_map]
  have : ((φ.toMonoidHom).comp ψ.toMonoidHom) =
      (ψ.toMonoidHom).comp (((ψ.trans φ).trans ψ.symm).toMonoidHom) := by
    ext x
    simp
  rw [this, ← Subgroup.map_map, hσ]

end Char

@[expose] def CharPair (S : Type*) [Group S] (R₀ : Subgroup S) : Prop :=
  ∃ (Q₁ Q₂ : Subgroup ↥R₀) (g h : S), Q₁.Characteristic ∧ Q₂.Characteristic ∧
    g ∈ Subgroup.normalizer ((Q₁.map R₀.subtype : Subgroup S) : Set S) ∧
    h ∈ Subgroup.normalizer ((Q₂.map R₀.subtype : Subgroup S) : Set S) ∧
    g ∉ Subgroup.normalizer ((Q₂.map R₀.subtype : Subgroup S) : Set S) ∧
    h ∉ Subgroup.normalizer ((Q₁.map R₀.subtype : Subgroup S) : Set S) ∧
    Subgroup.closure ({g, h} : Set S) = ⊤

section Transport

variable {S S' : Type*} [Group S] [Group S']

theorem mem_map_equiv' (e : S ≃* S') (H : Subgroup S) (x : S) :
    e x ∈ H.map e.toMonoidHom ↔ x ∈ H := by
  rw [Subgroup.mem_map_equiv]; simp

theorem mem_normalizer_map_equiv (e : S ≃* S') (H : Subgroup S) (x : S) :
    e x ∈ Subgroup.normalizer ((H.map e.toMonoidHom : Subgroup S') : Set S') ↔
      x ∈ Subgroup.normalizer (H : Set S) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (e y)
    rw [mem_map_equiv', show e x * e y * (e x)⁻¹ = e (x * y * x⁻¹) by simp, mem_map_equiv']
      at this
    exact this
  · intro h y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [mem_map_equiv', show e x * e y' * (e x)⁻¹ = e (x * y' * x⁻¹) by simp, mem_map_equiv']
    exact h y'

theorem CharPair.map {R₀ : Subgroup S} (h : CharPair S R₀) (e : S ≃* S') :
    CharPair S' (R₀.map e.toMonoidHom) := by
  obtain ⟨Q₁, Q₂, g, k, c₁, c₂, hg1, hk2, hg2, hk1, hgen⟩ := h
  let ψ : ↥R₀ ≃* ↥(R₀.map e.toMonoidHom) := e.subgroupMap R₀
  have hmap : ∀ Q : Subgroup ↥R₀,
      (Q.map ψ.toMonoidHom).map (R₀.map e.toMonoidHom).subtype = (Q.map R₀.subtype).map e.toMonoidHom := by
    intro Q
    ext y
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, ⟨q, hq, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨ψ q, ⟨q, hq, rfl⟩, rfl⟩
  refine ⟨Q₁.map ψ.toMonoidHom, Q₂.map ψ.toMonoidHom, e g, e k, characteristic_map_equiv c₁ ψ,
    characteristic_map_equiv c₂ ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmap]; exact (mem_normalizer_map_equiv e _ g).2 hg1
  · rw [hmap]; exact (mem_normalizer_map_equiv e _ k).2 hk2
  · rw [hmap]; exact fun h' => hg2 ((mem_normalizer_map_equiv e _ g).1 h')
  · rw [hmap]; exact fun h' => hk1 ((mem_normalizer_map_equiv e _ k).1 h')
  · have : ({e g, e k} : Set S') = e.toMonoidHom '' ({g, k} : Set S) := by
      ext y; simp
    rw [this, ← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective _ e.surjective]

end Transport

section Extension

variable {X : Type*} [Group X] (T K : Subgroup X) [K.Normal]

@[expose] def conjR (t : X) (ht : t ∈ T) :
    ↥((T ⊓ K).subgroupOf K) ≃* ↥((T ⊓ K).subgroupOf K) where
  toFun r := ⟨(MulAut.conjNormal t : MulAut K) r.1, by
    have hr := r.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hr ⊢
    refine ⟨?_, ((MulAut.conjNormal t : MulAut K) r.1).2⟩
    rw [MulAut.conjNormal_apply]
    exact T.mul_mem (T.mul_mem ht hr.1) (T.inv_mem ht)⟩
  invFun r := ⟨(MulAut.conjNormal t⁻¹ : MulAut K) r.1, by
    have hr := r.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hr ⊢
    refine ⟨?_, ((MulAut.conjNormal t⁻¹ : MulAut K) r.1).2⟩
    rw [MulAut.conjNormal_apply]
    exact T.mul_mem (T.mul_mem (T.inv_mem ht) hr.1) (by simpa using ht)⟩
  left_inv r := by
    apply Subtype.ext
    show (MulAut.conjNormal t⁻¹ : MulAut K) ((MulAut.conjNormal t : MulAut K) r.1) = r.1
    rw [← MulAut.mul_apply, ← map_mul]
    simp
  right_inv r := by
    apply Subtype.ext
    show (MulAut.conjNormal t : MulAut K) ((MulAut.conjNormal t⁻¹ : MulAut K) r.1) = r.1
    rw [← MulAut.mul_apply, ← map_mul]
    simp
  map_mul' r s := by
    apply Subtype.ext
    exact map_mul (MulAut.conjNormal t : MulAut K) r.1 s.1

theorem mem_map_conj_iff {Q : Subgroup ↥((T ⊓ K).subgroupOf K)} (hQ : Q.Characteristic)
    {t : X} (ht : t ∈ T) (z : K) :
    z ∈ Q.map ((T ⊓ K).subgroupOf K).subtype ↔
      (MulAut.conjNormal t : MulAut K) z ∈ Q.map ((T ⊓ K).subgroupOf K).subtype := by
  have key : ∀ {t : X}, t ∈ T → ∀ z : K, z ∈ Q.map ((T ⊓ K).subgroupOf K).subtype →
      (MulAut.conjNormal t : MulAut K) z ∈ Q.map ((T ⊓ K).subgroupOf K).subtype := by
    intro t ht z hz
    obtain ⟨q, hq, rfl⟩ := hz
    have hmap := Subgroup.characteristic_iff_map_eq.1 hQ (conjR T K t ht)
    have : conjR T K t ht q ∈ Q := by
      rw [← hmap]; exact ⟨q, hq, rfl⟩
    exact ⟨_, this, rfl⟩
  refine ⟨key ht z, fun h => ?_⟩
  have := key (T.inv_mem ht) _ h
  have e : (MulAut.conjNormal t⁻¹ : MulAut K) ((MulAut.conjNormal t : MulAut K) z) = z := by
    rw [← MulAut.mul_apply, ← map_mul]
    simp
  rwa [e] at this

end Extension

section TwoCoatoms

variable {X : Type*} [Group X] (T K : Subgroup X) [K.Normal]

omit [K.Normal] in
theorem sup_inf_of_stable (U : Subgroup K) (hRU : (T ⊓ K).subgroupOf K ≤ U)
    (hfwd : ∀ {t : X}, t ∈ T → ∀ x ∈ U.map K.subtype, t * x * t⁻¹ ∈ U.map K.subtype) :
    (U.map K.subtype ⊔ T) ⊓ K = U.map K.subtype := by
  set U' : Subgroup X := U.map K.subtype with hU'
  have hU'K : U' ≤ K := Subgroup.map_subtype_le U
  have hnorm : T ≤ Subgroup.normalizer (U' : Set X) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hfwd ht x hx, fun hx => ?_⟩
    have := hfwd (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hmul : (↑(U' ⊔ T) : Set X) = (U' : Set X) * T :=
    Subgroup.coe_mul_of_right_le_normalizer_left U' T hnorm
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

omit [K.Normal] in
theorem sup_ne_top_of_stable (U : Subgroup K) (hRU : (T ⊓ K).subgroupOf K ≤ U)
    (hfwd : ∀ {t : X}, t ∈ T → ∀ x ∈ U.map K.subtype, t * x * t⁻¹ ∈ U.map K.subtype)
    (hU : U ≠ ⊤) : U.map K.subtype ⊔ T ≠ ⊤ := by
  intro htop
  apply hU
  have hVK := sup_inf_of_stable T K U hRU hfwd
  rw [eq_top_iff]
  intro k _
  have hkK : (k : X) ∈ (U.map K.subtype ⊔ T) ⊓ K := ⟨htop ▸ Subgroup.mem_top _, k.2⟩
  rw [hVK] at hkK
  obtain ⟨u, hu, hue⟩ := hkK
  have : u = k := Subtype.ext hue
  exact this ▸ hu

theorem normalizer_props {Q : Subgroup ↥((T ⊓ K).subgroupOf K)} (hQ : Q.Characteristic) :
    (T ⊓ K).subgroupOf K ≤
      Subgroup.normalizer ((Q.map ((T ⊓ K).subgroupOf K).subtype : Subgroup K) : Set K) ∧
    ∀ {t : X}, t ∈ T → ∀ y ∈
      Subgroup.normalizer ((Q.map ((T ⊓ K).subgroupOf K).subtype : Subgroup K) : Set K),
      (MulAut.conjNormal t : MulAut K) y ∈
        Subgroup.normalizer ((Q.map ((T ⊓ K).subgroupOf K).subtype : Subgroup K) : Set K) := by
  have : Q.Normal := inferInstance
  refine ⟨fun r hr => ?_, fun {t} ht y hy => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    have key : ∀ (r : K) (hr : r ∈ (T ⊓ K).subgroupOf K) (z : K),
        z ∈ Q.map ((T ⊓ K).subgroupOf K).subtype →
        r * z * r⁻¹ ∈ Q.map ((T ⊓ K).subgroupOf K).subtype := by
      intro r hr z hz
      obtain ⟨q, hq, rfl⟩ := hz
      have := Q.normal_of_characteristic.conj_mem q hq ⟨r, hr⟩
      exact ⟨_, this, rfl⟩
    refine ⟨key r hr z, fun h => ?_⟩
    have hr' : r⁻¹ ∈ (T ⊓ K).subgroupOf K := Subgroup.inv_mem _ hr
    have := key r⁻¹ hr' _ h
    simpa [mul_assoc] using this
  · rw [Subgroup.mem_normalizer_iff] at hy ⊢
    intro z
    have e : (MulAut.conjNormal t : MulAut K) y * z * ((MulAut.conjNormal t : MulAut K) y)⁻¹ =
        (MulAut.conjNormal t : MulAut K)
          (y * (MulAut.conjNormal t⁻¹ : MulAut K) z * y⁻¹) := by
      have : z = (MulAut.conjNormal t : MulAut K) ((MulAut.conjNormal t⁻¹ : MulAut K) z) := by
        rw [← MulAut.mul_apply, ← map_mul]
        simp
      conv_lhs => rw [this]
      simp [map_mul, map_inv]
    rw [e, ← mem_map_conj_iff T K hQ ht]
    exact (mem_map_conj_iff T K hQ (T.inv_mem ht) z).trans (hy _)

theorem exists_two_coatoms_of_charPair [Finite X] (hKT : K ⊔ T = ⊤)
    (h : CharPair ↥K ((T ⊓ K).subgroupOf K)) :
    ∃ V₁ V₂ : Subgroup X, V₁ ≠ V₂ ∧ IsCoatom V₁ ∧ IsCoatom V₂ ∧ T ≤ V₁ ∧ T ≤ V₂ := by
  obtain ⟨Q₁, Q₂, g, k, c₁, c₂, hg1, hk2, hg2, hk1, hgen⟩ := h
  set N₁ : Subgroup K := Subgroup.normalizer
    ((Q₁.map ((T ⊓ K).subgroupOf K).subtype : Subgroup K) : Set K) with hN₁
  set N₂ : Subgroup K := Subgroup.normalizer
    ((Q₂.map ((T ⊓ K).subgroupOf K).subtype : Subgroup K) : Set K) with hN₂
  obtain ⟨hR1, hS1⟩ := normalizer_props T K c₁
  obtain ⟨hR2, hS2⟩ := normalizer_props T K c₂
  have hN1top : N₁ ≠ ⊤ := fun h => hk1 (h ▸ Subgroup.mem_top k)
  have hN2top : N₂ ≠ ⊤ := fun h => hg2 (h ▸ Subgroup.mem_top g)
  have hgenN : N₁ ⊔ N₂ = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mem_sup_left hg1
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Subgroup.mem_sup_right hk2
  have hfwd : ∀ (N : Subgroup K),
      (∀ {t : X}, t ∈ T → ∀ y ∈ N, (MulAut.conjNormal t : MulAut K) y ∈ N) →
      ∀ {t : X}, t ∈ T → ∀ x ∈ N.map K.subtype, t * x * t⁻¹ ∈ N.map K.subtype := by
    intro N hN t ht x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨_, hN ht y hy, by simp [MulAut.conjNormal_apply]⟩
  have hV1 : N₁.map K.subtype ⊔ T ≠ ⊤ :=
    sup_ne_top_of_stable T K N₁ hR1 (hfwd N₁ hS1) hN1top
  have hV2 : N₂.map K.subtype ⊔ T ≠ ⊤ :=
    sup_ne_top_of_stable T K N₂ hR2 (hfwd N₂ hS2) hN2top
  obtain ⟨M₁, hM1c, hM1⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (N₁.map K.subtype ⊔ T)).resolve_left hV1
  obtain ⟨M₂, hM2c, hM2⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (N₂.map K.subtype ⊔ T)).resolve_left hV2
  refine ⟨M₁, M₂, fun hM => ?_, hM1c, hM2c, le_trans le_sup_right hM1,
    le_trans le_sup_right hM2⟩
  subst hM
  have hKle : K ≤ N₁.map K.subtype ⊔ N₂.map K.subtype := by
    rw [← Subgroup.map_sup, hgenN, Subgroup.map_top, Subgroup.range_subtype]
  have hKM : K ≤ M₁ :=
    le_trans hKle (sup_le (le_trans le_sup_left hM1) (le_trans le_sup_left hM2))
  have hTM : T ≤ M₁ := le_trans le_sup_right hM1
  apply hM1c.1
  rw [eq_top_iff, ← hKT]
  exact sup_le hKM hTM

end TwoCoatoms

section SylowTransport

theorem CharPair.of_sylow {S : Type*} [Group S] [Finite S] {R R' : Subgroup S}
    (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.index) (hR' : IsPGroup 2 R') (hR'i : ¬ 2 ∣ R'.index)
    (h : CharPair S R) : CharPair S R' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 S := hR.toSylow hRi
  let P' : Sylow 2 S := hR'.toSylow hR'i
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P P'
  have hconj : (R.map (MulAut.conj g).toMonoidHom) = R' := by
    have := congrArg (fun T : Sylow 2 S => (T : Subgroup S)) hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at this
    exact this
  rw [← hconj]
  exact h.map (MulAut.conj g)

theorem twoExtension_of_charPair {S : Type} [Group S] [Finite S] {R₀ : Subgroup S}
    (hR0 : IsPGroup 2 R₀) (hR0i : ¬ 2 ∣ R₀.index) (hmodel : CharPair S R₀)
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
  have h1 : CharPair S (((T ⊓ K).subgroupOf K).map e.toMonoidHom) :=
    CharPair.of_sylow hR0 hR0i hmap hmapi hmodel
  have h2 := h1.map e.symm
  have : (((T ⊓ K).subgroupOf K).map e.toMonoidHom).map e.symm.toMonoidHom =
      (T ⊓ K).subgroupOf K := by
    rw [Subgroup.map_map]
    ext x
    simp
  rw [this] at h2
  exact exists_two_coatoms_of_charPair T K hKT h2

theorem twoExtension_of_charPair_of_equiv {S₁ S₂ : Type} [Group S₁] [Finite S₁] [Group S₂]
    (f : S₁ ≃* S₂) {R₁ : Subgroup S₁} (hR1 : IsPGroup 2 R₁) (hR1i : ¬ 2 ∣ R₁.index)
    (hmodel : CharPair S₁ R₁) (X : Type) [Group X] [Finite X] (T K : Subgroup X) [K.Normal]
    (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hKT : K ⊔ T = ⊤) (e : ↥K ≃* S₂) :
    ∃ U₁ U₂ : Subgroup X, U₁ ≠ U₂ ∧ IsCoatom U₁ ∧ IsCoatom U₂ ∧ T ≤ U₁ ∧ T ≤ U₂ := by
  have : Finite S₂ := Finite.of_equiv S₁ f.toEquiv
  have hi : (R₁.map f.toMonoidHom).index = R₁.index := Subgroup.index_map_equiv R₁ f
  refine twoExtension_of_charPair (R₀ := R₁.map f.toMonoidHom) (hR1.map f.toMonoidHom)
    (by rw [hi]; exact hR1i) (hmodel.map f) X T K hT hTi hKT e

end SylowTransport

end CFSG.QuasithinUnique.Setup.X1
