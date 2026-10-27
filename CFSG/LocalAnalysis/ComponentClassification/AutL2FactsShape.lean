module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG Subgroup

variable {G G' : Type*} [Group G] [Group G']

structure SylowShape (I : Subgroup G) (FA FAany : G → Prop) (T : Subgroup G) (v : G) :
    Prop where
  dihedral : ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥(T ⊓ I) ≃* DihedralGroup (2 ^ m))
  mem : v ∈ T
  not_mem_inn : v ∉ T ⊓ I
  field : FAany v
  field₀ : FA (v ^ (orderOf v / 2))
  disj : zpowers v ⊓ (T ⊓ I) = ⊥
  relIndex_le : ((T ⊓ I) ⊔ zpowers v).relIndex T ≤ 2
  derived : ⁅(T ⊓ I) ⊔ zpowers v, (T ⊓ I) ⊔ zpowers v⁆ = ⁅T ⊓ I, T ⊓ I⁆
  comm_v₀ : ∀ ρ ∈ T ⊓ I, ρ * v ^ (orderOf v / 2) = v ^ (orderOf v / 2) * ρ
  centralizer_v₀ : T ⊓ centralizer {v ^ (orderOf v / 2)} = (T ⊓ I) ⊔ zpowers v
  centralizer_R : T ⊓ centralizer ((T ⊓ I : Subgroup G) : Set G) =
    ((T ⊓ I) ⊓ centralizer ((T ⊓ I : Subgroup G) : Set G)) ⊔ zpowers (v ^ (orderOf v / 2))
  fieldInv : ∀ k ∈ T, FA k → ∃ ρ ∈ T ⊓ I, k = ρ * v ^ (orderOf v / 2)
  center_of_ne : T ≠ (T ⊓ I) ⊔ zpowers v →
    T ⊓ centralizer (T : Set G) = (T ⊓ I) ⊓ centralizer ((T ⊓ I : Subgroup G) : Set G)
  derived_of_ne : T ≠ (T ⊓ I) ⊔ zpowers v → ∀ α ∈ T, α ∉ (T ⊓ I) ⊔ zpowers v →
    (⁅T, T⁆ : Subgroup G) = ⁅T ⊓ I, zpowers α⁆
  derived_cyclic_of_ne : T ≠ (T ⊓ I) ⊔ zpowers v →
    IsCyclic (⁅T, T⁆ : Subgroup G) ∧ (⁅T, T⁆ : Subgroup G) ≤ T ⊓ I ∧
      (⁅T, T⁆ : Subgroup G).relIndex (T ⊓ I) = 2
  swap_of_ne : T ≠ (T ⊓ I) ⊔ zpowers v → ∀ α ∈ T, α ∉ (T ⊓ I) ⊔ zpowers v →
    ∀ y ∈ T ⊓ I, y ^ 2 = 1 → y ∉ centralizer ((T ⊓ I : Subgroup G) : Set G) →
      ∀ ρ ∈ T ⊓ I, α⁻¹ * y * α ≠ ρ⁻¹ * y * ρ
  small_of_ne : T ≠ (T ⊓ I) ⊔ zpowers v → ∀ α ∈ T, α ∉ (T ⊓ I) ⊔ zpowers v →
    α ^ 2 = 1 → Nat.card ↥((T ⊓ I) ⊓ centralizer {α}) ≤ 4

theorem sylowAutData_iff_shape {Y : Type} [Group Y] (T : Subgroup (MulAut Y)) (v : MulAut Y) :
    HarrisLit.SylowAutData T v ↔
      SylowShape (HarrisLit.innAut Y) HarrisLit.IsFieldAutPSL2 HarrisLit.IsFieldAutPSL2Any T v :=
  ⟨fun h => ⟨h.dihedral, h.mem, h.not_mem_inn, h.field, h.field₀, h.disj, h.relIndex_le,
      h.derived, h.comm_v₀, h.centralizer_v₀, h.centralizer_R, h.fieldInv, h.center_of_ne,
      h.derived_of_ne, h.derived_cyclic_of_ne, h.swap_of_ne, h.small_of_ne⟩,
    fun h => ⟨h.dihedral, h.mem, h.not_mem_inn, h.field, h.field₀, h.disj, h.relIndex_le,
      h.derived, h.comm_v₀, h.centralizer_v₀, h.centralizer_R, h.fieldInv, h.center_of_ne,
      h.derived_of_ne, h.derived_cyclic_of_ne, h.swap_of_ne, h.small_of_ne⟩⟩

section Map

variable (Φ : G ≃* G')

theorem map_inf_mulEquiv (A B : Subgroup G) :
    (A ⊓ B).map Φ.toMonoidHom = A.map Φ.toMonoidHom ⊓ B.map Φ.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_inf]

theorem map_centralizer_set (S : Set G) :
    (centralizer S).map Φ.toMonoidHom = centralizer (Φ '' S) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨s, hs, rfl⟩
    have := h s hs
    apply Φ.symm.injective
    simpa using this
  · intro h s hs
    have := h (Φ s) ⟨s, hs, rfl⟩
    apply Φ.injective
    simpa using this

theorem map_centralizer_subgroup (S : Subgroup G) :
    (centralizer (S : Set G)).map Φ.toMonoidHom =
      centralizer ((S.map Φ.toMonoidHom : Subgroup G') : Set G') := by
  rw [map_centralizer_set, Subgroup.coe_map]
  rfl

theorem map_centralizer_singleton (w : G) :
    (centralizer {w}).map Φ.toMonoidHom = centralizer {Φ w} := by
  rw [map_centralizer_set, Set.image_singleton]

theorem map_zpowers_mulEquiv (w : G) : (zpowers w).map Φ.toMonoidHom = zpowers (Φ w) :=
  MonoidHom.map_zpowers _ _

theorem map_symm_map_mulEquiv (A : Subgroup G) :
    (A.map Φ.toMonoidHom).map Φ.symm.toMonoidHom = A := by
  ext x
  simp

theorem map_map_symm_mulEquiv (A : Subgroup G') :
    (A.map Φ.symm.toMonoidHom).map Φ.toMonoidHom = A := by
  ext x
  simp

theorem card_map_mulEquiv (A : Subgroup G) : Nat.card (A.map Φ.toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective Φ.injective

theorem SylowShape.map {I : Subgroup G} {FA FAany : G → Prop} {I' : Subgroup G'}
    {FA' FAany' : G' → Prop} (hI : I.map Φ.toMonoidHom = I') (hFA : ∀ x, FA x ↔ FA' (Φ x))
    (hFAany : ∀ x, FAany x ↔ FAany' (Φ x)) {T : Subgroup G} {v : G}
    (h : SylowShape I FA FAany T v) :
    SylowShape I' FA' FAany' (T.map Φ.toMonoidHom) (Φ v) := by
  set f := Φ.toMonoidHom
  set R := T ⊓ I with hRdef
  set T' := T.map f
  have hR : R.map f = T' ⊓ I' := by rw [map_inf_mulEquiv, hI]
  have hord : orderOf (Φ v) = orderOf v := MulEquiv.orderOf_eq Φ v
  have hw : Φ (v ^ (orderOf v / 2)) = Φ v ^ (orderOf (Φ v) / 2) := by rw [map_pow, hord]
  have hH : (R ⊔ zpowers v).map f = (T' ⊓ I') ⊔ zpowers (Φ v) := by
    rw [Subgroup.map_sup, hR, map_zpowers_mulEquiv]
  have hCR : (centralizer (R : Set G)).map f = centralizer ((T' ⊓ I' : Subgroup G') : Set G') := by
    rw [map_centralizer_subgroup, hR]
  have hne : T' ≠ (T' ⊓ I') ⊔ zpowers (Φ v) → T ≠ R ⊔ zpowers v := by
    intro hne heq
    apply hne
    rw [← hH, ← heq]
  have hpull : ∀ α ∈ T', α ∉ (T' ⊓ I') ⊔ zpowers (Φ v) →
      Φ.symm α ∈ T ∧ Φ.symm α ∉ R ⊔ zpowers v ∧ Φ (Φ.symm α) = α := by
    intro α hα hα'
    refine ⟨(Subgroup.mem_map_equiv).mp hα, fun h' => hα' ?_, by simp⟩
    rw [← hH]
    exact (Subgroup.mem_map_equiv).mpr h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨m, hm, ⟨e⟩⟩ := h.dihedral
    exact ⟨m, hm, ⟨((MulEquiv.subgroupCongr hR).symm.trans
      (R.equivMapOfInjective f Φ.injective).symm).trans e⟩⟩
  · exact Subgroup.mem_map_of_mem f h.mem
  · rw [← hR]
    intro h'
    apply h.not_mem_inn
    have := (Subgroup.mem_map_equiv).mp h'
    rw [MulEquiv.symm_apply_apply] at this
    exact this
  · exact (hFAany v).mp h.field
  · rw [← hw]
    exact (hFA _).mp h.field₀
  · rw [← hR, ← map_zpowers_mulEquiv, ← map_inf_mulEquiv, h.disj, Subgroup.map_bot]
  · rw [← hH, Subgroup.relIndex_map_map_of_injective _ _ Φ.injective]
    exact h.relIndex_le
  · rw [← hH, ← hR, ← Subgroup.map_commutator, ← Subgroup.map_commutator, h.derived]
  · intro ρ hρ
    rw [← hR] at hρ
    obtain ⟨ρ₀, hρ₀, rfl⟩ := hρ
    rw [← hw]
    change Φ ρ₀ * Φ _ = Φ _ * Φ ρ₀
    rw [← map_mul, ← map_mul, h.comm_v₀ ρ₀ hρ₀]
  · rw [← hw, ← map_centralizer_singleton, ← map_inf_mulEquiv, h.centralizer_v₀, hH]
  · rw [← hw, ← hCR, ← hR, ← map_zpowers_mulEquiv, ← map_inf_mulEquiv, ← map_inf_mulEquiv,
      ← Subgroup.map_sup, h.centralizer_R]
  · intro k hk hFk
    have hk₀ : Φ.symm k ∈ T := (Subgroup.mem_map_equiv).mp hk
    obtain ⟨ρ₀, hρ₀, hkρ⟩ := h.fieldInv (Φ.symm k) hk₀ ((hFA _).mpr (by simpa using hFk))
    refine ⟨Φ ρ₀, by rw [← hR]; exact Subgroup.mem_map_of_mem f hρ₀, ?_⟩
    rw [← hw, ← map_mul, ← hkρ]
    simp
  · intro hne'
    rw [← hR, ← map_centralizer_subgroup, ← map_centralizer_subgroup, ← map_inf_mulEquiv,
      ← map_inf_mulEquiv, h.center_of_ne (hne hne')]
  · intro hne' α hα hα'
    obtain ⟨h1, h2, h3⟩ := hpull α hα hα'
    rw [← hR, ← h3, ← map_zpowers_mulEquiv, ← Subgroup.map_commutator,
      ← Subgroup.map_commutator, h.derived_of_ne (hne hne') _ h1 h2]
  · intro hne'
    obtain ⟨hc1, hc2, hc3⟩ := h.derived_cyclic_of_ne (hne hne')
    rw [← Subgroup.map_commutator, ← hR]
    refine ⟨?_, Subgroup.map_mono hc2, ?_⟩
    · have := hc1
      exact isCyclic_of_surjective (⁅T, T⁆.equivMapOfInjective f Φ.injective)
        (MulEquiv.surjective _)
    · rw [Subgroup.relIndex_map_map_of_injective _ _ Φ.injective]
      exact hc3
  · intro hne' α hα hα' y hy hy2 hyC ρ hρ
    obtain ⟨h1, h2, h3⟩ := hpull α hα hα'
    rw [← hR] at hy hρ
    have hy₀ : Φ.symm y ∈ R := (Subgroup.mem_map_equiv).mp hy
    have hρ₀ : Φ.symm ρ ∈ R := (Subgroup.mem_map_equiv).mp hρ
    have hy₀2 : Φ.symm y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    have hy₀C : Φ.symm y ∉ centralizer (R : Set G) := by
      intro hC
      apply hyC
      rw [← hCR]
      exact (Subgroup.mem_map_equiv).mpr hC
    have := h.swap_of_ne (hne hne') _ h1 h2 _ hy₀ hy₀2 hy₀C _ hρ₀
    intro heq
    apply this
    apply Φ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact heq
  · intro hne' α hα hα' hα2
    obtain ⟨h1, h2, h3⟩ := hpull α hα hα'
    have hα₀2 : (Φ.symm α) ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
    have := h.small_of_ne (hne hne') _ h1 h2 hα₀2
    rw [← hR, ← h3, ← map_centralizer_singleton, ← map_inf_mulEquiv, card_map_mulEquiv]
    exact this

end Map

@[expose] def IsSylowIn (T K : Subgroup G) : Prop :=
  T ≤ K ∧ IsPGroup 2 T ∧ ∀ Q : Subgroup G, Q ≤ K → IsPGroup 2 Q → T ≤ Q → Q = T

theorem isSylowIn_iff (T K : Subgroup G) :
    IsSylowIn T K ↔ T ≤ K ∧ ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K) = T.subgroupOf K := by
  constructor
  · rintro ⟨hTK, hT2, hmax⟩
    refine ⟨hTK, ⟨T.subgroupOf K, hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm, ?_⟩, rfl⟩
    intro Q hQ hTQ
    have hQK : Q.map K.subtype ≤ K := Subgroup.map_subtype_le Q
    have hQ2 : IsPGroup 2 (Q.map K.subtype) :=
      hQ.of_equiv (Q.equivMapOfInjective K.subtype K.subtype_injective)
    have hTQ' : T ≤ Q.map K.subtype := by
      intro t ht
      exact ⟨⟨t, hTK ht⟩, hTQ (show (⟨t, hTK ht⟩ : K) ∈ T.subgroupOf K from ht), rfl⟩
    have := hmax _ hQK hQ2 hTQ'
    rw [← this]
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_subgroupOf.mp hx
      rwa [Subtype.ext hyx] at hy
  · rintro ⟨hTK, P, hP⟩
    have hT2 : IsPGroup 2 T := by
      have := P.isPGroup'
      rw [hP] at this
      exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hTK)
    refine ⟨hTK, hT2, fun Q hQK hQ hTQ => ?_⟩
    have hQ2 : IsPGroup 2 (Q.subgroupOf K) :=
      hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQK).symm
    have hle : (P : Subgroup ↥K) ≤ Q.subgroupOf K := by
      rw [hP]
      exact fun x hx => hTQ hx
    have h1 := P.is_maximal' hQ2 hle
    rw [hP, Subgroup.subgroupOf_inj, inf_of_le_left hQK, inf_of_le_left hTK] at h1
    exact h1

theorem IsSylowIn.map (Φ : G ≃* G') {T K : Subgroup G} (h : IsSylowIn T K) :
    IsSylowIn (T.map Φ.toMonoidHom) (K.map Φ.toMonoidHom) := by
  obtain ⟨hTK, hT2, hmax⟩ := h
  refine ⟨Subgroup.map_mono hTK, hT2.map _, fun Q hQK hQ hTQ => ?_⟩
  have h1 : Q.map Φ.symm.toMonoidHom ≤ K := by
    rw [← map_symm_map_mulEquiv Φ K]
    exact Subgroup.map_mono hQK
  have h3 : T ≤ Q.map Φ.symm.toMonoidHom := by
    rw [← map_symm_map_mulEquiv Φ T]
    exact Subgroup.map_mono hTQ
  have := hmax _ h1 (hQ.map _) h3
  rw [← this, map_map_symm_mulEquiv]

theorem mem_smul_sylow_iff_conj {H : Type*} [Group H] {p : ℕ} (P : Sylow p H) (g d : H) :
    d ∈ ((g • P : Sylow p H) : Subgroup H) ↔ g⁻¹ * d * g ∈ (P : Subgroup H) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.smul_def, MulAut.conj_apply, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  · intro h
    exact ⟨_, h, by rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

theorem IsSylowIn.exists_conj [Finite G] {T₁ T₂ K : Subgroup G} (h₁ : IsSylowIn T₁ K)
    (h₂ : IsSylowIn T₂ K) : ∃ g ∈ K, T₂ = T₁.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, P₁, hP₁⟩ := (isSylowIn_iff T₁ K).mp h₁
  obtain ⟨-, P₂, hP₂⟩ := (isSylowIn_iff T₂ K).mp h₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥K) P₁ P₂
  refine ⟨g, g.2, ?_⟩
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro hx
    have hxK : x ∈ K := h₂.1 hx
    have h1 : (⟨x, hxK⟩ : K) ∈ ((g • P₁ : Sylow 2 K) : Subgroup K) := by
      rw [hg, hP₂]
      exact hx
    rw [mem_smul_sylow_iff_conj, hP₁] at h1
    exact h1
  · intro hx
    have hxK : x ∈ K := by
      have := K.mul_mem (K.mul_mem g.2 (h₁.1 hx)) (K.inv_mem g.2)
      rwa [show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x by group] at this
    have h1 : g⁻¹ * (⟨x, hxK⟩ : K) * g ∈ (P₁ : Subgroup K) := by
      rw [hP₁]
      exact hx
    rw [← mem_smul_sylow_iff_conj, hg, hP₂] at h1
    exact h1

end CFSG.ComponentClassification.AutL2Facts
