module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A8Pure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519 Equiv Equiv.Perm
  Subgroup

section Model

variable {G : Type} [Group G]

@[expose] def modelHom (J : Subgroup G) (φ : ↥J ≃* alternatingGroup (Fin 8)) (π : Perm (Fin 8)) :
    ↥J →* Perm (Fin 8) :=
  (MulAut.conj π).toMonoidHom.comp ((alternatingGroup (Fin 8)).subtype.comp φ.toMonoidHom)

theorem modelHom_apply (J : Subgroup G) (φ : ↥J ≃* alternatingGroup (Fin 8)) (π : Perm (Fin 8))
    (y : ↥J) : modelHom J φ π y = π * ((φ y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * π⁻¹ :=
  rfl

theorem modelHom_injective (J : Subgroup G) (φ : ↥J ≃* alternatingGroup (Fin 8))
    (π : Perm (Fin 8)) : Function.Injective (modelHom J φ π) := by
  intro y y' h
  rw [modelHom_apply, modelHom_apply] at h
  have h1 : ((φ y : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      ((φ y' : alternatingGroup (Fin 8)) : Perm (Fin 8)) :=
    mul_left_cancel (mul_right_cancel h)
  exact φ.injective (Subtype.ext h1)

theorem modelHom_sign (J : Subgroup G) (φ : ↥J ≃* alternatingGroup (Fin 8)) (π : Perm (Fin 8))
    (y : ↥J) : modelHom J φ π y ∈ alternatingGroup (Fin 8) := by
  rw [modelHom_apply]
  have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
  exact hn.conj_mem _ (φ y).2 π

theorem modelHom_surj (J : Subgroup G) (φ : ↥J ≃* alternatingGroup (Fin 8)) (π : Perm (Fin 8))
    {p : Perm (Fin 8)} (hp : p ∈ alternatingGroup (Fin 8)) : ∃ y : ↥J, modelHom J φ π y = p := by
  have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
  have hmem : π⁻¹ * p * π ∈ alternatingGroup (Fin 8) := by
    have := hn.conj_mem p hp π⁻¹
    simpa using this
  refine ⟨φ.symm ⟨π⁻¹ * p * π, hmem⟩, ?_⟩
  rw [modelHom_apply]
  simp only [MulEquiv.apply_symm_apply]
  show π * (π⁻¹ * p * π) * π⁻¹ = p
  group

variable (J : Subgroup G) (ψ : ↥J →* Perm (Fin 8))

@[expose] def modelImg (X : Subgroup G) : Subgroup (Perm (Fin 8)) := (X.subgroupOf J).map ψ

@[expose] def modelPull (P : Subgroup (Perm (Fin 8))) : Subgroup G := (P.comap ψ).map J.subtype

variable {J ψ}

theorem mem_modelImg {X : Subgroup G} {p : Perm (Fin 8)} :
    p ∈ modelImg J ψ X ↔ ∃ y : ↥J, (y : G) ∈ X ∧ ψ y = p := by
  simp [modelImg, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mem_modelPull {P : Subgroup (Perm (Fin 8))} {x : G} :
    x ∈ modelPull J ψ P ↔ ∃ hx : x ∈ J, ψ ⟨x, hx⟩ ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem modelImg_mono {X Y : Subgroup G} (h : X ≤ Y) : modelImg J ψ X ≤ modelImg J ψ Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem card_modelImg (hψ : Function.Injective ψ) {X : Subgroup G} (hX : X ≤ J) :
    Nat.card (modelImg J ψ X) = Nat.card X := by
  rw [modelImg, Subgroup.card_map_of_injective hψ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem modelImg_injective (hψ : Function.Injective ψ) {X Y : Subgroup G} (hX : X ≤ J)
    (hY : Y ≤ J) (h : modelImg J ψ X = modelImg J ψ Y) : X = Y := by
  have h1 : X.subgroupOf J = Y.subgroupOf J := Subgroup.map_injective hψ h
  calc X = (X.subgroupOf J).map J.subtype := (Subgroup.map_subgroupOf_eq_of_le hX).symm
    _ = (Y.subgroupOf J).map J.subtype := by rw [h1]
    _ = Y := Subgroup.map_subgroupOf_eq_of_le hY

theorem isA4Block_modelImg (hψ : Function.Injective ψ) {L U : Subgroup G} (h : IsA4Block L U)
    (hL : L ≤ J) : IsA4Block (modelImg J ψ L) (modelImg J ψ U) := by
  have hU : U ≤ J := h.le.trans hL
  have h1 : IsA4Block (L.subgroupOf J) (U.subgroupOf J) := by
    apply IsA4Block.of_map_injective J.subtype J.subtype_injective
    rwa [Subgroup.map_subgroupOf_eq_of_le hL, Subgroup.map_subgroupOf_eq_of_le hU]
  exact h1.map_of_injective ψ hψ

theorem isA4Block_modelPull (hψ : Function.Injective ψ) {P Q : Subgroup (Perm (Fin 8))}
    (h : IsA4Block P Q) (hP : P ≤ ψ.range) : IsA4Block (modelPull J ψ P) (modelPull J ψ Q) := by
  have hQ : Q ≤ ψ.range := h.le.trans hP
  have h1 : IsA4Block (P.comap ψ) (Q.comap ψ) := by
    apply IsA4Block.of_map_injective ψ hψ
    rwa [Subgroup.map_comap_eq_self hP, Subgroup.map_comap_eq_self hQ]
  exact h1.map_of_injective J.subtype J.subtype_injective

end Model

theorem tabA8_of_model {G : Type} [Group G] {J K : Subgroup G} {t : G}
    {L₁ L₂ U₁ U₂ D : Subgroup G} (ψ : ↥J →* Perm (Fin 8)) (hψinj : Function.Injective ψ)
    (hψalt : ∀ y, ψ y ∈ alternatingGroup (Fin 8))
    (hψsurj : ∀ p ∈ alternatingGroup (Fin 8), ∃ y : ↥J, ψ y = p)
    (htn : t ∈ Subgroup.normalizer (J : Set G))
    (hrelψ : ∀ y y' : ↥J, (y' : G) = t * y * t⁻¹ →
      ψ y' = swap (0 : Fin 8) 1 * ψ y * (swap (0 : Fin 8) 1)⁻¹)
    (hKcomp : IsComponentIn K (J ⊓ Subgroup.centralizer ({t} : Set G)))
    (e₀ : ↥K ≃* alternatingGroup (Fin 6)) (hA₁ : IsA4Block L₁ U₁) (hA₂ : IsA4Block L₂ U₂)
    (h₁ : L₁ ≤ K) (h₂ : L₂ ≤ K) (hne : U₁ ≠ U₂) (hDK : D ≤ K) (hD8 : Nat.card D = 8)
    (hU₁ : U₁ ≤ D) (hU₂ : U₂ ≤ D) :
    ∃ Λ Λr W : Subgroup G, (Λ = L₁ ∨ Λ = L₂) ∧ Λr ≤ J ∧ IsA4Block Λr W ∧
      (∀ l ∈ Λ, ∀ y ∈ Λr, l * y = y * l) ∧ t ∈ Subgroup.normalizer (Λr : Set G) ∧ t ∉ Λr := by
  have hKJ : K ≤ J := hKcomp.1.trans inf_le_left
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) := hKcomp.1.trans inf_le_right
  have hKC : modelImg J ψ K ≤ Subgroup.centralizer {swap (0 : Fin 8) 1} := by
    intro p hp
    obtain ⟨y, hyK, rfl⟩ := mem_modelImg.mp hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    have htk : t * (y : G) * t⁻¹ = (y : G) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hKt hyK)
      rw [← this]
      group
    have h1 := hrelψ y y htk.symm
    calc ψ y * swap (0 : Fin 8) 1
        = (swap (0 : Fin 8) 1 * ψ y * (swap (0 : Fin 8) 1)⁻¹) * swap (0 : Fin 8) 1 := by
          rw [← h1]
      _ = swap (0 : Fin 8) 1 * ψ y := by group
  have hKalt : modelImg J ψ K ≤ alternatingGroup (Fin 8) := by
    intro p hp
    obtain ⟨y, -, rfl⟩ := mem_modelImg.mp hp
    exact hψalt y
  have hKcard : Nat.card (modelImg J ψ K) = 360 := by
    rw [card_modelImg hψinj hKJ, Nat.card_congr e₀.toEquiv]
    exact card_alt6'
  have hKperf0 : ⁅K, K⁆ = K :=
    Subgroup.isPerfect_iff.mp (BenderBranch.isQuasisimple_of_isComponentIn hKcomp).1
  have hKperf : ⁅modelImg J ψ K, modelImg J ψ K⁆ = modelImg J ψ K := by
    rw [modelImg, ← Subgroup.map_commutator]
    congr 1
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKJ, hKperf0]
  have hL₁J : L₁ ≤ J := h₁.trans hKJ
  have hL₂J : L₂ ≤ J := h₂.trans hKJ
  have hU₁J : U₁ ≤ J := hA₁.le.trans hL₁J
  have hU₂J : U₂ ≤ J := hA₂.le.trans hL₂J
  obtain ⟨Λ', Λr', W', hΛ', hΛalt, hΛA4, hcomm', hnorm', hnot'⟩ :=
    tabA8_pure hKC hKalt hKcard hKperf (isA4Block_modelImg hψinj hA₁ hL₁J)
      (isA4Block_modelImg hψinj hA₂ hL₂J) (modelImg_mono h₁) (modelImg_mono h₂)
      (fun h => hne (modelImg_injective hψinj hU₁J hU₂J h)) (modelImg_mono hDK)
      ((card_modelImg hψinj (hDK.trans hKJ)).trans hD8) (modelImg_mono hU₁) (modelImg_mono hU₂)
  obtain ⟨L, hLcase, hcomm⟩ : ∃ L : Subgroup G, (L = L₁ ∨ L = L₂) ∧
      ∀ l ∈ modelImg J ψ L, ∀ y ∈ Λr', l * y = y * l := by
    rcases hΛ' with h | h
    · refine ⟨L₁, Or.inl rfl, ?_⟩
      subst h
      exact hcomm'
    · refine ⟨L₂, Or.inr rfl, ?_⟩
      subst h
      exact hcomm'
  have hLJ : L ≤ J := by
    rcases hLcase with rfl | rfl
    · exact hL₁J
    · exact hL₂J
  have hrange : Λr' ≤ ψ.range := fun p hp => by
    obtain ⟨y, hy⟩ := hψsurj p (hΛalt hp)
    exact ⟨y, hy⟩
  refine ⟨L, modelPull J ψ Λr', modelPull J ψ W', hLcase, ?_, isA4Block_modelPull hψinj hΛA4 hrange,
    ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  ·
    intro l hl y hy
    obtain ⟨hyJ, hyp⟩ := mem_modelPull.mp hy
    have hlp : ψ ⟨l, hLJ hl⟩ ∈ modelImg J ψ L := mem_modelImg.mpr ⟨⟨l, hLJ hl⟩, hl, rfl⟩
    have h1 := hcomm _ hlp _ hyp
    rw [← map_mul, ← map_mul] at h1
    have h2 := hψinj h1
    exact congrArg Subtype.val h2
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have htx : x ∈ J ↔ t * x * t⁻¹ ∈ J := Subgroup.mem_normalizer_iff.mp htn x
    constructor
    · intro hx
      obtain ⟨hxJ, hxp⟩ := mem_modelPull.mp hx
      have hxJ' : t * x * t⁻¹ ∈ J := htx.mp hxJ
      refine mem_modelPull.mpr ⟨hxJ', ?_⟩
      have h1 := hrelψ ⟨x, hxJ⟩ ⟨t * x * t⁻¹, hxJ'⟩ rfl
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp hnorm' _).mp hxp
    · intro hx
      obtain ⟨hxJ', hxp⟩ := mem_modelPull.mp hx
      have hxJ : x ∈ J := htx.mpr hxJ'
      refine mem_modelPull.mpr ⟨hxJ, ?_⟩
      have h1 := hrelψ ⟨x, hxJ⟩ ⟨t * x * t⁻¹, hxJ'⟩ rfl
      rw [h1] at hxp
      exact (Subgroup.mem_normalizer_iff.mp hnorm' _).mpr hxp
  ·
    intro ht
    obtain ⟨htJ, htp⟩ := mem_modelPull.mp ht
    have hcent : ∀ p ∈ alternatingGroup (Fin 8),
        ((swap (0 : Fin 8) 1)⁻¹ * ψ ⟨t, htJ⟩) * p = p * ((swap (0 : Fin 8) 1)⁻¹ * ψ ⟨t, htJ⟩) := by
      intro p hp
      obtain ⟨y, rfl⟩ := hψsurj p hp
      have h1 := hrelψ y (⟨t, htJ⟩ * y * ⟨t, htJ⟩⁻¹) (by simp)
      rw [map_mul, map_mul, map_inv] at h1
      calc ((swap (0 : Fin 8) 1)⁻¹ * ψ ⟨t, htJ⟩) * ψ y
          = (swap (0 : Fin 8) 1)⁻¹ * (ψ ⟨t, htJ⟩ * ψ y * (ψ ⟨t, htJ⟩)⁻¹) * ψ ⟨t, htJ⟩ := by group
        _ = (swap (0 : Fin 8) 1)⁻¹ * (swap (0 : Fin 8) 1 * ψ y * (swap (0 : Fin 8) 1)⁻¹) *
              ψ ⟨t, htJ⟩ := by rw [h1]
        _ = ψ y * ((swap (0 : Fin 8) 1)⁻¹ * ψ ⟨t, htJ⟩) := by group
    have h1 := eq_one_of_comm_alternatingGroup hcent
    have h2 : ψ ⟨t, htJ⟩ = swap (0 : Fin 8) 1 :=
      calc ψ ⟨t, htJ⟩ = swap (0 : Fin 8) 1 * ((swap (0 : Fin 8) 1)⁻¹ * ψ ⟨t, htJ⟩) := by group
        _ = swap (0 : Fin 8) 1 := by rw [h1, mul_one]
    have hτalt : ψ ⟨t, htJ⟩ ∈ alternatingGroup (Fin 8) := hΛalt htp
    rw [mem_alternatingGroup, h2, Equiv.Perm.sign_swap (show (0 : Fin 8) ≠ 1 by decide)] at hτalt
    exact absurd hτalt (by decide)

theorem tabA8 :
    ∀ (G : Type) [Group G] [Finite G] (J K : Subgroup G) (t : G) (L₁ L₂ U₁ U₂ D : Subgroup G),
      PatA8 J K t → IsComponentIn K (J ⊓ Subgroup.centralizer ({t} : Set G)) →
      IsA4Block L₁ U₁ → IsA4Block L₂ U₂ → L₁ ≤ K → L₂ ≤ K → U₁ ≠ U₂ → D ≤ K → Nat.card D = 8 →
      U₁ ≤ D → U₂ ≤ D →
        ∃ Λ Λr W : Subgroup G, (Λ = L₁ ∨ Λ = L₂) ∧ Λr ≤ J ∧ IsA4Block Λr W ∧
          (∀ l ∈ Λ, ∀ y ∈ Λr, l * y = y * l) ∧ t ∈ Subgroup.normalizer (Λr : Set G) ∧ t ∉ Λr := by
  intro G _ _ J K t L₁ L₂ U₁ U₂ D hpat hKcomp hA₁ hA₂ h₁ h₂ hne hDK hD8 hU₁ hU₂
  obtain ⟨hA6, φ, a, b, hab, htn, hrel⟩ := hpat
  obtain ⟨e₀⟩ := hA6
  obtain ⟨π, hπa, hπb⟩ : ∃ π : Perm (Fin 8), π a = 0 ∧ π b = 1 := by
    have key : ∀ a b : Fin 8, a ≠ b → (swap (swap a 0 b) 1 * swap a 0) a = 0 ∧
        (swap (swap a 0 b) 1 * swap a 0) b = 1 := by decide
    exact ⟨_, key a b hab⟩
  refine tabA8_of_model (modelHom J φ π) (modelHom_injective J φ π) (modelHom_sign J φ π)
    (fun p hp => modelHom_surj J φ π hp) htn ?_ hKcomp e₀ hA₁ hA₂ h₁ h₂ hne hDK hD8 hU₁ hU₂
  intro y y' hy
  have hy' : (y : G) = t⁻¹ * y' * t := by rw [hy]; group
  have h1 := hrel y' y hy'
  have h2 : ((φ y : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      swap a b * ((φ y' : alternatingGroup (Fin 8)) : Perm (Fin 8)) * (swap a b)⁻¹ := by
    rw [h1, MulAut.conjNormal_apply]
  have hss : swap a b * swap a b = 1 := Equiv.swap_mul_self a b
  have hsi : (swap a b)⁻¹ = swap a b := Equiv.swap_inv a b
  have h3 : ((φ y' : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      swap a b * ((φ y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * (swap a b)⁻¹ := by
    rw [h2, hsi]
    calc ((φ y' : alternatingGroup (Fin 8)) : Perm (Fin 8))
        = (swap a b * swap a b) * ((φ y' : alternatingGroup (Fin 8)) : Perm (Fin 8)) *
          (swap a b * swap a b) := by rw [hss]; group
      _ = _ := by group
  have hs : π * swap a b * π⁻¹ = swap (0 : Fin 8) 1 := by
    rw [← Equiv.swap_apply_apply, hπa, hπb]
  calc modelHom J φ π y' = π * ((φ y' : alternatingGroup (Fin 8)) : Perm (Fin 8)) * π⁻¹ := rfl
    _ = π * (swap a b * ((φ y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * (swap a b)⁻¹) *
          π⁻¹ := by rw [h3]
    _ = (π * swap a b * π⁻¹) * (π * ((φ y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * π⁻¹) *
          (π * swap a b * π⁻¹)⁻¹ := by group
    _ = swap (0 : Fin 8) 1 * (π * ((φ y : alternatingGroup (Fin 8)) : Perm (Fin 8)) * π⁻¹) *
          (swap (0 : Fin 8) 1)⁻¹ := by rw [hs]
    _ = swap (0 : Fin 8) 1 * modelHom J φ π y * (swap (0 : Fin 8) 1)⁻¹ := rfl

end CFSG.QuasithinUnique.DoubleA3
