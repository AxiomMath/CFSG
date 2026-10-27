module

public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.GLS.TwoThin.Struct

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def conjAut {X : Subgroup G} {q : G} (hq : q ∈ normalizer (X : Set G)) : ↥X ≃* ↥X where
  toFun a := ⟨q * a * q⁻¹, (Subgroup.mem_normalizer_iff.mp hq a).mp a.2⟩
  invFun a := ⟨q⁻¹ * a * q, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hq) a).mp a.2
    simpa using this⟩
  left_inv a := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv a := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem mul_mem_pPrimeCoreOf_of_mem_normalizer {K : Subgroup G} {q : G}
    (hq : q ∈ normalizer (K : Set G)) {o : G} (ho : o ∈ pPrimeCoreOf 2 K) :
    q * o * q⁻¹ ∈ pPrimeCoreOf 2 K := by
  obtain ⟨o₀, ho₀, rfl⟩ := ho
  have h := pPrimeCore_map_iso 2 (conjAut hq)
  have h1 : conjAut hq o₀ ∈ pPrimeCore 2 ↥K := by
    rw [← h]
    exact Subgroup.mem_map_of_mem _ ho₀
  exact ⟨conjAut hq o₀, h1, rfl⟩

theorem mem_normalizer_pPrimeCoreOf {K : Subgroup G} {q : G} (hq : q ∈ normalizer (K : Set G)) :
    q ∈ normalizer (pPrimeCoreOf 2 K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => mul_mem_pPrimeCoreOf_of_mem_normalizer hq hh
  · intro hh
    have := mul_mem_pPrimeCoreOf_of_mem_normalizer (inv_mem hq) hh
    simpa [mul_assoc] using this

theorem pPrimeCoreOf_eq_map_subgroupOf {K Y' : Subgroup G} (h : K ≤ Y') :
    pPrimeCoreOf 2 K = (pPrimeCoreOf 2 (K.subgroupOf Y')).map Y'.subtype := by
  let e : ↥(K.subgroupOf Y') ≃* ↥K := Subgroup.subgroupOfEquivOfLe h
  unfold pPrimeCoreOf
  rw [Subgroup.map_map, ← pPrimeCore_map_iso 2 e, Subgroup.map_map]
  rfl

variable [Finite G]

theorem mem_pPrimeCoreOf_of_barMk_eq_one {Y' K' : Subgroup G} (hK'Y : K' ≤ Y')
    (hsub : (K'.subgroupOf Y').IsSubnormal) {k : G} (hk : k ∈ K') (hkY : k ∈ Y')
    (h : barMk ↥Y' ⟨k, hkY⟩ = 1) : k ∈ pPrimeCoreOf 2 K' := by
  let M := K'.subgroupOf Y'
  have ha : (⟨⟨k, hkY⟩, Subgroup.mem_subgroupOf.mpr hk⟩ : ↥M) ∈
      ((QuotientGroup.mk' (pPrimeCore 2 ↥Y')).comp M.subtype).ker := h
  rw [ker_restrict_eq_pPrimeCore hsub] at ha
  rw [pPrimeCoreOf_eq_map_subgroupOf hK'Y]
  exact ⟨⟨k, hkY⟩, ⟨_, ha, rfl⟩, rfl⟩

theorem mem_normalizer_of_map_normalizes {Y' K' : Subgroup G} (hK'Y : K' ≤ Y')
    (hK'2 : TwoComponents.IsTwoComponent (K'.subgroupOf Y')) {q : G} (hq : q ∈ Y')
    (hπ : ((K'.subgroupOf Y').map (barMk ↥Y')).map (MulAut.conj (barMk ↥Y' ⟨q, hq⟩)).toMonoidHom =
      (K'.subgroupOf Y').map (barMk ↥Y')) :
    q ∈ normalizer (K' : Set G) := by
  let M := K'.subgroupOf Y'
  let qY : ↥Y' := ⟨q, hq⟩
  let c : ↥Y' ≃* ↥Y' := MulAut.conj qY
  have h2 : TwoComponents.IsTwoComponent (M.map c.toMonoidHom) :=
    (TwoComponentTransport.equiv_iff c M).mpr hK'2
  have hcomp : (barMk ↥Y').comp c.toMonoidHom =
      (MulAut.conj (barMk ↥Y' qY)).toMonoidHom.comp (barMk ↥Y') := by
    ext a
    simp [c]
  have himg : (M.map c.toMonoidHom).map (barMk ↥Y') = M.map (barMk ↥Y') := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact hπ
  have hMeq : M.map c.toMonoidHom = M :=
    OddKernelTwoComponents.lift_unique (barMk ↥Y') barMk_surjective odd_card_ker_barMk _ _ h2
      hK'2 himg
  have key : ∀ a : ↥Y', c a ∈ M ↔ a ∈ M := fun a => by
    have := Subgroup.mem_map_equiv (f := c) (K := M) (x := c a)
    rw [hMeq] at this
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have hkY : k ∈ Y' := hK'Y hk
    have hm : (⟨k, hkY⟩ : ↥Y') ∈ M := Subgroup.mem_subgroupOf.mpr hk
    exact Subgroup.mem_subgroupOf.mp ((key _).mpr hm)
  · intro hk
    have hkY : k ∈ Y' := by
      have h1 : q⁻¹ * (q * k * q⁻¹) * q ∈ Y' :=
        mul_mem (mul_mem (inv_mem hq) (hK'Y hk)) hq
      simpa [mul_assoc] using h1
    have hm : c ⟨k, hkY⟩ ∈ M := Subgroup.mem_subgroupOf.mpr hk
    exact Subgroup.mem_subgroupOf.mp ((key _).mp hm)

theorem mem_centralizerSection_of_map_eq {Y' K' : Subgroup G} (hK'Y : K' ≤ Y')
    (hK'2 : TwoComponents.IsTwoComponent (K'.subgroupOf Y')) {q : G} (hq : q ∈ Y')
    (hπ : ∀ m ∈ K'.subgroupOf Y', barMk ↥Y' (⟨q, hq⟩ * m * ⟨q, hq⟩⁻¹) = barMk ↥Y' m) :
    q ∈ centralizerSection K' (pPrimeCoreOf 2 K') := by
  let M := K'.subgroupOf Y'
  let qY : ↥Y' := ⟨q, hq⟩
  have hsub : M.IsSubnormal :=
    Components.mathlib_subnormal_of_chain hK'2.1 Subgroup.IsSubnormal.top
  have hnorm : ((K'.subgroupOf Y').map (barMk ↥Y')).map
      (MulAut.conj (barMk ↥Y' ⟨q, hq⟩)).toMonoidHom = (K'.subgroupOf Y').map (barMk ↥Y') := by
    ext z
    constructor
    · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
      refine ⟨m, hm, ?_⟩
      have := hπ m hm
      simpa using this.symm
    · rintro ⟨m, hm, rfl⟩
      refine ⟨barMk ↥Y' m, ⟨m, hm, rfl⟩, ?_⟩
      have := hπ m hm
      simpa using this
  have hqN : q ∈ normalizer (K' : Set G) := mem_normalizer_of_map_normalizes hK'Y hK'2 hq hnorm
  refine ⟨hqN, mem_normalizer_pPrimeCoreOf hqN, fun k hk => ?_⟩
  have hkY : k ∈ Y' := hK'Y hk
  have hqk : q * k⁻¹ * q⁻¹ ∈ K' := (Subgroup.mem_normalizer_iff.mp hqN _).mp (inv_mem hk)
  have hcomm : ⁅k, q⁆ = k * (q * k⁻¹ * q⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hcK : ⁅k, q⁆ ∈ K' := by
    rw [hcomm]
    exact mul_mem hk hqk
  have hcY : ⁅k, q⁆ ∈ Y' := hK'Y hcK
  refine mem_pPrimeCoreOf_of_barMk_eq_one hK'Y hsub hcK hcY ?_
  have ha : (⟨k, hkY⟩ : ↥Y') ∈ M := Subgroup.mem_subgroupOf.mpr hk
  have ha' : (⟨k, hkY⟩ : ↥Y')⁻¹ ∈ M := inv_mem ha
  have h1 := hπ _ ha'
  have : (⟨⁅k, q⁆, hcY⟩ : ↥Y') = ⟨k, hkY⟩ * (qY * (⟨k, hkY⟩ : ↥Y')⁻¹ * qY⁻¹) := by
    apply Subtype.ext
    exact hcomm
  rw [this, map_mul, h1]
  simp

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {q : G} (hA : q ∈ normalizer (A : Set G))
    (hB : q ∈ normalizer (B : Set G)) : q ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  simp only [Subgroup.mem_inf]
  rw [hA h, hB h]

theorem conj_mem_of_unique_isPCompIn {X Λ : Subgroup G} (hΛ : IsPCompIn 2 X Λ)
    (huniq : ∀ L : Subgroup G, IsPCompIn 2 X L → L = Λ) {q : G}
    (hq : q ∈ normalizer (X : Set G)) {a : G} (ha : a ∈ Λ) : q * a * q⁻¹ ∈ Λ := by
  let σ := conjAut hq
  let L₁ : Subgroup G := Λ.map (MulAut.conj q).toMonoidHom
  have hL₁X : L₁ ≤ X := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hq b).mp (hΛ.1 hb)
  have hmap : (Λ.subgroupOf X).map σ.toMonoidHom = L₁.subgroupOf X := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, Subgroup.mem_subgroupOf.mp hw, rfl⟩
    · intro hz
      obtain ⟨b, hb, hbz⟩ := Subgroup.mem_subgroupOf.mp hz
      refine ⟨⟨b, hΛ.1 hb⟩, Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hbz⟩
  have hL₁ : IsPCompIn 2 X L₁ := by
    refine isPCompIn_two_iff.mpr ⟨hL₁X, ?_⟩
    rw [← hmap]
    exact (TwoComponentTransport.equiv_iff σ (Λ.subgroupOf X)).mpr (isPCompIn_two_iff.mp hΛ).2
  have := huniq L₁ hL₁
  rw [← this]
  exact ⟨a, ha, rfl⟩

end CFSG.GH74.GLS.TwoThin
