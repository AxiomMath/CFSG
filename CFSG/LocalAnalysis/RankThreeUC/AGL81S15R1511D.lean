module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

theorem isLThreeTwoPow_of_mulEquiv_aux1 {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (h : IsLThreeTwoPow T) : IsLThreeTwoPow S := by
  unfold IsLThreeTwoPow at h ⊢
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨d, hd, ⟨e.trans f⟩⟩

theorem isLThreeTwoPow_quotient_aux2 {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (f : A ≃* B) (h : IsLThreeTwoPow (↥B ⧸ CFSG.pPrimeCore 3 ↥B)) :
    IsLThreeTwoPow (↥A ⧸ CFSG.pPrimeCore 3 ↥A) :=
  isLThreeTwoPow_of_mulEquiv_aux1
    (QuotientGroup.congr (CFSG.pPrimeCore 3 ↥A) (CFSG.pPrimeCore 3 ↥B) f
      (CFSG.pPrimeCore_map_iso 3 f)) h

theorem isPComponent_map_equivMap_aux1 {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X →* Y) (hφ : Function.Injective φ) (K L : Subgroup X)
    (h : CFSG.IsPComponent 3 (L.subgroupOf K)) :
    CFSG.IsPComponent 3 ((L.map φ).subgroupOf (K.map φ)) := by
  have hmap : (L.subgroupOf K).map (K.equivMapOfInjective φ hφ).toMonoidHom =
      (L.map φ).subgroupOf (K.map φ) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map.mpr ⟨(z : X), Subgroup.mem_subgroupOf.mp hz, rfl⟩)
    · intro hx
      obtain ⟨w, hwL, hwx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp x.2
      have hwk : w = k := hφ (hwx.trans hkx.symm)
      subst hwk
      exact Subgroup.mem_map.mpr ⟨⟨w, hkK⟩, Subgroup.mem_subgroupOf.mpr hwL, Subtype.ext hwx⟩
  rw [← hmap]
  exact ((CFSG.LocalAnalysis.ComponentInitial.p_component_isomorphism_transport 3 Nat.prime_three
    (K.equivMapOfInjective φ hφ)).1 (L.subgroupOf K)).mp h

section GLevel

variable {G : Type} [Group G] [Finite G]

def normalizer_le_normalizer_of_characteristic_aux1 (T : Subgroup G) {g : G}
    (hg : g ∈ normalizer (T : Set G)) : ↥T ≃* ↥T where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp x.2
    simpa using h⟩
  left_inv x := by
    ext
    simp [mul_assoc]
  right_inv x := by
    ext
    simp [mul_assoc]
  map_mul' x y := by
    ext
    simp [mul_assoc]

theorem normalizer_le_normalizer_of_characteristic {T Ti : Subgroup G} (hle : Ti ≤ T)
    (hchar : (Ti.subgroupOf T).Characteristic) :
    normalizer (T : Set G) ≤ normalizer (Ti : Set G) := by
  have key : ∀ g ∈ normalizer (T : Set G), ∀ y ∈ Ti, g * y * g⁻¹ ∈ Ti := by
    intro g hg y hy
    have hmap := Subgroup.characteristic_iff_map_le.mp hchar
      (normalizer_le_normalizer_of_characteristic_aux1 T hg)
    have hmem := hmap (Subgroup.mem_map.mpr ⟨⟨y, hle hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩)
    exact Subgroup.mem_subgroupOf.mp hmem
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro hy
    have h := key g⁻¹ (inv_mem hg) (g * y * g⁻¹) hy
    simpa [mul_assoc] using h

theorem isStronglyPEmbedded_subgroupOf_inf {M H : Subgroup G} {p : ℕ}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) (hHM : ¬ H ≤ M)
    (hp : p ∣ Nat.card ↥(H ⊓ M)) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p ((H ⊓ M).subgroupOf H) := by
  obtain ⟨-, -, hconj⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hHM (htop.trans inf_le_right)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact hp
  · intro g hg hdvd
    have hgM : (g : G) ∉ M := fun hgM =>
      hg (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨g.2, hgM⟩))
    set Y := (H ⊓ M).subgroupOf H
    set Z := Y ⊓ Y.map (MulAut.conj g).toMonoidHom
    have hle : Z.map H.subtype ≤ M ⊓ M.map (MulAut.conj (g : G)).toMonoidHom := by
      rintro x ⟨z, hz, rfl⟩
      obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz1)).2, ?_⟩
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz2
      refine Subgroup.mem_map.mpr
        ⟨(y : G), (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2, ?_⟩
      have h := congrArg Subtype.val hyz
      simpa [MulAut.conj_apply, mul_assoc] using h
    have hcard1 : Nat.card ↥(Z.map H.subtype) = Nat.card ↥Z :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hcard2 := Subgroup.card_dvd_of_le hle
    apply hconj (g : G) hgM
    have h1 : p ∣ Nat.card ↥(Z.map H.subtype) := by
      rw [hcard1]
      exact hdvd
    exact h1.trans hcard2

theorem normalizer_inf_le_of_sylow_aux1 {X : Type} [Group X] {q : ℕ} [Fact q.Prime]
    (M : Subgroup X) (g : M) (T : Sylow q M) :
    ((g • T : Sylow q M) : Subgroup M).map M.subtype =
      ((T : Subgroup M).map M.subtype).map (MulAut.conj (g : X)).toMonoidHom := by
  ext x
  simp only [Sylow.coe_subgroup_smul, Subgroup.mem_map,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · refine ⟨g⁻¹ * y * g, ?_, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply] using hy
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hz
    · simp [MulAut.conj_apply]

theorem normalizer_inf_le_of_sylow_aux2 {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {K P P' : Subgroup X} (h : CFSG.ABGLocalTools.IsSylowOf p P K)
    (h' : CFSG.ABGLocalTools.IsSylowOf p P' K) :
    ∃ g ∈ K, P' = P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  exact ⟨(g : X), g.2, by rw [← hg, normalizer_inf_le_of_sylow_aux1]⟩

theorem normalizer_inf_le_of_sylow {M H T S : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hTH : T ≤ H)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S H) (hSM : S ≤ M)
    (hN : normalizer (S : Set G) ⊓ H ≤ M) : normalizer (T : Set G) ⊓ H ≤ M := by
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T (H ⊓ M) :=
    hT.of_le (le_inf hTH hT.le) inf_le_right
  have hS' : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ M) :=
    hS.of_le (le_inf hS.le hSM) inf_le_left
  obtain ⟨g, hgN, hTg⟩ := normalizer_inf_le_of_sylow_aux2 hS' hT'
  have hgH : g ∈ H := (Subgroup.mem_inf.mp hgN).1
  have hgM : g ∈ M := (Subgroup.mem_inf.mp hgN).2
  have hmemT : ∀ y : G, y ∈ T ↔ g⁻¹ * y * g ∈ S := by
    intro y
    rw [hTg, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, hsy⟩
      have e : g⁻¹ * y * g = s := by
        rw [← hsy]
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hs
    · intro h
      exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  intro x hx
  obtain ⟨hxN, hxH⟩ := Subgroup.mem_inf.mp hx
  have hx'N : g⁻¹ * x * g ∈ normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ S ↔ g * y * g⁻¹ ∈ T := by
      rw [hmemT]
      simp [mul_assoc]
    have h2 : g * y * g⁻¹ ∈ T ↔ x * (g * y * g⁻¹) * x⁻¹ ∈ T :=
      Subgroup.mem_normalizer_iff.mp hxN (g * y * g⁻¹)
    have h3 : x * (g * y * g⁻¹) * x⁻¹ ∈ T ↔ g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g ∈ S :=
      hmemT _
    have e : g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ := by
      group
    calc y ∈ S ↔ g * y * g⁻¹ ∈ T := h1
      _ ↔ x * (g * y * g⁻¹) * x⁻¹ ∈ T := h2
      _ ↔ g⁻¹ * (x * (g * y * g⁻¹) * x⁻¹) * g ∈ S := h3
      _ ↔ g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ ∈ S := by rw [e]
  have hx'H : g⁻¹ * x * g ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem hgH) hxH) hgH
  have hx'M : g⁻¹ * x * g ∈ M := hN (Subgroup.mem_inf.mpr ⟨hx'N, hx'H⟩)
  have hxeq : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [hxeq]
  exact M.mul_mem (M.mul_mem hgM hx'M) (M.inv_mem hgM)

theorem false_of_threeComponent_aux1 {M : Subgroup G} {Ti : Subgroup ↥M} (x : ↥M) :
    (x : G) ∈ normalizer ((Ti.map M.subtype : Subgroup G) : Set G) ↔
      x ∈ normalizer (Ti : Set ↥M) := by
  have hmem : ∀ y : ↥M, (y : G) ∈ Ti.map M.subtype ↔ y ∈ Ti := fun y =>
    Subgroup.mem_map_iff_mem M.subtype_injective
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    exact (hmem y).symm.trans ((h (y : G)).trans (hmem (x * y * x⁻¹)))
  · intro h z
    by_cases hz : z ∈ M
    · exact (hmem ⟨z, hz⟩).trans ((h ⟨z, hz⟩).trans (hmem (x * ⟨z, hz⟩ * x⁻¹)).symm)
    · have hzT : z ∉ Ti.map M.subtype := fun hm => hz (Subgroup.map_subtype_le Ti hm)
      have hxzT : (x : G) * z * (x : G)⁻¹ ∉ Ti.map M.subtype := fun hm => by
        apply hz
        have hM : (x : G) * z * (x : G)⁻¹ ∈ M := Subgroup.map_subtype_le Ti hm
        have := M.mul_mem (M.mul_mem (M.inv_mem x.2) hM) x.2
        simpa [mul_assoc] using this
      exact ⟨fun h1 => absurd h1 hzT, fun h1 => absurd h1 hxzT⟩

theorem false_of_threeComponent_aux2 {M : Subgroup G} (Ti : Subgroup ↥M) :
    normalizer ((Ti.map M.subtype : Subgroup G) : Set G) ⊓ M =
      (normalizer (Ti : Set ↥M)).map M.subtype := by
  ext g
  constructor
  · rintro ⟨hgN, hgM⟩
    exact Subgroup.mem_map.mpr
      ⟨⟨g, hgM⟩, (false_of_threeComponent_aux1 ⟨g, hgM⟩).mp hgN, rfl⟩
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact Subgroup.mem_inf.mpr ⟨(false_of_threeComponent_aux1 x).mpr hx, x.2⟩

end GLevel

end CFSG.LocalAnalysis.RankThreeUC.S15
