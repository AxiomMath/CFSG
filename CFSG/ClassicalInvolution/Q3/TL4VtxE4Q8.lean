module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

namespace Vtx

section Char

variable {G : Type} [Group G] {K₀ : Subgroup G}

theorem natCard_conjSub (g : G) (K : Subgroup G) : Nat.card ↥(conjSub g K) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_of_mem_conjClass (h2 : IsPGroup 2 ↥K₀) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K₀) : IsPGroup 2 ↥J := by
  obtain ⟨g, rfl⟩ := hJ
  exact h2.map (MulAut.conj g).toMonoidHom

theorem isSylow2In_self {J : Subgroup G} (h2 : IsPGroup 2 ↥J) : IsSylow2In J J :=
  ⟨le_rfl, h2, fun _ hV _ hJV => le_antisymm hV hJV⟩

variable [Finite G]

omit [Finite G] in
theorem mem_RSet_conjClass_iff (h2 : IsPGroup 2 ↥K₀) {R : Subgroup G} :
    R ∈ RSet (CoreAssembly.conjClass K₀) ↔ R ∈ CoreAssembly.conjClass K₀ := by
  constructor
  · intro hR
    obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
    have hJR := hRJ.2.2 J le_rfl (isPGroup_of_mem_conjClass h2 hJ) hRJ.1
    rw [← hJR]
    exact hJ
  · intro hR
    exact mem_RSet_of_isSylow2In hR (isSylow2In_self (isPGroup_of_mem_conjClass h2 hR))

theorem eq_of_le_of_mem_conjClass {A B : Subgroup G} (hA : A ∈ CoreAssembly.conjClass K₀)
    (hB : B ∈ CoreAssembly.conjClass K₀) (hAB : A ≤ B) : A = B := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  exact Subgroup.eq_of_le_of_card_ge hAB (by rw [natCard_conjSub, natCard_conjSub])

theorem mem_omegaNbr_conjClass_iff (h2 : IsPGroup 2 ↥K₀) {K J : Subgroup G} :
    J ∈ omegaNbr (CoreAssembly.conjClass K₀) K ↔ J ∈ CoreAssembly.conjClass K₀ ∧ J ≠ K ∧
      J ≤ Subgroup.normalizer (K : Set G) := by
  constructor
  · rintro ⟨hJ, hne, R, hR, hRJ, hRN⟩
    have hR' := (mem_RSet_conjClass_iff h2).mp hR
    rw [eq_of_le_of_mem_conjClass hR' hJ hRJ] at hRN
    exact ⟨hJ, hne, hRN⟩
  · rintro ⟨hJ, hne, hJN⟩
    exact ⟨hJ, hne, J, (mem_RSet_conjClass_iff h2).mpr hJ, le_rfl, hJN⟩

theorem mem_omegaStarNbr_conjClass_iff (h2 : IsPGroup 2 ↥K₀) (h8 : Nat.card ↥K₀ = 8)
    {K J : Subgroup G} :
    J ∈ omegaStarNbr (CoreAssembly.conjClass K₀) K ↔ J ∈ CoreAssembly.conjClass K₀ ∧ J ≠ K ∧
      ∃ u ∈ J, orderOf u = 4 ∧ u ∈ Subgroup.normalizer (K : Set G) := by
  have h8' : ∀ A ∈ CoreAssembly.conjClass K₀, Nat.card ↥A = 8 := by
    rintro _ ⟨g, rfl⟩
    rw [natCard_conjSub, h8]
  constructor
  · rintro ⟨hJ, hne, U, ⟨R, hR, hUR, hcyc, hidx⟩, hUJ, hUN⟩
    have hR' := (mem_RSet_conjClass_iff h2).mp hR
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hidx, h8' R hR'] at h1
    have hU4 : Nat.card ↥U = 4 := by omega
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf (g : G) = 4 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hU4]
    exact ⟨hJ, hne, g, hUJ g.2, hord, hUN g.2⟩
  · rintro ⟨hJ, hne, u, huJ, hu4, huN⟩
    refine ⟨hJ, hne, Subgroup.zpowers u, ?_, Subgroup.zpowers_le.mpr huJ,
      Subgroup.zpowers_le.mpr huN⟩
    refine mem_USet_of_natCard hJ (isSylow2In_self (isPGroup_of_mem_conjClass h2 hJ))
      (Subgroup.zpowers_le.mpr huJ) inferInstance ?_
    rw [Nat.card_zpowers, hu4, h8' J hJ]

end Char

section Conj

variable {G : Type} [Group G]

theorem conjSub_le_normalizer {J K : Subgroup G} (h : J ≤ Subgroup.normalizer (K : Set G))
    (g : G) : conjSub g J ≤ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  rw [mem_normalizer_iff_conjSub_eq]
  have h1 := mem_normalizer_iff_conjSub_eq.mp (h hx)
  calc conjSub x (conjSub g K) = conjSub g (conjSub (g⁻¹ * x * g) K) := by
        rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
    _ = conjSub g K := by rw [h1]

theorem conj_mem_normalizer_conjSub {K : Subgroup G} {u : G}
    (h : u ∈ Subgroup.normalizer (K : Set G)) (g : G) :
    g * u * g⁻¹ ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) := by
  have h2 := conjSub_le_normalizer (Subgroup.zpowers_le.mpr h) g
  exact h2 (conj_mem_conjSub (Subgroup.mem_zpowers u))

end Conj

section Map

variable {M G : Type} [Group M] [Group G] (φ : M →* G)

theorem mem_normalizer_map_iff (hφ : Function.Injective φ) {u : M} {K : Subgroup M} :
    φ u ∈ Subgroup.normalizer ((K.map φ : Subgroup G) : Set G) ↔
      u ∈ Subgroup.normalizer (K : Set M) := by
  rw [mem_normalizer_iff_conjSub_eq, mem_normalizer_iff_conjSub_eq, conjSub_map]
  exact (Subgroup.map_injective hφ).eq_iff

theorem map_le_normalizer_map_iff (hφ : Function.Injective φ) {J K : Subgroup M} :
    J.map φ ≤ Subgroup.normalizer ((K.map φ : Subgroup G) : Set G) ↔
      J ≤ Subgroup.normalizer (K : Set M) := by
  constructor
  · intro h j hj
    exact (mem_normalizer_map_iff φ hφ).mp (h (Subgroup.mem_map_of_mem φ hj))
  · rintro h _ ⟨j, hj, rfl⟩
    exact (mem_normalizer_map_iff φ hφ).mpr (h hj)

theorem isUniqueInvolution_map (hφ : Function.Injective φ) {K : Subgroup M} {s : M}
    (h : IsUniqueInvolution K s) : IsUniqueInvolution (K.map φ) (φ s) where
  mem := Subgroup.mem_map_of_mem φ h.mem
  ne_one := fun h1 => h.ne_one (hφ (h1.trans (map_one φ).symm))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨k, hk, rfl⟩ hkk
    rw [← map_mul, ← map_one φ] at hkk
    rcases h.unique k hk (hφ hkk) with h1 | h1
    · left
      rw [h1, map_one]
    · right
      rw [h1]

end Map

structure AmbientQuatDatum {G : Type} [Group G] (H K : Subgroup G) (s : G) : Prop where
  le : K ≤ H
  q8 : Nonempty (↥K ≃* QuaternionGroup 2)
  inv : IsUniqueInvolution K s
  twins : ∀ c ∈ H, c * s = s * c → conjSub c K = K ∨ ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x

section Ambient

variable {M G : Type} [Group M] [Group G] (φ : M →* G)

theorem ambientQuatDatum_map (hφ : Function.Injective φ) {K : Subgroup M} {s : M}
    (hd : QuatTwinDatum K s) : AmbientQuatDatum φ.range (K.map φ) (φ s) := by
  obtain ⟨e⟩ := hd.q8
  refine ⟨Subgroup.map_le_range φ K, ⟨(K.equivMapOfInjective φ hφ).symm.trans e⟩,
    isUniqueInvolution_map φ hφ hd.inv, ?_⟩
  rintro _ ⟨m, rfl⟩ hms
  have hm : m ∈ Subgroup.centralizer ({s} : Set M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hφ (by rw [map_mul, map_mul, hms])
  rw [conjSub_map]
  rcases hd.twins m hm with h | h
  · left
    rw [h]
  · right
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

end Ambient

theorem AmbientQuatDatum.conj {G : Type} [Group G] {H K : Subgroup G} {s : G}
    (hd : AmbientQuatDatum H K s) {g : G} (hg : g ∈ H) :
    AmbientQuatDatum H (conjSub g K) (g * s * g⁻¹) := by
  obtain ⟨e⟩ := hd.q8
  refine ⟨fun x hx => ?_, ⟨(K.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩, hd.inv.conj g, fun c hc hcs => ?_⟩
  · rw [mem_conjSub_iff] at hx
    have h1 := H.mul_mem (H.mul_mem hg (hd.le hx)) (H.inv_mem hg)
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
  · have hc' : g⁻¹ * c * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hg) hc) hg
    have hcs' : g⁻¹ * c * g * s = s * (g⁻¹ * c * g) := by
      calc g⁻¹ * c * g * s = g⁻¹ * (c * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * c) * g := by rw [hcs]
        _ = s * (g⁻¹ * c * g) := by group
    have he : conjSub c (conjSub g K) = conjSub g (conjSub (g⁻¹ * c * g) K) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [he]
    rcases hd.twins _ hc' hcs' with h | h
    · left
      rw [h]
    · right
      intro x hx y hy
      rw [mem_conjSub_iff] at hx hy
      have h2 := h _ hx _ hy
      calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h2]
        _ = y * x := by group

end Vtx

end CFSG.ClassicalInvolution.Q3.TL4
