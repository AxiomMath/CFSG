module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalRows
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup

theorem normalizer_subtype_eq {A : Type} [Group A] (L : Subgroup A) (U : Subgroup L) :
    (normalizer ((U.map L.subtype : Subgroup A) : Set A)).subgroupOf L =
      normalizer (U : Set L) := by
  have h2 : (U.map L.subtype).subgroupOf L = U :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective U
  have h := Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le U)
  rw [h2] at h
  exact h

theorem mem_normalizer_subtype_iff {A : Type} [Group A] (L : Subgroup A) (U : Subgroup L) (x : L) :
    x ∈ normalizer (U : Set L) ↔ (x : A) ∈ normalizer ((U.map L.subtype : Subgroup A) : Set A) := by
  rw [← normalizer_subtype_eq L U]
  exact Iff.rfl

theorem pCoreOf_subtype_map {A : Type} [Group A] {K₀ L : Subgroup A} (hK₀L : K₀ ≤ L) :
    (pCoreOf 2 (K₀.subgroupOf L)).map L.subtype = pCoreOf 2 K₀ := by
  have hcomp : L.subtype.comp (K₀.subgroupOf L).subtype =
      K₀.subtype.comp (Subgroup.subgroupOfEquivOfLe hK₀L).toMonoidHom := by
    ext x
    rfl
  unfold pCoreOf
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe hK₀L)]

theorem map_inf_ne_bot_of_subgroupOf {A : Type} [Group A] {K₀ L : Subgroup A} (U : Subgroup L)
    (hUK : U ⊓ K₀.subgroupOf L ≠ ⊥) : U.map L.subtype ⊓ K₀ ≠ ⊥ := by
  intro hbot
  apply hUK
  rw [eq_bot_iff]
  rintro y ⟨hyU, hyK⟩
  have hmem : (y : A) ∈ U.map L.subtype ⊓ K₀ :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨y, hyU, rfl⟩, Subgroup.mem_subgroupOf.mp hyK⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (Subtype.ext hmem)

theorem row_of_model {s : TauCeti.SporadicName} {p : ℕ}
    (h : ∀ (G : Type) [Group G] [Finite G],
      Nonempty (G ≃* (TauCeti.CFSGIndex.sporadic s).Group) → p.Prime → 5 ≤ p →
      ∀ (K : Subgroup G) (z : G), orderOf z = p → K ≠ ⊤ → z ∈ K →
        normalizer (zpowers z : Set G) ≤ K →
        (∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
          normalizer (U : Set G) ≤ K) →
        (∃ y ∈ pCoreOf 2 K, z * y ≠ y * z) → normalizer (pCoreOf 2 K : Set G) = K →
        KxSection z K 3 ∧ s ≠ .M11) :
    KFactSporLocalRow s p := by
  unfold KFactSporLocalRow
  intro A _ _ L K₀ z hL _ _ hp hp5 _ hz hK₀L hzK hnL hN hcl hy hNN
  have hzL : z ∈ L := hK₀L hzK
  have hzord : orderOf (⟨z, hzL⟩ : L) = p := (Subgroup.orderOf_mk z hzL).trans hz
  have hKne : K₀.subgroupOf L ≠ ⊤ := fun htop => hnL (Subgroup.subgroupOf_eq_top.mp htop)
  have hzK' : (⟨z, hzL⟩ : L) ∈ K₀.subgroupOf L := Subgroup.mem_subgroupOf.mpr hzK
  have hzpow : (zpowers (⟨z, hzL⟩ : L)).map L.subtype = zpowers z :=
    MonoidHom.map_zpowers L.subtype _
  have hnorm : normalizer ((zpowers (⟨z, hzL⟩ : L) : Subgroup L) : Set L) ≤ K₀.subgroupOf L := by
    intro x hx
    have hx' : (x : A) ∈ normalizer ((zpowers z : Subgroup A) : Set A) := by
      rw [← hzpow]
      exact (mem_normalizer_subtype_iff L _ x).mp hx
    exact Subgroup.mem_subgroupOf.mpr (hN (Subgroup.mem_inf.mpr ⟨hx', x.2⟩))
  have hclos : ∀ U : Subgroup L, IsPGroup 2 U → (⟨z, hzL⟩ : L) ∈ normalizer (U : Set L) →
      U ⊓ K₀.subgroupOf L ≠ ⊥ → normalizer (U : Set L) ≤ K₀.subgroupOf L := by
    intro U hU hzU hUK x hx
    have hzA : z ∈ normalizer ((U.map L.subtype : Subgroup A) : Set A) :=
      (mem_normalizer_subtype_iff L U _).mp hzU
    have hNV := hcl (U.map L.subtype) (Subgroup.map_subtype_le U) (hU.map L.subtype) hzA
      (map_inf_ne_bot_of_subgroupOf U hUK)
    have hxA : (x : A) ∈ normalizer ((U.map L.subtype : Subgroup A) : Set A) :=
      (mem_normalizer_subtype_iff L U x).mp hx
    exact Subgroup.mem_subgroupOf.mpr (hNV (Subgroup.mem_inf.mpr ⟨hxA, x.2⟩))
  have hy' : ∃ y ∈ pCoreOf 2 (K₀.subgroupOf L), (⟨z, hzL⟩ : L) * y ≠ y * ⟨z, hzL⟩ := by
    obtain ⟨y, hyP, hyne⟩ := hy
    have hyP' : y ∈ (pCoreOf 2 (K₀.subgroupOf L)).map L.subtype := by
      rw [pCoreOf_subtype_map hK₀L]
      exact hyP
    obtain ⟨y', hy'P, hy'eq⟩ := Subgroup.mem_map.mp hyP'
    refine ⟨y', hy'P, fun heq => hyne ?_⟩
    have h2 := congrArg Subtype.val heq
    simp only [Subgroup.coe_mul] at h2
    rw [← hy'eq]
    exact h2
  have hNN' : normalizer ((pCoreOf 2 (K₀.subgroupOf L) : Subgroup L) : Set L) =
      K₀.subgroupOf L := by
    have key := normalizer_subtype_eq L (pCoreOf 2 (K₀.subgroupOf L))
    rw [pCoreOf_subtype_map hK₀L] at key
    rw [← key]
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : A) ∈ normalizer ((pCoreOf 2 K₀ : Subgroup A) : Set A) ⊓ L :=
        Subgroup.mem_inf.mpr ⟨hx, x.2⟩
      rw [hNN] at hx'
      exact hx'
    · intro hx
      have hx' : (x : A) ∈ normalizer ((pCoreOf 2 K₀ : Subgroup A) : Set A) ⊓ L := by
        rw [hNN]
        exact hx
      exact (Subgroup.mem_inf.mp hx').1
  obtain ⟨hKx, hM⟩ :=
    h ↥L hL hp hp5 (K₀.subgroupOf L) ⟨z, hzL⟩ hzord hKne hzK' hnorm hclos hy' hNN'
  unfold KxSection at hKx ⊢
  obtain ⟨H, N, hHK, hsimp, hzH, hzN, hdvd⟩ := hKx
  refine ⟨⟨H.map L.subtype, N.map L.subtype, ?_, ?_, ?_, ?_, ?_⟩, hM⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    exact Subgroup.mem_subgroupOf.mp (hHK hx)
  · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection.map_of_injective
      L.subtype L.subtype_injective hsimp
  · exact Subgroup.mem_map.mpr ⟨⟨z, hzL⟩, hzH, rfl⟩
  · intro hzN'
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hzN'
    have hx0 : x = ⟨z, hzL⟩ := Subtype.ext hxe
    exact hzN (hx0 ▸ hx)
  · rw [Subgroup.relIndex_map_map_of_injective N H L.subtype_injective]
    exact hdvd

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
