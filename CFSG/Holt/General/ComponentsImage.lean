module

public import CFSG.Holt.General.Components
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention

public section

namespace CFSG.Holt.General

open Subgroup MulAction CFSG.ComponentClassification

variable {G : Type*} [Group G] {G' : Type*} [Group G']

theorem map_zStarIn_mulEquiv {B : Subgroup G} {B' : Subgroup G'} (ε : B ≃* B') :
    (zStarIn B).map ε.toMonoidHom = zStarIn B' := by
  have hO := CFSG.pPrimeCore_map_iso 2 ε
  ext x
  rw [mem_map_equiv, mem_zStarIn_iff, mem_zStarIn_iff]
  constructor
  · intro h y
    have := mem_map_of_mem ε.toMonoidHom (h (ε.symm y))
    rw [hO] at this
    simpa using this
  · intro h y
    have h1 := h (ε y)
    rw [← hO, mem_map_equiv] at h1
    simpa using h1

theorem comap_zStarIn_of_bijective {B : Subgroup G} {B' : Subgroup G'} (ψ : B →* B')
    (hψ : Function.Bijective ψ) : (zStarIn B').comap ψ = zStarIn B := by
  have h := map_zStarIn_mulEquiv (MulEquiv.ofBijective ψ hψ)
  have hψe : (MulEquiv.ofBijective ψ hψ).toMonoidHom = ψ := MonoidHom.ext fun _ => rfl
  rw [hψe] at h
  rw [← h, comap_map_eq_self_of_injective hψ.1]

@[expose] noncomputable def zStarQuotientEquiv {B : Subgroup G} {B' : Subgroup G'} (ψ : B →* B')
    (hψ : Function.Surjective ψ) (h : (zStarIn B').comap ψ = zStarIn B) :
    B ⧸ zStarIn B ≃* B' ⧸ zStarIn B' :=
  (QuotientGroup.quotientMulEquivOfEq
      (by rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', h])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (zStarIn B')).comp ψ)
      ((QuotientGroup.mk'_surjective _).comp hψ))

@[simp]
theorem zStarQuotientEquiv_mk {B : Subgroup G} {B' : Subgroup G'} (ψ : B →* B')
    (hψ : Function.Surjective ψ) (h : (zStarIn B').comap ψ = zStarIn B) (b : B) :
    zStarQuotientEquiv ψ hψ h (b : B ⧸ zStarIn B) = (ψ b : B' ⧸ zStarIn B') :=
  rfl

theorem map_map_mk_zStarQuotientEquiv {B : Subgroup G} {B' : Subgroup G'} (ψ : B →* B')
    (hψ : Function.Surjective ψ) (h : (zStarIn B').comap ψ = zStarIn B) (W : Subgroup B) :
    (W.map (QuotientGroup.mk' (zStarIn B))).map (zStarQuotientEquiv ψ hψ h).toMonoidHom =
      (W.map ψ).map (QuotientGroup.mk' (zStarIn B')) := by
  rw [map_map, map_map]
  rfl

theorem map_subgroupOf_subgroupMap (φ : G →* G') (B U : Subgroup G) (hU : φ.ker ≤ U) :
    (U.subgroupOf B).map (φ.subgroupMap B) = (U.map φ).subgroupOf (B.map φ) := by
  ext ⟨y, hy⟩
  rw [mem_subgroupOf]
  constructor
  · rintro ⟨b, hb, hby⟩
    rw [← congrArg Subtype.val hby]
    exact mem_map_of_mem φ (mem_subgroupOf.mp hb)
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨b, hbB, hbu⟩ := hy
    have hk : u⁻¹ * b ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hbu, inv_mul_cancel]
    refine ⟨⟨b, hbB⟩, mem_subgroupOf.mpr ?_, Subtype.ext hbu⟩
    have := mul_mem hu (hU hk)
    rwa [mul_inv_cancel_left] at this

theorem map_stabilizerImage_zStarQuotientEquiv {Ω Ω' : Type*} [MulAction G Ω]
    [MulAction G' Ω'] {α : Ω} {α' : Ω'} {φ : G →* G'}
    (hstab : (stabilizer G' α').comap φ = stabilizer G α) {B : Subgroup G}
    (h : (zStarIn (B.map φ)).comap (φ.subgroupMap B) = zStarIn B) :
    (stabilizerImage Ω α B).map
        (zStarQuotientEquiv (φ.subgroupMap B) (φ.subgroupMap_surjective B) h).toMonoidHom =
      stabilizerImage Ω' α' (B.map φ) := by
  have hker : φ.ker ≤ stabilizer G α := by
    intro x hx
    rw [← hstab, mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hsub : ((stabilizer G α).map φ).subgroupOf (B.map φ) =
      (stabilizer G' α').subgroupOf (B.map φ) := by
    ext ⟨y, b, -, rfl⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    constructor
    · rintro ⟨g, hg, hgy⟩
      have hg' : φ g ∈ stabilizer G' α' := by
        rw [← mem_comap, hstab]; exact hg
      rwa [← hgy]
    · intro hb
      have hb' : b ∈ stabilizer G α := by rw [← hstab, mem_comap]; exact hb
      exact mem_map_of_mem φ hb'
  unfold stabilizerImage
  rw [map_map_mk_zStarQuotientEquiv, map_subgroupOf_subgroupMap φ B _ hker, hsub]

section Image

variable [Finite G] {φ : G →* G'} (hφ : Function.Surjective φ) {B : Subgroup G}
  (hB : CFSG.IsPComponent 2 B) (hBφ : ¬ B ≤ φ.ker)

include hφ hB hBφ

theorem isPComponent_map : CFSG.IsPComponent 2 (B.map φ) := by
  have : Finite G' := Finite.of_surjective φ hφ
  rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple] at hB ⊢
  obtain ⟨hsub, hres, hqs⟩ := hB
  have hψ : Function.Surjective (φ.subgroupMap B) := φ.subgroupMap_surjective B
  have hres' : CatalogueBPrimeJoin.primeResidual 2 (B.map φ) = ⊤ := by
    rw [← CatalogueBPrimeJoin.primeResidual_map_surjective 2 _ hψ, hres,
      map_top_of_surjective _ hψ]
  refine ⟨hsub.map hφ, hres', ?_⟩
  have : (CFSG.pPrimeCore 2 B).Normal := CFSG.pPrimeCore_normal
  have : (CFSG.pPrimeCore 2 (B.map φ)).Normal := CFSG.pPrimeCore_normal
  have hle : CFSG.pPrimeCore 2 B ≤ (CFSG.pPrimeCore 2 (B.map φ)).comap (φ.subgroupMap B) :=
    map_le_iff_le_comap.mp (CFSG.map_pPrimeCore_le _ hψ)
  have hθ := QuotientGroup.map_surjective_of_surjective _ _ _
    (QuotientGroup.mk_surjective.comp hψ) hle
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs
      (QuotientGroup.map _ _ _ hle).normal_ker with hker | hker
  · exfalso
    apply hBφ
    have hO : CFSG.pPrimeCore 2 (B.map φ) = ⊤ := by
      rw [← QuotientGroup.subsingleton_iff]
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := hθ a
      obtain ⟨b, rfl⟩ := hθ b
      rw [MonoidHom.mem_ker.mp (hker ▸ mem_top a), MonoidHom.mem_ker.mp (hker ▸ mem_top b)]
    have hcop : Nat.Coprime 2 (Nat.card (B.map φ)) := by
      have := CFSG.pPrimeCore_coprime_card (p := 2) (G := B.map φ)
      rwa [hO, card_top] at this
    have hbot := CatalogueBPrimeJoin.primeResidual_eq_bot_of_coprime_card 2 hcop
    rw [hres'] at hbot
    rw [← Subgroup.map_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx⟩ : B.map φ) ∈ (⊥ : Subgroup (B.map φ)) := hbot ▸ mem_top _
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp hx'))
  · exact CFSG.LocalCores.isQuasisimple_of_surjective hqs _ hθ hker

end Image

section Transport

variable {Ω Ω' : Type*} [MulAction G Ω] [MulAction G' Ω']

private theorem fusionIsBenderGroup_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.Open.fusionIsBenderGroup X) : CFSG.Open.fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem IsGoodZ.congr {α : Ω} {α' : Ω'} {B : Subgroup G} {B' : Subgroup G'}
    (ε : B ⧸ zStarIn B ≃* B' ⧸ zStarIn B')
    (hε : (stabilizerImage Ω α B).map ε.toMonoidHom = stabilizerImage Ω' α' B')
    (h : IsGoodZ G Ω α B) : IsGoodZ G' Ω' α' B' := by
  rcases h with ⟨hbend, hse⟩ | ⟨m, hm, e, he⟩
  · refine Or.inl ⟨fusionIsBenderGroup_congr ε hbend, ?_⟩
    rw [← hε]
    exact CFSG.GH74.Uniqueness.Bender.IsStronglyEmbedded.map hse ε
  · refine Or.inr ⟨m, hm, ε.symm.trans e, ?_⟩
    have hsymm : (stabilizerImage Ω' α' B').map ε.symm.toMonoidHom = stabilizerImage Ω α B :=
      (map_symm_eq_iff_map_eq _).mpr hε
    have htrans : (ε.symm.trans e).toMonoidHom = e.toMonoidHom.comp ε.symm.toMonoidHom := rfl
    rw [htrans, ← map_map, hsymm, he]

theorem isGoodZ_congr {α : Ω} {α' : Ω'} {B : Subgroup G} {B' : Subgroup G'}
    (ε : B ⧸ zStarIn B ≃* B' ⧸ zStarIn B')
    (hε : (stabilizerImage Ω α B).map ε.toMonoidHom = stabilizerImage Ω' α' B') :
    IsGoodZ G Ω α B ↔ IsGoodZ G' Ω' α' B' :=
  ⟨IsGoodZ.congr ε hε, IsGoodZ.congr ε.symm ((map_symm_eq_iff_map_eq _).mpr hε)⟩

end Transport

end CFSG.Holt.General
