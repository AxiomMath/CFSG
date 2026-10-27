module

public import CFSG.GF2Type.Aschbacher1976Full.HSEmbedFacts
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourSymplecticFusion
public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.GF2Type.Aschbacher1976Full.WidthForm

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.LocalAnalysis.ComponentInitial
open scoped IsMulCommutative

private noncomputable def bilinIsometryEquiv {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (B : LinearMap.BilinForm K V) :
    bilinIsometryGroup B ≃* TauCeti.BilinForm.isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).subgroupMap
      (bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact TauCeti.BilinForm.mem_isometryGroup_iff.mpr hh
      · intro hg
        exact ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm g,
          TauCeti.BilinForm.mem_isometryGroup_iff.mp hg,
          (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).apply_symm_apply g⟩))

theorem hbar_embeds_perm_six {G : Type} [Group G] [Finite G] {z : G}
    (hZ : IsZ4Star z 2) (hz : orderOf z = 2) (hF2 : IsPGroup 2 ↥(Fz z)) :
    ∃ ι : ↥(Hz z) →* Equiv.Perm (Fin 6), ι.ker = (Fz z).subgroupOf (Hz z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ
  obtain ⟨hvel, -, b, -, -, halt, hnd, -, -, -, -, ⟨ι₀, hι₀inj, -⟩, -⟩ :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergCH.core_symplectic_transport (B := ⊥) bot_le
      (Embed.isCharacteristicP_Hz hF2) (by simp) (Embed.Fz_eq_inSubgroup_pCore hF2)
      (Embed.isCyclic_center_Fz hD hz hF2) (Width.isEA_quot (Embed.cdata_Fz hD hz))
      (Embed.z_mem_map_center_Fz hD hz hF2) hz (Embed.commutator_Fz hD hz)
  haveI := hvel
  have hfin := Embed.finrank_quot_pCore hD hz hF2
  haveI : FiniteDimensional (ZMod 2)
      (Additive (↥(pCore 2 ↥(Hz z)) ⧸ Subgroup.center ↥(pCore 2 ↥(Hz z)))) :=
    Module.Finite.of_finite
  obtain ⟨Φ⟩ := LargeExtraspecial.S45Q.nonempty_isometryGroup_equiv_perm halt hnd hfin
  let τ : ↥(bilinIsometryGroup b) →* Equiv.Perm (Fin 6) :=
    Φ.toMonoidHom.comp (bilinIsometryEquiv b).toMonoidHom
  have hτ : Function.Injective τ := Φ.injective.comp (bilinIsometryEquiv b).injective
  refine ⟨τ.comp (ι₀.comp (QuotientGroup.mk' (pCore 2 ↥(Hz z)))), ?_⟩
  have hsub : (Fz z).subgroupOf (Hz z) = pCore 2 ↥(Hz z) := by
    rw [Embed.Fz_eq_inSubgroup_pCore hF2]
    exact Subgroup.comap_map_eq_self_of_injective (Hz z).subtype_injective _
  rw [hsub]
  ext h
  constructor
  · intro hh
    have h1 : ι₀ (h : ↥(Hz z) ⧸ pCore 2 ↥(Hz z)) = 1 := (injective_iff_map_eq_one τ).mp hτ _ hh
    have h2 : (h : ↥(Hz z) ⧸ pCore 2 ↥(Hz z)) = 1 := (injective_iff_map_eq_one ι₀).mp hι₀inj _ h1
    exact (QuotientGroup.eq_one_iff h).mp h2
  · intro hh
    have h2 : (h : ↥(Hz z) ⧸ pCore 2 ↥(Hz z)) = 1 := (QuotientGroup.eq_one_iff h).mpr hh
    show τ (ι₀ (h : ↥(Hz z) ⧸ pCore 2 ↥(Hz z))) = 1
    rw [h2, map_one, map_one]

end CFSG.GF2Type.Aschbacher1976Full.HS
