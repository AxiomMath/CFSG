module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphE6
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm sigma_xm_single sigma_xm_neg_single)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

local instance f4PilotQ2E6RowCTNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Family

variable {G : Type} [Group G]

structure IsTwoE6GraphFamily (G₀ : Subgroup G) (t : G) (K' : Type) [Field K']
    (φ : ∀ J, (e6Datum K').leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (e6Datum K').leviAmalgam φ
  iSup_range : ⨆ J, (φ J).range = G₀
  conj : ∀ (i : Fin (Tag.rank .E6))
    (x : CFSG.LieType.CurtisTits.levi (e6Datum K').rootGroup {i})
    (y : CFSG.LieType.CurtisTits.levi (e6Datum K').rootGroup {rhoPerm i}),
    (y : e6Data_valid.minGroup K') = sigma K' (RingHom.id K') x →
      t * φ ⟨{i}, card_singleton_le_two_E6 i⟩ x * t⁻¹ =
        φ ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩ y

theorem IsTwoE6GraphFamily.apply_mem {G₀ : Subgroup G} {t : G} {K' : Type} [Field K']
    {φ : ∀ J, (e6Datum K').leviAmalgam J →* G} (hφ : IsTwoE6GraphFamily G₀ t K' φ) (J)
    (y : (e6Datum K').leviAmalgam J) : φ J y ∈ G₀ := by
  rw [← hφ.iSup_range]
  exact le_iSup (fun J => (φ J).range) J ⟨y, rfl⟩

end Family

section CT

variable {G : Type} [Group G]

theorem exists_surjective_of_isTwoE6GraphFamily {K' : Type} [Field K'] {G₀ : Subgroup G}
    {t : G} (hne : G₀ ≠ ⊥) {φ : ∀ J, (e6Datum K').leviAmalgam J →* G}
    (hφ : IsTwoE6GraphFamily G₀ t K' φ) :
    ∃ ψ : e6Data_valid.minGroup K' →* G₀,
      (∀ J (y : (e6Datum K').leviAmalgam J), ((ψ y : G₀) : G) = φ J y) ∧
        Function.Surjective ψ ∧ ψ.ker ≤ center (e6Data_valid.minGroup K') ∧
          center G₀ = (center (e6Data_valid.minGroup K')).map ψ := by
  set φ' : ∀ J, (e6Datum K').leviAmalgam J →* G₀ := fun J =>
    (φ J).codRestrict G₀ (hφ.apply_mem J) with hφ'def
  have hφ' : IsCompatible (e6Datum K').leviAmalgam φ' := fun i j hij x y hxy =>
    Subtype.ext (hφ.compatible i j hij x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hφ.iSup_range
    rw [← MonoidHom.range_comp]
    rfl
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    by_contra h
    push Not at h
    apply hne
    rw [← hφ.iSup_range, eq_bot_iff]
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    exact mem_bot.2 (congrArg Subtype.val (h J x))
  obtain ⟨ψ, hψ, hsurj, hker, -, hZ⟩ :=
    E6Pilot.exists_surjective_of_isCompatible_e6 K' φ' hφ' hgen' hnt
  exact ⟨ψ, fun J y => congrArg Subtype.val (hψ J y), hsurj, hker, hZ⟩

theorem center_eq_bot_of_isTwoE6GraphFamily {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2) {G₀ : Subgroup G} {t : G} (hne : G₀ ≠ ⊥)
    {φ : ∀ J, (e6Datum K').leviAmalgam J →* G} (hφ : IsTwoE6GraphFamily G₀ t K' φ) :
    center G₀ = ⊥ := by
  obtain ⟨ψ, -, -, -, hZ⟩ := exists_surjective_of_isTwoE6GraphFamily hne hφ
  have hc := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K').1
  rw [hK'] at hc
  have hbot : center (e6Data_valid.minGroup K') = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hc]; rfl)
  rw [hZ, hbot, Subgroup.map_bot]

end CT

section Recognition

variable {G : Type} [Group G]

theorem exists_center_quotient_graph_of_isTwoE6GraphFamily {K' : Type} [Field K'] [Finite K']
    {G₀ : Subgroup G} {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (hne : G₀ ≠ ⊥)
    {φ : ∀ J, (e6Datum K').leviAmalgam J →* G} (hφ : IsTwoE6GraphFamily G₀ t K' φ) :
    ∃ e₆ : G₀ ⧸ center G₀ ≃* adjointGroup Tag.E6 K',
      normalizerQuotMulAut e₆ ⟨t, htN⟩ = exactNormalAut Tag.E6 K' 1 (RingEquiv.refl K') 1 := by
  obtain ⟨ψ, hψφ, hsurj, hker, hZ⟩ := exists_surjective_of_isTwoE6GraphFamily hne hφ
  have hconj : ∀ g, t * (ψ g : G) * t⁻¹ = ψ (sigma K' (RingHom.id K') g) := by
    have h : (MulAut.conj t).toMonoidHom.comp (G₀.subtype.comp ψ) =
        G₀.subtype.comp (ψ.comp (sigma K' (RingHom.id K'))) := by
      refine MonoidHom.eq_of_eqOn_dense (closure_xm_simple_eq_top e6Data_valid K') ?_
      rintro _ ⟨i, c, rfl | rfl⟩
      · have h1 : ((ψ (e6Data_valid.xm K' (Pi.single i 1) c) : G₀) : G) =
            φ ⟨{i}, card_singleton_le_two_E6 i⟩ ⟨_, xm_single_mem_scLevi i c⟩ :=
          hψφ ⟨{i}, card_singleton_le_two_E6 i⟩ ⟨_, xm_single_mem_scLevi i c⟩
        have h2 : ((ψ (e6Data_valid.xm K' (Pi.single (rhoPerm i) 1) c) : G₀) : G) =
            φ ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩
              ⟨_, xm_single_mem_scLevi (rhoPerm i) c⟩ :=
          hψφ ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩
            ⟨_, xm_single_mem_scLevi (rhoPerm i) c⟩
        have h3 := hφ.conj i ⟨_, xm_single_mem_scLevi i c⟩
          ⟨_, xm_single_mem_scLevi (rhoPerm i) c⟩ (sigma_xm_single (RingHom.id K') i c).symm
        change t * ((ψ (e6Data_valid.xm K' (Pi.single i 1) c) : G₀) : G) * t⁻¹ =
          ((ψ (sigma K' (RingHom.id K') (e6Data_valid.xm K' (Pi.single i 1) c)) : G₀) : G)
        rw [sigma_xm_single, RingHom.id_apply, h1, h2]
        exact h3
      · have h1 : ((ψ (e6Data_valid.xm K' (-Pi.single i 1) c) : G₀) : G) =
            φ ⟨{i}, card_singleton_le_two_E6 i⟩ ⟨_, xm_neg_single_mem_scLevi i c⟩ :=
          hψφ ⟨{i}, card_singleton_le_two_E6 i⟩ ⟨_, xm_neg_single_mem_scLevi i c⟩
        have h2 : ((ψ (e6Data_valid.xm K' (-Pi.single (rhoPerm i) 1) c) : G₀) : G) =
            φ ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩
              ⟨_, xm_neg_single_mem_scLevi (rhoPerm i) c⟩ :=
          hψφ ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩
            ⟨_, xm_neg_single_mem_scLevi (rhoPerm i) c⟩
        have h3 := hφ.conj i ⟨_, xm_neg_single_mem_scLevi i c⟩
          ⟨_, xm_neg_single_mem_scLevi (rhoPerm i) c⟩
          (sigma_xm_neg_single (RingHom.id K') i c).symm
        change t * ((ψ (e6Data_valid.xm K' (-Pi.single i 1) c) : G₀) : G) * t⁻¹ =
          ((ψ (sigma K' (RingHom.id K') (e6Data_valid.xm K' (-Pi.single i 1) c)) : G₀) : G)
        rw [sigma_xm_neg_single, RingHom.id_apply, h1, h2]
        exact h3
    intro g
    exact DFunLike.congr_fun h g
  set Ψ : adjointGroup .E6 K' ≃* G₀ ⧸ center G₀ :=
    (E6Pilot.centerQuotientIsogenyEquiv (K := K')).symm.trans
      (E6Pilot.centerQuotientMulEquiv ψ hsurj hker hZ) with hΨ
  have hΨθ : ∀ s, Ψ (e6Isogeny K' s) = QuotientGroup.mk (ψ s) := by
    intro s
    rw [hΨ, MulEquiv.trans_apply, ← E6Pilot.centerQuotientIsogenyEquiv_mk,
      MulEquiv.symm_apply_apply, E6Pilot.centerQuotientMulEquiv_mk]
  refine ⟨Ψ.symm, ?_⟩
  have hact : ∀ s, normalizerQuotMulAut Ψ.symm ⟨t, htN⟩ (e6Isogeny K' s) =
      e6Isogeny K' (sigma K' (RingHom.id K') s) := by
    intro s
    have h1 : e6Isogeny K' s = Ψ.symm (QuotientGroup.mk' (center G₀) (ψ s)) := by
      rw [QuotientGroup.mk'_apply, ← hΨθ, MulEquiv.symm_apply_apply]
    have h2 : G₀.normalizerMonoidHom ⟨t, htN⟩ (ψ s) = ψ (sigma K' (RingHom.id K') s) :=
      Subtype.ext ((Subgroup.normalizerMonoidHom_apply_apply_coe G₀ _ _).trans (hconj s))
    rw [h1, normalizerQuotMulAut_apply, h2, QuotientGroup.mk'_apply, ← hΨθ,
      MulEquiv.symm_apply_apply]
  have hhom : (normalizerQuotMulAut Ψ.symm ⟨t, htN⟩).toMonoidHom =
      (exactNormalAut Tag.E6 K' 1 (RingEquiv.refl K') 1).toMonoidHom := by
    refine CFSG.LieType.Ree.adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, exactNormalAut_one_xElement,
        xElement_eq_e6Isogeny, hact, sigma_xm_single, RingHom.id_apply, ← xElement_eq_e6Isogeny]
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, exactNormalAut_one_yElement,
        yElement_eq_e6Isogeny, hact, sigma_xm_neg_single, RingHom.id_apply,
        ← yElement_eq_e6Isogeny]
  exact MulEquiv.ext fun x => DFunLike.congr_fun hhom x

theorem exists_center_quotient_graph_normalForm_of_isTwoE6GraphFamily {K' : Type} [Field K']
    [Finite K'] {G₀ : Subgroup G} {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (hne : G₀ ≠ ⊥)
    {φ : ∀ J, (e6Datum K').leviAmalgam J →* G} (hφ : IsTwoE6GraphFamily G₀ t K' φ) :
    ∃ e₆ : G₀ ⧸ center G₀ ≃* adjointGroup Tag.E6 K',
      ∃ (χ : MulAut (adjointGroup Tag.E6 K')) (g : adjointGroup Tag.E6 K')
        (a : Fin Tag.E6.rank → K'ˣ) (σ' : K' ≃+* K'),
        χ * normalizerQuotMulAut e₆ ⟨t, htN⟩ * χ⁻¹ =
          MulAut.conj g * exactNormalAut Tag.E6 K' a σ' 1 := by
  obtain ⟨e₆, hact⟩ := exists_center_quotient_graph_of_isTwoE6GraphFamily htN hne hφ
  refine ⟨e₆, 1, 1, 1, RingEquiv.refl K', ?_⟩
  rw [hact, map_one, one_mul, inv_one, mul_one]

end Recognition

end CFSG.SeitzReduction.F4Pilot
