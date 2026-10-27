module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainOdd
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTField

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.LieType.CurtisTits (IsCompatible)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rhoPerm sigma_xm_single sigma_xm_neg_single)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)

local instance f4PilotCTGraphE6NeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

theorem card_singleton_le_two_E6 (i : Fin (Tag.rank .E6)) :
    ({i} : Finset (Fin (Tag.rank .E6))).card ≤ 2 := by
  simp

section Generators


theorem xm_single_mem_scLevi {K' : Type} [Field K'] (i : Fin (Tag.rank .E6)) (c : K') :
    e6Data_valid.xm K' (Pi.single i 1) c ∈
      CFSG.LieType.CurtisTits.levi (e6Datum K').rootGroup {i} := by
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  exact mem_sup_left (e6Data_valid.xm_mem_rootGroup K' _ c)

theorem xm_neg_single_mem_scLevi {K' : Type} [Field K'] (i : Fin (Tag.rank .E6)) (c : K') :
    e6Data_valid.xm K' (-Pi.single i 1) c ∈
      CFSG.LieType.CurtisTits.levi (e6Datum K').rootGroup {i} := by
  rw [CFSG.LieType.CurtisTits.levi_singleton]
  exact mem_sup_right (e6Data_valid.xm_mem_rootGroup K' _ c)

end Generators

section Family


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

structure IsE6GraphRowFamily (e : L ≃* adjointGroup .F4 K) (t : G) (K' : Type) [Field K']
    (φ : ∀ J, (e6Datum K').leviAmalgam J →* G) : Prop where
  compatible : IsCompatible (e6Datum K').leviAmalgam φ
  iSup_range : ⨆ J, (φ J).range = pieceSpan e
  conj : ∀ (i : Fin (Tag.rank .E6))
    (x : CFSG.LieType.CurtisTits.levi (e6Datum K').rootGroup {i})
    (y : CFSG.LieType.CurtisTits.levi (e6Datum K').rootGroup {rhoPerm i}),
    (y : e6Data_valid.minGroup K') = sigma K' (RingHom.id K') x →
      t * φ ⟨{i}, card_singleton_le_two_E6 i⟩ x * t⁻¹ =
        φ ⟨{rhoPerm i}, card_singleton_le_two_E6 (rhoPerm i)⟩ y

end Family


section Recognition


variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem xElement_eq_e6Isogeny {K' : Type} [Field K'] [Finite K'] (i : Fin (Tag.rank .E6))
    (c : K') : xElement i c = e6Isogeny K' (e6Data_valid.xm K' (Pi.single i 1) c) := by
  rw [e6Isogeny_xm_single, eltElement_simpleRoot_E6]

theorem yElement_eq_e6Isogeny {K' : Type} [Field K'] [Finite K'] (i : Fin (Tag.rank .E6))
    (c : K') : yElement i c = e6Isogeny K' (e6Data_valid.xm K' (-Pi.single i 1) c) := by
  rw [e6Isogeny_xm_neg_single, eltElement_neg_simpleRoot_E6]

theorem exactNormalAut_one_xElement {K' : Type} [Field K'] (i : Fin (Tag.rank .E6)) (c : K') :
    exactNormalAut Tag.E6 K' 1 (RingEquiv.refl K') 1 (xElement i c) = xElement (rhoPerm i) c := by
  have h := exactNormalAut_adjX (τ := Tag.E6) (K := K') 1 (RingEquiv.refl K') 1 i c
  simp only [Pi.one_apply, Units.val_one, one_mul, RingEquiv.refl_apply] at h
  exact h

theorem exactNormalAut_one_yElement {K' : Type} [Field K'] (i : Fin (Tag.rank .E6)) (c : K') :
    exactNormalAut Tag.E6 K' 1 (RingEquiv.refl K') 1 (yElement i c) = yElement (rhoPerm i) c := by
  have h := exactNormalAut_adjY (τ := Tag.E6) (K := K') 1 (RingEquiv.refl K') 1 i c
  simp only [Pi.one_apply, inv_one, Units.val_one, one_mul, RingEquiv.refl_apply] at h
  exact h


theorem exists_center_quotient_graph_of_isE6GraphRowFamily {K' : Type} [Field K'] [Finite K']
    {e : L ≃* adjointGroup .F4 K} {t : G} (htL : t ∈ centralizer (L : Set G))
    (hne : pieceSpan e ≠ ⊥) {φ : ∀ J, (e6Datum K').leviAmalgam J →* G}
    (hφ : IsE6GraphRowFamily e t K' φ) :
    ∃ (e₆ : pieceSpan e ⧸ center (pieceSpan e) ≃* adjointGroup Tag.E6 K')
      (htN : t ∈ normalizer (pieceSpan e : Set G)),
      normalizerQuotMulAut e₆ ⟨t, htN⟩ = exactNormalAut Tag.E6 K' 1 (RingEquiv.refl K') 1 := by
  set G₀ := pieceSpan e with hG₀
  have hle : ∀ J y, φ J y ∈ G₀ := fun J y => by
    rw [hG₀, ← hφ.iSup_range]
    exact le_iSup (fun J => (φ J).range) J ⟨y, rfl⟩
  set φ' : ∀ J, (e6Datum K').leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J)
    with hφ'def
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
    rw [hG₀, ← hφ.iSup_range, eq_bot_iff]
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    exact mem_bot.2 (congrArg Subtype.val (h J x))
  obtain ⟨ψ, hψ, hsurj, hker, -, hZ⟩ :=
    E6Pilot.exists_surjective_of_isCompatible_e6 K' φ' hφ' hgen' hnt
  have hψφ : ∀ J (y : (e6Datum K').leviAmalgam J), ((ψ y : G₀) : G) = φ J y :=
    fun J y => congrArg Subtype.val (hψ J y)
  have htN : t ∈ normalizer (G₀ : Set G) :=
    mem_normalizer_iSup fun J => le_normalizer_pieceCore e htL J.1
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
  refine ⟨Ψ.symm, htN, ?_⟩
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

end Recognition

section Input


@[expose] def E6GraphRowFamilyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .F4 K) (t : G) (f : ℕ), F4Work L K t f → 2 ≤ f → E6RowKinds e t f →
    ∃ φ : ∀ J, (e6Datum K).leviAmalgam J →* G, IsE6GraphRowFamily e t K φ

end Input

section Reduction


theorem pieceSpan_ne_bot {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
    (hq : 4 ≤ Nat.card K) (e : L ≃* adjointGroup .F4 K) : pieceSpan e ≠ ⊥ := by
  intro hbot
  have := CFSG.LieType.Chevalley.nontrivial_adjointGroup_F4 (K := K)
  obtain ⟨x, hx⟩ := exists_ne (1 : adjointGroup Tag.F4 K)
  apply hx
  have h1 : ((e.symm x : L) : G) ∈ pieceSpan e := le_pieceSpan hq e (e.symm x).2
  rw [hbot, mem_bot] at h1
  have h2 : e.symm x = 1 := Subtype.ext h1
  rw [← e.apply_symm_apply x, h2, map_one]

theorem e6RowCTQuotInput_of_familyInput (h : E6GraphRowFamilyInput) : E6RowCTQuotInput := by
  intro G _ _ L K _ _ _ e t f hw hf hk
  obtain ⟨φ, hφ⟩ := h G L K e t f hw hf hk
  have h4 : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨e₆, htN, hact⟩ := exists_center_quotient_graph_of_isE6GraphRowFamily
    hw.mem_centralizer (pieceSpan_ne_bot h4 e) hφ
  refine ⟨K, inferInstance, inferInstance, hw.card_eq, e₆, htN, 1, 1, 1, RingEquiv.refl K, ?_⟩
  rw [hact, map_one, one_mul, inv_one, mul_one]

end Reduction

end CFSG.SeitzReduction.F4Pilot
