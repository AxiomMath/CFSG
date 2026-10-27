module

public import CFSG.CGT.PushingUpLit.CGT6K1.Defs
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndPass
public import CFSG.RankThree.PartOne.S8.ResidualBound

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.EndQuot

section Abstract

variable {Γ : Type} [Group Γ] [Finite Γ] {Λ Υ T : Subgroup Γ} [Λ.Normal]

theorem cfg_centralizer_layer_eq_bot (h : Cfg Γ Λ Υ T) :
    Subgroup.centralizer (CFSG.layer (Γ ⧸ zc Λ) : Set (Γ ⧸ zc Λ)) = ⊥ := by
  have hperf : Group.IsPerfect ↥Λ := h.qs.1
  rw [h.layer_eq]
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zc Λ) x
  have h1 : g ∈ (Subgroup.centralizer ((Λ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ))
      : Set (Γ ⧸ zc Λ))).comap (QuotientGroup.mk' (zc Λ)) := hx
  rw [centralizer_comap le_rfl hperf] at h1
  have h2 : g ∈ zc Λ := h.centralizer_le h1
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).mpr h2

theorem cfg_exists_outer_of_inf_bot (h : Cfg Γ Λ Υ T)
    (hout : T.map (QuotientGroup.mk' (zc Λ)) ⊓ CFSG.layer (Γ ⧸ zc Λ) = ⊥) :
    ∃ t ∈ T, orderOf t = 2 ∧ t ∉ Λ := by
  have hev : 2 ∣ Nat.card T := even_iff_two_dvd.mp (even_card_of_pgroup h.T2 h.Tne)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 hev
  refine ⟨(t : Γ), t.2, by rw [Subgroup.orderOf_coe]; exact ht, fun htΛ => ?_⟩
  have hmem : QuotientGroup.mk' (zc Λ) (t : Γ) ∈
      T.map (QuotientGroup.mk' (zc Λ)) ⊓ CFSG.layer (Γ ⧸ zc Λ) := by
    refine ⟨Subgroup.mem_map_of_mem _ t.2, ?_⟩
    rw [h.layer_eq]
    exact Subgroup.mem_map_of_mem _ htΛ
  rw [hout, Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_mk] at hmem
  have h2 : (t : Γ) ∈ T ⊓ zc Λ := ⟨t.2, hmem⟩
  rw [inf_zc_eq_bot_of_pgroup h.T2 h.zodd, Subgroup.mem_bot] at h2
  have h3 : t = 1 := Subtype.ext h2
  rw [h3, orderOf_one] at ht
  exact absurd ht (by norm_num)

end Abstract

section Endgame

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem endCfg4_almostSimple (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (h : EndCfg4 G T Y) {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f) :
    AlmostSimple (quotG G Y) f ((Y.subgroupOf G).map (piG G Y))
      ((T.subgroupOf G).map (piG G Y)) := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hcfg := h.cfg hf hY
  obtain ⟨eL⟩ := h.nonempty_equiv_layerQ hf hY
  obtain ⟨eΥ⟩ := hcfg.nonempty_equiv
  obtain ⟨eY⟩ := id hY
  set A : Subgroup (quotG G Y) := (Y.subgroupOf G).map (piG G Y) with hA
  let eA : ↥A ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq f) :=
    eΥ.symm.trans ((Subgroup.subgroupOfEquivOfLe hYG).trans eY)
  have hfld : ∃ (k : Type) (_ : Field k) (_ : Fintype k), Fintype.card k = 2 ^ f ∧
      Nonempty (↥A ≃* Matrix.SpecialLinearGroup (Fin 2) k) := by
    let _ : Fintype (Fq f) := Fintype.ofFinite _
    refine ⟨Fq f, inferInstance, inferInstance, ?_, ⟨eA⟩⟩
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 f (by omega)
  have hsL : IsSimpleGroup (LayerQ G Y) := h.quasi.2
  have hlay : CFSG.layer (quotG G Y) = (lamG G Y).map (piG G Y) := hcfg.layer_eq
  refine
    { kgroup := ?_
      std := ⟨hf, hcfg.standard_map, hcfg.not_normal, hfld⟩
      simple := MulEquiv.isSimpleGroup eL
      cen := cfg_centralizer_layer_eq_bot hcfg
      le := ?_
      sylow := hcfg.isSylow
      ne := ?_ }
  · have hKG : CFSG.SectionRank.IsKGroupCat ↥G :=
      CFSG.RankThree.PartOne.isKGroupCat_of_isKGroup hbridge h.kgroup
    exact hKG.quotient (EndQuot.zc (lamG G Y))
  · rw [hlay]
    exact Subgroup.map_mono hcfg.le
  · intro hbot
    apply hcfg.Tne
    have h1 := hcfg.card_map_T
    have hbot' : Subgroup.map (QuotientGroup.mk' (zc (lamG G Y))) (T.subgroupOf G) = ⊥ := hbot
    rw [hbot', Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.mp h1.symm

theorem endCfg4_outerT_of_inf_bot (h : EndCfg4 G T Y) {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f)
    (hout : (T.subgroupOf G).map (piG G Y) ⊓ CFSG.layer (quotG G Y) = ⊥) : OuterT G T Y := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  obtain ⟨t, ht, hord, hnot⟩ := cfg_exists_outer_of_inf_bot (h.cfg hf hY) hout
  refine ⟨(t : MulAut V), ht, ?_, fun hmem => hnot ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hord
  · rw [normalClosure_subgroupOf_eq hYG]
    exact hmem

end Endgame

end CFSG.CGT.PushingUpLit.CGT6K1
