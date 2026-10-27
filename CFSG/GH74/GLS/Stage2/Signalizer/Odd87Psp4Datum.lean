module

public import CFSG.GH74.GLS.Stage2.Local.P27.DatumPlus
public import CFSG.GH74.GLS.Stage2.Local.P27.LayerAAux
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Cls
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Count
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Jx
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1U
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Us

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Main

variable {G : Type} [Group G] [Finite G]

@[expose] def DatumPlusPsp4 (z x : G) (q : ℕ) : Prop :=
  ∃ (T D₁ U T₁ : Subgroup G) (n : ℕ) (t' : G),
    Cfg z x T q ∧ Syl z x T D₁ U U n t' ∧ Tr z x T D₁ U U T₁ ∧ Extra z x T D₁ U U t'

omit [Finite G] in
theorem DatumPlusPsp4.toDatumPlusQ {z x : G} {q : ℕ} (h : DatumPlusPsp4 z x q) : DatumPlusQ z x q := by
  obtain ⟨T, D₁, U, T₁, n, t', h1, h2, h3, h4⟩ := h
  exact ⟨T, D₁, U, U, T₁, n, t', h1, h2, h3, h4⟩

theorem datumPlusPsp4_of_ps4 {z t u x : G} {S US : Subgroup G} {a q : ℕ} {Z X : Set G}
    (pic : L4Pic z t u x S US q Z X)
    (A : Ps4Actual S z t a Z X US) (St : Ps4StdC S z u a Z X) : DatumPlusPsp4 z x q := by
  obtain ⟨T, D₁, T₁, M, n, t', T₁s, o, hc⟩ := ps4_out pic A St
  have htr : Tr z x T D₁ US US T₁ :=
    CFSG.GH74.GLS.Stage2.Local.P27Br.tr_of_sep o.cfg o.syl o.I_le_J o.T₁_le o.x_T₁ o.T₁_cyc
      o.T₁_card o.CTz o.D₂_M o.M_T o.D₂_J o.sep o.cos o.Mcomm o.M_D₁ o.M_DD
  have hIC : Ixz z x ≤ centralizer ({x} : Set G) :=
    (pLayerOf_le_P27 2 (centralizer ({x, z} : Set G))).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  have hfus : ∀ s ∈ US, orderOf s = 2 → ∃ c ∈ centralizer ({x} : Set G), c * t' * c⁻¹ = s := by
    intro s hs hs2
    obtain ⟨c, hc, hcs⟩ := fusion_of_I_L2 o.cfg.q_odd o.syl.U_syl o.cfg.I_L2 hs o.syl.t'_U hs2
      o.syl.t'_ord
    exact ⟨c, hIC hc, hcs⟩
  exact ⟨T, D₁, US, T₁, n, t', o.cfg, o.syl, htr,
    Extra.of_parts o.cfg o.syl htr hfus (Or.inr ⟨rfl, o.index_eq⟩)
      ⟨T₁s, hc.le, hc.dih, hc.D₁_le, hc.inf, hc.sup⟩⟩

theorem datumPlusPsp4_of_stage1_psp4 {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x₀ : G} (hK : KGH G) (hSch : P34.GHSchreier)
    (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z)) (h4 : Stage1PSp4 G z S q L₁ L₂)
    (hx : TwoClassData G z S L₁ L₂ q x₀) : ∃ x : G, DatumPlusPsp4 z x q := by
  obtain ⟨t, htS, htc, hsw⟩ := hx.swap_exists
  obtain ⟨P₁, P₂, a, hD, hP12, -, -, hcard, hP₁eq, -⟩ :=
    Psp4Stage1.psp4_data_of_stage1_t hz hS h4 htS htc hsw
  have hSC : S ≤ Cen z := Psp4Stage1.S_le_Cen hS
  obtain ⟨u, hu⟩ := Psp4Stage1.exists_uhyp hD
  have hxu : IsConj x₀ u := Psp4Stage1.isConj_of_uhyp hx hu hP12
  have hA := Psp4.ps4_actual hD
  have hSt := Psp4.ps4_std_compl hD hu
  have hcls := Psp4Stage1.isConj_iff_mem_traces hz hD hP12 hx htc hsw
  have hsyl_t : IsSylowOf 2 (S ⊓ centralizer ({t} : Set G)) (centralizer ({t * z, z} : Set G)) :=
    Psp4Stage1.isSylowOf_centralizer_of_card hz hS h4.pair htS htc hsw hP₁eq hcard
      (by rw [h4.index, hA.card_Ct, pow_add, pow_one])
  obtain ⟨-, hUsyl⟩ := Psp4Stage1.us_le_ixz_and_sylow hz hS h4.pair htS htc hsw hP₁eq hcard hsyl_t
    hA.US_le hA.US_card
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have htz_comm : t * z = z * t := (Subgroup.mem_centralizer_iff.1 (hSC htS) z (by simp)).symm
  have htz_ord : orderOf (t * z) = 2 :=
    orderOf_mul_of_comm_invol hD.t_inv hzz htz_comm (p1_t_ne_z h4.pair hsw)
  have hxtz : IsConj x₀ (t * z) := (hx.swap_conseq t htS htc hsw).1
  have hnc_tz : ¬ IsCentralInvolution (t * z) := fun h =>
    hx.x_nonCentral (isCentralInvolution_of_isConj_P27 h hxtz.symm)
  have hIJ : Ixz z (t * z) ≤ Jx (t * z) :=
    Psp4Stage1.ixz_le_jx_of_kgh hK hSch ⟨htz_ord, hnc_tz⟩
      (Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        calc t * z * z = z * t * z := by rw [htz_comm]
          _ = z * (t * z) := by group)) hz.1
  have pic : L4Pic z t u (t * z) S (Psp4.US P₁ t) q (Psp4.Zc (P₁ ⊔ P₂) z t) (Psp4.Xc (P₁ ⊔ P₂) z t) :=
    { x_def := rfl
      z_central := hz
      S_syl := isSylowOf_top_of_central hz hS
      z_S := hD.z_mem
      z_comm := hD.z_cent
      t_S := htS
      t_inv := hD.t_inv
      t_ne_z := p1_t_ne_z h4.pair hsw
      t_conj := htc
      u_S := (sup_le hD.P₁_le hD.P₂_le) hu.mem
      u_inv := hu.sq
      u_ne := hu.ne_one
      u_ne_z := hu.ne_z
      classes := fun y hy => (hx.classes y hy).imp id (fun h => hxu.symm.trans h)
      u_nc := fun h => hx.x_nonCentral (isCentralInvolution_of_isConj_P27 h hxu.symm)
      cls_Z := fun y hy h2 h1 => (hcls y hy h2 h1).1
      cls_X := fun y hy h2 h1 =>
        ⟨fun h => ((hcls y hy h2 h1).2).1 (hxu.trans h),
          fun h => hxu.symm.trans (((hcls y hy h2 h1).2).2 h)⟩
      syl_t := hsyl_t
      US_syl := hUsyl
      I_L2 := (ixz_L2 hz hS h4.pair htS htc hsw).2
      q_odd := h4.pair.odd
      q_gt := h4.pair.gt3
      I_le_J := hIJ }
  exact ⟨t * z, datumPlusPsp4_of_ps4 pic hA hSt⟩

theorem datumPlusPsp4_of_ctx {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.psp4 S) (hSch : P34.GHSchreier) :
    ∃ (x : G) (q : ℕ), DatumPlusPsp4 z x q := by
  have hd := hctx.data
  cases hd with
  | psp4 h =>
    obtain ⟨q, L₁, L₂, h4⟩ := h
    obtain ⟨x₀, hx⟩ := h4.two
    obtain ⟨x, hx'⟩ := datumPlusPsp4_of_stage1_psp4 hctx.std.kgh hSch hctx.central hctx.sylow h4 hx
    exact ⟨x, q, hx'⟩

end CFSG.GH74.GLS.Stage2.Local.P27
