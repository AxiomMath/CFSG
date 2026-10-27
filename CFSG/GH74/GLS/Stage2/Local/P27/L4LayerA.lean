module

public import CFSG.GH74.GLS.Stage2.Local.P27.LayerAAux
public import CFSG.GH74.GLS.Stage2.Local.P27.DatumPlus
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Std
public import CFSG.GH74.GLS.Stage2.Local.P27.S45L4Cls
public import CFSG.GH74.GLS.Stage2.Local.P27.L4WFacts
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Count
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Us
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Jx

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem datumPlusQL4_of_stage1_l4 {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x₀ : G} (hK : KGH G) (hSch : P34.GHSchreier)
    (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂)
    (hidx : (RC S z).relIndex S ≤ 4) (hx : TwoClassData G z S L₁ L₂ q x₀)
    (hfield : ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂ ∧
      ∃ w ∈ S, orderOf w = 2 ∧ t * w = w * t ∧ w ∉ RC S z ⊔ zpowers t ∧
        GoodInvolution z S L₁ L₂ q w ∧ IsConj z w ∧ IsConj z (t * w) ∧ IsConj x₀ (t * w * z) ∧
        ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y) :
    ∃ x : G, DatumPlusQL4 z x q := by
  obtain ⟨t, htS, htc, hsw, w, hwS, hwo, htw, hwRt, hgood, hwz, htwz, htwx, hcos⟩ := hfield
  obtain ⟨P₁, P₂, a, hPD, hP12, -, -, hcard, hP₁eq, -⟩ :=
    Psp4Stage1.pair_data_of_stage1_t hz hS hP htS htc hsw
  have hSC : S ≤ Cen z := Psp4Stage1.S_le_Cen hS
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo, pow_two] at this
  have hwR : w ∉ RC S z := fun h => hwRt (Subgroup.mem_sup_left h)
  have htR : t ∉ RC S z := by
    rw [← hP12]
    exact hPD.t_not
  have hnorm := RC_conj_mem hSC
  obtain ⟨hidx4, hRinf, hSeq⟩ := S45.l4_S_structure (inf_le_left : RC S z ≤ S) hnorm htS hwS hPD.t_inv hw2 htw
    htR hwRt hidx
  have hidx4' : (RC S z).relIndex S = 4 := hidx4
  obtain ⟨hwnorm, hwdih⟩ := l4_w_facts hz hS hP hP₁eq hcard hgood hwR
  have d : L4.DataL4 S P₁ P₂ z t w a :=
    ⟨hPD.z_mem, hPD.z_ord, hPD.z_cent, hPD.P₁_le, hPD.P₂_le, hPD.P₁_quat, hPD.P₂_quat, hPD.inter,
      hPD.comm, hPD.t_mem, hPD.t_inv, hPD.swap, hwS, hw2, htw, by rw [hP12]; exact hidx4,
      by rw [hP12]; exact hRinf, by rw [hP12]; exact hSeq, hwnorm, hwdih⟩
  have hA := L4.l4_actual d
  obtain ⟨u, huR, hu2, hu1, huz, -, hSt⟩ := L4.l4_exists_std d
  have huRC : u ∈ RC S z := by rw [← hP12]; exact huR
  have hord_u : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  have hxu : IsConj x₀ u := (hx.invol_L u huRC.2 hord_u huz).1
  have hcls := S45.isConj_iff_mem_traces_l4 hz d hP12 hx htc hsw hwz htwz htwx hcos hA.partition
  have hsyl_t : IsSylowOf 2 (S ⊓ centralizer ({t} : Set G)) (centralizer ({t * z, z} : Set G)) :=
    Psp4Stage1.isSylowOf_centralizer_of_card hz hS hP htS htc hsw hP₁eq hcard
      (by rw [hidx4', hA.card_Ct, pow_add]; exact le_of_eq rfl)
  obtain ⟨-, hUsyl⟩ := Psp4Stage1.us_le_ixz_and_sylow hz hS hP htS htc hsw hP₁eq hcard hsyl_t hA.US_le
    hA.US_card
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have htz_comm : t * z = z * t := (Subgroup.mem_centralizer_iff.1 (hSC htS) z (by simp)).symm
  have htz_ord : orderOf (t * z) = 2 :=
    orderOf_mul_of_comm_invol hPD.t_inv hzz htz_comm (p1_t_ne_z hP hsw)
  have hxtz : IsConj x₀ (t * z) := (hx.swap_conseq t htS htc hsw).1
  have hnc_tz : ¬ IsCentralInvolution (t * z) := fun h =>
    hx.x_nonCentral (isCentralInvolution_of_isConj_P27 h hxtz.symm)
  have hIJ : Ixz z (t * z) ≤ Jx (t * z) :=
    Psp4Stage1.ixz_le_jx_of_kgh hK hSch ⟨htz_ord, hnc_tz⟩
      (Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        calc t * z * z = z * t * z := by rw [htz_comm]
          _ = z * (t * z) := by group)) hz.1
  have pic : L4Pic z t u (t * z) S (Psp4.US P₁ t) q (L4.ZcL (P₁ ⊔ P₂) z t w) (L4.XcL (P₁ ⊔ P₂) z t w) :=
    { x_def := rfl
      z_central := hz
      S_syl := isSylowOf_top_of_central hz hS
      z_S := hPD.z_mem
      z_comm := hPD.z_cent
      t_S := htS
      t_inv := hPD.t_inv
      t_ne_z := p1_t_ne_z hP hsw
      t_conj := htc
      u_S := (sup_le hPD.P₁_le hPD.P₂_le) huR
      u_inv := hu2
      u_ne := hu1
      u_ne_z := huz
      classes := fun y hy => (hx.classes y hy).imp id (fun h => hxu.symm.trans h)
      u_nc := fun h => hx.x_nonCentral (isCentralInvolution_of_isConj_P27 h hxu.symm)
      cls_Z := fun y hy h2 h1 => (hcls y hy h2 h1).1
      cls_X := fun y hy h2 h1 =>
        ⟨fun h => ((hcls y hy h2 h1).2).1 (hxu.trans h),
          fun h => hxu.symm.trans (((hcls y hy h2 h1).2).2 h)⟩
      syl_t := hsyl_t
      US_syl := hUsyl
      I_L2 := (ixz_L2 hz hS hP htS htc hsw).2
      q_odd := hP.odd
      q_gt := hP.gt3
      I_le_J := hIJ }
  exact ⟨t * z, datumPlusQL4_of_l4 pic hA hSt⟩

theorem datumPlusQ_of_stage1_l4 {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x₀ : G} (hK : KGH G) (hSch : P34.GHSchreier)
    (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂)
    (hidx : (RC S z).relIndex S ≤ 4) (hx : TwoClassData G z S L₁ L₂ q x₀)
    (hfield : ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂ ∧
      ∃ w ∈ S, orderOf w = 2 ∧ t * w = w * t ∧ w ∉ RC S z ⊔ zpowers t ∧
        GoodInvolution z S L₁ L₂ q w ∧ IsConj z w ∧ IsConj z (t * w) ∧ IsConj x₀ (t * w * z) ∧
        ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y) :
    ∃ x : G, DatumPlusQ z x q :=
  (datumPlusQL4_of_stage1_l4 hK hSch hz hS hP hidx hx hfield).imp fun _ h => h.toDatumPlusQ

theorem datumPlus_of_stage1_l4 {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x₀ : G} (hK : KGH G) (hSch : P34.GHSchreier)
    (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂)
    (hidx : (RC S z).relIndex S ≤ 4) (hx : TwoClassData G z S L₁ L₂ q x₀)
    (hfield : ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂ ∧
      ∃ w ∈ S, orderOf w = 2 ∧ t * w = w * t ∧ w ∉ RC S z ⊔ zpowers t ∧
        GoodInvolution z S L₁ L₂ q w ∧ IsConj z w ∧ IsConj z (t * w) ∧ IsConj x₀ (t * w * z) ∧
        ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y) :
    ∃ x : G, DatumPlus z x :=
  (datumPlusQ_of_stage1_l4 hK hSch hz hS hP hidx hx hfield).imp fun _ h => h.toDatumPlus

theorem datum_of_stage1_l4 {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x₀ : G} (hK : KGH G) (hSch : P34.GHSchreier)
    (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂)
    (hidx : (RC S z).relIndex S ≤ 4) (hx : TwoClassData G z S L₁ L₂ q x₀)
    (hfield : ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂ ∧
      ∃ w ∈ S, orderOf w = 2 ∧ t * w = w * t ∧ w ∉ RC S z ⊔ zpowers t ∧
        GoodInvolution z S L₁ L₂ q w ∧ IsConj z w ∧ IsConj z (t * w) ∧ IsConj x₀ (t * w * z) ∧
        ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y) :
    ∃ x : G, Datum z x :=
  (datumPlus_of_stage1_l4 hK hSch hz hS hP hidx hx hfield).imp fun _ h => h.datum

end CFSG.GH74.GLS.Stage2.Local.P27
