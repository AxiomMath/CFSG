module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResFSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResPerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResHInvariant
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResLayerD
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Alt8Main

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

section Action

variable {G : Type} [Group G]

abbrev DV (D : Subgroup G) : Subgroup (normalizer (D : Set G)) :=
  D.subgroupOf (normalizer (D : Set G))

theorem mem_DV {D : Subgroup G} {n : normalizer (D : Set G)} : n ∈ DV D ↔ (n : G) ∈ D :=
  mem_subgroupOf

@[expose] noncomputable def actD (D : Subgroup G) (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) :
    egQD D →* MulAut (DV D) :=
  QuotientGroup.lift (DV D) MulAut.conjNormal fun v hv => by
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have h1 : v * (u : normalizer (D : Set G)) = u * v :=
      Subtype.ext (hc v.1 (mem_DV.1 hv) u.1.1 (mem_DV.1 u.2))
    calc v * (u : normalizer (D : Set G)) * v⁻¹ = u * v * v⁻¹ := by rw [h1]
      _ = u := by group

theorem actD_mk (D : Subgroup G) (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (n : normalizer (D : Set G)) (v : DV D) :
    ((actD D hc (QuotientGroup.mk n) v : DV D) : normalizer (D : Set G)) = n * v * n⁻¹ := by
  have h1 : actD D hc (QuotientGroup.mk n) = MulAut.conjNormal n := rfl
  rw [h1]
  exact MulAut.conjNormal_apply n v

theorem mem_cQuot_of_actD_eq_one (D : Subgroup G) (hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    {y : egQD D} (hy : actD D hc y = 1) : y ∈ CSide.cQuot D := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨n, ?_, rfl⟩
  show n ∈ (centralizer (D : Set G)).subgroupOf (normalizer (D : Set G))
  rw [mem_subgroupOf, mem_centralizer_iff]
  intro d hd
  have hdN : d ∈ normalizer (D : Set G) := le_normalizer hd
  have h1 := actD_mk D hc n ⟨⟨d, hdN⟩, mem_DV.2 hd⟩
  rw [hy, MulAut.one_apply] at h1
  have h2 : (⟨d, hdN⟩ : normalizer (D : Set G)) * n = n * ⟨d, hdN⟩ := by
    calc (⟨d, hdN⟩ : normalizer (D : Set G)) * n = (n * ⟨d, hdN⟩ * n⁻¹) * n := by rw [← h1]
      _ = n * ⟨d, hdN⟩ := by group
  exact congrArg Subtype.val h2

end Action

section Abstract

open CFSG.EvenSporadicStandard.M24Std.DResH.Fixed

theorem fixed_inf_D2_eq_bot {V Γ : Type} [Group V] [Finite V] [Group Γ] (ρ : Γ →* MulAut V)
    (S1 S2 : Subgroup Γ) (hc2 : Nat.card S2 = 20160) (hf2 : ∀ g ∈ S2, ρ g = 1 → g = 1)
    (horder : ∀ U : Subgroup V, (∀ g ∈ S1, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ g ∈ S2, ∀ u ∈ U, ρ g u ∈ U) →
      Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 256)
    (D1 D2 : Subgroup V) (hD2card : Nat.card D2 = 16) (hsup : D1 ⊔ D2 = ⊤)
    (hfix2 : ∀ g ∈ S2, ∀ u ∈ D1, ρ g u = u) (hfix1 : ∀ g ∈ S1, ∀ u ∈ D2, ρ g u = u) :
    ∀ u ∈ D2, (∀ g ∈ S2, ρ g u = u) → u = 1 := by
  intro u hu hfu
  by_contra hu1
  set Q : Subgroup V := D2 ⊓ fixedSubgroup ρ S2 with hQ
  have hQD : Q ≤ D2 := inf_le_left
  have hcard := horder Q (fun g hg w hw => by rw [hfix1 g hg w hw.1]; exact hw)
    (fun g hg w hw => by rw [hw.2 g hg]; exact hw)
  have hle : Nat.card Q ≤ 16 := hD2card ▸ Subgroup.card_le_of_le hQD
  have hgt : 1 < Nat.card Q := by
    rw [Subgroup.one_lt_card_iff_ne_bot, Ne, eq_bot_iff_forall]
    intro hall
    exact hu1 (hall u ⟨hu, hfu⟩)
  have hQ16 : Nat.card Q = 16 := by omega
  have hQe : Q = D2 := eq_of_le_of_card_ge hQD (by rw [hQ16, hD2card])
  have hD2fix : D2 ≤ fixedSubgroup ρ S2 := hQe ▸ inf_le_right
  have hD1fix : D1 ≤ fixedSubgroup ρ S2 := fun u hu g hg => hfix2 g hg u hu
  have htop : fixedSubgroup ρ S2 = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le hD1fix hD2fix
  exact fixedSubgroup_ne_top ρ hc2 hf2 htop

end Abstract

section Core

variable {G : Type} [Group G] [Finite G] {L B D : Subgroup G} {z : G}

open CFSG.EvenSporadicStandard.M24Std.DResH.Fixed in
theorem dPos_core (hs : LocalSetting G L z) (hB : OctadType L B) (hb : OctadBasics L B)
    (hD : NData B z D) (hA8 : Alt8Data L B)
    (hE : Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃*
      alternatingGroup (Fin 8) × alternatingGroup (Fin 8))) : FFzData D z := by
  have hBL : B ≤ L := hB.1
  have hc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := hD.elem.1
  have hzN : z ∈ normalizer (D : Set G) := LayerD.z_mem_normalizer_D hs hBL hD
  have hY : LayerHyp (DSide.ztD hs hBL hD) (psiD hs hBL hD).range :=
    ⟨orderOf_ztD hs hBL hD, psiD_range_equiv hs hBL hb hD hA8, centralizer_ztD hs hBL hb hD,
      mem_centralizer_iff.2 (by
        rintro _ ⟨y, rfl⟩
        exact psiD_comm hs hBL hD y)⟩
  obtain ⟨S1, S2, ⟨e1⟩, ⟨e2⟩, hcomm, hdisj, hO1, hO2, hz12, hz21, hHS⟩ := hY.exists_factors hE
  have := alt8_simple
  have hS1 : IsSimpleGroup S1 := e1.isSimpleGroup
  have hS2 : IsSimpleGroup S2 := e2.isSimpleGroup
  have hc1 : Nat.card S1 = 20160 := by rw [Nat.card_congr e1.toEquiv, card_alt8]
  have hc2 : Nat.card S2 = 20160 := by rw [Nat.card_congr e2.toEquiv, card_alt8]
  let ρ := actD D hc
  have hV2 : ∀ a : DV D, a * a = 1 := fun a =>
    Subtype.ext (Subtype.ext (hD.elem.2 a.1.1 (mem_DV.1 a.2)))
  have hVc : ∀ a b : DV D, a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (hc a.1.1 (mem_DV.1 a.2) b.1.1 (mem_DV.1 b.2)))
  have hV : Nat.card (DV D) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun d hd => le_normalizer hd)).toEquiv]
    exact hD.card
  have hfaith : ∀ S : Subgroup (egQD D), Disjoint S (fusionOddCore (egQD D)) →
      ∀ g ∈ S, ρ g = 1 → g = 1 := by
    intro S hS g hg hρ1
    exact (disjoint_def.1 hS) hg
      (DSide.cQuot_le_oddCore hs hBL hb hD (mem_cQuot_of_actD_eq_one D hc hρ1))
  have hzz : DSide.ztD hs hBL hD * DSide.ztD hs hBL hD = 1 := hY.mul_self
  have horder : ∀ U : Subgroup (DV D), (∀ g ∈ S1, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ g ∈ S2, ∀ u ∈ U, ρ g u ∈ U) →
      Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 256 := by
    intro U hU1 hU2
    let U' : Subgroup G := (U.map (DV D).subtype).map (normalizer (D : Set G)).subtype
    have hU'D : U' ≤ D := by
      rintro _ ⟨_, ⟨u, -, rfl⟩, rfl⟩
      exact mem_DV.1 u.2
    have hU'inv : ∀ l ∈ egNL L B, ∀ u ∈ U', l * u * l⁻¹ ∈ U' := by
      rintro l hl _ ⟨_, ⟨u0, hu0, rfl⟩, rfl⟩
      have hlN : l ∈ normalizer (D : Set G) := LayerD.egNL_le_normalizer_D hs hBL hD hl
      obtain ⟨a, ha, b, hb', hab⟩ := hHS _ ⟨⟨l, hl⟩, rfl⟩
      have hpsi : psiD hs hBL hD ⟨l, hl⟩ = QuotientGroup.mk ⟨l, hlN⟩ := psiD_apply hs hBL hD ⟨l, hl⟩
      have hact : ρ (a * b) u0 ∈ U := by
        rw [map_mul]
        exact hU1 a ha _ (hU2 b hb' u0 hu0)
      rw [← hab, hpsi] at hact
      refine ⟨_, ⟨ρ (QuotientGroup.mk ⟨l, hlN⟩) u0, hact, rfl⟩, ?_⟩
      have := congrArg Subtype.val (actD_mk D hc ⟨l, hlN⟩ u0)
      simpa using this
    have hcard := DResH.card_invariant_mem hs hBL hb hD U' hU'D hU'inv
    have hUU' : Nat.card U' = Nat.card U := by
      rw [Subgroup.card_map_of_injective (normalizer (D : Set G)).subtype_injective,
        Subgroup.card_map_of_injective (DV D).subtype_injective]
    rwa [hUU'] at hcard
  obtain ⟨D1, D2, hD1c, hD2c, hinf, hsup, hfix2, hfix1, hinv1, hinv2, hzD12, hzD21, hclos⟩ :=
    DResH.exists_fixed_decomposition ρ hVc hV2 hV S1 S2 hS1 hS2 hc1 hc2 hcomm
      (hfaith S1 hO1) (hfaith S2 hO2) (DSide.ztD hs hBL hD) hzz hz12 hz21 horder
  have hsetup : FSetup (DV D) (QuotientGroup.mk' (DV D)) ρ S1 S2 D1 D2 ⟨z, hzN⟩ :=
    { hq := QuotientGroup.mk'_surjective _
      hker := QuotientGroup.ker_mk' _
      hρ := fun n v => actD_mk D hc n v
      hVc := hVc
      e1 := ⟨e1⟩
      e2 := ⟨e2⟩
      hcomm := hcomm
      hdisj := hdisj
      hz := Subtype.ext (Octad.z_mul_self hs)
      hz12 := hz12
      hz21 := hz21
      hD1card := hD1c
      hD2card := hD2c
      hDinf := hinf
      hDsup := hsup
      hfix2 := hfix2
      hfix1 := hfix1
      hinv1 := hinv1
      hinv2 := hinv2
      hzD12 := hzD12
      hzD21 := hzD21
      hclos := hclos
      hD2triv := fixed_inf_D2_eq_bot ρ S1 S2 hc2 (hfaith S2 hO2) horder D1 D2 hD2c hsup hfix2
        hfix1 }
  obtain ⟨F, hFcard, hFcomm, hFint⟩ := hsetup.exists_F
  refine ⟨F.map (normalizer (D : Set G)).subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨f, -, rfl⟩
    exact f.2
  · rw [Subgroup.card_map_of_injective (normalizer (D : Set G)).subtype_injective, hFcard]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hFcomm a ha b hb)
  · rintro _ ⟨a, ha, rfl⟩ ⟨c, hcF, hca⟩
    have h1 : (⟨z, hzN⟩ : normalizer (D : Set G)) * a * ⟨z, hzN⟩⁻¹ = c := Subtype.ext hca.symm
    have := hFint a ha (h1 ▸ hcF)
    rw [this]
    rfl

end Core

theorem residue_dPos :
    Ega81Sit fun _ _ _ _ z _ _ _ D =>
      Nonempty (egaLayer (egQD D ⧸ fusionOddCore (egQD D)) ≃*
        alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) → FFzData D z := by
  intro G _ _ L z hZ hstd hs A B C D hF hE
  exact dPos_core hs hF.pair.octad hF.octad hF.nData (alt8Data_of_type hF.pair.octad) hE

end CFSG.EvenSporadicStandard.M24Std.DRes
