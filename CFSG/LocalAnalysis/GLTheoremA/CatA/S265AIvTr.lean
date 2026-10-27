module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AIvDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
import CFSG.GroupTheory.PLayer.CenterQuotientAction
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AP2
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.HardMathSupport.Solomon.Coordinator
  (commutator_le_left_of_le_normalizer le_normalizer_commutator_right')
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem conj_injective {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g g' h
  have hc : g'⁻¹ * g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun z => by
    have hz := DFunLike.congr_fun h z
    simp only [MulAut.conj_apply] at hz
    calc z * (g'⁻¹ * g) = g'⁻¹ * (g' * z * g'⁻¹) * g := by group
      _ = g'⁻¹ * g * z := by rw [← hz]; group
  exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 (hZ ▸ hc))).symm

private theorem normal_range_conj (G : Type*) [Group G] :
    (MulAut.conj : G →* MulAut G).range.Normal :=
  ⟨fun _ ⟨g, hg⟩ α => ⟨α g, by
    rw [← hg]
    ext s
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]⟩⟩

omit [Finite Ω] in
private theorem conj_eq_of_conj_eq {S : Subgroup Ω} [S.Normal] {e : ↥S} {g : Ω}
    (h : MulAut.conj e = MulAut.conjNormal g) (s : ↥S) :
    g * s * g⁻¹ = ((e * s * e⁻¹ : ↥S) : Ω) := by
  rw [← MulAut.conjNormal_apply, ← h, MulAut.conj_apply]

omit [Finite Ω] in
private theorem centralizer_eq_of_conj_eq {S : Subgroup Ω} [S.Normal] {e : ↥S} {g : Ω}
    (h : MulAut.conj e = MulAut.conjNormal g) :
    Subgroup.centralizer ({e} : Set ↥S) = (cx g).subgroupOf S := by
  ext s
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have h1 := conj_eq_of_conj_eq h s
  constructor
  · intro hse
    rw [show e * s * e⁻¹ = s by rw [← hse, mul_inv_cancel_right]] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  · intro hsg
    rw [show g * (s : Ω) * g⁻¹ = s by rw [← hsg, mul_inv_cancel_right]] at h1
    exact (mul_inv_eq_iff_eq_mul.1 (Subtype.ext h1.symm)).symm

private theorem exists_gen {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}
    (h : QSCfg 3 S B T x D K) : ∃ y ∈ D, y ∉ Subgroup.zpowers x ∧ D = Dgrp y x ∧
      S ⊓ Subgroup.centralizer (D : Set Ω) = S ⊓ cx y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hDB, -, hDcard, hxD, -, -, -⟩ := h.std
  have hx3 : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 x h.xB) h.x1]
  obtain ⟨y, hyD, hyx⟩ := SetLike.not_le_iff_exists.1 fun hle : D ≤ Subgroup.zpowers x => by
    have h1 := Subgroup.card_le_of_le hle
    rw [hDcard, hx3] at h1
    norm_num at h1
  have hy1 : y ≠ 1 := fun h1 => hyx (h1 ▸ (Subgroup.zpowers x).one_mem)
  have hcard : Nat.card ↥(Dgrp y x) = 3 ^ 2 := by
    rw [dgrp_eq]
    exact s265_card_sup Nat.prime_three h.elem (Subgroup.zpowers_le.2 h.xB)
      (by rw [hx3, pow_one]) (hDB hyD) hyx
      (by rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 y (hDB hyD)) hy1])
  have hDeq : D = Dgrp y x := (Subgroup.eq_of_le_of_card_ge ((Subgroup.closure_le D).2
    (Set.insert_subset_iff.2 ⟨hyD, Set.singleton_subset_iff.2 hxD⟩)) (by rw [hcard, hDcard])).symm
  refine ⟨y, hyD, hyx, hDeq, ?_⟩
  rw [hDeq]
  exact inf_cs_dgrp fun s _ => Subgroup.mem_centralizer_singleton_iff.2 (h.xcen s)

omit [Finite Ω] in
private theorem three_dvd_card {K : Subgroup Ω} (hK : catalogIs (PSimple 3 K) S9.isSp6two) :
    3 ∣ Nat.card ↥K := by
  obtain ⟨e⟩ := CatB.bridge_sp6two hK
  have h3 : 3 ∣ Nat.card (PSimple 3 K) := by
    rw [(Nat.card_congr e.toEquiv).trans CatB.U4Sp8.card_sp_three]
    norm_num
  exact h3.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))

private theorem conjNormal_eq_one_iff {S B T : Subgroup Ω} [S.Normal] {x : Ω}
    {D K : Subgroup Ω} (h : QSCfg 3 S B T x D K) {b : Ω} (hb : b ∈ B) :
    (MulAut.conjNormal b : MulAut ↥S) = 1 ↔ b ∈ Subgroup.zpowers x := by
  refine ⟨fun h1 => (h.centB b hb).1 (centMod_of_mem_centralizer
    (Subgroup.mem_centralizer_iff.2 fun s hs => ?_)), fun hbx => ?_⟩
  · have h2 := MulAut.conjNormal_apply b (⟨s, hs⟩ : ↥S)
    rw [h1, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2.symm).symm
  · have hbz : b ∈ Subgroup.center Ω :=
      Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 h.xcen) hbx
    ext s
    rw [MulAut.conjNormal_apply, MulAut.one_apply, (Subgroup.mem_center_iff.1 hbz s).symm,
      mul_inv_cancel_right]

theorem caseIv_false_of_core {Q : TauCeti.CFSGIndex → Prop} (hcore : IvCoreAt Q)
    {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K)
    (hK6 : catalogIs (PSimple 3 K) S9.isSp6two) (hr : Nat.card B = 9 * Nat.card D)
    (hU : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥) (hZK : Subgroup.center (PQuot 3 K) = ⊥)
    (hQ : catalogIs ↥S Q) (hZS : Subgroup.center ↥S = ⊥)
    (hinn : ∀ α : MulAut ↥S, α ^ 3 = 1 → ∃ g : ↥S, α = MulAut.conj g) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := h.cfg.normal
  obtain ⟨hDB, -, hDcard, -, hKL, -, hDK⟩ := h.cfg.std
  obtain ⟨d0, hd0D, hd0x, hDeq, hSd0⟩ := exists_gen h.cfg
  have hN := h.nlAct (three_dvd_card hK6)
  have hKS : K ≤ S := fun k hk => (hN.comp.1 hk).1
  have heng := eq_bot_of_normalized_two_subgroup_of_nlAct hN h.cfg.elem
    (fun g hg => (hDK.le hg).2) hZK (CatB.bridge_sp6two hK6) hr h.cfg.rank
  set ρ : Ω →* MulAut ↥S := MulAut.conjNormal with hρ
  set c : ↥S →* MulAut ↥S := MulAut.conj
  have hc : Function.Injective c := conj_injective hZS
  have hker : ∀ b ∈ B, ρ b = 1 ↔ b ∈ Subgroup.zpowers x := fun b hb =>
    conjNormal_eq_one_iff h.cfg hb
  have hρB : B.map ρ ≤ c.range := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨g, hg⟩ := hinn (ρ b) (by rw [← map_pow, h.cfg.elem.2 b hb, map_one])
    exact ⟨g, hg.symm⟩
  set Bb : Subgroup ↥S := (B.map ρ).comap c
  have hBb27 : Nat.card Bb = 27 := by
    rw [← Subgroup.card_map_of_injective hc, Subgroup.map_comap_eq_self hρB]
    have hk : (ρ.domRestrict B).ker = (Subgroup.zpowers x).subgroupOf B :=
      Subgroup.ext fun b => hker b b.2
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ρ.domRestrict B).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (ρ.domRestrict B)).toEquiv,
      MonoidHom.domRestrict_range, hk,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 h.cfg.xB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (h.cfg.elem.2 x h.cfg.xB) h.cfg.x1, hr, hDcard] at h1
    omega
  obtain ⟨d, hd⟩ := hρB ⟨d0, hDB hd0D, rfl⟩
  have hdBb : d ∈ Bb := show c d ∈ B.map ρ by rw [hd]; exact ⟨d0, hDB hd0D, rfl⟩
  have hd1 : d ≠ 1 := fun h1 => hd0x ((hker d0 (hDB hd0D)).1 (by rw [← hd, h1, map_one]))
  have hCd : Subgroup.centralizer ({d} : Set ↥S) =
      (S ⊓ Subgroup.centralizer (D : Set Ω)).subgroupOf S := by
    rw [centralizer_eq_of_conj_eq hd, hSd0, Subgroup.inf_subgroupOf_left]
  have hK' : GLAPComponent 3 (Subgroup.centralizer ({d} : Set ↥S)) (K.subgroupOf S) :=
    hCd ▸ glaPComponent_subgroupOf Nat.prime_three inf_le_left hN.comp
  have hK'6 : catalogIs (PSimple 3 (K.subgroupOf S)) S9.isSp6two := by
    obtain ⟨e⟩ := nonempty_pQuot_equiv_subgroupOf 3 hKS
    obtain ⟨i, hi, ⟨f⟩⟩ := hK6
    exact ⟨i, hi, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans f⟩⟩
  have hnl : ∀ e ∈ Bb, e ∉ Subgroup.zpowers d →
      GLAPLayer 3 (K.subgroupOf S ⊓ Subgroup.centralizer ({e} : Set ↥S)) = ⊥ := by
    intro e he hed
    obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 he)
    have hbD : b ∉ D := fun hbD => hed (by
      have hD : D ≤ (Subgroup.zpowers (ρ d0)).comap ρ := by
        rw [hDeq]
        refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨Subgroup.mem_comap.2
          (Subgroup.mem_zpowers _), Set.singleton_subset_iff.2 (Subgroup.mem_comap.2 ?_)⟩)
        rw [(hker x h.cfg.xB).2 (Subgroup.mem_zpowers x)]
        exact one_mem _
      have h1 := hD hbD
      rw [Subgroup.mem_comap, hbe, ← hd, ← MonoidHom.map_zpowers] at h1
      exact (Subgroup.mem_map_iff_mem hc).1 h1)
    have hinf : K.subgroupOf S ⊓ (cx b).subgroupOf S = (K ⊓ cx b).subgroupOf S := by
      ext s
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    rw [centralizer_eq_of_conj_eq hbe.symm, hinf]
    have hmap := CFSG.glaPLayer_map_eq_of_injective Nat.prime_three S.subtype
      S.subtype_injective ((K ⊓ cx b).subgroupOf S)
    rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hKS), h.nl b hb hbD] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 hmap
  have hC : ∀ W : Subgroup ↥S, IsPGroup 2 W → W ≤ Subgroup.centralizer ({d} : Set ↥S) →
      Bb ≤ Subgroup.normalizer (W : Set ↥S) → W = ⊥ := by
    intro W hW hWd hBbW
    refine (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1
      (heng _ (hW.map _) ?_ fun b hb => ?_)
    · rintro _ ⟨w, hw, rfl⟩
      have hw' := hWd hw
      rw [hCd, Subgroup.mem_subgroupOf] at hw'
      rw [hKL]
      exact S12.mem_normalizer_glaLayer' (Subgroup.le_normalizer hw')
    · obtain ⟨e, he⟩ := hρB ⟨b, hb, rfl⟩
      have hn := Subgroup.mem_normalizer_iff.1
        (hBbW (show c e ∈ B.map ρ by rw [he]; exact ⟨b, hb, rfl⟩))
      refine Subgroup.mem_normalizer_fintype fun n hn' => ?_
      obtain ⟨w, hw, rfl⟩ := hn'
      exact ⟨e * w * e⁻¹, (hn w).1 hw, (conj_eq_of_conj_eq he w).symm⟩
  have hall := hcore hQ ((h.cfg.elem.map ρ).comap hc) hBb27 hdBb hd1 hK' hK'6 hnl hC
  have hBU : B ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup Ω) : Set Ω) :=
    le_normalizer_commutator_right' T B
  have hU2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) :=
    h.cfg.two.to_le (commutator_le_left_of_le_normalizer h.cfg.bnorm)
  have hρU : (⁅T, B⁆ : Subgroup Ω).map ρ ≤ c.range := by
    rw [Subgroup.map_le_iff_le_comap]
    haveI : (c.range.comap ρ).Normal := (normal_range_conj ↥S).comap ρ
    exact (Subgroup.commutator_mono le_rfl
      (show B ≤ c.range.comap ρ from fun b hb => hρB ⟨b, hb, rfl⟩)).trans
      (Subgroup.commutator_le_right _ _)
  have hW := hall _ ((hU2.map ρ).comap_of_injective c hc) fun e he => by
    obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 he)
    have hn := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer_map ρ ⟨b, hBU hb, rfl⟩)
    refine Subgroup.mem_normalizer_iff.2 fun s => ?_
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, ← hbe]
    exact hn (c s)
  have hUρ : (⁅T, B⁆ : Subgroup Ω).map ρ = ⊥ := by
    rw [← Subgroup.map_comap_eq_self hρU, hW, Subgroup.map_bot]
  refine hU (heng _ hU2 (fun u hu => Subgroup.mem_normalizer_fintype fun k hk => ?_) hBU)
  have hu1 : ρ u = 1 := (Subgroup.map_eq_bot_iff _).1 hUρ hu
  have h1 := MulAut.conjNormal_apply (H := S) u ⟨k, hKS hk⟩
  rw [← hρ, hu1, MulAut.one_apply] at h1
  rw [show u * k * u⁻¹ = k from h1.symm]
  exact hk

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
