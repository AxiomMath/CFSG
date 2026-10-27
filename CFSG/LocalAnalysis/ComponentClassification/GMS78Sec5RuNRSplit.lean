module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRAct
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.GMS78RuS
open CFSG.ComponentClassification.GMS78.RuSimCode CFSG.ComponentClassification.GMS78.RuSModel

section Cert

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

structure ConjData (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (c : MulAut RuR) : Prop where
  sq : c * c = 1
  fix_m : ∀ x, (c x).m = x.m
  fix_A : ∀ t, c ⟨0, t⟩ = ⟨0, t⟩
  mem : ∀ k : nK, c * (k : MulAut RuR) * c ∈ (actN hM hS).range
  fix_D : ∀ k : nK, ∀ j : Fin 8, (∀ x, (k : MulAut RuR) x = nAut (dCode j) x) →
    c * (k : MulAut RuR) * c = k

@[expose] noncomputable def kConj (c : MulAut RuR) : Subgroup (MulAut RuR) :=
  nK.map (MulAut.conj c).toMonoidHom

theorem mem_kConj_iff {c : MulAut RuR} (hc2 : c * c = 1) (f : MulAut RuR) :
    f ∈ kConj c ↔ ∃ k : nK, c * (k : MulAut RuR) * c = f := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, by simp [MulAut.conj_apply, hci]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, by simp [MulAut.conj_apply, hci]⟩

@[expose] noncomputable def kTil (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (c : MulAut RuR) : Subgroup G :=
  ((kConj c).comap (actN hM hS)).map (normalizer (R : Set G)).subtype

theorem mem_kTil_iff (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (c : MulAut RuR) (g : G) :
    g ∈ kTil hM hS c ↔ ∃ hg : g ∈ normalizer (R : Set G), actN hM hS ⟨g, hg⟩ ∈ kConj c := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem kTil_le_normalizer (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (c : MulAut RuR) :
    kTil hM hS c ≤ normalizer (R : Set G) := by
  rintro _ ⟨n, -, rfl⟩
  exact n.2

theorem A_le_R (hM : Sec3.SzR.MaskCoords L T R μ ν) : gmsA L T ≤ R := hM.le

theorem A_le_kTil (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (c : MulAut RuR) : gmsA L T ≤ kTil hM hS c := by
  intro a ha
  have haN : a ∈ normalizer (R : Set G) := le_normalizer (A_le_R hM ha)
  refine (mem_kTil_iff hM hS c a).mpr ⟨haN, ?_⟩
  rw [actN_eq_one_of_mem_A hM hS ⟨a, haN⟩ ha]
  exact one_mem _

theorem dSub_le_kTil (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) {c : MulAut RuR} (hc : ConjData hM hS c) :
    dSub hS ≤ kTil hM hS c := by
  rintro _ ⟨d, rfl⟩
  refine (mem_kTil_iff hM hS c _).mpr ⟨hS.mem _, (mem_kConj_iff hc.sq _).mpr ?_⟩
  have hdm : dCode d ∈ glList := by revert d; decide
  let k : nK := ⟨nAutE hdm, dCode d, hdm, fun _ => rfl⟩
  refine ⟨k, (hc.fix_D k d fun _ => rfl).trans ?_⟩
  exact MulEquiv.ext fun x => (actN_D hM hS d x).symm

theorem eq_one_of_mem_kConj (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) {c : MulAut RuR} (hc : ConjData hM hS c)
    {f : MulAut RuR} (hf : f ∈ kConj c) (hA : ∀ t, f ⟨0, t⟩ = ⟨0, t⟩) : f = 1 := by
  obtain ⟨k, rfl⟩ := (mem_kConj_iff hc.sq f).mp hf
  obtain ⟨r, -, hk⟩ := k.2
  have hrt : ∀ t, linApply r t = t := by
    intro t
    have h := hA t
    rw [MulAut.mul_apply, MulAut.mul_apply, hc.fix_A, hk, nAut_A1, hc.fix_A] at h
    exact congrArg RuR.t h
  have hr1 := linId_of_linApply hrt
  have hk1 : (k : MulAut RuR) = 1 := MulEquiv.ext fun x => by
    rw [hk, hr1, nAut_linId]
    rfl
  rw [hk1, mul_one, hc.sq]

theorem kTil_inf_R (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R) {c : MulAut RuR}
    (hc : ConjData hM hS c) : kTil hM hS c ⊓ R = gmsA L T := by
  refine le_antisymm (fun g hg => ?_) (le_inf (A_le_kTil hM hS c) (A_le_R hM))
  obtain ⟨⟨hgN, hgK⟩, hgR⟩ := And.intro ((mem_kTil_iff hM hS c g).mp hg.1) hg.2
  have hfix : ∀ t, actN hM hS ⟨g, hgN⟩ ⟨0, t⟩ = ⟨0, t⟩ := by
    intro t
    apply thetaR_injective hS
    rw [actN_apply]
    change g * thetaR hS ⟨0, t⟩ * g⁻¹ = thetaR hS ⟨0, t⟩
    rw [hM.central g hgR _ (thetaR_A1 hS t).1, mul_inv_cancel_right]
  have h1 := eq_one_of_mem_kConj hM hS hc hgK hfix
  exact mem_A_of_actN_eq_one hM hS hNC ⟨g, hgN⟩ h1

theorem kTil_sup_R (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R) {c : MulAut RuR}
    (hc : ConjData hM hS c) : kTil hM hS c ⊔ R = normalizer (R : Set G) := by
  refine le_antisymm (sup_le (kTil_le_normalizer hM hS c) le_normalizer) fun g hgN => ?_
  obtain ⟨r, hr, -, -, hrA⟩ := actN_code hM hS ⟨g, hgN⟩
  let k : nK := ⟨nAutE hr, r, hr, fun _ => rfl⟩
  obtain ⟨n', hn'⟩ := hc.mem k
  have hn'K : (n' : G) ∈ kTil hM hS c :=
    (mem_kTil_iff hM hS c _).mpr ⟨n'.2, hn' ▸ (mem_kConj_iff hc.sq _).mpr ⟨k, rfl⟩⟩
  have hkA : ∀ t, (c * (k : MulAut RuR) * c) ⟨0, t⟩ = ⟨0, linApply r t⟩ := by
    intro t
    rw [MulAut.mul_apply, MulAut.mul_apply, hc.fix_A]
    change c (nAut r ⟨0, t⟩) = _
    rw [nAut_A1, hc.fix_A]
  have hfix : ∀ t, actN hM hS (n'⁻¹ * ⟨g, hgN⟩) ⟨0, t⟩ = ⟨0, t⟩ := by
    intro t
    rw [map_mul, map_inv, MulAut.mul_apply, hrA, hn', MulAut.inv_apply, MulEquiv.symm_apply_eq,
      hkA]
  have hR := mem_R_of_actN hM hS hNC _ hfix
  have e : g = (n' : G) * (((n'⁻¹ * ⟨g, hgN⟩ : ↥(normalizer (R : Set G))) : G)) := by
    simp
  rw [e]
  exact mul_mem_sup hn'K hR

theorem normalizer_R_le (hM : Sec3.SzR.MaskCoords L T R μ ν) :
    normalizer (R : Set G) ≤ normalizer (gmsA L T : Set G) := by
  intro g hg
  refine mem_normalizer_iff.mpr fun b => ⟨fun hb => hM.normA g hg b hb, fun hb => ?_⟩
  have := hM.normA g⁻¹ (inv_mem hg) _ hb
  simpa [mul_assoc] using this

theorem map_thetaR_A1R (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) : A1R.map (thetaR hS) = gmsA L T := by
  refine le_antisymm ?_ fun a ha => ?_
  · rintro _ ⟨y, hy, rfl⟩
    have hy0 : y = ⟨0, y.t⟩ := RuR.ext hy rfl
    rw [hy0]
    exact (thetaR_A1 hS y.t).1
  · obtain ⟨y, hy⟩ : a ∈ (thetaR hS).range := by
      rw [range_thetaR hM hS]
      exact A_le_R hM ha
    refine ⟨y, ?_, hy⟩
    have h := (hM.ker a (A_le_R hM ha)).mpr ha
    rw [← hy, μ_thetaR hS y] at h
    exact Fin.ext h

theorem card_A (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ) :
    Nat.card (gmsA L T) = 8 := by
  rw [← map_thetaR_A1R hM hS, Subgroup.card_map_of_injective (thetaR_injective hS), card_A1R]

theorem card_normalizer (hidx : R.relIndex (normalizer (R : Set G)) = 168)
    (hcardR : Nat.card R = 2048) : Nat.card (normalizer (R : Set G)) = 344064 := by
  have h := Subgroup.relIndex_mul_card (H := R) (K := normalizer (R : Set G))
  rw [inf_of_le_left le_normalizer, hidx, hcardR] at h
  omega

theorem card_kTil (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) (hcardR : Nat.card R = 2048)
    {c : MulAut RuR} (hc : ConjData hM hS c) : Nat.card (kTil hM hS c) = 1344 := by
  have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := R) (B := kTil hM hS c) (kTil_le_normalizer hM hS c)
  rw [sup_comm, kTil_sup_R hM hS hNC hc, inf_comm, kTil_inf_R hM hS hNC hc,
    card_normalizer hidx hcardR, card_A hM hS, hcardR] at h
  omega

theorem exists_compl [Finite G] (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) (hcardR : Nat.card R = 2048)
    {c : MulAut RuR} (hc : ConjData hM hS c) :
    ∃ K₀ : Subgroup G, K₀ ≤ kTil hM hS c ∧ K₀ ⊓ gmsA L T = ⊥ ∧ Nat.card K₀ = 168 := by
  classical
  set Kt := kTil hM hS c with hKt
  have hAK : gmsA L T ≤ Kt := A_le_kTil hM hS c
  have hDK : dSub hS ≤ Kt := dSub_le_kTil hM hS hc
  set VA : Subgroup Kt := (gmsA L T).subgroupOf Kt with hVA
  have hVAn : VA.Normal := ⟨fun a ha g => by
    rw [mem_subgroupOf] at ha ⊢
    exact hM.normA g (kTil_le_normalizer hM hS c g.2) a ha⟩
  have hVAc : IsMulCommutative VA := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hM.central _ (A_le_R hM (mem_subgroupOf.mp a.2)) _ (mem_subgroupOf.mp b.2)))⟩⟩
  have hcardVA : Nat.card VA = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv, card_A hM hS]
  have hVAp : IsPGroup 2 VA := IsPGroup.of_card (n := 3) (by rw [hcardVA]; norm_num)
  have hinfAD : gmsA L T ⊓ dSub hS = ⊥ := eq_bot_iff.mpr fun g hg => by
    have h : g ∈ dSub hS ⊓ R := ⟨hg.2, A_le_R hM hg.1⟩
    rwa [dSub_inf_R hM hS] at h
  have hcardDA : Nat.card (gmsA L T ⊔ dSub hS : Subgroup G) = 64 := by
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := gmsA L T) (B := dSub hS) ((dSub_le_normalizer hS).trans (normalizer_R_le hM))
    rw [hinfAD, Subgroup.card_bot, card_A hM hS, card_dSub hS] at h
    omega
  set Pt : Subgroup Kt := (gmsA L T ⊔ dSub hS).subgroupOf Kt with hPt
  have hcardPt : Nat.card Pt = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (sup_le hAK hDK)).toEquiv, hcardDA]
  have hPtp : IsPGroup 2 Pt := IsPGroup.of_card (n := 6) (by rw [hcardPt]; norm_num)
  have hcardKt : Nat.card Kt = 1344 := card_kTil hM hS hNC hidx hcardR hc
  have hidxPt : Pt.index = 21 := by
    have h := Pt.card_mul_index
    rw [hcardPt, hcardKt] at h
    omega
  have hndvd : ¬ 2 ∣ Pt.index := by
    rw [hidxPt]
    decide
  set P : Sylow 2 Kt := hPtp.toSylow hndvd with hP
  set Dt : Subgroup Kt := (dSub hS).subgroupOf Kt with hDt
  have hPcoe : (P : Subgroup Kt) = Pt := IsPGroup.toSylow_coe hPtp hndvd
  have hDtP : Dt ≤ P := by
    rw [hPcoe]
    intro x hx
    exact mem_subgroupOf.mpr (le_sup_right (a := gmsA L T) (mem_subgroupOf.mp hx))
  have hinfD : VA ⊓ Dt = ⊥ := eq_bot_iff.mpr fun x hx => by
    have h : (x : G) ∈ gmsA L T ⊓ dSub hS := ⟨mem_subgroupOf.mp hx.1, mem_subgroupOf.mp hx.2⟩
    rw [hinfAD, mem_bot] at h
    rw [mem_bot]
    exact Subtype.ext h
  have hsupD : VA ⊔ Dt = P := by
    rw [hPcoe, hPt, subgroupOf_sup hAK hDK]
  obtain ⟨K₂, hK₂i, hK₂s⟩ := (CFSG.Quasithin.gaschutz hVAp P).mpr ⟨Dt, hDtP, hinfD, hsupD⟩
  refine ⟨K₂.map Kt.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · refine eq_bot_iff.mpr ?_
    rintro _ ⟨⟨k, hk, rfl⟩, hgA⟩
    have h : k ∈ VA ⊓ K₂ := ⟨mem_subgroupOf.mpr hgA, hk⟩
    rw [hK₂i, mem_bot] at h
    rw [mem_bot, h]
    rfl
  · rw [Subgroup.card_map_of_injective Kt.subtype_injective]
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_normal K₂ VA
    rw [sup_comm, hK₂s, inf_comm, hK₂i, Subgroup.card_bot, Subgroup.card_top, hcardKt,
      hcardVA] at h
    omega

end Cert

end CFSG.ComponentClassification.GMS78.RuN
