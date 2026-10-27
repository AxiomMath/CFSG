module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.CGT.Foote82.T66.Perm310
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.PartTwo
open Equiv Equiv.Perm

@[expose] noncomputable def pCoreQuotAut (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ CFSG.pCore 2 X) where
  toFun φ := QuotientGroup.congr (CFSG.pCore 2 X) (CFSG.pCore 2 X) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' φ ψ := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

variable {G : Type} [Group G]

@[expose] noncomputable def barConj (K : Subgroup G) :
    ↥(Subgroup.normalizer (K : Set G)) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  (pCoreQuotAut ↥K).comp K.normalizerMonoidHom

theorem barConj_mk (K : Subgroup G) (y : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    barConj K y (QuotientGroup.mk k) =
      QuotientGroup.mk (⟨(y : G) * k * (y : G)⁻¹, (y.2 k).mp k.2⟩ : ↥K) :=
  rfl

theorem coe_mem_pCoreOf_iff {K : Subgroup G} (x : ↥K) :
    (x : G) ∈ pCoreOf 2 K ↔ x ∈ CFSG.pCore 2 ↥K := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

@[expose] def fixBar (K T : Subgroup G) (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) where
  carrier := {x | ∀ t : ↥T, barConj K (Subgroup.inclusion hT t) x = x}
  mul_mem' {a b} ha hb t := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ha t, hb t]
  one_mem' t := map_one _
  inv_mem' {a} ha t := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, ha t]

theorem barConj_mk_eq_iff (K : Subgroup G) (y : ↥(Subgroup.normalizer (K : Set G))) (k : ↥K) :
    barConj K y (QuotientGroup.mk k) = QuotientGroup.mk k ↔
      (y : G) * k * (y : G)⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 K := by
  rw [barConj_mk, QuotientGroup.eq_iff_div_mem, ← coe_mem_pCoreOf_iff, div_eq_mul_inv]
  exact Iff.rfl

theorem centralizerBarIn_eq_fixBar {K T : Subgroup G} (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    centralizerBarIn K T = fixBar K T hT := by
  set S : Set G := {x : G | x ∈ K ∧ ∀ t ∈ T, t * x * t⁻¹ * x⁻¹ ∈ pCoreOf 2 K} with hS
  have hW : Subgroup.closure S ≤
      ((fixBar K T hT).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map K.subtype := by
    rw [Subgroup.closure_le]
    rintro x ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, fun t => ?_, rfl⟩
    exact (barConj_mk_eq_iff K (Subgroup.inclusion hT t) ⟨x, hxK⟩).mpr (hx t t.2)
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk
    obtain ⟨k', hk', hkk'⟩ := hW hk
    have : k' = k := Subtype.ext hkk'
    rw [← this]
    exact hk'
  · intro hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨k, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨k.2, fun t ht => ?_⟩
    exact (barConj_mk_eq_iff K (Subgroup.inclusion hT ⟨t, ht⟩) k).mp (hx ⟨t, ht⟩)

theorem isComponentOf_map_of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {L K : Subgroup X} (h : IsComponentOf L K) :
    IsComponentOf (L.map f) (K.map f) :=
  ⟨Subgroup.map_mono h.1, CFSG.Open.IsSubnormal.map f h.2.1,
    CFSG.Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective f hf).symm h.2.2⟩

section Alt

variable {N : ℕ}

noncomputable def altBarEquiv {K : Subgroup G} {α : ↥K →* alternatingGroup (Fin N)}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin N) :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)

noncomputable def altImage (hN : 7 ≤ N) {K T : Subgroup G}
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin N))
    (hT : T ≤ Subgroup.normalizer (K : Set G)) : ↥T →* Perm (Fin N) :=
  (CFSG.GH74.GLS.IVK.Proofs2.altAutEquiv hN e).toMonoidHom.comp
    ((barConj K).comp (Subgroup.inclusion hT))

theorem map_centralizerBarIn_alt (hN : 7 ≤ N) {K T : Subgroup G}
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin N))
    (hT : T ≤ Subgroup.normalizer (K : Set G)) :
    (centralizerBarIn K T).map (CFSG.GH74.GLS.IVK.Proofs2.psiAlt e) =
      alternatingGroup (Fin N) ⊓
        Subgroup.centralizer ((altImage hN e hT).range : Set (Perm (Fin N))) := by
  open CFSG.GH74.GLS.IVK.Proofs2 in
  rw [centralizerBarIn_eq_fixBar hT]
  ext σ
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨psiAlt_mem e x, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro r ⟨t, rfl⟩
    have h := altAutEquiv_spec hN e (barConj K (Subgroup.inclusion hT t)) x
    rw [hx t] at h
    have h' : psiAlt e x * altImage hN e hT t = altImage hN e hT t * psiAlt e x := by
      conv_lhs => rw [h]
      simp only [altImage, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      group
    exact h'.symm
  · rintro ⟨hσA, hσC⟩
    refine ⟨e.symm ⟨σ, hσA⟩, fun t => ?_, ?_⟩
    · apply psiAlt_injective e
      rw [altAutEquiv_spec hN e]
      have hc := Subgroup.mem_centralizer_iff.mp hσC (altImage hN e hT t) ⟨t, rfl⟩
      have hψ : psiAlt e (e.symm ⟨σ, hσA⟩) = σ := by simp [psiAlt_apply]
      rw [hψ]
      have hc' : altImage hN e hT t * σ = σ * altImage hN e hT t := hc
      simp only [altImage, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hc'
      rw [hc']
      group
    · show ((e (e.symm ⟨σ, hσA⟩) : alternatingGroup (Fin N)) : Perm (Fin N)) = σ
      rw [MulEquiv.apply_symm_apply]

theorem eq_of_isComponentOf_alt (hN : 7 ≤ N) {K T : Subgroup G}
    {A B : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)} (hK : IsAltNaturalType K N) (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hA : IsComponentOf A (centralizerBarIn K T))
    (hB : IsComponentOf B (centralizerBarIn K T)) : A = B := by
  open CFSG.GH74.GLS.IVK.Proofs2 in
  obtain ⟨α, hα, hker, -⟩ := hK
  set e := altBarEquiv hα hker
  have hR : IsPGroup 2 (altImage hN e hTK).range :=
    hT.of_surjective (altImage hN e hTK).rangeRestrict (altImage hN e hTK).rangeRestrict_surjective
  have hX := map_centralizerBarIn_alt hN e hTK
  have hinj := psiAlt_injective e
  have h₁ := (eq_altOn_of_isComponentOf hR hX.ge (hX.le.trans inf_le_right)
    (isComponentOf_map_of_injective _ hinj hA)).2
  have h₂ := (eq_altOn_of_isComponentOf hR hX.ge (hX.le.trans inf_le_right)
    (isComponentOf_map_of_injective _ hinj hB)).2
  exact Subgroup.map_injective hinj (h₁.trans h₂.symm)

end Alt

section OmegaMinus

variable [Finite G]

theorem card_eq_of_isOmegaMinusType_two {K : Subgroup G} (hK : IsOmegaMinusType K 2) :
    Nat.card K = 25920 * Nat.card (CFSG.pCore 2 ↥K) := by
  have h1 := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_quot_of_isOmegaMinusType hK
  have h2 := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_omegaMinusTwo (k := 2) le_rfl
  have h3 : Nat.card (omegaMinusTwo 2) = 25920 := by
    have : (∏ i ∈ Finset.Icc 1 2, ((2 : ℤ) ^ (2 * i) - 1)) = 45 := by decide
    rw [this] at h2
    norm_num at h2
    exact_mod_cast h2
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), h1, h3]

theorem mem_pCore_of_central_of_isAltNaturalType_six {J : Subgroup G}
    (hJ : IsAltNaturalType J 6) {b : ↥J} (hb : ∀ a : ↥J, a * b = b * a) :
    b ∈ CFSG.pCore 2 ↥J := by
  obtain ⟨α, hα, hker, -⟩ := hJ
  rw [← hker, MonoidHom.mem_ker]
  have hc : α b ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := hα g
    rw [← map_mul, ← map_mul, hb a]
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hc
  exact hc

theorem five_dvd_card_of_isAltNaturalType_six {J : Subgroup G} (hJ : IsAltNaturalType J 6) :
    5 ∣ Nat.card J := by
  obtain ⟨α, hα, -, -⟩ := hJ
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hdvd : Nat.card (alternatingGroup (Fin 6)) ∣ Nat.card J := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
    exact dvd_mul_right _ _
  rw [h360] at hdvd
  exact dvd_trans (by norm_num) hdvd

theorem false_of_commute_omegaMinus {K J₁ J₂ : Subgroup G} (hK : IsOmegaMinusType K 2)
    (h₁ : J₁ ≤ K) (h₂ : J₂ ≤ K) (hc : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a)
    (hJ₁ : IsAltNaturalType J₁ 6) (hJ₂ : IsAltNaturalType J₂ 6) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 (five_dvd_card_of_isAltNaturalType_six hJ₁)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 5 (five_dvd_card_of_isAltNaturalType_six hJ₂)
  have haG : orderOf (a : G) = 5 := by rw [Subgroup.orderOf_coe]; exact ha
  have hbG : orderOf (b : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hb
  have hbJ₁ : (b : G) ∉ J₁ := by
    intro hbJ
    have hcen := mem_pCore_of_central_of_isAltNaturalType_six hJ₁ (b := ⟨b, hbJ⟩)
      (fun a' => Subtype.ext (hc (a' : G) a'.2 (b : G) b.2))
    set x : ↥(CFSG.pCore 2 ↥J₁) := ⟨⟨b, hbJ⟩, hcen⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥J₁)) x
    have hbx : orderOf (b : G) = orderOf x :=
      (Subgroup.orderOf_coe (x : ↥J₁)).trans (Subgroup.orderOf_coe x)
    rw [hbG, hk] at hbx
    rcases k with _ | k
    · norm_num at hbx
    · have h2 : (2 : ℕ) ∣ 5 := by
        rw [hbx, pow_succ]
        exact dvd_mul_left _ _
      norm_num at h2
  have hpa : IsPGroup 5 (Subgroup.zpowers (a : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, haG, pow_one])
  have hpb : IsPGroup 5 (Subgroup.zpowers (b : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbG, pow_one])
  have hbC : (b : G) ∈ Subgroup.centralizer (Subgroup.zpowers (a : G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact Commute.zpow_left (hc (a : G) a.2 (b : G) b.2) k
  have hnorm : Subgroup.zpowers (b : G) ≤
      Subgroup.normalizer (Subgroup.zpowers (a : G) : Set G) :=
    (Subgroup.zpowers_le.mpr hbC).trans (Subgroup.centralizer_le_normalizer _)
  have hP : IsPGroup 5 ↥(Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers (a : G)) :=
    IsPGroup.to_sup_of_normal_right' hpb hpa hnorm
  have hPK : Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers (a : G) ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr (h₂ b.2)) (Subgroup.zpowers_le.mpr (h₁ a.2))
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨c, hc2⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  have hdvd : 5 ^ m ∣ 25920 := by
    have h := Subgroup.card_dvd_of_le hPK
    rw [hm, card_eq_of_isOmegaMinusType_two hK, hc2] at h
    exact (Nat.Coprime.pow m c (by norm_num : Nat.Coprime 5 2)).dvd_of_dvd_mul_right h
  have hm1 : m ≤ 1 := by
    by_contra hm1
    have h25 : 25 ∣ 25920 :=
      dvd_trans (show 25 ∣ 5 ^ m from by
        rw [show (25 : ℕ) = 5 ^ 2 by norm_num]
        exact pow_dvd_pow 5 (by omega)) hdvd
    norm_num at h25
  have hcardP : Nat.card ↥(Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers (a : G)) ≤
      Nat.card (Subgroup.zpowers (a : G)) := by
    rw [hm, Nat.card_zpowers, haG]
    calc 5 ^ m ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      _ = 5 := pow_one 5
  have hPa : Subgroup.zpowers (a : G) = Subgroup.zpowers (b : G) ⊔ Subgroup.zpowers (a : G) :=
    Subgroup.eq_of_le_of_card_ge le_sup_right hcardP
  have hb' : (b : G) ∈ Subgroup.zpowers (a : G) := by
    rw [hPa]
    exact (le_sup_left : Subgroup.zpowers (b : G) ≤ _) (Subgroup.mem_zpowers _)
  exact hbJ₁ (Subgroup.zpowers_le.mpr a.2 hb')

end OmegaMinus

end CFSG.CGT.Foote82
