module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Small
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Long
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalOut
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviCent
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.Sporadic.Schreier.TitsOther

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

theorem card_g2Q
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) {A R T : Subgroup G} {g : G}
    (hc : Sec3 A R T g) {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) (hZ1 : center ↥A = ⊥) :
    Nat.card (g2Q ψ T) = Nat.card K - 1 := by
  classical
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hAK : A ⊓ centralizer (A : Set G) = ⊥ := by
    rw [← card_eq_one, RankTwoL3Even.card_inf_centralizer_eq, hZ1, card_bot]
  have htinj : Function.Injective (LieType.Chevalley.torusEltHom .G2 K g2ir) := by
    intro t t' h
    have h1 := torus_r_v (K := K) t 1
    have h2 := torus_r_v (K := K) t' 1
    have h3 : torusElt .G2 K g2ir t = torusElt .G2 K g2ir t' := h
    rw [h3, h2, mul_one, mul_one] at h1
    exact Units.ext (pinnedX_injective .G2 K g2v h1).symm
  have hcardH : Nat.card (g2TorusR K) = Nat.card K - 1 := by
    rw [g2TorusR, ← SetLike.coe_sort_coe, MonoidHom.coe_range,
      Nat.card_range_of_injective htinj, Nat.card_units]
  have hHC : ∀ h ∈ g2TorusR K, h ∈ adjointGroup .G2 K := by
    rintro _ ⟨t, rfl⟩
    exact torusElt_mem_adjointGroup g2ir t
  have key : ∀ w : g2Q ψ T, ∃ h : g2TorusR K,
      ψ ⟨w, le_normalizer (g2Q_le w.2)⟩ = MulAut.conj ⟨(h : ModGL .G2 K), hHC _ h.2⟩ := by
    intro w
    obtain ⟨y, hy, hyψ⟩ := mem_g2Inn.1 (psi_mem_of_mem_g2Q w.2)
    exact ⟨⟨y, hy⟩, hyψ.symm⟩
  choose F hF using key
  refine (Nat.card_eq_of_bijective F ⟨fun w w' hww => ?_, fun h => ?_⟩).trans hcardH
  · have h1 : ψ ⟨w, le_normalizer (g2Q_le w.2)⟩ = ψ ⟨w', le_normalizer (g2Q_le w'.2)⟩ := by
      rw [hF, hF, hww]
    have hwA := g2Q_le w.2
    have hw'A := g2Q_le w'.2
    have hN := mul_mem (inv_mem (le_normalizer hwA)) (le_normalizer hw'A)
    have h2 : (w : G)⁻¹ * w' ∈ A ⊓ centralizer (A : Set G) := by
      refine mem_inf.2 ⟨mul_mem (inv_mem hwA) hw'A, (hψ.eq_one_iff ⟨_, hN⟩).1 ?_⟩
      rw [psi_mul (inv_mem (le_normalizer hwA)) (le_normalizer hw'A),
        psi_inv (le_normalizer hwA), h1, inv_mul_cancel]
    rw [hAK, mem_bot, inv_mul_eq_one] at h2
    exact Subtype.ext h2
  · obtain ⟨w, hw, hwψ⟩ := exists_mem_g2Q h4 h32 h184 hK4 hc hψ hT
      (y := ⟨(h : ModGL .G2 K), hHC _ h.2⟩) h.2
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    have h1 := (hF ⟨w, hw⟩).symm.trans hwψ
    exact congrArg (fun y : ↥(adjointGroup .G2 K) => (y : ModGL .G2 K)) (hinj h1)

omit [Finite G] in
theorem psi_injOn_of_center_eq_bot {K : Type} [Field K] {A : Subgroup G}
    {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hZ1 : center ↥A = ⊥) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (h : ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩) : a = b := by
  have hAK : A ⊓ centralizer (A : Set G) = ⊥ := by
    rw [← card_eq_one, RankTwoL3Even.card_inf_centralizer_eq, hZ1, card_bot]
  have hN := mul_mem (inv_mem (le_normalizer ha)) (le_normalizer hb)
  have h2 : a⁻¹ * b ∈ A ⊓ centralizer (A : Set G) := by
    refine mem_inf.2 ⟨mul_mem (inv_mem ha) hb, (hψ.eq_one_iff ⟨_, hN⟩).1 ?_⟩
    rw [psi_mul (inv_mem (le_normalizer ha)) (le_normalizer hb), psi_inv (le_normalizer ha), h,
      inv_mul_cancel]
  rw [hAK, mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem center_layerCentralizer_g2Q
    (h4 : Asc75Theorem4) (h32 : Lemma32)
    (h184 : G2Centr184) (h187 : G2Levi187) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 2) {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
    {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) (hZ1 : center ↥A = ⊥) :
    (center ↥(layerCentralizer A (g2Q ψ T))).map (layerCentralizer A (g2Q ψ T)).subtype =
      g2Q ψ T := by
  classical
  have hZC := LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K)
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hψinj : ∀ {a b : G} (ha : a ∈ A) (hb : b ∈ A),
      ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩ → a = b :=
    fun ha hb h => psi_injOn_of_center_eq_bot hψ hZ1 ha hb h
  obtain ⟨L, hLC, -, hLperf, hLH, hCdec, -, hLt, -, -, hZL⟩ := h187 K 2 hK le_rfl
  have hZL' := hZL rfl
  have hLq : CFSG.Open.IsQuasisimple ↥L := by
    simp only [ite_true] at hLt
    exact open_isQuasisimple_of_psl hLperf hLt
  have hlay := g2_layerCentralizer_eq h4 h32 h184 hK4 hc hψ hT hLC hLperf hLH hCdec hLq
  have hS := g2Inn_le_range (K := K) L
  have hSperf := commutator_g2Inn hLC hLperf
  have hHr : ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2TorusR K ↔
      (y : ModGL .G2 K) ∈ L ∧ ∀ l ∈ L, (y : ModGL .G2 K) * l = l * y := by
    intro y
    rw [← hZL']
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [← hzy]
      exact ⟨z.2, fun l hl => congrArg Subtype.val (mem_center_iff.1 hz ⟨l, hl⟩).symm⟩
    · rintro ⟨hyL, hy⟩
      exact ⟨⟨_, hyL⟩, mem_center_iff.2 fun l => Subtype.ext (hy l l.2).symm, rfl⟩
  rw [hlay]
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    change (z : G) ∈ g2Q ψ T
    have hzA : (z : G) ∈ A := leviLift_le z.2
    obtain ⟨y, hy⟩ := hψ.map_mem (z : G) hzA
    have hyL : (y : ModGL .G2 K) ∈ L := by
      have h1 := psi_mem_of_mem_leviLift z.2
      rw [← hy] at h1
      obtain ⟨y', hy', hyy⟩ := mem_g2Inn.1 h1
      rw [← hinj hyy]
      exact hy'
    have hycomm : ∀ l ∈ L, (y : ModGL .G2 K) * l = l * y := by
      intro l hl
      obtain ⟨l₀, hl₀, hl₀ψ⟩ := exists_mem_leviLift hψ hS hSperf
        (conj_mem_g2Inn (y := ⟨l, hLC hl⟩) hl)
      have h1 : (z : G) * l₀ = l₀ * z :=
        congrArg Subtype.val (mem_center_iff.1 hz ⟨l₀, hl₀⟩).symm
      have h2 : ψ ⟨(z : G), le_normalizer hzA⟩ * ψ ⟨l₀, le_normalizer (leviLift_le hl₀)⟩ =
          ψ ⟨l₀, le_normalizer (leviLift_le hl₀)⟩ * ψ ⟨(z : G), le_normalizer hzA⟩ := by
        rw [← map_mul, ← map_mul]
        exact congrArg ψ (Subtype.ext h1)
      rw [← hy, hl₀ψ, ← map_mul, ← map_mul] at h2
      exact congrArg Subtype.val (hinj h2)
    have hyH := (hHr y).2 ⟨hyL, hycomm⟩
    obtain ⟨w, hw, hwψ⟩ := exists_mem_g2Q h4 h32 h184 hK4 hc hψ hT hyH
    rw [hψinj hzA (g2Q_le hw) (hy.symm.trans hwψ.symm)]
    exact hw
  · intro w hw
    have hwA := g2Q_le hw
    obtain ⟨y, hyH, hyψ⟩ := mem_g2Inn.1 (psi_mem_of_mem_g2Q hw)
    obtain ⟨hyL, hycomm⟩ := (hHr y).1 hyH
    obtain ⟨l₀, hl₀, hl₀ψ⟩ := exists_mem_leviLift hψ hS hSperf (conj_mem_g2Inn (y := y) hyL)
    have hwl : l₀ = w := hψinj (leviLift_le hl₀) hwA (hl₀ψ.trans hyψ)
    subst hwl
    refine ⟨⟨l₀, hl₀⟩, mem_center_iff.2 fun l => Subtype.ext ?_, rfl⟩
    have hlA : (l : G) ∈ A := leviLift_le l.2
    obtain ⟨x, hxL, hxψ⟩ := mem_g2Inn.1 (psi_mem_of_mem_leviLift l.2)
    have h1 : ψ ⟨(l : G), le_normalizer hlA⟩ * ψ ⟨l₀, le_normalizer (leviLift_le hl₀)⟩ =
        ψ ⟨l₀, le_normalizer (leviLift_le hl₀)⟩ * ψ ⟨(l : G), le_normalizer hlA⟩ := by
      rw [← hxψ, hl₀ψ, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hycomm x hxL).symm
    have hmul : ∀ a b : G, ∀ (ha : a ∈ A) (hb : b ∈ A),
        ψ ⟨a * b, le_normalizer (mul_mem ha hb)⟩ =
          ψ ⟨a, le_normalizer ha⟩ * ψ ⟨b, le_normalizer hb⟩ :=
      fun a b ha hb => psi_mul (le_normalizer ha) (le_normalizer hb)
    change (l : G) * l₀ = l₀ * l
    refine hψinj (mul_mem hlA (leviLift_le hl₀)) (mul_mem (leviLift_le hl₀) hlA) ?_
    rw [hmul _ _ hlA (leviLift_le hl₀), hmul _ _ (leviLift_le hl₀) hlA, h1]

theorem g2_coords_four
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h184 : G2Centr184)
    (h187 : G2Levi187) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ 2)
    {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
    {ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K)}
    (hψ : IsActionHom A
      (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range ψ)
    (hT : ActsIn ψ T (rootSubgroup .G2 K g2c)) :
    (∀ (w : G) (hw : w ∈ g2Q ψ T), ∃ t : Kˣ, ψ ⟨w, le_normalizer (g2Q_le hw)⟩ =
      MulAut.conj ⟨torusElt .G2 K g2ir t,
        g2RankOne_le_adjointGroup g2ir (torusElt_mem_g2RankOne g2ir t)⟩) ∧
    (∀ (l : G) (hl : l ∈ layerCentralizer A (g2Q ψ T)),
      ψ ⟨l, le_normalizer (mem_inf.1 (AS76b.layerCentralizer_le A _ hl)).1⟩ ∈
        g2Inn K (g2LongA2 K)) ∧
    ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2LongA2 K →
      ∃ (l : G) (hl : l ∈ layerCentralizer A (g2Q ψ T)),
        ψ ⟨l, le_normalizer (mem_inf.1 (AS76b.layerCentralizer_le A _ hl)).1⟩ =
          MulAut.conj y := by
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  obtain ⟨L, hLC, -, hLperf, hLH, hCdec, -, hLt, -, -, hZL⟩ := h187 K 2 hK le_rfl
  have hLq : CFSG.Open.IsQuasisimple ↥L := by
    simp only [ite_true] at hLt
    exact open_isQuasisimple_of_psl hLperf hLt
  have hlay := g2_layerCentralizer_eq h4 h32 h184 hK4 hc hψ hT hLC hLperf hLH hCdec hLq
  have hLeq := eq_g2LongA2_of_levi (by rw [hK]; norm_num) hLC hLH hCdec (hZL rfl)
  refine ⟨fun w hw => ?_, fun l hl => ?_, fun y hy => ?_⟩
  · obtain ⟨y, ⟨t, ht⟩, hyψ⟩ := mem_g2Inn.1 (psi_mem_of_mem_g2Q hw)
    exact ⟨t, hyψ.symm.trans (congrArg _ (Subtype.ext ht.symm))⟩
  · have hl' := hl
    rw [hlay] at hl'
    have h : ψ ⟨l, le_normalizer (mem_inf.1 (AS76b.layerCentralizer_le A _ hl)).1⟩ ∈
        g2Inn K L := psi_mem_of_mem_leviLift hl'
    rwa [hLeq] at h
  · have hyL : (y : ModGL .G2 K) ∈ L := hLeq ▸ hy
    obtain ⟨l₀, hl₀, hl₀ψ⟩ := exists_mem_leviLift hψ (g2Inn_le_range (K := K) L)
      (commutator_g2Inn hLC hLperf) (conj_mem_g2Inn (y := y) hyL)
    rw [← hlay] at hl₀
    exact ⟨l₀, hl₀, hl₀ψ⟩

theorem exists_config814_g2_coords
    (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h33 : Lemma33Three) (h184 : G2Centr184) (h184s : G2Centr184s)
    (h187 : G2Levi187) (htc : G2TorusConj) {A R : Subgroup G} (m : ℕ) (hm : 2 ≤ m) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
    (e : rankTwoQuot A ≃* Blueprint.AdjointQuotient .G2 K) (hA : Hyp31 A)
    (hZA : Odd (Nat.card (center A))) (hR : IsSylowOf 2 R (centralizer (A : Set G))) :
    ∃ ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K),
      IsActionHom A (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range
        ψ ∧ ∃ (g : G) (T : Subgroup G), Config814 (ExcModel.g2 m hm K hK e) g R T (g2Q ψ T) ∧
          Sec3 A R T g ∧ ActsIn ψ T (rootSubgroup .G2 K g2c) ∧
          (center ↥A = ⊥ → Nat.card (g2Q ψ T) = Nat.card K - 1 ∧
            (∀ {a b : G} (ha : a ∈ A) (hb : b ∈ A),
              ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩ → a = b) ∧
            (m = 2 → (center ↥(layerCentralizer A (g2Q ψ T))).map
              (layerCentralizer A (g2Q ψ T)).subtype = g2Q ψ T ∧
              (∀ (w : G) (hw : w ∈ g2Q ψ T), ∃ t : Kˣ, ψ ⟨w, le_normalizer (g2Q_le hw)⟩ =
                MulAut.conj ⟨torusElt .G2 K g2ir t,
                  g2RankOne_le_adjointGroup g2ir (torusElt_mem_g2RankOne g2ir t)⟩) ∧
              (∀ (l : G) (hl : l ∈ layerCentralizer A (g2Q ψ T)),
                ψ ⟨l, le_normalizer (mem_inf.1 (AS76b.layerCentralizer_le A _ hl)).1⟩ ∈
                  g2Inn K (g2LongA2 K)) ∧
              ∀ y : ↥(adjointGroup .G2 K), (y : ModGL .G2 K) ∈ g2LongA2 K →
                ∃ (l : G) (hl : l ∈ layerCentralizer A (g2Q ψ T)),
                  ψ ⟨l, le_normalizer (mem_inf.1 (AS76b.layerCentralizer_le A _ hl)).1⟩ =
                    MulAut.conj y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have h34 : Asc08Lemma34 := asc08Lemma34
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hAp : commutator ↥A = ⊤ := hA.standard.1.1
  obtain ⟨ψ, hψ⟩ := exists_g2_isActionHom hAp e
  refine ⟨ψ, hψ, ?_⟩
  have hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))) := by
    refine odd_card_commutator_outer_of_quot hAp (odd_card_commutator_outer_G2 hm ?_)
    refine ⟨⟨Nat.prime_two, by omega, rfl, ?_⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨g₀, hg₀, R₀, T₀, hR₀, hT₀, -, -, hTR, -, -⟩ := section3Config_of h32 h33 h4 h34 G A hA
  have hc₀ : Sec3 A R₀ T₀ g₀ := ⟨hA, hR₀, hg₀, hT₀, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  obtain ⟨T₁, g₁, hc₁, hT₁p, hT₁c⟩ : ∃ (T' : Subgroup G) (g' : G), Sec3 A R₀ T' g' ∧
      G2Pinned ψ T' g2c ∧ ActsIn ψ T' (rootSubgroup .G2 K g2c) := by
    obtain ⟨a, ha, hlong | hshort⟩ := g2_exists_pinned h4 h32 h184 h184s hc₀ hOut hK4 hψ
    · exact ⟨_, _, sec3_conj hc₀ ha, hlong.1, hlong.2⟩
    · exact g2_long_of_short' hm hK h4 h32 h184 h184s (sec3_conj hc₀ ha) hOut hZA hψ
        hshort.1 hshort.2
  obtain ⟨T₂, g₂, hc₂, -, hT₂c⟩ := exists_sec3_of_isSylowOf hψ hc₁ hR hT₁p hT₁c
  obtain ⟨b, hb, hRlong | hRshort⟩ := g2_exists_pinned h4 h32 h184 h184s hc₂.swap hOut hK4 hψ
  · have hc₃ := sec3_mul_left hc₂ (inv_mem hb)
    refine ⟨b⁻¹ * g₂, T₂, g2_config814_of_longLong h4 h32 h184 h187 htc hm hK e
      hc₃ hOut hZA hψ hT₂c ?_ ?_, hc₃, hT₂c, fun hZ1 => ⟨card_g2Q h4 h32 h184 hK4 hc₃ hψ hT₂c hZ1,
        fun ha hb h => psi_injOn_of_center_eq_bot hψ hZ1 ha hb h,
        fun hm2 => ⟨center_layerCentralizer_g2Q h4 h32 h184 h187 (by rw [hK, hm2]) hc₃ hψ hT₂c
          hZ1, g2_coords_four h4 h32 h184 h187 (by rw [hK, hm2]) hc₃ hψ hT₂c⟩⟩⟩
    · rw [rightConjugate_inv_mul_inv]
      exact hRlong.1
    · rw [rightConjugate_inv_mul_inv]
      exact hRlong.2
  · exfalso
    refine g2_not_mixed h4 h32 h184 h184s (sec3_mul_left hc₂ (inv_mem hb)) hOut hZA hK4 hψ
      hT₂c ?_ ?_
    · rw [rightConjugate_inv_mul_inv]
      exact hRshort.1
    · rw [rightConjugate_inv_mul_inv]
      exact hRshort.2

theorem exists_config814_g2
    (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h33 : Lemma33Three) (h184 : G2Centr184) (h184s : G2Centr184s)
    (h187 : G2Levi187) (htc : G2TorusConj) {A R : Subgroup G} (m : ℕ) (hm : 2 ≤ m) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ m)
    (e : rankTwoQuot A ≃* Blueprint.AdjointQuotient .G2 K) (hA : Hyp31 A)
    (hZA : Odd (Nat.card (center A))) (hR : IsSylowOf 2 R (centralizer (A : Set G))) :
    ∃ ψ : normalizer (A : Set G) →* MulAut ↥(adjointGroup .G2 K),
      IsActionHom A (MulAut.conj : ↥(adjointGroup .G2 K) →* MulAut ↥(adjointGroup .G2 K)).range
        ψ ∧ ∃ (g : G) (T : Subgroup G), Config814 (ExcModel.g2 m hm K hK e) g R T (g2Q ψ T) ∧
          (center ↥A = ⊥ → Nat.card (g2Q ψ T) = Nat.card K - 1 ∧
            (m = 2 → (center ↥(layerCentralizer A (g2Q ψ T))).map
              (layerCentralizer A (g2Q ψ T)).subtype = g2Q ψ T)) := by
  obtain ⟨ψ, hψ, g, T, hcfg, -, -, hQ⟩ := exists_config814_g2_coords h4 h32 h33 h184 h184s h187
    htc m hm K hK e hA hZA hR
  exact ⟨ψ, hψ, g, T, hcfg, fun hZ1 => ⟨(hQ hZ1).1, fun hm2 => ((hQ hZ1).2.2 hm2).1⟩⟩

theorem step814_g2
    (h4 : Asc75Theorem4)
    (h32 : Lemma32) (h33 : Lemma33Three) (h184 : G2Centr184) (h184s : G2Centr184s)
    (h187 : G2Levi187) (htc : G2TorusConj) : Step814 .G2 := by
  intro G _ _ A D hD hA hZA
  cases D with
  | g2 m hm K hK e =>
    obtain ⟨g₀, hg₀, R, -, hR, -⟩ := section3Config_of h32 h33 h4 asc08Lemma34 G A hA
    obtain ⟨ψ, -, g, T, hcfg, -⟩ := exists_config814_g2 h4 h32 h33 h184 h184s h187 htc m hm K hK
      e hA hZA hR
    exact ⟨g, R, T, _, hcfg⟩
  | f4 => simp [ExcModel.tag] at hD
  | e6 => simp [ExcModel.tag] at hD
  | e7 => simp [ExcModel.tag] at hD
  | e8 => simp [ExcModel.tag] at hD
  | triality => simp [ExcModel.tag] at hD
  | twistedE6 => simp [ExcModel.tag] at hD
  | ree => simp [ExcModel.tag] at hD
  | tits => simp [ExcModel.tag] at hD

end CFSG.ComponentClassification.RankTwoExceptional
