module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step28
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step211
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step215
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Odd
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step218Mat
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step213
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2LocalQ
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step26

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

section Setting

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem card_sec2P_sup_sec2S (h21 : Step21) (h26 : Step26) (hS : Sec2Setting G A R g E F) :
    Nat.card (sec2P E) = 1024 ∧ Nat.card (sec2S A R E F) = 1024 ∧
      Nat.card (sec2S A R E F ⊓ sec2P E : Subgroup G) = 256 ∧
      Nat.card (sec2P E ⊔ sec2S A R E F : Subgroup G) = 4 * Nat.card (sec2S A R E F) := by
  obtain ⟨-, ⟨hEP, hEP16, -⟩, -, -, -, -, -, -, ⟨hESP, hESP4, -⟩, ⟨hES, hES16, -⟩⟩ :=
    h21 G A R g E F hS
  obtain ⟨-, -, -, -, -, -, -, hHS, -⟩ := h26 G A R g E F hS
  have hE := hS.frame.cardE
  have hP : Nat.card (sec2P E) = 1024 := by
    have h := relIndex_mul_card E (sec2P E)
    rw [inf_eq_left.mpr hEP, hEP16, hE] at h
    omega
  have hS' : Nat.card (sec2S A R E F) = 1024 := by
    have h := relIndex_mul_card E (sec2S A R E F)
    rw [inf_eq_left.mpr hES, hES16, hE] at h
    omega
  have hSP : Nat.card (sec2S A R E F ⊓ sec2P E : Subgroup G) = 256 := by
    have h := relIndex_mul_card E (sec2S A R E F ⊓ sec2P E)
    rw [inf_eq_left.mpr hESP, hESP4, hE] at h
    omega
  refine ⟨hP, hS', hSP, ?_⟩
  have hPN : sec2P E ≤ normalizer (sec2S A R E F : Set G) := le_sup_left.trans hHS
  have h := card_sup_mul_card_inf hPN
  rw [hSP, hP, sup_comm] at h
  omega

theorem card_sec2H_eq (h26 : Step26) (hS : Sec2Setting G A R g E F) :
    Nat.card (sec2H E F) = 60 * Nat.card (sec2S A R E F) := by
  obtain ⟨-, hSH, ⟨φ, hφs, hφker⟩, -, -, -, -, -, -⟩ := h26 G A R g E F hS
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv, hφker,
    Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv] at h
  rw [h, Nat.card_eq_fintype_card (α := alternatingGroup (Fin 5)), card_alternatingGroup,
    Fintype.card_fin]
  rfl

theorem inf_sec2H_eq (h21 : Step21) (h26 : Step26) (hS : Sec2Setting G A R g E F)
    {T₀ : Subgroup G} (hPST : sec2P E ⊔ sec2S A R E F ≤ T₀) (hT₀ : IsPGroup 2 T₀) :
    T₀ ⊓ sec2H E F = sec2P E ⊔ sec2S A R E F := by
  obtain ⟨-, hSH, -, -, -, -, -, -, -⟩ := h26 G A R g E F hS
  obtain ⟨-, hS1024, -, hPS⟩ := card_sec2P_sup_sec2S h21 h26 hS
  have hH := card_sec2H_eq h26 hS
  have hle : sec2P E ⊔ sec2S A R E F ≤ T₀ ⊓ sec2H E F := le_inf hPST (sup_le le_sup_left hSH)
  obtain ⟨k, hk⟩ := (hT₀.to_inf_left (K := sec2H E F)).exists_card_eq
  have hdvd : Nat.card (T₀ ⊓ sec2H E F : Subgroup G) ∣ Nat.card (sec2H E F) :=
    card_dvd_of_le inf_le_right
  rw [hk, hH, hS1024, show 60 * 1024 = 15 * 2 ^ 12 by norm_num] at hdvd
  have hk' : 2 ^ k ∣ 2 ^ 12 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_left hdvd
  have hk12 : k ≤ 12 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hk'
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hk, hPS, hS1024]
  calc 2 ^ k ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hk12
    _ = 4 * 1024 := by norm_num

theorem le_normalizer_sec2P (h21 : Step21) (h24 : Step24) (h25 : Step25) (h26 : Step26)
    (h29 : Step29) (hS : Sec2Setting G A R g E F) {T₀ : Subgroup G}
    (hPST : sec2P E ⊔ sec2S A R E F ≤ T₀)
    (hT₀ : IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G))) :
    T₀ ≤ normalizer (sec2P E : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, -, -, -, hNH⟩ := h26 G A R g E F hS
  have hSp := special_of h24 hS
  have hinf := inf_sec2H_eq h21 h26 hS hPST hT₀.isPGroup
  set PS := sec2P E ⊔ sec2S A R E F with hPSdef
  have hT₀PS : ∀ t ∈ T₀, t ∈ normalizer (PS : Set G) := by
    intro t ht
    rw [← hinf]
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer ht, hNH (hT₀.le ht)⟩
  have hT₀Z : ∀ t ∈ T₀, t ∈ normalizer (sec2Z A E F : Set G) := fun t ht => by
    rw [← hSp.center]
    exact mem_normalizer_centerIn (hT₀.le ht)
  have h25' := h25 G A R g E F hS
  have hV : ∀ t ∈ T₀, ∀ v ∈ E ⊓ A, t * v * t⁻¹ ∈ E ⊓ A := by
    intro t ht v hv
    have hv' : v ∈ {x | x ∈ PS ∧ ∀ y ∈ PS, x⁻¹ * y⁻¹ * x * y ∈ sec2Z A E F} := by
      rw [h25']
      exact hv
    obtain ⟨hvPS, hvc⟩ := hv'
    have hmem : t * v * t⁻¹ ∈ {x | x ∈ PS ∧ ∀ y ∈ PS, x⁻¹ * y⁻¹ * x * y ∈ sec2Z A E F} := by
      refine ⟨(mem_normalizer_iff.mp (hT₀PS t ht) v).mp hvPS, fun y hy => ?_⟩
      have hy' : t⁻¹ * y * t ∈ PS := by
        have := (mem_normalizer_iff.mp (inv_mem (hT₀PS t ht)) y).mp hy
        simpa using this
      have h2 := (mem_normalizer_iff.mp (hT₀Z t ht) _).mp (hvc _ hy')
      have e : (t * v * t⁻¹)⁻¹ * y⁻¹ * (t * v * t⁻¹) * y =
          t * (v⁻¹ * (t⁻¹ * y * t)⁻¹ * v * (t⁻¹ * y * t)) * t⁻¹ := by group
      rw [e]
      exact h2
    rw [h25'] at hmem
    exact hmem
  have hTV : T₀ ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_iff.mpr fun v => ⟨hV t ht v, fun h => by
      have := hV t⁻¹ (inv_mem ht) _ h
      simpa [mul_assoc] using this⟩
  obtain ⟨x, hx, hxS⟩ := exists_mem_sec2P_not_mem_sec2S h26 hS
  have hPsyl := (h29 G A R g E F hS x hx hxS).2.2.1
  have hPT₀ : sec2P E ≤ T₀ := le_sup_left.trans hPST
  have hPeq : T₀ ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) = sec2P E :=
    hPsyl.eq_of_le (le_inf hPT₀ hPsyl.le) inf_le_right hT₀.isPGroup.to_inf_left
  intro t ht
  rw [← hPeq]
  exact inf_normalizer_le_normalizer_inf
    ⟨le_normalizer ht, normalizer_le_normalizer_centralizer_of _ (hTV ht)⟩

theorem sec2F_le_sec2K
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h211 : Step211) (hS : Sec2Setting G A R g E F) {u y : G} (huy : Sec2UY A R E F u y) :
    F ≤ sec2K E := by
  classical
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  obtain ⟨huAS, hu3, huE⟩ : u ∈ A ⊓ normalizer (sec2S A R E F : Set G) ∧ orderOf u = 3 ∧
      ∃ e ∈ E, u⁻¹ * e * u ≠ e := ⟨huy.1, huy.2.1, huy.2.2.1⟩
  obtain ⟨huEn, -, -, hufix⟩ := sec2U_facts h11 hE16 hF hL hodd huAS hu3 huE
  have huFA := (mem_normalizer_inf_of_orderOf_eq_three h11 hE16 hF hL hodd huAS.1 huAS.2 hu3).2
  have huP : u ∈ normalizer (sec2P E : Set G) := normalizer_le_normalizer_sec2P E huEn
  have hFS := (le_sec2S_and_le_sec2S (A := A) (R := R) hF).2
  have hFP : F ≤ normalizer (sec2P E : Set G) :=
    (hFS.trans (sec2S_le_normalizer_left hF hL hodd)).trans (normalizer_le_normalizer_sec2P E)
  have huZ : u ∈ normalizer (sec2Z A F E : Set G) := by
    rw [sec2Z_comm]
    exact (mem_normalizer_sec2S_of_mem hF huAS.1 huEn
      (sec2U_facts h11 hE16 hF hL hodd huAS hu3 huE).2.1).1
  have hufix' : ∀ w ∈ sec2Z A F E, u * w * u⁻¹ = w → w = 1 := by
    rw [sec2Z_comm]
    exact hufix
  have hoddK : ∀ k ∈ normalizer (sec2P E : Set G), orderOf k = 3 → k ∈ sec2K E :=
    fun k hk hk3 => subset_closure ⟨hk, by rw [hk3]; decide⟩
  have hval : ∀ f ∈ F, f⁻¹ * (u * f * u⁻¹) ∈ sec2K E := by
    intro f hf
    have e : f⁻¹ * (u * f * u⁻¹) = (f⁻¹ * u * f) * u⁻¹ := by group
    rw [e]
    refine mul_mem (hoddK _ (mul_mem (mul_mem (inv_mem (hFP hf)) huP) (hFP hf)) ?_)
      (hoddK _ (inv_mem huP) (by rw [orderOf_inv, hu3]))
    have := orderOf_injective (MulAut.conj f⁻¹).toMonoidHom (MulAut.conj f⁻¹).injective u
    simpa [hu3] using this
  have hmapsto : ∀ f ∈ F ⊓ A, f⁻¹ * (u * f * u⁻¹) ∈ F ⊓ A := fun f hf =>
    mul_mem (inv_mem hf) ((mem_normalizer_iff.mp huFA f).mp hf)
  let m : ↥(F ⊓ A) → ↥(F ⊓ A) := fun f => ⟨_, hmapsto f f.2⟩
  have hm : Function.Injective m := by
    intro f f' h
    have h1 : (f : G)⁻¹ * (u * f * u⁻¹) = (f' : G)⁻¹ * (u * f' * u⁻¹) := congrArg Subtype.val h
    have h1' : (f : G)⁻¹ * u * f = (f' : G)⁻¹ * u * f' :=
      mul_right_cancel (b := u⁻¹) (by simpa [mul_assoc] using h1)
    have hc : (f' : G) * (f : G)⁻¹ ∈ F ⊓ A := mul_mem f'.2 (inv_mem f.2)
    have hcu : u * ((f' : G) * (f : G)⁻¹) * u⁻¹ = (f' : G) * (f : G)⁻¹ := by
      have h2 : (f' : G) * (f : G)⁻¹ * u * ((f' : G) * (f : G)⁻¹)⁻¹ = u := by
        calc (f' : G) * (f : G)⁻¹ * u * ((f' : G) * (f : G)⁻¹)⁻¹
            = f' * ((f : G)⁻¹ * u * f) * (f' : G)⁻¹ := by group
          _ = f' * ((f' : G)⁻¹ * u * f') * (f' : G)⁻¹ := by rw [h1']
          _ = u := by group
      calc u * ((f' : G) * (f : G)⁻¹) * u⁻¹
          = ((f' : G) * (f : G)⁻¹ * u * ((f' : G) * (f : G)⁻¹)⁻¹) *
            ((f' : G) * (f : G)⁻¹) * u⁻¹ := by rw [h2]
        _ = (f' : G) * (f : G)⁻¹ := by group
    have h6 := eq_one_of_conj_eq_of_sec2Z hF.symm hL hodd huAS.1 huZ hufix' hc hcu
    exact Subtype.ext (mul_inv_eq_one.mp h6).symm
  have hsurj : Function.Surjective m := Finite.injective_iff_surjective.mp hm
  have hFAK : F ⊓ A ≤ sec2K E := by
    intro a ha
    obtain ⟨f, hf⟩ := hsurj ⟨a, ha⟩
    have h1 : (f : G)⁻¹ * (u * f * u⁻¹) = a := congrArg Subtype.val hf
    rw [← h1]
    exact hval f f.2.1
  obtain ⟨hPOK, -, -, -, -, -, -, -, -⟩ := h211 G A R g E F hS
  have hPK : sec2P E ≤ sec2K E := le_sup_left.trans hPOK
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 6) (by rw [hF.cardE]; norm_num)
  have hEP : E ≤ sec2P E := le_sec2P hE2 le_normalizer le_rfl
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  rw [eq_inf_sup_of_le_sup hRA hF.R_le_F hF.F_le]
  exact sup_le hFAK ((hF.R_le_E.trans hEP).trans hPK)

theorem sec2P_sup_sec2S_le_sec2T (h211 : Step211) (hS : Sec2Setting G A R g E F)
    (hFK : F ≤ sec2K E) {T₀ : Subgroup G} (hPST : sec2P E ⊔ sec2S A R E F ≤ T₀) :
    sec2P E ⊔ sec2S A R E F ≤ sec2T E T₀ := by
  obtain ⟨hPOK, -, -, -, -, -, -, -, -⟩ := h211 G A R g E F hS
  have hPK : sec2P E ≤ sec2K E := le_sup_left.trans hPOK
  refine le_inf hPST (sup_le hPK (sup_le hFK ?_))
  exact fun c hc => hPK (mem_centralizerMod.mp hc).1

theorem relIndex_sec2T_eq_two (h21 : Step21) (h26 : Step26) (h211 : Step211)
    (hS : Sec2Setting G A R g E F) (hFK : F ≤ sec2K E) {T₀ : Subgroup G}
    (hPST : sec2P E ⊔ sec2S A R E F ≤ T₀) (hT₀G : IsSylowOf 2 T₀ ⊤)
    (hT₀P : T₀ ≤ normalizer (sec2P E : Set G)) :
    IsSylowOf 2 (sec2T E T₀) (sec2K E) ∧
      (sec2P E ⊔ sec2S A R E F).relIndex (sec2T E T₀) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKP : sec2K E ≤ normalizer (sec2P E : Set G) := sec2K_le_normalizer E
  have hTsyl : IsSylowOf 2 (sec2T E T₀) (sec2K E) :=
    (hT₀G.of_le hT₀P le_top).inf_of_le_normalizer hKP fun n hn => mem_normalizer_oUpperTwo hn
  refine ⟨hTsyl, ?_⟩
  obtain ⟨hP, hS1024, -, hPS⟩ := card_sec2P_sup_sec2S h21 h26 hS
  obtain ⟨hPOK, hidx, -, -, -, -, -, -, -⟩ := h211 G A R g E F hS
  have hPST' := sec2P_sup_sec2S_le_sec2T h211 hS hFK hPST
  set O := AS76b.oddCoreIn (sec2K E) with hO
  have hPK : sec2P E ≤ sec2K E := le_sup_left.trans hPOK
  have hPO : Nat.card (sec2P E ⊔ O : Subgroup G) = 1024 * Nat.card O := by
    have hON : O ≤ normalizer (sec2P E : Set G) := (AS76b.oddCoreIn_le _).trans hKP
    have h := card_sup_mul_card_inf hON
    rw [NXKernel.inf_eq_bot_of_two_odd (isPGroup_sec2P E) (AS76b.odd_card_oddCoreIn _),
      card_bot, mul_one, hP] at h
    exact h
  have hK : Nat.card (sec2K E) = 1080 * (1024 * Nat.card O) := by
    have h := relIndex_mul_card (sec2P E ⊔ O) (sec2K E)
    rw [inf_eq_left.mpr hPOK, hidx, hPO] at h
    exact h.symm
  have hTK : (sec2T E T₀).relIndex (sec2K E) * Nat.card (sec2T E T₀) = Nat.card (sec2K E) := by
    have h := relIndex_mul_card (sec2T E T₀) (sec2K E)
    have hle : sec2T E T₀ ⊓ sec2K E = sec2T E T₀ := inf_eq_left.mpr inf_le_right
    rwa [hle] at h
  have hodd : ¬ 2 ∣ (sec2T E T₀).relIndex (sec2K E) := (isSylowOf_iff.mp hTsyl).2.2
  obtain ⟨n, hn⟩ := hTsyl.isPGroup.exists_card_eq
  have hPST2 : (sec2P E ⊔ sec2S A R E F).relIndex (sec2T E T₀) * Nat.card
      (sec2P E ⊔ sec2S A R E F : Subgroup G) = Nat.card (sec2T E T₀) := by
    have h := relIndex_mul_card (sec2P E ⊔ sec2S A R E F) (sec2T E T₀)
    rwa [inf_eq_left.mpr hPST'] at h
  rw [hPS, hS1024] at hPST2
  rw [hK, hn] at hTK
  rw [hn] at hPST2
  have hOodd : Odd (Nat.card O) := AS76b.odd_card_oddCoreIn _
  obtain ⟨r, hr⟩ := hOodd
  obtain ⟨q, hq⟩ : Odd ((sec2T E T₀).relIndex (sec2K E)) := Nat.odd_iff.mpr (by omega)
  rw [hq, hr] at hTK
  have hn13 : 2 ^ n = 2 ^ 13 := by
    have h1 : (2 * q + 1) * 2 ^ n = 2 ^ 13 * (135 * (2 * r + 1)) := by rw [hTK]; ring
    have h2 : 2 ^ n ∣ 2 ^ 13 * (135 * (2 * r + 1)) := ⟨2 * q + 1, by rw [← h1]; ring⟩
    have h3 : 2 ^ 13 ∣ (2 * q + 1) * 2 ^ n := ⟨135 * (2 * r + 1), h1⟩
    have hc1 : Nat.Coprime (2 ^ n) (135 * (2 * r + 1)) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega))
    have hc2 : Nat.Coprime (2 ^ 13) (2 * q + 1) :=
      Nat.Coprime.pow_left 13 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega))
    exact Nat.dvd_antisymm (hc1.dvd_of_dvd_mul_right h2) (hc2.dvd_of_dvd_mul_left h3)
  rw [hn13] at hPST2
  omega

end Setting

section Five

open Equiv

local instance decEqPerm5'' : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

local instance decMemAlt5'' :
    DecidablePred (fun σ : Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Perm.sign.decidableMemKer

theorem five_fixed_unique : ∀ a : Perm (Fin 5), a ∈ alternatingGroup (Fin 5) → a ^ 2 = 1 →
    a ≠ 1 → ∀ k k' : Fin 5, a k = k → a k' = k' → k = k' := by
  decide +kernel

theorem five_exists_fixed : ∀ a : Perm (Fin 5), a ∈ alternatingGroup (Fin 5) → a ^ 2 = 1 →
    ∃ k, a k = k := by
  decide +kernel

theorem five_mem_four : ∀ (k : Fin 5) (σ y : Perm (Fin 5)), σ k = k → y k = k →
    y ∈ alternatingGroup (Fin 5) → y ^ 3 = 1 → y ≠ 1 → σ ^ 8 = 1 →
    (y⁻¹ * σ⁻¹ * y * σ) ^ 2 = 1 → σ ∈ alternatingGroup (Fin 5) ∧ σ ^ 2 = 1 := by
  decide +kernel

theorem five_four_cases : ∀ (k : Fin 5) (σ : Perm (Fin 5)), σ k = k →
    σ ∈ alternatingGroup (Fin 5) → σ ^ 2 = 1 → ∀ a : Perm (Fin 5), a k = k →
    a ∈ alternatingGroup (Fin 5) → a ^ 2 = 1 → a ≠ 1 → ∀ y : Perm (Fin 5), y k = k →
    y ∈ alternatingGroup (Fin 5) → y ^ 3 = 1 → y ≠ 1 →
    σ = 1 ∨ σ = a ∨ σ = y * a * y⁻¹ ∨ σ = y⁻¹ * a * y := by
  decide +kernel

end Five

section ConjAut

variable {H S : Subgroup G} (φ : ↥H →* alternatingGroup (Fin 5))
  (hφs : Function.Surjective φ) (hφker : φ.ker = S.subgroupOf H)

@[expose] def conjOnH (g : G) (hg : g ∈ normalizer (H : Set G)) : ↥H →* ↥H where
  toFun h := ⟨g * h * g⁻¹, (mem_normalizer_iff.mp hg h).mp h.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem conjOnH_apply (g : G) (hg : g ∈ normalizer (H : Set G)) (h : ↥H) :
    ((conjOnH g hg h : ↥H) : G) = g * h * g⁻¹ := rfl

include hφs hφker

omit [Finite G] in
theorem conjOnH_comp {g : G} (hgH : g ∈ normalizer (H : Set G))
    (hgS : g ∈ normalizer (S : Set G)) :
    Function.Surjective (φ.comp (conjOnH g hgH)) ∧ (φ.comp (conjOnH g hgH)).ker = φ.ker := by
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨h, rfl⟩ := hφs a
    have hmem : g⁻¹ * h * g⁻¹⁻¹ ∈ H := (mem_normalizer_iff.mp (inv_mem hgH) h).mp h.2
    refine ⟨⟨_, hmem⟩, congrArg φ (Subtype.ext ?_)⟩
    simp only [conjOnH_apply]
    group
  · ext h
    have e1 : h ∈ (φ.comp (conjOnH g hgH)).ker ↔ conjOnH g hgH h ∈ φ.ker := Iff.rfl
    rw [e1, hφker, mem_subgroupOf, mem_subgroupOf, conjOnH_apply]
    exact (mem_normalizer_iff.mp hgS h).symm

@[expose] noncomputable def autOfConjH {g : G} (hgH : g ∈ normalizer (H : Set G))
    (hgS : g ∈ normalizer (S : Set G)) : MulAut (alternatingGroup (Fin 5)) :=
  (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (conjOnH_comp φ hφs hφker hgH hgS).2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (conjOnH_comp φ hφs hφker hgH hgS).1))

omit [Finite G] in
theorem autOfConjH_apply {g : G} (hgH : g ∈ normalizer (H : Set G))
    (hgS : g ∈ normalizer (S : Set G)) (h : ↥H) :
    autOfConjH φ hφs hφker hgH hgS (φ h) = φ (conjOnH g hgH h) := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm (φ h) =
      ((h : ↥H) : ↥H ⧸ φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [autOfConjH, MulEquiv.trans_apply, e, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

@[expose] noncomputable def autOfConjHHom :
    ↥(normalizer (H : Set G) ⊓ normalizer (S : Set G)) →* MulAut (alternatingGroup (Fin 5)) where
  toFun g := autOfConjH φ hφs hφker g.2.1 g.2.2
  map_one' := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨h, rfl⟩ := hφs a
    rw [autOfConjH_apply]
    exact congrArg φ (Subtype.ext (by simp [conjOnH_apply]))
  map_mul' g g' := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨h, rfl⟩ := hφs a
    rw [MulAut.mul_apply, autOfConjH_apply, autOfConjH_apply, autOfConjH_apply]
    exact congrArg φ (Subtype.ext (by simp only [conjOnH_apply, Subgroup.coe_mul]; group))

end ConjAut

@[expose] noncomputable def autAltFive : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))

omit [Finite G] in
theorem autAltFive_apply (σ : Equiv.Perm (Fin 5)) (a : alternatingGroup (Fin 5)) :
    ((autAltFive σ a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = σ * a * σ⁻¹ :=
  MulAut.conjNormal_apply σ a

omit [Finite G] in
theorem exists_perm_conjOnH {H S : Subgroup G} (φ : ↥H →* alternatingGroup (Fin 5))
    (hφs : Function.Surjective φ) (hφker : φ.ker = S.subgroupOf H) {g : G}
    (hgH : g ∈ normalizer (H : Set G)) (hgS : g ∈ normalizer (S : Set G)) :
    ∃ σ : Equiv.Perm (Fin 5), ∀ h : ↥H,
      ((φ (conjOnH g hgH h) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        σ * (φ h : Equiv.Perm (Fin 5)) * σ⁻¹ := by
  refine ⟨autAltFive.symm (autOfConjH φ hφs hφker hgH hgS), fun h => ?_⟩
  rw [← autOfConjH_apply φ hφs hφker hgH hgS, ← autAltFive_apply, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem eq_one_of_forall_conj_eq {τ : Equiv.Perm (Fin 5)}
    (h : ∀ a : alternatingGroup (Fin 5), τ * (a : Equiv.Perm (Fin 5)) * τ⁻¹ = a) : τ = 1 := by
  apply autAltFive.injective
  rw [map_one]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [autAltFive_apply, h a]
  rfl

omit [Finite G] in
theorem perm_conjH_pow {H : Subgroup G} (φ : ↥H →* alternatingGroup (Fin 5)) {g : G}
    (hgH : g ∈ normalizer (H : Set G)) {σ : Equiv.Perm (Fin 5)}
    (hσ : ∀ h : ↥H, ((φ (conjOnH g hgH h) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      σ * (φ h : Equiv.Perm (Fin 5)) * σ⁻¹) (n : ℕ) (h : ↥H) :
    ((φ (conjOnH (g ^ n) (pow_mem hgH n) h) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
      σ ^ n * (φ h : Equiv.Perm (Fin 5)) * (σ ^ n)⁻¹ := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, inv_one, mul_one]
    exact congrArg (fun a : alternatingGroup (Fin 5) => (a : Equiv.Perm (Fin 5)))
      (congrArg φ (Subtype.ext (by simp [conjOnH_apply])))
  | succ n ih =>
    have e : conjOnH (g ^ (n + 1)) (pow_mem hgH (n + 1)) h =
        conjOnH g hgH (conjOnH (g ^ n) (pow_mem hgH n) h) :=
      Subtype.ext (by simp only [conjOnH_apply, pow_succ']; group)
    rw [e, hσ, ih, pow_succ']
    group

omit [Finite G] in
theorem exists_mem_conj_mem_of_comm_mem {H S P : Subgroup G}
    (φ : ↥H →* alternatingGroup (Fin 5)) (hφs : Function.Surjective φ)
    (hφker : φ.ker = S.subgroupOf H) (hPH : P ≤ H)
    (hP4 : Nat.card ((P.subgroupOf H).map φ) = 4) {y : G} (hyH : y ∈ H)
    (hyP : y ∈ normalizer (P : Set G)) (hy3 : y ^ 3 = 1) (hyS : y ∉ S) {t : G}
    (htH : t ∈ normalizer (H : Set G)) (htS : t ∈ normalizer (S : Set G))
    (htP : t ∈ normalizer (P : Set G)) {n : ℕ} (htn : t ^ 2 ^ n = 1)
    (hyt : y⁻¹ * t⁻¹ * y * t ∈ P) :
    ∃ p₀ ∈ P, ∀ h ∈ H, (p₀⁻¹ * t) * h * (p₀⁻¹ * t)⁻¹ * h⁻¹ ∈ S := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_conjOnH φ hφs hφker htH htS
  let ψ : ↥H →* Equiv.Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp φ
  have hψ : ∀ h : ↥H, ψ h = ((φ h : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) :=
    fun _ => rfl
  have hψA : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin 5) := fun h => (φ h).2
  have hψ1 : ∀ h : ↥H, ψ h = 1 → (h : G) ∈ S := fun h h1 => by
    have h2 : φ h = 1 := Subtype.ext h1
    have h3 : h ∈ φ.ker := h2
    rw [hφker, mem_subgroupOf] at h3
    exact h3
  have htH' : ∀ g ∈ H, t * g * t⁻¹ ∈ H := fun g hg => (mem_normalizer_iff.mp htH g).mp hg
  have hσ' : ∀ g (hg : g ∈ H), ψ ⟨t * g * t⁻¹, htH' g hg⟩ = σ * ψ ⟨g, hg⟩ * σ⁻¹ :=
    fun g hg => hσ ⟨g, hg⟩
  have hP2 : ∀ p (hp : p ∈ P), ψ ⟨p, hPH hp⟩ ^ 2 = 1 := by
    intro p hp
    have hv : φ ⟨p, hPH hp⟩ ∈ (P.subgroupOf H).map φ := ⟨⟨p, hPH hp⟩, hp, rfl⟩
    have h4 : (⟨_, hv⟩ : ↥((P.subgroupOf H).map φ)) ^ 4 = 1 := by
      rw [← hP4]
      exact pow_card_eq_one'
    have h4' : ψ ⟨p, hPH hp⟩ ^ 4 = 1 := by
      have := congrArg (fun w : ↥((P.subgroupOf H).map φ) =>
        ((w : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))) h4
      rw [hψ]
      simpa using this
    exact Sec2V4.sq_eq_one_of_pow_four _ (hψA _) h4'
  obtain ⟨p₁, hp₁, ha1⟩ : ∃ p₁ ∈ P, ∀ hp : p₁ ∈ H, ψ ⟨p₁, hp⟩ ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Nat.card ((P.subgroupOf H).map φ) ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      refine ⟨fun v w => ?_⟩
      obtain ⟨⟨p, hpH⟩, hp, hpv⟩ := v.2
      obtain ⟨⟨q, hqH⟩, hq, hqw⟩ := w.2
      obtain ⟨hpH', hp1⟩ := hall p hp
      obtain ⟨hqH', hq1⟩ := hall q hq
      apply Subtype.ext
      rw [← hpv, ← hqw]
      exact Subtype.ext (hp1.trans hq1.symm)
    omega
  have hp₁H := hPH hp₁
  set a := ψ ⟨p₁, hp₁H⟩ with ha
  have ha1' : a ≠ 1 := ha1 hp₁H
  have haA := hψA ⟨p₁, hp₁H⟩
  have ha2 := hP2 p₁ hp₁
  obtain ⟨k, hk⟩ := five_exists_fixed a haA ha2
  have huniq := five_fixed_unique a haA ha2 ha1'
  have hinv : ∀ p (hp : p ∈ P), (ψ ⟨p, hPH hp⟩)⁻¹ = ψ ⟨p, hPH hp⟩ := fun p hp =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hP2 p hp)
  have hPk : ∀ p (hp : p ∈ P), ψ ⟨p, hPH hp⟩ k = k := by
    intro p hp
    have hcomm : ψ ⟨p, hPH hp⟩ * a = a * ψ ⟨p, hPH hp⟩ := by
      have hpp : p * p₁ ∈ P := P.mul_mem hp hp₁
      have e : ψ ⟨p * p₁, hPH hpp⟩ = ψ ⟨p, hPH hp⟩ * a := by
        rw [ha, ← map_mul]
        rfl
      calc ψ ⟨p, hPH hp⟩ * a = (ψ ⟨p * p₁, hPH hpp⟩)⁻¹ := by rw [hinv _ hpp, e]
        _ = a⁻¹ * (ψ ⟨p, hPH hp⟩)⁻¹ := by rw [e, mul_inv_rev]
        _ = a * ψ ⟨p, hPH hp⟩ := by rw [hinv p hp, ha, hinv p₁ hp₁]
    refine (huniq k (ψ ⟨p, hPH hp⟩ k) hk ?_).symm
    calc a (ψ ⟨p, hPH hp⟩ k) = (a * ψ ⟨p, hPH hp⟩) k := rfl
      _ = (ψ ⟨p, hPH hp⟩ * a) k := by rw [hcomm]
      _ = ψ ⟨p, hPH hp⟩ k := by rw [Equiv.Perm.mul_apply, hk]
  set yb := ψ ⟨y, hyH⟩ with hyb
  have hybA : yb ∈ alternatingGroup (Fin 5) := hψA _
  have hyb3 : yb ^ 3 = 1 := by
    rw [hyb, ← map_pow]
    have e : (⟨y, hyH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [e, map_one]
  have hyb1 : yb ≠ 1 := fun h => hyS (hψ1 _ h)
  have hconjP : ∀ g (hg : g ∈ H) (hgP : g ∈ normalizer (P : Set G)) p (hp : p ∈ P),
      ψ ⟨g, hg⟩ * ψ ⟨p, hPH hp⟩ * (ψ ⟨g, hg⟩)⁻¹ =
        ψ ⟨g * p * g⁻¹, hPH ((mem_normalizer_iff.mp hgP p).mp hp)⟩ := by
    intro g hg _ p hp
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hfix : ∀ τ : Equiv.Perm (Fin 5), (τ * a * τ⁻¹) k = k → τ k = k := by
    intro τ hτ
    have h1 : a (τ⁻¹ k) = τ⁻¹ k := by
      have := congrArg (fun i => τ⁻¹ i) hτ
      simpa [Equiv.Perm.mul_apply] using this
    have h2 := huniq k (τ⁻¹ k) hk h1
    have h3 := congrArg (fun i => τ i) h2
    simpa using h3
  have hybk : yb k = k := hfix yb (by
    rw [hyb, ha, hconjP y hyH hyP p₁ hp₁]
    exact hPk _ ((mem_normalizer_iff.mp hyP p₁).mp hp₁))
  have hσk : σ k = k := hfix σ (by
    have hp : t * p₁ * t⁻¹ ∈ P := (mem_normalizer_iff.mp htP p₁).mp hp₁
    rw [ha, ← hσ' p₁ hp₁H]
    exact hPk _ hp)
  have hσpow : σ ^ 2 ^ n = 1 := by
    apply eq_one_of_forall_conj_eq
    intro b
    obtain ⟨h, rfl⟩ := hφs b
    have h1 := perm_conjH_pow φ htH hσ (2 ^ n) h
    have e : conjOnH (t ^ 2 ^ n) (pow_mem htH (2 ^ n)) h = h :=
      Subtype.ext (by simp [conjOnH_apply, htn])
    rw [e] at h1
    exact h1.symm
  have hσ8 : σ ^ 8 = 1 := by
    have hdvd : orderOf σ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hσpow
    obtain ⟨m, -, hmo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have h120 : orderOf σ ∣ 15 * 2 ^ 3 := by
      have := orderOf_dvd_card (G := Equiv.Perm (Fin 5)) (x := σ)
      simpa [Fintype.card_perm, Nat.factorial] using this
    rw [hmo] at h120
    have h8 : 2 ^ m ∣ 2 ^ 3 :=
      (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_left h120
    have : orderOf σ ∣ 8 := by rw [hmo]; simpa using h8
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hyt' : t⁻¹ * y * t ∈ H := by
    have := (mem_normalizer_iff.mp (inv_mem htH) y).mp hyH
    simpa using this
  have hX : σ⁻¹ * yb * σ = ψ ⟨t⁻¹ * y * t, hyt'⟩ := by
    have h1 := hσ' _ hyt'
    have e : (⟨t * (t⁻¹ * y * t) * t⁻¹, htH' _ hyt'⟩ : ↥H) = ⟨y, hyH⟩ :=
      Subtype.ext (by simp only; group)
    rw [e] at h1
    rw [hyb, h1]
    group
  have hcomm2 : (yb⁻¹ * σ⁻¹ * yb * σ) ^ 2 = 1 := by
    have e2 : yb⁻¹ * σ⁻¹ * yb * σ = ψ ⟨y⁻¹ * t⁻¹ * y * t, hPH hyt⟩ := by
      calc yb⁻¹ * σ⁻¹ * yb * σ = yb⁻¹ * (σ⁻¹ * yb * σ) := by group
        _ = (ψ ⟨y, hyH⟩)⁻¹ * ψ ⟨t⁻¹ * y * t, hyt'⟩ := by rw [hX]
        _ = ψ ⟨y⁻¹ * t⁻¹ * y * t, hPH hyt⟩ := by
            rw [← map_inv, ← map_mul]
            congr 1
            exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [e2]
    exact hP2 _ hyt
  obtain ⟨hσA, hσ2⟩ := five_mem_four k σ yb hσk hybk hybA hyb3 hyb1 hσ8 hcomm2
  obtain ⟨p₀, hp₀, hψp₀⟩ : ∃ p₀ ∈ P, ∀ hp : p₀ ∈ H, ψ ⟨p₀, hp⟩ = σ := by
    rcases five_four_cases k σ hσk hσA hσ2 a hk haA ha2 ha1' yb hybk hybA hyb3 hyb1 with
      h | h | h | h
    · exact ⟨1, one_mem _, fun _ => by rw [h]; exact map_one ψ⟩
    · exact ⟨p₁, hp₁, fun _ => h.symm⟩
    · refine ⟨y * p₁ * y⁻¹, (mem_normalizer_iff.mp hyP p₁).mp hp₁, fun hp => ?_⟩
      rw [h, hyb, ha, hconjP y hyH hyP p₁ hp₁]
    · have hyP' : y⁻¹ ∈ normalizer (P : Set G) := inv_mem hyP
      refine ⟨y⁻¹ * p₁ * y⁻¹⁻¹, (mem_normalizer_iff.mp hyP' p₁).mp hp₁, fun hp => ?_⟩
      rw [h, hyb, ha, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv])
  refine ⟨p₀, hp₀, fun h hh => ?_⟩
  have hp₀H := hPH hp₀
  have hth := htH' h hh
  have hmem : p₀⁻¹ * (t * h * t⁻¹) * p₀ * h⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hp₀H) hth) hp₀H) (H.inv_mem hh)
  have e : (p₀⁻¹ * t) * h * (p₀⁻¹ * t)⁻¹ * h⁻¹ = p₀⁻¹ * (t * h * t⁻¹) * p₀ * h⁻¹ := by group
  rw [e]
  refine hψ1 ⟨_, hmem⟩ ?_
  have e3 : (⟨_, hmem⟩ : ↥H) = (⟨p₀, hp₀H⟩ : ↥H)⁻¹ * ⟨_, hth⟩ * ⟨p₀, hp₀H⟩ * (⟨h, hh⟩ : ↥H)⁻¹ :=
    rfl
  rw [e3, map_mul, map_mul, map_mul, map_inv, map_inv, hσ' h hh, hψp₀ hp₀H]
  group

section Center

variable {S Z T₀ T : Subgroup G} (hS : Special S Z)
  (hc6 : IsSylowOf 2 S (centralizerMod (normalizer (S : Set G)) S Z))
  (hT₀ : IsSylowOf 2 T₀ (normalizer (S : Set G))) (hTT₀ : T ≤ T₀) (hST : S ≤ T)
include hS hc6 hT₀ hTT₀ hST

theorem centerIn_le_sec2Z_of_le : centerIn T ≤ Z := fun z hz => by
  have hzS : z ∈ S := mem_of_forall_inv_mul_conj_mem hS hc6 hT₀ (hTT₀ hz.1) fun s hs => by
    have h1 : s * z = z * s := mem_centralizer_iff.mp hz.2 s (hST hs)
    have e : s⁻¹ * (z * s * z⁻¹) = 1 := by rw [← h1, mul_inv_cancel_right, inv_mul_cancel]
    rw [e]
    exact one_mem _
  rw [← hS.center]
  exact ⟨hzS, mem_centralizer_iff.mpr fun s hs => mem_centralizer_iff.mp hz.2 s (hST hs)⟩

theorem mem_sec2Z_of_forall_mem_centerIn
    (hc1 : ∀ s ∈ S, s ∉ Z → {c | ∃ t ∈ S, c = s⁻¹ * t⁻¹ * s * t} = (Z : Set G)) {x : G}
    (hx : x ∈ T) (hZ₀ : ¬ Z ≤ centerIn T)
    (hxc : ∀ t ∈ T, x⁻¹ * (t * x * t⁻¹) ∈ centerIn T) : x ∈ Z := by
  have hZT := centerIn_le_sec2Z_of_le hS hc6 hT₀ hTT₀ hST
  have hN : ∀ y ∈ T, y ∈ normalizer (centerIn T : Set G) := fun y hy =>
    mem_normalizer_centerIn (le_normalizer hy)
  have hxS : x ∈ S := mem_of_forall_inv_mul_conj_mem hS hc6 hT₀ (hTT₀ hx) fun s hs => by
    have hc := inv_mem (hxc s (hST hs))
    have e1 : s⁻¹ * (x * s * x⁻¹) =
        x * (s⁻¹ * (x⁻¹ * (s * x * s⁻¹))⁻¹ * s⁻¹⁻¹) * x⁻¹ := by group
    rw [e1]
    have h1 := (mem_normalizer_iff.mp (hN s⁻¹ (inv_mem (hST hs))) _).mp hc
    exact hZT ((mem_normalizer_iff.mp (hN x hx) _).mp h1)
  by_contra hxZ
  apply hZ₀
  intro z hz
  have hz' : z ∈ (Z : Set G) := hz
  rw [← hc1 x hxS hxZ] at hz'
  obtain ⟨t, ht, rfl⟩ := hz'
  have := hxc t⁻¹ (hST (inv_mem ht))
  simpa [mul_assoc] using this

theorem map_upperCentralSeries_two_eq
    (hc1 : ∀ s ∈ S, s ∉ Z → {c | ∃ t ∈ S, c = s⁻¹ * t⁻¹ * s * t} = (Z : Set G))
    (hne : centerIn T ≠ Z) : (Subgroup.upperCentralSeries ↥T 2).map T.subtype = Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZT := centerIn_le_sec2Z_of_le hS hc6 hT₀ hTT₀ hST
  have hZ₀ : ¬ Z ≤ centerIn T := fun h => hne (le_antisymm hZT h)
  have hT2 : IsPGroup 2 T := hT₀.isPGroup.to_le hTT₀
  have hZleT : Z ≤ T := hS.le.trans hST
  have hTZ : ∀ t ∈ T, t ∈ normalizer (Z : Set G) := fun t ht => by
    rw [← hS.center]
    exact mem_normalizer_centerIn (hT₀.le (hTT₀ ht))
  have hcen : ∀ a : ↥T, a ∈ center ↥T ↔ (a : G) ∈ centerIn T := fun a => by
    rw [centerIn_eq_map]
    constructor
    · intro h
      exact ⟨a, h, rfl⟩
    · rintro ⟨b, hb, hba⟩
      rwa [show a = b from Subtype.ext hba.symm]
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    refine mem_sec2Z_of_forall_mem_centerIn hS hc6 hT₀ hTT₀ hST hc1 w.2 hZ₀ fun t ht => ?_
    have hwinv : w⁻¹ ∈ Subgroup.upperCentralSeries ↥T 2 := inv_mem hw
    have h1 := (Subgroup.mem_upperCentralSeries_succ_iff.mp hwinv) ⟨t, ht⟩
    rw [Subgroup.upperCentralSeries_one, hcen, commutatorElement_def] at h1
    simpa [mul_assoc] using h1
  · intro z hz
    have hne1 : centerIn T ≠ ⊥ := by
      have hT1 : T ≠ ⊥ := fun h => by
        have h1 := Subgroup.card_le_of_le (h ▸ hZleT)
        rw [hS.card, card_bot] at h1
        omega
      have h := inf_centerIn_ne_bot hT2 le_rfl le_normalizer hT1
      rwa [inf_eq_right.mpr (show centerIn T ≤ T from inf_le_left)] at h
    have hcard : Nat.card (centerIn T) = 2 := by
      have hdvd : Nat.card (centerIn T) ∣ 2 ^ 2 := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hS.card]
        exact Subgroup.card_dvd_of_le hZT
      have h1 : Nat.card (centerIn T) ≠ 1 := fun h => hne1 (Subgroup.card_eq_one.mp h)
      have h4 : Nat.card (centerIn T) ≠ 4 := fun h =>
        hne (Subgroup.eq_of_le_of_card_ge hZT (by rw [h, hS.card]))
      obtain ⟨i, hi, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact absurd hn h1
      · exact hn
      · exact absurd hn h4
    have hidx : ((centerIn T).subgroupOf Z).index = 2 := by
      have h := Subgroup.card_mul_index ((centerIn T).subgroupOf Z)
      rw [Nat.card_congr (subgroupOfEquivOfLe hZT).toEquiv, hcard, hS.card] at h
      omega
    refine ⟨⟨z, hZleT hz⟩, ?_, rfl⟩
    show (⟨z, hZleT hz⟩ : ↥T) ∈ Subgroup.upperCentralSeries ↥T (1 + 1)
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one, hcen, commutatorElement_def]
    have hw : (y : G) * z * (y : G)⁻¹ ∈ Z := (mem_normalizer_iff.mp (hTZ y y.2) z).mp hz
    have hside : (y : G) * z * (y : G)⁻¹ ∈ centerIn T ↔ z ∈ centerIn T := by
      constructor
      · intro h
        have := (mem_normalizer_iff.mp (mem_normalizer_centerIn (le_normalizer
          (inv_mem y.2))) _).mp h
        simpa [mul_assoc] using this
      · intro h
        exact (mem_normalizer_iff.mp (mem_normalizer_centerIn (le_normalizer y.2)) _).mp h
    have hmem := (mul_mem_iff_of_index_two hidx (a := (⟨z, hz⟩ : ↥Z))
      (b := (⟨_, hw⟩ : ↥Z)⁻¹)).mpr (by
        rw [inv_mem_iff (x := (⟨_, hw⟩ : ↥Z)), mem_subgroupOf, mem_subgroupOf]
        exact hside.symm)
    rw [mem_subgroupOf] at hmem
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmem ⊢
    convert hmem using 1
    group

end Center

section Cent

variable {S Z : Subgroup G} (hS : Special S Z)
include hS

omit [Finite G] in
theorem mem_centralizer_Z_of_forall {w : G} (hw : ∀ s ∈ S, s⁻¹ * (w * s * w⁻¹) ∈ Z) :
    ∀ z ∈ Z, w * z * w⁻¹ = z := by
  have hcom : ∀ z ∈ Z, ∀ s ∈ S, Commute z s := fun z hz s hs => hS.comm_Z hz hs
  have hle : (⁅S, S⁆ : Subgroup G) ≤ centralizer ({w} : Set G) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, mem_centralizer_singleton_iff]
    have hza := hw a ha
    have hzb := hw b hb
    have ea : w * a * w⁻¹ = (a⁻¹ * (w * a * w⁻¹)) * a := by
      rw [(hcom _ hza a ha).eq]
      group
    have eb : w * b * w⁻¹ = (b⁻¹ * (w * b * w⁻¹)) * b := by
      rw [(hcom _ hzb b hb).eq]
      group
    have key : w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ = a * b * a⁻¹ * b⁻¹ := by
      calc w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ = (w * a * w⁻¹) * (w * b * w⁻¹) * (w * a * w⁻¹)⁻¹ *
            (w * b * w⁻¹)⁻¹ := by group
        _ = (a⁻¹ * (w * a * w⁻¹)) * a * ((b⁻¹ * (w * b * w⁻¹)) * b) *
            ((a⁻¹ * (w * a * w⁻¹)) * a)⁻¹ * ((b⁻¹ * (w * b * w⁻¹)) * b)⁻¹ := by
            rw [← ea, ← eb]
        _ = a * b * a⁻¹ * b⁻¹ := commutator_mul_mul_of_commute (hcom _ hza a ha)
            (hcom _ hza b hb) (hcom _ hzb a ha) (hcom _ hzb b hb) (hcom _ hza _ (hS.le hzb))
    calc a * b * a⁻¹ * b⁻¹ * w = w * (w⁻¹ * (a * b * a⁻¹ * b⁻¹) * w) := by group
      _ = w * (a * b * a⁻¹ * b⁻¹) := by
          congr 1
          calc w⁻¹ * (a * b * a⁻¹ * b⁻¹) * w
              = w⁻¹ * (w * (a * b * a⁻¹ * b⁻¹) * w⁻¹) * w := by rw [key]
            _ = a * b * a⁻¹ * b⁻¹ := by group
  intro z hz
  rw [← hS.comm] at hz
  have h1 := mem_centralizer_singleton_iff.mp (hle hz)
  calc w * z * w⁻¹ = z * w * w⁻¹ := by rw [h1]
    _ = z := by group

omit [Finite G] in
theorem mem_centralizer_of_odd_of_forall {w : G} (hwo : Odd (orderOf w))
    (hw : ∀ s ∈ S, s⁻¹ * (w * s * w⁻¹) ∈ Z) : ∀ s ∈ S, w * s * w⁻¹ = s := by
  have hZc := mem_centralizer_Z_of_forall hS hw
  intro s hs
  set z := s⁻¹ * (w * s * w⁻¹) with hz
  have hzZ : z ∈ Z := hw s hs
  have hws : w * s * w⁻¹ = s * z := by rw [hz]; group
  have hpow : ∀ m : ℕ, w ^ m * s * (w ^ m)⁻¹ = s * z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc w ^ (m + 1) * s * (w ^ (m + 1))⁻¹ = w * (w ^ m * s * (w ^ m)⁻¹) * w⁻¹ := by
            rw [pow_succ']
            group
        _ = w * (s * z ^ m) * w⁻¹ := by rw [ih]
        _ = (w * s * w⁻¹) * (w * z ^ m * w⁻¹) := by group
        _ = s * z * z ^ m := by rw [hZc _ (pow_mem hzZ m), hws]
        _ = s * z ^ (m + 1) := by rw [pow_succ']; group
  have hn := hpow (orderOf w)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hn
  have hzn : z ^ orderOf w = 1 := by
    have := congrArg (fun v => s⁻¹ * v) hn
    simpa using this.symm
  obtain ⟨k, hk⟩ := hwo
  have hz2 : z * z = 1 := hS.elem z hzZ
  have hz1 : z = 1 := by
    rw [hk, pow_succ, pow_mul, sq, hz2, one_pow, one_mul] at hzn
    exact hzn
  rw [hws, hz1, mul_one]

end Cent

theorem mem_sec2S_of_mem_I {A R : Subgroup G} {g : G} {E F : Subgroup G} (h21 : Step21)
    (h24 : Step24) (h26 : Step26) (h211 : Step211) (hS : Sec2Setting G A R g E F)
    {I : Subgroup G} (hSI : sec2S A R E F ≤ I) (hIO : I ⊓ AS76b.oddCoreIn (sec2K E) = ⊥)
    {w : G} (hwI : w ∈ I) (hwS : w ∈ normalizer (sec2S A R E F : Set G))
    (hw : ∀ s ∈ sec2S A R E F, s⁻¹ * (w * s * w⁻¹) ∈ sec2Z A E F) : w ∈ sec2S A R E F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSp := special_of h24 hS
  obtain ⟨-, -, -, -, -, hc6, -, -, -⟩ := h26 G A R g E F hS
  set S := sec2S A R E F with hSdef
  set Z := sec2Z A E F with hZdef
  set W := I ⊓ centralizerMod (normalizer (S : Set G)) S Z with hW
  have hmemC : ∀ v ∈ normalizer (S : Set G), (∀ s ∈ S, s⁻¹ * (v * s * v⁻¹) ∈ Z) →
      v ∈ centralizerMod (normalizer (S : Set G)) S Z := by
    intro v hv hvs
    have hvZ : v ∈ normalizer (Z : Set G) := by
      rw [← hSp.center]
      exact mem_normalizer_centerIn hv
    refine ⟨hv, hvZ, fun y hy => ?_⟩
    have hy' : v⁻¹ * y * v ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem hv) y).mp hy
      simpa using this
    have h1 := hvs _ hy'
    have e : y⁻¹ * v⁻¹ * y * v = ((v⁻¹ * y * v)⁻¹ * (v * (v⁻¹ * y * v) * v⁻¹))⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hSW : S ≤ W := le_inf hSI hc6.le
  have hWsyl : IsSylowOf 2 S W := hc6.of_le hSW inf_le_right
  have hWS : W = S := by
    by_contra hne
    have hidx : ¬ 2 ∣ S.relIndex W := (isSylowOf_iff.mp hWsyl).2.2
    have hidx1 : S.relIndex W ≠ 1 := fun h => hne (le_antisymm
      (fun x hx => relIndex_eq_one.mp h hx) hSW)
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hidx1
    have hq2 : q ≠ 2 := fun h => hidx (h ▸ hqdvd)
    have hqW : q ∣ Nat.card W := by
      have h := relIndex_mul_card S W
      rw [inf_eq_left.mpr hSW] at h
      exact hqdvd.trans ⟨_, h.symm⟩
    have : Fact q.Prime := ⟨hq⟩
    have := Fintype.ofFinite ↥W
    rw [Nat.card_eq_fintype_card] at hqW
    obtain ⟨⟨v, hvW⟩, hvq⟩ := exists_prime_orderOf_dvd_card q hqW
    have hvq' : orderOf v = q := by
      rw [← hvq]
      exact Subgroup.orderOf_coe (⟨v, hvW⟩ : ↥W)
    have hv1 : v ≠ 1 := fun h => by
      rw [h, orderOf_one] at hvq'
      exact hq.one_lt.ne' hvq'.symm
    have hvo : Odd (orderOf v) := by rw [hvq']; exact hq.odd_of_ne_two hq2
    have hvinv := inv_mem (mem_inf.mp hvW).2
    have hvs : ∀ s ∈ S, s⁻¹ * (v * s * v⁻¹) ∈ Z := fun s hs => by
      have h1 := (mem_centralizerMod.mp hvinv).2.2 s hs
      simpa [mul_assoc] using h1
    have hvc := mem_centralizer_of_odd_of_forall hSp hvo hvs
    have hvC : v ∈ centralizer (S : Set G) := mem_centralizer_iff.mpr fun s hs => by
      have := hvc s hs
      calc s * v = v * s * v⁻¹ * v := by rw [this]
        _ = v * s := by group
    have hvO := oddCoreIn_centralizer_le_oddCoreIn_sec2K h21 h211 hS
      (mem_oddCoreIn_centralizer_S h24 h26 hS hvC hvo)
    have hvIO : v ∈ I ⊓ AS76b.oddCoreIn (sec2K E) := ⟨(mem_inf.mp hvW).1, hvO⟩
    rw [hIO, mem_bot] at hvIO
    exact hv1 hvIO
  rw [← hWS]
  exact ⟨hwI, hmemC w hwS hw⟩

section Mat

variable {S Z H : Subgroup G} (C : Coord S Z H) (hS : Special S Z)
  (hHS : H ≤ normalizer (S : Set G)) (hSH : normalizer (S : Set G) ≤ normalizer (H : Set G))
include C hS hHS hSH

omit [Finite G] C hS hHS hSH in
theorem card_units_mat2 : Fintype.card {M : Mat2 // ∃ N : Mat2, matMul M N = matOne} = 6 := by
  decide

omit [Finite G] C hS hHS hSH in
theorem card_units_mat2' : Nat.card {M : Mat2 // ∃ N : Mat2, matMul M N = matOne} = 6 := by
  rw [Nat.card_eq_fintype_card]
  exact card_units_mat2

omit [Finite G] in
theorem card_le_six_mul {D : Subgroup G} (hSD : S ≤ D) (hDN : D ≤ normalizer (S : Set G))
    (hDH : ∀ g ∈ D, ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ S)
    (hDS : ∀ g ∈ D, (∀ s ∈ S, s⁻¹ * (g * s * g⁻¹) ∈ Z) → g ∈ S) :
    Nat.card D ≤ 6 * Nat.card S := by
  classical
  have hM : ∀ g : ↥D, ∃ M : Mat2, ∀ s ∈ S, C.Ψ ((g : G) * s * (g : G)⁻¹) = matAct M (C.Ψ s) :=
    fun g => C.exists_mat_of_mem hS hHS hSH (hDN g.2) (hDH g g.2)
  choose M hMs using hM
  have heq : ∀ {A B : Mat2}, (∀ s ∈ S, matAct A (C.Ψ s) = matAct B (C.Ψ s)) → A = B := by
    intro A B h
    refine mat_eq_of_matAct fun m hm1 hm2 => ?_
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    rw [Prod.mk.eta] at hsm
    rw [← hsm]
    exact h s hs
  have hgs : ∀ (g : ↥D) {a : G}, a ∈ S → (g : G) * a * (g : G)⁻¹ ∈ S := fun g a ha =>
    (mem_normalizer_iff.mp (hDN g.2) a).mp ha
  have hmul : ∀ g g' : ↥D, M (g * g') = matMul (M g) (M g') := by
    intro g g'
    refine heq fun s hs => ?_
    rw [← hMs _ s hs, matAct_matMul, ← hMs g' s hs, ← hMs g _ (hgs g' hs)]
    congr 1
    simp only [Subgroup.coe_mul]
    group
  have hone : M 1 = matOne := heq fun s hs => by
    rw [← hMs 1 s hs, matAct_matOne]
    congr 1
    simp
  have hmemS : ∀ g : ↥D, (g : G) ∈ S → M g = matOne := by
    intro g hg
    refine heq fun s hs => ?_
    rw [← hMs g s hs, matAct_matOne, C.Ψ_conj_S hS hg hs]
  have hinj : ∀ g g' : ↥D, M g = M g' → ((g⁻¹ * g' : ↥D) : G) ∈ S := by
    intro g g' h
    refine hDS _ (g⁻¹ * g').2 fun s hs => ?_
    have h1 : C.Ψ ((g : G) * s⁻¹ * (g : G)⁻¹) = C.Ψ ((g' : G) * s⁻¹ * (g' : G)⁻¹) := by
      rw [hMs g _ (S.inv_mem hs), hMs g' _ (S.inv_mem hs), h]
    rw [C.Ψ_eq_iff hS (hgs g (S.inv_mem hs)) (hgs g' (S.inv_mem hs))] at h1
    have hgZ : (g : G)⁻¹ ∈ normalizer (Z : Set G) := by
      rw [← hS.center]
      exact mem_normalizer_centerIn (inv_mem (hDN g.2))
    have h2 := (mem_normalizer_iff.mp hgZ _).mp h1
    have e : s⁻¹ * (((g : G)⁻¹ * g') * s * ((g : G)⁻¹ * g')⁻¹) =
        ((g : G)⁻¹ * ((g : G) * s⁻¹ * (g : G)⁻¹ * ((g' : G) * s⁻¹ * (g' : G)⁻¹)⁻¹) *
          (g : G)⁻¹⁻¹) := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact h2
  let f : ↥D ⧸ S.subgroupOf D → {A : Mat2 // ∃ N : Mat2, matMul A N = matOne} :=
    Quotient.lift (fun g => ⟨M g, ⟨M g⁻¹, by rw [← hmul, mul_inv_cancel, hone]⟩⟩) (by
      intro g g' hgg'
      have h1 : (g⁻¹ * g' : ↥D) ∈ S.subgroupOf D := QuotientGroup.leftRel_apply.mp hgg'
      rw [mem_subgroupOf] at h1
      apply Subtype.ext
      show M g = M g'
      calc M g = matMul (M g) matOne := by
            refine heq fun s hs => ?_
            rw [matAct_matMul, matAct_matOne]
        _ = matMul (M g) (M (g⁻¹ * g')) := by rw [hmemS _ h1]
        _ = M g' := by rw [← hmul, mul_inv_cancel_left])
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H g => ?_
    induction b using QuotientGroup.induction_on with | H g' => ?_
    have h1 : M g = M g' := congrArg Subtype.val hab
    apply QuotientGroup.eq.mpr
    rw [mem_subgroupOf]
    exact hinj g g' h1
  have hcardQ : Nat.card (↥D ⧸ S.subgroupOf D) ≤ 6 := by
    rw [← card_units_mat2']
    exact Nat.card_le_card_of_injective f hf
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf D)
  rw [Nat.card_congr (subgroupOfEquivOfLe hSD).toEquiv] at h
  rw [h]
  exact Nat.mul_le_mul_right _ hcardQ

end Mat

section Phi

abbrev ZSharp (Z : Subgroup G) : Type := {z : ↥Z // z ≠ 1}

omit [Finite G] in
theorem card_zSharp {Z : Subgroup G} [Finite Z] (h4 : Nat.card Z = 4) :
    Nat.card (ZSharp Z) = 3 := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥Z))
  rw [Finite.card_option, h4] at h
  show Nat.card {z : ↥Z // z ≠ 1} = 3
  omega

omit [Finite G] in
theorem conj_mem_zSharp {Z : Subgroup G} {g : G} (hg : g ∈ normalizer (Z : Set G))
    (z : ZSharp Z) : g * (z : G) * g⁻¹ ∈ Z ∧ g * (z : G) * g⁻¹ ≠ 1 :=
  ⟨(mem_normalizer_iff.mp hg z).mp z.1.2, fun h => z.2 (Subtype.ext (by
    rw [Subgroup.coe_one]
    calc ((z : ↥Z) : G) = g⁻¹ * (g * (z : G) * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group))⟩

@[expose] noncomputable def zConj (Z : Subgroup G) :
    ↥(normalizer (Z : Set G)) →* Equiv.Perm (ZSharp Z) where
  toFun g :=
    { toFun := fun z => ⟨⟨_, (conj_mem_zSharp g.2 z).1⟩, fun h =>
        (conj_mem_zSharp g.2 z).2 (congrArg Subtype.val h)⟩
      invFun := fun z => ⟨⟨_, (conj_mem_zSharp (inv_mem g.2) z).1⟩, fun h =>
        (conj_mem_zSharp (inv_mem g.2) z).2 (congrArg Subtype.val h)⟩
      left_inv := fun z => Subtype.ext (Subtype.ext (by simp only; group))
      right_inv := fun z => Subtype.ext (Subtype.ext (by simp only; group)) }
  map_one' := Equiv.ext fun z => Subtype.ext (Subtype.ext (by simp))
  map_mul' g g' := Equiv.ext fun z => Subtype.ext (Subtype.ext (by
    simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply, Subgroup.coe_mul]
    group))

omit [Finite G] in
theorem zConj_apply (Z : Subgroup G) (g : ↥(normalizer (Z : Set G))) (z : ZSharp Z) :
    ((zConj Z g z : ↥Z) : G) = g * (z : G) * (g : G)⁻¹ := rfl

omit [Finite G] in
theorem zConj_eq_one_iff (Z : Subgroup G) (g : ↥(normalizer (Z : Set G))) :
    zConj Z g = 1 ↔ ∀ z ∈ Z, (g : G) * z * (g : G)⁻¹ = z := by
  constructor
  · intro h z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      group
    · have := congrArg (fun π : Equiv.Perm (ZSharp Z) => ((π ⟨⟨z, hz⟩, fun h => hz1
        (congrArg Subtype.val h)⟩ : ↥Z) : G)) h
      simpa [zConj_apply] using this
  · intro h
    exact Equiv.ext fun z => Subtype.ext (Subtype.ext (by
      rw [zConj_apply]
      exact h z z.1.2))

theorem perm3_gen : ∀ ρ τ π : Equiv.Perm (Fin 3), ρ ^ 3 = 1 → ρ ≠ 1 → τ ^ 2 = 1 → τ ≠ 1 →
    ∃ i : Fin 3, ∃ j : Fin 2, π = ρ ^ (i : ℕ) * τ ^ (j : ℕ) := by
  decide

end Phi

theorem exists_phi_of {S Z H T : Subgroup G} (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hSH : normalizer (S : Set G) ≤ normalizer (H : Set G))
    (hSHle : S ≤ H) (hHZ : H ≤ centralizer (Z : Set G)) {x c : G} (hx3 : orderOf x = 3)
    (hxS : x ∈ normalizer (S : Set G)) (hxH' : ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S)
    (hxZ : ¬ ∀ z ∈ Z, x * z * x⁻¹ = z) (hcT : c ∈ T) (hcZ : ¬ ∀ z ∈ Z, c * z * c⁻¹ = z)
    (hcH : ∀ h ∈ H, c * h * c⁻¹ * h⁻¹ ∈ S) (hc2 : c * c ∈ S)
    (hTS : T ≤ normalizer (S : Set G)) (hTH : ∀ τ ∈ T, τ ∈ H ∨ c⁻¹ * τ ∈ H)
    (hTA : ∀ τ ∈ T, ∃ p ∈ H, ∀ h ∈ H, (p⁻¹ * τ) * h * (p⁻¹ * τ)⁻¹ * h⁻¹ ∈ S)
    (hD : Nat.card (zpowers x ⊔ zpowers c ⊔ S : Subgroup G) ≤ 6 * Nat.card S) :
    ∃ φ : ↥(H ⊔ zpowers x ⊔ T) →* Equiv.Perm (Fin 3) × alternatingGroup (Fin 5),
      Function.Surjective φ ∧ φ.ker = S.subgroupOf (H ⊔ zpowers x ⊔ T) := by
  classical
  set X := H ⊔ zpowers x ⊔ T with hX
  have hZN : normalizer (S : Set G) ≤ normalizer (Z : Set G) := fun n hn => by
    rw [← hS.center]
    exact mem_normalizer_centerIn hn
  have hxH : x ∈ normalizer (H : Set G) := hSH hxS
  have hXS : X ≤ normalizer (S : Set G) := sup_le (sup_le hHS (zpowers_le.mpr hxS)) hTS
  have hXM : X ≤ normalizer (H : Set G) ⊓ normalizer (S : Set G) :=
    le_inf (hXS.trans hSH) hXS
  have hXZ : X ≤ normalizer (Z : Set G) := hXS.trans hZN
  have hZ3 := card_zSharp (Z := Z) hS.card
  let e : ZSharp Z ≃ Fin 3 := (Finite.equivFin _).trans (finCongr hZ3)
  let φ₁ : ↥X →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom e).toMonoidHom.comp ((zConj Z).comp (Subgroup.inclusion hXZ))
  have hφ₁ : ∀ g : ↥X, φ₁ g = 1 ↔ ∀ z ∈ Z, (g : G) * z * (g : G)⁻¹ = z := by
    intro g
    have h := zConj_eq_one_iff Z (Subgroup.inclusion hXZ g)
    simp only [Subgroup.coe_inclusion] at h
    rw [← h]
    simp only [φ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      exact (Equiv.permCongrHom e).injective (h.trans (map_one _).symm)
    · intro h
      rw [h, map_one]
  let σX : ↥X →* Equiv.Perm (Fin 5) :=
    (autAltFive.symm.toMonoidHom.comp (autOfConjHHom C.φ C.surj C.ker)).comp
      (Subgroup.inclusion hXM)
  have hσX : ∀ (g : ↥X) (h : ↥H),
      ((C.φ (conjOnH (g : G) (hXM g.2).1 h) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) =
        σX g * (C.φ h : Equiv.Perm (Fin 5)) * (σX g)⁻¹ := by
    intro g h
    rw [← autOfConjH_apply C.φ C.surj C.ker (hXM g.2).1 (hXM g.2).2, ← autAltFive_apply]
    simp only [σX, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hσH : ∀ (g : ↥X) (hg : (g : G) ∈ H), σX g = (C.φ ⟨g, hg⟩ : Equiv.Perm (Fin 5)) := by
    intro g hg
    set τ := ((C.φ ⟨g, hg⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) with hτ
    have h1 : τ⁻¹ * σX g = 1 := by
      apply eq_one_of_forall_conj_eq
      intro b
      obtain ⟨h, rfl⟩ := C.surj b
      have e1 := hσX g h
      have e2 : ((C.φ (conjOnH (g : G) (hXM g.2).1 h) : alternatingGroup (Fin 5)) :
          Equiv.Perm (Fin 5)) = τ * (C.φ h : Equiv.Perm (Fin 5)) * τ⁻¹ := by
        have : conjOnH (g : G) (hXM g.2).1 h = ⟨g, hg⟩ * h * (⟨g, hg⟩ : ↥H)⁻¹ :=
          Subtype.ext (by simp [conjOnH_apply])
        rw [this, map_mul, map_mul, map_inv]
        rfl
      calc τ⁻¹ * σX g * (C.φ h : Equiv.Perm (Fin 5)) * (τ⁻¹ * σX g)⁻¹ =
          τ⁻¹ * (σX g * (C.φ h : Equiv.Perm (Fin 5)) * (σX g)⁻¹) * τ := by group
        _ = τ⁻¹ * (τ * (C.φ h : Equiv.Perm (Fin 5)) * τ⁻¹) * τ := by rw [← e1, e2]
        _ = (C.φ h : Equiv.Perm (Fin 5)) := by group
    calc σX g = τ * (τ⁻¹ * σX g) := by group
      _ = τ := by rw [h1, mul_one]
  have hσC : ∀ g : ↥X, (∀ h ∈ H, (g : G) * h * (g : G)⁻¹ * h⁻¹ ∈ S) → σX g = 1 := by
    intro g hgH
    apply eq_one_of_forall_conj_eq
    intro b
    obtain ⟨h, rfl⟩ := C.surj b
    rw [← hσX g h]
    have hk : (conjOnH (g : G) (hXM g.2).1 h) * h⁻¹ ∈ C.φ.ker := by
      rw [C.ker, mem_subgroupOf]
      simpa [conjOnH_apply] using hgH h h.2
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hk
    rw [hk]
  have hxH'' : ∀ h ∈ H, x * h * x⁻¹ * h⁻¹ ∈ S := by
    intro h hh
    have hxh : x * h * x⁻¹ ∈ H := (mem_normalizer_iff.mp hxH h).mp hh
    have h1 := hxH' _ hxh
    have h2 := (mem_normalizer_iff.mp (hHS hh) _).mp h1
    have e : x * h * x⁻¹ * h⁻¹ =
        h * (x⁻¹ * (x * h * x⁻¹)⁻¹ * x * (x * h * x⁻¹)) * h⁻¹ := by group
    rw [e]
    exact h2
  have hxX : x ∈ X := mem_sup_left (mem_sup_right (mem_zpowers x))
  have hcX : c ∈ X := mem_sup_right hcT
  have hrange : ∀ g : ↥X, σX g ∈ alternatingGroup (Fin 5) := by
    let L : Subgroup G := ((alternatingGroup (Fin 5)).comap σX).map X.subtype
    have hL : ∀ g : ↥X, σX g ∈ alternatingGroup (Fin 5) → (g : G) ∈ L :=
      fun g hg => ⟨g, hg, rfl⟩
    have hXL : X ≤ L := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro h hh
        have hhX : h ∈ X := mem_sup_left (mem_sup_left hh)
        refine hL ⟨h, hhX⟩ ?_
        rw [hσH ⟨h, hhX⟩ hh]
        exact (C.φ _).2
      · rw [zpowers_le]
        refine hL ⟨x, hxX⟩ ?_
        rw [hσC ⟨x, hxX⟩ hxH'']
        exact one_mem _
      · intro τ hτ
        have hτX : τ ∈ X := mem_sup_right hτ
        obtain ⟨p, hp, hpτ⟩ := hTA τ hτ
        have hpX : p ∈ X := mem_sup_left (mem_sup_left hp)
        have hc'X : p⁻¹ * τ ∈ X := X.mul_mem (X.inv_mem hpX) hτX
        have e : (⟨τ, hτX⟩ : ↥X) = ⟨p, hpX⟩ * ⟨p⁻¹ * τ, hc'X⟩ := Subtype.ext (by simp)
        refine hL ⟨τ, hτX⟩ ?_
        rw [e, map_mul, hσH ⟨p, hpX⟩ hp, hσC ⟨_, hc'X⟩ hpτ, mul_one]
        exact (C.φ _).2
    intro g
    obtain ⟨g', hg', hgg'⟩ := hXL g.2
    rw [show g = g' from Subtype.ext hgg'.symm]
    exact hg'
  let φ₂ : ↥X →* alternatingGroup (Fin 5) := σX.codRestrict _ hrange
  have hφ₂ : ∀ g : ↥X, ((φ₂ g : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = σX g :=
    fun _ => rfl
  have hφ₁H : ∀ g : ↥X, (g : G) ∈ H → φ₁ g = 1 := fun g hg => (hφ₁ g).mpr fun z hz => by
    have h1 : z * g = g * z := mem_centralizer_iff.mp (hHZ hg) z hz
    rw [← h1]
    group
  have hφ₂H : ∀ (g : ↥X) (hg : (g : G) ∈ H), φ₂ g = C.φ ⟨g, hg⟩ := fun g hg =>
    Subtype.ext (by rw [hφ₂, hσH g hg])
  have hφ₂C : ∀ g : ↥X, (∀ h ∈ H, (g : G) * h * (g : G)⁻¹ * h⁻¹ ∈ S) → φ₂ g = 1 :=
    fun g hg => Subtype.ext (by rw [hφ₂, hσC g hg]; rfl)
  have hx1 : φ₁ ⟨x, hxX⟩ ≠ 1 := fun h => hxZ ((hφ₁ _).mp h)
  have hc1 : φ₁ ⟨c, hcX⟩ ≠ 1 := fun h => hcZ ((hφ₁ _).mp h)
  have hx3' : φ₁ ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have e : (⟨x, hxX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by rw [← hx3]; simp [pow_orderOf_eq_one])
    rw [e, map_one]
  have hc2' : φ₁ ⟨c, hcX⟩ ^ 2 = 1 := by
    rw [← map_pow, sq]
    exact hφ₁H _ (hSHle hc2)
  set D : Subgroup G := zpowers x ⊔ zpowers c ⊔ S with hDdef
  have hcN : c ∈ normalizer (H : Set G) := hSH (hTS hcT)
  have hDH : D ≤ normalizer (H : Set G) :=
    sup_le (sup_le (zpowers_le.mpr hxH) (zpowers_le.mpr hcN)) (hSHle.trans le_normalizer)
  have hXD : X ≤ H ⊔ D := by
    refine sup_le (sup_le le_sup_left ?_) fun τ hτ => ?_
    · exact (zpowers_le.mpr (mem_sup_left (mem_sup_left (mem_zpowers x)))).trans le_sup_right
    · rcases hTH τ hτ with h | h
      · exact mem_sup_left h
      · have e : τ = c * (c⁻¹ * τ) := by group
        rw [e]
        exact mul_mem (mem_sup_right (mem_sup_left (mem_sup_right (mem_zpowers c))))
          (mem_sup_left h)
  have hH60 : Nat.card H = 60 * Nat.card S := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup C.φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective C.φ C.surj).toEquiv, C.ker,
      Nat.card_congr (subgroupOfEquivOfLe hSHle).toEquiv, Sec2V4.card_alternatingGroup_five] at h
    exact h
  have hXcard : Nat.card X ≤ 360 * Nat.card S := by
    have h1 := card_sup_mul_card_inf hDH
    have h2 : Nat.card S ≤ Nat.card (H ⊓ D : Subgroup G) :=
      Subgroup.card_le_of_le (le_inf hSHle le_sup_right)
    have h3 : Nat.card X ≤ Nat.card (H ⊔ D : Subgroup G) := Subgroup.card_le_of_le hXD
    have hpos : 0 < Nat.card S := Nat.card_pos
    have h4 : Nat.card (H ⊔ D : Subgroup G) * Nat.card S ≤ 360 * Nat.card S * Nat.card S :=
      calc Nat.card (H ⊔ D : Subgroup G) * Nat.card S
          ≤ Nat.card (H ⊔ D : Subgroup G) * Nat.card (H ⊓ D : Subgroup G) :=
            Nat.mul_le_mul_left _ h2
        _ = Nat.card H * Nat.card D := h1
        _ ≤ 60 * Nat.card S * (6 * Nat.card S) := by rw [hH60]; exact Nat.mul_le_mul_left _ hD
        _ = 360 * Nat.card S * Nat.card S := by ring
    exact h3.trans (Nat.le_of_mul_le_mul_right h4 hpos)
  have hsurj : Function.Surjective (φ₁.prod φ₂) := by
    rintro ⟨π, b⟩
    obtain ⟨i, j, hij⟩ := perm3_gen _ _ π hx3' hx1 hc2' hc1
    obtain ⟨h, rfl⟩ := C.surj b
    have hhX : (h : G) ∈ X := mem_sup_left (mem_sup_left h.2)
    refine ⟨⟨x, hxX⟩ ^ (i : ℕ) * ⟨c, hcX⟩ ^ (j : ℕ) * ⟨h, hhX⟩, Prod.ext ?_ ?_⟩
    · simp only [MonoidHom.prod_apply, map_mul, map_pow, Prod.fst_mul, Prod.pow_fst]
      rw [hφ₁H ⟨h, hhX⟩ h.2, mul_one, hij]
    · simp only [MonoidHom.prod_apply, map_mul, map_pow, Prod.snd_mul, Prod.pow_snd]
      rw [hφ₂C ⟨x, hxX⟩ hxH'', hφ₂C ⟨c, hcX⟩ hcH, hφ₂H ⟨h, hhX⟩ h.2, one_pow, one_pow,
        one_mul, one_mul]
  refine ⟨φ₁.prod φ₂, hsurj, ?_⟩
  have hSker : S.subgroupOf X ≤ (φ₁.prod φ₂).ker := by
    intro g hg
    rw [mem_subgroupOf] at hg
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, hφ₁H g (hSHle hg), hφ₂H g (hSHle hg)]
    have h1 : (⟨g, hSHle hg⟩ : ↥H) ∈ C.φ.ker := by rw [C.ker, mem_subgroupOf]; exact hg
    rw [MonoidHom.mem_ker.mp h1]
    rfl
  refine (Subgroup.eq_of_le_of_card_ge hSker ?_).symm
  have hcardX : Nat.card X = 360 * Nat.card (φ₁.prod φ₂).ker := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ₁.prod φ₂).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
      Nat.card_prod, Sec2V4.card_alternatingGroup_five, Nat.card_perm, Nat.card_fin] at h
    rw [h]
    rfl
  rw [Nat.card_congr (subgroupOfEquivOfLe (show S ≤ X from
    fun s hs => mem_sup_left (mem_sup_left (hSHle hs)))).toEquiv]
  have := hXcard
  rw [hcardX] at this
  omega

omit [Finite G] in
theorem exists_mem_I_of {S Z H I O : Subgroup G} (hS : Special S Z) (hSI : S ≤ I)
    (hOI : O ≤ centralizer (I : Set G)) (hIO : I ⊓ O = ⊥) (hOH : O ≤ centralizer (H : Set G))
    {x₀ : G} (hx₀ : x₀ ∈ I ⊔ O) (hx₀F4 : ActsAsF4Scalar x₀ S Z)
    (hx₀cl : closure {c | ∃ w ∈ Z, c = w⁻¹ * x₀⁻¹ * w * x₀} = Z) (hx₀3 : x₀ ^ 3 = 1)
    (hx₀H : x₀ ∈ normalizer (H : Set G)) (hx₀H' : ∀ h ∈ H, x₀⁻¹ * h⁻¹ * x₀ * h ∈ S) :
    ∃ x ∈ I, orderOf x = 3 ∧ ActsAsF4Scalar x S Z ∧
      closure {c | ∃ w ∈ Z, c = w⁻¹ * x⁻¹ * w * x} = Z ∧ x ∈ normalizer (H : Set G) ∧
      ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hIOc : I ≤ centralizer (O : Set G) := Subgroup.le_centralizer_iff.mp hOI
  obtain ⟨i, hi, o, ho, rfl, hio⟩ := NXKernel.exists_mul_of_mem_sup hIOc hx₀
  have hoS : ∀ s ∈ S, s * o = o * s := fun s hs => mem_centralizer_iff.mp (hOI ho) s (hSI hs)
  have hoH : ∀ h ∈ H, h * o = o * h := fun h hh => mem_centralizer_iff.mp (hOH ho) h hh
  have hoN : ∀ {K : Subgroup G}, (∀ k ∈ K, k * o = o * k) → o ∈ normalizer (K : Set G) :=
    fun hK => centralizer_le_normalizer _ (mem_centralizer_iff.mpr hK)
  have hie : i = i * o * o⁻¹ := by group
  have hiS : i ∈ normalizer (S : Set G) := by
    rw [hie]
    exact mul_mem hx₀F4.1 (inv_mem (hoN hoS))
  have hiH : i ∈ normalizer (H : Set G) := by
    rw [hie]
    exact mul_mem hx₀H (inv_mem (hoN hoH))
  have hconj : ∀ {K : Subgroup G}, i ∈ normalizer (K : Set G) → (∀ k ∈ K, k * o = o * k) →
      ∀ k ∈ K, (i * o)⁻¹ * k * (i * o) = i⁻¹ * k * i := by
    intro K hiK hoK k hk
    have hk' : i⁻¹ * k * i ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hiK) k).mp hk
      simpa using this
    calc (i * o)⁻¹ * k * (i * o) = o⁻¹ * (i⁻¹ * k * i) * o := by group
      _ = o⁻¹ * (o * (i⁻¹ * k * i)) := by rw [mul_assoc, hoK _ hk']
      _ = i⁻¹ * k * i := by group
  have hcS := hconj hiS hoS
  have hcH := hconj hiH hoH
  have hiS' : ∀ s ∈ S, i⁻¹ * s * i ∈ S := fun s hs => by
    have := (mem_normalizer_iff.mp (inv_mem hiS) s).mp hs
    simpa using this
  have hiZ : i ∈ normalizer (Z : Set G) := by
    rw [← hS.center]
    exact mem_normalizer_centerIn hiS
  have hi3 : i ^ 3 = 1 := by
    have hc : Commute i o := hio
    have h1 : i ^ 3 * o ^ 3 = 1 := by rw [← hc.mul_pow]; exact hx₀3
    have h2 : i ^ 3 = (o ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : i ^ 3 ∈ I ⊓ O :=
      mem_inf.mpr ⟨pow_mem hi 3, by rw [h2]; exact inv_mem (pow_mem ho 3)⟩
    rw [hIO, mem_bot] at h3
    exact h3
  have hi1 : i ≠ 1 := by
    rintro rfl
    have hZ1 : Z = ⊥ := by
      rw [← hx₀cl, eq_bot_iff, closure_le]
      rintro c ⟨w, hw, rfl⟩
      have := hoS w (hS.le hw)
      rw [one_mul, SetLike.mem_coe, mem_bot]
      calc w⁻¹ * o⁻¹ * w * o = w⁻¹ * o⁻¹ * (w * o) := by group
        _ = w⁻¹ * o⁻¹ * (o * w) := by rw [this]
        _ = 1 := by group
    have h4 := hS.card
    rw [hZ1, card_bot] at h4
    omega
  refine ⟨i, hi, orderOf_eq_prime hi3 hi1, ⟨hiS, hiZ, fun s hs => ?_⟩, ?_, hiH, fun h hh => ?_⟩
  · have h1 := hx₀F4.2.2 s hs
    have e1 := hcS s hs
    have e2 : (i * o)⁻¹ * (i * o)⁻¹ * s * (i * o) * (i * o) = i⁻¹ * i⁻¹ * s * i * i := by
      calc (i * o)⁻¹ * (i * o)⁻¹ * s * (i * o) * (i * o) =
          (i * o)⁻¹ * ((i * o)⁻¹ * s * (i * o)) * (i * o) := by group
        _ = (i * o)⁻¹ * (i⁻¹ * s * i) * (i * o) := by rw [e1]
        _ = i⁻¹ * (i⁻¹ * s * i) * i := hcS _ (hiS' s hs)
        _ = i⁻¹ * i⁻¹ * s * i * i := by group
    rw [e1, e2] at h1
    exact h1
  · have hset : {c | ∃ w ∈ Z, c = w⁻¹ * i⁻¹ * w * i} =
        {c | ∃ w ∈ Z, c = w⁻¹ * (i * o)⁻¹ * w * (i * o)} := by
      ext c
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w, hw, ?_⟩
        have := hcS w (hS.le hw)
        calc w⁻¹ * i⁻¹ * w * i = w⁻¹ * (i⁻¹ * w * i) := by group
          _ = w⁻¹ * ((i * o)⁻¹ * w * (i * o)) := by rw [this]
          _ = w⁻¹ * (i * o)⁻¹ * w * (i * o) := by group
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w, hw, ?_⟩
        have := hcS w (hS.le hw)
        calc w⁻¹ * (i * o)⁻¹ * w * (i * o) = w⁻¹ * ((i * o)⁻¹ * w * (i * o)) := by group
          _ = w⁻¹ * (i⁻¹ * w * i) := by rw [this]
          _ = w⁻¹ * i⁻¹ * w * i := by group
    rw [hset]
    exact hx₀cl
  · have h1 := hx₀H' h hh
    have e1 := hcH h⁻¹ (H.inv_mem hh)
    have e : i⁻¹ * h⁻¹ * i * h = (i * o)⁻¹ * h⁻¹ * (i * o) * h := by rw [e1]
    rw [e]
    exact h1

theorem matAct_add (A B : Mat2) (m : Pair) :
    matAct (fun i j => A i j + B i j) m = matAct A m + matAct B m := by
  simp only [matAct, add_smul, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> simp only <;> abel

theorem matAct_ord3 (X : Mat2) (m : Pair) :
    matAct (fun i j => matMul X X i j + X i j + matOne i j) m =
      matAct X (matAct X m) + matAct X m + m := by
  have h1 := matAct_add (fun i j => matMul X X i j + X i j) matOne m
  have h2 := matAct_add (matMul X X) X m
  rw [h1, h2, matAct_matMul, matAct_matOne]

theorem invol_ord3 : ∀ (k : Fin 3) (i : Fin 2),
    matMul (matMul (matMul (invol k) (ord3 i)) (invol k)) (ord3 i) = matOne := by
  decide

section Setting2

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_phi_sec2T
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (h21 : Step21) (h23 : Step23) (h24 : Step24) (h26 : Step26) (h27 : Step27)
    (h211 : Step211) (hS : Sec2Setting G A R g E F) (hFK : F ≤ sec2K E) {T₀ : Subgroup G}
    (hPST : sec2P E ⊔ sec2S A R E F ≤ T₀)
    (hT₀s : IsSylowOf 2 T₀ (normalizer (sec2S A R E F : Set G)))
    (hT₀P : T₀ ≤ normalizer (sec2P E : Set G))
    (hidx : (sec2P E ⊔ sec2S A R E F).relIndex (sec2T E T₀) = 2) :
    (∃ x : G, orderOf x = 3 ∧ ActsAsF4Scalar x (sec2S A R E F) (sec2Z A E F) ∧
      closure {c | ∃ w ∈ sec2Z A E F, c = w⁻¹ * x⁻¹ * w * x} = sec2Z A E F ∧
      x ∈ normalizer (sec2H E F : Set G) ∧
      (∀ h ∈ sec2H E F, x⁻¹ * h⁻¹ * x * h ∈ sec2S A R E F) ∧
      ∃ φ : ↥(sec2H E F ⊔ zpowers x ⊔ sec2T E T₀) →*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 5),
        Function.Surjective φ ∧
          φ.ker = (sec2S A R E F).subgroupOf (sec2H E F ⊔ zpowers x ⊔ sec2T E T₀)) ∧
      centerIn (sec2T E T₀) ≠ sec2Z A E F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  have hSp := special_of h24 hS
  obtain ⟨C⟩ := nonempty_coord h26 hS
  obtain ⟨hc1, hSH, -, hHCS, -, hc6, -, hHS, hNH⟩ := h26 G A R g E F hS
  set S := sec2S A R E F with hSdef
  set Z := sec2Z A E F with hZdef
  set H := sec2H E F with hHdef
  set P := sec2P E with hPdef
  set K := sec2K E with hKdef
  set T := sec2T E T₀ with hTdef
  set O := AS76b.oddCoreIn K with hOdef
  have hOodd : Odd (Nat.card O) := AS76b.odd_card_oddCoreIn K
  have hPST' := sec2P_sup_sec2S_le_sec2T h211 hS hFK hPST
  have hST : S ≤ T := le_sup_right.trans hPST'
  have hTT₀ : T ≤ T₀ := inf_le_left
  have hTK : T ≤ K := inf_le_right
  have hT2 : IsPGroup 2 T := hT₀s.isPGroup.to_le hTT₀
  have hS2 : IsPGroup 2 S := hT2.to_le hST
  have hPH : P ≤ H := le_sup_left
  obtain ⟨I, hPI, hIO, hIOK, hOI⟩ := step212Prod_of' h4 h34 hE16 h21 h211 hS hFK
  have h2I : ∀ k ∈ K, ∀ n : ℕ, k ^ 2 ^ n = 1 → k ∈ I := fun k hk n hkn =>
    mem_of_mem_sup_of_inf_eq_bot hOodd hOI hIO (by rw [hIOK]; exact hk) hkn
  have hTI : T ≤ I := fun τ hτ => by
    obtain ⟨n, hn⟩ := hT2 ⟨τ, hτ⟩
    exact h2I τ (hTK hτ) n (by simpa using congrArg Subtype.val hn)
  have hSI : S ≤ I := hST.trans hTI
  have hOP : O ≤ centralizer (P : Set G) := hOI.trans (centralizer_le hPI)
  have hOP' : P ≤ centralizer (O : Set G) := Subgroup.le_centralizer_iff.mp hOP
  have hSF : Sec2Setting G A R g F E := ⟨hF.symm, hL, hodd, hS.below⟩
  have hOPF : O ≤ centralizer (sec2P F : Set G) := by
    intro o ho
    have hoF : o ∈ centralizer (F : Set G) := centralizer_le
      ((le_sec2S_and_le_sec2S (A := A) (R := R) hF).2.trans hSI) (hOI ho)
    exact (h21 G A R g F E hSF).2.2.1
      (mem_oddCoreIn_centralizer_E hF.symm hL hodd hoF (odd_orderOf_of_mem hOodd ho))
  have hOH : O ≤ centralizer (H : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hOP) (Subgroup.le_centralizer_iff.mp hOPF)
  have hOHbot : ∀ o ∈ O, o ∈ H → o = 1 := by
    intro o ho hoH
    have h1 : o ∈ H ⊓ centralizer (S : Set G) := ⟨hoH, centralizer_le hSH (hOH ho)⟩
    rw [hHCS] at h1
    have h2 : o ∈ (S : Subgroup G) ⊓ O := ⟨hSp.le h1, ho⟩
    rw [NXKernel.inf_eq_bot_of_two_odd hS2 hOodd, mem_bot] at h2
    exact h2
  obtain ⟨u, y, huy⟩ := (h27 G A R g E F hS).1
  obtain ⟨x₀, hx₀3, hux₀, hx₀F4, hx₀cl, hx₀H, hx₀H'⟩ := (h27 G A R g E F hS).2 u y huy
  have hPZ := sec2P_le_normalizer_sec2Z h11 hE16 hF hL hodd
  have hyE := mem_normalizer_E_of_sec2UY h23 h26 hS hPZ huy
  have huE := (sec2U_facts h11 hE16 hF hL hodd huy.1 huy.2.1 huy.2.2.1).1
  have hyP : y ∈ normalizer (P : Set G) := normalizer_le_normalizer_sec2P E hyE
  have hx₀E : x₀ ∈ normalizer (E : Set G) := by
    rcases hux₀ with h | h
    · have e : x₀ = u * y⁻¹ := by rw [h]; group
      rw [e]
      exact mul_mem huE (inv_mem hyE)
    · have e : x₀ = u * y := by rw [h]; group
      rw [e]
      exact mul_mem huE hyE
  have hx₀K : x₀ ∈ K := subset_closure ⟨normalizer_le_normalizer_sec2P E hx₀E,
    by rw [hx₀3]; decide⟩
  have hx₀3' : x₀ ^ 3 = 1 := by rw [← hx₀3]; exact pow_orderOf_eq_one x₀
  obtain ⟨x, hxI, hx3, hxF4, hxcl, hxH, hxH'⟩ := exists_mem_I_of hSp hSI hOI hIO hOH
    (by rw [hIOK]; exact hx₀K) hx₀F4 hx₀cl hx₀3' hx₀H hx₀H'
  have hxZ : ¬ ∀ z ∈ Z, x * z * x⁻¹ = z := by
    intro hall
    have hZ1 : Z = ⊥ := by
      rw [← hxcl, eq_bot_iff, closure_le]
      rintro c ⟨w, hw, rfl⟩
      have h1 := hall w hw
      rw [SetLike.mem_coe, mem_bot]
      calc w⁻¹ * x⁻¹ * w * x = w⁻¹ * x⁻¹ * (x * w * x⁻¹) * x := by rw [h1]
        _ = 1 := by group
    have h4 := hSp.card
    rw [hZ1, card_bot] at h4
    omega
  obtain ⟨-, -, -, hyPO, -, -, -, -, -⟩ := h211 G A R g E F hS
  have hyH : y ∈ H := huy.2.2.2.1.1.1
  have hy3 : y ^ 3 = 1 := by rw [← huy.2.2.2.2]; exact pow_orderOf_eq_one y
  have hyS : y ∉ S := fun h => by
    obtain ⟨n, hn⟩ := hS2 ⟨y, h⟩
    have h1 : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h2 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
    rw [huy.2.2.2.2] at h2
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have : (2 : ℕ) ∣ 3 := by
      rcases m with _ | m
      · simp at hm
      · rw [pow_succ] at hm
        exact ⟨2 ^ m, by rw [hm]; ring⟩
    omega
  have hP4 : Nat.card ((P.subgroupOf H).map C.φ) = 4 := by
    rw [C.card_map_φ hPH]
    obtain ⟨-, hPE, -, -, -, -, -, -, hSPE, -⟩ := h21 G A R g E F hS
    have h1 := Subgroup.relIndex_mul_relIndex E (S ⊓ P) P hSPE.1 inf_le_right
    rw [hSPE.2.1, hPE.2.1, Subgroup.inf_relIndex_right] at h1
    omega
  have hTN : T ≤ normalizer (S : Set G) := hTT₀.trans hT₀s.le
  have hTA : ∀ τ ∈ T, ∃ p ∈ P, ∀ h ∈ H, (p⁻¹ * τ) * h * (p⁻¹ * τ)⁻¹ * h⁻¹ ∈ S := by
    intro τ hτ
    obtain ⟨n, hn⟩ := hT2 ⟨τ, hτ⟩
    have hτn : τ ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hτH : τ ∈ normalizer (H : Set G) := hNH (hTN hτ)
    have hyt : y⁻¹ * τ⁻¹ * y * τ ∈ P := by
      have h1 := hyPO u y huy τ (hTK hτ)
      obtain ⟨p, hp, o, ho, hpo, -⟩ := NXKernel.exists_mul_of_mem_sup hOP' h1
      have hτy : τ⁻¹ * y * τ ∈ H := by
        have := (mem_normalizer_iff.mp (inv_mem hτH) y).mp hyH
        simpa using this
      have hmem : y⁻¹ * τ⁻¹ * y * τ ∈ H := by
        have e : y⁻¹ * τ⁻¹ * y * τ = y⁻¹ * (τ⁻¹ * y * τ) := by group
        rw [e]
        exact mul_mem (inv_mem hyH) hτy
      have hoH : o ∈ H := by
        have e : o = p⁻¹ * (y⁻¹ * τ⁻¹ * y * τ) := by rw [hpo]; group
        rw [e]
        exact mul_mem (inv_mem (hPH hp)) hmem
      rw [hpo, hOHbot o ho hoH, mul_one]
      exact hp
    exact exists_mem_conj_mem_of_comm_mem C.φ C.surj C.ker hPH hP4 hyH hyP hy3 hyS hτH
      (hTN hτ) (hT₀P (hTT₀ hτ)) hτn hyt
  have hinf := inf_sec2H_eq h21 h26 hS hPST hT₀s.isPGroup
  have hTPS : T ⊓ H = P ⊔ S := le_antisymm (by rw [← hinf]; exact inf_le_inf_right H hTT₀)
    (le_inf hPST' (sup_le hPH hSH))
  have hidx' : ((P ⊔ S).subgroupOf T).index = 2 := hidx
  obtain ⟨t, htT, htH⟩ : ∃ t ∈ T, t ∉ H := by
    by_contra hall
    push Not at hall
    have h1 : T ≤ P ⊔ S := fun τ hτ => by rw [← hTPS]; exact ⟨hτ, hall τ hτ⟩
    have h2 : (P ⊔ S).relIndex T = 1 := relIndex_eq_one.mpr h1
    omega
  obtain ⟨p₀, hp₀, hp₀t⟩ := hTA t htT
  set c := p₀⁻¹ * t with hc
  have hp₀T : p₀ ∈ T := hPST' (mem_sup_left hp₀)
  have hcT : c ∈ T := T.mul_mem (T.inv_mem hp₀T) htT
  have hcH : c ∉ H := fun h => htH (by
    have e : t = p₀ * c := by rw [hc]; group
    rw [e]
    exact mul_mem (hPH hp₀) h)
  have hcPS : c ∉ (P ⊔ S : Subgroup G) := fun h => hcH ((sup_le hPH hSH) h)
  have hTH : ∀ τ ∈ T, τ ∈ H ∨ c⁻¹ * τ ∈ H := by
    intro τ hτ
    by_cases hτPS : τ ∈ P ⊔ S
    · exact Or.inl ((sup_le hPH hSH) hτPS)
    · right
      have h1 := mul_mem_iff_of_index_two hidx' (a := ⟨c, hcT⟩⁻¹) (b := ⟨τ, hτ⟩)
      rw [mem_subgroupOf, mem_subgroupOf, mem_subgroupOf] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      have h2 : c⁻¹ ∉ (P ⊔ S : Subgroup G) := fun h => hcPS (by simpa using inv_mem h)
      exact (sup_le hPH hSH) (h1.mpr (iff_of_false h2 hτPS))
  have hc2PS : c * c ∈ P ⊔ S := by
    have h1 := mul_mem_iff_of_index_two hidx' (a := ⟨c, hcT⟩) (b := ⟨c, hcT⟩)
    rw [mem_subgroupOf, mem_subgroupOf] at h1
    exact h1.mpr Iff.rfl
  have hcH' : ∀ h ∈ H, c * h * c⁻¹ * h⁻¹ ∈ S := hp₀t
  have hcN : c ∈ normalizer (S : Set G) := hTN hcT
  have hxN : x ∈ normalizer (S : Set G) := hxF4.1
  let CH : Subgroup G :=
    { carrier := {w | w ∈ normalizer (S : Set G) ∧ w ∈ normalizer (H : Set G) ∧
        ∀ h ∈ H, w * h * w⁻¹ * h⁻¹ ∈ S}
      mul_mem' := by
        rintro a b ⟨haS, haH, ha⟩ ⟨hbS, hbH, hb⟩
        refine ⟨mul_mem haS hbS, mul_mem haH hbH, fun h hh => ?_⟩
        have e : a * b * h * (a * b)⁻¹ * h⁻¹ = a * (b * h * b⁻¹ * h⁻¹) * a⁻¹ *
            (a * h * a⁻¹ * h⁻¹) := by group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.mp haS _).mp (hb h hh)) (ha h hh)
      one_mem' := ⟨one_mem _, one_mem _, fun h hh => by simp⟩
      inv_mem' := by
        rintro a ⟨haS, haH, ha⟩
        refine ⟨inv_mem haS, inv_mem haH, fun h hh => ?_⟩
        have hk : a⁻¹ * h * a ∈ H := by
          have := (mem_normalizer_iff.mp (inv_mem haH) h).mp hh
          simpa using this
        have h1 := inv_mem (ha _ hk)
        have e : a⁻¹ * h * a⁻¹⁻¹ * h⁻¹ = (a * (a⁻¹ * h * a) * a⁻¹ * (a⁻¹ * h * a)⁻¹)⁻¹ := by
          group
        rw [e]
        exact h1 }
  have hmemCH : ∀ {w : G}, w ∈ normalizer (S : Set G) → (∀ h ∈ H, w * h * w⁻¹ * h⁻¹ ∈ S) →
      w ∈ CH := fun hwS hwH => ⟨hwS, hNH hwS, hwH⟩
  have hxH'' : ∀ h ∈ H, x * h * x⁻¹ * h⁻¹ ∈ S := by
    intro h hh
    have hxh : x * h * x⁻¹ ∈ H := (mem_normalizer_iff.mp hxH h).mp hh
    have h1 := hxH' _ hxh
    have h2 := (mem_normalizer_iff.mp (hHS hh) _).mp h1
    have e : x * h * x⁻¹ * h⁻¹ =
        h * (x⁻¹ * (x * h * x⁻¹)⁻¹ * x * (x * h * x⁻¹)) * h⁻¹ := by group
    rw [e]
    exact h2
  have hxCH : x ∈ CH := hmemCH hxN hxH''
  have hcCH : c ∈ CH := hmemCH hcN hcH'
  have hSCH : S ≤ CH := fun s hs => hmemCH (le_normalizer hs) fun h hh => by
    have e : s * h * s⁻¹ * h⁻¹ = s * (h * s⁻¹ * h⁻¹) := by group
    rw [e]
    exact mul_mem hs ((mem_normalizer_iff.mp (hHS hh) _).mp (inv_mem hs))
  have hmat : ∀ w ∈ CH, ∃ M : Mat2, ∀ s ∈ S, C.Ψ (w * s * w⁻¹) = matAct M (C.Ψ s) :=
    fun w hw => C.exists_mat_of_mem hSp hHS hNH hw.1 hw.2.2
  have hmatEq : ∀ {A B : Mat2}, (∀ s ∈ S, matAct A (C.Ψ s) = matAct B (C.Ψ s)) → A = B := by
    intro A B h
    refine mat_eq_of_matAct fun m hm1 hm2 => ?_
    obtain ⟨s, hs, hsm⟩ := C.exists_Ψ_eq hm1 hm2
    rw [Prod.mk.eta] at hsm
    rw [← hsm]
    exact h s hs
  have hmatMul : ∀ {a b : G} {A B : Mat2}, a ∈ normalizer (S : Set G) →
      b ∈ normalizer (S : Set G) → (∀ s ∈ S, C.Ψ (a * s * a⁻¹) = matAct A (C.Ψ s)) →
      (∀ s ∈ S, C.Ψ (b * s * b⁻¹) = matAct B (C.Ψ s)) →
      ∀ s ∈ S, C.Ψ ((a * b) * s * (a * b)⁻¹) = matAct (matMul A B) (C.Ψ s) := by
    intro a b A B ha hb hA hB s hs
    have hbs : b * s * b⁻¹ ∈ S := (mem_normalizer_iff.mp hb s).mp hs
    rw [matAct_matMul, ← hB s hs, ← hA _ hbs]
    congr 1
    group
  have hmatOne : ∀ {w : G}, w ∈ normalizer (S : Set G) →
      (∀ s ∈ S, C.Ψ (w * s * w⁻¹) = matAct matOne (C.Ψ s)) →
      ∀ s ∈ S, s⁻¹ * (w * s * w⁻¹) ∈ Z := by
    intro w hw hM s hs
    have hws : w * s * w⁻¹ ∈ S := (mem_normalizer_iff.mp hw s).mp hs
    have h1 := hM s hs
    rw [matAct_matOne, C.Ψ_eq_iff hSp hws hs] at h1
    have h2 := (mem_normalizer_iff.mp (show s⁻¹ ∈ normalizer (Z : Set G) by
      rw [← hSp.center]
      exact mem_normalizer_centerIn (le_normalizer (inv_mem hs))) _).mp h1
    have e : s⁻¹ * (w * s * w⁻¹) = s⁻¹ * (w * s * w⁻¹ * s⁻¹) * s⁻¹⁻¹ := by group
    rw [e]
    exact h2
  obtain ⟨X, hX⟩ := hmat x⁻¹ (inv_mem hxCH)
  have hXo : ∃ i, X = ord3 i := by
    apply ord3_cases
    refine hmatEq fun s hs => ?_
    rw [matAct_ord3]
    have hs1 : x⁻¹ * s * x⁻¹⁻¹ ∈ S := (mem_normalizer_iff.mp (inv_mem hxN) s).mp hs
    rw [← hX s hs, ← hX _ hs1]
    have h1 := hxF4.2.2 s hs
    have hs2 : x⁻¹ * (x⁻¹ * s * x⁻¹⁻¹) * x⁻¹⁻¹ ∈ S :=
      (mem_normalizer_iff.mp (inv_mem hxN) _).mp hs1
    have e1 : x⁻¹ * s * x⁻¹⁻¹ = x⁻¹ * s * x := by group
    have e2 : x⁻¹ * (x⁻¹ * s * x⁻¹⁻¹) * x⁻¹⁻¹ = x⁻¹ * x⁻¹ * s * x * x := by group
    rw [e2]
    rw [e1] at hs1
    rw [e2] at hs2
    rw [e1]
    have h2 := (C.Ψ_eq_zero_iff hSp (S.mul_mem (S.mul_mem hs hs1) hs2)).mpr h1
    rw [C.Ψ_mul hSp (S.mul_mem hs hs1) hs2, C.Ψ_mul hSp hs hs1] at h2
    have h0 : matAct (0 : Mat2) (C.Ψ s) = 0 := by simp [matAct]
    rw [h0, ← h2]
    abel
  have hc2S : c * c ∈ S := by
    have hc2H : c * c ∈ H := (sup_le hPH hSH) hc2PS
    have hcc : c * c ∈ CH := CH.mul_mem hcCH hcCH
    have h1 : ∀ b : alternatingGroup (Fin 5), C.φ ⟨c * c, hc2H⟩ * b = b * C.φ ⟨c * c, hc2H⟩ := by
      intro b
      obtain ⟨h, rfl⟩ := C.surj b
      have hk : (⟨c * c, hc2H⟩ : ↥H) * h * (⟨c * c, hc2H⟩ : ↥H)⁻¹ * h⁻¹ ∈ C.φ.ker := by
        rw [C.ker, mem_subgroupOf]
        exact hcc.2.2 h h.2
      rw [MonoidHom.mem_ker] at hk
      simp only [map_mul, map_inv] at hk
      have := mul_inv_eq_one.mp hk
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have h2 := alt5_eq_one_of_comm h1
    have h3 : (⟨c * c, hc2H⟩ : ↥H) ∈ C.φ.ker := h2
    rw [C.ker, mem_subgroupOf] at h3
    exact h3
  obtain ⟨Y, hY⟩ := hmat c hcCH
  have hYY : matMul Y Y = matOne := by
    refine hmatEq fun s hs => ?_
    rw [← hmatMul hcN hcN hY hY s hs, matAct_matOne, C.Ψ_conj_S hSp hc2S hs]
  have hY1 : Y ≠ matOne := by
    intro h
    apply hcPS
    refine mem_sup_right (mem_of_forall_inv_mul_conj_mem hSp hc6 hT₀s (hTT₀ hcT) ?_)
    exact hmatOne hcN (by rw [← h]; exact hY)
  obtain ⟨k, hk⟩ := invol_cases Y hYY hY1
  obtain ⟨i, hi⟩ := hXo
  have hYinv : ∀ s ∈ S, C.Ψ (c⁻¹ * s * c⁻¹⁻¹) = matAct Y (C.Ψ s) := by
    intro s hs
    have hs' : c⁻¹ * s * c⁻¹⁻¹ ∈ S := (mem_normalizer_iff.mp (inv_mem hcN) s).mp hs
    have h1 := hY _ hs'
    have e : c * (c⁻¹ * s * c⁻¹⁻¹) * c⁻¹ = s := by group
    rw [e] at h1
    rw [h1, ← matAct_matMul, hYY, matAct_matOne]
  have hw : ∀ s ∈ S, C.Ψ ((c * x⁻¹ * c⁻¹ * x⁻¹) * s * (c * x⁻¹ * c⁻¹ * x⁻¹)⁻¹) =
      matAct matOne (C.Ψ s) := by
    have h1 := hmatMul (mul_mem (mul_mem hcN (inv_mem hxN)) (inv_mem hcN)) (inv_mem hxN)
      (hmatMul (mul_mem hcN (inv_mem hxN)) (inv_mem hcN) (hmatMul hcN (inv_mem hxN) hY hX)
        hYinv) hX
    intro s hs
    rw [h1 s hs, hk, hi, invol_ord3]
  have hwZ := mem_centralizer_Z_of_forall hSp
    (hmatOne (mul_mem (mul_mem (mul_mem hcN (inv_mem hxN)) (inv_mem hcN)) (inv_mem hxN)) hw)
  have hZN : ∀ {n : G}, n ∈ normalizer (S : Set G) → ∀ z ∈ Z, n * z * n⁻¹ ∈ Z :=
    fun hn z hz => conj_mem_Z_of_normS hSp hn hz
  have hcZ : ¬ ∀ z ∈ Z, c * z * c⁻¹ = z := by
    intro hcz
    apply hxZ
    have hcz' : ∀ z ∈ Z, c⁻¹ * z * c = z := fun z hz => by
      have h1 := hcz _ (by simpa using hZN (inv_mem hcN) z hz)
      calc c⁻¹ * z * c = c * (c⁻¹ * z * c) * c⁻¹ := h1.symm
        _ = z := by group
    have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    have hx2 : ∀ z ∈ Z, x⁻¹ * x⁻¹ * z * x * x = z := by
      intro z hz
      have hz1 : x⁻¹ * z * x ∈ Z := by simpa using hZN (inv_mem hxN) z hz
      have hz2 : x⁻¹ * x⁻¹ * z * x * x ∈ Z := by
        have := hZN (inv_mem hxN) _ hz1
        simpa [mul_assoc] using this
      calc x⁻¹ * x⁻¹ * z * x * x = c * (x⁻¹ * x⁻¹ * z * x * x) * c⁻¹ := (hcz _ hz2).symm
        _ = c * (x⁻¹ * (c⁻¹ * (x⁻¹ * z * x) * c) * x) * c⁻¹ := by rw [hcz' _ hz1]; group
        _ = (c * x⁻¹ * c⁻¹ * x⁻¹) * z * (c * x⁻¹ * c⁻¹ * x⁻¹)⁻¹ := by group
        _ = z := hwZ z hz
    intro z hz
    have hxz : x * z * x⁻¹ ∈ Z := hZN hxN z hz
    calc x * z * x⁻¹ = x⁻¹ * x⁻¹ * (x * z * x⁻¹) * x * x := (hx2 _ hxz).symm
      _ = x⁻¹ * z * x := by group
      _ = x⁻¹ * (x⁻¹ * x⁻¹ * z * x * x) * x := by rw [hx2 z hz]
      _ = (x * (x * x))⁻¹ * z * (x * (x * x)) := by group
      _ = z := by rw [← pow_three, hx3']; group
  set D : Subgroup G := zpowers x ⊔ zpowers c ⊔ S with hDdef
  have hDCH : D ≤ CH :=
    sup_le (sup_le (zpowers_le.mpr hxCH) (zpowers_le.mpr hcCH)) hSCH
  have hDI : D ≤ I :=
    sup_le (sup_le (zpowers_le.mpr hxI) (zpowers_le.mpr (hTI hcT))) hSI
  have hD : Nat.card D ≤ 6 * Nat.card S :=
    card_le_six_mul C hSp hHS hNH le_sup_right (hDCH.trans fun w hw => hw.1)
      (fun w hw => (hDCH hw).2.2)
      (fun w hw hws => mem_sec2S_of_mem_I h21 h24 h26 h211 hS hSI hIO (hDI hw)
        (hDCH hw).1 hws)
  have hHZ : H ≤ centralizer (Z : Set G) := sec2H_le_centralizer_sec2Z h11 hE16 hF hL hodd
  refine ⟨⟨x, hx3, hxF4, hxcl, hxH, hxH', exists_phi_of C hSp hHS hNH hSH hHZ hx3 hxN hxH'
    hxZ hcT hcZ hcH' hc2S hTN hTH (fun τ hτ => ?_) hD⟩, fun h => hcZ fun z hz => ?_⟩
  · obtain ⟨p, hp, hpτ⟩ := hTA τ hτ
    exact ⟨p, hPH hp, hpτ⟩
  · rw [← h] at hz
    have h1 : c * z = z * c := mem_centralizer_iff.mp hz.2 c hcT
    rw [h1]
    group

end Setting2

end Sec2

open Sec2 in
theorem step212_of
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h22iv : Step22iv) (h28 : Step28) :
    Step212 := by
  intro G _ _ A R g E F hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h21 := step21_of h11 hE16
  have h23 := step23_of h11 hE16 h22iv
  have h24 := step24_of h11 hE16
  have h25 := step25_of h11 hE16 h22iv
  have h26 := step26_of h11 hE16 h22iv
  have h27 := step27_of h11 hE16 h22iv
  have h29 := step29_of h11 hE16 h22iv
  have h211 := step211_of h11 hE16 h22iv
  obtain ⟨hc1, hSH, -, -, -, hc6, -, hHS, -⟩ := h26 G A R g E F hS
  have hSp := special_of h24 hS
  have hPS2 : IsPGroup 2 (sec2P E ⊔ sec2S A R E F : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_sec2P E) hc6.isPGroup
      (le_sup_left.trans hHS)
  have hPSN : sec2P E ⊔ sec2S A R E F ≤ normalizer (sec2S A R E F : Set G) :=
    sup_le (le_sup_left.trans hHS) le_normalizer
  obtain ⟨T₀, hT₀s, hPST₀⟩ := AschbacherTheorem3.exists_isSylowOf_le hPS2 hPSN
  refine ⟨⟨T₀, hPST₀, hT₀s⟩, fun T₀ hPST hT₀s => ?_⟩
  have hT₀G : IsSylowOf 2 T₀ ⊤ := (h28 G A R g E F hS T₀ hT₀s).2.1
  have hT₀P := le_normalizer_sec2P h21 h24 h25 h26 h29 hS hPST hT₀s
  obtain ⟨u, y, huy⟩ := (h27 G A R g E F hS).1
  have hFK := sec2F_le_sec2K h11 hE16 h211 hS huy
  have hPST' := sec2P_sup_sec2S_le_sec2T h211 hS hFK hPST
  obtain ⟨-, hidx⟩ := relIndex_sec2T_eq_two h21 h26 h211 hS hFK hPST hT₀G hT₀P
  obtain ⟨hii, hZne⟩ := exists_phi_sec2T h4 h34 h11 hE16 h21 h23 h24 h26 h27 h211 hS hFK hPST
    hT₀s hT₀P hidx
  exact ⟨hT₀G, hPST', hii, map_upperCentralSeries_two_eq hSp hc6 hT₀s inf_le_left
    (le_sup_right.trans hPST') hc1 hZne, hZne, hT₀P⟩

end CFSG.ComponentClassification.AS81
