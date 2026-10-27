module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22FullClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Final

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22 Lemma37 Lemma22Full
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section ElemAbelian

omit [Finite G] in
theorem isElemAbelian_conj {p : ℕ} {V : Subgroup G} (hV : IsElemAbelian p V) (c : G) :
    IsElemAbelian p (conj V c) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, hax⟩ := mem_map.mp x.2
    obtain ⟨b, hb, hby⟩ := mem_map.mp y.2
    apply Subtype.ext
    simp only [coe_mul]
    rw [← hax, ← hby, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    rw [← map_pow, hV.2 a ha, map_one]

omit [Finite G] in
theorem isElemAbelian_subgroupOf {p : ℕ} {V X : Subgroup G} (hV : IsElemAbelian p V) :
    IsElemAbelian p (V.subgroupOf X) := CFSG.Open.IsElemAbelian.subgroupOf hV X

theorem exists_fourGroup_le {R : Subgroup G} (hR : IsElemAbelian 2 R) {n : ℕ} (hn : 2 ≤ n)
    (hcard : 2 ^ n = Nat.card R) :
    ∃ V : Subgroup G, V ≤ R ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 2 ∣ Nat.card ↥R := hcard ▸ pow_dvd_pow 2 hn
  obtain ⟨V', hV'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥R) 2 hdvd
  refine ⟨V'.map R.subtype, map_subtype_le _, IsElemAbelian.mono hR (map_subtype_le _), ?_⟩
  rw [card_map_of_injective (subtype_injective _), hV']
  norm_num

end ElemAbelian

theorem closureSetting_subgroupOf {X K R L : Subgroup G} {c : G} (hc : c ∈ X) (hKX : K ≤ X)
    (hLX : L ≤ X) (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hNL : normalizer (K : Set G) ⊓ X ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R (X ⊓ centralizer (L : Set G)))
    (hc1 : conj L c ≤ centralizer (L : Set G))
    (hc2 : X ⊓ centralizer (L : Set G) ≤ normalizer (conj L c : Set G)) (hc3 : R ≤ conj L c) :
    ClosureSetting (K.subgroupOf X) (R.subgroupOf X) (L.subgroupOf X) ⟨c, hc⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : R ≤ X := hR.le.trans hKX
  have hcX : conj L c ≤ X := conj_le_of_mem hLX hc
  refine ⟨tightlyEmbedded_subgroupOf hKX hK, (isSylowOf_subgroupOf_iff hRX hKX).mpr hR,
    (isQuasisimple_subgroupOf_iff hLX).mpr hL, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← subgroupOf_normalizer_eq hKX, mem_subgroupOf] at hx
    rw [← subgroupOf_normalizer_eq hLX, mem_subgroupOf]
    exact hNL ⟨hx, x.2⟩
  · rw [centralizer_subgroupOf hLX, ← inf_subgroupOf_left (centralizer (L : Set G)) X]
    exact (isSylowOf_subgroupOf_iff hRX inf_le_left).mpr hRL
  · rw [conj_subgroupOf, centralizer_subgroupOf hLX]
    intro y hy
    exact hc1 hy
  · rw [conj_subgroupOf, centralizer_subgroupOf hLX, ← subgroupOf_normalizer_eq hcX]
    intro y hy
    exact hc2 ⟨y.2, hy⟩
  · rw [conj_subgroupOf]
    intro y hy
    exact hc3 hy

theorem lemma37_of_theorem5_of_le
    (h5 : Asc75T4.Theorem5Statement)
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W L R : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : L ≤ A ⊓ centralizer (W : Set G))
    (hNL : normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G))) :
    standardComponentIsStandard (L.subgroupOf (centralizer (W : Set G))) ∨
      ∃ c ∈ centralizer (W : Set G), conj L c ≤ centralizer (L : Set G) ∧ L ⊓ conj L c = ⊥ ∧
        normalClosure ((L.subgroupOf (centralizer (W : Set G)) : Subgroup (centralizer (W : Set G)))
          : Set (centralizer (W : Set G))) = (L ⊔ conj L c).subgroupOf (centralizer (W : Set G)) ∧
        R ≤ conj L c ∧
        ∃ n : ℕ, 2 ≤ n ∧ 2 ^ n = Nat.card R ∧ Nonempty (↥L ≃* SL(2, GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases lemma37_bender_of_le h4 h32 h34 hA hR hWA hL hLA hNL hRL with
    h | ⟨c, hc, hc1, hc2, hc3, n, hn, hcard, ⟨e⟩⟩
  · exact Or.inl h
  right
  set X := centralizer (W : Set G) with hX
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hK'te := tightlyEmbedded_oddCoreIn_sup h4 h32 h34 hA hR
  have hK'K : oddCoreIn (centralizer (A : Set G)) ⊔ R ≤ centralizer (A : Set G) :=
    sup_le (oddCoreIn_le _) hR.le
  have hKW : centralizer (A : Set G) ≤ X := centralizer_le fun x hx => hWA hx
  have hLW : L ≤ X := hLA.trans inf_le_right
  have hNK' : normalizer ((oddCoreIn (centralizer (A : Set G)) ⊔ R : Subgroup G) : Set G) ⊓ X ≤
      normalizer (L : Set G) := by
    intro x hx
    obtain ⟨hxN, hxW⟩ := mem_inf.mp hx
    have hxA : x ∈ normalizer (A : Set G) := by
      rw [← normalizer_centralizer_eq hA.standard]
      exact normalizer_le_of_le_of_even hKte hK'K hK'te.1 hxN
    exact hNL ⟨hxA, hxW⟩
  have hRCL := isSylowOf_of_isSylowOf_inf_normalizer hRL
  have hSet := closureSetting_subgroupOf hc (hK'K.trans hKW) hLW hK'te (hR.of_le le_sup_right hK'K)
    hL hNK' hRCL hc1 hc2 hc3
  have hRe : IsElemAbelian 2 R := h32 G A hA R hR
  obtain ⟨V₀, hV₀R, hV₀e, hV₀4⟩ := exists_fourGroup_le hRe hn hcard
  have hVL : conj V₀ c⁻¹ ≤ L := by
    calc conj V₀ c⁻¹ ≤ conj (conj L c) c⁻¹ := map_mono (hV₀R.trans hc3)
      _ = L := by rw [conj_conj, inv_mul_cancel, conj_one]
  have hV : ∃ V : Subgroup X, V ≤ L.subgroupOf X ∧ IsElemAbelian 2 V ∧ Nat.card V = 4 := by
    refine ⟨(conj V₀ c⁻¹).subgroupOf X, fun x hx => hVL hx,
      isElemAbelian_subgroupOf (isElemAbelian_conj hV₀e c⁻¹), ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe (hVL.trans hLW)).toEquiv, card_conj, hV₀4]
  have hclos := hSet.normalClosure_eq_sup h5 hV
  have hcX : conj L c ≤ X := conj_le_of_mem hLW hc
  refine ⟨c, hc, hc1, ?_, ?_, hc3, n, hn, hcard, ⟨e⟩⟩
  ·
    have hZ : center ↥L = ⊥ := by
      have h1 := card_center_congr e
      rw [center_sl_two_eq_bot, card_bot] at h1
      exact card_eq_one.mp h1
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxc⟩ := mem_inf.mp hx
    have hxZ : (⟨x, hxL⟩ : L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext ((mem_centralizer_iff.mp (hc1 hxc)) y y.2)
    rw [hZ, mem_bot] at hxZ
    rw [mem_bot]
    exact congrArg Subtype.val hxZ
  · rw [hclos, conj_subgroupOf, ← subgroupOf_sup hLW hcX]

theorem lemma37_of_le
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W L R : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : L ≤ A ⊓ centralizer (W : Set G))
    (hNL : normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G))) :
    standardComponentIsStandard (L.subgroupOf (centralizer (W : Set G))) ∨
      ∃ c ∈ centralizer (W : Set G), conj L c ≤ centralizer (L : Set G) ∧ L ⊓ conj L c = ⊥ ∧
        normalClosure ((L.subgroupOf (centralizer (W : Set G)) : Subgroup (centralizer (W : Set G)))
          : Set (centralizer (W : Set G))) = (L ⊔ conj L c).subgroupOf (centralizer (W : Set G)) ∧
        R ≤ conj L c ∧
        ∃ n : ℕ, 2 ≤ n ∧ 2 ^ n = Nat.card R ∧ Nonempty (↥L ≃* SL(2, GaloisField 2 n)) :=
  lemma37_of_theorem5_of_le AschbacherTheorem5.conclusion_holds h4 h32 h34 hA hR hWA hL hLA hNL
    hRL

end CFSG.ComponentClassification.AS76b
