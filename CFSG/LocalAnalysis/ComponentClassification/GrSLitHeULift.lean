module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKFixed
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std
public import Certificates.Certificate2022
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

namespace HeU

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem mem_of_odd_index {N T : Subgroup H} (hn : (T.subgroupOf N).Normal)
    (hodd : Odd (T.subgroupOf N).index) {x : H} (hxN : x ∈ N) (hx : x * x = 1) : x ∈ T := by
  set q := QuotientGroup.mk' (T.subgroupOf N) (⟨x, hxN⟩ : N) with hq
  have h2 : q ^ 2 = 1 := by
    rw [sq, hq, ← map_mul, show (⟨x, hxN⟩ : N) * ⟨x, hxN⟩ = 1 from Subtype.ext hx, map_one]
  have h1 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have h3 : orderOf q ∣ (T.subgroupOf N).index := by
    rw [index]
    exact orderOf_dvd_natCard q
  have h4 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h3
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)
  rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact mem_subgroupOf.mp h4

theorem exists_lift {u : H} (hu : u * u = 1)
    {K : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hK : K ≤ centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) u} : Set (H ⧸ pPrimeCore 2 H)))
    (hKp : IsPComponent 2 (K.subgroupOf
      (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) u} : Set (H ⧸ pPrimeCore 2 H))))) :
    ∃ T : Subgroup H, T ≤ centralizer ({u} : Set H) ∧
      IsPComponent 2 (T.subgroupOf (centralizer ({u} : Set H))) ∧
      T.map (QuotientGroup.mk' (pPrimeCore 2 H)) = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  set X := centralizer ({u} : Set H) with hX
  have hXmap : X.map π = centralizer ({π u} : Set (H ⧸ pPrimeCore 2 H)) :=
    UnbalancedLayer.map_centralizer_eq GSThmB.OddQuot.odd_card_pPrimeCore hu
  set f := π.subgroupMap X with hf
  have hfs : Function.Surjective f := π.subgroupMap_surjective X
  have hfk : ¬ 2 ∣ Nat.card f.ker :=
    GSThmB.OddQuot.not_two_dvd_card_ker_subgroupMap π GSThmB.OddQuot.not_two_dvd_card_ker X
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hfs
    hfk
  have hK' : IsPComponent 2 (K.subgroupOf (X.map π)) := by
    rw [hXmap]
    exact hKp
  obtain ⟨T', hT', hT'K⟩ := hbij.surjOn hK'
  refine ⟨T'.map X.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [show (T'.map X.subtype).subgroupOf X = T' from
      comap_map_eq_self_of_injective X.subtype_injective T']
    exact hT'
  · have hKX : K ≤ X.map π := hXmap ▸ hK
    have h1 : (T'.map f).map (X.map π).subtype = (T'.map X.subtype).map π := by
      rw [map_map, map_map, GSThmB.OddQuot.subtype_comp_subgroupMap]
    rw [← h1]
    have hT'K' : T'.map f = K.subgroupOf (X.map π) := hT'K
    rw [hT'K', subgroupOf_map_subtype, inf_of_le_left hKX]

theorem exists_layer_lift {u : H} (hu : u * u = 1)
    {K : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hK : K ≤ centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) u} : Set (H ⧸ pPrimeCore 2 H)))
    (hKp : IsPComponent 2 (K.subgroupOf
      (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) u} : Set (H ⧸ pPrimeCore 2 H)))))
    (hKperf : ⁅K, K⁆ = K) (hKt : IsL34Type (↥K ⧸ center ↥K)) :
    ∃ T : Subgroup H, T ≤ centralizer ({u} : Set H) ∧
      IsPComponent 2 (T.subgroupOf (centralizer ({u} : Set H))) ∧
      IsL34Type (↥T ⧸ Open.fusionZStar ↥T) ∧
      ∀ x ∈ centralizer ({u} : Set H), x * x = 1 →
        QuotientGroup.mk' (pPrimeCore 2 H) x ∈ (center ↥K).map K.subtype →
        x ∈ (Open.fusionZStar ↥T).map T.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  obtain ⟨T, hTX, hTp, hTK⟩ := exists_lift hu hK hKp
  set X := centralizer ({u} : Set H) with hX
  let f : T →* K := (π.comp T.subtype).codRestrict K fun t => by
    rw [← hTK]
    exact mem_map_of_mem π t.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    rw [← hTK] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  have hOodd : Odd (Nat.card (pPrimeCore 2 H)) := GSThmB.OddQuot.odd_card_pPrimeCore
  have hfk : ¬ 2 ∣ Nat.card f.ker := by
    let g : f.ker →* pPrimeCore 2 H :=
      (T.subtype.comp f.ker.subtype).codRestrict (pPrimeCore 2 H) fun k => by
        have h1 : f (k : T) = 1 := k.2
        have h2 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : pPrimeCore 2 H => (x : H)) h
      exact Subtype.ext (Subtype.ext h')
    exact Nat.not_even_iff_odd.mpr (hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)) ∘
      even_iff_two_dvd.mpr
  have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ hK).1 hKp).2.2
  have hKs : IsSimpleGroup (↥K ⧸ center ↥K) := HeInner.isSimpleGroup_of_l34 hKt
  have hKperf' : commutator ↥K = ⊤ := (isPerfect_iff.mpr hKperf).commutator_eq_top
  have hOK : pPrimeCore 2 ↥K ≤ center ↥K := by
    have hne : pPrimeCore 2 ↥K ≠ ⊤ := by
      intro htop
      obtain ⟨-, hs, -⟩ := hKq
      have hsub : Subsingleton (↥K ⧸ pPrimeCore 2 ↥K) := QuotientGroup.subsingleton_iff.mpr htop
      have : Nontrivial ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) :=
        hs.toNontrivial
      have : Subsingleton ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) := by
        constructor
        intro x y
        obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
        obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
        rw [Subsingleton.elim x' y']
      exact false_of_nontrivial_of_subsingleton
        ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K))
    exact Quasisimple.normal_le_center_of_ne_top ⟨hKperf', hKs⟩ _ hne
  have hZK : Open.fusionZStar ↥K = center ↥K := GrS5.fusionZStar_eq_center_of_le hKperf' hOK
  obtain ⟨eT⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective f hf hfk
  have htype : IsL34Type (↥T ⧸ Open.fusionZStar ↥T) :=
    LieType.CurtisTits.lieModel_of_mulEquiv
      (eT.trans (QuotientGroup.quotientMulEquivOfEq hZK)).symm hKt
  refine ⟨T, hTX, hTp, htype, fun x hxX hx hxZ => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hxZ
  have hxK : π x ∈ K := by rw [← hzx]; exact (z : K).2
  rw [← hTK] at hxK
  obtain ⟨t, htT, htx⟩ := hxK
  have ho : t⁻¹ * x ∈ pPrimeCore 2 H ⊓ X := by
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem (hTX htT)) hxX⟩
    rw [← QuotientGroup.eq]
    exact htx
  set O' := pPrimeCore 2 H ⊓ X with hO'
  set N := T ⊔ O' with hN
  have hO'X : O' ≤ X := inf_le_right
  have hO'N : O' ≤ normalizer (T : Set H) := by
    intro o ho'
    have hT'p : IsPComponent 2 (T.subgroupOf X) := hTp
    have hOX : (⟨o, hO'X ho'⟩ : X) ∈ pPrimeCore 2 ↥X := by
      apply le_sSup (s := {K : Subgroup ↥X | K.Normal ∧ Nat.Coprime 2 (Nat.card K)})
        ⟨?_, ?_⟩ (show (⟨o, hO'X ho'⟩ : X) ∈ O'.subgroupOf X from mem_subgroupOf.mpr ho')
      · refine ⟨fun n hn g => ?_⟩
        rw [mem_subgroupOf] at hn ⊢
        obtain ⟨hn1, hn2⟩ := mem_inf.mp hn
        exact mem_inf.mpr ⟨(pPrimeCore_normal (p := 2) (G := H)).conj_mem _ hn1 _,
          mul_mem (mul_mem g.2 hn2) (inv_mem g.2)⟩
      · have h1 : Nat.card ↥(O'.subgroupOf X) ∣ Nat.card (pPrimeCore 2 H) := by
          rw [Nat.card_congr (subgroupOfEquivOfLe hO'X).toEquiv]
          exact card_dvd_of_le inf_le_left
        exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    have h1 := UnbalancedLayer.pPrimeCore_le_normalizer hT'p hOX
    rw [mem_normalizer_iff] at h1 ⊢
    intro y
    constructor
    · intro hy
      by_cases hyX : y ∈ X
      · have := (h1 ⟨y, hyX⟩).mp (mem_subgroupOf.mpr hy)
        exact mem_subgroupOf.mp this
      · exact absurd (hTX hy) hyX
    · intro hy
      have hyX : y ∈ X := by
        have h2 := hTX hy
        have h3 := mul_mem (mul_mem (inv_mem (hO'X ho')) h2) (hO'X ho')
        rwa [show o⁻¹ * (o * y * o⁻¹) * o = y by group] at h3
      have := (h1 ⟨y, hyX⟩).mpr (mem_subgroupOf.mpr hy)
      exact mem_subgroupOf.mp this
  have hnorm : (T.subgroupOf N).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have hgN : (g : H) ∈ normalizer (T : Set H) :=
      (sup_le (le_normalizer) hO'N) g.2
    exact (mem_normalizer_iff.mp hgN n).mp hn
  have hodd : Odd (T.subgroupOf N).index := by
    have hle : T.subgroupOf N ⊔ O'.subgroupOf N = ⊤ := by
      rw [← subgroupOf_sup le_sup_left le_sup_right]
      exact subgroupOf_self N
    have : (T.subgroupOf N).Normal := hnorm
    have h1 : (T.subgroupOf N).index = (T.subgroupOf N).relIndex (O'.subgroupOf N) := by
      rw [← relIndex_top_right, ← hle, relIndex_sup_left]
    rw [h1]
    have h2 : (T.subgroupOf N).relIndex (O'.subgroupOf N) ∣ Nat.card (O'.subgroupOf N) :=
      relIndex_dvd_card _ _
    have h3 : Nat.card (O'.subgroupOf N) ∣ Nat.card (pPrimeCore 2 H) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv]
      exact card_dvd_of_le inf_le_left
    exact hOodd.of_dvd_nat (h2.trans h3)
  have hxN : x ∈ N := by
    rw [show x = t * (t⁻¹ * x) by group]
    exact mul_mem (mem_sup_left htT) (mem_sup_right ho)
  have hxT : x ∈ T := mem_of_odd_index hnorm hodd hxN hx
  have hcomap := GSThmB.OddQuot.comap_fusionZStar_of_surjective f hf hfk
  have hfx : f ⟨x, hxT⟩ ∈ Open.fusionZStar ↥K := by
    rw [hZK]
    have : f ⟨x, hxT⟩ = z := Subtype.ext hzx.symm
    rw [this]
    exact hz
  refine ⟨⟨x, hxT⟩, ?_, rfl⟩
  rw [← hcomap]
  exact hfx

end HeU

end CFSG.ComponentClassification.GrSLit
