module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveExclusion
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Shapes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainFactors
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainInner
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools SectionSix.Exclusion

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem mem_centralizerIn_iff_centralizes {B L : Subgroup G} (hLB : L ≤ B) (x : G) :
    x ∈ centralizerIn B L ↔ x ∈ Subgroup.normalizer (B : Set G) ∧
      aschbacherThm5Centralizes (aschbacherThm5Core B) L x := by
  rw [mem_centralizerIn_iff]
  constructor
  · rintro ⟨hx, hc⟩
    exact ⟨hx, (centralizes_iff_mem_centralizer B L hLB ⟨x, hx⟩).mpr hc⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, (centralizes_iff_mem_centralizer B L hLB ⟨x, hx⟩).mp hc⟩

omit [Finite G] in
theorem mem_normalizer_centralizerIn {B L : Subgroup G} (hLB : L ≤ B) {y : G}
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) (hyL : y ∈ Subgroup.normalizer (L : Set G)) :
    y ∈ Subgroup.normalizer ((centralizerIn B L : Subgroup G) : Set G) := by
  have hyO : y ∈ Subgroup.normalizer (aschbacherThm5Core B : Set G) :=
    normalizer_le_normalizer_core B hyB
  have key : ∀ z : G, z ∈ Subgroup.normalizer (L : Set G) →
      z ∈ Subgroup.normalizer (aschbacherThm5Core B : Set G) → ∀ x : G,
      aschbacherThm5Centralizes (aschbacherThm5Core B) L x →
      aschbacherThm5Centralizes (aschbacherThm5Core B) L (z * x * z⁻¹) := by
    intro z hzL hzO x hx l hl
    have hl' : z⁻¹ * l * z⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ hzL) l).mp hl
    have h1 := (Subgroup.mem_normalizer_iff.mp hzO _).mp (hx _ hl')
    convert h1 using 1
    group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_centralizerIn_iff_centralizes hLB, mem_centralizerIn_iff_centralizes hLB]
  constructor
  · rintro ⟨hxB, hxc⟩
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hyB hxB) (Subgroup.inv_mem _ hyB),
      key y hyL hyO x hxc⟩
  · rintro ⟨hxB, hxc⟩
    refine ⟨?_, ?_⟩
    · have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hyB) hxB) hyB
      simpa [mul_assoc] using h1
    · have h1 := key y⁻¹ (Subgroup.inv_mem _ hyL) (Subgroup.inv_mem _ hyO) _ hxc
      simpa [mul_assoc] using h1

namespace FieldHyps

variable {t g : G}

theorem false_of_thm3 (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) {j m : Fin 2} (hjm : j ≠ m)
    {T₀ : Subgroup G} (hT₀2 : IsPGroup 2 T₀) (htT₀ : t ∈ T₀)
    (hT₀L : T₀ ≤ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    (hT₀A : T₀ ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (hT₀H : T₀ ≤ Subgroup.normalizer (D : Set G))
    (hAK : aschbacherThm5Preimage D (Abar i) ⊓
        Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) ≤
      Subgroup.normalizer
        ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
          Set G))
    (hsmall : ∀ C : Subgroup G, C ≤ aschbacherThm5Preimage D (Abar i) ⊓
      Subgroup.centralizer (T₀ : Set G) → IsPGroup 2 C → Nat.card C ≤ Nat.card T₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set B := rightConjugate D g with hBdef
  set K := Subgroup.normalizer ((B : Subgroup G) : Set G) with hKdef
  set Lm := aschbacherThm5Preimage B (conjFactors D Abar g m) with hLm
  set Lj := aschbacherThm5Preimage B (conjFactors D Abar g j) with hLj
  have hC' := hC.conj g
  have hLjB : Lj ≤ B := preimage_le B _
  have hLmB : Lm ≤ B := preimage_le B _
  have hAD : A ≤ D := preimage_le D _
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := hAD.trans Subgroup.le_normalizer
  have hDA : D ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAD).mp
      (canonical_preimage_normal D Abar hC.hyp.hcomm hC.hyp.hgen i)
  have htwoT : ∀ u ∈ T₀, ∃ e : ℕ, u ^ (2 ^ e) = 1 := by
    intro u hu
    obtain ⟨e, he⟩ := hT₀2 ⟨u, hu⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hcentj : ∀ x ∈ Lm, aschbacherThm5Centralizes (aschbacherThm5Core B) Lj x := fun x hx =>
    cross_factor_centralizes B (conjFactors D Abar g) hC'.hyp.hcomm j m hjm x hx
  have hAj : ∀ u ∈ A, (∃ e : ℕ, u ^ (2 ^ e) = 1) →
      aschbacherThm5Centralizes (aschbacherThm5Core B) Lj u → u = 1 := by
    intro u huA hu2 huc
    by_contra hu1
    exact hF.not_centralizes_conj hin hC (l := j) huA hu2 hu1 huc
  have hframe : AschbacherTheorem3.Frame A T₀ := by
    refine ⟨hT₀A, ?_, hT₀2⟩
    rw [eq_bot_iff]
    rintro u ⟨huT, huA⟩
    exact (Subgroup.mem_bot).mpr (hAj u huA (htwoT u huT) (hcentj u (hT₀L huT)))
  have hT₀1 : T₀ ≠ ⊥ := by
    intro h
    have ht1 : t = 1 := by
      have h1 := htT₀
      rw [h, Subgroup.mem_bot] at h1
      exact h1
    have h2 := hF.two
    rw [ht1, orderOf_one] at h2
    omega
  set P := (A ⊔ T₀) ⊓ centralizerIn B Lj with hPdef
  have hmemP : ∀ x : G, x ∈ P ↔ x ∈ A ⊔ T₀ ∧ x ∈ K ∧
      aschbacherThm5Centralizes (aschbacherThm5Core B) Lj x := by
    intro x
    rw [hPdef, Subgroup.mem_inf, mem_centralizerIn_iff_centralizes hLjB]
  have hT₀P : T₀ ≤ P := fun x hx =>
    (hmemP x).mpr ⟨le_sup_right (a := A) hx, Subgroup.le_normalizer (hLmB (hT₀L hx)),
      hcentj x (hT₀L hx)⟩
  have hTP : IsSylowOf 2 T₀ P := by
    obtain ⟨P₂, hP₂, hTP₂⟩ := exists_isSylowOf_le hT₀P hT₀2
    have heq : P₂ = T₀ := by
      refine le_antisymm (fun x hx => ?_) hTP₂
      obtain ⟨s, hs, a, ha, rfl⟩ := hframe.mem_sup_iff.mp ((hmemP x).mp (hP₂.le hx)).1
      have haP₂ : a ∈ P₂ := by
        have h1 := P₂.mul_mem (P₂.inv_mem (hTP₂ hs)) hx
        rwa [inv_mul_cancel_left] at h1
      have ha2 : ∃ e : ℕ, a ^ (2 ^ e) = 1 := by
        obtain ⟨e, he⟩ := hP₂.isPGroup ⟨a, haP₂⟩
        exact ⟨e, by simpa using congrArg Subtype.val he⟩
      obtain ⟨-, -, hac⟩ := (hmemP a).mp (hP₂.le haP₂)
      rw [hAj a ha ha2 hac, mul_one]
      exact hs
    rw [← heq]
    exact hP₂
  have heven : Even (Nat.card P) := by
    have h2 : 2 ∣ Nat.card T₀ := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT₀2
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hT₀1 (Subgroup.eq_bot_of_card_eq T₀ (by rw [hn, pow_zero]))
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_le hT₀P))
  have htight : ∀ y ∈ A ⊔ T₀, y ∉ Subgroup.normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)) := by
    intro y hy hyN
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨⟨u, huP, huy⟩, hu2⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hu2' : orderOf u = 2 := by
      rw [← hu2]
      exact (Subgroup.orderOf_mk u (Subgroup.mem_inf.mpr ⟨huP, huy⟩)).symm
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hu2'
      omega
    obtain ⟨-, -, huc⟩ := (hmemP u).mp huP
    have hyu : y * u * y⁻¹ ∈ P := (mem_rightConjugate_iff P y u).mp huy
    obtain ⟨-, -, hyuc⟩ := (hmemP _).mp hyu
    have hyK : y⁻¹ ∈ K := by
      refine hC'.hyp.hi j j u y⁻¹ (two_power_of_orderOf hu2') ?_ huc ?_
      · rw [hC.center, Subgroup.mem_bot]
        exact hu1
      · rw [inv_inv]
        exact hyuc
    have hyK' : y ∈ K := by simpa using K.inv_mem hyK
    apply hyN
    obtain ⟨s, hs, a, ha, rfl⟩ := hframe.mem_sup_iff.mp hy
    have hsK : s ∈ K := Subgroup.le_normalizer (hLmB (hT₀L hs))
    have haK : a ∈ K := by
      have h1 := K.mul_mem (K.inv_mem hsK) hyK'
      rwa [inv_mul_cancel_left] at h1
    have hsaL : s * a ∈ Subgroup.normalizer (Lm : Set G) :=
      Subgroup.mul_mem _ (Subgroup.le_normalizer (hT₀L hs)) (hAK ⟨ha, haK⟩)
    have hsaLj : s * a ∈ Subgroup.normalizer (Lj : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_other_of_map hC'.hyp hyK' hjm.symm
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp hsaL))
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hy, mem_normalizer_centralizerIn hLjB hyK' hsaLj⟩
  obtain ⟨S, hS, hTS, hSN⟩ := exists_sylow_normalizer (le_sup_right : T₀ ≤ A ⊔ T₀) hT₀2
  obtain ⟨hNeq, hTC, hTCc⟩ := AschbacherTheorem3.lemma_4_1 hframe hS.le hTS
  set C := S ⊓ Subgroup.normalizer (T₀ : Set G) ⊓ A with hCdef
  have hCle : C ≤ A ⊓ Subgroup.centralizer (T₀ : Set G) := by
    intro c hc
    refine Subgroup.mem_inf.mpr ⟨hc.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := Subgroup.commutator_mem_commutator hx hc
    rw [hTCc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hC2 : IsPGroup 2 C := hS.isPGroup.to_le (inf_le_left.trans inf_le_left)
  have hidx : T₀.relIndex (S ⊓ Subgroup.normalizer (T₀ : Set G)) ≤ Nat.card T₀ := by
    have hTSN : T₀ ≤ S ⊓ Subgroup.normalizer (T₀ : Set G) := le_inf hTS Subgroup.le_normalizer
    have h1 := Subgroup.relIndex_mul_card T₀ (S ⊓ Subgroup.normalizer (T₀ : Set G))
    have h2 : Nat.card (S ⊓ Subgroup.normalizer (T₀ : Set G) : Subgroup G) =
        Nat.card T₀ * Nat.card C := by
      rw [hNeq]
      exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer T₀ C
        (inf_le_left.trans inf_le_right) (disjoint_iff.mpr hTC)
    rw [inf_eq_left.mpr hTSN, h2, mul_comm] at h1
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h1]
    exact hsmall C hCle hC2
  have hconc := thm3_bar hin.theorem_3 hAD (core_le_preimage D (Abar i)) hDA hT₀H hT₀A hT₀2
    hT₀1 hframe.inf_eq_bot (inf_le_left : P ≤ A ⊔ T₀) hTP heven htight hS hTS hSN hidx
  obtain ⟨mm, KK, -, hKK, -, hKKgen⟩ := bar_factor_components hC.hyp i
  have hTnc : ∃ l, ⁅KK l, bar D T₀⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have hcentr : bar D T₀ ≤ Subgroup.centralizer (bar D A : Set (Bar D)) := by
      rw [Subgroup.le_centralizer_iff, ← hKKgen]
      exact iSup_le fun l => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall l)
    have htk : aschbacherThm5Centralizes (aschbacherThm5Core D) A t :=
      (centralizes_iff_mem_centralizer D _ hAD ⟨t, hF.mem⟩).mpr
        (hcentr (toBar_mem_bar D htT₀))
    apply hF.false_of_centralizes_inv_mul hin hC hii' hnd (a := 1) A.one_mem
    rw [inv_one, one_mul]
    exact htk
  obtain ⟨l, hl⟩ := hTnc
  rcases thm3_one_or_three (isPGroup_bar hT₀2) (bar_mono D hTS) (isPGroup_bar hS.isPGroup)
    (hKK l).1 (hKK l).2 hl hconc with ⟨-, hSQ, -⟩ | ⟨n, -, hO2eq, hO2inf, hO2comm, hO2el, -, -⟩
  ·
    have hSbar : IsSylowOf 2 (bar D S) (bar D A ⊔ bar D T₀) := by
      rw [← bar_sup hAH hT₀H]
      exact isSylowOf_bar hS (sup_le hAH hT₀H)
    have hR := hSbar.inf_of_le_normalizer (N := bar D A) le_sup_left
      (sup_le Subgroup.le_normalizer (bar_le_normalizer hT₀A hAH))
    have hrankA : 2 ≤ CFSG.Open.pRank 2 (bar D A) := by
      have h1 : 2 ≤ CFSG.Open.pRank 2 (Abar i) :=
        (hF.two_le_pRank hin hC i).trans (pRank_preimage_le _)
      have h2 := CFSG.SectionRank.pRank_le_map (p := 2) one_lt_two (quotientEmbedding D)
        (quotientEmbedding_injective D) (Abar i)
      rw [map_quotientEmbedding] at h2
      exact h1.trans h2
    have hrankS : 2 ≤ CFSG.Open.pRank 2 (bar D S ⊓ bar D A) := by
      obtain ⟨T', hT'⟩ := hR
      rw [← hT', AschbacherKnownGroup.Lemma38.pRank_sylow_map T']
      exact hrankA
    rcases hSQ with hcyc | hquat | hdih
    · exact AschbacherStrongEmbedding.Lemma34.not_isCyclic_of_two_le_pRank hrankS hcyc
    · have h1 := hrankS.trans (Involution.pRank_le_one_of_quaternion hquat)
      omega
    · apply hnd
      obtain ⟨n, hn, ⟨e⟩⟩ := hdih
      obtain ⟨P', hP'⟩ := hR
      exact hasDihedralSylowTwo_of_mulEquiv (factorEquiv D (Abar i)).symm
        ⟨P', n, hn, ⟨((P' : Subgroup (bar D A)).equivMapOfInjective _
          (bar D A).subtype_injective).trans ((MulEquiv.subgroupCongr hP').trans e)⟩⟩
  ·
    have hQ2 : AschbacherTheorem3.oTwoPrime (bar D A) = bar D A := by
      apply le_antisymm (Linear.oTwoPrime_le _)
      rw [← hKKgen]
      refine iSup_le fun l' => ?_
      calc KK l' = AschbacherTheorem3.oTwoPrime (KK l') :=
            (Linear.oTwoPrime_eq_of_quasisimple (hKK l').1.2.2).symm
        _ ≤ AschbacherTheorem3.oTwoPrime (⨆ l, KK l) :=
            Subgroup.closure_mono fun _ hx => ⟨le_iSup KK l' hx.1, hx.2⟩
    rw [hQ2] at hO2eq hO2inf hO2comm
    have htbar : toBar D ⟨t, hF.mem⟩ ∈ bar D T₀ := toBar_mem_bar D htT₀
    have ht2 : toBar D ⟨t, hF.mem⟩ ∈ AschbacherTheorem3.oTwoPrime (bar D A ⊔ bar D T₀) :=
      Linear.le_oTwoPrime le_sup_right (isPGroup_bar hT₀2) htbar
    rw [hO2eq, sup_comm] at ht2
    have hecomm : ∀ e ∈ pCoreOf 2 (bar D A ⊔ bar D T₀), ∀ x ∈ bar D A, e * x = x * e := by
      intro e he x hx
      have h1 := Subgroup.commutator_mem_commutator he hx
      rw [hO2comm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hframe3 : AschbacherTheorem3.Frame (bar D A) (pCoreOf 2 (bar D A ⊔ bar D T₀)) := by
      refine ⟨fun e he => ?_, hO2inf, ?_⟩
      · apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (hecomm e he x hx).symm
      · intro e
        refine ⟨1, Subtype.ext ?_⟩
        rw [pow_one]
        exact hO2el.2 e e.2
    obtain ⟨e, he, q, hq, heq⟩ := hframe3.mem_sup_iff.mp ht2
    have hq' : q ∈ (Abar i).map (quotientEmbedding D) := by
      rw [map_quotientEmbedding]
      exact hq
    obtain ⟨y, hy, rfl⟩ := hq'
    apply hF.false_of_inner hin hC hii' hnd (y := ⟨y, hy⟩)
    intro x
    apply Subtype.ext
    apply quotientEmbedding_injective D
    have hxQ : quotientEmbedding D (x : D ⧸ aschbacherThm5OddCore D) ∈ bar D A := by
      rw [← map_quotientEmbedding]
      exact ⟨x, x.2, rfl⟩
    rw [hF.alpha_apply, quotientEmbedding_onQuotient, ← heq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    have h1 := hecomm e he _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hq hxQ)
      (Subgroup.inv_mem _ hq))
    calc e * quotientEmbedding D y * quotientEmbedding D x * (e * quotientEmbedding D y)⁻¹ =
        (e * (quotientEmbedding D y * quotientEmbedding D x * (quotientEmbedding D y)⁻¹)) *
          e⁻¹ := by group
      _ = quotientEmbedding D y * quotientEmbedding D x * (quotientEmbedding D y)⁻¹ := by
          rw [h1, mul_inv_cancel_right]

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
