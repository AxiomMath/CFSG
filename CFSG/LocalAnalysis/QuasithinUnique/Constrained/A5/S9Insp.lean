module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9InspV
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9InspC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32LeKOut
import Mathlib.Tactic.Group
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate43
public import Certificates.Certificate110
public import Certificates.Certificate113
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2199
public import Certificates.Certificate2202
public import Certificates.Certificate2204
public import Certificates.Certificate3029
public import Certificates.Certificate3120
public import Certificates.Certificate3157
public import Certificates.Certificate4041
public import Certificates.Certificate4121
public import Certificates.Certificate4145
public import Certificates.Certificate17037
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import Certificates.Certificate12952
public import Certificates.Certificate14951
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9InspB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableAll
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.TabBig
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.StronglyEmbedded

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Id2519 CFSG.QuasithinUnique.A5.Insp

section Eight

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}

theorem eight_dvd_card (cfg : A5Cfg G T M H S L) (D : U9Data T M H S L z u A V) (hVK : V ≤ K)
    (hTu : T ⊓ centralizerElem u ≤ Subgroup.normalizer (K : Set G)) : 8 ∣ Nat.card ↥K := by
  obtain ⟨x, hxT, hxS, hxu⟩ := D.s7.x_exists
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hTu ⟨hxT, hxu⟩
  have hR := D.R_eq x hxT hxS
  have hVP : V ≤ baum S ⊓ K := le_inf (D.V_le.trans D.U_le_R) hVK
  have hVxU : conjR V x ≤ conjR (blockU L) x := Subgroup.map_mono D.V_le
  have hVxP : conjR V x ≤ baum S ⊓ K := by
    refine le_inf ?_ ?_
    · rw [hR]
      exact hVxU.trans le_sup_right
    · intro y hy
      rw [mem_conjR_iff] at hy
      have hyK : x * y * x⁻¹ ∈ K := hVK hy
      have hxi : x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normalizer (K : Set G)).inv_mem hxN
      have := (Subgroup.mem_normalizer_iff.mp hxi (x * y * x⁻¹)).mp hyK
      simpa [mul_assoc] using this
  have hVcard : Nat.card V = 4 := D.hA.card_U
  have hVxcard : Nat.card ↥(conjR V x) = 4 := by
    unfold conjR
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact hVcard
  have hne : V ≠ conjR V x := by
    intro h
    exact D.not_le_conj hxT hxS (h ▸ hVxU)
  have hP2 : IsPGroup 2 ↥(baum S ⊓ K) :=
    cfg.cs.setting.isPGroup.to_le (inf_le_left.trans (baum_le_S.trans cfg.cs.le_T))
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  have hdvd4 : 4 ∣ 2 ^ n := by
    rw [← hn, ← hVcard]
    exact Subgroup.card_dvd_of_le hVP
  have hn2 : 2 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n <;> simp at hdvd4
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn2' : n = 2 := by omega
    subst hn2'
    apply hne
    have h1 : V = baum S ⊓ K :=
      Subgroup.eq_of_le_of_card_ge hVP (by rw [hn, hVcard]; norm_num)
    have h2 : conjR V x = baum S ⊓ K :=
      Subgroup.eq_of_le_of_card_ge hVxP (by rw [hn, hVxcard]; norm_num)
    exact h1.trans h2.symm
  have h8 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 hn3
  rw [← hn] at h8
  exact h8.trans (Subgroup.card_dvd_of_le inf_le_right)

end Eight

theorem lemma2_4_29_9_K_proved
    (h247 : Lemma2_4_27) (h245_4 : Lemma245_4) (hC54 : LemmaC54_3)
    (h314 : A314A5Excluded) (hP : Prop121Three) :
    ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G), A5Cfg G T M H S L →
      ∀ z u : G, A5Step7 T M H S L z u → oddCoreIn (centralizerElem u) = ⊥ →
        ∀ K : Subgroup G, IsComponentIn K (centralizerElem u) →
          z ∈ Subgroup.normalizer (K : Set G) → ⁅K, Subgroup.zpowers z⁆ = K → ¬ K ≤ M →
          ((¬ CentralQuotientAlt K 6 ∧ ¬ CentralQuotientAlt K 7) → Ch1.InducesInner z K) →
          IsListedComponent M (T ⊓ centralizerElem u) K z → K9Type ↥K ∧ u * z ∈ K := by
  intro G _ _ T M H S L cfg z u s7 _hodd K hK _hzN hcomm _hKM _hinn hlist
  obtain ⟨A, V, D⟩ := exists_u9data h247 h245_4 hC54 h314 cfg s7
  have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hN2 := relIndex_N_le_two hP cfg D hK
  have hAN : A ≤ centralizerElem u ⊓ Subgroup.normalizer (K : Set G) :=
    A_le_of_relIndex D inf_le_left hN2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAN.trans inf_le_right
  have hdat := a5_datum cfg D hK hcomm hN2
  have hty : K32ListedType ↥K := by
    rcases IsListedComponentW.k32ListedType_or hlist.toW with h | h | h
    · exact h
    · exact (false_of_centerG_card_three cfg D hK hAK (by
        have := h.2.1
        unfold centerG
        rw [Subgroup.card_map_of_injective K.subtype_injective]
        exact this)).elim
    · exact (false_of_centerG_card_three cfg D hK hAK (by
        have := h.2.1
        unfold centerG
        rw [Subgroup.card_map_of_injective K.subtype_injective]
        exact this)).elim
  have h8 : KInEightT ↥K := kInEightT_of_datum hq hty hdat
  have hcenter : Subgroup.center ↥K = ⊥ := kInEight_center_eq_bot hq h8
  have hZK : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1 := fun k hk hc =>
    congrArg Subtype.val (center_trivial_of_center_eq_bot hcenter ⟨k, hk⟩ fun x' =>
      Subtype.ext (hc x' x'.2))
  have hout : ∀ g : MulAut ↥K, g ^ 3 = 1 → g ∈ innAut ↥K := fun g hg =>
    kInEight_aut_three_inner hq h8 g hg
  have hmax : ∀ E : Subgroup G, E ≤ T → IsElemAbelian 2 E → Nat.card ↥E ≤ 16 := by
    have h27 : Lemma2_4_27Concl T H S L :=
      h247 G T M H S L cfg.cs (Or.inl ⟨cfg.alt5, cfg.single⟩)
    obtain ⟨x, hxT, hxS, -⟩ := s7.x_exists
    obtain ⟨r, hrS, hrR⟩ : ∃ r ∈ S, r ∉ baum S := by
      by_contra hcon
      push Not at hcon
      have h1 : (baum S).relIndex S = 1 := Subgroup.relIndex_eq_one.mpr hcon
      have := s7.R_index
      omega
    obtain ⟨A₁, -, hA₁⟩ := h27.2.1 x hxT hxS r hrS hrR
    have hQ : IsMaxElemAbelian T (pCoreOf 2 H) := (hA₁ _).mpr (Or.inl rfl)
    rw [s7.Q_eq] at hQ
    intro E hET hE
    have := hQ.2.2 E hET hE
    rw [D.U_card] at this
    exact this
  have huzK : u * z ∈ K := uz_mem_K D hK hcomm hN2 hZK hout hmax
  have hTu : T ⊓ centralizerElem u ≤ Subgroup.normalizer (K : Set G) :=
    D.Tu_le_normalizer hK huzK hZK
  have hVK : V ≤ K := D.hA.le_of_mem hAK huzK D.uz_mem D.uz_ne_one
  have hcent : ∀ g ∈ K, g * (u * z) = (u * z) * g → g ∈ T := fun g hg hc =>
    (mem_Tu_of_commute_uz D (hK.1 hg) hc).1
  have hT2 : IsPGroup 2 ↥T := cfg.cs.setting.isPGroup
  have h8' := h8
  unfold KInEightT at h8'
  rcases h8' with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | h17 | h33 | ⟨⟨e⟩⟩
  ·
    exfalso
    have h8d := eight_dvd_card cfg D hVK hTu
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup] at h8d
    revert h8d
    decide
  · exact ⟨Or.inl ⟨e⟩, huzK⟩
  · exact (false_of_noTwoCent e (noTwoCent_alt (n := 7) (by norm_num)) hT2 huzK (uz_sq D)
      D.uz_ne_one hcent).elim
  · exact (false_of_noTwoCent e (noTwoCent_alt (n := 8) (by norm_num)) hT2 huzK (uz_sq D)
      D.uz_ne_one hcent).elim
  · exact ⟨Or.inr (Or.inl ⟨e⟩), huzK⟩
  · exact ⟨Or.inr (Or.inr h17), huzK⟩
  · exact (false_of_noTwoCent (MulEquiv.refl ↥K) (noTwoCent_of_psl33 h33) hT2 huzK (uz_sq D)
      D.uz_ne_one hcent).elim
  · exact (false_of_noTwoCent (MulEquiv.refl ↥K) (noTwoCent_of_m11 ⟨e⟩) hT2 huzK (uz_sq D)
      D.uz_ne_one hcent).elim

end CFSG.QuasithinUnique.A5
