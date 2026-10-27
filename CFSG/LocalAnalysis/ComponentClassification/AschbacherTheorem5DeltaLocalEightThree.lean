module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveFactor

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Eight

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem normalizer_factor_le (hC : Counterexample G D r Abar) (a : Fin r) :
    Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) ≤
      Subgroup.normalizer (D : Set G) :=
  factor_normalizer_le D r Abar hC.hyp.hii a

theorem le_normalizer_factor (hC : Counterexample G D r Abar) (a : Fin r) :
    D ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp
    (canonical_preimage_normal D Abar hC.hyp.hcomm hC.hyp.hgen a)

theorem inf_factor_eq_bot (hC : Counterexample G D r Abar) {a : Fin r} {x : G}
    (hx : x ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hTL : T ≤ rightConjugate (aschbacherThm5Preimage D (Abar a)) x) (hT2 : IsPGroup 2 T) :
    T ⊓ aschbacherThm5Preimage D (Abar a) = ⊥ := by
  obtain ⟨b, hba⟩ := Strong.exists_ne_index (two_le hC) a
  rw [eq_bot_iff]
  intro t ht
  have htT : t ∈ T := ht.1
  have htA : t ∈ aschbacherThm5Preimage D (Abar a) := ht.2
  rw [Subgroup.mem_bot]
  by_contra ht1
  obtain ⟨n, hn⟩ := hT2 ⟨t, htT⟩
  have htL : t ∈ aschbacherThm5Preimage (rightConjugate D x) (conjFactors D Abar x a) := by
    rw [preimage_conjFactors]
    exact hTL htT
  apply hx
  exact SixTools.mem_normalizer_of_fusion_conj hC (g := x) (y := t)
    ⟨n, by simpa using congrArg Subtype.val hn⟩ ht1
    (centralizes_of_mem_centralizing (factor_le_centralizing hC.hyp.hcomm hba htA))
    (centralizes_of_mem_centralizing (factor_le_centralizing (hC.conj x).hyp.hcomm hba htL))

theorem altThree_of_tight (h3 : AschbacherTheorem3.Theorem3Statement)
    (hC : Counterexample G D r Abar) {a : Fin r} {x : G}
    (hx : x ∉ Subgroup.normalizer (D : Set G)) {T : Subgroup G}
    (hTsyl : IsSylowOf 2 T (rightConjugate (aschbacherThm5Preimage D (Abar a)) x ⊓
      Subgroup.normalizer (aschbacherThm5Preimage D (Abar a) : Set G)))
    (hTcyc : ¬ IsCyclic T)
    (hstar : ∀ y ∈ aschbacherThm5Preimage D (Abar a),
      y ∉ Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) x : Set G) →
      T ⊓ rightConjugate T y = ⊥)
    (hidx : ∀ Q : Subgroup G, Q ≤ aschbacherThm5Preimage D (Abar a) ⊓
        Subgroup.normalizer (rightConjugate (aschbacherThm5Preimage D (Abar a)) x : Set G) →
      IsPGroup 2 Q → Nat.card Q ≤ Nat.card T) :
    Thm3AltThree (bar D (aschbacherThm5Preimage D (Abar a))) (bar D T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set L := rightConjugate A x with hLdef
  obtain ⟨b, hba⟩ := Strong.exists_ne_index (two_le hC) a
  have hAD : A ≤ D := preimage_le D _
  have hOA : aschbacherThm5Core D ≤ A := core_le_preimage D _
  have hDA := le_normalizer_factor hC a
  have hT2 : IsPGroup 2 T := hTsyl.isPGroup
  have hTL : T ≤ L := hTsyl.le.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (A : Set G) := hTsyl.le.trans inf_le_right
  have hTH : T ≤ Subgroup.normalizer (D : Set G) := hTN.trans (normalizer_factor_le hC a)
  have hT1 : T ≠ ⊥ := by
    rintro rfl
    exact hTcyc Factor.isCyclic_bot
  have hTA : T ⊓ A = ⊥ := inf_factor_eq_bot hC hx hTL hT2
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  set P := L ⊓ (A ⊔ T) with hPdef
  have hATN : A ⊔ T ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hTN
  have hTP : IsSylowOf 2 T P := hTsyl.of_le (le_inf hTL le_sup_right) (inf_le_inf_left _ hATN)
  have heven : Even (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hT1 (Subgroup.eq_bot_of_card_eq T (by rw [hn, pow_zero]))
    have h2T : 2 ∣ Nat.card T := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    exact even_iff_two_dvd.mpr (h2T.trans (Subgroup.card_dvd_of_le hTP.le))
  have hmul : ∀ z ∈ A ⊔ T, ∃ a₀ ∈ A, ∃ s ∈ T, z = a₀ * s := fun z hz => by
    have hz' : z ∈ ((A ⊔ T : Subgroup G) : Set G) := hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A T hTN] at hz'
    obtain ⟨a₀, ha₀, s, hs, rfl⟩ := Set.mem_mul.mp hz'
    exact ⟨a₀, ha₀, s, hs, rfl⟩
  have htight : ∀ y ∈ A ⊔ T, y ∉ Subgroup.normalizer (P : Set G) →
      Odd (Nat.card (P ⊓ rightConjugate P y : Subgroup G)) := by
    intro y hy hyN
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hw' : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
    have hwP : (w : G) ∈ P := w.2.1
    have hwPy : y * w * y⁻¹ ∈ P := (mem_rightConjugate_iff P y w).mp w.2.2
    have hyL : y ∉ Subgroup.normalizer (L : Set G) := fun hyL => hyN
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hyL, Subgroup.le_normalizer hy⟩)
    have hyw' : orderOf (y * w * y⁻¹) = 2 := by
      have hsc : SemiconjBy y (w : G) (y * w * y⁻¹) := by
        rw [SemiconjBy]
        group
      rw [← SemiconjBy.orderOf_eq y hsc]
      exact hw'
    obtain ⟨c, hc, hcw⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hTP
      (AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two hw') (Subgroup.zpowers_le.mpr hwP)
    obtain ⟨c', hc', hcw'⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hTP
      (AschbacherToolkit.isPGroup_zpowers_of_orderOf_eq_two hyw')
      (Subgroup.zpowers_le.mpr hwPy)
    have ht₁ : c⁻¹ * w * c ∈ T :=
      hcw (AschbacherTheorem3.conj_mem_rightConjugate (Subgroup.mem_zpowers _) c)
    have ht₂ : c'⁻¹ * (y * w * y⁻¹) * c' ∈ T :=
      hcw' (AschbacherTheorem3.conj_mem_rightConjugate (Subgroup.mem_zpowers _) c')
    have hzAT : c'⁻¹ * y * c ∈ A ⊔ T :=
      (A ⊔ T).mul_mem ((A ⊔ T).mul_mem ((A ⊔ T).inv_mem hc'.2) hy) hc.2
    have hzL : c'⁻¹ * y * c ∉ Subgroup.normalizer (L : Set G) := by
      intro hz
      apply hyL
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (hLN hc'.1) hz)
        (Subgroup.inv_mem _ (hLN hc.1))
      simpa [mul_assoc] using this
    obtain ⟨a₁, ha₁, s₁, hs₁, hz⟩ := hmul _ hzAT
    have ha₁L : a₁ ∉ Subgroup.normalizer (L : Set G) := by
      intro ha
      apply hzL
      rw [hz]
      exact Subgroup.mul_mem _ ha (hLN (hTL hs₁))
    have hmem : s₁ * (c⁻¹ * w * c) * s₁⁻¹ ∈ T ⊓ rightConjugate T a₁ := by
      refine ⟨T.mul_mem (T.mul_mem hs₁ ht₁) (T.inv_mem hs₁), (mem_rightConjugate_iff T a₁ _).mpr ?_⟩
      have h1 : a₁ * (s₁ * (c⁻¹ * w * c) * s₁⁻¹) * a₁⁻¹ = c'⁻¹ * (y * w * y⁻¹) * c' := by
        rw [show a₁ * (s₁ * (c⁻¹ * w * c) * s₁⁻¹) * a₁⁻¹ =
          (a₁ * s₁) * (c⁻¹ * w * c) * (a₁ * s₁)⁻¹ by group, ← hz]
        group
      rw [h1]
      exact ht₂
    rw [hstar a₁ ha₁ ha₁L, Subgroup.mem_bot] at hmem
    have hw1 : (w : G) = 1 := by
      calc (w : G) = c * s₁⁻¹ * (s₁ * (c⁻¹ * w * c) * s₁⁻¹) * s₁ * c⁻¹ := by group
        _ = 1 := by rw [hmem]; group
    rw [hw1, orderOf_one] at hw'
    omega
  obtain ⟨S, hS, hTS, hSN⟩ := exists_sylow_normalizer (le_sup_right : T ≤ A ⊔ T) hT2
  have hidx' : T.relIndex (S ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card T := by
    set W := S ⊓ Subgroup.normalizer (T : Set G) with hW
    have hTW : T ≤ W := le_inf hTS Subgroup.le_normalizer
    have hW2 : IsPGroup 2 W := hS.isPGroup.to_le inf_le_left
    have hTWA : T ≤ Subgroup.normalizer ((W ⊓ A : Subgroup G) : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTW ht), hTN ht⟩
    have hWAT : (W ⊓ A) ⊓ T = ⊥ := le_bot_iff.mp
      ((inf_le_inf_right T inf_le_right).trans (by rw [inf_comm]; exact hTA.le))
    have hWeq : (W ⊓ A) ⊔ T = W := by
      refine le_antisymm (sup_le inf_le_left hTW) (fun w hw => ?_)
      obtain ⟨a₀, ha₀, s, hs, rfl⟩ := hmul w (hS.le hw.1)
      have ha₀W : a₀ ∈ W := by
        have := W.mul_mem hw (W.inv_mem (hTW hs))
        simpa using this
      exact Subgroup.mul_mem_sup ⟨ha₀W, ha₀⟩ hs
    have hcard := AschbacherTheorem3.card_sup_of_le_normalizer hTWA hWAT
    rw [hWeq] at hcard
    have hrel := Subgroup.relIndex_mul_card T W
    rw [inf_eq_left.mpr hTW, hcard] at hrel
    rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel]
    refine hidx _ (le_inf inf_le_right fun y hy => ?_) (hW2.to_le inf_le_left)
    by_contra hyL
    have hbot := hstar y hy.2 hyL
    rw [(rightConjugate_eq_self_iff T y).mpr hy.1.2, inf_idem] at hbot
    exact hT1 hbot
  have hconc := thm3_bar h3 hAD hOA hDA hTH hTN hT2 hT1 hTA inf_le_right hTP heven htight hS hTS
    hSN hidx'
  obtain ⟨m, K, -, hK, -, hKgen⟩ := bar_factor_components hC.hyp a
  have hTC := bar_overlap_inf_centralizer hC (factor_le_centralizing hC.hyp.hcomm hba) hx hTL
    hT2 a
  have hex : ∃ l, ⁅K l, bar D T⁆ ≠ ⊥ := by
    by_contra hno
    push Not at hno
    apply hT1
    have hle : bar D A ≤ Subgroup.centralizer (bar D T : Set (Bar D)) := by
      rw [← hKgen]
      exact iSup_le fun l => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hno l)
    have hTbot : bar D T = ⊥ := by
      rw [eq_bot_iff, ← hTC]
      exact le_inf le_rfl (Subgroup.le_centralizer_iff.mp hle)
    exact (bar_eq_bot_iff_of_isPGroup hT2 hTH).mp hTbot
  obtain ⟨l, hl⟩ := hex
  rcases thm3_one_or_three (isPGroup_bar hT2) (bar_mono D hTS) (isPGroup_bar hS.isPGroup)
    (hK l).1 (hK l).2 hl hconc with h1 | h3'
  · exact absurd ((isCyclic_bar_iff hT2 hTH).mp h1.1) hTcyc
  · exact h3'

end DeltaLocal.Eight

end CFSG.ComponentClassification.AschbacherTheorem5
