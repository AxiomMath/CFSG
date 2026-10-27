module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveFrame

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix SectionSix.BarTools DeltaLocal DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem lemma_6_5_two (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (i : Fin r) :
    ∃ x ∈ aschbacherThm5Preimage D (Abar i) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) g,
      x ∉ factorZStar D Abar i ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hstar : ∀ x ∈ aschbacherThm5Preimage D (Abar i) ⊓
      rightConjugate (Subgroup.normalizer (D : Set G)) g,
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ factorZStar D Abar i :=
    fun x hx hk => by_contra fun hz => hcon ⟨x, hx, hz, hk⟩
  obtain ⟨-, -, hg, U, hU⟩ := hΔ
  have hgH : g ∉ Subgroup.normalizer (D : Set G) :=
    fun h => hg ((rightConjugate_eq_self_iff _ g).mpr (Subgroup.le_normalizer h))
  set A := aschbacherThm5Preimage D (Abar i) with hAdef
  set Hg := rightConjugate (Subgroup.normalizer (D : Set G)) g with hHgdef
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hZg : rightConjugate (zStar D Abar) g ≤ Hg :=
    AschbacherTheorem3.rightConjugate_le_rightConjugate zStar_le_normalizer g
  obtain ⟨V, hVA, hVel, hV4⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2)
    (Seven.two_le_pRank_inter h3 hin hC hg hU i)
  have hVZ : V ≤ zStar D Abar ⊓ Hg := fun v hv =>
    ⟨factorZStar_le_zStar hC.hyp i (hstar v (hVA hv) ⟨1, by rw [pow_one]; exact hVel.2 v hv⟩),
      (hVA hv).2⟩
  have hrank1 : 2 ≤ CFSG.Open.pRank 2 (zStar D Abar ⊓ Hg) :=
    CFSG.SectionRank.le_pRank (by norm_num) hVZ hVel hV4
  have heven : Even (Nat.card (zStar D Abar)) := by
    have h1 : Nat.card V ∣ Nat.card (zStar D Abar) :=
      Subgroup.card_dvd_of_le (hVZ.trans inf_le_left)
    rw [hV4] at h1
    exact even_iff_two_dvd.mpr ((dvd_pow_self 2 (by norm_num)).trans h1)
  have hrank2 := pRank_zStar_le hC heven hgH
  obtain ⟨E, hEQ, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2)
    (rightConjugate (zStar D Abar) g ⊓ Subgroup.normalizer (D : Set G))
  have hEZ : E ≤ rightConjugate (zStar D Abar) g := hEQ.trans inf_le_left
  have hEH : E ≤ Subgroup.normalizer (D : Set G) := hEQ.trans inf_le_right
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hEcard
  have hrankE : CFSG.Open.pRank 2 (rightConjugate (zStar D Abar) g ⊓
      Subgroup.normalizer (D : Set G)) ≤ CFSG.Open.pRank 2 E :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEel hEcard
  have hrankE2 : 2 ≤ CFSG.Open.pRank 2 E := (hrank1.trans hrank2).trans hrankE
  have hEC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ Hg := fun e he he1 =>
    centralizer_le_of_mem_zStar_conj hC g (hEZ he) ⟨1, by rw [pow_one]; exact hEel.2 e he⟩ he1
  have hEA : E ≤ Subgroup.normalizer (A : Set G) := by
    intro e he
    obtain ⟨W, hWE, hWel, hW4, heW⟩ := exists_fourGroup_mem hEel (hrank1.trans hrank2) hEcard he
    exact lemma_6_5_one hC hg ⟨hWE.trans hEH, hWel, hW4, fun w hw hw1 => hEC w (hWE hw) hw1⟩ i
      heW
  have hodd : Odd (Nat.card (rightConjugate (zStar D Abar) g ⊓ A : Subgroup G)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    have htZg : (t : G) ∈ rightConjugate (zStar D Abar) g := t.2.1
    have htA : (t : G) ∈ A := t.2.2
    have ht2 : ∃ k : ℕ, (t : G) ^ (2 ^ k) = 1 :=
      ⟨1, by rw [pow_one, ← ht']; exact pow_orderOf_eq_one _⟩
    have htZ := factorZStar_le_zStar hC.hyp i (hstar t ⟨htA, hZg htZg⟩ ht2)
    rw [eq_one_of_mem_zStar_inf hC hgH htZ htZg ht2, orderOf_one] at ht'
    omega
  have hEA0 : E ⊓ A = ⊥ :=
    two_subgroup_of_odd_eq_bot _ _ (hE2.to_le inf_le_left) hodd (inf_le_inf_right A hEZ)
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hEcard
    have : 2 ^ 2 ≤ 2 ^ CFSG.Open.pRank 2 (rightConjugate (zStar D Abar) g ⊓
        Subgroup.normalizer (D : Set G)) := Nat.pow_le_pow_right (by norm_num) (hrank1.trans hrank2)
    omega
  obtain ⟨e₀, he₀E, he₀2⟩ := exists_orderOf_eq_two hE2 hE1
  have he₀1 : e₀ ≠ 1 := fun h => by rw [h, orderOf_one] at he₀2; omega
  have he₀H : e₀ ∈ Subgroup.normalizer (D : Set G) := hEH he₀E
  have hCe₀ := hEC e₀ he₀E he₀1
  obtain ⟨m, K, hm, hK, hcomm, hgen⟩ := bar_factor_components hC.hyp i
  have hKl : ∀ l, IsComponentOf (K l) ⊤ := fun l => (hK l).1
  obtain ⟨l⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hKE : bar D E ≤ Subgroup.normalizer (K l : Set (Bar D)) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (mem_bar_iff D E x).mp hx
    by_cases he1 : (e : G) = 1
    · rw [show e = 1 from Subtype.ext he1, map_one]
      exact Subgroup.one_mem _
    by_contra hn
    have he2 : orderOf (e : G) = 2 := orderOf_eq_prime (hEel.2 _ he) he1
    obtain ⟨x, hx, hxZ, hx2⟩ :=
      exists_outer_of_moved (hEH he) (hEA he) he2 (hEC _ he he1) (hKl l) (hK l).2 hn
    exact hxZ (hstar x hx hx2)
  have hKH : ¬ K l ≤ bar D ((A ⊓ Hg) ⊔ E) := by
    intro hle
    obtain ⟨k, hkK, hk2, hkZ⟩ := exists_two_element_not_mem_centerOf (hKl l).2.2
    have hEN : E ≤ Subgroup.normalizer ((A ⊓ Hg : Subgroup G) : Set G) := fun e he =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hEA he, Subgroup.le_normalizer (hZg (hEZ he))⟩
    have hk' : k ∈ bar D (A ⊓ Hg) := by
      have h1 : k ∈ bar D ((A ⊓ Hg) ⊔ E) ⊓ bar D A := ⟨hle hkK, (hK l).2 hkK⟩
      rwa [← bar_inf_of_core_le (core_le_preimage D _), sup_inf_eq_of_le inf_le_left hEN hEA0]
        at h1
    obtain ⟨w, hw, hw2, rfl⟩ := exists_two_lift (inf_le_left.trans hAH) hk' hk2
    apply hkZ
    exact ⟨hkK, Subgroup.centralizer_le (hK l).2 ((mem_factorZStar_iff hw.1).mp (hstar w hw hw2))⟩
  have hZ : CFSG.Open.pRank 2 (AschbacherTheorem3.centerOf (K l) ⊓
      Subgroup.centralizer (bar D E : Set (Bar D))) ≤ CFSG.Open.pRank 2 (bar D E) := by
    obtain ⟨F, hFle, hFel, hFcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2)
      (AschbacherTheorem3.centerOf (K l) ⊓ Subgroup.centralizer (bar D E : Set (Bar D)))
    have hF2 : IsPGroup 2 F := IsPGroup.of_card hFcard
    have hFbar : F ≤ bar D (A ⊓ Subgroup.centralizer ({e₀} : Set G)) := by
      rw [bar_inf_centralizer (core_le_preimage D _) he₀H he₀2]
      intro f hf
      refine ⟨(hK l).2 (hFle hf).1.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact ((Subgroup.mem_centralizer_iff.mp (hFle hf).2) _
        (toBar_mem_bar D (h := ⟨e₀, he₀H⟩) he₀E)).symm
    obtain ⟨V', hV'le, hV'2, hV'F⟩ := lift_two_subgroup (inf_le_left.trans hAH) hF2 hFbar
    have hV'H : V' ≤ Subgroup.normalizer (D : Set G) := hV'le.trans (inf_le_left.trans hAH)
    have hV'card : Nat.card V' = 2 ^ CFSG.Open.pRank 2 (AschbacherTheorem3.centerOf (K l) ⊓
        Subgroup.centralizer (bar D E : Set (Bar D))) := by
      rw [← card_bar_of_isPGroup hV'2 hV'H, hV'F, hFcard]
    have hV'el : IsElemAbelian 2 V' :=
      RankOne.isElemAbelian_of_equiv (barEquiv hV'2 hV'H) (by rw [hV'F]; exact hFel)
    have hV'Z : V' ≤ zStar D Abar ⊓ Hg := by
      intro v hv
      refine ⟨factorZStar_le_zStar hC.hyp i ?_, hCe₀ (hV'le hv).2⟩
      have hvF : toBar D ⟨v, hV'H hv⟩ ∈ F := by
        rw [← hV'F]
        exact toBar_mem_bar D (h := ⟨v, hV'H hv⟩) hv
      exact (mem_factorZStar_iff (w := ⟨v, hV'H hv⟩) (hV'le hv).1).mpr
        (centerOf_le_centralizer hcomm hgen l (hFle hvF).1)
    exact (CFSG.SectionRank.le_pRank (by norm_num) hV'Z hV'el hV'card).trans
      (hrank2.trans (hrankE.trans (Seven.pRank_le_bar hEH)))
  obtain ⟨a, haK, ha2, haC, haZ⟩ :=
    exists_of_lemma_4_9 hin hC i hEZ hEH hE2 hEA hodd hrankE2 hKl hcomm hgen l hKE hKH hZ
  have hamem : a ∈ bar D (A ⊓ Subgroup.centralizer ({e₀} : Set G)) := by
    rw [bar_inf_centralizer (core_le_preimage D _) he₀H he₀2]
    refine ⟨(hK l).2 haK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp haC) _
      (toBar_mem_bar D (h := ⟨e₀, he₀H⟩) he₀E)).symm
  obtain ⟨w, hw, hw2, rfl⟩ := exists_two_lift (inf_le_left.trans hAH) hamem ha2
  apply haZ
  exact ⟨haK, Subgroup.centralizer_le (hK l).2
    ((mem_factorZStar_iff hw.1).mp (hstar w ⟨hw.1, hCe₀ hw.2⟩ hw2))⟩

end CFSG.ComponentClassification.AschbacherTheorem5
