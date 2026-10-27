module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalNineTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalEightThree
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalFiveTwo

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal.Nine

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem orbit_normalizes (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) {g : G}
    (hΔ : rightConjugate (Subgroup.normalizer (D : Set G)) g ∈
      deltaConjugates (Subgroup.normalizer (D : Set G))) (hr : 3 ≤ r) {i j k : Fin r}
    {P B : Subgroup G} (hPL : P ≤ rightConjugate (aschbacherThm5Preimage D (Abar i)) g)
    (hPH : P ≤ Subgroup.normalizer (D : Set G)) (hP2 : IsPGroup 2 P) (hBD : B ≤ D)
    (hjB : aschbacherThm5Preimage D (Abar j) ≤ B) (hBk : B ≤ centralizing D (Abar k))
    (hPB : P ≤ Subgroup.normalizer (B : Set G)) :
    P ≤ Subgroup.normalizer (aschbacherThm5Preimage D (Abar j) : Set G) ∧
      ∃ Q : Subgroup G, IsSylowOf 2 Q (aschbacherThm5Preimage D (Abar j) ⊓
        rightConjugate (Subgroup.normalizer (D : Set G)) g) ∧ ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set Hg := rightConjugate H g with hHgdef
  set L := rightConjugate (aschbacherThm5Preimage D (Abar i)) g with hLdef
  have hg : g ∉ H := by
    obtain ⟨-, -, hne, -⟩ := hΔ
    exact fun h => hne ((rightConjugate_eq_self_iff _ g).mpr (Subgroup.le_normalizer h))
  have hLHg : L ≤ Hg := AschbacherTheorem3.rightConjugate_le_rightConjugate
    ((preimage_le D _).trans Subgroup.le_normalizer) g
  have hPHg : P ≤ Hg := hPL.trans hLHg
  have hPK : P ≤ Subgroup.normalizer ((B ⊓ Hg : Subgroup G) : Set G) := fun p hp =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hPB hp, Subgroup.le_normalizer (hPHg hp)⟩
  obtain ⟨Q₀, hQ₀, hPQ₀⟩ := exists_invariant_sylow' hP2 hPK
  have hQ₀K : Q₀ ≤ B ⊓ Hg := hQ₀.le
  have hQ₀B : Q₀ ≤ B := hQ₀K.trans inf_le_left
  have hQP2 : IsPGroup 2 (Q₀ ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hQ₀.isPGroup hP2 hPQ₀
  have hBN : Q₀ ⊔ P ≤ Subgroup.normalizer (B : Set G) :=
    sup_le (hQ₀B.trans Subgroup.le_normalizer) hPB
  have hQN : Q₀ ≤ Subgroup.normalizer (P : Set G) := by
    intro x hx
    have hxHg : x ∈ Hg := (hQ₀K hx).2
    have hKxQP : P ⊔ rightConjugate P x ≤ Q₀ ⊔ P := by
      refine sup_le le_sup_right fun y hy => ?_
      rw [mem_rightConjugate_iff] at hy
      have := (Q₀ ⊔ P).mul_mem ((Q₀ ⊔ P).mul_mem (Subgroup.mem_sup_left (Q₀.inv_mem hx))
        (Subgroup.mem_sup_right hy)) (Subgroup.mem_sup_left hx)
      simpa [mul_assoc] using this
    have hKxL : P ⊔ rightConjugate P x ≤ L ⊔ rightConjugate L x :=
      sup_le_sup hPL (AschbacherTheorem3.rightConjugate_le_rightConjugate hPL x)
    have hKx2 : IsPGroup 2 (P ⊔ rightConjugate P x : Subgroup G) := hQP2.to_le hKxQP
    have hKxB : (P ⊔ rightConjugate P x) ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      intro t ht
      obtain ⟨n, hn⟩ := hKx2 ⟨t, ht.1⟩
      exact Subgroup.mem_bot.mpr (eq_one_of_mem_cross hC hg hr (i := i) hxHg hBk
        ⟨hKxL ht.1, ht.2⟩ ⟨n, by simpa using congrArg Subtype.val hn⟩)
    have hPBb : P ⊓ B = ⊥ :=
      le_bot_iff.mp (by rw [← hKxB]; exact inf_le_inf_right B le_sup_left)
    have hc1 := AschbacherTheorem3.card_sup_of_le_normalizer (hKxQP.trans hBN)
      (by rw [inf_comm]; exact hKxB)
    have hc2 := AschbacherTheorem3.card_sup_of_le_normalizer hPB (by rw [inf_comm]; exact hPBb)
    have hle : B ⊔ (P ⊔ rightConjugate P x) ≤ B ⊔ P :=
      sup_le le_sup_left (hKxQP.trans (sup_le (hQ₀B.trans le_sup_left) le_sup_right))
    have hc3 := Subgroup.card_le_of_le hle
    rw [hc1, hc2] at hc3
    have hKxP : Nat.card (P ⊔ rightConjugate P x : Subgroup G) ≤ Nat.card P :=
      Nat.le_of_mul_le_mul_left hc3 Nat.card_pos
    have hKxeq : P = P ⊔ rightConjugate P x := Subgroup.eq_of_le_of_card_ge le_sup_left hKxP
    have hPx : rightConjugate P x ≤ P :=
      le_sup_right.trans (le_of_eq hKxeq.symm)
    have hPxeq : rightConjugate P x = P :=
      Subgroup.eq_of_le_of_card_ge hPx (by rw [rightConjugate_card])
    exact (rightConjugate_eq_self_iff P x).mp hPxeq
  have hPQbot : P ⊓ Q₀ = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨n, hn⟩ := hP2 ⟨t, ht.1⟩
    have ht' : t ∈ (L ⊔ rightConjugate L 1) ⊓ B :=
      ⟨Subgroup.mem_sup_left (hPL ht.1), hQ₀B ht.2⟩
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_cross hC hg hr (i := i) Hg.one_mem hBk ht'
      ⟨n, by simpa using congrArg Subtype.val hn⟩)
  have hcomm : ∀ p ∈ P, ∀ q ∈ Q₀, p * q = q * p := by
    intro p hp q hq
    have h1 : p⁻¹ * q⁻¹ * p * q ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hQN hq)) p).mp hp
      have h := P.mul_mem (P.inv_mem hp) this
      simpa [mul_assoc] using h
    have h2 : p⁻¹ * q⁻¹ * p * q ∈ Q₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPQ₀ hp)) q⁻¹).mp
        (Q₀.inv_mem hq)
      have h := Q₀.mul_mem this hq
      simpa [mul_assoc] using h
    have h3 : p⁻¹ * q⁻¹ * p * q ∈ P ⊓ Q₀ := ⟨h1, h2⟩
    rw [hPQbot, Subgroup.mem_bot] at h3
    calc p * q = q * p * (p⁻¹ * q⁻¹ * p * q) := by group
      _ = q * p := by rw [h3, mul_one]
  have hAjK : aschbacherThm5Preimage D (Abar j) ⊓ Hg ≤ B ⊓ Hg := inf_le_inf_right Hg hjB
  have hKN : B ⊓ Hg ≤ Subgroup.normalizer
      ((aschbacherThm5Preimage D (Abar j) ⊓ Hg : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Eight.le_normalizer_factor hC j (hBD hy.1), Subgroup.le_normalizer hy.2⟩
  have hQ := hQ₀.inf_of_le_normalizer hAjK hKN
  refine ⟨?_, _, hQ, fun p hp q hq => hcomm p hp q hq.1⟩
  obtain ⟨x₀, hx₀, hx₀Z, k₀, hk₀⟩ := lemma_6_5_two h3 hin hC hΔ j
  obtain ⟨c, hc, hcle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hQ
    (Five.isPGroup_zpowers_of_pow hk₀) (Subgroup.zpowers_le.mpr hx₀)
  have hq : c⁻¹ * x₀ * c ∈ Q₀ ⊓ (aschbacherThm5Preimage D (Abar j) ⊓ Hg) :=
    hcle (AschbacherTheorem3.conj_mem_rightConjugate (Subgroup.mem_zpowers x₀) c)
  have hqZ : c⁻¹ * x₀ * c ∉ factorZStar D Abar j := by
    intro h
    apply hx₀Z
    have := conj_mem_factorZStar (c := c) hc.1 h
    simpa [mul_assoc] using this
  intro p hp
  by_contra hpN
  obtain ⟨j', hj'⟩ := hC.hyp.hperm p (hPH hp) j
  have hjj : j' ≠ j := by
    rintro rfl
    exact hpN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hj')
  have hqj' : c⁻¹ * x₀ * c ∈ aschbacherThm5Preimage D (Abar j') := by
    rw [← hj']
    refine ⟨c⁻¹ * x₀ * c, hq.2.1, ?_⟩
    have h := hcomm p hp _ hq.1
    show p * (c⁻¹ * x₀ * c) * p⁻¹ = c⁻¹ * x₀ * c
    rw [h]
    group
  exact hqZ ⟨hq.2.1, factor_le_centralizing hC.hyp.hcomm (Ne.symm hjj) hqj'⟩

end DeltaLocal.Nine

end CFSG.ComponentClassification.AschbacherTheorem5
