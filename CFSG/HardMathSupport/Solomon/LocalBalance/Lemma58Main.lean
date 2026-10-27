module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58
public import CFSG.Quasithin.H13.A7Nat1238QZ
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_of_normalizes {A S B : Subgroup G} (hA : A ≤ S)
    (hB : B ≤ Subgroup.normalizer (S : Set G)) : ⁅A, B⁆ ≤ S := by
  refine Subgroup.commutator_le.2 fun x hx b hb => ?_
  have h1 : b * x⁻¹ * b⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.1 (hB hb) x⁻¹).1 (S.inv_mem (hA hx))
  have h2 := S.mul_mem (hA hx) h1
  rw [commutatorElement_def]
  simpa [mul_assoc] using h2

theorem even_card_of_le_of_pGroup_two {S H : Subgroup G} (hS : IsPGroup 2 S) (hne : S ≠ ⊥)
    (hle : S ≤ H) : Even (Nat.card H) := by
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq S hn
  have h2 : 2 ∣ Nat.card S := by
    rw [hn]; exact dvd_pow_self 2 hn0
  exact even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hle))

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {z : G} (hz : z ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, z = a * b := by
  have hcomm : ∀ (m : A) (n : B), Commute (A.subtype m) (B.subtype n) := fun m n => hc m m.2 n n.2
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range]; simp
  rw [← hrange] at hz
  obtain ⟨⟨m, n⟩, rfl⟩ := hz
  exact ⟨m, m.2, n, n.2, rfl⟩

omit [Finite G] in
theorem commutator_sup_le_of_centralizes {S0 E E' : Subgroup G}
    (hc : ∀ a ∈ E, ∀ b ∈ E', a * b = b * a) (hS0E : ∀ x ∈ S0, ∀ e ∈ E, x * e = e * x) :
    ⁅S0, E ⊔ E'⁆ ≤ ⁅S0, E'⁆ := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨e, he, e', he', rfl⟩ := exists_mul_of_mem_sup_of_commute hc hy
  have hxe : x * e = e * x := hS0E x hx e he
  have hee : e * e' = e' * e := hc e he e' he'
  have hce : Commute e x := hxe.symm
  have hee' : Commute e e' := hee
  have hcc : Commute e (x * e' * x⁻¹ * e'⁻¹) :=
    ((hce.mul_right hee').mul_right hce.inv_right).mul_right hee'.inv_right
  have h1 : ⁅x, e * e'⁆ = e * (x * e' * x⁻¹ * e'⁻¹) * e⁻¹ := by
    rw [commutatorElement_def]
    calc x * (e * e') * x⁻¹ * (e * e')⁻¹ = (x * e) * e' * x⁻¹ * e'⁻¹ * e⁻¹ := by group
      _ = (e * x) * e' * x⁻¹ * e'⁻¹ * e⁻¹ := by rw [hxe]
      _ = e * (x * e' * x⁻¹ * e'⁻¹) * e⁻¹ := by group
  have h2 : e * (x * e' * x⁻¹ * e'⁻¹) * e⁻¹ = x * e' * x⁻¹ * e'⁻¹ :=
    mul_inv_eq_iff_eq_mul.2 hcc.eq
  rw [h1, h2]
  exact Subgroup.commutator_mem_commutator hx he'

theorem lemma58_of_inputs (h57 : Lemma57) (hS : InputBZeroMaxS) : Lemma58 := by
  intro G _ _ m hstd hcase B hB B' hB'el h4 h3
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hrank4 : GLATwoLocalRank 3 G = 4 := hcase.2.1
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBcard : Nat.card B = 3 ^ 4 := by
    have := hB.1.2.1
    rwa [hrank4] at this
  have hweak : IsWeaklyBalancedWrt 3 2 B := h57 G m hstd hcase B hB
  obtain ⟨D₀, hD₀, S, hS2, hSne, hSΔ, hBS, hSB⟩ := hS G m hstd B hB
  obtain ⟨E, hE, hS0ne⟩ := exists_hyperplane_commutator_ne hBel hBcard hS2 hBS
    (by rw [hSB]; exact hSne)
  set C : Subgroup G := S ⊓ Subgroup.centralizer (E : Set G) with hC
  set S0 : Subgroup G := ⁅C, B⁆ with hS0
  have hEB : E ≤ B := hE.1
  have hEel : IsElemAbelian 3 E := hE.2.1
  have hEcard : Nat.card E = 3 ^ 3 := hE.2.2
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => elemAbelian_comm hBel ha hb
  have hBC : B ≤ Subgroup.normalizer (C : Set G) := by
    intro b hb
    refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hBS hb) x).1 hx.1
    · refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
      have h1 := Subgroup.mem_centralizer_iff.1 hx.2 e he
      have h2 := hcommB e (hEB he) b hb
      calc e * (b * x * b⁻¹) = (e * b) * x * b⁻¹ := by group
        _ = (b * e) * x * b⁻¹ := by rw [h2]
        _ = b * (e * x) * b⁻¹ := by group
        _ = b * (x * e) * b⁻¹ := by rw [h1]
        _ = (b * x * b⁻¹) * e := by
          calc b * (x * e) * b⁻¹ = b * x * (e * b⁻¹) := by group
            _ = b * x * (b⁻¹ * e) := by
              congr 1
              have := hcommB e (hEB he) b⁻¹ (B.inv_mem hb)
              exact this
            _ = (b * x * b⁻¹) * e := by group
  have hS0S : S0 ≤ S := commutator_le_of_normalizes inf_le_left hBS
  have hS02 : IsPGroup 2 S0 := hS2.to_le hS0S
  have hS0cE : S0 ≤ Subgroup.centralizer (E : Set G) := by
    refine Subgroup.commutator_le.2 fun x hx b hb => ?_
    refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
    have h1 := Subgroup.mem_centralizer_iff.1 hx.2 e he
    have hc1 : Commute e x := h1
    have hc2 : Commute e b := hcommB e (hEB he) b hb
    exact (((hc1.mul_right hc2).mul_right hc1.inv_right).mul_right hc2.inv_right).eq
  have hS0Δ : S0 ≤ GLADelta 3 E := by
    intro y hy
    simp only [GLADelta, Subgroup.mem_iInf]
    intro e he he1
    have hCle : C ≤ GLADelta 3 D₀ ⊓ Subgroup.centralizer ({e} : Set G) := by
      refine le_inf (inf_le_left.trans hSΔ) fun x hx => ?_
      have := Subgroup.mem_centralizer_iff.1 hx.2 e he
      exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
    exact hweak D₀ hD₀ e (hEB he) he1 (Subgroup.commutator_mono hCle le_rfl hy)
  have hS0B : ⁅S0, B⁆ = S0 := commutator_double_of_two_three hBel (hS2.to_le inf_le_left) hBC
  obtain ⟨D, hDB', hDpl, hS0D, E', hE', hα⟩ : ∃ D : Subgroup G, D ≤ B' ∧ IsPPlane 3 D ∧
      S0 ≤ GLADelta 3 D ∧ ∃ E' : Subgroup G, IsEkIn 3 3 (B ⊓ B') E' ∧
        Even (Nat.card (alphaE 3 2 E')) := by
    by_cases hEB' : E ≤ B'
    · have hE1 : IsEkIn 3 3 (B ⊓ B') E := ⟨le_inf hEB hEB', hEel, hEcard⟩
      obtain ⟨D, hDE, hDel, hDcard⟩ := exists_le_isElemAbelian_card (p := 3) hEel (n := 2)
        (by rw [hEcard]; exact pow_dvd_pow 3 (by norm_num))
      refine ⟨D, hDE.trans hEB', ⟨hDel, hDcard⟩,
        hS0Δ.trans (glaDelta_le_glaDelta_of_le hDE), E, hE1, ?_⟩
      exact even_card_of_le_of_pGroup_two hS02 hS0ne (hS0Δ.trans le_sup_right)
    · set E' : Subgroup G := B ⊓ B' with hE'def
      have hE'el : IsElemAbelian 3 E' := isElemAbelian_mono hBel inf_le_left
      obtain ⟨k, hk⟩ := (GL83.isPGroup_of_isElemAbelian hE'el).exists_card_eq
      have hk3 : 3 ≤ k := by
        have := pRank_eq_of_card hp hE'el hk
        omega
      have hk4 : k ≤ 4 := by
        have hd : 3 ^ k ∣ 3 ^ 4 := hk ▸ hBcard ▸ Subgroup.card_dvd_of_le (inf_le_left : E' ≤ B)
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd
      have hk4' : k ≠ 4 := by
        intro h
        apply hEB'
        have hEq : E' = B := by
          refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
          rw [hk, h, hBcard]
        have : B ≤ B' := hEq ▸ inf_le_right
        exact hEB.trans this
      have hE'card : Nat.card E' = 3 ^ 3 := by
        have : k = 3 := by omega
        rw [hk, this]
      have hcomm : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x := fun x hx y hy =>
        hcommB x (hEB hx) y hy.1
      have hmul := CFSG.Quasithin.H13.A7.card_sup_mul_card_inf_of_commute hcomm
      have hsupB : E ⊔ E' ≤ B := sup_le hEB inf_le_left
      have hEE' : ¬ E' ≤ E := by
        intro hle
        apply hEB'
        have hEq : E' = E := by
          refine Subgroup.eq_of_le_of_card_ge hle ?_
          rw [hEcard, hE'card]
        rw [← hEq]
        exact inf_le_right
      have hsup : E ⊔ E' = B := by
        have h1 : Nat.card E ∣ Nat.card (E ⊔ E' : Subgroup G) := Subgroup.card_dvd_of_le le_sup_left
        have h2 : Nat.card (E ⊔ E' : Subgroup G) ∣ 3 ^ 4 := hBcard ▸ Subgroup.card_dvd_of_le hsupB
        have h3' : Nat.card E ≠ Nat.card (E ⊔ E' : Subgroup G) := by
          intro h
          exact hEE' (by
            have hEq : E = E ⊔ E' := Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq h.symm)
            exact hEq ▸ le_sup_right)
        obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 h2
        rw [hEcard, hj'] at h1 h3'
        have hj3 : 3 ≤ j := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
        have hj4 : j = 4 := by
          have : j ≠ 3 := fun h => h3' (by rw [h])
          omega
        refine Subgroup.eq_of_le_of_card_ge hsupB ?_
        rw [hBcard, hj', hj4]
      have hEE'card : Nat.card (E ⊓ E' : Subgroup G) = 3 ^ 2 := by
        rw [hsup, hBcard, hEcard, hE'card] at hmul
        have : Nat.card (E ⊓ E' : Subgroup G) * 3 ^ 4 = 3 ^ 2 * 3 ^ 4 := by
          rw [mul_comm] at hmul
          calc _ = 3 ^ 3 * 3 ^ 3 := hmul
            _ = 3 ^ 2 * 3 ^ 4 := by norm_num
        exact Nat.eq_of_mul_eq_mul_right (by norm_num) this
      have hDE : E ⊓ E' ≤ E := inf_le_left
      have hDE' : E ⊓ E' ≤ E' := inf_le_right
      refine ⟨E ⊓ E', hDE'.trans inf_le_right,
        ⟨isElemAbelian_mono hEel hDE, hEE'card⟩,
        hS0Δ.trans (glaDelta_le_glaDelta_of_le hDE), E', ⟨le_rfl, hE'el, hE'card⟩, ?_⟩
      have hS0E : ⁅S0, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hS0cE
      have hS0E' : S0 = ⁅S0, E'⁆ := by
        calc S0 = ⁅S0, B⁆ := hS0B.symm
          _ = ⁅S0, E ⊔ E'⁆ := by rw [hsup]
          _ = ⁅S0, E'⁆ := by
              refine le_antisymm (commutator_sup_le_of_centralizes hcomm ?_) ?_
              · exact fun x hx e he => (Subgroup.mem_centralizer_iff.1 (hS0cE hx) e he).symm
              · exact Subgroup.commutator_mono le_rfl le_sup_right
      have hle : S0 ≤ alphaE 3 2 E' := by
        refine le_trans ?_ (le_sup_left : _ ≤ alphaE 3 2 E')
        refine le_trans ?_ (le_iSup₂_of_le (E ⊓ E') ⟨hDE', isElemAbelian_mono hEel hDE, hEE'card⟩ le_rfl)
        rw [hS0E']
        exact Subgroup.commutator_mono (hS0Δ.trans (glaDelta_le_glaDelta_of_le hDE)) le_rfl
      exact even_card_of_le_of_pGroup_two hS02 hS0ne hle
  have hDne : D ≠ ⊥ := by
    intro h
    have h1 := hDpl.2
    rw [h, Subgroup.card_bot] at h1
    have h2 : 1 < 3 ^ 2 := by norm_num
    omega
  have hYN : B' ≤ Subgroup.normalizer (GLADelta 3 D : Set G) := le_normalizer_gLADelta hB'el hDB'
  have hcop : ¬ 3 ∣ Nat.card (GLADelta 3 D) :=
    (hp.coprime_iff_not_dvd).1
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta hp hDne)
  have hev : Even (Nat.card (GLADelta 3 D)) :=
    even_card_of_le_of_pGroup_two hS02 hS0ne hS0D
  obtain ⟨T, hT, -, hT2, hB'T⟩ := exists_twoGroup_normalized_of_coprime_even hp (by norm_num)
    (GL83.isPGroup_of_isElemAbelian hB'el) hYN hcop hev
  have hrk : CFSG.Open.pRank 3 B' ≤ GLATwoLocalRank 3 G :=
    pRank_le_glaTwoLocalRank_of_normalizes hp hT hT2 hB'T
  obtain ⟨k, hk⟩ := (GL83.isPGroup_of_isElemAbelian hB'el).exists_card_eq
  have hk' : CFSG.Open.pRank 3 B' = k := pRank_eq_of_card hp hB'el hk
  have hk4 : k = 4 := by omega
  refine ⟨⟨⟨hB'el, ?_, T, hT, hT2, hB'T⟩, D, hDB', hDpl, ?_⟩, E', hE', hα⟩
  · rw [hk, hrank4, hk4]
  · exact even_card_of_le_of_pGroup_two hS02 hS0ne hS0D

end CFSG.HardMathSupport.Solomon.LocalBalance
