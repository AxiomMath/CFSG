module

public import CFSG.ClassicalInvolution.Asc77.WP3L52Comp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.LocalCores CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Counting

variable {X : Type} [Group X]

theorem thm5IH_comm_of_sq {A : Subgroup X} (hA2 : ∀ a ∈ A, a * a = 1) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  intro x hx y hy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hA2 x hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hA2 y hy)
  have h := inv_eq_of_mul_eq_one_right (hA2 (x * y) (A.mul_mem hx hy))
  rw [mul_inv_rev, hxi, hyi] at h
  exact h.symm

theorem thm5IH_mem_or_mul_mem {B E : Subgroup X} (hEB : E ≤ B) (hB : Nat.card B = 4)
    (hE : 2 ≤ Nat.card E) {y : X} (hyB : y ∈ B) (hyE : y ∉ E) {x : X} (hxB : x ∈ B) :
    x ∈ E ∨ x * y ∈ E := by
  set H : Subgroup B := E.subgroupOf B with hH
  have hcardH : Nat.card H = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv
  have h1 : Nat.card H * H.index = 4 := by rw [Subgroup.card_mul_index, hB]
  have h2 : H.index ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one] at h
    have : (⟨y, hyB⟩ : B) ∈ H := by rw [h]; exact Subgroup.mem_top _
    exact hyE (Subgroup.mem_subgroupOf.mp this)
  have h3 : H.index ≠ 0 := by
    intro h
    rw [h] at h1
    omega
  have hidx : H.index = 2 := by
    rw [hcardH] at h1
    by_contra hne
    have h4 : 3 ≤ H.index := by omega
    nlinarith
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hxB⟩ : B)) (b := ⟨y, hyB⟩)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
  by_cases hx : x ∈ E
  · exact Or.inl hx
  · refine Or.inr (key.mpr ?_)
    exact ⟨fun h => absurd h hx, fun h => absurd h hyE⟩

end Counting

section Main

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem thm5IH_commutator_centralizes {L : Subgroup X} {x e : X}
    (hx : x ∈ Subgroup.normalizer (L : Set X)) (he : ∀ k ∈ L, e * k = k * e) :
    ∀ k ∈ L, ⁅e, x⁆ * k = k * ⁅e, x⁆ := by
  intro k hk
  have h1 := Lemma52Proof.commutator_centralizes_of_centralizes
    (conjSub_eq_of_mem_normalizer hx) he k hk
  have h2 : ⁅e, x⁆ = ⁅x, e⁆⁻¹ := (commutatorElement_inv x e).symm
  rw [h2]
  have h3 : Commute (⁅x, e⁆ : X) k := h1
  exact h3.inv_left.eq

theorem thm5IH_alphaOf_eq_bot_of_components (hO : CFSG.pPrimeCore 2 X = ⊥) {A : Subgroup X}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA4 : Nat.card A = 4)
    (hcomp : ∀ L : Subgroup X, IsComponent L → A ≤ Subgroup.normalizer (L : Set X) ∧
      ((∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ L, a * x = x * a) → alphaOf (inducedImage L A) = ⊥)) :
    alphaOf A = ⊥ := by
  have hAcomm := thm5IH_comm_of_sq hA2
  rw [alphaOf_eq_bot_iff]
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  ·
    have haa : a * a = 1 := hA2 a ha
    have hAC : ∀ b ∈ A, b ∈ Subgroup.centralizer ({a} : Set X) := fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm b hb a ha)
    by_contra hD0
    have hDP : ⁅involutionOddCore a, A⁆ ≤ involutionOddCore a := by
      rw [Subgroup.commutator_le]
      intro p hp b hb
      have e : ⁅p, b⁆ = p * (b * p⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (involutionOddCore a).mul_mem hp
        (conj_mem_involutionOddCore (hAC b hb) ((involutionOddCore a).inv_mem hp))
    obtain ⟨L, hL, x₀, hx₀, y₀, hy₀, hxy₀⟩ := Lemma52Proof.exists_component_moved hO haa ha1 hDP hD0
    obtain ⟨hAN, hfaith⟩ := hcomp L hL
    have haN := hAN ha
    have key : ∀ p ∈ involutionOddCore a, ∀ b ∈ A, ∀ y ∈ L, ⁅p, b⁆ * y = y * ⁅p, b⁆ := by
      intro p hp b hb
      have hpN : p ∈ Subgroup.normalizer (L : Set X) :=
        mem_normalizer_of_conjSub_eq
          (Lemma52Proof.normalizes_component_of_mem_involutionOddCore hL haa hp)
      have hbN := hAN hb
      have hcN : ⁅p, b⁆ ∈ Subgroup.normalizer (L : Set X) := by
        simp only [commutatorElement_def]
        exact (Subgroup.normalizer (L : Set X)).mul_mem
          ((Subgroup.normalizer (L : Set X)).mul_mem
            ((Subgroup.normalizer (L : Set X)).mul_mem hpN hbN)
            ((Subgroup.normalizer (L : Set X)).inv_mem hpN))
          ((Subgroup.normalizer (L : Set X)).inv_mem hbN)
      by_cases haL : ∀ x ∈ L, a * x = x * a
      ·
        have hpc := Lemma52Proof.centralizes_of_centralizes_involution hL hp haL
        exact thm5IH_commutator_centralizes hbN hpc
      · by_cases hf : ∀ a' ∈ A, a' ≠ 1 → ¬ ∀ x ∈ L, a' * x = x * a'
        ·
          have hα := (hfaith hf)
          have hd1' : toInducedAutOn L ⟨a, haN⟩ ≠ 1 := by
            have hy := hf a ha ha1
            push Not at hy
            obtain ⟨y, hy, hay⟩ := hy
            exact Lemma52Proof.toInducedAutOn_ne_one_of_moved L haN hy hay
          have h1 : toInducedAutOn L ⟨p, hpN⟩ ∈ involutionOddCore (toInducedAutOn L ⟨a, haN⟩) :=
            Lemma52Proof.toInducedAutOn_mem_involutionOddCore L haa haN hpN hp
          have h2 : toInducedAutOn L ⟨b, hbN⟩ ∈ inducedImage L A :=
            Lemma52Proof.toInducedAutOn_mem_inducedImage L A hb hbN
          have h3 : toInducedAutOn L ⟨a, haN⟩ ∈ inducedImage L A :=
            Lemma52Proof.toInducedAutOn_mem_inducedImage L A ha haN
          have h4 : ⁅toInducedAutOn L ⟨p, hpN⟩, toInducedAutOn L ⟨b, hbN⟩⁆ ∈
              alphaOf (inducedImage L A) :=
            commutator_le_alphaOf (inducedImage L A) h3 hd1'
              (Subgroup.commutator_mem_commutator h1 h2)
          rw [hα, Subgroup.mem_bot] at h4
          have h5 : toInducedAutOn L ⟨⁅p, b⁆, hcN⟩ = 1 := by
            rw [← h4, ← map_commutatorElement]
            rfl
          exact Lemma52Proof.commute_of_toInducedAutOn_eq_one L hcN h5
        ·
          push Not at hf
          obtain ⟨a₀, ha₀, ha₀1, ha₀c⟩ := hf
          set E : Subgroup X := A ⊓ Subgroup.centralizer (L : Set X) with hE
          have hmemE : ∀ e : X, e ∈ E ↔ e ∈ A ∧ ∀ y ∈ L, e * y = y * e := by
            intro e
            rw [hE, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
            exact and_congr_right fun _ =>
              ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩
          have ha₀E : a₀ ∈ E := (hmemE a₀).mpr ⟨ha₀, ha₀c⟩
          have haE : a ∉ E := fun h => haL ((hmemE a).mp h).2
          have hEA : E ≤ A := fun e he => ((hmemE e).mp he).1
          have hcardE : 2 ≤ Nat.card E := by
            classical
            have h1 : (1 : X) ∈ E := E.one_mem
            have hne : (1 : X) ≠ a₀ := fun h => ha₀1 h.symm
            have : ({1, a₀} : Finset X).card = 2 := Finset.card_pair hne
            calc 2 = ({1, a₀} : Finset X).card := this.symm
              _ = (↑({1, a₀} : Finset X) : Set X).ncard := (Set.ncard_coe_finset _).symm
              _ ≤ (E : Set X).ncard := by
                refine Set.ncard_le_ncard ?_ (Set.toFinite _)
                intro z hz
                simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
                  Set.mem_singleton_iff] at hz
                rcases hz with rfl | rfl
                · exact h1
                · exact ha₀E
              _ = Nat.card E := (Nat.card_coe_set_eq _).symm
          have hpa : p * a = a * p :=
            Subgroup.mem_centralizer_singleton_iff.mp
              (involutionOddCore_le_centralizer a hp)
          have hρb : ∀ b ∈ A, ∀ hbN : b ∈ Subgroup.normalizer (L : Set X),
              toInducedAutOn L ⟨b, hbN⟩ = 1 ∨
                toInducedAutOn L ⟨b, hbN⟩ = toInducedAutOn L ⟨a, haN⟩ := by
            intro b hb hbN
            rcases thm5IH_mem_or_mul_mem hEA hA4 hcardE ha haE hb with h | h
            · left
              exact Lemma52Proof.toInducedAutOn_eq_one_of_commute L hbN ((hmemE b).mp h).2
            · right
              have hbaN : b * a ∈ Subgroup.normalizer (L : Set X) := mul_mem hbN haN
              have h1 : toInducedAutOn L ⟨b * a, hbaN⟩ = 1 :=
                Lemma52Proof.toInducedAutOn_eq_one_of_commute L hbaN ((hmemE _).mp h).2
              have h2 : toInducedAutOn L ⟨b * a, hbaN⟩ =
                  toInducedAutOn L ⟨b, hbN⟩ * toInducedAutOn L ⟨a, haN⟩ := by
                rw [← map_mul]
                rfl
              rw [h2] at h1
              have h3 : toInducedAutOn L ⟨a, haN⟩ * toInducedAutOn L ⟨a, haN⟩ = 1 := by
                rw [← map_mul]
                have : (⟨a, haN⟩ : ↥(Subgroup.normalizer (L : Set X))) * ⟨a, haN⟩ = 1 :=
                  Subtype.ext haa
                rw [this, map_one]
              calc toInducedAutOn L ⟨b, hbN⟩
                  = toInducedAutOn L ⟨b, hbN⟩ * (toInducedAutOn L ⟨a, haN⟩ *
                      toInducedAutOn L ⟨a, haN⟩) := by rw [h3, mul_one]
                _ = (toInducedAutOn L ⟨b, hbN⟩ * toInducedAutOn L ⟨a, haN⟩) *
                      toInducedAutOn L ⟨a, haN⟩ := by rw [mul_assoc]
                _ = toInducedAutOn L ⟨a, haN⟩ := by rw [h1, one_mul]
          have hcommρ : toInducedAutOn L ⟨p, hpN⟩ * toInducedAutOn L ⟨a, haN⟩ =
              toInducedAutOn L ⟨a, haN⟩ * toInducedAutOn L ⟨p, hpN⟩ := by
            rw [← map_mul, ← map_mul]
            congr 1
            exact Subtype.ext hpa
          have h5 : toInducedAutOn L ⟨⁅p, b⁆, hcN⟩ = 1 := by
            have e1 : toInducedAutOn L ⟨⁅p, b⁆, hcN⟩ =
                ⁅toInducedAutOn L ⟨p, hpN⟩, toInducedAutOn L ⟨b, hbN⟩⁆ := by
              rw [← map_commutatorElement]
              rfl
            rw [e1, commutatorElement_eq_one_iff_mul_comm]
            rcases hρb b hb hbN with h | h
            · rw [h, mul_one, one_mul]
            · rw [h]
              exact hcommρ
          exact Lemma52Proof.commute_of_toInducedAutOn_eq_one L hcN h5
    have hDL : ⁅involutionOddCore a, A⁆ ≤ Subgroup.centralizer (L : Set X) := by
      rw [Subgroup.commutator_le]
      intro p hp b hb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (key p hp b hb y hy).symm
    exact hxy₀ (Subgroup.mem_centralizer_iff.mp (hDL hx₀) y₀ hy₀).symm
  ·
    change deltaCore A = ⊥
    obtain ⟨f₀, hf₀A, hf₀1⟩ := exists_ne_one_of_card_eq_two_pow (S := A) (n := 2) (by norm_num)
      (by rw [hA4]; norm_num)
    have hDf : ∀ f ∈ A, f ≠ 1 → deltaCore A ≤ involutionOddCore f := fun f hf hf1 =>
      deltaCore_le_involutionOddCore hf hf1
    have hodd : Odd (Nat.card (deltaCore A)) := odd_card_deltaCore hf₀A hf₀1
    have hord : orderOf f₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hA2 f₀ hf₀A) hf₀1
    have hQ : deltaCore A ≤ Subgroup.centralizer (CFSG.pCore 2 X : Set X) := by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have := commute_pCore_of_mem_involutionOddCore hord (hDf f₀ hf₀A hf₀1 hd) q hq
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    refine eq_bot_of_centralizes_pCore_of_centralizes_components hO hodd hQ ?_
    intro L hL d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨hAN, hfaith⟩ := hcomp L hL
    suffices h : d * y = y * d from h.symm
    by_cases hf : ∀ a' ∈ A, a' ≠ 1 → ¬ ∀ x ∈ L, a' * x = x * a'
    ·
      have hα := hfaith hf
      have hdN : d ∈ Subgroup.normalizer (L : Set X) :=
        mem_normalizer_of_conjSub_eq
          (Lemma52Proof.normalizes_component_of_mem_involutionOddCore hL (hA2 f₀ hf₀A)
            (hDf f₀ hf₀A hf₀1 hd))
      have hmem : toInducedAutOn L ⟨d, hdN⟩ ∈ alphaOf (inducedImage L A) := by
        refine iInf_le_alphaOf _ ?_
        simp only [Subgroup.mem_iInf]
        intro bh hbh hbh1
        obtain ⟨b, hbN, hbA, rfl⟩ := Lemma52Proof.exists_of_mem_inducedImage hbh
        have hb1 : b ≠ 1 := fun h1 => hbh1 (by
          have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set X))) = 1 := Subtype.ext h1
          rw [this, map_one])
        exact Lemma52Proof.toInducedAutOn_mem_involutionOddCore L (hA2 b hbA) hbN hdN
          (hDf b hbA hb1 hd)
      rw [hα, Subgroup.mem_bot] at hmem
      exact Lemma52Proof.commute_of_toInducedAutOn_eq_one L hdN hmem y hy
    ·
      push Not at hf
      obtain ⟨a₀, ha₀, ha₀1, ha₀c⟩ := hf
      exact Lemma52Proof.centralizes_of_centralizes_involution hL (hDf a₀ ha₀ ha₀1 hd) ha₀c y hy

end Main

end CFSG.ClassicalInvolution.Asc77
