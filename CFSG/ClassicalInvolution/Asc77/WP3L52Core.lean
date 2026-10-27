module

public import CFSG.ClassicalInvolution.Asc77.WP3L52Comp

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.LocalCores CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Hyp

variable {Q : Type} [Group Q]

@[expose] def MovedByAllIn (B Z K : Subgroup Q) : Prop :=
  ∀ x ∈ B, x ∉ Z → ∃ y ∈ K, x * y ≠ y * x

structure Hyp51In (B Z : Subgroup Q) : Prop where
  uniq : ∀ L₁ L₂ : Subgroup Q, IsComponent L₁ → IsComponent L₂ → MovedByAllIn B Z L₁ →
    MovedByAllIn B Z L₂ → L₁ = L₂
  alpha : ∀ L : Subgroup Q, IsComponent L → MovedByAllIn B Z L → alphaOf (inducedImage L B) = ⊥

end Hyp

namespace Lemma52Proof

section Counting

variable {Q : Type} [Group Q]

theorem isPGroup_two_of_sq {B : Subgroup Q} (hBsq : ∀ x ∈ B, x * x = 1) : IsPGroup 2 B :=
  fun g => ⟨1, Subtype.ext (by simpa [sq] using hBsq g g.2)⟩

theorem mem_or_mul_mem_of_card {B E : Subgroup Q} (hEB : E ≤ B) (hB : Nat.card B = 8)
    (hE : 4 ≤ Nat.card E) {y : Q} (hyB : y ∈ B) (hyE : y ∉ E) {x : Q} (hxB : x ∈ B) :
    x ∈ E ∨ x * y ∈ E := by
  set H : Subgroup B := E.subgroupOf B with hH
  have hcardH : Nat.card H = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEB).toEquiv
  have h1 : Nat.card H * H.index = 8 := by rw [Subgroup.card_mul_index, hB]
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

theorem four_le_card_of_mem {E : Subgroup Q} [Finite Q] {c b : Q} (hcE : c ∈ E) (hbE : b ∈ E)
    (hc1 : c ≠ 1) (hb1 : b ≠ 1) (hbc : b ≠ c) (hcc : c * c = 1) : 4 ≤ Nat.card E := by
  classical
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have h1 : (1 : Q) ∉ ({c, b, b * c} : Finset Q) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hc1.symm, hb1.symm, fun h => hbc ?_⟩
    have := eq_inv_of_mul_eq_one_left h.symm
    rw [this, hcinv]
  have h2 : c ∉ ({b, b * c} : Finset Q) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => hbc h.symm, fun h => hb1 ?_⟩
    have h' : b * c = 1 * c := by rw [one_mul]; exact h.symm
    exact mul_right_cancel h'
  have h3 : b ≠ b * c := fun h => hc1 (by
    have h' : b * c = b * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h')
  have hs : ({1, c, b, b * c} : Finset Q).card = 4 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_pair h3]
  have hsub : (↑({1, c, b, b * c} : Finset Q) : Set Q) ⊆ (E : Set Q) := by
    intro z hz
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact hcE
    · exact hbE
    · exact E.mul_mem hbE hcE
  calc 4 = ({1, c, b, b * c} : Finset Q).card := hs.symm
    _ = (↑({1, c, b, b * c} : Finset Q) : Set Q).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (E : Set Q).ncard := Set.ncard_le_ncard hsub
    _ = Nat.card E := (Nat.card_coe_set_eq _).symm

end Counting

section Unique

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem conjSub_eq_of_unique {B Z : Subgroup Q} (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (H : Hyp51In B Z) {L : Subgroup Q} (hL : IsComponent L) (hmv : MovedByAllIn B Z L) {b : Q}
    (hb : b ∈ B) : conjSub b L = L := by
  have hL' : IsComponent (conjSub b L) := isComponent_map_mulEquiv (MulAut.conj b) hL
  have hmv' : MovedByAllIn B Z (conjSub b L) := by
    intro x hx hxZ
    obtain ⟨y, hy, hxy⟩ := hmv x hx hxZ
    refine ⟨b * y * b⁻¹, conj_mem_conjSub hy, fun h => hxy ?_⟩
    have hxb : x * b = b * x := hcomm x hx b hb
    have hbx : b⁻¹ * x = x * b⁻¹ := by
      calc b⁻¹ * x = b⁻¹ * (x * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * x) * b⁻¹ := by rw [hxb]
        _ = x * b⁻¹ := by group
    have h1 : b * (x * y) * b⁻¹ = b * (y * x) * b⁻¹ := by
      calc b * (x * y) * b⁻¹ = (b * x) * y * b⁻¹ := by group
        _ = (x * b) * y * b⁻¹ := by rw [hxb]
        _ = x * (b * y * b⁻¹) := by group
        _ = (b * y * b⁻¹) * x := h
        _ = b * y * (b⁻¹ * x) := by group
        _ = b * y * (x * b⁻¹) := by rw [hbx]
        _ = b * (y * x) * b⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  exact H.uniq _ _ hL' hL hmv' hmv

end Unique

end Lemma52Proof

open Lemma52Proof

section Main

variable {Q : Type} [Group Q] [Finite Q]

theorem commutator_involutionOddCore_eq_bot_of_hyp51In (hO : CFSG.pPrimeCore 2 Q = ⊥)
    {B Z : Subgroup Q} {c : Q} (hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hBsq : ∀ x ∈ B, x * x = 1) (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hcZ : ∀ y : Q, y * c = c * y) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = c) (H : Hyp51In B Z) {d : Q}
    (hdB : d ∈ B) (hdZ : d ∉ Z) : ⁅involutionOddCore d, B⁆ = ⊥ := by
  have hd1 : d ≠ 1 := fun h => hdZ ((hZ d).mpr (Or.inl h))
  have hdd : d * d = 1 := hBsq d hdB
  have hcc : c * c = 1 := hBsq c hcB
  have hBC : ∀ b ∈ B, b ∈ Subgroup.centralizer ({d} : Set Q) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hBcomm b hb d hdB)
  by_contra hD0
  have hDP : ⁅involutionOddCore d, B⁆ ≤ involutionOddCore d := by
    rw [Subgroup.commutator_le]
    intro p hp b hb
    have e : ⁅p, b⁆ = p * (b * p⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (involutionOddCore d).mul_mem hp
      (conj_mem_involutionOddCore (hBC b hb) ((involutionOddCore d).inv_mem hp))
  obtain ⟨K, hK, x₀, hx₀, y₀, hy₀, hxy₀⟩ := exists_component_moved hO hdd hd1 hDP hD0
  have hnorm : ∀ x ∈ ⁅involutionOddCore d, B⁆, conjSub x K = K := fun x hx =>
    normalizes_component_of_mem_involutionOddCore hK hdd (hDP hx)
  have hdK : ¬ ∀ y ∈ K, d * y = y * d := fun h =>
    hxy₀ (centralizes_of_centralizes_involution hK (hDP hx₀) h y₀ hy₀)
  have hDD : ⁅⁅involutionOddCore d, B⁆, B⁆ = ⁅involutionOddCore d, B⁆ :=
    commutator_commutator_eq_of_isPGroup (isPGroup_two_of_sq hBsq)
      (odd_card_oddCoreIn (Subgroup.centralizer ({d} : Set Q)))
      (fun b hb => normalizer_oddCoreIn _ (hBC b hb))
  have hmoved : MovedByAllIn B Z K := by
    intro b hb hbZ
    by_contra hcon
    push Not at hcon
    have hb1 : b ≠ 1 := fun h => hbZ ((hZ b).mpr (Or.inl h))
    have hbc : b ≠ c := fun h => hbZ ((hZ b).mpr (Or.inr h))
    set E : Subgroup Q := B ⊓ Subgroup.centralizer (K : Set Q) with hE
    have hcen : ∀ e : Q, e ∈ E ↔ e ∈ B ∧ ∀ y ∈ K, e * y = y * e := by
      intro e
      rw [hE, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      exact and_congr_right fun _ => ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩
    have hcE : c ∈ E := (hcen c).mpr ⟨hcB, fun y _ => (hcZ y).symm⟩
    have hbE : b ∈ E := (hcen b).mpr ⟨hb, fun y hy => (hcon y hy)⟩
    have hdE : d ∉ E := fun h => hdK ((hcen d).mp h).2
    have hEB : E ≤ B := fun e he => ((hcen e).mp he).1
    have h4 : 4 ≤ Nat.card E := four_le_card_of_mem hcE hbE hc1 hb1 hbc hcc
    have hcomp : ∀ x ∈ ⁅involutionOddCore d, B⁆, ∀ b' ∈ B,
        ⁅x, b'⁆ ∈ Subgroup.centralizer (K : Set Q) := by
      intro x hx b' hb'
      have hxd : x * d = d * x :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (involutionOddCore_le_centralizer d (hDP hx))
      have key : ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (K : Set Q) := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (commutator_centralizes_of_centralizes (hnorm x hx) ((hcen e).mp he).2 k hk).symm
      rcases mem_or_mul_mem_of_card hEB hB8 h4 hdB hdE hb' with h | h
      · exact key b' h
      · have e : ⁅x, b'⁆ = ⁅x, b' * d⁆ := by
          have hxd' : x⁻¹ * d = d * x⁻¹ := by
            calc x⁻¹ * d = x⁻¹ * (d * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * d) * x⁻¹ := by rw [hxd]
              _ = d * x⁻¹ := by group
          simp only [commutatorElement_def]
          calc x * b' * x⁻¹ * b'⁻¹ = x * b' * (x⁻¹ * d * d⁻¹) * b'⁻¹ := by group
            _ = x * b' * (d * x⁻¹ * d⁻¹) * b'⁻¹ := by rw [hxd']
            _ = x * (b' * d) * x⁻¹ * (b' * d)⁻¹ := by group
        rw [e]
        exact key _ h
    have hDK : ⁅involutionOddCore d, B⁆ ≤ Subgroup.centralizer (K : Set Q) := by
      refine le_of_eq_of_le hDD.symm ?_
      rw [Subgroup.commutator_le]
      exact hcomp
    exact hxy₀ (Subgroup.mem_centralizer_iff.mp (hDK hx₀) y₀ hy₀).symm
  have hBN : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Q) := fun b hb =>
    mem_normalizer_of_conjSub_eq (conjSub_eq_of_unique hBcomm H hK hmoved hb)
  have hdN := hBN d hdB
  have hd1' : toInducedAutOn K ⟨d, hdN⟩ ≠ 1 := by
    obtain ⟨y, hy, hdy⟩ := hmoved d hdB hdZ
    exact toInducedAutOn_ne_one_of_moved K hdN hy hdy
  have hα := H.alpha K hK hmoved
  have hDK : ⁅involutionOddCore d, B⁆ ≤ Subgroup.centralizer (K : Set Q) := by
    rw [Subgroup.commutator_le]
    intro p hp b hb
    have hpN : p ∈ Subgroup.normalizer (K : Set Q) :=
      mem_normalizer_of_conjSub_eq (normalizes_component_of_mem_involutionOddCore hK hdd hp)
    have hbN := hBN b hb
    have hcN : ⁅p, b⁆ ∈ Subgroup.normalizer (K : Set Q) := by
      simp only [commutatorElement_def]
      exact (Subgroup.normalizer (K : Set Q)).mul_mem
        ((Subgroup.normalizer (K : Set Q)).mul_mem
          ((Subgroup.normalizer (K : Set Q)).mul_mem hpN hbN)
          ((Subgroup.normalizer (K : Set Q)).inv_mem hpN))
        ((Subgroup.normalizer (K : Set Q)).inv_mem hbN)
    have h1 : toInducedAutOn K ⟨p, hpN⟩ ∈ involutionOddCore (toInducedAutOn K ⟨d, hdN⟩) :=
      toInducedAutOn_mem_involutionOddCore K hdd hdN hpN hp
    have h2 : toInducedAutOn K ⟨b, hbN⟩ ∈ inducedImage K B :=
      toInducedAutOn_mem_inducedImage K B hb hbN
    have h3 : toInducedAutOn K ⟨d, hdN⟩ ∈ inducedImage K B :=
      toInducedAutOn_mem_inducedImage K B hdB hdN
    have h4 : ⁅toInducedAutOn K ⟨p, hpN⟩, toInducedAutOn K ⟨b, hbN⟩⁆ ∈ alphaOf (inducedImage K B) :=
      commutator_le_alphaOf (inducedImage K B) h3 hd1'
        (Subgroup.commutator_mem_commutator h1 h2)
    rw [hα, Subgroup.mem_bot] at h4
    have h5 : toInducedAutOn K ⟨⁅p, b⁆, hcN⟩ = 1 := by
      rw [← h4, ← map_commutatorElement]
      rfl
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (commute_of_toInducedAutOn_eq_one K hcN h5 k hk).symm
  exact hxy₀ (Subgroup.mem_centralizer_iff.mp (hDK hx₀) y₀ hy₀).symm

theorem deltaCore_eq_bot_of_hyp51In (hO : CFSG.pPrimeCore 2 Q = ⊥) {B Z : Subgroup Q} {c : Q}
    (hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBsq : ∀ x ∈ B, x * x = 1)
    (hB8 : Nat.card B = 8) (hcB : c ∈ B) (hc1 : c ≠ 1) (hcZ : ∀ y : Q, y * c = c * y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = c) (H : Hyp51In B Z) {F : Subgroup Q} (hFB : F ≤ B)
    (hF4 : Nat.card F = 4) : deltaCore F = ⊥ := by
  have hcc : c * c = 1 := hBsq c hcB
  have hDf : ∀ f ∈ F, f ≠ 1 → deltaCore F ≤ involutionOddCore f := fun f hf hf1 =>
    deltaCore_le_involutionOddCore hf hf1
  by_cases hcF : c ∈ F
  ·
    have hnormal : (involutionOddCore c).Normal :=
      ⟨fun n hn g => conj_mem_involutionOddCore
        (Subgroup.mem_centralizer_singleton_iff.mpr (hcZ g)) hn⟩
    have hodd : Odd (Nat.card (involutionOddCore c)) :=
      odd_card_oddCoreIn (Subgroup.centralizer ({c} : Set Q))
    have h2 : involutionOddCore c ≤ CFSG.pPrimeCore 2 Q :=
      le_sSup ⟨hnormal, Nat.coprime_two_left.2 hodd⟩
    rw [hO] at h2
    exact le_bot_iff.mp ((hDf c hcF hc1).trans h2)
  · by_contra hD0
    obtain ⟨f₀, hf₀F, hf₀1⟩ := exists_ne_one_of_card_eq_two_pow (S := F) (n := 2) (by norm_num)
      (by rw [hF4]; norm_num)
    obtain ⟨K, hK, x₀, hx₀, y₀, hy₀, hxy₀⟩ :=
      exists_component_moved hO (hBsq f₀ (hFB hf₀F)) hf₀1 (hDf f₀ hf₀F hf₀1) hD0
    have hnorm : ∀ x ∈ deltaCore F, conjSub x K = K := fun x hx =>
      normalizes_component_of_mem_involutionOddCore hK (hBsq f₀ (hFB hf₀F))
        (hDf f₀ hf₀F hf₀1 hx)
    have hfK : ∀ f ∈ F, f ≠ 1 → ¬ ∀ y ∈ K, f * y = y * f := fun f hf hf1 h =>
      hxy₀ (centralizes_of_centralizes_involution hK (hDf f hf hf1 hx₀) h y₀ hy₀)
    have hdec : ∀ x ∈ B, x ∈ F ∨ x * c ∈ F := fun x hx =>
      mem_or_mul_mem_of_card hFB hB8 hF4.symm.le hcB hcF hx
    have hmoved : MovedByAllIn B Z K := by
      intro b hb hbZ
      by_contra hcon
      push Not at hcon
      have hb1 : b ≠ 1 := fun h => hbZ ((hZ b).mpr (Or.inl h))
      have hbc : b ≠ c := fun h => hbZ ((hZ b).mpr (Or.inr h))
      rcases hdec b hb with h | h
      · exact hfK b h hb1 hcon
      · refine hfK (b * c) h (fun h1 => hbc ?_) (fun y hy => ?_)
        · rw [eq_inv_of_mul_eq_one_left h1]
          exact inv_eq_of_mul_eq_one_right hcc
        · calc b * c * y = b * (c * y) := by group
            _ = b * (y * c) := by rw [← hcZ y]
            _ = (b * y) * c := by group
            _ = (y * b) * c := by rw [hcon y hy]
            _ = y * (b * c) := by group
    have hBN : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Q) := fun b hb =>
      mem_normalizer_of_conjSub_eq (conjSub_eq_of_unique hBcomm H hK hmoved hb)
    have hcN := hBN c hcB
    have hc1' : toInducedAutOn K ⟨c, hcN⟩ = 1 :=
      toInducedAutOn_eq_one_of_commute K hcN (fun y _ => (hcZ y).symm)
    have hα := H.alpha K hK hmoved
    have hDK : deltaCore F ≤ Subgroup.centralizer (K : Set Q) := by
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (K : Set Q) :=
        mem_normalizer_of_conjSub_eq (hnorm x hx)
      have hmem : toInducedAutOn K ⟨x, hxN⟩ ∈ alphaOf (inducedImage K B) := by
        refine iInf_le_alphaOf _ ?_
        simp only [Subgroup.mem_iInf]
        intro bh hbh hbh1
        obtain ⟨b, hbN, hbB, rfl⟩ := exists_of_mem_inducedImage hbh
        rcases hdec b hbB with h | h
        · have hb1 : b ≠ 1 := fun h1 => hbh1 (by
            have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (K : Set Q))) = 1 := Subtype.ext h1
            rw [this, map_one])
          exact toInducedAutOn_mem_involutionOddCore K (hBsq b hbB) hbN hxN (hDf b h hb1 hx)
        · have hbcN : b * c ∈ Subgroup.normalizer (K : Set Q) := mul_mem hbN hcN
          have heq : toInducedAutOn K ⟨b, hbN⟩ = toInducedAutOn K ⟨b * c, hbcN⟩ := by
            have : (⟨b * c, hbcN⟩ : ↥(Subgroup.normalizer (K : Set Q))) =
                ⟨b, hbN⟩ * ⟨c, hcN⟩ := rfl
            rw [this, map_mul, hc1', mul_one]
          rw [heq] at hbh1 ⊢
          have hbc1 : b * c ≠ 1 := fun h1 => hbh1 (by
            have : (⟨b * c, hbcN⟩ : ↥(Subgroup.normalizer (K : Set Q))) = 1 := Subtype.ext h1
            rw [this, map_one])
          exact toInducedAutOn_mem_involutionOddCore K (hBsq (b * c) (B.mul_mem hbB hcB)) hbcN hxN
            (hDf (b * c) h hbc1 hx)
      rw [hα, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (commute_of_toInducedAutOn_eq_one K hxN hmem k hk).symm
    exact hxy₀ (Subgroup.mem_centralizer_iff.mp (hDK hx₀) y₀ hy₀).symm

end Main

end CFSG.ClassicalInvolution.Asc77
