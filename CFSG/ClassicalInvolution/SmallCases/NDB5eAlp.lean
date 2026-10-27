module

public import CFSG.ClassicalInvolution.SmallCases.NDB5eTor
import CFSG.ClassicalInvolution.Balance.StrongPowSuMain
public import CFSG.ClassicalInvolution.SmallCases.NDB2Alpha

public section

namespace CFSG.ClassicalInvolution.NDB.Alpha

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem closure_pair_comm {K : Type*} [Group K] {x₁ x₂ : K} (h : x₁ * x₂ = x₂ * x₁) :
    ∀ u ∈ Subgroup.closure ({x₁, x₂} : Set K), ∀ v ∈ Subgroup.closure ({x₁, x₂} : Set K),
      u * v = v * u := by
  set S : Set K := {x₁, x₂} with hS
  have hSS : S ⊆ Subgroup.centralizer S := by
    intro a ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro b hb
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [rfl, h.symm, h, rfl]
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := (Subgroup.closure_le _).mpr hSS
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.centralizer S : Set K) :=
    (Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_centralizer_iff.mpr fun g hg =>
      ((Subgroup.mem_centralizer_iff.mp hg) x hx).symm
  intro u hu v hv
  exact ((Subgroup.mem_centralizer_iff.mp (h2 hu)) v (h1 hv)).symm

theorem alpha_toral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {z₁ z₂ s : G}
    (hA : IsElemAbelian 2 (Subgroup.closure ({z₁, z₂, s} : Set G)))
    (hA8 : Nat.card (Subgroup.closure ({z₁, z₂, s} : Set G)) = 8) (hs1 : s ≠ 1)
    {Φ : Set (Subgroup G)} (hN : NormalizesLayer Φ s) (D : LocalLieSystemAt p f Φ s)
    (j₀ : Fin D.card) (ht : D.tag j₀ = .PSL ∨ D.tag j₀ = .PSU)
    (hA1 : ¬ (D.tag j₀ = .PSL ∧ D.rank j₀ = 2))
    (hker : (secComponentHom hN D j₀).ker ≤ Subgroup.center (compModel D j₀).K)
    {R₁ R₂ : Subgroup (compModel D j₀).K}
    (hR₁ : R₁ ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D)
    (hR₂ : R₂ ∈ fundamentalSubgroups (D.tag j₀) (compModel D j₀).D) {L₁ L₂ : Subgroup G}
    (himg₁ : R₁.map (secComponentHom hN D j₀) = modOdd s L₁)
    (himg₂ : R₂.map (secComponentHom hN D j₀) = modOdd s L₂)
    (hU₁ : ∀ h, IsUniqueInvolution (modOdd s L₁) (oddQuotMk s ⟨z₁, h⟩))
    (hU₂ : ∀ h, IsUniqueInvolution (modOdd s L₂) (oddQuotMk s ⟨z₂, h⟩))
    (hz₂L₁ : ∀ h, conjSub (oddQuotMk s ⟨z₂, h⟩) (modOdd s L₁) = modOdd s L₁)
    (hmov : MovedByAll (Subgroup.closure ({z₁, z₂, s} : Set G)) s
      (secComponentHom hN D j₀).range) :
    alphaOf (inducedImage (secComponentHom hN D j₀).range
      (modOdd s (Subgroup.closure ({z₁, z₂, s} : Set G)))) = ⊥ := by
  set ψ := secComponentHom hN D j₀ with hψ
  set B := Subgroup.closure ({z₁, z₂, s} : Set G) with hB
  set Cs := Subgroup.centralizer ({s} : Set G) with hCs
  have hsB : s ∈ B := Subgroup.subset_closure (by simp)
  have hz₁B : z₁ ∈ B := Subgroup.subset_closure (by simp)
  have hz₂B : z₂ ∈ B := Subgroup.subset_closure (by simp)
  have hBC : B ≤ Cs := Lemma52Proof.le_centralizer_of_mem hA hsB
  have hz₁C := hBC hz₁B
  have hz₂C := hBC hz₂B
  have hG2 : D.tag j₀ ≠ .G2 := by rcases ht with h | h <;> rw [h] <;> decide
  have hD4 : D.tag j₀ ≠ .trialityD4 := by rcases ht with h | h <;> rw [h] <;> decide
  have h5 : 5 ≤ p ^ D.exp j₀ := by
    rcases D.exp_eq j₀ with h1 | ⟨h1, -⟩
    · rw [h1]
      exact hq
    · exact absurd h1 hD4
  obtain ⟨x₁, x₂, hx₁2, hx₂2, hx₁₂, hψ₁, hψ₂⟩ := exists_commuting_lifts hp2 h5 hG2 hD4 hA1 hker
    hR₁ hR₂ himg₁ himg₂ hz₁C hz₂C (hU₁ hz₁C) (hU₂ hz₂C) (hz₂L₁ hz₂C)
  set P := Subgroup.closure ({x₁, x₂} : Set (compModel D j₀).K) with hP
  have hPc := closure_pair_comm hx₁₂
  have key : ∀ a (ha : a ∈ B) (haC : a ∈ Cs), ∃ x ∈ P, x ^ 2 = 1 ∧ ∀ y ∈ ψ.range,
      oddQuotMk s ⟨a, haC⟩ * y * (oddQuotMk s ⟨a, haC⟩)⁻¹ = ψ x * y * (ψ x)⁻¹ := by
    have gen₁ : ∀ h : z₁ ∈ Cs, ∃ x ∈ P, x ^ 2 = 1 ∧ ∀ y ∈ ψ.range,
        oddQuotMk s ⟨z₁, h⟩ * y * (oddQuotMk s ⟨z₁, h⟩)⁻¹ = ψ x * y * (ψ x)⁻¹ := fun h =>
      ⟨x₁, Subgroup.subset_closure (by simp), by rw [sq]; exact hx₁2, fun y _ => by rw [hψ₁]⟩
    have gen₂ : ∀ h : z₂ ∈ Cs, ∃ x ∈ P, x ^ 2 = 1 ∧ ∀ y ∈ ψ.range,
        oddQuotMk s ⟨z₂, h⟩ * y * (oddQuotMk s ⟨z₂, h⟩)⁻¹ = ψ x * y * (ψ x)⁻¹ := fun h =>
      ⟨x₂, Subgroup.subset_closure (by simp), by rw [sq]; exact hx₂2, fun y _ => by rw [hψ₂]⟩
    have gen₃ : ∀ h : s ∈ Cs, ∃ x ∈ P, x ^ 2 = 1 ∧ ∀ y ∈ ψ.range,
        oddQuotMk s ⟨s, h⟩ * y * (oddQuotMk s ⟨s, h⟩)⁻¹ = ψ x * y * (ψ x)⁻¹ := fun h =>
      ⟨1, Subgroup.one_mem _, one_pow _, fun y _ => by
        simp only [map_one, one_mul, inv_one, mul_one]
        show Lemma52Proof.oddQuotSelf s * y * (Lemma52Proof.oddQuotSelf s)⁻¹ = y
        rw [← Lemma52Proof.oddQuotSelf_central s y]
        group⟩
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      intro hxC
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact gen₁ hxC
      · exact gen₂ hxC
      · exact gen₃ hxC
    | one =>
      intro h1
      refine ⟨1, Subgroup.one_mem _, one_pow _, fun y _ => ?_⟩
      have e : (⟨1, h1⟩ : Cs) = 1 := rfl
      simp only [e, map_one, one_mul, inv_one, mul_one]
    | mul a b ha hb iha ihb =>
      intro habC
      obtain ⟨x, hxP, hx2, hxa⟩ := iha (hBC ha)
      obtain ⟨x', hx'P, hx'2, hxb⟩ := ihb (hBC hb)
      have hc : Commute x x' := hPc x hxP x' hx'P
      refine ⟨x * x', P.mul_mem hxP hx'P, by rw [hc.mul_pow, hx2, hx'2, one_mul], fun y hy => ?_⟩
      have e : (⟨a * b, habC⟩ : Cs) = ⟨a, hBC ha⟩ * ⟨b, hBC hb⟩ := rfl
      rw [e, map_mul]
      have hψx' : ψ x' ∈ ψ.range := ⟨x', rfl⟩
      have hy' : ψ x' * y * (ψ x')⁻¹ ∈ ψ.range :=
        ψ.range.mul_mem (ψ.range.mul_mem hψx' hy) (ψ.range.inv_mem hψx')
      calc oddQuotMk s ⟨a, hBC ha⟩ * oddQuotMk s ⟨b, hBC hb⟩ * y *
            (oddQuotMk s ⟨a, hBC ha⟩ * oddQuotMk s ⟨b, hBC hb⟩)⁻¹
          = oddQuotMk s ⟨a, hBC ha⟩ * (oddQuotMk s ⟨b, hBC hb⟩ * y *
            (oddQuotMk s ⟨b, hBC hb⟩)⁻¹) * (oddQuotMk s ⟨a, hBC ha⟩)⁻¹ := by group
        _ = oddQuotMk s ⟨a, hBC ha⟩ * (ψ x' * y * (ψ x')⁻¹) * (oddQuotMk s ⟨a, hBC ha⟩)⁻¹ := by
            rw [hxb y hy]
        _ = ψ x * (ψ x' * y * (ψ x')⁻¹) * (ψ x)⁻¹ := hxa _ hy'
        _ = ψ (x * x') * y * (ψ (x * x'))⁻¹ := by rw [map_mul]; group
    | inv a ha iha =>
      intro haC
      have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (Lemma52Proof.mul_self_eq_one_of_mem hA ha)
      have e : (⟨a⁻¹, haC⟩ : Cs) = ⟨a, hBC ha⟩ := Subtype.ext hai
      rw [e]
      exact iha (hBC ha)
  have htoral : ∀ b ∈ modOdd s B, ∃ x ∈ P, x ^ 2 = 1 ∧
      ∀ y ∈ ψ.range, b * y * b⁻¹ = ψ x * y * (ψ x)⁻¹ := by
    rintro _ ⟨⟨a, haC⟩, haB, rfl⟩
    exact key a haB haC
  have hBN : modOdd s B ≤ Subgroup.normalizer (ψ.range : Set (OddQuot s)) := by
    intro b hb
    obtain ⟨x, -, -, hxb⟩ := htoral b hb
    have hb2 : b * b = 1 := Lemma52Proof.modOdd_sq hA b hb
    have hψx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hxb y hy]
      exact ψ.range.mul_mem (ψ.range.mul_mem hψx hy) (ψ.range.inv_mem hψx)
    · intro hy
      have e : b * (b * y * b⁻¹) * b⁻¹ = y := by
        rw [show b * (b * y * b⁻¹) * b⁻¹ = (b * b) * y * (b * b)⁻¹ by group, hb2]
        group
      rw [← e, hxb _ hy]
      exact ψ.range.mul_mem (ψ.range.mul_mem hψx hy) (ψ.range.inv_mem hψx)
  have hmemZ := fun x => Lemma52Proof.mem_modOdd_zpowers_iff hA hsB hs1 x
  have hself : Lemma52Proof.oddQuotSelf s ∈ modOdd s (Subgroup.zpowers s) :=
    (hmemZ _).mpr (Or.inr rfl)
  have hZcard : Nat.card (modOdd s (Subgroup.zpowers s)) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨Lemma52Proof.oddQuotSelf s, hself⟩, fun h =>
      Lemma52Proof.oddQuotSelf_ne_one hA hsB hs1 (congrArg Subtype.val h).symm, ?_⟩
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (hmemZ w).mp w.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hZB : modOdd s (Subgroup.zpowers s) ≤ modOdd s B := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
    exact ⟨k, Subgroup.zpowers_le.mpr hsB hk, rfl⟩
  have hZ : ∀ w ∈ modOdd s (Subgroup.zpowers s), ∀ y ∈ ψ.range, w * y = y * w := by
    intro w hw y _
    rcases (hmemZ w).mp hw with rfl | rfl
    · simp
    · exact (Lemma52Proof.oddQuotSelf_central s y).symm
  have hZ' : ∀ b' ∈ modOdd s B, (∀ y ∈ ψ.range, b' * y = y * b') →
      b' ∈ modOdd s (Subgroup.zpowers s) := by
    intro b' hb' hcomm
    by_contra hnot
    obtain ⟨y, hy, hne'⟩ := hmov b' hb' hnot
    exact hne' (hcomm y hy)
  have : Group.IsPerfect (compModel D j₀).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero _ _ _ _ _ (D.isFundTag j₀)
      (D.admissible j₀)).1.1
  have hSB : Balance.StrongBalance.StrongLocalTwoBalanceToralPowOn 2 (D.tag j₀)
      (fun _ _ _ => True) := by
    rcases ht with h | h
    · rw [h]
      exact Balance.StrongBalance.Linear.strongLocalTwoBalanceToralPowOn_PSL_two
    · rw [h]
      exact Balance.StrongBalance.Unitary.strongLocalTwoBalanceToralPowOn_PSU_two
  exact Vertex.alphaOf_inducedImage_eq_bot_of_toralPow Fact.out (D.isFundTag j₀) (D.admissible j₀)
    hp2 h5 (Qn := fun _ _ _ => True) trivial hSB ψ hker (Lemma52Proof.modOdd_sq hA)
    (Lemma52Proof.card_modOdd_eq_eight hA hA8 hsB) hBN hZcard hZB hZ hZ' ⟨P, hPc, htoral⟩

end CFSG.ClassicalInvolution.NDB.Alpha
