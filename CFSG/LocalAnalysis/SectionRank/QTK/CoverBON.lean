module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import Certificates.Certificate7261
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native LocalWitness
open CFSG.RankThree.PartTwo.Census.FourGroup

namespace SignedData

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem exists_of_check [Inhabited M] (D : SignedData) (h : SignedData.check O D = true) :
    ∃ (R : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ)
      (a b d₁ d₂ : (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ),
      R ≠ ⊥ ∧ IsPGroup 2 R ∧ a ∈ normalizer (R : Set _) ∧ b ∈ normalizer (R : Set _) ∧
        a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
        (∀ i j : ℕ, i < 3 → j < 3 → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) ∧
        d₁ * a * d₁⁻¹ = a⁻¹ ∧ d₁ * b * d₁⁻¹ = b ∧ d₂ * b * d₂⁻¹ = b⁻¹ := by
  set S := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  unfold SignedData.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hprog, ht₁, ht₂, ha, hb, hd₁, hd₂⟩, hel⟩, hT₁⟩, hT₂⟩, hT₁₂⟩, hmov⟩,
    hcA₁⟩, hcA₂⟩, hcB₁⟩, hcB₂⟩, hD₁⟩, hD₂⟩, hDA⟩, hDB⟩, hDB'⟩ := h
  set R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs) with hR
  have hreg : ∀ r < D.base.nregs, Sp.WF R[r]! ∧ Sp.toMat R[r]! ∈ S := fun r hr =>
    Sp.regsOf_ok hprog hr
  obtain ⟨wT₁, mT₁⟩ := hreg _ ht₁
  obtain ⟨wT₂, mT₂⟩ := hreg _ ht₂
  obtain ⟨wA, mA⟩ := hreg _ ha
  obtain ⟨wB, mB⟩ := hreg _ hb
  obtain ⟨wD₁, mD₁⟩ := hreg _ hd₁
  obtain ⟨wD₂, mD₂⟩ := hreg _ hd₂
  have hsq : ∀ {X : M}, Sp.WF X → O.eq (O.mul X X) O.one = true → Sp.toMat X ^ 2 = 1 :=
    fun {X} hX h => by
      have := Sp.toMat_eq (Sp.mul_wf hX hX) Sp.one_wf h
      rwa [Sp.toMat_mul hX hX, Sp.toMat_one, ← sq] at this
  have hcm : ∀ {X Y : M}, Sp.WF X → Sp.WF Y → O.commOK X Y = true →
      Sp.toMat X * Sp.toMat Y = Sp.toMat Y * Sp.toMat X := fun {X Y} hX hY h => by
    have := Sp.toMat_eq (Sp.mul_wf hX hY) (Sp.mul_wf hY hX) h
    rwa [Sp.toMat_mul hX hY, Sp.toMat_mul hY hX] at this
  have hinv : ∀ {X Y : M}, Sp.WF X → Sp.WF Y →
      O.eq (O.mul X Y) (O.mul (O.mul Y Y) X) = true →
      Sp.toMat X * Sp.toMat Y = Sp.toMat Y * Sp.toMat Y * Sp.toMat X := fun {X Y} hX hY h => by
    have := Sp.toMat_eq (Sp.mul_wf hX hY) (Sp.mul_wf (Sp.mul_wf hY hY) hX) h
    rwa [Sp.toMat_mul hX hY, Sp.toMat_mul (Sp.mul_wf hY hY) hX, Sp.toMat_mul hY hY] at this
  have hw : ∀ X ∈ [R[D.a]!, R[D.b]!], Sp.WF X := by
    intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl
    · exact wA
    · exact wB
  unfold Ops.elemOK at hel
  simp only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] at hel
  obtain ⟨⟨⟨hcubeA, hcubeB⟩, hcomms⟩, hker⟩ := hel
  have hcube : ∀ {X : M}, Sp.WF X → O.cubeOK X = true → Sp.toMat X ^ 3 = 1 := fun {X} hX h => by
    have := Sp.toMat_eq (Sp.mul_wf (Sp.mul_wf hX hX) hX) Sp.one_wf h
    rwa [Sp.toMat_mul (Sp.mul_wf hX hX) hX, Sp.toMat_mul hX hX, Sp.toMat_one, ← pow_two,
      ← pow_succ] at this
  have hAB : Sp.toMat R[D.a]! * Sp.toMat R[D.b]! = Sp.toMat R[D.b]! * Sp.toMat R[D.a]! :=
    List.rel_of_pairwise_cons (Sp.pairwise_of_commsOK hw hcomms) (List.mem_singleton_self _)
  let τ₁ : Sˣ := unitOf S mT₁ two_ne_zero (hsq wT₁ hT₁)
  let τ₂ : Sˣ := unitOf S mT₂ two_ne_zero (hsq wT₂ hT₂)
  let α : Sˣ := unitOf S mA three_ne_zero (hcube wA hcubeA)
  let β : Sˣ := unitOf S mB three_ne_zero (hcube wB hcubeB)
  let δ₁ : Sˣ := unitOf S mD₁ two_ne_zero (hsq wD₁ hD₁)
  let δ₂ : Sˣ := unitOf S mD₂ two_ne_zero (hsq wD₂ hD₂)
  have fτ₁ : valHom S τ₁ = Sp.toMat R[D.t₁]! := valHom_unitOf S _ _ _
  have fτ₂ : valHom S τ₂ = Sp.toMat R[D.t₂]! := valHom_unitOf S _ _ _
  have fα : valHom S α = Sp.toMat R[D.a]! := valHom_unitOf S _ _ _
  have fβ : valHom S β = Sp.toMat R[D.b]! := valHom_unitOf S _ _ _
  have fδ₁ : valHom S δ₁ = Sp.toMat R[D.d₁]! := valHom_unitOf S _ _ _
  have fδ₂ : valHom S δ₂ = Sp.toMat R[D.d₂]! := valHom_unitOf S _ _ _
  have hα3 : α ^ 3 = 1 := unitOf_pow S _ _ _
  have hβ3 : β ^ 3 = 1 := unitOf_pow S _ _ _
  set P := Subgroup.closure ({τ₁, τ₂} : Set Sˣ)
  have hτ₁P : τ₁ ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)
  have hτ₂P : τ₂ ∈ P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hP : P ≠ ⊥ := by
    intro hbot
    have h1 := hτ₁P
    rw [hbot, mem_bot] at h1
    obtain ⟨k, -, hk⟩ := List.any_eq_true.1 hmov
    apply Sp.toVec_ne hk
    rw [Sp.toVec_vmul (Sp.unit_wf k) wT₁, ← fτ₁, h1, map_one, Matrix.vecMul_one]
  have hP2 : IsPGroup 2 P :=
    isPGroup_closure_pair (unitOf_pow S _ _ _) (unitOf_pow S _ _ _)
      (valHom_injective S (by rw [map_mul, map_mul, fτ₁, fτ₂]; exact hcm wT₁ wT₂ hT₁₂))
  have key : ∀ (w τ : Sˣ) (W T : M), Sp.WF W → Sp.WF T → valHom S w = Sp.toMat W →
      valHom S τ = Sp.toMat T →
      CFSG.RankThree.PartTwo.Census.V4Data.conjOK O W T R[D.t₁]! R[D.t₂]! = true →
      w * τ * w⁻¹ ∈ P := by
    intro w τ W T hW hT fw fτ hc
    rcases CFSG.RankThree.PartTwo.Census.OpsSpec.toMat_of_conjOK Sp hW hT wT₁ wT₂ hc with
      he | he | he
    · have e1 : w * τ = τ₁ * w :=
        valHom_injective S (by rw [map_mul, map_mul, fw, fτ, fτ₁]; exact he)
      rw [e1, mul_inv_cancel_right]
      exact hτ₁P
    · have e1 : w * τ = τ₂ * w :=
        valHom_injective S (by rw [map_mul, map_mul, fw, fτ, fτ₂]; exact he)
      rw [e1, mul_inv_cancel_right]
      exact hτ₂P
    · have e1 : w * τ = τ₁ * τ₂ * w :=
        valHom_injective S (by rw [map_mul, map_mul, map_mul, fw, fτ, fτ₁, fτ₂]; exact he)
      rw [e1, mul_inv_cancel_right]
      exact P.mul_mem hτ₁P hτ₂P
  have hαN : α ∈ normalizer (P : Set Sˣ) := by
    refine mem_normalizer_closure_of_pow_three hα3 ?_
    rintro x (rfl | rfl)
    · exact key α τ₁ _ _ wA wT₁ fα fτ₁ hcA₁
    · exact key α τ₂ _ _ wA wT₂ fα fτ₂ hcA₂
  have hβN : β ∈ normalizer (P : Set Sˣ) := by
    refine mem_normalizer_closure_of_pow_three hβ3 ?_
    rintro x (rfl | rfl)
    · exact key β τ₁ _ _ wB wT₁ fβ fτ₁ hcB₁
    · exact key β τ₂ _ _ wB wT₂ fβ fτ₂ hcB₂
  have hinvU : ∀ {u : Sˣ}, u ^ 3 = 1 → u * u = u⁻¹ := fun {u} hu =>
    eq_inv_of_mul_eq_one_left (by rw [← pow_three', hu])
  have e₁ : δ₁ * α = α * α * δ₁ := valHom_injective S (by
    rw [map_mul, map_mul, map_mul, fδ₁, fα]
    exact hinv wD₁ wA hDA)
  have e₂ : δ₁ * β = β * δ₁ := valHom_injective S (by
    rw [map_mul, map_mul, fδ₁, fβ]
    exact hcm wD₁ wB hDB)
  have e₃ : δ₂ * β = β * β * δ₂ := valHom_injective S (by
    rw [map_mul, map_mul, map_mul, fδ₂, fβ]
    exact hinv wD₂ wB hDB')
  refine ⟨P, α, β, δ₁, δ₂, hP, hP2, hαN, hβN, hα3, hβ3,
    valHom_injective S (by rw [map_mul, map_mul, fα, fβ]; exact hAB), ?_, ?_, ?_, ?_⟩
  · intro i j hi hj h1
    by_contra hne
    refine Sp.ne_one_of_kerOK hw hker (![⟨i, hi⟩, ⟨j, hj⟩] : Fin 2 → Fin 3) (fun h0 => hne ?_) ?_
    · have h0' : (⟨i, hi⟩ : Fin 3) = 0 := congrFun h0 (0 : Fin 2)
      have h1' : (⟨j, hj⟩ : Fin 3) = 0 := congrFun h0 (1 : Fin 2)
      exact ⟨congrArg Fin.val h0', congrArg Fin.val h1'⟩
    · have h2 := congrArg (valHom S) h1
      rw [map_mul, map_pow, map_pow, fα, fβ, map_one] at h2
      calc _ = Sp.toMat R[D.a]! ^ i * (Sp.toMat R[D.b]! ^ j * 1) := rfl
        _ = 1 := by rw [mul_one, h2]
  · rw [e₁, mul_inv_cancel_right]
    exact hinvU hα3
  · rw [e₂, mul_inv_cancel_right]
  · rw [e₃, mul_inv_cancel_right]
    exact hinvU hβ3

end SignedData

variable {G : Type} [Group G] [Finite G]

theorem onSigned_check :
    SignedData.check (ops3 154) onSigned = true :=
  Certificates.certificate7261

theorem exists_signed_ON :
    ∃ (R : Subgroup NativeSporadic.ON) (a b d₁ d₂ : NativeSporadic.ON),
      R ≠ ⊥ ∧ IsPGroup 2 R ∧ a ∈ normalizer (R : Set _) ∧ b ∈ normalizer (R : Set _) ∧
        a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧
        (∀ i j : ℕ, i < 3 → j < 3 → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0) ∧
        d₁ * a * d₁⁻¹ = a⁻¹ ∧ d₁ * b * d₁⁻¹ = b ∧ d₂ * b * d₂⁻¹ = b⁻¹ :=
  SignedData.exists_of_check (spec3 154) onSigned onSigned_check

theorem not_three_dvd_card_center_of_ON
    (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G} (e : ↥Y ⧸ center ↥Y ≃* NativeSporadic.ON) :
    ¬ 3 ∣ Nat.card (center ↥Y) := by
  obtain ⟨R, a, b, d₁, d₂, hR, hR2, ha, hb, ha3, hb3, hab, hind, h1, h2, h3⟩ := exists_signed_ON
  exact @not_dvd_card_center_of_signed_equiv G _ _ he Y NativeSporadic.ON Units.instGroup e 3
    Nat.prime_three (by norm_num) R hR hR2 a b d₁ d₂ ha hb ha3 hb3 hab hind h1 h2 h3

end CFSG.SectionRank.QTK.CoverB
