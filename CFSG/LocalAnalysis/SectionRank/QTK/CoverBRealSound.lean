module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBA134Defs
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBRealCheck
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native LocalWitness
open CFSG.RankThree.PartTwo.Census.FourGroup

namespace RealData

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem realLocalElement_of_localOK {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod p))}
    (D : RealData) {T₁ T₂ X Dd : M} (hT₁ : Sp.WF T₁ ∧ Sp.toMat T₁ ∈ S)
    (hT₂ : Sp.WF T₂ ∧ Sp.toMat T₂ ∈ S) (hX : Sp.WF X ∧ Sp.toMat X ∈ S)
    (hD : Sp.WF Dd ∧ Sp.toMat Dd ∈ S) (h : localOK O D T₁ T₂ X Dd = true) :
    RealLocalElement Sˣ 3 := by
  unfold localOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hT₁1, hT₂1⟩, hT₁₂⟩, hmov⟩, hc₁⟩, hc₂⟩, hcube⟩, hmovX⟩, hk⟩, hDk⟩, hDX⟩ := h
  obtain ⟨wT₁, mT₁⟩ := hT₁
  obtain ⟨wT₂, mT₂⟩ := hT₂
  obtain ⟨wX, mX⟩ := hX
  obtain ⟨wD, mD⟩ := hD
  have hsq : ∀ {Y : M}, Sp.WF Y → O.eq (O.mul Y Y) O.one = true → Sp.toMat Y ^ 2 = 1 :=
    fun {Y} hY h => by
      have := Sp.toMat_eq (Sp.mul_wf hY hY) Sp.one_wf h
      rwa [Sp.toMat_mul hY hY, Sp.toMat_one, ← sq] at this
  have hX3 : Sp.toMat X ^ 3 = 1 := by
    have := Sp.toMat_eq (Sp.mul_wf (Sp.mul_wf wX wX) wX) Sp.one_wf hcube
    rwa [Sp.toMat_mul (Sp.mul_wf wX wX) wX, Sp.toMat_mul wX wX, Sp.toMat_one, ← pow_two,
      ← pow_succ] at this
  have hDXm : Sp.toMat Dd * Sp.toMat X = Sp.toMat X * Sp.toMat X * Sp.toMat Dd := by
    have := Sp.toMat_eq (Sp.mul_wf wD wX) (Sp.mul_wf (Sp.mul_wf wX wX) wD) hDX
    rwa [Sp.toMat_mul wD wX, Sp.toMat_mul (Sp.mul_wf wX wX) wD, Sp.toMat_mul wX wX] at this
  have hT₁₂m : Sp.toMat T₁ * Sp.toMat T₂ = Sp.toMat T₂ * Sp.toMat T₁ := by
    have := Sp.toMat_eq (Sp.mul_wf wT₁ wT₂) (Sp.mul_wf wT₂ wT₁) hT₁₂
    rwa [Sp.toMat_mul wT₁ wT₂, Sp.toMat_mul wT₂ wT₁] at this
  let τ₁ : Sˣ := unitOf S mT₁ two_ne_zero (hsq wT₁ hT₁1)
  let τ₂ : Sˣ := unitOf S mT₂ two_ne_zero (hsq wT₂ hT₂1)
  let ξ : Sˣ := unitOf S mX three_ne_zero hX3
  let δ : Sˣ := unitOf S mD hk.ne' (Sp.pow_eq_one_of_check wD hDk)
  have fτ₁ : valHom S τ₁ = Sp.toMat T₁ := valHom_unitOf S _ _ _
  have fτ₂ : valHom S τ₂ = Sp.toMat T₂ := valHom_unitOf S _ _ _
  have fξ : valHom S ξ = Sp.toMat X := valHom_unitOf S _ _ _
  have fδ : valHom S δ = Sp.toMat Dd := valHom_unitOf S _ _ _
  have hξ3 : ξ ^ 3 = 1 := unitOf_pow S _ _ _
  set P := Subgroup.closure ({τ₁, τ₂} : Set Sˣ)
  have hτ₁P : τ₁ ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)
  have hτ₂P : τ₂ ∈ P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmove : ∀ {Y : M} {u : Sˣ}, Sp.WF Y → valHom S u = Sp.toMat Y →
      D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) Y) (O.unit k)) = true → u ≠ 1 :=
    fun {Y} {u} hY fu hm h1 => by
      obtain ⟨k, -, hk⟩ := List.any_eq_true.1 hm
      apply Sp.toVec_ne hk
      rw [Sp.toVec_vmul (Sp.unit_wf k) hY, ← fu, h1, map_one, Matrix.vecMul_one]
  have hP : P ≠ ⊥ := by
    intro hbot
    have h1 := hτ₁P
    rw [hbot, mem_bot] at h1
    exact hmove wT₁ fτ₁ hmov h1
  have hP2 : IsPGroup 2 P :=
    isPGroup_closure_pair (unitOf_pow S _ _ _) (unitOf_pow S _ _ _)
      (valHom_injective S (by rw [map_mul, map_mul, fτ₁, fτ₂]; exact hT₁₂m))
  have key : ∀ (τ : Sˣ) (T : M), Sp.WF T → valHom S τ = Sp.toMat T →
      CFSG.RankThree.PartTwo.Census.V4Data.conjOK O X T T₁ T₂ = true → ξ * τ * ξ⁻¹ ∈ P := by
    intro τ T hT fτ hc
    rcases CFSG.RankThree.PartTwo.Census.OpsSpec.toMat_of_conjOK Sp wX hT wT₁ wT₂ hc with
      he | he | he
    · have e1 : ξ * τ = τ₁ * ξ :=
        valHom_injective S (by rw [map_mul, map_mul, fξ, fτ, fτ₁]; exact he)
      rw [e1, mul_inv_cancel_right]
      exact hτ₁P
    · have e1 : ξ * τ = τ₂ * ξ :=
        valHom_injective S (by rw [map_mul, map_mul, fξ, fτ, fτ₂]; exact he)
      rw [e1, mul_inv_cancel_right]
      exact hτ₂P
    · have e1 : ξ * τ = τ₁ * τ₂ * ξ :=
        valHom_injective S (by rw [map_mul, map_mul, map_mul, fξ, fτ, fτ₁, fτ₂]; exact he)
      rw [e1, mul_inv_cancel_right]
      exact P.mul_mem hτ₁P hτ₂P
  have hξN : ξ ∈ normalizer (P : Set Sˣ) := by
    refine mem_normalizer_closure_of_pow_three hξ3 ?_
    rintro y (rfl | rfl)
    · exact key τ₁ T₁ wT₁ fτ₁ hc₁
    · exact key τ₂ T₂ wT₂ fτ₂ hc₂
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hξo : orderOf ξ = 3 := orderOf_eq_prime hξ3 (hmove wX fξ hmovX)
  have e₁ : δ * ξ = ξ * ξ * δ := valHom_injective S (by
    rw [map_mul, map_mul, map_mul, fδ, fξ]
    exact hDXm)
  refine ⟨P, hP, hP2, ξ, hξN, hξo, δ, ?_⟩
  rw [e₁, mul_inv_cancel_right]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_three', hξ3])

theorem realLocalElement_of_checkElem [Inhabited M] (D : RealData)
    (h : checkElem O D = true) :
    RealLocalElement (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ 3 := by
  unfold checkElem at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at h
  obtain ⟨⟨hprog, ht₁, ht₂, hx, hd⟩, hloc⟩ := h
  exact realLocalElement_of_localOK Sp D (Sp.regsOf_ok hprog ht₁) (Sp.regsOf_ok hprog ht₂)
    (Sp.regsOf_ok hprog hx) (Sp.regsOf_ok hprog hd) hloc

end RealData

end CFSG.SectionRank.QTK.CoverB
