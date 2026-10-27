module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotRoots
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcDefs

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.F4Sec8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.SeitzReduction
open CFSG.SeitzReduction.F4Pilot (C3Set C3Roots)
open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.RankTwoExceptional.Exc

variable {K : Type} [Field K]

variable (K) in
@[expose] def f4Rep (L : List ℕ) :
    adjointGroup .F4 K :=
  ⟨f4CollProd K L, f4CollProd_mem L⟩

theorem coe_f4Rep (L : List ℕ) :
    (f4Rep K L : ModGL .F4 K) = f4CollProd K L :=
  rfl

theorem coe_f4Rep_singleton (p : ℕ) :
    (f4Rep K [p] : ModGL .F4 K) = f4x K p 1 := by
  simp [coe_f4Rep]

theorem f4Rep_pair (a b : ℕ) :
    f4Rep K [a, b] = f4Rep K [a] * f4Rep K [b] :=
  Subtype.ext (by simp [coe_f4Rep])

theorem phi_f4Rep_pairShort
    [Finite K] [CharP K 2]
    (k : Fin 12) :
    f4DescPhi K (f4Rep K [f4PairShort k]) = f4Rep K [f4PairLong k] := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hs, -, hd⟩ := f4Pair_roots k
  have h := finiteExceptionalAut_pinnedX_short (K := K) hs 1
  rw [hd, one_pow] at h
  have e₁ : f4Rep K [f4PairShort k] =
      ⟨pinnedX .F4 K (orbitCertRoot .F4 (f4PairShort k)) 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (by rw [coe_f4Rep_singleton]; rfl)
  have e₂ : f4Rep K [f4PairLong k] =
      ⟨pinnedX .F4 K (orbitCertRoot .F4 (f4PairLong k)) 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (by rw [coe_f4Rep_singleton]; rfl)
  rw [e₁, e₂]
  exact h

theorem phi_f4Rep_pairLong
    [Finite K] [CharP K 2]
    (k : Fin 12) :
    f4DescPhi K (f4Rep K [f4PairLong k]) = f4Rep K [f4PairShort k] := by
  have h := f4Desc_phi_f4x_pairLong (K := K) k
  have e₁ : f4Rep K [f4PairLong k] = ⟨f4x K (f4PairLong k) 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (coe_f4Rep_singleton _)
  have e₂ : f4Rep K [f4PairShort k] = ⟨f4x K (f4PairShort k) 1, pinnedX_mem_adjointGroup _ _⟩ :=
    Subtype.ext (coe_f4Rep_singleton _)
  rw [e₁, e₂]
  exact h

theorem phi_f4Rep_classes
    [Finite K] [CharP K 2] :
    f4DescPhi K (f4Rep K [47]) = f4Rep K [44] ∧ f4DescPhi K (f4Rep K [44]) = f4Rep K [47] ∧
      f4DescPhi K (f4Rep K [47, 44]) = f4Rep K [47, 44] ∧
      f4DescPhi K (f4Rep K [41, 45]) = f4Rep K [41, 45] := by
  have h47 := phi_f4Rep_pairLong (K := K) 11
  have h44 := phi_f4Rep_pairShort (K := K) 11
  have h45 := phi_f4Rep_pairLong (K := K) 9
  have h41 := phi_f4Rep_pairShort (K := K) 9
  rw [show f4PairLong 11 = 47 from rfl, show f4PairShort 11 = 44 from rfl] at h47 h44
  rw [show f4PairLong 9 = 45 from rfl, show f4PairShort 9 = 41 from rfl] at h45 h41
  have c1 : f4Rep K [44] * f4Rep K [47] = f4Rep K [47] * f4Rep K [44] := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, coe_f4Rep_singleton]
    exact (commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 44) (q := 47)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 1).eq
  have c2 : f4Rep K [45] * f4Rep K [41] = f4Rep K [41] * f4Rep K [45] := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, coe_f4Rep_singleton]
    exact (commute_f4x_of_f4CollComm_eq_nil (K := K) (p := 45) (q := 41)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (fun _ => by decide) 1 1).eq
  refine ⟨h47, h44, ?_, ?_⟩
  · rw [f4Rep_pair, map_mul, h47, h44, c1]
  · rw [f4Rep_pair, map_mul, h41, h45, c2]


theorem phi_pow_f4Rep_mem
    [Finite K] [CharP K 2] (k : ℕ) {x : adjointGroup .F4 K}
    (hx : x ∈ [f4Rep K [47], f4Rep K [44], f4Rep K [47, 44], f4Rep K [41, 45]]) :
    ((f4DescPhi K) ^ k) x ∈ [f4Rep K [47], f4Rep K [44], f4Rep K [47, 44], f4Rep K [41, 45]] := by
  obtain ⟨h47, h44, htu, hv⟩ := phi_f4Rep_classes (K := K)
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ih ⊢
    rcases ih with h | h | h | h <;> rw [h]
    · exact Or.inr (Or.inl h47)
    · exact Or.inl h44
    · exact Or.inr (Or.inr (Or.inl htu))
    · exact Or.inr (Or.inr (Or.inr hv))

theorem classesCover_AS
    [Finite K] [CharP K 2] :
    ClassesCover [f4Rep K [47], f4Rep K [44], f4Rep K [47, 44], f4Rep K [41, 45]] := by
  intro y hy2 hy1
  obtain ⟨ψ, L, hL, he⟩ := exists_mulAut_eq_f4DescProd (pow_two y ▸ hy2) hy1
  obtain ⟨g, hg, hgL⟩ := exists_conj_of_mem_f4FrameCandidates (K := K) (f4DescCandidates_eq ▸ hL)
  set β := MulAut.conj (⟨g, hg⟩ : adjointGroup .F4 K) * ψ with hβdef
  have hβ : ((β y : adjointGroup .F4 K) : ModGL .F4 K) = g * f4CollProd K L * g⁻¹ := by
    rw [hβdef, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, he]
    rfl
  have hβy : β y ∈ [f4Rep K [47], f4Rep K [44], f4Rep K [47, 44], f4Rep K [41, 45]] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hgL with h | h | h
    · exact Or.inl (Subtype.ext (by rw [hβ, h, coe_f4Rep_singleton]))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by
        rw [hβ, h, coe_f4Rep, f4CollProd_pair]))))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by
        rw [hβ, h, coe_f4Rep, f4CollProd_pair]))))
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form n.pos K hK
  obtain ⟨⟨h₀, k⟩, hhk₀, -⟩ := hnf β⁻¹
  set h : adjointGroup .F4 K := h₀
  have hhk : β⁻¹ = MulAut.conj h * (f4DescPhi K) ^ (k : ℕ) := hhk₀
  clear_value h
  clear hhk₀
  have hy' : y = h * ((f4DescPhi K) ^ (k : ℕ)) (β y) * h⁻¹ := by
    have e : β⁻¹ (β y) = y := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [← MulAut.conj_apply, ← MulAut.mul_apply, ← hhk, e]
  exact ⟨_, phi_pow_f4Rep_mem k hβy, isConj_iff.2 ⟨h, hy'.symm⟩⟩

theorem isConj_f4Rep_levi
    [CharP K 2] :
    IsConj (f4Rep K [47]) (f4Rep K [32]) ∧ IsConj (f4Rep K [44]) (f4Rep K [31]) ∧
      IsConj (f4Rep K [47, 44]) (f4Rep K [32, 31]) ∧
      IsConj (f4Rep K [41, 45]) (f4Rep K [28, 32]) := by
  have key : ∀ (ω : List ℕ), (∀ j ∈ ω, j < 4) → ∀ (L : List ℕ), (∀ p ∈ L, p < 48) →
      IsConj (f4Rep K L) (f4Rep K (L.map (f4CollWeylPerm ω))) := fun ω hω L hL =>
    isConj_iff.2 ⟨⟨f4CollWeylElt K ω, f4CollWeylElt_mem ω⟩,
      Subtype.ext (f4CollWeylElt_conj_prod hω L hL)⟩
  have hω : ∀ j ∈ [0, 1, 2, 3, 1, 0], j < 4 := by decide
  have hω' : ∀ j ∈ [0, 1, 2, 3, 1, 2, 1], j < 4 := by decide
  have e₁ : [47].map (f4CollWeylPerm [0, 1, 2, 3, 1, 0]) = [32] := by decide
  have e₂ : [44].map (f4CollWeylPerm [0, 1, 2, 3, 1, 0]) = [31] := by decide
  have e₃ : [47, 44].map (f4CollWeylPerm [0, 1, 2, 3, 1, 0]) = [32, 31] := by decide
  have e₄ : [41, 45].map (f4CollWeylPerm [0, 1, 2, 3, 1, 2, 1]) = [28, 32] := by decide
  exact ⟨e₁ ▸ key _ hω [47] (by decide), e₂ ▸ key _ hω [44] (by decide),
    e₃ ▸ key _ hω [47, 44] (by decide), e₄ ▸ key _ hω' [41, 45] (by decide)⟩

theorem classesCover_levi
    [Finite K] [CharP K 2] :
    ClassesCover [f4Rep K [32], f4Rep K [31], f4Rep K [32, 31], f4Rep K [28, 32]] := by
  intro y hy2 hy1
  obtain ⟨x, hx, hxy⟩ := classesCover_AS (K := K) y hy2 hy1
  obtain ⟨c₁, c₂, c₃, c₄⟩ := isConj_f4Rep_levi (K := K)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨_, Or.inl rfl, c₁.symm.trans hxy⟩
  · exact ⟨_, Or.inr (Or.inl rfl), c₂.symm.trans hxy⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), c₃.symm.trans hxy⟩
  · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), c₄.symm.trans hxy⟩

theorem orbitCertRoot_mem_C3Roots :
    ∀ p ∈ [28, 31, 32], orbitCertRoot .F4 p ∈ C3Roots := by
  decide +kernel

theorem f4Rep_mem_C3 :
    ∀ L ∈ [[32], [31], [32, 31], [28, 32]], (f4Rep K L : ModGL .F4 K) ∈ rootSpan .F4 K C3Set := by
  have h : ∀ p ∈ [28, 31, 32], f4x K p 1 ∈ rootSpan .F4 K C3Set := fun p hp =>
    pinnedX_mem_rootSpan (orbitCertRoot_mem_C3Roots p hp) 1
  intro L hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl <;> simp only [coe_f4Rep, f4CollProd_cons, f4CollProd_nil,
    mul_one]
  · exact h 32 (by decide)
  · exact h 31 (by decide)
  · exact mul_mem (h 32 (by decide)) (h 31 (by decide))
  · exact mul_mem (h 28 (by decide)) (h 32 (by decide))

end CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
