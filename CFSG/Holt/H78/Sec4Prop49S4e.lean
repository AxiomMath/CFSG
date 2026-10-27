module

public import CFSG.Holt.H78.Sec4Prop49S4d
import CFSG.Holt.H78.Sec4Prop49S4f
import CFSG.Holt.H78.Sec4LineDiag2
import CFSG.Holt.H78.Sec4Prop49S6
import CFSG.Holt.H78.Sec4Lemma48
public import CFSG.Holt.H78.Sec4Prop49S4b
public import CFSG.Holt.H78.Sec4Prop49S4c

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open Equiv
open scoped Pointwise

section Step76

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {hS : Sec4Setting G Ω} {C : P49Config G Ω α v}

theorem P49K3.false_of_ncard_coord_le_one (K : P49K3 hS C) (hι : ∀ j, j = K.j₀)
    (hSEc : SEChainUnitary)
    (h1 : ∀ p : K.D'.Ψc K.j₀, {δ : holtDelta G Ω α C.β | K.D'.coord δ K.j₀ = p}.ncard ≤ 1) :
    False := by
  classical
  have hαβ := C.ne
  set e : holtDelta G Ω α C.β → K.D'.Ψc K.j₀ := fun δ => K.D'.coord δ K.j₀ with he
  have he_inj : Function.Injective e := fun δ δ' h =>
    (Set.ncard_le_one (Set.toFinite _)).mp (h1 (e δ)) δ rfl δ' h.symm
  have he_bij : Function.Bijective e := ⟨he_inj, fun p => K.D'.exists_coord_apply_eq K.j₀ p⟩
  let E := Equiv.ofBijective e he_bij
  have h7Δ : (holtDelta G Ω α C.β).ncard = 7 := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr E, Nat.card_eq_fintype_card, K.card_eq]
  have hAltG : alternatingGroup (holtDelta G Ω α C.β) ≤ twoPointSection G Ω α C.β := by
    intro σ hσ
    have hσ' : E.permCongr σ ∈ alternatingGroup (K.D'.Ψc K.j₀) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_permCongr]
      exact hσ
    rw [← K.alt] at hσ'
    obtain ⟨h, -, hhσ⟩ := (mem_factorImage).mp hσ'
    have hσh : ((h : twoPointSection G Ω α C.β) : Perm (holtDelta G Ω α C.β)) = σ := by
      ext δ
      apply congrArg Subtype.val
      apply he_inj
      show K.D'.coord ((h : twoPointSection G Ω α C.β) • δ) K.j₀ = K.D'.coord (σ δ) K.j₀
      rw [K.D'.coord_smul h δ K.j₀, hhσ, Equiv.permCongr_apply]
      show E (σ (E.symm (E δ))) = E (σ δ)
      rw [E.symm_apply_apply]
    rw [← hσh]
    exact (h : twoPointSection G Ω α C.β).2
  have hAlt := alternatingGroup_le_inducedPerm_inf hαβ hAltG
  obtain ⟨p, -⟩ : ∃ p : K.D'.Ψc K.j₀, True := ⟨K.D'.coord ⟨_, (C.exists_mem_holtDelta_ne
    hS).choose_spec.choose_spec.1⟩ K.j₀, trivial⟩
  have hB3 : 3 ∣ (holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i)
      (C.D.coord C.b C.i)).ncard := by
    rw [← C.ncard_B_eq hS, K.ncard_B hι p]
    exact dvd_mul_right 3 _
  obtain ⟨δ, δ', hδ, hδ', hne⟩ := C.exists_mem_holtDelta_ne hS
  obtain ⟨y, hyα, -, hyβ, hyγ'⟩ := C.exists_mem_longInvAt_smul_eq hS hSEc hB3 ⟨hδ, δ.2⟩
    ⟨hδ', δ'.2⟩ fun h => hne (Subtype.ext h)
  have hδΔ' : (δ : Ω) ∈ holtDelta' G Ω α C.β := ⟨y, hyα, hyβ⟩
  have hΔ' : holtDelta' G Ω α C.β = holtDelta G Ω α C.β := by
    rw [hS.holtDelta'_eq_orbit hαβ hδΔ', holtDelta_eq_orbit hS.star hαβ hδ]
  have hs : ∃ s ∈ longInvAt G Ω α, ∃ δ ∈ holtDelta G Ω α C.β, s • δ ∈ holtDelta G Ω α C.β :=
    ⟨y, hyα, δ', hδ', hyγ'.1⟩
  have hαΔ : α ∉ holtDelta G Ω α C.β := left_notMem_holtDelta hαβ
  have hβΔ : C.β ∉ holtDelta G Ω α C.β := right_notMem_holtDelta hαβ
  have hαΛ : α ∈ ({α, C.β} ∪ holtDelta G Ω α C.β : Set Ω) := Or.inl (Or.inl rfl)
  have h2tr := two_transitive_of_alternatingGroup_le (by omega) _ hAlt
  have hJ := isJClosed_union_holtDelta hS.star hαβ h2tr hΔ' hs
  have hclique := exists_mem_longInvAt_smul_eq_of_two_transitive hαβ h2tr hs
  have hβδ : ∀ δ ∈ holtDelta G Ω α C.β, ∃ s ∈ longInvAt G Ω α, s • C.β = δ := fun δ hδ => by
    rw [← hΔ'] at hδ
    exact hδ
  obtain ⟨w, hw⟩ := longInvSwap_nonempty hS.star α C.β
  obtain ⟨δw, hδw, -⟩ := hw.1.2
  have hwΛ : w ∈ stabilizer G ({α, C.β} ∪ holtDelta G Ω α C.β) :=
    hJ δw (Or.inr ⟨w, hw, hδw⟩) w ⟨hw.1, hδw⟩
  have hA := alternatingGroup_le_inducedPerm_union hαβ hαΔ hβΔ (by omega) _ hAlt
    (fun s hs => hJ α hαΛ s hs) ⟨w, hwΛ, hw.2⟩ hβδ hclique
  have h7 : 7 ≤ ({α, C.β} ∪ holtDelta G Ω α C.β : Set Ω).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_left.mpr fun y hy hyΔ => by
      rcases hy with rfl | rfl
      exacts [hαΔ hyΔ, hβΔ hyΔ]), Set.ncard_pair hαβ]
    omega
  exact hS.not_conclusion (Or.inl (hS.alternatingGroup_le_of_jClosed hαΛ h7 hJ (by convert hA)))

end Step76

section Step94

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.p49Step94 (hS : Sec4Setting G Ω)
    (hL48 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      ∀ (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))) (i : D.ι),
        IsNaturalSE (factorImage _ _ (D.L i) (D.ρ i)))
    (hSEf : SEFieldFixBound) (hSEc : SEChainUnitary) : P49Step94 G Ω := by
  intro α v C h3
  obtain ⟨K⟩ := C.nonempty_p49K3 hS (hS.p49Step96 hL48) h3
  have hι : ∀ j, j = K.j₀ := K.eq_j₀ hL48
  refine K.false_of_ncard_coord_le_one hι hSEc fun p => ?_
  by_cases hT : Odd (Nat.card (twoPointKernel G Ω α C.β))
  · exact K.ncard_coord_le_one_of_odd hι hSEf hT p
  · exact K.ncard_coord_le_one_of_even hι hSEc hT p

theorem Sec4Setting.p49Step94_of (hS : Sec4Setting G Ω)
    (hP43 : ∀ {α β : Ω}, α ≠ β → IsEmpty (AltConfig G Ω α β))
    (hP46 : ∀ {α : Ω} {v : G}, IsTypeL G Ω α v →
      CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥)
    (hSEf : SEFieldFixBound) (hSEc : SEChainUnitary) : P49Step94 G Ω :=
  hS.p49Step94 (fun hv D i => hS.isNaturalSE_factor_typeLSection_of hP43 hv (hP46 hv) D i)
    hSEf hSEc

end Step94

end CFSG.Holt.H78
