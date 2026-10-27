module

public import CFSG.Holt.H78.Sec4Prop46BRec3
public import CFSG.Holt.H78.Sec4LineDiag2

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open CFSG.GH74.Uniqueness.Bender Equiv
open scoped Pointwise

section StepC

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

theorem Sec4Setting.false_of_stepC_of_lineTheorem (hS : Sec4Setting G Ω) {α β : Ω}
    (hαβ : α ≠ β) [DecidablePred (· ∈ holtDelta G Ω α β)] (h5 : 5 ≤ (holtDelta G Ω α β).ncard)
    (hAlt : alternatingGroup (holtDelta G Ω α β) ≤
      inducedPerm (stabilizer G α ⊓ stabilizer G β) (holtDelta G Ω α β)
        ((stabilizer_inf_le_stabilizer_pair α β).trans (stabilizer_pair_le α β)))
    (hΔ' : holtDelta' G Ω α β = holtDelta G Ω α β)
    (hs : ∃ s ∈ longInvAt G Ω α, ∃ δ ∈ holtDelta G Ω α β, s • δ ∈ holtDelta G Ω α β) :
    False := by
  classical
  have hαΔ : α ∉ holtDelta G Ω α β := left_notMem_holtDelta hαβ
  have hβΔ : β ∉ holtDelta G Ω α β := right_notMem_holtDelta hαβ
  have hαΛ : α ∈ ({α, β} ∪ holtDelta G Ω α β : Set Ω) := Or.inl (Or.inl rfl)
  have h2tr := two_transitive_of_alternatingGroup_le (by omega) _ hAlt
  have hJ := isJClosed_union_holtDelta hS.star hαβ h2tr hΔ' hs
  have hclique := exists_mem_longInvAt_smul_eq_of_two_transitive hαβ h2tr hs
  have hβδ : ∀ δ ∈ holtDelta G Ω α β, ∃ s ∈ longInvAt G Ω α, s • β = δ := fun δ hδ => by
    rw [← hΔ'] at hδ
    exact hδ
  obtain ⟨w, hw⟩ := longInvSwap_nonempty hS.star α β
  obtain ⟨δw, hδw, -⟩ := hw.1.2
  have hwΛ : w ∈ stabilizer G ({α, β} ∪ holtDelta G Ω α β) :=
    hJ δw (Or.inr ⟨w, hw, hδw⟩) w ⟨hw.1, hδw⟩
  have hA := alternatingGroup_le_inducedPerm_union hαβ hαΔ hβΔ (by omega) _ hAlt
    (fun s hs => hJ α hαΛ s hs) ⟨w, hwΛ, hw.2⟩ hβδ hclique
  have h7 : 7 ≤ ({α, β} ∪ holtDelta G Ω α β : Set Ω).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_left.mpr fun y hy hyΔ => by
      rcases hy with rfl | rfl
      exacts [hαΔ hyΔ, hβΔ hyΔ]), Set.ncard_pair hαβ]
    omega
  have hAltΩ : alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range := by
    refine hS.alternatingGroup_le_of_jClosed (Λ := {α, β} ∪ holtDelta G Ω α β) hαΛ h7 ?_ ?_
    · exact hJ
    · convert hA
  exact hS.not_conclusion (Or.inl hAltΩ)

end StepC

section O3

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

namespace Prop46CaseB

variable (hC : Prop46CaseB G Ω α β γ v P)
include hC

theorem false_of_smul_eq_inv (hS : Sec4Setting G Ω) {s : G} (hs : IsConj v s)
    (hsv : Commute s v) (hsΦ : fixedBy Ω s ≠ fixedBy Ω v) (hsα : s • α = α)
    {p₀ : typeLSection G Ω v} (hp₀ : p₀ ∈ P)
    (hp₀β : ((p₀ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω) = β)
    (hH : s • β = ((p₀⁻¹ • (⟨α, hC.α_mem⟩ : fixSet Ω (Subgroup.zpowers v)) : _) : Ω)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ, hτ2, hτv, -, -, hτα, hτβ, hτγ, h5, hG, h3Δ, h5F, htop, -⟩ :=
    hC.rec_of_smul_eq_inv hS hs hsv hsΦ hsα hp₀ hp₀β hH
  have hV : IsPGroup 2 (Subgroup.zpowers τ) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by rw [pow_one, sq, hτ2])
  have hmemV : ∀ {ω : Ω}, ω ∈ fixSet Ω (Subgroup.zpowers τ) ↔ τ • ω = ω := fun {ω} => by
    rw [fixSet_zpowers]; exact Iff.rfl
  have h3 : 3 ≤ Nat.card (fixSet Ω (Subgroup.zpowers τ)) := by omega
  set Λ := holtDelta G Ω α β ∩ fixSet Ω (Subgroup.zpowers τ) with hΛ
  obtain ⟨δ₃, hδ₃, hδ₃γ⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < Λ.ncard) γ
  have hδ₄ : v • δ₃ ∈ Λ :=
    ⟨smul_mem_holtDelta_of_mem_pair hC.v_mem_pair hδ₃.1, hmemV.mpr (by
      rw [← mul_smul, hτv.eq, mul_smul, hmemV.mp hδ₃.2])⟩
  have hvv : ∀ ω : Ω, v • v • ω = ω := fun ω => by rw [smul_smul, hC.v_mul_v, one_smul]
  have h34 : δ₃ ≠ v • δ₃ := fun h => hδ₃γ ((hC.fixed_iff δ₃ hδ₃.1).mp h.symm)
  have h4γ : v • δ₃ ≠ γ := fun h => hδ₃γ (by rw [← hvv δ₃, h, hC.smul_γ])
  have hαΔ := left_notMem_holtDelta (G := G) hC.ne
  have hβΔ := right_notMem_holtDelta (G := G) hC.ne
  have hne : ∀ {ω ω' : Ω}, ω ∉ holtDelta G Ω α β → ω' ∈ holtDelta G Ω α β → ω ≠ ω' :=
    fun h h' e => h (e ▸ h')
  have hF : ∀ ω ∈ fixSet Ω (Subgroup.zpowers τ),
      ω = α ∨ ω = β ∨ ω = γ ∨ ω = δ₃ ∨ ω = v • δ₃ := by
    have hsub : ({α, β, γ, δ₃, v • δ₃} : Set Ω) ⊆ fixSet Ω (Subgroup.zpowers τ) := by
      intro ω hω
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
      rcases hω with rfl | rfl | rfl | rfl | rfl
      exacts [hmemV.mpr hτα, hmemV.mpr hτβ, hmemV.mpr hτγ, hδ₃.2, hδ₄.2]
    have hc : ({α, β, γ, δ₃, v • δ₃} : Set Ω).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem (by simp [hC.ne, hne hαΔ hC.mem_holtDelta, hne hαΔ hδ₃.1,
          hne hαΔ hδ₄.1]),
        Set.ncard_insert_of_notMem (by simp [hne hβΔ hC.mem_holtDelta, hne hβΔ hδ₃.1,
          hne hβΔ hδ₄.1]),
        Set.ncard_insert_of_notMem (by simp [Ne.symm hδ₃γ, Ne.symm h4γ]), Set.ncard_pair h34]
    have heq := Set.eq_of_subset_of_ncard_le hsub
      (by rw [hc, ← Nat.card_coe_set_eq, h5F]) (Set.toFinite _)
    intro ω hω
    rw [← heq] at hω
    simpa using hω
  set a : fixSet Ω (Subgroup.zpowers τ) := ⟨α, hmemV.mpr hτα⟩
  set b : fixSet Ω (Subgroup.zpowers τ) := ⟨β, hmemV.mpr hτβ⟩
  set g : fixSet Ω (Subgroup.zpowers τ) := ⟨γ, hmemV.mpr hτγ⟩
  set d₃ : fixSet Ω (Subgroup.zpowers τ) := ⟨δ₃, hδ₃.2⟩
  set d₄ : fixSet Ω (Subgroup.zpowers τ) := ⟨v • δ₃, hδ₄.2⟩
  have hn : ∀ {x y : fixSet Ω (Subgroup.zpowers τ)}, (x : Ω) ≠ y → x ≠ y :=
    fun h e => h (congrArg Subtype.val e)
  have hbg : b ≠ g := hn (hne hβΔ hC.mem_holtDelta)
  have hbd₃ : b ≠ d₃ := hn (hne hβΔ hδ₃.1)
  have hbd₄ : b ≠ d₄ := hn (hne hβΔ hδ₄.1)
  have hgd₃ : g ≠ d₃ := hn (Ne.symm hδ₃γ)
  have hgd₄ : g ≠ d₄ := hn (Ne.symm h4γ)
  have hd₃₄ : d₃ ≠ d₄ := hn h34
  have hab : a ≠ b := hn hC.ne
  have hag : a ≠ g := hn (hne hαΔ hC.mem_holtDelta)
  have had₃ : a ≠ d₃ := hn (hne hαΔ hδ₃.1)
  have had₄ : a ≠ d₄ := hn (hne hαΔ hδ₄.1)
  set π : Equiv.Perm (fixSet Ω (Subgroup.zpowers τ)) := swap b g * swap d₃ d₄ with hπ
  have hπa : π a = a := by
    rw [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne had₃ had₄, swap_apply_of_ne_of_ne hab hag]
  have hπb : π b = g := by
    rw [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne hbd₃ hbd₄, swap_apply_left]
  have hπd₃ : π d₃ = d₄ := by
    rw [hπ, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hbd₄) (Ne.symm hgd₄)]
  have hπJ : π ∈ longInv (Equiv.Perm (fixSet Ω (Subgroup.zpowers τ)))
      (fixSet Ω (Subgroup.zpowers τ)) := by
    have hπ2 : π ^ 2 = 1 := by
      rw [sq, hπ]
      exact swap_mul_swap_mul_self hbg hbd₃ hbd₄ hgd₃ hgd₄ hd₃₄
    have hπ1 : π ≠ 1 := fun h => hbg (by rw [← hπb, h, Perm.one_apply])
    refine ⟨orderOf_eq_prime hπ2 hπ1, a, hπa, fun x hx => ?_⟩
    change π x = x at hx
    have hπg : π g = b := by
      rw [hπ, Perm.mul_apply, swap_apply_of_ne_of_ne hgd₃ hgd₄, swap_apply_right]
    have hπd₄ : π d₄ = d₃ := by
      rw [hπ, Perm.mul_apply, swap_apply_right,
        swap_apply_of_ne_of_ne (Ne.symm hbd₃) (Ne.symm hgd₃)]
    rcases hF x x.2 with h | h | h | h | h
    · exact Subtype.ext h
    · exact absurd (hx.symm.trans (show π x = g by rw [show x = b from Subtype.ext h, hπb]))
        (hn (by rw [h]; exact hne hβΔ hC.mem_holtDelta))
    · exact absurd (hx.symm.trans (show π x = b by rw [show x = g from Subtype.ext h, hπg]))
        (hn (by rw [h]; exact Ne.symm (hne hβΔ hC.mem_holtDelta)))
    · exact absurd (hx.symm.trans (show π x = d₄ by rw [show x = d₃ from Subtype.ext h, hπd₃]))
        (hn (by rw [h]; exact h34))
    · exact absurd (hx.symm.trans (show π x = d₃ by rw [show x = d₄ from Subtype.ext h, hπd₄]))
        (hn (by rw [h]; exact Ne.symm h34))
  have hπmem : π ∈ centralizerImage Ω (Subgroup.zpowers τ) := htop ▸ Subgroup.mem_top π
  obtain ⟨c, hcJ, -, hcπ⟩ := (hS.mem_longInv_centralizerImage_iff hV h3 ⟨π, hπmem⟩).mp
    (mem_longInv_subgroup_perm_iff.mpr hπJ)
  have hcα : c • α = α := (hcπ a).symm.trans (congrArg Subtype.val hπa)
  have hcβ : c • β = γ := (hcπ b).symm.trans (congrArg Subtype.val hπb)
  have hcδ : c • δ₃ = v • δ₃ := (hcπ d₃).symm.trans (congrArg Subtype.val hπd₃)
  have hcJα : c ∈ longInvAt G Ω α := ⟨hcJ, hcα⟩
  have hΔ' : holtDelta' G Ω α β = holtDelta G Ω α β :=
    (hS.holtDelta'_eq_orbit hC.ne ⟨c, hcJα, hcβ⟩).trans
      (holtDelta_eq_orbit_of_mem hC.mem_holtDelta).symm
  have hAlt := alternatingGroup_le_inducedPerm_inf (G := G) hC.ne
    (show alternatingGroup (holtDelta G Ω α β) ≤ twoPointSection G Ω α β by rw [hG]; exact le_top)
  exact hS.false_of_stepC_of_lineTheorem hC.ne (by rw [← Nat.card_coe_set_eq, h5]) hAlt hΔ'
    ⟨c, hcJα, δ₃, hδ₃.1, hcδ ▸ hδ₄.1⟩

end Prop46CaseB

end O3

end CFSG.Holt.H78
