module

import CFSG.Holt.H78.Sec4KnownKV
import CFSG.Holt.H78.SEModelFive
public import CFSG.Holt.H78.Sec4Prop49S4

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open Equiv
open scoped Pointwise

section Chain


theorem IsNaturalSE.holtDelta_eq_holtDelta' (hSEc : SEChainUnitary) {Ψ : Type} [Fintype Ψ]
    [DecidableEq Ψ] {M : Subgroup (Perm Ψ)} (hM : IsNaturalSE M) {a b : Ψ} (hab : a ≠ b)
    (h3 : 3 ∣ (holtDelta M Ψ a b).ncard) : holtDelta M Ψ a b = holtDelta' M Ψ a b := by
  classical
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  have hcard := hA.ncard_holtDelta hab
  have hcard' := hA.ncard_holtDelta' hab
  suffices hsub : holtDelta M Ψ a b ⊆ holtDelta' M Ψ a b from
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hcard']) (Set.toFinite _)
  rcases hA.benderType.cases' with ⟨rfl, -, hn⟩ | ⟨rfl, -, a', -, rfl⟩ | ⟨rfl, -, -⟩
  ·
    have hq := hA.card_eq
    have hcompl : ({a, b}ᶜ : Set Ψ).ncard = 2 ^ n - 1 := by
      rw [Set.ncard_compl, Set.ncard_pair hab, hq, pow_one]
      omega
    have hΔ : holtDelta M Ψ a b ⊆ {a, b}ᶜ := fun x hx hx' => by
      rcases hx' with rfl | rfl
      exacts [left_notMem_holtDelta hab hx, right_notMem_holtDelta hab hx]
    have hΔ' : holtDelta' M Ψ a b ⊆ {a, b}ᶜ := fun x hx hx' => by
      obtain ⟨s, hs, rfl⟩ := hx
      rcases hx' with h | h
      · exact hab (by rw [← hs.2, ← h, smul_smul, mul_self_eq_one_of_mem_longInv hs.1, one_smul])
      · exact hab (hs.1.2.unique hs.2 h)
    rw [Set.eq_of_subset_of_ncard_le hΔ (by rw [hcard, hcompl]) (Set.toFinite _),
      Set.eq_of_subset_of_ncard_le hΔ' (by rw [hcard', hcompl]) (Set.toFinite _)]
  ·
    exfalso
    have h2 : 2 ^ (2 * a' + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hpos : 1 ≤ 2 ^ (2 * a' + 1) := Nat.one_le_two_pow
    rw [hcard] at h3
    omega
  · exact hSEc Ψ M n e hA hab

end Chain

section Along

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G}

theorem P49Config.exists_mem_longInvAt_smul_eq (C : P49Config G Ω α v) (hS : Sec4Setting G Ω)
    (hSEc : SEChainUnitary)
    (h3 : 3 ∣ (holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i)
      (C.D.coord C.b C.i)).ncard)
    {γ γ' : Ω} (hγ : γ ∈ holtDelta G Ω α C.β ∩ fixSet Ω (Subgroup.zpowers v))
    (hγ' : γ' ∈ holtDelta G Ω α C.β ∩ fixSet Ω (Subgroup.zpowers v)) (hne : γ ≠ γ') :
    ∃ y ∈ longInvAt G Ω α, y ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ∧
      y • C.β = γ ∧ y • γ' ∈ holtDelta G Ω α C.β ∩ fixSet Ω (Subgroup.zpowers v) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := C.isNaturalSE C.i
  have hab := C.coord_ne
  have hΔΔ' := hM.holtDelta_eq_holtDelta' hSEc hab h3
  set g : fixSet Ω (Subgroup.zpowers v) := ⟨γ, hγ.2⟩ with hg
  set g' : fixSet Ω (Subgroup.zpowers v) := ⟨γ', hγ'.2⟩ with hg'
  obtain ⟨hgl, hgi⟩ := (C.mem_holtDelta_iff hS g).mp hγ.1
  obtain ⟨hg'l, hg'i⟩ := (C.mem_holtDelta_iff hS g').mp hγ'.1
  rw [hΔΔ'] at hgi hg'i
  obtain ⟨s, hs, hsb⟩ := hgi
  obtain ⟨s', hs', hs'b⟩ := hg'i
  have hxx' : C.D.coord g C.i ≠ C.D.coord g' C.i := fun h => hne (by
    have hgg : g = g' := C.coord_injective (funext fun j => by
      rcases eq_or_ne j C.i with rfl | hj
      · exact h
      · rw [hgl j hj, hg'l j hj])
    exact congrArg (fun y : fixSet Ω (Subgroup.zpowers v) => (y : Ω)) hgg)
  have hss' : s ≠ s' := fun h => hxx' (by rw [← hsb, ← hs'b, h])
  have hsInv : (s : Perm (C.D.Ψc C.i)) * s = 1 := by
    rw [← Subgroup.coe_mul, mul_self_eq_one_of_mem_longInv hs.1, Subgroup.coe_one]
  have hs'Inv : (s' : Perm (C.D.Ψc C.i)) * s' = 1 := by
    rw [← Subgroup.coe_mul, mul_self_eq_one_of_mem_longInv hs'.1, Subgroup.coe_one]
  have hcl := hM.mem_mulLongInvClosure_of_mul_self s.2 hs.2 hsInv
  have hcl' := hM.mem_mulLongInvClosure_of_mul_self s'.2 hs'.2 hs'Inv
  have hprod := mul_mem hcl hcl'
  have hprodM := mulLongInvClosure_le _ _ hprod
  have hprod1 : (s : Perm (C.D.Ψc C.i)) * s' ≠ 1 := fun h => hss' (Subtype.ext (by
    rw [← mul_left_cancel_iff (a := (s : Perm (C.D.Ψc C.i))), hsInv, h]))
  have hprodJ : (⟨(s : Perm (C.D.Ψc C.i)) * s', hprodM.1⟩ : C.D.M C.i) ∈
      longInvAt (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) := by
    have h2 : orderOf ((s : Perm (C.D.Ψc C.i)) * s') = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hM.mul_self_of_mem_mulLongInvClosure hprod) hprod1
    have hJ := hM.mem_longInv_perm hprodM.1 h2
    refine ⟨⟨by rwa [← Subgroup.orderOf_coe], ?_⟩, hprodM.2⟩
    obtain ⟨z, hz, hzu⟩ := hJ.2
    exact ⟨z, hz, fun z' hz' => hzu z' hz'⟩
  have hsx' : (s : Perm (C.D.Ψc C.i)) (C.D.coord g' C.i) ∈
      holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i) := by
    rw [hΔΔ']
    refine ⟨_, hprodJ, ?_⟩
    rw [← hs'b]
    rfl
  obtain ⟨t, ht, u, -, -, htu, htuv, -⟩ := C.isTypeL
  have htv : t ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    mem_centralizer_zpowers_iff.mpr (by rw [← htuv, mul_assoc t u t, ← htu.eq])
  have hV := C.isPGroup_zpowers
  have h3F := three_le_card_fixSet_of_isTypeL hS.star C.isTypeL
  set t₀ := centralizerImageElt (Ω := Ω) htv with ht₀def
  have ht₀ : t₀ ∈ longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) C.a :=
    (hS.mem_longInvAt_centralizerImage_iff hV h3F t₀).mpr
      ⟨t, by rw [C.coe_a]; exact ht, htv, fun ω => rfl⟩
  set t₀H : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩ with ht₀H
  have hfixa : ∀ j, C.D.ρ j t₀H (C.D.coord C.a j) = C.D.coord C.a j := fun j =>
    (C.D.rho_mem_longInvAt ht₀ j).2
  obtain ⟨w, hw, hρw⟩ := C.D.exists_mem_longInvAt_rho_eq C.a
    (Function.update (fun j => C.D.ρ j t₀H) C.i (s : Perm (C.D.Ψc C.i))) (fun j => by
      rcases eq_or_ne j C.i with rfl | hj
      · rw [Function.update_self]
        exact Subgroup.map_le_range _ _ s.2
      · rw [Function.update_of_ne hj]
        exact ⟨t₀H, rfl⟩) (fun j => by
      rcases eq_or_ne j C.i with rfl | hj
      · rw [Function.update_self]
        refine ⟨⟨by rw [Subgroup.orderOf_coe]; exact hs.1.1, ?_⟩, hs.2⟩
        obtain ⟨z, hz, hzu⟩ := hs.1.2
        exact ⟨z, hz, fun z' hz' => hzu z' hz'⟩
      · rw [Function.update_of_ne hj]
        exact C.D.rho_mem_longInvAt ht₀ j)
  obtain ⟨y, hyJ, hyC, hyw⟩ :=
    (hS.mem_longInv_centralizerImage_iff hV h3F (w : typeLSection G Ω v)).mp hw.1
  refine ⟨y, ⟨hyJ, ?_⟩, hyC, ?_, ?_⟩
  · rw [← C.coe_a, ← hyw C.a]
    exact congrArg Subtype.val hw.2
  · have hwb : (w : typeLSection G Ω v) • C.b = g := C.coord_injective (funext fun j => by
      rw [C.D.coord_smul w C.b j, hρw j]
      rcases eq_or_ne j C.i with rfl | hj
      · rw [Function.update_self]
        exact hsb
      · rw [Function.update_of_ne hj, ← C.coord_eq j hj, hfixa j, hgl j hj])
    rw [show C.β = (C.b : Ω) from rfl, ← hyw C.b]
    exact congrArg Subtype.val hwb
  · have hwg' : (((w : typeLSection G Ω v) • g' : fixSet Ω (Subgroup.zpowers v)) : Ω) ∈
        holtDelta G Ω α C.β := (C.mem_holtDelta_iff hS ((w : typeLSection G Ω v) • g')).mpr
      ⟨fun j hj => by
        rw [C.D.coord_smul, hρw j, Function.update_of_ne hj, hg'l j hj, hfixa j],
       by rw [C.D.coord_smul, hρw C.i, Function.update_self]; exact hsx'⟩
    rw [← hyw g']
    exact ⟨hwg', ((w : typeLSection G Ω v) • g').2⟩

end Along

end CFSG.Holt.H78
