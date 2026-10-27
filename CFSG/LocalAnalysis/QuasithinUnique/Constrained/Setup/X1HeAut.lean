module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeTrans
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Blueprint

section RLevel

theorem heA0P_fst : heA0P.1 = heGen 0 := by simp [heA0P]

theorem heA1P_fst : heA1P.1 = heGen 1 := by simp [heA1P]

theorem pRep_heA0P : PRep 8330 heA0P (heGenPerm 0) := by
  refine ⟨?_, ?_⟩
  · rw [heA0P_fst]
    exact rep_heGen (k := 0) (by norm_num)
  · exact rep_heGen_inv (k := 0) (by norm_num)

theorem pRep_heA1P : PRep 8330 heA1P (heGenPerm 1) := by
  refine ⟨?_, ?_⟩
  · rw [heA1P_fst]
    exact rep_heGen (k := 1) (by norm_num)
  · exact rep_heGen_inv (k := 1) (by norm_num)

theorem regIn_heP : RegIn 8330 heP [heA0P, heA1P] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨heGenPerm 0, heGenPerm_mem (by norm_num), pRep_heA0P⟩
  · exact ⟨heGenPerm 1, heGenPerm_mem (by norm_num), pRep_heA1P⟩

theorem regIn_heAutGroup
    : RegIn 8330 heAutGroup [heA0P, heA1P, heUP] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨heGenPerm 0, heP_le_heAutGroup (heGenPerm_mem (by norm_num)), pRep_heA0P⟩
  · exact ⟨heGenPerm 1, heP_le_heAutGroup (heGenPerm_mem (by norm_num)), pRep_heA1P⟩
  · exact ⟨heAutU, heAutU_mem_heAutGroup, PRep.of_sq rep_heU (by rw [← sq]; exact heAutU_sq)⟩

theorem regIn_heSylGens
    : RegIn 8330 heAutGroup heSylGens := by
  have h := RegIn.run heSylProg regIn_heAutGroup
  intro r hr
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hr
  exact h.getD k

theorem he_rank_R
    : ∀ B : Subgroup ↥heAutGroup, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 6 :=
  sylVerify_sound (N := 2048) (a := 11) (m := 3935925) (by norm_num)
    (by rw [card_heAutGroup]; norm_num) (by decide) regIn_heSylGens he_syl_check

theorem gen3_of_check
    {t : PArr} {τ : Equiv.Perm (Fin 8330)} (ht : PRep 8330 t τ)
    {ws : List (List ℤ)} {prog : List (ℤ × ℤ)} (hws : ws.length = 3)
    (hc : threeConjCheck 8330 [heA0P, heA1P] t ws prog [heGen 0, heGen 1] = true) :
    ∃ gs : List (Equiv.Perm (Fin 8330)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ heP) ∧
      heP ≤ Subgroup.closure (conjSet gs {τ}) := by
  obtain ⟨gs, hlen, hgs, hmem⟩ := threeConj_sound regIn_heP ht hc
  refine ⟨gs, hlen.trans hws, hgs, ?_⟩
  have h0 := hmem (heGen 0) (by simp) _ (rep_heGen (by norm_num))
  have h1 := hmem (heGen 1) (by simp) _ (rep_heGen (by norm_num))
  rw [heP]
  refine (Subgroup.closure_le _).2 ?_
  rintro y (rfl | rfl)
  · exact h0
  · exact h1

theorem gen3_transfer {t x c : Equiv.Perm (Fin 8330)} (hc : c ∈ heP) (hx : x = c * t * c⁻¹)
    (h : ∃ gs : List (Equiv.Perm (Fin 8330)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ heP) ∧
      heP ≤ Subgroup.closure (conjSet gs {t})) :
    ∃ gs : List (Equiv.Perm (Fin 8330)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ heP) ∧
      heP ≤ Subgroup.closure (conjSet gs {x}) := by
  obtain ⟨gs, hlen, hgs, hle⟩ := h
  refine ⟨gs.map (· * c⁻¹), by simp [hlen], ?_, fun a ha => ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact heP.mul_mem (hgs g' hg') (heP.inv_mem hc)
  · refine closure_conjSet_transfer (T := {x}) (T' := {t}) c⁻¹ (fun t' ht' => ⟨x, rfl, ?_⟩) gs
      (hle ha)
    have : t' = t := by simpa using ht'
    rw [this, hx]
    group

theorem he_gen_perm
    {x : Equiv.Perm (Fin 8330)} (hxR : x ∈ heAutGroup) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) :
    ∃ gs : List (Equiv.Perm (Fin 8330)), gs.length = 3 ∧ (∀ g ∈ gs, g ∈ heP) ∧
      heP ≤ Subgroup.closure (conjSet gs {x}) := by
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have c0 := gen3_of_check (PRep.of_sq (rep_heGen (k := 0) (by norm_num))
    (by rw [← sq]; exact heGen0_sq) : PRep 8330 heT0P (heGenPerm 0)) rfl he_conj0_check
  have c1 := gen3_of_check (PRep.of_sq rep_heT1 (by
    rw [← sq]
    have := pow_orderOf_eq_one heT1P
    rwa [orderOf_heT1P] at this) : PRep 8330 heT1ArrP heT1P) rfl he_conj1_check
  have cu := gen3_of_check (PRep.of_sq rep_heU (by rw [← sq]; exact heAutU_sq) :
    PRep 8330 heUP heAutU) rfl he_conjU_check
  by_cases hxP : x ∈ heP
  · rcases involution_conj_cases hxP hord with ⟨c, hc, hxc⟩ | ⟨c, hc, hxc⟩
    · exact gen3_transfer hc hxc c0
    · exact gen3_transfer hc hxc c1
  · obtain ⟨c, hc, hxc⟩ := exists_conj_heAutU hxR hxP hord
    exact gen3_transfer hc hxc cu

end RLevel

section SLevel

theorem he_model
    : ∃ Φ : ↥heAutGroup ≃* MulAut NativeSporadic.He,
    ∀ (x : ↥heAutGroup) (h : NativeSporadic.He), Φ x h = heEquivP.symm (heConjR x (heEquivP h)) :=
  ctbh_full_automorphism_permutation_model.2.2.2.2.2 heEquivP

theorem he_rank
    : ∀ B : Subgroup (MulAut (NativeSporadic.Carrier .He)),
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 6 := by
  obtain ⟨Φ0, -⟩ := he_model
  let Φ : ↥heAutGroup ≃* MulAut (NativeSporadic.Carrier .He) := Φ0
  exact rank_of_equiv Φ he_rank_R

theorem he_gen
    : ∀ ψ : MulAut (NativeSporadic.Carrier .He), ψ * ψ = 1 → ψ ≠ 1 →
    ∃ cs : List (MulAut (NativeSporadic.Carrier .He)), cs.length = 3 ∧
      (∀ c ∈ cs, c ∈ (MulAut.conj : NativeSporadic.Carrier .He →*
        MulAut (NativeSporadic.Carrier .He)).range) ∧
      ∀ s : NativeSporadic.Carrier .He, MulAut.conj s ∈ Subgroup.closure (conjSet cs {ψ}) := by
  obtain ⟨Φ0, hΦ0⟩ := he_model
  let Φ : ↥heAutGroup ≃* MulAut (NativeSporadic.Carrier .He) := Φ0
  let θ : NativeSporadic.Carrier .He ≃* heP := heEquivP
  have hΦ : ∀ (x : ↥heAutGroup) (s : NativeSporadic.Carrier .He),
      Φ x s = θ.symm (heConjR x (θ s)) := hΦ0
  refine gen_of_equiv heP_le_heAutGroup Φ θ (fun s => conj_compat heP_le_heAutGroup heConjR
    (fun x a => heConjR_apply x a) Φ θ hΦ s) ?_
  intro x hx hx2 hx1
  exact he_gen_perm hx (by rw [sq]; exact hx2) hx1

end SLevel

end CFSG.QuasithinUnique.Setup.X1
