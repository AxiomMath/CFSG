module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HSAux.PlaneDelta
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HeAux.Kit
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HSAux.ThreeCent
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.Blueprint CFSG.Open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.HSAux

private theorem hs_hidx :
    ∀ a ∈ hsR, ∀ b ∈ hsR, a ∉ hsP → b ∉ hsP → a * b ∈ hsP := by
  obtain ⟨hU2, -, -, hmap, -, hRmem, -⟩ := hs_normalizing_model
  have hUn : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have huu : hsU * hsU = 1 := by rw [← sq]; exact hU2
  intro a ha b hb haP hbP
  have haU : a * hsU ∈ hsP := ((hRmem a).1 ha).resolve_left haP
  have hbU : b * hsU ∈ hsP := ((hRmem b).1 hb).resolve_left hbP
  have h1 : hsU * (b * hsU) * hsU⁻¹ ∈ hsP := hUn _ hbU
  have e : a * b = (a * hsU) * (hsU * (b * hsU) * hsU⁻¹) := by
    calc a * b = a * (hsU * hsU) * b := by rw [huu, mul_one]
      _ = (a * hsU) * (hsU * (b * hsU) * hsU⁻¹) := by group
  rw [e]
  exact hsP.mul_mem haU h1

private theorem hs_hinv :
    ∀ t ∈ hsR, t ∉ hsP → t * t = 1 →
      9 ∣ Nat.card ↥(hsP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) →
        Nat.card ↥(hsP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) = 40320 := by
  intro t htR htP htt hdvd
  obtain ⟨-, -, -, hrows, hcover, -, hlist, -⟩ := hs_involution_centralizers
  have ho2 : orderOf t = 2 :=
    orderOf_eq_prime (by rw [sq]; exact htt) (fun h => htP (h ▸ hsP.one_mem))
  obtain ⟨r, hr, g, hg, htg⟩ := hcover t htR ho2
  obtain ⟨-, -, hrout, -, hrcard, -⟩ := hrows r hr
  have hout : r.outer = true := by
    apply hrout.2
    intro hmem
    apply htP
    rw [htg]
    exact hsP.mul_mem (hsP.mul_mem hg hmem) (hsP.inv_mem hg)
  have hcard : Nat.card ↥(hsP ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 3850)))) =
      r.centOrder := by
    rw [htg, inf_centralizer_conj hsP hg, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hrcard]
  have hmem : (r.outer, r.classSize, r.centOrder) ∈
      hsRows.map (fun r => (r.outer, r.classSize, r.centOrder)) := List.mem_map.2 ⟨r, hr, rfl⟩
  rw [hlist, hout] at hmem
  rw [hcard] at hdvd ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact h
  · rw [h] at hdvd
    exact absurd hdvd (by norm_num)

theorem sporadicTwoBalanceThree_HS :
    SporadicTwoBalanceThree .HS := by
  intro S _ _ hS hnab he
  obtain ⟨e0⟩ := he
  obtain ⟨eN⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  let θ : S ≃* ↥hsP := (e0.trans eN.symm).trans hsPermEquiv
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer S) ≤ 2 := by
    rw [Nat.card_congr (equivalence θ).toEquiv]
    exact hs_outer_card_le
  exact HeAux.isLocallyBalancedAbs_two_of_autModel_planes Nat.prime_three (by norm_num)
    hs_autModel θ hcen hout fun E hEP hE hEc H' hPH' hH'R y hy =>
      eq_one_of_mem_cores hs_autModel.le hs_autModel.conj_mem hs_hidx gLAPPrimeCoreOf_hs_three
        (nP := 44352000) (nY := 40320) card_hsP hs_hinv (by decide) hEP hE.2 hEc hPH' hH'R hy

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
