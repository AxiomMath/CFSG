module

public import CFSG.Certificates.Kernel.RouteP.Link
public import CFSG.Certificates.Kernel.RouteP.MonoPerm
public import CFSG.Certificates.Kernel.RouteP.TabComplete

public section

namespace CFSG.KS.RouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KC.Fi24Net CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] def kb (OT : Nat → Nat) (b p : Nat) : Nat :=
  (if (OT (p / 512)).testBit (64 * (p % 512) + b) then 1 else 0) +
    (if (OT (p / 512)).testBit (64 * (p % 512) + (b + 1)) then 2 else 0)

theorem toNat_ofNat_lt' {k : Nat} (hk : k < 2 ^ 32) : (UInt32.ofNat k).toNat = k := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hk]

theorem rep_expandRight {OT : Nat → Nat} {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {j b : Nat}
    {pb kap : Array UInt32} (hpb : ∀ p < 306936, (pb[p]!).toNat = recF OT b p + 1)
    (hkap : ∀ p < 306936, (kap[p]!).toNat = kb OT (b + 19) p)
    (hj : LOK NW KA KB (Int.ofNat (j + 1))) (hg : ∀ k < 19, genOK OT (NW j) b k = true)
    (ha : kapLinkOK OT (KA j) (b + 19) = true) (hb : kapLinkOK OT (KB j) (b + 20) = true) :
    Rep 920808 (expandRight pb kap) (gT NW KA KB j)⁻¹ := by
  intro N hN
  rw [idx_of_lt _ hN, Perm.smul_def, gT_inv_apply hj]
  change _ = eE NW KA KB j N
  have hn' : netOK (NW j) = true := hj.1
  rw [eE_rec hn' hg ha hb hN]
  unfold expandRight
  have hp : N / 3 < 306936 := by omega
  have hr : recF OT b (N / 3) < 2 ^ 19 := Nat.mod_lt _ (by decide)
  have hk3 : kb OT (b + 19) (N / 3) ≤ 3 := by unfold kb; split_ifs <;> omega
  rw [ap_ofFn _ hN, hpb _ hp, hkap _ hp, toNat_ofNat_lt' (by omega), Nat.add_sub_cancel]
  unfold kb
  rfl

private theorem arr2_get0 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[0]! = a := rfl

private theorem arr2_get1 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[1]! = b := rfl

theorem mTabs_rep_of {OT : Nat → Nat} {D : Nat → Nat → Nat}
    (hl : (numLines coverGensText).size = 4 ∧ ∀ k < 4, ((numLines coverGensText)[k]!).size = 306936 ∧
      ∀ p < 306936, ((numLines coverGensText)[k]!)[p]! = UInt32.ofNat (D k p))
    (hD : ∀ p < 306936, D 0 p = recF OT 0 p + 1 ∧ D 1 p = kb OT 19 p ∧ D 2 p = recF OT 32 p + 1 ∧
      D 3 p = kb OT 51 p)
    {NW : Nat → Nat → Nat} {KA KB : Nat → Nat}
    (h0 : LOK NW KA KB (Int.ofNat 1)) (g0 : ∀ k < 19, genOK OT (NW 0) 0 k = true)
    (a0 : kapLinkOK OT (KA 0) 19 = true) (b0 : kapLinkOK OT (KB 0) 20 = true)
    (h1 : LOK NW KA KB (Int.ofNat 2)) (g1 : ∀ k < 19, genOK OT (NW 1) 32 k = true)
    (a1 : kapLinkOK OT (KA 1) 51 = true) (b1 : kapLinkOK OT (KB 1) 52 = true) :
    Rep 920808 (mTabs ())[0]! (gT NW KA KB 0) ∧ Rep 920808 (mTabs ())[1]! (gT NW KA KB 1) := by
  have hn : (920808 : Nat) < 2 ^ 32 := by decide
  have hlt : ∀ k < 4, ∀ p < 306936, D k p < 2 ^ 32 := by
    intro k hk p hp
    obtain ⟨e0, e1, e2, e3⟩ := hD p hp
    have r0 : recF OT 0 p < 2 ^ 19 := Nat.mod_lt _ (by decide)
    have r2 : recF OT 32 p < 2 ^ 19 := Nat.mod_lt _ (by decide)
    have k0 : kb OT 19 p ≤ 3 := by unfold kb; split_ifs <;> omega
    have k1 : kb OT 51 p ≤ 3 := by unfold kb; split_ifs <;> omega
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> omega
  have hv : ∀ k < 4, ∀ p < 306936, (((numLines coverGensText)[k]!)[p]!).toNat = D k p := by
    intro k hk p hp
    rw [(hl.2 k hk).2 p hp, toNat_ofNat_lt' (hlt k hk p hp)]
  have e0 : (mTabs ())[0]! = invT degree (expandRight (numLines coverGensText)[0]!
      (numLines coverGensText)[1]!) := by
    rw [mTabs]
    exact arr2_get0 _ _
  have e1 : (mTabs ())[1]! = invT degree (expandRight (numLines coverGensText)[2]!
      (numLines coverGensText)[3]!) := by
    rw [mTabs]
    exact arr2_get1 _ _
  refine ⟨?_, ?_⟩
  · rw [e0]
    have := rep_invT hn (rep_expandRight (b := 0) (j := 0) (fun p hp => by rw [hv 0 (by decide) p hp,
      (hD p hp).1]) (fun p hp => by rw [hv 1 (by decide) p hp, (hD p hp).2.1]) h0 g0 a0 b0)
    rwa [inv_inv] at this
  · rw [e1]
    have := rep_invT hn (rep_expandRight (b := 32) (j := 1) (fun p hp => by rw [hv 2 (by decide) p hp,
      (hD p hp).2.2.1]) (fun p hp => by rw [hv 3 (by decide) p hp, (hD p hp).2.2.2]) h1 g1 a1 b1)
    rwa [inv_inv] at this

end CFSG.KS.RouteP

end
