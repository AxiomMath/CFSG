
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveBaseBase

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveLeaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public import Certificates.Certificate13671

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  Timmesfeld.Co1Five Matrix

section Elts

section Leaves

local notation "Rows" => CFSG.Sporadic.Co1Schreier.Native.Rows

theorem leaf_bot (hG : GOK) {τ : ℕ} (hτ : τ < 3) :
    GLAPPrimeCoreOf 5 (Cen (g1 hG τ) (g2 hG τ)) = ⊥ ∧
      Nat.card (Cen (g1 hG τ) (g2 hG τ)) = 125 * leafR.getD τ 0 := by
  have hpl := (planeOK_parts (globalOK_parts hG).2.2.2.2).2.2 τ hτ
  have h1 : MRep (a0Row gRows (repA.getD τ 0)) ((g1 hG τ : ↥GA) : GL24) := rep_a0Row hG hpl.1
  have h2 : MRep (a0Row gRows (repB.getD τ 0)) ((g2 hG τ : ↥GA) : GL24) :=
    rep_a0Row hG hpl.2.1
  obtain ⟨hc, hb⟩ := Certificates.certificate13671 τ hτ _ _ h1 h2
  exact ⟨hb, hc⟩

end Leaves

section Leaves2

theorem plane_bot (hG : GOK) {p : ℕ}
    (hp : p < 31) : GLAPPrimeCoreOf 5 (Subgroup.centralizer ({xP hG p,
      yP hG p} : Set ↥GA)) = ⊥ := by
  have hτ := ((planeOK_parts (globalOK_parts hG).2.2.2.2).1 p hp).1
  rw [xP_eq hG hp, yP_eq hG hp]
  exact gLAPPrimeCoreOf_pair_conj (cP p) _ _ (leaf_bot hG hτ).1

end Leaves2

section Planes

theorem hB_all (hG : GOK) :
    ∀ B : Subgroup ↥GA, B ≤ A0 hG → B.relIndex (A0 hG) = 5 →
      GLAPPrimeCoreOf 5 (Subgroup.centralizer (B : Set ↥GA)) = ⊥ := by
  intro B hB hidx
  obtain ⟨p, hp, rfl⟩ := plane_eq hG hB hidx
  rw [Subgroup.centralizer_closure]
  exact plane_bot hG hp

theorem hT0 (hG : GOK) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ((A0 hG : Subgroup ↥GA) : Set ↥GA)) = ⊥ := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨hbot, hcard⟩ := leaf_bot hG (τ := 0) (by norm_num)
  have hr : leafR.getD 0 0 = 1 := rfl
  rw [hr, mul_one] at hcard
  have hg1 : g1 hG 0 ∈ A0 hG := ⟨_, rfl⟩
  have hg2 : g2 hG 0 ∈ A0 hG := ⟨_, rfl⟩
  have hle : Subgroup.centralizer ((A0 hG : Subgroup ↥GA) : Set ↥GA) ≤
      Cen (g1 hG 0) (g2 hG 0) := by
    apply Subgroup.centralizer_le
    intro z hz
    rcases hz with rfl | rfl
    · exact hg1
    · exact hg2
  have hp : IsPGroup 5 ↥(Cen (g1 hG 0) (g2 hG 0)) :=
    IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  exact gLAPPrimeCoreOf_eq_bot_of_isPGroup Nat.prime_five (hp.to_le hle)

theorem oPrimeCoreTrivialAt_GA (hG : GOK) :
    OPrimeCoreTrivialAt 5 ↥GA := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  intro s hs
  obtain ⟨c, a, hca⟩ := fusion_exists hG s hs
  refine (gLAPPrimeCoreOf_centralizer_conj c s).1 ?_
  have hs' : orderOf (c * s * c⁻¹) = 5 := by rw [orderOf_conj_eq, hs]
  rw [hca] at hs' ⊢
  exact gLAPPrimeCoreOf_eq_bot_of_elemAbelian Nat.prime_five (A0_elemAbelian hG)
    (⟨_, rfl⟩ : φ hG (Multiplicative.ofAdd a) ∈ A0 hG) hs' (hB_all hG) (hT0 hG)

end Planes

end Elts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F
