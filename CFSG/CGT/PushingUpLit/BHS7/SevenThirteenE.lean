module

public import CFSG.CGT.PushingUpLit.BHS7.OffenderModule
public import CFSG.CGT.PushingUpLit.BHS5.FiveSixAsm
public import CFSG.CGT.PushingUpLit.BHS.FourSymI

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {P T M W : Subgroup Γ}

theorem wtG_eq_card_of_isOffG (hmin : MinPar P T M)
    (hWe : IsElemAbelian 2 W) (hPW : P ≤ Subgroup.normalizer (W : Set Γ))
    (hker : P ⊓ Subgroup.centralizer (W : Set Γ) ≤ M)
    (hO2 : pCoreOf 2 P ≤ Subgroup.centralizer (W : Set Γ)) {A : Subgroup Γ} (hAT : A ≤ T)
    (hOff : IsOffG W A) : wtG W A = Nat.card ↥W := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
  have hAW : A ≤ Subgroup.normalizer (W : Set Γ) := hOff.1
  have hAP : A ≤ P := hAT.trans hmin.T_le
  have hminA := minPar_autOn hmin hPW hker
  have hO2A := pCoreOf_autOn_eq_bot hmin hPW hker hO2
  have hoffA : IsOff (autOn A W) := (isOffG_iff_isOff_autOn hWe hAW).mp hOff
  have hAA : autOn A W ≤ autOn P W := autOn_le_autOn W hAP
  obtain ⟨g, hg, u, hu, hgu⟩ := BHS5.five_six bhsSymType hV2 hminA hO2A ⟨autOn A W, hAA, hoffA⟩
  have hfix : ∀ v ∈ fixV (autOn T W), ∀ x ∈ autOn T W, x v = v := fun v hv x hx => by
    have := (mem_fixV_iff_le.mp hv) hx
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
  have hcen : cenIn (autOn P W) (fixV (autOn T W)) ≤ autOn M W := by
    set X := cenIn (autOn P W) (fixV (autOn T W)) with hX
    have hTX : autOn T W ≤ X := fun t ht => ⟨hminA.T_le ht, fun v hv => hfix v hv t ht⟩
    have hXP : X ≤ autOn P W := cenIn_le _ _
    have hXlt : X < autOn P W := lt_of_le_of_ne hXP fun hEq => hgu (by
      have hgX : g ∈ X := hEq ▸ hg
      exact hgX.2 u hu)
    exact hminA.max X hTX hXlt
  obtain ⟨B, hB⟩ := exists_isAOff ⟨autOn A W, hAA, hoffA⟩
  have hnum := three_six_numeric hV2 hminA hO2A hcen hB
  have hle : wt (autOn A W) ≤ offMax (autOn P W) := wt_le_offMax hAA hoffA
  have hBw : Nat.card ↥W = wt B := hnum.card
  have hBmax : wt B = offMax (autOn P W) := hB.2.2.1
  have hge : Nat.card ↥W ≤ wt (autOn A W) := hoffA.card_le_wt
  rw [← wt_autOn hWe hAW]
  omega

omit [Finite Γ] in
theorem isMaxElemAbelian_inf_centralizer_sup [Finite Γ] {T A W : Subgroup Γ}
    (hA : IsMaxElemAbelian T A) (hWe : IsElemAbelian 2 W) (hWT : W ≤ T)
    (hrel : (W ⊓ Subgroup.centralizer (A : Set Γ)).relIndex W =
      (A ⊓ Subgroup.centralizer (W : Set Γ)).relIndex A) :
    IsMaxElemAbelian T ((A ⊓ Subgroup.centralizer (W : Set Γ)) ⊔ W) := by
  set A₀ : Subgroup Γ := A ⊓ Subgroup.centralizer (W : Set Γ) with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hcomm : ∀ x ∈ A₀, ∀ y ∈ W, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hel : IsElemAbelian 2 (A₀ ⊔ W) :=
    isElemAbelian_sup' (isElemAbelian_mono' hA.2.1 hA₀A) hWe hcomm
  have hcard := card_sup_mul_card_inf' hcomm
  have hrA := Subgroup.relIndex_mul_card A₀ A
  rw [inf_of_le_left hA₀A] at hrA
  have hrW := Subgroup.relIndex_mul_card (W ⊓ Subgroup.centralizer (A : Set Γ)) W
  rw [inf_of_le_left inf_le_left] at hrW
  have hle : A₀ ⊓ W ≤ W ⊓ Subgroup.centralizer (A : Set Γ) := by
    intro x hx
    refine ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact (isElemAbelian_comm' hA.2.1 hx.1.1 ha).symm
  have hpos : 0 < Nat.card ↥(A₀ ⊓ W) := Nat.card_pos
  have h1 : Nat.card ↥A ≤ Nat.card ↥(A₀ ⊔ W) := by
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Nat.card ↥A * Nat.card ↥(A₀ ⊓ W)
        ≤ Nat.card ↥A * Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set Γ)) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
      _ = Nat.card ↥A₀ * Nat.card ↥W := by
          rw [← hrA, ← hrW, hrel]; ring
      _ = Nat.card ↥(A₀ ⊔ W) * Nat.card ↥(A₀ ⊓ W) := hcard.symm
  exact ⟨sup_le (hA₀A.trans hA.1) hWT, hel, fun B hBS hBe => (hA.2.2 B hBS hBe).trans h1⟩

theorem le_thompsonJ_of_minPar (hmin : MinPar P T M)
    (hWe : IsElemAbelian 2 W) (hPW : P ≤ Subgroup.normalizer (W : Set Γ))
    (hker : P ⊓ Subgroup.centralizer (W : Set Γ) ≤ M)
    (hO2 : pCoreOf 2 P ≤ Subgroup.centralizer (W : Set Γ)) (hWT : W ≤ T) :
    W ≤ thompsonJ T := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hTW : T ≤ Subgroup.normalizer (W : Set Γ) := hmin.T_le.trans hPW
  have hrel : (W ⊓ Subgroup.centralizer (A : Set Γ)).relIndex W =
      (A ⊓ Subgroup.centralizer (W : Set Γ)).relIndex A := by
    by_cases hc : A ≤ Subgroup.centralizer (W : Set Γ)
    · have hWA : W ≤ Subgroup.centralizer (A : Set Γ) := fun w hw =>
        Subgroup.mem_centralizer_iff.mpr fun a ha =>
          (Subgroup.mem_centralizer_iff.mp (hc ha) w hw).symm
      rw [inf_of_le_left hWA, inf_of_le_left hc, Subgroup.relIndex_self, Subgroup.relIndex_self]
    · have hOff : IsOffG W A := isOffG_of_isMaxElemAbelian hWe hWT hTW hA hc
      have hwt := wtG_eq_card_of_isOffG hmin hWe hPW hker hO2 hA.1 hOff
      have hrW := Subgroup.relIndex_mul_card (W ⊓ Subgroup.centralizer (A : Set Γ)) W
      rw [inf_of_le_left inf_le_left] at hrW
      have hpos : 0 < Nat.card ↥(W ⊓ Subgroup.centralizer (A : Set Γ)) := Nat.card_pos
      unfold wtG at hwt
      exact Nat.eq_of_mul_eq_mul_right hpos (hrW.trans hwt.symm)
  have := isMaxElemAbelian_inf_centralizer_sup hA hWe hWT hrel
  exact (le_sup_right : W ≤ (A ⊓ Subgroup.centralizer (W : Set Γ)) ⊔ W).trans
    (le_iSup₂_of_le _ this le_rfl)

end CFSG.CGT.PushingUpLit.BHS7
