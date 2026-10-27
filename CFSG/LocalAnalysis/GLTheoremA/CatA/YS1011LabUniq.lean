module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq2
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreExcB
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.Quasithin.EmptyFaithful.S146zYFOOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.E8Pilot CFSG.StandardType.MpTypeDet CFSG.StandardType.NbrInnerMore
open CFSG.SeitzReduction.E8Pilot CFSG.StandardType.MpTypeDet CFSG.StandardType.NbrInnerMore

def excOrd (t : LargeEvenLieTag) (f : ℕ) : ℕ :=
  match t with
  | .E6 => ordE6 (2 ^ f)
  | .E7 => ordE7 (2 ^ f)
  | .E8 => ordE8 (2 ^ f)
  | .F4 => ordF4 (2 ^ f)
  | .twE6 => ordTwistedE6 (2 ^ f)
  | .triD4 => ordTrialityD4 (2 ^ f)
  | .G2 => ordG2 (2 ^ f)
  | .twB2 => ordSuzuki (2 ^ f)
  | .twF4 => ordTwistedF4 (2 ^ f)
  | .twF4der => ordTits
  | _ => 0

def excOK (t : LargeEvenLieTag) (f : ℕ) : Prop :=
  match t with
  | .E6 | .E7 | .E8 | .F4 | .twE6 | .triD4 => 1 ≤ f
  | .G2 => 2 ≤ f
  | .twB2 | .twF4 => f % 2 = 1 ∧ 3 ≤ f
  | .twF4der => f = 1
  | _ => False

theorem excOrd_G2_ne_Suzuki {g f : ℕ} (hg : 2 ≤ g) (hf : 1 ≤ f) :
    ordG2 (2 ^ g) ≠ ordSuzuki (2 ^ f) := by
  intro h
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' (by omega : 1 ≤ g)
  rw [h] at h1
  obtain ⟨hN, hZ⟩ := h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' hf)
  have hk := (hZ (g * 6) (by omega) (by omega)).mp (Or.inl dvd_rfl)
  rcases hk with ⟨-, h3⟩ | h2
  · exact (h3 (by rw [← hN])).elim
  · have := Nat.le_of_dvd (by omega) h2
    omega

theorem ordG2_ne_ordTits {g : ℕ} (hg : 1 ≤ g) : ordG2 (2 ^ g) ≠ ordTits := by
  have h := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' hg).ne_of_ne
    (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide) (show g * 6 ≠ 11 by omega)
  intro he
  apply h
  rw [he]
  norm_num [ordTits]

theorem ordSuzuki_ne_ordTits {g : ℕ} (hg : 1 ≤ g) : ordSuzuki (2 ^ g) ≠ ordTits := by
  have h := (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki' hg).ne_of_ne
    (show Odd (3 ^ 3 * 5 ^ 2 * 13) by decide) (show g * 2 ≠ 11 by omega)
  intro he
  apply h
  rw [he]
  norm_num [ordTits]

theorem same_G2 {f f' : ℕ} (hf : excOK .G2 f) (hf' : excOK .G2 f') (h : excOrd .G2 f = excOrd .G2 f') :
    f = f' := by
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2' (by simp only [excOK] at hf; omega :
    1 ≤ f)
  have h2 : ordG2 (2 ^ f) = ordG2 (2 ^ f') := h
  rw [h2] at h1
  have hN := (h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordG2'
    (by simp only [excOK] at hf'; omega : 1 ≤ f'))).1
  omega

theorem same_twB2 {f f' : ℕ} (hf : excOK .twB2 f) (hf' : excOK .twB2 f')
    (h : excOrd .twB2 f = excOrd .twB2 f') : f = f' := by
  have h1 := CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki'
    (by simp only [excOK] at hf; omega : 1 ≤ f)
  have h2 : ordSuzuki (2 ^ f) = ordSuzuki (2 ^ f') := h
  rw [h2] at h1
  have hN := (h1.transfer (CFSG.SeitzReduction.F4Pilot.EvenExc.profile_ordSuzuki'
    (by simp only [excOK] at hf'; omega : 1 ≤ f'))).1
  omega

theorem same_Tits {f f' : ℕ} (hf : excOK .twF4der f) (hf' : excOK .twF4der f') (_h : excOrd .twF4der f = excOrd .twF4der f') :
    f = f' := by
  simp only [excOK] at hf hf'
  omega


theorem same_E6 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .E6 f')
    (h : excOrd .E6 f = excOrd .E6 f') : f = f' :=
  CFSG.StandardType.MpTypeDet.eq_of_ordE6_eq (by simp only [excOK] at hf; omega) (by simp only [excOK] at hf'; omega) h

theorem same_E7 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .E7 f')
    (h : excOrd .E7 f = excOrd .E7 f') : f = f' :=
  CFSG.SeitzReduction.E8Pilot.eq_of_ordE7_eq (by simp only [excOK] at hf; omega) (by simp only [excOK] at hf'; omega) h

theorem same_E8 {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .E8 f')
    (h : excOrd .E8 f = excOrd .E8 f') : f = f' :=
  CFSG.StandardType.NbrInnerMore.eq_of_ordE8_eq (by simp only [excOK] at hf; omega) (by simp only [excOK] at hf'; omega) h

theorem same_F4 {f f' : ℕ} (hf : excOK .F4 f) (hf' : excOK .F4 f')
    (h : excOrd .F4 f = excOrd .F4 f') : f = f' :=
  CFSG.StandardType.NbrInnerMore.eq_of_ordF4_eq (by simp only [excOK] at hf; omega) (by simp only [excOK] at hf'; omega) h

theorem same_twE6 {f f' : ℕ} (hf : excOK .twE6 f) (hf' : excOK .twE6 f')
    (h : excOrd .twE6 f = excOrd .twE6 f') : f = f' :=
  CFSG.StandardType.MpTypeDet.eq_of_ordTwistedE6_eq (by simp only [excOK] at hf; omega) (by simp only [excOK] at hf'; omega) h

theorem same_triD4 {f f' : ℕ} (hf : excOK .triD4 f) (hf' : excOK .triD4 f')
    (h : excOrd .triD4 f = excOrd .triD4 f') : f = f' :=
  CFSG.StandardType.NbrInnerMore.eq_of_ordTrialityD4_eq (by simp only [excOK] at hf; omega) (by simp only [excOK] at hf'; omega) h

theorem same_twF4 {f f' : ℕ} (hf : excOK .twF4 f) (hf' : excOK .twF4 f')
    (h : excOrd .twF4 f = excOrd .twF4 f') : f = f' :=
  CFSG.StandardType.NbrInnerMore.eq_of_ordTwistedF4_eq (by simp only [excOK] at hf; omega) (by simp only [excOK] at hf'; omega) h

theorem ne_E6_E7 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .E7 f') :
    excOrd .E6 f ≠ excOrd .E7 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact ordE6_ne_ordE7 h1 h2

theorem ne_E6_E8 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .E8 f') :
    excOrd .E6 f ≠ excOrd .E8 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact ordE6_ne_ordE8 h1 h2

theorem ne_E6_F4 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .F4 f') :
    excOrd .E6 f ≠ excOrd .F4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact ordE6_ne_ordF4 h1 h2

theorem ne_E6_twE6 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .twE6 f') :
    excOrd .E6 f ≠ excOrd .twE6 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact ordE6_ne_ordTwistedE6 h1 h2

theorem ne_E6_triD4 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .triD4 f') :
    excOrd .E6 f ≠ excOrd .triD4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTrialityD4_ne_ordE6 h2 h1).symm

theorem ne_E6_G2 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .G2 f') :
    excOrd .E6 f ≠ excOrd .G2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordG2_ne_ordE6 h2 h1).symm

theorem ne_E6_twB2 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .twB2 f') :
    excOrd .E6 f ≠ excOrd .twB2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordSuzuki_ne_ordE6 h2 h1).symm

theorem ne_E6_twF4 {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .twF4 f') :
    excOrd .E6 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedF4_ne_ordE6 h2 h1).symm

theorem ne_E6_Tits {f f' : ℕ} (hf : excOK .E6 f) (hf' : excOK .twF4der f') :
    excOrd .E6 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact (ordTits_ne_ordE6 h1).symm

theorem ne_E7_E8 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .E8 f') :
    excOrd .E7 f ≠ excOrd .E8 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordE8_ne_ordE7 h2 h1).symm

theorem ne_E7_F4 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .F4 f') :
    excOrd .E7 f ≠ excOrd .F4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordF4_ne_ordE7 h2 h1).symm

theorem ne_E7_twE6 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .twE6 f') :
    excOrd .E7 f ≠ excOrd .twE6 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedE6_ne_ordE7 h2 h1).symm

theorem ne_E7_triD4 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .triD4 f') :
    excOrd .E7 f ≠ excOrd .triD4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTrialityD4_ne_ordE7 h2 h1).symm

theorem ne_E7_G2 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .G2 f') :
    excOrd .E7 f ≠ excOrd .G2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordG2_ne_ordE7 h2 h1).symm

theorem ne_E7_twB2 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .twB2 f') :
    excOrd .E7 f ≠ excOrd .twB2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordSuzuki_ne_ordE7 h2 h1).symm

theorem ne_E7_twF4 {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .twF4 f') :
    excOrd .E7 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedF4_ne_ordE7 h2 h1).symm

theorem ne_E7_Tits {f f' : ℕ} (hf : excOK .E7 f) (hf' : excOK .twF4der f') :
    excOrd .E7 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact (ordTits_ne_ordE7 h1).symm

theorem ne_E8_twE6 {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .twE6 f') :
    excOrd .E8 f ≠ excOrd .twE6 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedE6_ne_ordE8 h2 h1).symm

theorem ne_E8_triD4 {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .triD4 f') :
    excOrd .E8 f ≠ excOrd .triD4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTrialityD4_ne_ordE8 h2 h1).symm

theorem ne_E8_G2 {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .G2 f') :
    excOrd .E8 f ≠ excOrd .G2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordG2_ne_ordE8 h2 h1).symm

theorem ne_E8_twB2 {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .twB2 f') :
    excOrd .E8 f ≠ excOrd .twB2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordSuzuki_ne_ordE8 h2 h1).symm

theorem ne_E8_twF4 {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .twF4 f') :
    excOrd .E8 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedF4_ne_ordE8 h2 h1).symm

theorem ne_E8_Tits {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .twF4der f') :
    excOrd .E8 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact (ordTits_ne_ordE8 h1).symm

theorem ne_E8_F4 {f f' : ℕ} (hf : excOK .E8 f) (hf' : excOK .F4 f') :
    excOrd .E8 f ≠ excOrd .F4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordF4_ne_ordE8 h2 h1).symm

theorem ne_F4_twE6 {f f' : ℕ} (hf : excOK .F4 f) (hf' : excOK .twE6 f') :
    excOrd .F4 f ≠ excOrd .twE6 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedE6_ne_ordF4 h2 h1).symm

theorem ne_F4_triD4 {f f' : ℕ} (hf : excOK .F4 f) (hf' : excOK .triD4 f') :
    excOrd .F4 f ≠ excOrd .triD4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTrialityD4_ne_ordF4 h2 h1).symm

theorem ne_F4_G2 {f f' : ℕ} (hf : excOK .F4 f) (hf' : excOK .G2 f') :
    excOrd .F4 f ≠ excOrd .G2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordG2_ne_ordF4 h2 h1).symm

theorem ne_F4_twB2 {f f' : ℕ} (hf : excOK .F4 f) (hf' : excOK .twB2 f') :
    excOrd .F4 f ≠ excOrd .twB2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordSuzuki_ne_ordF4 h2 h1).symm

theorem ne_F4_twF4 {f f' : ℕ} (hf : excOK .F4 f) (hf' : excOK .twF4 f') :
    excOrd .F4 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedF4_ne_ordF4 h2 h1).symm

theorem ne_F4_Tits {f f' : ℕ} (hf : excOK .F4 f) (hf' : excOK .twF4der f') :
    excOrd .F4 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact (ordTits_ne_ordF4 h1).symm

theorem ne_twE6_triD4 {f f' : ℕ} (hf : excOK .twE6 f) (hf' : excOK .triD4 f') :
    excOrd .twE6 f ≠ excOrd .triD4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTrialityD4_ne_ordTwistedE6 h2 h1).symm

theorem ne_twE6_G2 {f f' : ℕ} (hf : excOK .twE6 f) (hf' : excOK .G2 f') :
    excOrd .twE6 f ≠ excOrd .G2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordG2_ne_ordTwistedE6 h2 h1).symm

theorem ne_twE6_twB2 {f f' : ℕ} (hf : excOK .twE6 f) (hf' : excOK .twB2 f') :
    excOrd .twE6 f ≠ excOrd .twB2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordSuzuki_ne_ordTwistedE6 h2 h1).symm

theorem ne_twE6_twF4 {f f' : ℕ} (hf : excOK .twE6 f) (hf' : excOK .twF4 f') :
    excOrd .twE6 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordTwistedF4_ne_ordTwistedE6 h2 h1).symm

theorem ne_twE6_Tits {f f' : ℕ} (hf : excOK .twE6 f) (hf' : excOK .twF4der f') :
    excOrd .twE6 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact (ordTits_ne_ordTwistedE6 h1).symm

theorem ne_triD4_G2 {f f' : ℕ} (hf : excOK .triD4 f) (hf' : excOK .G2 f') :
    excOrd .triD4 f ≠ excOrd .G2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordG2_ne_ordTrialityD4 h2 h1).symm

theorem ne_triD4_twB2 {f f' : ℕ} (hf : excOK .triD4 f) (hf' : excOK .twB2 f') :
    excOrd .triD4 f ≠ excOrd .twB2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact (ordSuzuki_ne_ordTrialityD4 h2 h1).symm

theorem ne_triD4_twF4 {f f' : ℕ} (hf : excOK .triD4 f) (hf' : excOK .twF4 f') :
    excOrd .triD4 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact ordTrialityD4_ne_ordTwistedF4 h1 h2

theorem ne_triD4_Tits {f f' : ℕ} (hf : excOK .triD4 f) (hf' : excOK .twF4der f') :
    excOrd .triD4 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact (ordTits_ne_ordTrialityD4 h1).symm

theorem ne_G2_twB2 {f f' : ℕ} (hf : excOK .G2 f) (hf' : excOK .twB2 f') :
    excOrd .G2 f ≠ excOrd .twB2 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact excOrd_G2_ne_Suzuki (by simp only [excOK] at hf; omega) h2

theorem ne_G2_twF4 {f f' : ℕ} (hf : excOK .G2 f) (hf' : excOK .twF4 f') :
    excOrd .G2 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  have h3 : f' ≠ 2 := by simp only [excOK] at hf'; omega
  exact ordG2_ne_ordTwistedF4 h1 h2 h3

theorem ne_G2_Tits {f f' : ℕ} (hf : excOK .G2 f) (hf' : excOK .twF4der f') :
    excOrd .G2 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact ordG2_ne_ordTits h1

theorem ne_twB2_twF4 {f f' : ℕ} (hf : excOK .twB2 f) (hf' : excOK .twF4 f') :
    excOrd .twB2 f ≠ excOrd .twF4 f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  have h2 : 1 ≤ f' := by simp only [excOK] at hf'; omega
  exact ordSuzuki_ne_ordTwistedF4 h1 h2

theorem ne_twB2_Tits {f f' : ℕ} (hf : excOK .twB2 f) (hf' : excOK .twF4der f') :
    excOrd .twB2 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact ordSuzuki_ne_ordTits h1

theorem ne_twF4_Tits {f f' : ℕ} (hf : excOK .twF4 f) (hf' : excOK .twF4der f') :
    excOrd .twF4 f ≠ excOrd .twF4der f' := by
  have h1 : 1 ≤ f := by simp only [excOK] at hf; omega
  exact (ordTits_ne_ordTwistedF4 h1).symm

theorem excOrd_inj {t t' : LargeEvenLieTag} {f f' : ℕ} (ht : excOK t f) (ht' : excOK t' f')
    (h : excOrd t f = excOrd t' f') : t = t' ∧ f = f' := by
  match t, t', ht, ht', h with
  | .E6, .E6, ht, ht', h => exact ⟨rfl, same_E6 ht ht' h⟩
  | .E7, .E7, ht, ht', h => exact ⟨rfl, same_E7 ht ht' h⟩
  | .E8, .E8, ht, ht', h => exact ⟨rfl, same_E8 ht ht' h⟩
  | .F4, .F4, ht, ht', h => exact ⟨rfl, same_F4 ht ht' h⟩
  | .twE6, .twE6, ht, ht', h => exact ⟨rfl, same_twE6 ht ht' h⟩
  | .triD4, .triD4, ht, ht', h => exact ⟨rfl, same_triD4 ht ht' h⟩
  | .G2, .G2, ht, ht', h => exact ⟨rfl, same_G2 ht ht' h⟩
  | .twB2, .twB2, ht, ht', h => exact ⟨rfl, same_twB2 ht ht' h⟩
  | .twF4, .twF4, ht, ht', h => exact ⟨rfl, same_twF4 ht ht' h⟩
  | .twF4der, .twF4der, ht, ht', h => exact ⟨rfl, same_Tits ht ht' h⟩
  | .E6, .E7, ht, ht', h => exact absurd h (ne_E6_E7 ht ht')
  | .E7, .E6, ht, ht', h => exact absurd h.symm (ne_E6_E7 ht' ht)
  | .E6, .E8, ht, ht', h => exact absurd h (ne_E6_E8 ht ht')
  | .E8, .E6, ht, ht', h => exact absurd h.symm (ne_E6_E8 ht' ht)
  | .E6, .F4, ht, ht', h => exact absurd h (ne_E6_F4 ht ht')
  | .F4, .E6, ht, ht', h => exact absurd h.symm (ne_E6_F4 ht' ht)
  | .E6, .twE6, ht, ht', h => exact absurd h (ne_E6_twE6 ht ht')
  | .twE6, .E6, ht, ht', h => exact absurd h.symm (ne_E6_twE6 ht' ht)
  | .E6, .triD4, ht, ht', h => exact absurd h (ne_E6_triD4 ht ht')
  | .triD4, .E6, ht, ht', h => exact absurd h.symm (ne_E6_triD4 ht' ht)
  | .E6, .G2, ht, ht', h => exact absurd h (ne_E6_G2 ht ht')
  | .G2, .E6, ht, ht', h => exact absurd h.symm (ne_E6_G2 ht' ht)
  | .E6, .twB2, ht, ht', h => exact absurd h (ne_E6_twB2 ht ht')
  | .twB2, .E6, ht, ht', h => exact absurd h.symm (ne_E6_twB2 ht' ht)
  | .E6, .twF4, ht, ht', h => exact absurd h (ne_E6_twF4 ht ht')
  | .twF4, .E6, ht, ht', h => exact absurd h.symm (ne_E6_twF4 ht' ht)
  | .E6, .twF4der, ht, ht', h => exact absurd h (ne_E6_Tits ht ht')
  | .twF4der, .E6, ht, ht', h => exact absurd h.symm (ne_E6_Tits ht' ht)
  | .E7, .E8, ht, ht', h => exact absurd h (ne_E7_E8 ht ht')
  | .E8, .E7, ht, ht', h => exact absurd h.symm (ne_E7_E8 ht' ht)
  | .E7, .F4, ht, ht', h => exact absurd h (ne_E7_F4 ht ht')
  | .F4, .E7, ht, ht', h => exact absurd h.symm (ne_E7_F4 ht' ht)
  | .E7, .twE6, ht, ht', h => exact absurd h (ne_E7_twE6 ht ht')
  | .twE6, .E7, ht, ht', h => exact absurd h.symm (ne_E7_twE6 ht' ht)
  | .E7, .triD4, ht, ht', h => exact absurd h (ne_E7_triD4 ht ht')
  | .triD4, .E7, ht, ht', h => exact absurd h.symm (ne_E7_triD4 ht' ht)
  | .E7, .G2, ht, ht', h => exact absurd h (ne_E7_G2 ht ht')
  | .G2, .E7, ht, ht', h => exact absurd h.symm (ne_E7_G2 ht' ht)
  | .E7, .twB2, ht, ht', h => exact absurd h (ne_E7_twB2 ht ht')
  | .twB2, .E7, ht, ht', h => exact absurd h.symm (ne_E7_twB2 ht' ht)
  | .E7, .twF4, ht, ht', h => exact absurd h (ne_E7_twF4 ht ht')
  | .twF4, .E7, ht, ht', h => exact absurd h.symm (ne_E7_twF4 ht' ht)
  | .E7, .twF4der, ht, ht', h => exact absurd h (ne_E7_Tits ht ht')
  | .twF4der, .E7, ht, ht', h => exact absurd h.symm (ne_E7_Tits ht' ht)
  | .E8, .twE6, ht, ht', h => exact absurd h (ne_E8_twE6 ht ht')
  | .twE6, .E8, ht, ht', h => exact absurd h.symm (ne_E8_twE6 ht' ht)
  | .E8, .triD4, ht, ht', h => exact absurd h (ne_E8_triD4 ht ht')
  | .triD4, .E8, ht, ht', h => exact absurd h.symm (ne_E8_triD4 ht' ht)
  | .E8, .G2, ht, ht', h => exact absurd h (ne_E8_G2 ht ht')
  | .G2, .E8, ht, ht', h => exact absurd h.symm (ne_E8_G2 ht' ht)
  | .E8, .twB2, ht, ht', h => exact absurd h (ne_E8_twB2 ht ht')
  | .twB2, .E8, ht, ht', h => exact absurd h.symm (ne_E8_twB2 ht' ht)
  | .E8, .twF4, ht, ht', h => exact absurd h (ne_E8_twF4 ht ht')
  | .twF4, .E8, ht, ht', h => exact absurd h.symm (ne_E8_twF4 ht' ht)
  | .E8, .twF4der, ht, ht', h => exact absurd h (ne_E8_Tits ht ht')
  | .twF4der, .E8, ht, ht', h => exact absurd h.symm (ne_E8_Tits ht' ht)
  | .E8, .F4, ht, ht', h => exact absurd h (ne_E8_F4 ht ht')
  | .F4, .E8, ht, ht', h => exact absurd h.symm (ne_E8_F4 ht' ht)
  | .F4, .twE6, ht, ht', h => exact absurd h (ne_F4_twE6 ht ht')
  | .twE6, .F4, ht, ht', h => exact absurd h.symm (ne_F4_twE6 ht' ht)
  | .F4, .triD4, ht, ht', h => exact absurd h (ne_F4_triD4 ht ht')
  | .triD4, .F4, ht, ht', h => exact absurd h.symm (ne_F4_triD4 ht' ht)
  | .F4, .G2, ht, ht', h => exact absurd h (ne_F4_G2 ht ht')
  | .G2, .F4, ht, ht', h => exact absurd h.symm (ne_F4_G2 ht' ht)
  | .F4, .twB2, ht, ht', h => exact absurd h (ne_F4_twB2 ht ht')
  | .twB2, .F4, ht, ht', h => exact absurd h.symm (ne_F4_twB2 ht' ht)
  | .F4, .twF4, ht, ht', h => exact absurd h (ne_F4_twF4 ht ht')
  | .twF4, .F4, ht, ht', h => exact absurd h.symm (ne_F4_twF4 ht' ht)
  | .F4, .twF4der, ht, ht', h => exact absurd h (ne_F4_Tits ht ht')
  | .twF4der, .F4, ht, ht', h => exact absurd h.symm (ne_F4_Tits ht' ht)
  | .twE6, .triD4, ht, ht', h => exact absurd h (ne_twE6_triD4 ht ht')
  | .triD4, .twE6, ht, ht', h => exact absurd h.symm (ne_twE6_triD4 ht' ht)
  | .twE6, .G2, ht, ht', h => exact absurd h (ne_twE6_G2 ht ht')
  | .G2, .twE6, ht, ht', h => exact absurd h.symm (ne_twE6_G2 ht' ht)
  | .twE6, .twB2, ht, ht', h => exact absurd h (ne_twE6_twB2 ht ht')
  | .twB2, .twE6, ht, ht', h => exact absurd h.symm (ne_twE6_twB2 ht' ht)
  | .twE6, .twF4, ht, ht', h => exact absurd h (ne_twE6_twF4 ht ht')
  | .twF4, .twE6, ht, ht', h => exact absurd h.symm (ne_twE6_twF4 ht' ht)
  | .twE6, .twF4der, ht, ht', h => exact absurd h (ne_twE6_Tits ht ht')
  | .twF4der, .twE6, ht, ht', h => exact absurd h.symm (ne_twE6_Tits ht' ht)
  | .triD4, .G2, ht, ht', h => exact absurd h (ne_triD4_G2 ht ht')
  | .G2, .triD4, ht, ht', h => exact absurd h.symm (ne_triD4_G2 ht' ht)
  | .triD4, .twB2, ht, ht', h => exact absurd h (ne_triD4_twB2 ht ht')
  | .twB2, .triD4, ht, ht', h => exact absurd h.symm (ne_triD4_twB2 ht' ht)
  | .triD4, .twF4, ht, ht', h => exact absurd h (ne_triD4_twF4 ht ht')
  | .twF4, .triD4, ht, ht', h => exact absurd h.symm (ne_triD4_twF4 ht' ht)
  | .triD4, .twF4der, ht, ht', h => exact absurd h (ne_triD4_Tits ht ht')
  | .twF4der, .triD4, ht, ht', h => exact absurd h.symm (ne_triD4_Tits ht' ht)
  | .G2, .twB2, ht, ht', h => exact absurd h (ne_G2_twB2 ht ht')
  | .twB2, .G2, ht, ht', h => exact absurd h.symm (ne_G2_twB2 ht' ht)
  | .G2, .twF4, ht, ht', h => exact absurd h (ne_G2_twF4 ht ht')
  | .twF4, .G2, ht, ht', h => exact absurd h.symm (ne_G2_twF4 ht' ht)
  | .G2, .twF4der, ht, ht', h => exact absurd h (ne_G2_Tits ht ht')
  | .twF4der, .G2, ht, ht', h => exact absurd h.symm (ne_G2_Tits ht' ht)
  | .twB2, .twF4, ht, ht', h => exact absurd h (ne_twB2_twF4 ht ht')
  | .twF4, .twB2, ht, ht', h => exact absurd h.symm (ne_twB2_twF4 ht' ht)
  | .twB2, .twF4der, ht, ht', h => exact absurd h (ne_twB2_Tits ht ht')
  | .twF4der, .twB2, ht, ht', h => exact absurd h.symm (ne_twB2_Tits ht' ht)
  | .twF4, .twF4der, ht, ht', h => exact absurd h (ne_twF4_Tits ht ht')
  | .twF4der, .twF4, ht, ht', h => exact absurd h.symm (ne_twF4_Tits ht' ht)
  | LargeEvenLieTag.A, _, ht, _, _ => exact (ht : False).elim
  | LargeEvenLieTag.twA, _, ht, _, _ => exact (ht : False).elim
  | LargeEvenLieTag.B, _, ht, _, _ => exact (ht : False).elim
  | LargeEvenLieTag.C, _, ht, _, _ => exact (ht : False).elim
  | LargeEvenLieTag.D, _, ht, _, _ => exact (ht : False).elim
  | LargeEvenLieTag.twD, _, ht, _, _ => exact (ht : False).elim
  | LargeEvenLieTag.B2der, _, ht, _, _ => exact (ht : False).elim
  | LargeEvenLieTag.G2der, _, ht, _, _ => exact (ht : False).elim
  | _, LargeEvenLieTag.A, _, ht', _ => exact (ht' : False).elim
  | _, LargeEvenLieTag.twA, _, ht', _ => exact (ht' : False).elim
  | _, LargeEvenLieTag.B, _, ht', _ => exact (ht' : False).elim
  | _, LargeEvenLieTag.C, _, ht', _ => exact (ht' : False).elim
  | _, LargeEvenLieTag.D, _, ht', _ => exact (ht' : False).elim
  | _, LargeEvenLieTag.twD, _, ht', _ => exact (ht' : False).elim
  | _, LargeEvenLieTag.B2der, _, ht', _ => exact (ht' : False).elim
  | _, LargeEvenLieTag.G2der, _, ht', _ => exact (ht' : False).elim


def IsClsLab (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

section Cert

theorem cls_det {X : Type} [Group X] {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hc : IsClsLab lab) (hM : CFSG.StandardType.MarkedModel lab X) {t : StatedLieTag} {n f' : ℕ}
    (h : CFSG.Blueprint.LieModel X t n 2 f') :
    t = CFSG.StandardType.markTag lab ∧ n = CFSG.StandardType.markRank lab ∧
      f' = CFSG.StandardType.markDeg lab := by
  obtain ⟨tg, r, nn⟩ := lab
  unfold CFSG.StandardType.MarkedModel at hM
  unfold IsClsLab at hc
  dsimp only at hl hc
  have hc2 : CFSG.StandardType.markChar ⟨tg, r, nn⟩ = 2 := by
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hc2] at hM
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    rcases (show r = 1 ∨ 2 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSL 2 2 nn := hM
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.RankOne.sl2EvenTypeDet X nn t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hM' : CFSG.Blueprint.LieModel X .PSL (r + 1) 2 nn := hM
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by omega) hM' h
      exact ⟨h1, h2, h3⟩
  ·
    rcases (show r = 2 ∨ 3 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSU 3 2 nn := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.su3EvenTypeDet X nn t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hM' : CFSG.Blueprint.LieModel X .PSU (r + 1) 2 nn := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := r + 1) (by omega) X nn t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
  ·
    have hM' : CFSG.Blueprint.LieModel X .PSp r 2 nn := hM
    obtain ⟨h1, h2, h3⟩ :=
      CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet r X nn t n f' hM' h.admissible h
    exact ⟨h1, h2, h3⟩
  ·
    have hM' : CFSG.Blueprint.LieModel X .PSp r 2 nn := hM
    obtain ⟨h1, h2, h3⟩ :=
      CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet r X nn t n f' hM' h.admissible h
    exact ⟨h1, h2, h3⟩
  ·
    rcases (show r = 3 ∨ 4 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSL 4 2 nn := hM
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) hM' h
      exact ⟨h1, h2, h3⟩
    · have hr3 : r ≠ 3 := by omega
      have hM' : CFSG.Blueprint.LieModel X .POmegaPlus r 2 nn := by
        have h' := hM
        simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
          CFSG.StandardType.markDeg, if_neg hr3] at h'
        exact h'
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt r X .POmegaPlus nn t n f'
        (Or.inl rfl) hM' h.admissible h
      simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
        CFSG.StandardType.markDeg, if_neg hr3]
      exact ⟨h1, h2, h3⟩
  ·
    rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by
      have := hl.2; simp only [LargeEvenInLambda2] at this; omega) with rfl | rfl | hr
    · have hM' : CFSG.Blueprint.LieModel X .PSL 2 2 (2 * nn) := hM
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.RankOne.sl2EvenTypeDet X (2 * nn) t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hM' : CFSG.Blueprint.LieModel X .PSU 4 2 nn := hM
      obtain ⟨h1, h2, h3⟩ :=
        CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := 4) le_rfl X nn t n f' hM' h.admissible h
      exact ⟨h1, h2, h3⟩
    · have hr2 : r ≠ 2 := by omega
      have hr3 : r ≠ 3 := by omega
      have hM' : CFSG.Blueprint.LieModel X .POmegaMinus r 2 nn := by
        have h' := hM
        simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
          CFSG.StandardType.markDeg, if_neg hr2, if_neg hr3] at h'
        exact h'
      obtain ⟨h1, h2, h3⟩ := CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt r X .POmegaMinus nn t n f'
        (Or.inr rfl) hM' h.admissible h
      simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
        CFSG.StandardType.markDeg, if_neg hr2, if_neg hr3]
      exact ⟨h1, h2, h3⟩



theorem cls_pair (lab₁ lab₂ : LargeEvenLabel) (hl₁ : LargeEvenInLambda2 lab₁)
    (hl₂ : LargeEvenInLambda2 lab₂) (h₁ : IsClsLab lab₁) (h₂ : IsClsLab lab₂)
    (hs : CFSG.StandardType.markTag lab₁ = CFSG.StandardType.markTag lab₂)
    (hr : CFSG.StandardType.markRank lab₁ = CFSG.StandardType.markRank lab₂)
    (hd : CFSG.StandardType.markDeg lab₁ = CFSG.StandardType.markDeg lab₂) :
    lab₁ = lab₂ ∨ ((lab₁.tag = .B ∨ lab₁.tag = .C) ∧ (lab₂.tag = .B ∨ lab₂.tag = .C) ∧
      lab₁.rank = lab₂.rank ∧ lab₁.n = lab₂.n) ∨
    (CFSG.StandardType.markTag lab₁ = .PSL ∧ CFSG.StandardType.markRank lab₁ = 4) ∨
    (CFSG.StandardType.markTag lab₁ = .PSU ∧ CFSG.StandardType.markRank lab₁ = 4) ∨
    (CFSG.StandardType.markTag lab₁ = .PSL ∧ CFSG.StandardType.markRank lab₁ = 2) := by
  obtain ⟨t₁, r₁, n₁⟩ := lab₁
  obtain ⟨t₂, r₂, n₂⟩ := lab₂
  unfold IsClsLab at h₁ h₂
  dsimp only at hl₁ hl₂ h₁ h₂ hs hr hd ⊢
  rcases h₁ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markDeg,
      LargeEvenInLambda2] at hs hr hd hl₁ hl₂ ⊢ <;>
    (try split_ifs at hs hr hd ⊢) <;> simp_all <;> omega

def IsExcLab (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twE6 ∨
    lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der

def IsChar3Lab (lab : LargeEvenLabel) : Prop := lab.tag = .B2der ∨ lab.tag = .G2der

theorem partition_lab (lab : LargeEvenLabel) :
    IsClsLab lab ∨ IsExcLab lab ∨ IsChar3Lab lab := by
  obtain ⟨tg, r, n⟩ := lab
  cases tg <;> simp [IsClsLab, IsExcLab, IsChar3Lab]

theorem labelOf_model {G : Type} [Group G] [Finite G] {K : Subgroup G}
    {lab : LargeEvenLabel}
    (h : LabelOf K lab) :
    CFSG.Open.IsQuasisimple ↥K ∧ LargeEvenInLambda2 lab ∧
      CFSG.StandardType.MarkedModel lab (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨hL, lab', hlab', hraw⟩ := CFSG.StandardType.Canonical.largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨hs, -, θ, hP, hm⟩ := hQ
  have hP' : lab' = lab := hP
  subst hP'
  exact ⟨⟨hL, (θ.isSimpleGroup_congr).2 hs⟩, hlab', CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm⟩

theorem card_of_B2der {R : Type} [Group R] (hm : CFSG.StandardType.MarkedModel ⟨.B2der, 0, 1⟩ R) :
    Nat.card R = 360 := by
  have hm' : CFSG.Blueprint.LieModel R .PSL 2 3 2 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm'.statedClassicalModel (by decide)
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  rw [Nat.card_congr e.toEquiv, CFSG.GH74.GLS.Stage4.card_statedProj_statedSL_two_of_odd hodd, hK]
  norm_num

theorem card_of_G2der {R : Type} [Group R] (hm : CFSG.StandardType.MarkedModel ⟨.G2der, 0, 1⟩ R) :
    Nat.card R = 6048 := by
  have hm' : CFSG.Blueprint.LieModel R .PSU 3 3 1 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm'.statedClassicalModel (by decide)
  have h := CFSG.Quasithin.S146zY.FiveOdd.card_statedProj_statedSU_three (K := K) (p := 3)
    (by norm_num) (by rw [hK]; norm_num)
  rw [Nat.card_congr e.toEquiv, show (3 : ℕ) ^ 1 = 3 from rfl, h]
  norm_num

theorem evenLieOrder_of_excLab {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hE : IsExcLab lab) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder (CFSG.StandardType.markTag lab)
      (CFSG.StandardType.markRank lab) (CFSG.StandardType.markDeg lab) = excOrd lab.tag lab.n := by
  obtain ⟨tg, r, n⟩ := lab
  unfold IsExcLab at hE
  dsimp only at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem excOK_of_excLab {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hE : IsExcLab lab) :
    excOK lab.tag lab.n := by
  obtain ⟨tg, r, n⟩ := lab
  unfold IsExcLab at hE
  dsimp only at hE hl ⊢
  simp only [LargeEvenInLambda2, Nat.odd_iff] at hl
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [excOK] <;> omega

theorem exc_exc_case {Q : Type} [Group Q] [Finite Q] {lab₁ lab₂ : LargeEvenLabel}
    (hl₁ : LargeEvenInLambda2 lab₁) (hl₂ : LargeEvenInLambda2 lab₂) (hE₁ : IsExcLab lab₁)
    (hE₂ : IsExcLab lab₂)
    (hM₁ : CFSG.StandardType.MarkedModel lab₁ (Q ⧸ Subgroup.center Q))
    (hM₂ : CFSG.StandardType.MarkedModel lab₂ (Q ⧸ Subgroup.center Q)) : lab₁ = lab₂ := by
  have hc₁ : CFSG.StandardType.markChar lab₁ = 2 := by
    obtain ⟨tg, r, n⟩ := lab₁
    unfold IsExcLab at hE₁
    dsimp only at hE₁
    rcases hE₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hc₂ : CFSG.StandardType.markChar lab₂ = 2 := by
    obtain ⟨tg, r, n⟩ := lab₂
    unfold IsExcLab at hE₂
    dsimp only at hE₂
    rcases hE₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  unfold CFSG.StandardType.MarkedModel at hM₁ hM₂
  rw [hc₁] at hM₁
  rw [hc₂] at hM₂
  have e₁ := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₁
  have e₂ := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hM₂
  rw [evenLieOrder_of_excLab hl₁ hE₁] at e₁
  rw [evenLieOrder_of_excLab hl₂ hE₂] at e₂
  obtain ⟨ht, hn⟩ := excOrd_inj (excOK_of_excLab hl₁ hE₁) (excOK_of_excLab hl₂ hE₂) (e₁.symm.trans e₂)
  obtain ⟨t₁, r₁, n₁⟩ := lab₁
  obtain ⟨t₂, r₂, n₂⟩ := lab₂
  have hr₁ : r₁ = 0 := by
    unfold IsExcLab at hE₁
    dsimp only at hE₁ hl₁
    simp only [LargeEvenInLambda2] at hl₁
    rcases hE₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hr₂ : r₂ = 0 := by
    unfold IsExcLab at hE₂
    dsimp only at hE₂ hl₂
    simp only [LargeEvenInLambda2] at hl₂
    rcases hE₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  dsimp only at ht hn
  subst ht hn hr₁ hr₂
  rfl

theorem markChar_two_of_not_char3 {lab : LargeEvenLabel} (h : ¬ IsChar3Lab lab) :
    CFSG.StandardType.markChar lab = 2 := by
  obtain ⟨tg, r, n⟩ := lab
  unfold IsChar3Lab at h
  dsimp only at h
  cases tg <;> simp_all [CFSG.StandardType.markChar]

theorem lieModel_of_mark_two {X : Type} [Group X] {lab : LargeEvenLabel}
    (hM : CFSG.StandardType.MarkedModel lab X) (h2 : CFSG.StandardType.markChar lab = 2) :
    CFSG.Blueprint.LieModel X (CFSG.StandardType.markTag lab) (CFSG.StandardType.markRank lab) 2
      (CFSG.StandardType.markDeg lab) := by
  have h := hM
  unfold CFSG.StandardType.MarkedModel at h
  rwa [h2] at h

theorem one_le_markDeg {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) :
    1 ≤ CFSG.StandardType.markDeg lab := by
  obtain ⟨tg, r, n⟩ := lab
  have hn : 1 ≤ n := hl.1
  cases tg <;> simp only [CFSG.StandardType.markDeg] <;> (try split_ifs) <;> omega

theorem card_center_dvd_of_model {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q)
    {t : CFSG.Open.StatedLieTag} {n p f N : ℕ}
    (hm : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) t n p f) (hN : N ≠ 0)
    (hd : CFSG.LocalAnalysis.GLTheoremA.multProd t n p f ∣ N) :
    Nat.card (Subgroup.center Q) ∣ N := by
  have hne : CFSG.LocalAnalysis.GLTheoremA.multProd t n p f ≠ 0 := fun h => hN (zero_dvd_iff.1 (h ▸ hd))
  exact (CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hQ hm rfl rfl hne).trans hd

theorem evenRank_le_three_B2der {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q)
    (hM : CFSG.StandardType.MarkedModel ⟨.B2der, 0, 1⟩ (Q ⧸ Subgroup.center Q)) :
    CFSG.Open.evenRank Q ≤ 3 := by
  have hR := card_of_B2der hM
  have hM' : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSL 2 3 2 := hM
  have hZ := card_center_dvd_of_model hGA hQ (CFSG.Models.LieModel.of_blueprint (by decide) hM')
    (by decide) (show CFSG.LocalAnalysis.GLTheoremA.multProd .PSL 2 3 2 ∣ 6 from by decide)
  have hcard : Nat.card Q ∣ 2160 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hR]
    have := mul_dvd_mul_left 360 hZ
    norm_num at this
    exact this
  exact evenRank_le_three_of_card_dvd hcard (fun p hp hp2 => not_pow_four_dvd_2160 p hp hp2)

theorem evenRank_le_three_G2der {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q)
    (hM : CFSG.StandardType.MarkedModel ⟨.G2der, 0, 1⟩ (Q ⧸ Subgroup.center Q)) :
    CFSG.Open.evenRank Q ≤ 3 := by
  have hR := card_of_G2der hM
  have hM' : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSU 3 3 1 := hM
  have hZ := card_center_dvd_of_model hGA hQ (CFSG.Models.LieModel.of_blueprint (by decide) hM')
    (by decide) (show CFSG.LocalAnalysis.GLTheoremA.multProd .PSU 3 3 1 ∣ 1 from by decide)
  have hZ1 : Nat.card (Subgroup.center Q) = 1 := Nat.dvd_one.1 hZ
  have hcard : Nat.card Q ∣ 12096 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hR, hZ1]
    norm_num
  exact evenRank_le_three_of_card_dvd hcard (fun p hp hp2 => not_pow_four_dvd_12096 p hp hp2)

theorem char3_le_three {Q : Type} [Group Q] [Finite Q]
    (hGA : CFSG.Open.GriessAllModelsStatement) (hQ : CFSG.Open.IsQuasisimple Q)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hk : IsChar3Lab lab)
    (hM : CFSG.StandardType.MarkedModel lab (Q ⧸ Subgroup.center Q)) : CFSG.Open.evenRank Q ≤ 3 := by
  obtain ⟨tg, r, n⟩ := lab
  unfold IsChar3Lab at hk
  dsimp only at hk hl
  simp only [LargeEvenInLambda2] at hl
  rcases hk with rfl | rfl
  · have hr : r = 0 := by simp_all
    have hn : n = 1 := by simp_all
    subst hr hn
    exact evenRank_le_three_B2der hGA hQ hM
  · have hr : r = 0 := by simp_all
    have hn : n = 1 := by simp_all
    subst hr hn
    exact evenRank_le_three_G2der hGA hQ hM

theorem markChar_two_of_cls {lab : LargeEvenLabel} (h : IsClsLab lab) :
    CFSG.StandardType.markChar lab = 2 := by
  obtain ⟨tg, r, n⟩ := lab
  unfold IsClsLab at h
  dsimp only at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem markChar_two_of_exc {lab : LargeEvenLabel} (h : IsExcLab lab) :
    CFSG.StandardType.markChar lab = 2 := by
  obtain ⟨tg, r, n⟩ := lab
  unfold IsExcLab at h
  dsimp only at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem cls_cls_case {Q : Type} [Group Q] [Finite Q] (hGA : CFSG.Open.GriessAllModelsStatement)
    (hQ : CFSG.Open.IsQuasisimple Q) {lab₁ lab₂ : LargeEvenLabel} (hl₁ : LargeEvenInLambda2 lab₁)
    (hl₂ : LargeEvenInLambda2 lab₂) (hc₁ : IsClsLab lab₁) (hc₂ : IsClsLab lab₂)
    (hM₁ : CFSG.StandardType.MarkedModel lab₁ (Q ⧸ Subgroup.center Q))
    (hM₂ : CFSG.StandardType.MarkedModel lab₂ (Q ⧸ Subgroup.center Q))
    (he : 4 ≤ CFSG.Open.evenRank Q) :
    lab₁ = lab₂ ∨ ((lab₁.tag = .B ∨ lab₁.tag = .C) ∧ (lab₂.tag = .B ∨ lab₂.tag = .C) ∧
      lab₁.rank = lab₂.rank ∧ lab₁.n = lab₂.n) := by
  have hM₂' := lieModel_of_mark_two hM₂ (markChar_two_of_cls hc₂)
  have hM₁' := lieModel_of_mark_two hM₁ (markChar_two_of_cls hc₁)
  obtain ⟨hs, hr, hd⟩ := cls_det hl₁ hc₁ hM₁ hM₂'
  rcases cls_pair lab₁ lab₂ hl₁ hl₂ hc₁ hc₂ hs.symm hr.symm hd.symm with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr h
  · have hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSL 4 2 (CFSG.StandardType.markDeg lab₁) := by
      rw [h1, h2] at hM₁'
      exact hM₁'
    have := evenRank_le_three_PSL_four hGA hQ (one_le_markDeg hl₁) hm
    omega
  · have hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSU 4 2 (CFSG.StandardType.markDeg lab₁) := by
      rw [h1, h2] at hM₁'
      exact hM₁'
    have := evenRank_le_three_PSU_four hGA hQ (one_le_markDeg hl₁) hm
    omega
  · have hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSL 2 2 (CFSG.StandardType.markDeg lab₁) := by
      rw [h1, h2] at hM₁'
      exact hM₁'
    have := evenRank_le_three_PSL_two hGA hQ (one_le_markDeg hl₁) hm
    omega

theorem cls_exc_contra {Q : Type} [Group Q] [Finite Q] {lab₁ lab₂ : LargeEvenLabel}
    (hl₁ : LargeEvenInLambda2 lab₁) (hc₁ : IsClsLab lab₁) (hE₂ : IsExcLab lab₂)
    (hM₁ : CFSG.StandardType.MarkedModel lab₁ (Q ⧸ Subgroup.center Q))
    (hM₂ : CFSG.StandardType.MarkedModel lab₂ (Q ⧸ Subgroup.center Q)) : False := by
  have hM₂' := lieModel_of_mark_two hM₂ (markChar_two_of_exc hE₂)
  obtain ⟨hs, -, -⟩ := cls_det hl₁ hc₁ hM₁ hM₂'
  obtain ⟨t₁, r₁, n₁⟩ := lab₁
  obtain ⟨t₂, r₂, n₂⟩ := lab₂
  unfold IsClsLab at hc₁
  unfold IsExcLab at hE₂
  dsimp only at hc₁ hE₂ hs
  rcases hc₁ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hE₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (first
      | (simp [CFSG.StandardType.markTag] at hs; done)
      | (by_cases h2 : r₁ = 2 <;> by_cases h3 : r₁ = 3 <;>
          simp [CFSG.StandardType.markTag, h2, h3] at hs <;> done))

end Cert

section Main

theorem labelUniqAt_holds (G : Type) [Group G] [Finite G] : LabelUniqAt G := by
  intro K lab₁ lab₂ he h₁ h₂
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  obtain ⟨hQ₁, hl₁, hM₁⟩ := labelOf_model h₁
  obtain ⟨hQ₂, hl₂, hM₂⟩ := labelOf_model h₂
  rcases partition_lab lab₁ with c₁ | e₁ | k₁ <;> rcases partition_lab lab₂ with c₂ | e₂ | k₂
  · exact cls_cls_case hGA hQ₁ hl₁ hl₂ c₁ c₂ hM₁ hM₂ he
  · exact (cls_exc_contra hl₁ c₁ e₂ hM₁ hM₂).elim
  · have := char3_le_three hGA hQ₂ hl₂ k₂ hM₂
    omega
  · exact (cls_exc_contra hl₂ c₂ e₁ hM₂ hM₁).elim
  · exact Or.inl (exc_exc_case hl₁ hl₂ e₁ e₂ hM₁ hM₂)
  · have := char3_le_three hGA hQ₂ hl₂ k₂ hM₂
    omega
  · have := char3_le_three hGA hQ₁ hl₁ k₁ hM₁
    omega
  · have := char3_le_three hGA hQ₁ hl₁ k₁ hM₁
    omega
  · have := char3_le_three hGA hQ₁ hl₁ k₁ hM₁
    omega


end Main

end CFSG.LocalAnalysis.GLTheoremA
