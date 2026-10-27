module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.Bridge.LySurj
public import Certificates.Certificate129001
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Blueprint
open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
  CFSG.Sporadic.He.Native

@[expose] noncomputable def lyDihCJ : J :=
  evalWord seedFam lyDihWord

theorem lyDih_parts :
    (mulM 5 111 (lyDihC ()) (lyDihCi ()) == idM 111) = true ∧
      (powM 5 111 (lyDihP ()) 37 == idM 111) = true ∧ diffMod5 (lyDihP ()) (idM 111) = true := by
  have h := Certificates.certificate129001
  unfold lyDihCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem repM_lyDihC : RepM (lyDihC ()) lyDihCJ :=
  repM_evalWordM repM_seedM repM_seedMInv lyDihWord

theorem repM_lyDihCi :
    RepM (lyDihCi ()) lyDihCJ⁻¹ :=
  repM_lyDihC.inv_of_check (beq_iff_eq.1 lyDih_parts.1)

theorem repM_lyDihP :
    RepM (lyDihP ()) (a * (lyDihCJ * a * lyDihCJ⁻¹)) :=
  repM_matA.mul ((repM_lyDihC.mul repM_matA).mul repM_lyDihCi)

theorem orderOf_lyDih :
    orderOf (a * (lyDihCJ * a * lyDihCJ⁻¹)) = 37 := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  have hpow : RepM (powM 5 111 (lyDihP ()) 37) ((a * (lyDihCJ * a * lyDihCJ⁻¹)) ^ 37) := by
    have h := repM_lyDihP
    unfold RepM at h ⊢
    rw [toMat_powM, h, mat_pow']
  rw [beq_iff_eq.1 lyDih_parts.2.1] at hpow
  refine orderOf_eq_prime (hpow.unique repM_id) fun h1 => ?_
  apply toMat_ne_of_diffMod5 lyDih_parts.2.2
  rw [show toMat 5 111 (lyDihP ()) = mat _ from repM_lyDihP, h1,
    show toMat 5 111 (idM 111) = mat 1 from repM_id]

theorem orderOf_a_eq_two :
    orderOf a = 2 := by
  have h2 : a ^ 2 = 1 := by
    rw [sq]
    calc a * a = a * a⁻¹ := by rw [a_inv']
      _ = 1 := mul_inv_cancel a
  refine orderOf_eq_prime h2 fun h1 => ?_
  have h := orderOf_lyDih
  rw [h1, one_mul, mul_one, mul_inv_cancel, orderOf_one] at h
  exact absurd h (by norm_num)

theorem ly_dihedral :
    ∀ t : NativeSporadic.Ly, t * t = 1 → t ≠ 1 →
      ∃ c : NativeSporadic.Ly, orderOf (t * (c * t * c⁻¹)) = 37 := by
  intro t ht2 ht1
  set t₀ : NativeSporadic.Ly := lyEquivJ.symm a with ht₀
  set c₀ : NativeSporadic.Ly := lyEquivJ.symm lyDihCJ with hc₀
  have h₀ : orderOf (t₀ * (c₀ * t₀ * c₀⁻¹)) = 37 := by
    rw [ht₀, hc₀, ← map_inv, ← map_mul, ← map_mul, ← map_mul, MulEquiv.orderOf_eq, orderOf_lyDih]
  have ht₀2 : orderOf t₀ = 2 := by rw [ht₀, MulEquiv.orderOf_eq, orderOf_a_eq_two]
  have ht2' : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨h, hh⟩ := isConj_iff.1
    (CFSG.Sporadic.Recognition.LyonsSims.ly_isConj_of_involutions ht₀2 ht2')
  refine ⟨h * c₀ * h⁻¹, ?_⟩
  have e : t * ((h * c₀ * h⁻¹) * t * (h * c₀ * h⁻¹)⁻¹) =
      MulAut.conj h (t₀ * (c₀ * t₀ * c₀⁻¹)) := by
    rw [MulAut.conj_apply, ← hh]
    group
  rw [e, MulEquiv.orderOf_eq, h₀]

theorem ly_autInner :
    ∀ φ : NativeSporadic.Ly ≃* NativeSporadic.Ly, ∃ s : NativeSporadic.Ly,
      ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  have htop := CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput
  have h : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
    rw [htop]; trivial
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun x => by rw [← hs, MulAut.conj_apply]⟩

theorem ly_elemAbelian_le :
    ∀ B : Subgroup NativeSporadic.Ly, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 8 := by
  intro B _ hB
  have : Finite NativeSporadic.Ly := Nat.finite_of_card_ne_zero (by rw [card_Ly]; norm_num)
  exact QuasithinUnique.Setup.X1.card_le_of_exponent_two (a := 8)
    (m := 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67) (card_Ly.trans (by norm_num)) (by decide) B hB

theorem sporadicExclusion_Ly :
    QuasithinUnique.Setup.X1.SporadicExclusion .Ly := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact QuasithinUnique.Setup.X1.exclusion_of_autInner hW hq.1 hirr hE hEne hEel e ly_autInner
    (r := 8) (ρ := 18) (by norm_num) ly_elemAbelian_le
    (QuasithinUnique.Setup.X1.rank_of_dihedral hW hirr e (ρ := 18) (p := 37) (by norm_num)
      (by rw [QuasithinUnique.Setup.X1.orderOf_two_zmod_37]; norm_num) ly_dihedral)

theorem noIrrFFOffender_Ly :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Ly).Group :=
  Proving.noIrrFFOffender_of_exclusion sporadicExclusion_Ly CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_Ly :
    GF2NoFFSporadicFor .Ly :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Ly

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
