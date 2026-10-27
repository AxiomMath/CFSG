module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Z
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26RestrictPow

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4
open scoped commutatorElement

section Cit


theorem s26_l2_branch {r : ℕ} (hr : 4 ≤ r) {X : Type} [Group X] [Finite X]
    (hO : classicalInvolutionOddCore X = ⊥)
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ) {A : Subgroup X} (hA : A ∈ Φ)
    {S : Sylow 2 ↥A} {z : X} (hd : TightDatum A S z) (hz : IsUniqueInvolution A z)
    {L : Subgroup X} [L.Normal] (hLq : CFSG.IsQuasisimple ↥L)
    (hLC : Subgroup.centralizer (L : Set X) = Subgroup.center X) (hzn : z ∉ Subgroup.center X)
    (hnt : ∀ y : X, ∀ m ∈ Subgroup.center X, y * z * y⁻¹ = z * m → m = 1)
    (hL2 : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 ↥(socleOf L))
    (hTC : Subgroup.centralizer ((socleOf L : Subgroup (X ⧸ Subgroup.center X)) :
      Set (X ⧸ Subgroup.center X)) = ⊥)
    (hgen : (⨆ g : X, conjSub g A) = ⊤)
    {u b : X} (huS : u ∈ (S : Subgroup A).map A.subtype) (hbS : b ∈ (S : Subgroup A).map A.subtype)
    (hou : orderOf u = 2 ^ (r - 1)) (hbu : b * u * b⁻¹ = u⁻¹)
    (hbb : b * b = u ^ 2 ^ (r - 2)) (hzu : u ^ 2 ^ (r - 2) = z)
    (β : MulAut X) (hβu : β u = u) (hβ : β ^ 2 ^ (r - 1) = 1) :
    β ^ 2 ^ (r - 2) = 1 ∨ β ^ 2 ^ (r - 2) = MulAut.conj z := by
  classical
  obtain ⟨-, -, hdich⟩ := s26_l2_x_mem hr hO hΦ hA hd hz hzn hnt hL2 hTC huS hbS hou hbu hbb hzu
  have hZ := s26_l2_center_bot hr hO hΦ hA hd hz hLq hLC hzn hnt hL2 hTC hgen huS hbS hou hbu hbb
    hzu
  have hT : IsSimpleGroup ↥(socleOf L) := isSimpleGroup_socle hLq hLC
  have hab := exists_ne_comm_socle hLq hLC
  have hφpow : ∀ n : ℕ, Perp22Rest.quotCenterAut (β ^ n) =
      (Perp22Rest.quotCenterAut β : MulAut (X ⧸ Subgroup.center X)) ^ n := fun n =>
    MulEquiv.ext (quotCenterAut_pow β n)
  have hφ1 : Perp22Rest.quotCenterAut (1 : MulAut X) = 1 := by simpa using hφpow 0
  have hφu : Perp22Rest.quotCenterAut β (QuotientGroup.mk u) = QuotientGroup.mk u := by
    rw [Perp22Rest.quotCenterAut_mk, hβu]
  have hBcomm := TwinSocF4.restrictAut_comm_conjNormal hT hab hTC (Perp22Rest.quotCenterAut β) hφu
  have hBpow : (TwinSocF4.restrictAut hT hab hTC (Perp22Rest.quotCenterAut β)) ^ 2 ^ (r - 1) = 1 := by
    rw [← restrictAut_pow, ← hφpow, hβ, hφ1]
    exact restrictAut_one hT hab hTC
  have hlift : ∀ (γ : MulAut X) (g : X), (QuotientGroup.mk (γ g) : X ⧸ Subgroup.center X) =
      QuotientGroup.mk g → γ g = g := by
    intro γ g h
    have h1 : (γ g)⁻¹ * g ∈ Subgroup.center X := QuotientGroup.eq.mp h
    rw [hZ, Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  rcases hdich _ hBcomm hBpow with h1 | h2
  · left
    have hψ : TwinSocF4.restrictAut hT hab hTC (Perp22Rest.quotCenterAut (β ^ 2 ^ (r - 2))) = 1 := by
      rw [hφpow, restrictAut_pow]
      exact h1
    ext g
    refine hlift _ g ?_
    have := TwinSocF4.eq_self_of_restrictAut_eq_one hT hab hTC _ hψ (QuotientGroup.mk g)
    rw [Perp22Rest.quotCenterAut_mk] at this
    simpa using this
  · right
    have hψ : TwinSocF4.restrictAut hT hab hTC (Perp22Rest.quotCenterAut (β ^ 2 ^ (r - 2))) =
        MulAut.conjNormal (QuotientGroup.mk z : X ⧸ Subgroup.center X) := by
      rw [hφpow, restrictAut_pow]
      exact h2
    ext g
    have := TwinSocF4.eq_of_restrictAut_eq_conjNormal hT hab hTC _ (QuotientGroup.mk z) hψ (QuotientGroup.mk g)
    rw [Perp22Rest.quotCenterAut_mk] at this
    have h3 : (QuotientGroup.mk ((β ^ 2 ^ (r - 2)) g) : X ⧸ Subgroup.center X) =
        QuotientGroup.mk (z * g * z⁻¹) := by
      rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h4 := hlift (β ^ 2 ^ (r - 2)) g
    have h5 : (β ^ 2 ^ (r - 2)) g = z * g * z⁻¹ := by
      have h6 : ((β ^ 2 ^ (r - 2)) g)⁻¹ * (z * g * z⁻¹) ∈ Subgroup.center X := QuotientGroup.eq.mp h3
      rw [hZ, Subgroup.mem_bot] at h6
      exact inv_mul_eq_one.mp h6
    rw [h5]
    simp [MulAut.conj_apply]

end Cit

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
