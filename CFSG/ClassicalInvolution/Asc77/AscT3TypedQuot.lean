module

public import CFSG.ClassicalInvolution.Asc77.AscT3Conj
public import CFSG.ClassicalInvolution.Asc77.AscT3Stmt
public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import CFSG.ClassicalInvolution.Asc77.AscQuot614

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
open scoped commutatorElement

structure QuotViol {X : Type} [Group X] (Φ : Set (Subgroup X)) (K J : Subgroup X) (z j a : X) :
    Prop where
  mem_left : K ∈ Φ
  mem_right : J ∈ Φ
  hz : IsUniqueInvolution K z
  hj : IsUniqueInvolution J j
  ne : z ≠ j
  comm : z * j = j * z
  star : J ∈ omegaStarNbr Φ K
  ha : a ∈ pairNormalizers K J z j
  haj : a * j * a⁻¹ = z
  hne : conjSub a J ≠ K

section Group

variable {Y : Type} [Group Y] [Finite Y] {p f : ℕ} [Fact p.Prime] {Λ : Set (Subgroup Y)}

theorem eq_one_of_mul_self_of_mem_odd {N : Subgroup Y} (hN : Odd (Nat.card N)) {x : Y}
    (hx : x ∈ N) (hsq : x * x = 1) : x = 1 := by
  by_contra h1
  exact h1 (eq_one_of_isPGroup_of_mem_odd hN hx (isPGroup_zpowers_of_mul_self_eq_one hsq h1))

theorem eq_of_map_eq_of_commute {N : Subgroup Y} [N.Normal] (hN : Odd (Nat.card N)) {x y : Y}
    (hx : x * x = 1) (hy : y * y = 1) (hc : x * y = y * x)
    (h : QuotientGroup.mk' N x = QuotientGroup.mk' N y) : x = y := by
  have h1 : x * y ∈ N := by
    have : QuotientGroup.mk' N (x * y) = 1 := by
      rw [map_mul, h, ← map_mul, hy, map_one]
    exact (QuotientGroup.eq_one_iff _).mp this
  have h2 : (x * y) * (x * y) = 1 := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  have h3 : x * y = 1 := eq_one_of_mul_self_of_mem_odd hN h1 h2
  rw [eq_inv_of_mul_eq_one_right h3]
  exact (inv_eq_of_mul_eq_one_right hx).symm

theorem eq_of_map_eq_of_twin (hΛ : HypOmegaMod p f Λ) {K K' : Subgroup Y} (hK : K ∈ Λ)
    (hK' : K' ∈ Λ) {z : Y} (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z)
    (h : K.map (oddQuot Y) = K'.map (oddQuot Y)) : K = K' := by
  by_contra hne
  set π := oddQuot Y with hπ
  have hc := hΛ.comm_le_oddCore_of_twin hK hK' hne hz hz'
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (hΛ.isPerfect hK)
  have h1 : K.map π ≤ (oddCoreOf K).map π := by
    calc K.map π = (⁅K, K⁆).map π := by rw [hperf]
      _ = ⁅K.map π, K.map π⁆ := Subgroup.map_commutator _ _ _
      _ = ⁅K.map π, K'.map π⁆ := by rw [← h]
      _ = (⁅K, K'⁆).map π := (Subgroup.map_commutator _ _ _).symm
      _ ≤ (oddCoreOf K).map π := Subgroup.map_mono (hc.trans inf_le_left)
  have hzbar := isUniqueInvolution_map_mk_of_odd
    (X := classicalInvolutionOddCore Y) (odd_natCard_oddCore_inf K) hz
  have hzmem : π z ∈ (oddCoreOf K).map π := h1 ⟨z, hz.mem, rfl⟩
  have hodd : Odd (Nat.card ↥((oddCoreOf K).map π)) :=
    (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_map_dvd _ _)
  have hord : orderOf (π z) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzbar.sq) hzbar.ne_one
  have h2 : 2 ∣ Nat.card ↥((oddCoreOf K).map π) := by
    have := Subgroup.orderOf_dvd_natCard ((oddCoreOf K).map π) hzmem
    rwa [hord] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

omit [Finite Y] in
theorem map_pairNormalizers_le {Q : Type} [Group Q] (π : Y →* Q) (K J : Subgroup Y) (zK zJ : Y) :
    (pairNormalizers K J zK zJ).map π ≤
      pairNormalizers (K.map π) (J.map π) (π zK) (π zJ) := by
  have hZ : (Subgroup.closure ({zK, zJ} : Set Y)).map π =
      Subgroup.closure ({π zK, π zJ} : Set Q) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have key : ∀ A : Subgroup Y, (A ⊓ Subgroup.normalizer
      ((Subgroup.closure ({zK, zJ} : Set Y) : Subgroup Y) : Set Y)).map π ≤
      A.map π ⊓ Subgroup.normalizer ((Subgroup.closure ({π zK, π zJ} : Set Q) : Subgroup Q) :
        Set Q) := by
    intro A
    refine (Subgroup.map_inf_le _ _ π).trans (inf_le_inf_left _ ?_)
    rw [← hZ]
    exact Subgroup.le_normalizer_map π
  unfold pairNormalizers
  rw [Subgroup.map_sup]
  exact sup_le_sup (key K) (key J)

theorem quotViol_of_aViol (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΛ : HypOmegaMod p f Λ)
    {K J : Subgroup Y} {zK zJ : Y} (hK : K ∈ Λ) (hv : AViol Λ K J zK zJ) :
    ∃ a : Y, QuotViol (oddQuotientFamily Λ) (K.map (oddQuot Y)) (J.map (oddQuot Y))
      (oddQuot Y zK) (oddQuot Y zJ) (oddQuot Y a) := by
  set π := oddQuot Y with hπ
  have hN : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card Y
  obtain ⟨a, ha, haj, hΛ', hz', hne⟩ := hv.exists_twin (l6_2 p f) hp hq hΛ hK
  have hzKbar := isUniqueInvolution_map_mk_of_odd
    (X := classicalInvolutionOddCore Y) (odd_natCard_oddCore_inf K) hv.hzK
  have hzJbar := isUniqueInvolution_map_mk_of_odd
    (X := classicalInvolutionOddCore Y) (odd_natCard_oddCore_inf J) hv.hzJ
  have hcomm : zK * zJ = zJ * zK := hv.comm hp hΛ
  have hzne : π zK ≠ π zJ := fun h =>
    hv.ne_involution hΛ hK
      (eq_of_map_eq_of_commute hN hv.hzK.sq hv.hzJ.sq hcomm h).symm
  have hKJ : J.map π ≠ K.map π := fun h => hzne (hzKbar.eq (h ▸ hzJbar))
  refine ⟨a, ⟨mem_oddQuotientFamily hK, mem_oddQuotientFamily hv.mem, hzKbar, hzJbar, hzne, ?_,
    omegaStarNbr_map_quot hv.star hKJ, map_pairNormalizers_le π K J zK zJ ⟨a, ha, rfl⟩, ?_,
    ?_⟩⟩
  · rw [← map_mul, ← map_mul, hcomm]
  · rw [← map_mul, ← map_inv, ← map_mul, haj]
  · intro hcon
    refine hne (eq_of_map_eq_of_twin hΛ hΛ' hK hz' hv.hzK ?_)
    rw [AscQuot.map_conjSub]
    exact hcon

end Group

end CFSG.ClassicalInvolution.Asc77.T3Typed
