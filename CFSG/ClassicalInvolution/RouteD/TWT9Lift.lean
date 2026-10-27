module

public import CFSG.ClassicalInvolution.RouteD.TWT8Lift
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLift

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWT8
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}


theorem exists_spin_twin_pair_td4 (hodd : Odd (Nat.card K)) (hQ : Q.Nondegenerate)
    (F₀ : HypFrame Q 3) (hdim : 7 ≤ Module.finrank K V) (FM : OFrame Q) :
    ∃ x : spinGroup Q,
      FM.La.range = ((rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true true).map
        (MulAut.conj x).toMonoidHom).map (spinAction Q) ∧
      FM.swap.La.range = ((rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom).map (spinAction Q) := by
  classical
  have : Invertible (2 : K) := invertibleOfNonzero (IsFundamental.two_ne_zero_of_odd hodd)
  have hQ' : (polarBilin Q).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  let p₀ : ℕ → HypPair Q := fun k => if k = 0 then FM.P else FM.P'
  have ho₀ : ∀ a b, a < 2 → b < 2 → a ≠ b → (p₀ a).Orth (p₀ b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;> simp_all [p₀, FM.orth, FM.orth.symm]
  obtain ⟨p', hp', ho'⟩ := exists_orth_ext hodd hQ' p₀ 2 ho₀ 1 (by omega)
  have hp'0 : p' 0 = FM.P := by rw [hp' 0 (by omega)]; simp [p₀]
  have hp'1 : p' 1 = FM.P' := by rw [hp' 1 (by omega)]; simp [p₀]
  have o20 : (p' 2).Orth FM.P := by
    rw [← hp'0]; exact ho' 2 0 (by omega) (by omega) (by omega)
  have o21 : (p' 2).Orth FM.P' := by
    rw [← hp'1]; exact ho' 2 1 (by omega) (by omega) (by omega)
  have oFM : FM.P.Orth FM.P' := FM.orth
  let Pn : ℕ → HypPair Q := fun k => if k = 0 then p' 2 else if k = 1 then FM.P else FM.P'
  have hPn : ∀ a b, a < 3 → b < 3 → a ≠ b → (Pn a).Orth (Pn b) := by
    intro a b ha hb hab
    interval_cases a <;> interval_cases b <;>
      first
      | exact absurd rfl hab
      | simp [Pn, o20, o20.symm, o21, o21.symm, oFM, oFM.symm]
  let P : Fin 3 → HypPair Q := fun i => Pn i.val
  have hPo : ∀ i j : Fin 3, i ≠ j → (P i).Orth (P j) := fun i j hij =>
    hPn i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h))
  obtain ⟨x, hx1, -⟩ := exists_spin_family hodd hQ F₀ hPo (⟨0, by omega⟩ : Fin 3)
  have hPn1 : Pn 1 = FM.P := by simp [Pn]
  have hPn2 : Pn 2 = FM.P' := by simp [Pn]
  have hP1 : FM.P.e = spinAction Q x (F₀.vec ⟨1, by omega⟩ true) ∧
      FM.P.f = spinAction Q x (F₀.vec ⟨1, by omega⟩ false) := by
    have := hx1 ⟨1, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    rw [show P ⟨1, by omega⟩ = FM.P from hPn1] at this
    exact this
  have hP2 : FM.P'.e = spinAction Q x (F₀.vec ⟨2, by omega⟩ true) ∧
      FM.P'.f = spinAction Q x (F₀.vec ⟨2, by omega⟩ false) := by
    have := hx1 ⟨2, by omega⟩ (fun h => by have := congrArg Fin.val h; simp at this)
    rw [show P ⟨2, by omega⟩ = FM.P' from hPn2] at this
    exact this
  refine ⟨x, ?_, ?_⟩
  · exact La_range_eq_of_pairs F₀ (a := 1) (b := 2) (by omega) (by omega) (by omega) true true x
      FM.orth hP1 hP2
  · exact La_range_eq_of_pairs F₀ (a := 1) (b := 2) (by omega) (by omega) (by omega) true false x
      (orth_swapPair FM.orth) hP1 ⟨hP2.2, hP2.1⟩

end Model

section Rec

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B4 CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

variable {p f : ℕ} [Fact p.Prime]


theorem lift_td4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    (θ : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {RM RM' : Subgroup (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2))}
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr p f)))
    (hRM'f : RM' ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr p f)))
    (hne : RM' ≠ RM)
    (htwin : ∀ i j, IsFundamental (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) (RM.map (spinAction (quadMinus 4 (GaloisField p f)
          (minusCoeffs p f).1 (minusCoeffs p f).2))) i →
      IsFundamental (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
        (RM'.map (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2))) j → i = j)
    (hfixM : ∀ y ∈ RM, σ (θ y) = θ y) (hfixM' : ∀ y ∈ RM', σ (θ y) = θ y) :
    ∃ (x : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
      (α : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) ≃*
        spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
      (g₀ : Vm 4 (GaloisField p f) ≃ₗ[GaloisField p f] Vm 4 (GaloisField p f)),
      RM = ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 1 2
        (by omega) (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      RM' = ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 1 2
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, θ (α y) = σ (θ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2) ∧ g₀ * g₀ = 1 ∧
      (∀ y z, spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) (α y) (g₀ z) =
        g₀ (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) y z)) ∧
      (∀ a : Fin (4 - 1), 1 ≤ a.val → ∀ s,
        g₀ (spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2) x ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).vec a s)) =
        spinAction (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) x
          ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).vec a s)) := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr hf0
  have hadm : StatedLieAdmissible .POmegaMinus 4 p f := ⟨Fact.out, hf, by show 4 ≤ 4; omega⟩
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := Exotic.centralQuot_minus hp2 hq hadm
  have hq4 : 4 ≤ p ^ f := by omega
  have hirr := minusCoeffs_irr p f
  have hdim : 7 ≤ Module.finrank (GaloisField p f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p f) := by
    rw [finrank_minus p f 4 (by omega)]
    omega
  have hQ : (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite 4 (GaloisField p f) hirr)
  set F₀ : HypFrame (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)
      (4 - 1) := (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame with hF₀
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRMf
  obtain ⟨FM, hFM, hiMe⟩ := hiM
  obtain ⟨x, hx1, hx2⟩ := exists_spin_twin_pair_td4 hodd hQ F₀ hdim FM
  have hRM : RM = ((rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true true).map
      (MulAut.conj x).toMonoidHom) :=
    cq.map_inj hRMf (rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ true true x) (by rw [hFM, hx1])
  obtain ⟨iM', hiM'⟩ := cq.map_mem _ hRM'f
  obtain ⟨FM', hFM', hiM'e⟩ := hiM'
  have hii : FM'.La (-1) = FM.La (-1) := by
    have := htwin iM iM' ⟨FM, hFM, hiMe⟩ ⟨FM', hFM', hiM'e⟩
    rw [← hiMe, ← hiM'e]
    exact this.symm
  have hRM' : RM' = ((rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true false).map
      (MulAut.conj x).toMonoidHom) := by
    rcases Frame.La_range_eq_or_eq_swap h2 hii with h | h
    · exact absurd (cq.map_inj hRM'f hRMf (by rw [hFM', h, hFM])) hne
    · exact cq.map_inj hRM'f (rootSL2_conj_mem_gen hq4 cq F₀ _ _ _ true false x)
        (by rw [hFM', h, hx2])
  obtain ⟨α, g, hαθ, hα⟩ := exists_isConj_lift_minus hp2 (by norm_num : 4 ≤ 4) hf hK hirr θ hker σ
    hσ2 hσr
  have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := isPerfect_spinGroup_quadMinus (by norm_num : 4 ≤ 4) hirr
  have hα2 : ∀ y, α (α y) = y := by
    have key := eq_of_inv_mul_mem_center ((α : spinGroup (quadMinus 4 (GaloisField p f)
      (minusCoeffs p f).1 (minusCoeffs p f).2) →* _).comp
      (α : spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2) →* _))
      (MonoidHom.id (spinGroup (quadMinus 4 (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2))) (fun x => by
      apply hker
      rw [MonoidHom.mem_ker]
      change θ (x⁻¹ * α (α x)) = 1
      rw [map_mul, map_inv, hαθ, hαθ, hσ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hαM : ∀ r ∈ RM, α r = r :=
    eq_of_fixed_of_perfect θ hker α σ hαθ (cq.perf _ hRMf) hfixM
  have hαM' : ∀ r ∈ RM', α r = r :=
    eq_of_fixed_of_perfect θ hker α σ hαθ (cq.perf _ hRM'f) hfixM'
  let i2 : Fin (4 - 1) := ⟨1, by omega⟩
  let i3 : Fin (4 - 1) := ⟨2, by omega⟩
  have h23 : i2 ≠ i3 := fun h => by have := congrArg Fin.val h; simp [i2, i3] at this
  have h32 : i3 ≠ i2 := h23.symm
  have hmem : ∀ (s t : Bool) (c : GaloisField p f), ∃ t' : Bool,
      F₀.longRoot h23 s t (.ofAdd c) ∈
        rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true t' := by
    intro s t c
    cases s
    · refine ⟨!t, ?_⟩
      rw [F₀.longRoot_swap h23 false t c]
      have e : F₀.longRoot h23.symm t false (.ofAdd (-c)) =
          F₀.longSL2 h23 true (!t) (lowerSL2 (-c)) := by
        rw [HypFrame.longSL2_lowerSL2]
        simp
      show _ ∈ (F₀.longSL2 h23 true (!t)).range
      rw [e]
      exact ⟨_, rfl⟩
    · refine ⟨t, ?_⟩
      show _ ∈ (F₀.longSL2 h23 true t).range
      rw [← HypFrame.longSL2_upperSL2]
      exact ⟨_, rfl⟩
  have hfix23 : ∀ (s t : Bool) (c : GaloisField p f),
      conjTwist α x (F₀.longRoot h23 s t (.ofAdd c)) = F₀.longRoot h23 s t (.ofAdd c) := by
    intro s t c
    obtain ⟨t', ht'⟩ := hmem s t c
    have hy : x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹ ∈
        (rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true t').map
          (MulAut.conj x).toMonoidHom := ⟨_, ht', rfl⟩
    have hα' : α (x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹) =
        x * F₀.longRoot h23 s t (.ofAdd c) * x⁻¹ := by
      cases t'
      · rw [← hRM'] at hy
        exact hαM' _ hy
      · rw [← hRM] at hy
        exact hαM _ hy
    rw [conjTwist_apply, hα']
    group
  have hO : ∀ (a b : Fin (4 - 1)) (hab : a ≠ b), (fun a : Fin (4 - 1) => 1 ≤ a.val) a →
      (fun a : Fin (4 - 1) => 1 ≤ a.val) b → ∀ (s t : Bool) (c : GaloisField p f),
      conjTwist α x ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hab s t
        (.ofAdd c)) =
        (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hab s t (.ofAdd c) := by
    intro a b hab ha hb s t c
    have ha' : a = i2 ∨ a = i3 := by
      have ha2 : 1 ≤ a.val := ha
      have ha3 := a.isLt
      rcases (by omega : a.val = 1 ∨ a.val = 2) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    have hb' : b = i2 ∨ b = i3 := by
      have hb2 : 1 ≤ b.val := hb
      have hb3 := b.isLt
      rcases (by omega : b.val = 1 ∨ b.val = 2) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hab
    · exact hfix23 s t c
    · rw [show (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).longRoot hab s t
          (.ofAdd c) = F₀.longRoot hab s t (.ofAdd c) from rfl, F₀.longRoot_swap h32 s t c]
      exact hfix23 t s (-c)
    · exact absurd rfl hab
  have hA1 : ∀ c, conjTwist α x (F₀.longRoot h23 true true (.ofAdd c)) =
      F₀.longRoot h23 true true (.ofAdd c) := fun c => hfix23 true true c
  have hφ : ∀ c, g.φ c = c := fun c => (hα.conjSpin x).phi_eq_of_fix F₀ h23 true true hA1 c
  obtain ⟨g₀, hg₀O, hg₀2, hconj, hfixv⟩ := exists_lift_of_scalar_minus hirr hα hα2 x
    (O := fun a : Fin (4 - 1) => 1 ≤ a.val) (a₁ := i2) (a₂ := i3) (by simp [i2]) (by simp [i3])
    h23 hφ hO
  exact ⟨x, α, g₀, hRM, hRM', hαθ, hg₀O, hg₀2, hconj, fun a ha s => hfixv a ha s⟩

end Rec

end CFSG.ClassicalInvolution.RouteD.TWT9
