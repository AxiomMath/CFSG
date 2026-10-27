module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.D4TrialityAux.Descent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem descent_mulAut_mul_conj {G : Type*} [Group G] (β : MulAut G) (x : G) :
    β * MulAut.conj x = MulAut.conj (β x) * β :=
  MulEquiv.ext fun y => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem descent_inner {G Y : Type*} [Group G] [Group Y]
    (x : MulAut G) (j : Y →* G) (hj : Function.Injective j)
    (hfixed : ∀ y, x (j y) = j y) (hrange : ∀ w, x w = w → ∃ y, j y = w)
    (φ : MulAut Y) (Θ : MulAut G) (hΘ : ∀ y, j (φ y) = Θ (j y))
    (hφ : ∀ ζ : MulAut Y, Nat.Coprime 3 (orderOf ζ) → ζ * φ = φ * ζ →
      (∀ t, φ t = t → ζ t = t) → ζ ∈ innerAut Y)
    (hZ : Subgroup.center Y = ⊥)
    (hx : FaithfulAt 3 x)
    (θ : MulAut G) (hθ3 : Nat.Coprime 3 (orderOf θ)) (hθx : θ * x = x * θ)
    (hθΘ : θ * Θ = Θ * θ) (hθfix : ∀ y, φ y = y → θ (j y) = j y) :
    θ ∈ innerAut G := by
  have hθx' : ∀ w, x (θ w) = θ (x w) := fun w => (congrArg (fun e : MulAut G => e w) hθx).symm
  have hinv : θ⁻¹ * x = x * θ⁻¹ :=
    calc θ⁻¹ * x = θ⁻¹ * (x * θ) * θ⁻¹ := by group
      _ = θ⁻¹ * (θ * x) * θ⁻¹ := by rw [hθx]
      _ = x * θ⁻¹ := by group
  have hθx'' : ∀ w, x (θ⁻¹ w) = θ⁻¹ (x w) := fun w =>
    (congrArg (fun e : MulAut G => e w) hinv).symm
  have h1 : ∀ y, ∃ y', j y' = θ (j y) := fun y => hrange _ (by rw [hθx', hfixed])
  have h2 : ∀ y, ∃ y', j y' = θ⁻¹ (j y) := fun y => hrange _ (by rw [hθx'', hfixed])
  set ζ := restrictAut j hj θ h1 h2 with hζdef
  have hζ3 : Nat.Coprime 3 (orderOf ζ) :=
    Nat.Coprime.coprime_dvd_right (restrictAut_orderOf_dvd j hj θ h1 h2) hθ3
  have hζφ : ζ * φ = φ * ζ :=
    MulEquiv.ext fun y => hj (by
      change j (ζ (φ y)) = j (φ (ζ y))
      rw [hζdef, restrictAut_spec, hΘ, hΘ, restrictAut_spec]
      exact congrArg (fun e : MulAut G => e (j y)) hθΘ)
  have hζfix : ∀ t, φ t = t → ζ t = t := fun t ht =>
    hj (by rw [hζdef, restrictAut_spec]; exact hθfix t ht)
  obtain ⟨y, hy⟩ := hφ ζ hζ3 hζφ hζfix
  have hθy : θ (j y) = j y := by
    have h := restrictAut_spec j hj θ h1 h2 y
    rw [← hζdef, ← hy] at h
    simp only [MulAut.conj_apply, mul_inv_cancel_right] at h
    exact h.symm
  have hZinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have : z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro u
      have h := congrArg (fun φ : MulAut Y => φ u) hz
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    rw [hZ] at this
    exact this
  have hordy : orderOf (MulAut.conj y : MulAut Y) = orderOf y :=
    orderOf_injective (MulAut.conj : Y →* MulAut Y) hZinj y
  have hordjy : orderOf (j y) = orderOf y := orderOf_injective j hj y
  have hc3 : Nat.Coprime 3 (orderOf (MulAut.conj (j y) : MulAut G)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hζ3
    have h1' : orderOf (MulAut.conj (j y) : MulAut G) ∣ orderOf (j y) :=
      orderOf_map_dvd (MulAut.conj : G →* MulAut G) (j y)
    rw [hordjy, ← hordy, hy] at h1'
    exact h1'
  set θ' : MulAut G := (MulAut.conj (j y) : MulAut G)⁻¹ * θ with hθ'
  have hcommθ : Commute θ (MulAut.conj (j y) : MulAut G) := by
    show θ * MulAut.conj (j y) = MulAut.conj (j y) * θ
    rw [descent_mulAut_mul_conj, hθy]
  have hcommx : Commute x (MulAut.conj (j y) : MulAut G) := by
    show x * MulAut.conj (j y) = MulAut.conj (j y) * x
    rw [descent_mulAut_mul_conj, hfixed]
  have hθ'3 : Nat.Coprime 3 (orderOf θ') := by
    have hd : orderOf θ' ∣ Nat.lcm (orderOf (MulAut.conj (j y) : MulAut G)⁻¹) (orderOf θ) :=
      hcommθ.symm.inv_left.orderOf_mul_dvd_lcm
    refine Nat.Coprime.coprime_dvd_right hd ?_
    refine Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul _ _) ?_
    rw [orderOf_inv]
    exact Nat.Coprime.mul_right hc3 hθ3
  have hθ'x : θ' * x = x * θ' := by
    have h1' : (MulAut.conj (j y) : MulAut G)⁻¹ * x = x * (MulAut.conj (j y) : MulAut G)⁻¹ :=
      (Commute.inv_right hcommx).symm.eq
    calc θ' * x = (MulAut.conj (j y) : MulAut G)⁻¹ * (θ * x) := by rw [hθ', mul_assoc]
      _ = (MulAut.conj (j y) : MulAut G)⁻¹ * (x * θ) := by rw [hθx]
      _ = ((MulAut.conj (j y) : MulAut G)⁻¹ * x) * θ := by rw [← mul_assoc]
      _ = (x * (MulAut.conj (j y) : MulAut G)⁻¹) * θ := by rw [h1']
      _ = x * θ' := by rw [hθ', mul_assoc]
  have hθ'fix : ∀ t ∈ fixSub x, θ' t = t := by
    intro w hw
    obtain ⟨t, rfl⟩ := hrange w (mem_fixSub.1 hw)
    have h := restrictAut_spec j hj θ h1 h2 t
    rw [← hζdef, ← hy] at h
    rw [hθ', MulAut.mul_apply, ← h, ← map_inv (MulAut.conj : G →* MulAut G), MulAut.conj_apply,
      MulAut.conj_apply, map_mul, map_mul, map_inv]
    group
  have hθ'1 : θ' = 1 := hx θ' hθ'3 hθ'x hθ'fix
  have : θ = MulAut.conj (j y) := by
    have h := congrArg (fun e : MulAut G => (MulAut.conj (j y) : MulAut G) * e) hθ'1
    simpa [hθ'] using h
  exact ⟨j y, this.symm⟩

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
