module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitInvolution
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitTwoRank
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Interfaces
public import CFSG.LieType.Multipliers.U43
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers.U43 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial TauCeti CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem u43_center_eq_bot : Subgroup.center X₀ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs : IsSimpleGroup X₀ := by
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F9 3 1
      (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num) 4 (by norm_num) (by norm_num)
    simpa using this
  have hfin : Finite X₀ := Nat.finite_of_card_ne_zero (by rw [card_X₀]; norm_num)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X₀) with h0 | h0
  · exact h0
  · exfalso
    have hcomm : ∀ x y : X₀, x * y = y * x := fun x y =>
      (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top y) x)
    let _ : CommGroup X₀ := { (inferInstance : Group X₀) with mul_comm := hcomm }
    have hp := IsSimpleGroup.prime_card (α := X₀)
    rw [card_X₀] at hp
    exact absurd hp (by norm_num)

theorem u43_group_equiv {q : PrimePower} (hv : (LieTypeIndex.twistedA 3 q).Valid)
    (h3 : q.card = 3) : Nonempty ((CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group ≃* X₀) := by
  have hp : q.p.Prime := q.prime_p
  have hcard : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hp3 : q.p = 3 := by
    have h1 : q.p ∣ 3 := by
      rw [← h3, hcard]; exact dvd_pow_self _ q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1
  have he1 : q.exponent = 1 := by
    have h1 : 3 ^ q.exponent = 3 ^ 1 := by rw [← hp3, ← hcard, h3, hp3]; rfl
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
    (G := (CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) (MulEquiv.refl _)
  rw [hp3, he1] at hc
  exact nonempty_mulEquiv_X₀ (Or.inl ⟨by decide, hc⟩)

section Transport

variable {P Y : Type} [Group P] [Group Y]

theorem hgen_transport (φ : P ≃* Y)
    (H : ∀ α : MulAut P, α * α = 1 → α ≠ 1 → ∃ (x y : Fin 2 → P) (z : P),
      HeisCfg 3 2 x y z ∧ (∀ i, y i ^ 3 = 1) ∧ α (x 0) = (x 0)⁻¹) :
    ∀ ψ : MulAut Y, ψ * ψ = 1 → ψ ≠ 1 → ∃ (x y : Fin 2 → Y) (z : Y),
      HeisCfg 3 2 x y z ∧ (∀ i, y i ^ 3 = 1) ∧ ψ (x 0) = (x 0)⁻¹ := by
  intro ψ h2 h1
  have e1 : (MulAut.congr φ).symm ψ * (MulAut.congr φ).symm ψ = 1 := by
    rw [← map_mul, h2, map_one]
  have e2 : (MulAut.congr φ).symm ψ ≠ 1 := fun h => h1 ((MulEquiv.map_eq_one_iff (MulAut.congr φ).symm).1 h)
  obtain ⟨x, y, z, hc, hy, hx⟩ := H _ e1 e2
  refine ⟨fun i => φ (x i), fun i => φ (y i), φ z, hc.map φ.toMonoidHom ?_, fun i => ?_, ?_⟩
  · simp [hc.z1]
  · rw [← map_pow, hy i, map_one]
  · have hψ : ∀ a, ψ (φ a) = φ (((MulAut.congr φ).symm ψ) a) := fun a => by
      have := congrArg (fun f : MulAut Y => f (φ a)) ((MulAut.congr φ).apply_symm_apply ψ).symm
      simpa using this
    rw [hψ, hx, map_inv]

theorem autTwoRankLE_transport (φ : P ≃* Y) {m : ℕ} (H : AutTwoRankLE P m) : AutTwoRankLE Y m := by
  intro B hc hs
  let B' : Subgroup (MulAut P) := B.map (MulAut.congr φ).symm.toMonoidHom
  have hB' : Nat.card B' = Nat.card B :=
    (Nat.card_congr (B.equivMapOfInjective _ (MulAut.congr φ).symm.injective).toEquiv).symm
  rw [← hB']
  refine H B' ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg _ (hc x hx y hy)
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [hs x hx, map_one]

end Transport

theorem F9_unitaryData : UnitaryFieldData 3 1 F9 :=
  ⟨Nat.prime_three, le_rfl, by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num⟩

theorem hypPSU_equiv_X₀ : Nonempty (hypPSU F9_unitaryData 2 0 ≃* X₀) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 0) F9_unitaryData
  exact ⟨hypPSUEquivStatedProj F9_unitaryData hR (by norm_num)⟩

theorem u43_hgen : ∀ ψ : MulAut X₀, ψ * ψ = 1 → ψ ≠ 1 → ∃ (x y : Fin 2 → X₀) (z : X₀),
    HeisCfg 3 2 x y z ∧ (∀ i, y i ^ 3 = 1) ∧ ψ (x 0) = (x 0)⁻¹ := by
  obtain ⟨φ⟩ := hypPSU_equiv_X₀
  exact hgen_transport φ fun α h2 h1 => exists_heis_of_involution_hyp F9_unitaryData α h2 h1

theorem u43_autTwoRankLE : AutTwoRankLE X₀ 5 := by
  obtain ⟨φ⟩ := hypPSU_equiv_X₀
  exact autTwoRankLE_transport φ fun B hc hs => two_rank_hypPSU_le F9_unitaryData B hc hs

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
