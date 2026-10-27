module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightCoordinates

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

theorem split_eight_linear_three_extension_outside_involution_four_centralizers
    {Y : Type*} [Group Y] [Finite Y] {U : Subgroup Y} [U.Normal] [IsElementaryAbelian 2 U]
    (hU8 : Nat.card U = 8) (hcent : Subgroup.centralizer (U : Set Y) = U)
    (hfull : ∀ σ : MulAut U, ∃ y : Y, ∀ x : U, ((σ x : U) : Y) = y * x * y⁻¹)
    (hsplit : ∃ K : Subgroup Y, U ⊓ K = ⊥ ∧ U ⊔ K = ⊤) :
    ∀ x : Y, orderOf x = 2 → x ∉ U → ∃ y : Y, orderOf y = 4 ∧ Commute x y := by
  classical
  obtain ⟨K, hUK, hUKsup⟩ := hsplit
  let ρ : Y →* MulAut U := MulAut.conjNormal
  have hρ : ∀ (g : Y) (z : U), ((ρ g z : U) : Y) = g * z * g⁻¹ := fun g z =>
    MulAut.conjNormal_apply g z
  have hρker : ∀ g : Y, ρ g = 1 ↔ g ∈ U := by
    intro g
    have hmemc : g ∈ U ↔ g ∈ Subgroup.centralizer (U : Set Y) := by rw [hcent]
    rw [hmemc, Subgroup.mem_centralizer_iff]
    constructor
    · intro h z hz
      have h2 := congrArg (fun σ : MulAut U => ((σ ⟨z, hz⟩ : U) : Y)) h
      simp only [hρ, MulAut.one_apply] at h2
      calc z * g = g * z * g⁻¹ * g := by rw [h2]
        _ = g * z := by group
    · intro h
      apply MulEquiv.ext
      intro z
      apply Subtype.ext
      rw [hρ, MulAut.one_apply, ← h z z.2, mul_inv_cancel_right]
  have hdec : ∀ g : Y, ∃ w ∈ U, ∃ k ∈ K, w * k = g := fun g =>
    Subgroup.mem_sup_of_normal_left.mp (by rw [hUKsup]; exact Subgroup.mem_top g)
  have hρKinj : ∀ k ∈ K, ∀ k' ∈ K, ρ k = ρ k' → k = k' := by
    intro k hk k' hk' h
    have hmem : k'⁻¹ * k ∈ U := (hρker _).mp (by rw [map_mul, map_inv, h, inv_mul_cancel])
    have hone := Subgroup.disjoint_def.mp (disjoint_iff.mpr hUK) hmem (K.mul_mem (K.inv_mem hk') hk)
    exact (inv_mul_eq_one.mp hone).symm
  have hρKsurj : ∀ σ : MulAut U, ∃ k ∈ K, ρ k = σ := by
    intro σ
    obtain ⟨g, hg⟩ := hfull σ
    obtain ⟨w, hw, k, hk, rfl⟩ := hdec g
    refine ⟨k, hk, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hρ, hg z]
    have hwz : w * z = z * w := by
      have := congrArg Subtype.val (mul_comm_of_isElementaryAbelian (⟨w, hw⟩ : U) z)
      simpa using this
    calc k * (z : Y) * k⁻¹ = w * (k * z * k⁻¹) * w⁻¹ := by
          have hkz : k * (z : Y) * k⁻¹ ∈ U := (inferInstance : U.Normal).conj_mem _ z.2 k
          have := congrArg Subtype.val (mul_comm_of_isElementaryAbelian (⟨w, hw⟩ : U)
            ⟨_, hkz⟩)
          simp only [Subgroup.coe_mul] at this
          rw [this, mul_inv_cancel_right]
      _ = w * k * z * (w * k)⁻¹ := by group
  intro x hx2 hxU
  obtain ⟨w, hw, k, hk, rfl⟩ := hdec x
  set a := ρ k with ha_def
  have hρx : ρ (w * k) = a := by rw [map_mul, (hρker w).mpr hw, one_mul]
  have hxx : w * k * (w * k) = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => hxU ((hρker _).mp (hρx.trans h))
  have ha2 : a * a = 1 := by rw [← hρx, ← map_mul, hxx, map_one]
  have hk2 : k * k = 1 :=
    hρKinj _ (K.mul_mem hk hk) _ K.one_mem (by rw [map_mul, map_one]; exact ha2)
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have hwfix : a ⟨w, hw⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [ha_def, hρ, hkinv]
    have h1 : w * (k * w * k) = 1 := by rw [← hxx]; group
    have hw2 : w * w = 1 := by
      have := congrArg Subtype.val (show (⟨w, hw⟩ : U) * ⟨w, hw⟩ = 1 by
        rw [← pow_two]; exact sq_eq_one_of_isElementaryAbelian _)
      simpa using this
    calc k * w * k = w * (w * (k * w * k)) := by rw [← mul_assoc, hw2, one_mul]
      _ = w := by rw [h1, mul_one]
  obtain ⟨e, he, hae0, hae1, hae2⟩ := exists_transvection_basis hU8 ha1 ha2
  set ι := coordEquiv he hU8 with hι
  have hι_single : ∀ i, ι.symm (e i) = Multiplicative.ofAdd (Pi.single i 1) := fun i => by
    rw [MulEquiv.symm_apply_eq, hι, coordEquiv_single]
  have ha : a = MulAut.congr ι coordsS := by
    refine mulAut_ext_of_independent he hU8 fun i => ?_
    show a (e i) = ι (coordsS (ι.symm (e i)))
    rw [hι_single]
    fin_cases i <;>
      simp [hae0, hae1, hae2, hι, coordEquiv_apply, coordHom_apply, coordsS, coordsInvolution]
  have ha_apply : ∀ z, a z = ι (coordsS (ι.symm z)) := fun z => by rw [ha]; rfl
  set b : MulAut U := MulAut.congr ι coordsB with hb_def
  have hb_apply : ∀ z, b z = ι (coordsB (ι.symm z)) := fun z => rfl
  have hb2 : b * b = a := by
    rw [ha, hb_def, ← map_mul, coordsB_mul_self]
  obtain ⟨k', hk', hk'b⟩ := hρKsurj b
  have hk'2 : k' * k' = k :=
    hρKinj _ (K.mul_mem hk' hk') _ hk (by rw [map_mul, hk'b, hb2])
  obtain ⟨v, hv⟩ := ι.surjective ⟨w, hw⟩
  have hvfix : coordsS v = v := by
    apply ι.injective
    have h := hwfix
    rw [← hv, ha_apply, MulEquiv.symm_apply_apply] at h
    exact h
  set w' : U := ι (coordsCorrection v) with hw'_def
  have hkey : (⟨w, hw⟩ : U) * a w' = w' * b ⟨w, hw⟩ := by
    rw [ha_apply, hb_apply, ← hv, hw'_def, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply,
      ← map_mul, ← map_mul, coordsCorrection_spec v hvfix]
  have hconj_a : ∀ z : U, k * (z : Y) * k⁻¹ = (a z : Y) := fun z => (hρ k z).symm
  have hconj_b : ∀ z : U, k' * (z : Y) * k'⁻¹ = (b z : Y) := fun z => by
    rw [← hk'b, hρ]
  have hkk' : k * k' = k' * k := by rw [← hk'2, mul_assoc]
  refine ⟨(w' : Y) * k', ?_, ?_⟩
  ·
    set z : U := w' * b w' with hz
    have hy2 : ((w' : Y) * k') ^ 2 = (z : Y) * k := by
      rw [pow_two, hz, Subgroup.coe_mul, ← hconj_b w', ← hk'2]
      group
    have hza : (z : Y) * (a z : Y) = 1 := by
      have hzv : z = ι (coordsCorrection v * coordsB (coordsCorrection v)) := by
        rw [hz, hb_apply, hw'_def, MulEquiv.symm_apply_apply, map_mul]
      have h1 : z * a z = 1 := by
        rw [ha_apply, hzv, MulEquiv.symm_apply_apply, ← map_mul, coordsB_square_norm, map_one]
      have := congrArg Subtype.val h1
      simpa using this
    have hy4 : ((w' : Y) * k') ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hy2, pow_two]
      calc (z : Y) * k * ((z : Y) * k) = (z : Y) * (k * z * k⁻¹) * (k * k) := by group
        _ = 1 := by rw [hconj_a, hza, hk2, mul_one]
    have hy2ne : ((w' : Y) * k') ^ 2 ≠ 1 := by
      rw [hy2]
      intro h
      have hkU : k ∈ U := by
        have : k = (z : Y)⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]
        exact U.inv_mem z.2
      have hk1 : k = 1 := Subgroup.disjoint_def.mp (disjoint_iff.mpr hUK) hkU hk
      apply ha1
      rw [ha_def, hk1, map_one]
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := (w' : Y) * k')
      (by rw [pow_one]; exact hy2ne) (by simpa using hy4)
    simpa using this
  ·
    have hkey' : (w : Y) * (a w' : Y) = (w' : Y) * (b ⟨w, hw⟩ : Y) := by
      have := congrArg Subtype.val hkey
      simpa using this
    change w * k * ((w' : Y) * k') = (w' : Y) * k' * (w * k)
    calc w * k * ((w' : Y) * k') = w * (k * w' * k⁻¹) * (k * k') := by group
      _ = w * (a w' : Y) * (k * k') := by rw [hconj_a]
      _ = (w' : Y) * (b ⟨w, hw⟩ : Y) * (k' * k) := by rw [hkey', hkk']
      _ = (w' : Y) * (k' * w * k'⁻¹) * (k' * k) := by rw [← hconj_b]
      _ = (w' : Y) * k' * (w * k) := by group

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
