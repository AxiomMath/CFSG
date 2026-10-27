module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VCore
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VQuat
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L2VStd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Defs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.GorensteinWalter CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open CFSG.ClassicalInvolution.Q3.TL4.MF163
open scoped MatrixGroups

theorem l2_setup_iff {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A] (T : Subgroup A) [T.Normal]
    (hT : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 ↥T) (hC : Subgroup.centralizer (T : Set A) = ⊥)
    {x b z : A} (hxo : orderOf x = 2 ^ (r - 1)) (hbx : b * x * b⁻¹ = x⁻¹)
    (hbb : b * b = x ^ 2 ^ (r - 2)) (hz : x ^ 2 ^ (r - 2) = z) :
    ∃ (p f : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (Ψ : MulAut ↥T ≃* PGammaL2 K) (α : Kˣ),
      p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Nat.card K = p ^ f ∧ (2 : K) ≠ 0 ∧
      Nonempty (↥T ≃* GorensteinWalter.PSL2 K) ∧
      Ψ (MulAut.conjNormal z) = TwinSocF4.tor (-1) ∧
      Ψ (MulAut.conjNormal x) = TwinSocF4.tor α ∧ orderOf α = 2 ^ (r - 1) ∧
      Ψ (MulAut.conjNormal b) * Ψ (MulAut.conjNormal b) = TwinSocF4.tor (-1) ∧
      Ψ (MulAut.conjNormal b) * TwinSocF4.tor α * (Ψ (MulAut.conjNormal b))⁻¹ =
        TwinSocF4.tor α⁻¹ ∧
      (Ψ (MulAut.conjNormal b)).right ≠ 1 ∧
      (∀ a : A, a ∈ T ↔ Ψ (MulAut.conjNormal a) ∈ ((SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp
          (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, K) →* PGL2 K)).range) ∧
      (∃ a : A, a ∈ T ∧ a * z = z * a ∧ Ψ (MulAut.conjNormal a) = TwinSocF4.tor (-1) * TwinSocF4.wref) := by
  classical
  obtain ⟨p, f, K, hKf, hKfin, hp, hpodd, hf, h3, hKcard, ⟨e⟩⟩ := soc_l2_data hT
  haveI : Fact p.Prime := ⟨hp⟩
  have hOdd : IsOddPrimePower (Nat.card K) := ⟨p, f, hp, hpodd, hf, hKcard⟩
  have hcard : 3 < Nat.card K := by rw [hKcard]; exact h3
  have h2 : (2 : K) ≠ 0 := by
    have hodd : Odd (Nat.card K) := by rw [hKcard]; exact hpodd.pow
    exact CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hodd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hpodd (by decide)
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKcard hOdd hcard
  let Φ : PGammaL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hOdd hcard)
      ⟨pGammaL2ToMulAutPSL2_injective K hOdd hcard, hsurj⟩
  let Ψ : MulAut ↥T ≃* PGammaL2 K := (MulAut.congr e).trans Φ.symm
  have hΨconj : ∀ a : ↥T, Ψ (MulAut.conjNormal (a : A)) =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL (e a)) := by
    intro a
    apply Φ.injective
    show Φ (Φ.symm ((MulAut.congr e) (MulAut.conjNormal (a : A)))) = _
    rw [MulEquiv.apply_symm_apply]
    show _ = pGammaL2ToMulAutPSL2 K hOdd hcard _
    rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]
    ext y
    have h1 : (MulAut.conjNormal (a : A)) (e.symm y) = a * e.symm y * a⁻¹ :=
      Subtype.ext (by simp [MulAut.conjNormal_val])
    simp [MulAut.congr_apply, MulAut.conj_apply, h1]
  haveI : Finite K := hKfin
  let θ : A →* PGammaL2 K := Ψ.toMonoidHom.comp MulAut.conjNormal
  have hθ : ∀ g, θ g = Ψ (MulAut.conjNormal g) := fun g => rfl
  have hθinj : Function.Injective θ := Ψ.injective.comp (conjNormal_injective hC)
  have hXo : orderOf (θ x) = 2 ^ (r - 1) := by rw [orderOf_injective θ hθinj x]; exact hxo
  have hBX : θ b * θ x * (θ b)⁻¹ = (θ x)⁻¹ := by
    have := congrArg θ hbx
    simpa [map_mul, map_inv] using this
  have hBB : θ b * θ b = (θ x) ^ 2 ^ (r - 2) := by rw [← map_mul, hbb, map_pow]
  obtain ⟨hXR, hBR1, hBR2⟩ := quat_pgl2 hOdd h2 hr hXo hBX hBB
  have hneg : IsSquare (-1 : K) := isSquare_neg_one_of_fieldAut hOdd hBR2 hBR1
  have hXe := eq_inl_of_right_eq_one hXR
  set X₀ : PGL2 K := (θ x).left with hX₀
  set z₀ : PGL2 K := X₀ ^ 2 ^ (r - 2) with hz₀
  have hθz : θ z = SemidirectProduct.inl z₀ := by
    rw [← hz, map_pow, hXe, ← map_pow]
  have hz₀range : z₀ ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, K) →* PGL2 K).range := by
    have : z₀ = X₀ ^ 2 ^ (r - 3) * X₀ ^ 2 ^ (r - 3) := by
      rw [hz₀, ← pow_add, ← two_mul, ← pow_succ']
      congr 2
      omega
    rw [this]
    exact Subgroup.mul_self_mem_of_index_two (pgl2_psl2Range_index_eq_two K hOdd) _
  have hz₀ord : orderOf z₀ = 2 := by
    have h1 : orderOf (θ z) = 2 := by
      rw [← hz, map_pow, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
        (by rw [hXo]; exact pow_dvd_pow 2 (by omega)), hXo,
        show 2 ^ (r - 1) = 2 * 2 ^ (r - 2) by rw [← pow_succ']; congr 1; omega]
      exact Nat.mul_div_cancel 2 (by positivity)
    rw [hθz, orderOf_injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)
      SemidirectProduct.inl_injective] at h1
    exact h1
  obtain ⟨g, hg⟩ := exists_conj_std hKcard hpodd hf hneg h2 hz₀range hz₀ord
  set g₀ : PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL g with hg₀
  let Ψ' : MulAut ↥T ≃* PGammaL2 K :=
    Ψ.trans (MulAut.conj (SemidirectProduct.inl g₀ : PGammaL2 K))
  have hΨ' : ∀ φ, Ψ' φ = SemidirectProduct.inl g₀ * Ψ φ * (SemidirectProduct.inl g₀)⁻¹ :=
    fun φ => rfl
  let θ' : A →* PGammaL2 K := Ψ'.toMonoidHom.comp MulAut.conjNormal
  have hθ' : ∀ a, θ' a = Ψ' (MulAut.conjNormal a) := fun a => rfl
  have hθ'inj : Function.Injective θ' := Ψ'.injective.comp (conjNormal_injective hC)
  have hZ' : θ' z = tor (-1) := by
    rw [hθ', hΨ', ← hθ, hθz, ← map_inv, ← map_mul, ← map_mul, hg, tor_apply]
  have hZ'' : Ψ' (MulAut.conjNormal z) = tor (-1) := hZ'
  have hXR' : (θ' x).right = 1 := by
    rw [hθ', hΨ', ← hθ]
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, hXR, one_mul, mul_one, inv_one]
  have hXo' : orderOf (θ' x) = 2 ^ (r - 1) := by rw [orderOf_injective θ' hθ'inj x]; exact hxo
  have hX'Z : (θ' x) ^ 2 ^ (r - 2) = tor (-1) := by rw [← map_pow, hz, hZ']
  have hX'comm : θ' x * tor (-1) = tor (-1) * θ' x := by
    rw [← hX'Z]; exact (Commute.self_pow (θ' x) _).eq
  obtain ⟨α, ε, σ, hε, hX'e⟩ := exists_decomp h2 hX'comm
  have hσ : σ = 1 := by
    have h := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) hX'e
    rw [map_mul, map_mul, map_pow, rightHom_tor, rightHom_wref, SemidirectProduct.rightHom_inr,
      one_pow, one_mul, one_mul] at h
    exact h.symm.trans hXR'
  subst hσ
  have hε0 : ε = 0 := by
    by_contra hne
    have hε1 : ε = 1 := by omega
    subst hε1
    have hsq : θ' x * θ' x = 1 := by
      rw [hX'e, map_one, mul_one, pow_one]
      calc tor α * wref * (tor α * wref) = tor α * (wref * tor α) * wref := by group
        _ = 1 := by rw [wref_mul_tor, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul,
              wref_mul_wref]
    have hdvd := orderOf_dvd_of_pow_eq_one (show θ' x ^ 2 = 1 by rw [sq]; exact hsq)
    rw [hXo'] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have h8 : 2 ^ 3 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hε0
  have hX'tor : θ' x = tor α := by rw [hX'e, pow_zero, mul_one, map_one, mul_one]
  have hα : orderOf α = 2 ^ (r - 1) := by
    rw [← hXo', hX'tor, orderOf_injective (tor : Kˣ →* PGammaL2 K) tor_injective α]
  have hBX' : θ' b * θ' x * (θ' b)⁻¹ = (θ' x)⁻¹ := by
    have := congrArg θ' hbx
    simpa [map_mul, map_inv] using this
  have hB'B' : θ' b * θ' b = tor (-1) := by rw [← map_mul, hbb, hz, hZ']
  have hB'α : θ' b * tor α * (θ' b)⁻¹ = tor α⁻¹ := by
    rw [← hX'tor, hBX', map_inv, hX'tor]
  have hBR' : (θ' b).right ≠ 1 := by
    rw [hθ', hΨ', ← hθ]
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, one_mul, mul_one, inv_one]
    exact hBR1
  set a : ↥T := e.symm (g⁻¹ * (QuotientGroup.mk (sw : SL(2, K)) : PSL(2, K)) * g) with ha
  have hΨ'a : Ψ' (MulAut.conjNormal (a : A)) = tor (-1) * wref := by
    have h1 : e a = g⁻¹ * (QuotientGroup.mk (sw : SL(2, K)) : PSL(2, K)) * g := by
      rw [ha, MulEquiv.apply_symm_apply]
    have h2 : Matrix.ProjectiveSpecialLinearGroup.toPGL
        (g⁻¹ * (QuotientGroup.mk (sw : SL(2, K)) : PSL(2, K)) * g) =
        g₀⁻¹ * Matrix.ProjGenLinGroup.mk (dm (-1) * wm) * g₀ := by
      rw [map_mul, map_mul, map_inv, toPGL_sw]
    have h3 : (SemidirectProduct.inl g₀ : PGammaL2 K) *
        SemidirectProduct.inl (g₀⁻¹ * Matrix.ProjGenLinGroup.mk (dm (-1) * wm) * g₀) *
        (SemidirectProduct.inl g₀)⁻¹ =
        SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk (dm (-1) * wm)) := by
      have hinv : (SemidirectProduct.inl g₀ : PGammaL2 K)⁻¹ = SemidirectProduct.inl g₀⁻¹ :=
        (map_inv (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) g₀).symm
      rw [hinv, ← map_mul, ← map_mul]; congr 1; group
    rw [hΨ', hΨconj, h1, h2, h3, tor_apply, wref, ← map_mul, ← map_mul]
  have hwZ : (wref : PGammaL2 K) * tor (-1) = tor (-1) * wref := by
    rw [wref_mul_tor, inv_neg_one]
  have hcomm : MulAut.conjNormal (H := T) (a : A) * MulAut.conjNormal (H := T) z =
      MulAut.conjNormal (H := T) z * MulAut.conjNormal (H := T) (a : A) := by
    apply Ψ'.injective
    rw [map_mul, map_mul, hΨ'a, hZ'', mul_assoc, hwZ]
  have haz : (a : A) * z = z * (a : A) := by
    apply conjNormal_injective (T := T) hC
    rw [map_mul, map_mul]; exact hcomm
  let τ : PSL(2, K) →* PGammaL2 K :=
    (SemidirectProduct.inl : PGL2 K →* PGammaL2 K).comp
      (Matrix.ProjectiveSpecialLinearGroup.toPGL : PSL(2, K) →* PGL2 K)
  have hkey : ∀ s : PSL(2, K), Ψ' (MulAut.conjNormal (H := T) ((e.symm s : ↥T) : A)) =
      τ (g * s * g⁻¹) := by
    intro s
    rw [hΨ', hΨconj, MulEquiv.apply_symm_apply, hg₀]
    simp only [τ, MonoidHom.comp_apply, map_mul, map_inv]
  have hmemR : ∀ a : A, Ψ' (MulAut.conjNormal (H := T) a) ∈ τ.range → a ∈ T := by
    intro a ha
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp ha
    have ht : Ψ' (MulAut.conjNormal (H := T) ((e.symm (g⁻¹ * y * g) : ↥T) : A)) = τ y := by
      rw [hkey, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
    have hc : MulAut.conjNormal (H := T) a =
        MulAut.conjNormal (H := T) ((e.symm (g⁻¹ * y * g) : ↥T) : A) :=
      Ψ'.injective (hy.symm.trans ht.symm)
    have hac := conjNormal_injective (T := T) hC hc
    rw [hac]
    exact (e.symm _).2
  have hmemL : ∀ a : A, a ∈ T → Ψ' (MulAut.conjNormal (H := T) a) ∈ τ.range := by
    intro a ha
    refine MonoidHom.mem_range.mpr ⟨g * e ⟨a, ha⟩ * g⁻¹, ?_⟩
    have h1 := hkey (e ⟨a, ha⟩)
    rw [MulEquiv.symm_apply_apply] at h1
    exact h1.symm
  have hmemIff : ∀ a : A, a ∈ T ↔ Ψ' (MulAut.conjNormal (H := T) a) ∈ τ.range :=
    fun a => ⟨hmemL a, hmemR a⟩
  exact ⟨p, f, K, hKf, hKfin, Ψ', α, hp, hp2, hf, hKcard, h2, ⟨e⟩, hZ', (hθ' x).symm.trans hX'tor,
    hα, hB'B', hB'α, hBR', hmemIff, ⟨(a : A), a.2, haz, hΨ'a⟩⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
