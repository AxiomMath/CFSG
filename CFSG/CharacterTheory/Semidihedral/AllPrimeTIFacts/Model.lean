module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Core
public import CFSG.CharacterTheory.Semidihedral.ActualFourGroupAlignment
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Data

public section

namespace CFSG.Semidihedral.AllPrime.QDTI

noncomputable section

open Matrix CFSG.Semidihedral CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.MatrixTorus
open CFSG.ABGTheoremB
open scoped Pointwise

variable {F : Type} [Field F] {a : Fˣ} {A : Subgroup (F ≃+* F)}
  {hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a}

@[expose] def layerM (F : Type) [Field F] (a : Fˣ) (A : Subgroup (F ≃+* F))
    (hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a) : Subgroup (OriginalH F a A hfix) :=
  (originalSlInH F a A hfix).range

@[expose] def cenU (F : Type) [Field F] (a : Fˣ) (A : Subgroup (F ≃+* F))
    (hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a) : Subgroup (OriginalH F a A hfix) :=
  Subgroup.centralizer {originalU F a A hfix}

theorem slIn_injective : Function.Injective (originalSlInH F a A hfix) :=
  SemidirectProduct.inl_injective.comp (MatrixCoverData.inclusion_injective F a)

theorem slIn_left_left (Y : SL F) : (originalSlInH F a A hfix Y).left.left = Y := rfl

theorem slIn_left_right (Y : SL F) :
    (originalSlInH F a A hfix Y).left.right = 1 := rfl

theorem slIn_right (Y : SL F) : (originalSlInH F a A hfix Y).right = 1 := rfl

theorem decomp (m : OriginalH F a A hfix) :
    m = originalSlInH F a A hfix m.left.left *
      SemidirectProduct.inl (SemidirectProduct.inr m.left.right) *
        SemidirectProduct.inr m.right := by
  apply SemidirectProduct.ext
  · apply SemidirectProduct.ext
    · simp [originalSlInH, MatrixCoverData.inclusion]
    · simp [originalSlInH, MatrixCoverData.inclusion]
  · simp [originalSlInH, MatrixCoverData.inclusion]

theorem conj_inr_slIn (σ : A) (Y : SL F) :
    (SemidirectProduct.inr σ : OriginalH F a A hfix) * originalSlInH F a A hfix Y *
      (SemidirectProduct.inr σ)⁻¹ =
      originalSlInH F a A hfix
        (Matrix.SpecialLinearGroup.map (σ : F ≃+* F).toRingHom Y) := by
  rw [show originalSlInH F a A hfix Y = SemidirectProduct.inl (MatrixCoverData.inclusion F a Y)
    from rfl, ← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem conj_c2_slIn (e : C2) (Y : SL F) :
    (SemidirectProduct.inl (SemidirectProduct.inr e) : OriginalH F a A hfix) *
      originalSlInH F a A hfix Y * (SemidirectProduct.inl (SemidirectProduct.inr e))⁻¹ =
      originalSlInH F a A hfix (MatrixCoverData.action F a e Y) := by
  change SemidirectProduct.inl (SemidirectProduct.inr e) *
      SemidirectProduct.inl (SemidirectProduct.inl Y) *
      (SemidirectProduct.inl (SemidirectProduct.inr e))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← SemidirectProduct.inl_aut]
  rfl

@[expose] def actOn (m : OriginalH F a A hfix) (Y : SL F) : SL F :=
  m.left.left * MatrixCoverData.action F a m.left.right
    (Matrix.SpecialLinearGroup.map (m.right : F ≃+* F).toRingHom Y) * m.left.left⁻¹

theorem conj_slIn (m : OriginalH F a A hfix) (Y : SL F) :
    m * originalSlInH F a A hfix Y * m⁻¹ = originalSlInH F a A hfix (actOn m Y) := by
  conv_lhs => rw [decomp m]
  have h1 := conj_inr_slIn (a := a) (hfix := hfix) m.right Y
  have h2 := conj_c2_slIn (A := A) (hfix := hfix) m.left.right
    (Matrix.SpecialLinearGroup.map (m.right : F ≃+* F).toRingHom Y)
  calc originalSlInH F a A hfix m.left.left *
        SemidirectProduct.inl (SemidirectProduct.inr m.left.right) *
          SemidirectProduct.inr m.right * originalSlInH F a A hfix Y *
        (originalSlInH F a A hfix m.left.left *
          SemidirectProduct.inl (SemidirectProduct.inr m.left.right) *
            SemidirectProduct.inr m.right)⁻¹ =
      originalSlInH F a A hfix m.left.left *
        (SemidirectProduct.inl (SemidirectProduct.inr m.left.right) *
          (SemidirectProduct.inr m.right * originalSlInH F a A hfix Y *
            (SemidirectProduct.inr m.right)⁻¹) *
          (SemidirectProduct.inl (SemidirectProduct.inr m.left.right))⁻¹) *
        (originalSlInH F a A hfix m.left.left)⁻¹ := by group
    _ = originalSlInH F a A hfix (actOn m Y) := by
      rw [h1, h2, ← map_inv, ← map_mul, ← map_mul]
      rfl

theorem conj_u_slIn (Y : SL F) :
    originalU F a A hfix * originalSlInH F a A hfix Y * (originalU F a A hfix)⁻¹ =
      originalSlInH F a A hfix (beta F a Y) := by
  rw [conj_slIn]
  congr 1
  simp only [actOn]
  change (1 : SL F) * MatrixCoverData.action F a (Multiplicative.ofAdd (1 : ZMod 2))
    (Matrix.SpecialLinearGroup.map (1 : A).val.toRingHom Y) * 1⁻¹ = _
  rw [MatrixCoverData.action_one, inv_one, mul_one, one_mul]
  congr 1

theorem mem_cenU_iff (m : OriginalH F a A hfix) :
    m ∈ cenU F a A hfix ↔ m.left.left ∈ Torus F a := by
  rw [cenU, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hm
    have hm' : m.left ∈ Subgroup.centralizer {MatrixCoverData.u F a} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hl := congrArg (fun x : OriginalH F a A hfix => x.left) hm
      change m.left * originalFieldAction F a A hfix m.right (MatrixCoverData.u F a) =
        MatrixCoverData.u F a * originalFieldAction F a A hfix 1 m.left at hl
      have hfu : originalFieldAction F a A hfix m.right (MatrixCoverData.u F a) =
          MatrixCoverData.u F a := by
        rw [originalFieldAction_pair]
        apply SemidirectProduct.ext
        · exact map_one _
        · rfl
      rw [hfu, map_one, MulAut.one_apply] at hl
      exact hl
    exact (matrix_centralizer_u_iff F a m.left).mp hm'
  · intro hm
    have hm' := (matrix_centralizer_u_iff F a m.left).mpr hm
    rw [Subgroup.mem_centralizer_singleton_iff] at hm'
    apply SemidirectProduct.ext
    · change m.left * originalFieldAction F a A hfix m.right (MatrixCoverData.u F a) =
        MatrixCoverData.u F a * originalFieldAction F a A hfix 1 m.left
      have hfu : originalFieldAction F a A hfix m.right (MatrixCoverData.u F a) =
          MatrixCoverData.u F a := by
        rw [originalFieldAction_pair]
        apply SemidirectProduct.ext
        · exact map_one _
        · rfl
      rw [hfu, map_one, MulAut.one_apply]
      exact hm'
    · change m.right * 1 = 1 * m.right
      rw [mul_one, one_mul]

theorem slIn_mem_cenU_iff (Y : SL F) :
    originalSlInH F a A hfix Y ∈ cenU F a A hfix ↔ Y ∈ Torus F a :=
  mem_cenU_iff _

theorem u_mem_cenU : originalU F a A hfix ∈ cenU F a A hfix :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem layerM_normal : (layerM F a A hfix).Normal := by
  constructor
  rintro _ ⟨Y, rfl⟩ m
  exact ⟨actOn m Y, (conj_slIn m Y).symm⟩

theorem mem_layerM_iff (m : OriginalH F a A hfix) :
    m ∈ layerM F a A hfix ↔ m.left.right = 1 ∧ m.right = 1 := by
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨m.left.left, ?_⟩
    apply SemidirectProduct.ext
    · apply SemidirectProduct.ext
      · rfl
      · exact h1.symm
    · exact h2.symm

theorem layerM_inf_cenU :
    layerM F a A hfix ⊓ cenU F a A hfix = (Torus F a).map (originalSlInH F a A hfix) := by
  ext m
  constructor
  · rintro ⟨⟨Y, rfl⟩, hY⟩
    exact ⟨Y, (slIn_mem_cenU_iff Y).mp hY, rfl⟩
  · rintro ⟨Y, hY, rfl⟩
    exact ⟨⟨Y, rfl⟩, (slIn_mem_cenU_iff Y).mpr hY⟩

@[expose] def c2Hom : OriginalH F a A hfix →* C2 where
  toFun m := m.left.right
  map_one' := rfl
  map_mul' x y := by
    change (x.left * originalFieldAction F a A hfix x.right y.left).right = _
    rw [SemidirectProduct.mul_right, originalFieldAction_pair]

theorem c2Hom_apply (m : OriginalH F a A hfix) : c2Hom m = m.left.right := rfl

theorem mem_layerM_of_odd (m : OriginalH F a A hfix) (hodd : Odd (orderOf m))
    (hr : m.right = 1) : m ∈ layerM F a A hfix := by
  rw [mem_layerM_iff]
  refine ⟨?_, hr⟩
  have hpow : (c2Hom m) ^ orderOf m = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases C2_cases (c2Hom m) with h | h
  · exact h
  · exfalso
    rw [h, ← ofAdd_nsmul] at hpow
    obtain ⟨k, hk⟩ := hodd
    rw [hk] at hpow
    revert hpow
    simp only [ofAdd_eq_one]
    rw [nsmul_eq_mul]
    push_cast
    rw [show (2 * (k : ZMod 2) + 1) * 1 = 1 by
      rw [show (2 : ZMod 2) = 0 from rfl]; ring]
    decide

theorem fixes_sqrt_neg (hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a) (hA : Odd (Nat.card A))
    [Finite F] {l : F} (hl : l ^ 2 = -(a : F)) (σ : A) : (σ : F ≃+* F) l = l := by
  have hmem : -(a : F) ∈ MatrixCover.FixedField F A := by
    intro τ
    change (τ : F ≃+* F) (-(a : F)) = -(a : F)
    rw [map_neg, hfix τ]
  exact MatrixCover.square_root_fixed F A hA ⟨-(a : F), hmem⟩ l hl σ

theorem inv_of_inf_centralizer {H₀ : Type*} [Group H₀] [Finite H₀] {y : H₀} (hy : y * y = 1)
    {U : Subgroup H₀} (hU : ∀ x ∈ U, y * x * y⁻¹ ∈ U)
    (hCU : U ⊓ Subgroup.centralizer {y} = ⊥) :
    (∀ x ∈ U, y * x * y⁻¹ = x⁻¹) ∧ (∀ x ∈ U, ∀ x' ∈ U, x * x' = x' * x) := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  let φ : U →* U :=
    { toFun := fun x => ⟨y * x * y⁻¹, hU x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x x' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hfree : MonoidHom.FixedPointFree φ := by
    intro x hx
    have hx' : y * (x : H₀) * y⁻¹ = x := congrArg Subtype.val hx
    have hmem : (x : H₀) ∈ U ⊓ Subgroup.centralizer {y} := by
      refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (x : H₀) * y = y * x * y⁻¹ * y := by rw [hx']
        _ = y * x := by group
    rw [hCU, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hinvol : Function.Involutive φ := by
    intro x
    apply Subtype.ext
    change y * (y * x * y⁻¹) * y⁻¹ = x
    rw [hyinv]
    calc y * (y * (x : H₀) * y) * y = (y * y) * x * (y * y) := by group
      _ = x := by rw [hy]; group
  refine ⟨fun x hx => ?_, fun x hx x' hx' => ?_⟩
  · exact congrArg Subtype.val (congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨x, hx⟩)
  · exact congrArg Subtype.val (hfree.commute_all_of_involutive hinvol ⟨x, hx⟩ ⟨x', hx'⟩).eq

theorem originalU_mul_self : originalU F a A hfix * originalU F a A hfix = 1 := by
  rw [← pow_two]
  exact ActualFourGroupAlignment.originalU_square F a A hfix

theorem right_originalU : (originalU F a A hfix).right = 1 := rfl

theorem originalZ_eq : originalZ F a A hfix = originalSlInH F a A hfix
    (OddFieldSL2.minusIdentity F) := rfl

variable [Finite F]

theorem finite_originalH : Finite (OriginalH F a A hfix) := by
  have : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have : Finite (MatrixCoverData.M F a) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  exact Finite.of_equiv _ SemidirectProduct.equivProd.symm

omit [Finite F] in
theorem torus_eq_comap : Torus F a = (cenU F a A hfix).comap (originalSlInH F a A hfix) := by
  ext Y
  exact (slIn_mem_cenU_iff Y).symm

theorem isCyclic_layerM_inf_cenU (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) :
    IsCyclic (layerM F a A hfix ⊓ cenU F a A hfix : Subgroup (OriginalH F a A hfix)) := by
  have : IsCyclic (Torus F a) := torus_cyclic F a hodd ha
  rw [layerM_inf_cenU]
  exact isCyclic_of_surjective _ ((originalSlInH F a A hfix).subgroupMap_surjective (Torus F a))

omit [Finite F] in
theorem torus_mul_comm {X Y : SL F} (hX : X ∈ Torus F a) (hY : Y ∈ Torus F a) :
    X * Y = Y * X :=
  congrArg Subtype.val (mul_comm (⟨X, hX⟩ : Torus F a) ⟨Y, hY⟩)

theorem right_eq_one_of_centralizes (hodd : Odd (Nat.card F)) (hF : 5 ≤ Nat.card F)
    {g : OriginalH F a A hfix} (hg : g ∈ cenU F a A hfix)
    (hgc : g ∈ Subgroup.centralizer
      ((layerM F a A hfix ⊓ cenU F a A hfix : Subgroup (OriginalH F a A hfix)) :
        Set (OriginalH F a A hfix))) : g.right = 1 := by
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hX : g.left.left ∈ Torus F a := (mem_cenU_iff g).mp hg
  have hfixT : ∀ τ ∈ Torus F a, ∀ i j : Fin 2,
      (g.right : F ≃+* F) (τ.1 i j) = τ.1 i j := by
    intro τ hτ i j
    have hmem : originalSlInH F a A hfix τ ∈ layerM F a A hfix ⊓ cenU F a A hfix :=
      ⟨⟨τ, rfl⟩, (slIn_mem_cenU_iff τ).mpr hτ⟩
    have hc := Subgroup.mem_centralizer_iff.mp hgc _ hmem
    have hconj : g * originalSlInH F a A hfix τ * g⁻¹ = originalSlInH F a A hfix τ := by
      rw [← hc, mul_inv_cancel_right]
    rw [conj_slIn] at hconj
    have hact := slIn_injective hconj
    have hστ : Matrix.SpecialLinearGroup.map (g.right : F ≃+* F).toRingHom τ ∈ Torus F a :=
      torus_field_invariant F a (g.right : F ≃+* F) (hfix g.right) ⟨τ, hτ⟩
    simp only [actOn] at hact
    rw [action_torus_trivial F a g.left.right ⟨_, hστ⟩] at hact
    rw [torus_mul_comm hX hστ, mul_inv_cancel_right] at hact
    have := congrArg (fun Z : SL F => Z.1 i j) hact
    exact this
  have hσ := ringEquiv_eq_refl_of_fix_torus a h2 hF (g.right : F ≃+* F) hfixT
  exact Subtype.ext hσ

omit [Finite F] in
theorem eq_one_of_sq_eq_one_A (hA : Odd (Nat.card A)) {σ : A} (hσ : σ * σ = 1) : σ = 1 := by
  have h1 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hσ)
  have h2 : Odd (orderOf σ) := hA.of_dvd_nat (orderOf_dvd_natCard σ)
  have h3 : orderOf σ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2; exact absurd h2 (by decide)
  exact orderOf_eq_one_iff.mp h3

theorem signalizer_le_layerM (hA : Odd (Nat.card A)) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ U ∈ signalizers (⊤ : Subgroup (OriginalH F a A hfix)) (cenU F a A hfix) r,
        U ≤ layerM F a A hfix := by
  intro r hr hr2 U hU
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  obtain ⟨-, hUp, hCU, hUC⟩ := hU
  have hUu : ∀ x ∈ U, originalU F a A hfix * x * (originalU F a A hfix)⁻¹ ∈ U := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hCU u_mem_cenU) x).mp hx
  obtain ⟨hinv, -⟩ := inv_of_inf_centralizer originalU_mul_self hUu hUC
  intro x hx
  have hr' : x.right = 1 := by
    have h := congrArg (fun m : OriginalH F a A hfix => m.right) (hinv x hx)
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, right_originalU,
      one_mul, inv_one, mul_one] at h
    apply eq_one_of_sq_eq_one_A hA
    calc x.right * x.right = x.right * x.right⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel _
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := hUp ⟨x, hx⟩
  have hodd : Odd (orderOf x) := by
    have h1 : orderOf x ∣ r ^ k := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_of_pow_eq_one hk
    exact (hr.odd_of_ne_two hr2).pow.of_dvd_nat h1
  exact mem_layerM_of_odd x hodd hr'

theorem exists_generic_torus (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hq : 7 ≤ Nat.card F) : ∃ w ∈ Torus F a, w.1 0 0 * w.1 1 0 ≠ 0 := by
  have hWcard : 3 ≤ Nat.card (Wsl a) := by
    rw [card_Wsl hodd a ha]
    exact torusSize_half_ge_three hq
  have hW1 : Wsl a ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hWcard
    omega
  obtain ⟨⟨w₀, hw₀⟩, hw₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
  have hw₀1 : w₀ ≠ 1 := fun h => hw₀ne (Subtype.ext h)
  obtain ⟨hw₀T, hw₀o⟩ := (mem_Wsl_iff hodd a ha w₀).mp hw₀
  exact ⟨w₀, hw₀T, torus_entries_ne_zero_of_odd a hw₀T hw₀o hw₀1⟩

theorem layer_signalizer_elements {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup (OriginalH F a A hfix)}
    (hX : X ∈ signalizers (layerM F a A hfix) (cenU F a A hfix) r) {Y : SL F}
    (hY : originalSlInH F a A hfix Y ∈ X) :
    beta F a Y = Y⁻¹ ∧ Odd (orderOf Y) ∧
      ∀ τ ∈ Torus F a, Y * (τ * Y * τ⁻¹) = (τ * Y * τ⁻¹) * Y := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  obtain ⟨-, hXp, hCX, hXC⟩ := hX
  have hXu : ∀ x ∈ X, originalU F a A hfix * x * (originalU F a A hfix)⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hCX u_mem_cenU) x).mp hx
  obtain ⟨hinv, hcomm⟩ := inv_of_inf_centralizer originalU_mul_self hXu hXC
  refine ⟨?_, ?_, ?_⟩
  · have h := hinv _ hY
    rw [conj_u_slIn, ← map_inv] at h
    exact slIn_injective h
  · have : Fact r.Prime := ⟨hr⟩
    obtain ⟨k, hk⟩ := hXp ⟨_, hY⟩
    have h1 : orderOf (originalSlInH F a A hfix Y) ∣ r ^ k := by
      rw [← Subgroup.orderOf_mk _ hY]
      exact orderOf_dvd_of_pow_eq_one hk
    rw [orderOf_injective _ slIn_injective] at h1
    exact (hr.odd_of_ne_two hr2).pow.of_dvd_nat h1
  · intro τ hτ
    have hτC : originalSlInH F a A hfix τ ∈ cenU F a A hfix := (slIn_mem_cenU_iff τ).mpr hτ
    have hmem : originalSlInH F a A hfix (τ * Y * τ⁻¹) ∈ X := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hCX hτC) _).mp hY
    have h := hcomm _ hY _ hmem
    rw [← map_mul, ← map_mul] at h
    exact slIn_injective h

theorem layer_signalizer_model (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hq : 7 ≤ Nat.card F) {p : ℕ} [CharP F p] (hp : p.Prime) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ X ∈ signalizers (layerM F a A hfix) (cenU F a A hfix) r, X ≠ ⊥ →
        Nat.card F % 4 = 3 ∧ r = p := by
  intro r hr hr2 X hX hXne
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨⟨x, hx⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have hx1 : x ≠ 1 := fun h => hxne (Subtype.ext h)
  obtain ⟨Y, rfl⟩ := hX.1 hx
  have hY1 : Y ≠ 1 := by
    rintro rfl
    exact hx1 (map_one _)
  obtain ⟨hinv, hYo, hcomm⟩ := layer_signalizer_elements hr hr2 hX hx
  obtain ⟨w, hwT, hwxy⟩ := exists_generic_torus hodd ha hq
  obtain ⟨l, hl, hYl⟩ := inverted_odd_mem_rootGroup a h2 hinv hY1 hYo hwT hwxy (hcomm w hwT)
  refine ⟨(neg_coefficient_square_iff F a hodd ha).mp ⟨l, by rw [← hl]; ring⟩, ?_⟩
  have hpow := rootGroup_pow_char p hYl
  have hdvd : orderOf Y ∣ p := orderOf_dvd_of_pow_eq_one hpow
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := hX.2.1 ⟨_, hx⟩
  have h1 : orderOf Y ∣ r ^ k := by
    rw [← orderOf_injective _ (slIn_injective (hfix := hfix)), ← Subgroup.orderOf_mk _ hx]
    exact orderOf_dvd_of_pow_eq_one hk
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hY1
  · rw [h] at h1
    exact (Nat.prime_dvd_prime_iff_eq hp hr).mp
      (hp.dvd_of_dvd_pow h1) |>.symm

@[expose] def rootM (F : Type) [Field F] (a : Fˣ) (A : Subgroup (F ≃+* F))
    (hfix : ∀ σ : A, (σ : F ≃+* F) (a : F) = a) (l : F) : Subgroup (OriginalH F a A hfix) :=
  (rootGroup l).map (originalSlInH F a A hfix)

omit [Finite F] in
theorem action_mem_rootGroup {l : F} (hl : l ^ 2 = -(a : F)) (e : C2) {X : SL F}
    (hX : X ∈ rootGroup l) : MatrixCoverData.action F a e X ∈ rootGroup l := by
  rcases C2_cases e with rfl | rfl
  · rw [map_one]
    exact hX
  · rw [MatrixCoverData.action_one]
    exact beta_mem_rootGroup a hl hX

theorem actOn_mem_rootGroup (hA : Odd (Nat.card A)) {l : F} (hl : l ^ 2 = -(a : F))
    {c : OriginalH F a A hfix} (hc : c ∈ cenU F a A hfix) {X : SL F} (hX : X ∈ rootGroup l) :
    actOn c X ∈ rootGroup l := by
  have hT : c.left.left ∈ Torus F a := (mem_cenU_iff c).mp hc
  apply torus_conj_mem_rootGroup a hl hT
  apply action_mem_rootGroup hl
  exact map_mem_rootGroup _ (fixes_sqrt_neg hfix hA hl c.right) hX

theorem cenU_le_normalizer_rootM (hA : Odd (Nat.card A)) {l : F} (hl : l ^ 2 = -(a : F)) :
    cenU F a A hfix ≤ Subgroup.normalizer (rootM F a A hfix l : Set (OriginalH F a A hfix)) := by
  have key : ∀ c ∈ cenU F a A hfix, ∀ x ∈ rootM F a A hfix l, c * x * c⁻¹ ∈ rootM F a A hfix l := by
    rintro c hc _ ⟨X, hX, rfl⟩
    rw [conj_slIn]
    exact ⟨_, actOn_mem_rootGroup hA hl hc hX, rfl⟩
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key c hc x
  · intro hx
    have h := key c⁻¹ ((cenU F a A hfix).inv_mem hc) _ hx
    simpa [mul_assoc] using h

omit [Finite F] in
theorem card_rootM (l : F) [Finite F] : Nat.card (rootM F a A hfix l) = Nat.card F := by
  rw [rootM, Subgroup.card_map_of_injective slIn_injective, card_rootGroup]

theorem rootM_inf_cenU (hodd : Odd (Nat.card F)) {l : F} (hl : l ^ 2 = -(a : F)) :
    rootM F a A hfix l ⊓ cenU F a A hfix = ⊥ := by
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  rw [eq_bot_iff]
  rintro _ ⟨⟨X, hX, rfl⟩, hXC⟩
  have hXT := (slIn_mem_cenU_iff X).mp hXC
  have : X ∈ rootGroup l ⊓ Torus F a := ⟨hX, hXT⟩
  rw [rootGroup_inf_torus a h2 hl, Subgroup.mem_bot] at this
  rw [this, map_one]
  exact Subgroup.one_mem _

theorem rootM_mem_signalizers (hodd : Odd (Nat.card F)) (hA : Odd (Nat.card A)) {p f : ℕ}
    (hp : p.Prime) (hcard : Nat.card F = p ^ f) {l : F} (hl : l ^ 2 = -(a : F)) :
    rootM F a A hfix l ∈ signalizers (layerM F a A hfix) (cenU F a A hfix) p := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨Subgroup.map_le_range _ _, IsPGroup.of_card (n := f) ?_,
    cenU_le_normalizer_rootM hA hl, rootM_inf_cenU hodd hl⟩
  rw [card_rootM, hcard]

theorem layerM_eq_sup (hodd : Odd (Nat.card F)) {l : F} (hl0 : l ≠ 0) :
    layerM F a A hfix = rootM F a A hfix l ⊔ rootM F a A hfix (-l) := by
  rw [rootM, rootM, ← Subgroup.map_sup,
    rootGroup_sup_neg (OddFieldSL2.two_ne_zero_of_odd_card F hodd) hl0, ← MonoidHom.range_eq_map]
  rfl

theorem rootM_ne (hodd : Odd (Nat.card F)) {l : F} (hl0 : l ≠ 0) :
    rootM F a A hfix l ≠ rootM F a A hfix (-l) := by
  intro h
  apply rootGroup_ne_neg (OddFieldSL2.two_ne_zero_of_odd_card F hodd) hl0
  exact Subgroup.map_injective slIn_injective h

theorem conjSub_rootM (hA : Odd (Nat.card A)) {l : F} (hl : l ^ 2 = -(a : F))
    {h : OriginalH F a A hfix}
    (hh : h * originalU F a A hfix * h⁻¹ = originalZ F a A hfix * originalU F a A hfix) :
    TotallyInverted.conjSub h (rootM F a A hfix l) = rootM F a A hfix (-l) := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hl' : (-l) ^ 2 = -(a : F) := by rw [neg_sq]; exact hl
  set X := h.left.left with hXdef
  set k : OriginalH F a A hfix :=
    SemidirectProduct.inl (SemidirectProduct.inr h.left.right) * SemidirectProduct.inr h.right
    with hkdef
  have hhk : h = originalSlInH F a A hfix X * k := by
    rw [hkdef, ← mul_assoc]
    exact decomp h
  have hkC : k ∈ cenU F a A hfix := by
    rw [mem_cenU_iff]
    change (1 : SL F) * MatrixCoverData.action F a h.left.right
      (originalFieldAction F a A hfix 1 1).left ∈ Torus F a
    simp only [map_one, one_mul]
    rw [show ((1 : MatrixCoverData.M F a)).left = 1 from rfl, map_one]
    exact Subgroup.one_mem _
  have hku : k * originalU F a A hfix * k⁻¹ = originalU F a A hfix := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hkC
    rw [this, mul_inv_cancel_right]
  have hXu : originalSlInH F a A hfix X * originalU F a A hfix *
      (originalSlInH F a A hfix X)⁻¹ = originalZ F a A hfix * originalU F a A hfix := by
    rw [← hh, hhk]
    calc originalSlInH F a A hfix X * originalU F a A hfix * (originalSlInH F a A hfix X)⁻¹ =
        originalSlInH F a A hfix X * (k * originalU F a A hfix * k⁻¹) *
          (originalSlInH F a A hfix X)⁻¹ := by rw [hku]
      _ = originalSlInH F a A hfix X * k * originalU F a A hfix *
          (originalSlInH F a A hfix X * k)⁻¹ := by group
  have hβ : beta F a X⁻¹ = X⁻¹ * OddFieldSL2.minusIdentity F := by
    have h1 : originalSlInH F a A hfix X * originalSlInH F a A hfix (beta F a X⁻¹) =
        originalZ F a A hfix := by
      rw [← conj_u_slIn, map_inv]
      calc originalSlInH F a A hfix X * (originalU F a A hfix *
            (originalSlInH F a A hfix X)⁻¹ * (originalU F a A hfix)⁻¹) =
          (originalSlInH F a A hfix X * originalU F a A hfix *
            (originalSlInH F a A hfix X)⁻¹) * (originalU F a A hfix)⁻¹ := by group
        _ = originalZ F a A hfix := by rw [hXu, mul_inv_cancel_right]
    rw [originalZ_eq, ← map_mul] at h1
    have h2 := slIn_injective h1
    rw [← h2, inv_mul_cancel_left]
  have hβX : beta F a X = OddFieldSL2.minusIdentity F * X := by
    have hc : Commute (OddFieldSL2.minusIdentity F) X⁻¹ :=
      (Subgroup.mem_center_iff.mp (OddFieldSL2.minusIdentity_mem_center F) X⁻¹).symm
    have h3 : beta F a X = (beta F a X⁻¹)⁻¹ := by rw [map_inv, inv_inv]
    rw [h3, hβ, _root_.mul_inv_rev, inv_inv,
      show (OddFieldSL2.minusIdentity F)⁻¹ = OddFieldSL2.minusIdentity F from
        inv_eq_of_mul_eq_one_left (by
          rw [← pow_two]; exact OddFieldSL2.minusIdentity_square F)]
  have hanti := (beta_eq_neg_iff a X).mp hβX
  have hle : TotallyInverted.conjSub h (rootM F a A hfix l) ≤ rootM F a A hfix (-l) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨Y, hY, rfl⟩ := hy
    change h * originalSlInH F a A hfix Y * h⁻¹ ∈ rootM F a A hfix (-l)
    rw [hhk]
    have hkY : k * originalSlInH F a A hfix Y * k⁻¹ =
        originalSlInH F a A hfix (actOn k Y) := conj_slIn k Y
    have hkYm : actOn k Y ∈ rootGroup l := actOn_mem_rootGroup hA hl hkC hY
    rw [show originalSlInH F a A hfix X * k * originalSlInH F a A hfix Y *
          (originalSlInH F a A hfix X * k)⁻¹ =
        originalSlInH F a A hfix X * (k * originalSlInH F a A hfix Y * k⁻¹) *
          (originalSlInH F a A hfix X)⁻¹ by group, hkY, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, anticomm_conj_mem_rootGroup a hl hanti hkYm, rfl⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [card_rootM, TotallyInverted.conjSub,
    Subgroup.card_map_of_injective (MulAut.conj h).injective, card_rootM]

theorem signalizer_le_rootM_or (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hq : 7 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {l : F} (hl : l ^ 2 = -(a : F))
    {X : Subgroup (OriginalH F a A hfix)}
    (hX : X ∈ signalizers (layerM F a A hfix) (cenU F a A hfix) p) :
    X ≤ rootM F a A hfix l ∨ X ≤ rootM F a A hfix (-l) := by
  have h2 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨w, hwT, hwxy⟩ := exists_generic_torus hodd ha hq
  apply le_or_le_of_forall_mem_or_mem
  intro x hx
  obtain ⟨Y, rfl⟩ := hX.1 hx
  by_cases hY1 : Y = 1
  · left
    rw [hY1, map_one]
    exact Subgroup.one_mem _
  obtain ⟨hinv, hYo, hcomm⟩ := layer_signalizer_elements hp hp2 hX hx
  obtain ⟨l', hl', hYl'⟩ := inverted_odd_mem_rootGroup a h2 hinv hY1 hYo hwT hwxy (hcomm w hwT)
  have : (l' - l) * (l' + l) = 0 := by linear_combination hl' - hl
  rcases mul_eq_zero.mp this with h | h
  · left
    exact ⟨Y, by rwa [show l' = l by linear_combination h] at hYl', rfl⟩
  · right
    exact ⟨Y, by rwa [show l' = -l by linear_combination h] at hYl', rfl⟩

theorem rootM_irreducible (hodd : Odd (Nat.card F)) {l : F} (hl : l ^ 2 = -(a : F))
    (X : Subgroup (OriginalH F a A hfix)) (hX : X ≤ rootM F a A hfix l)
    (hCX : cenU F a A hfix ≤ Subgroup.normalizer (X : Set (OriginalH F a A hfix))) :
    X = ⊥ ∨ X = rootM F a A hfix l := by
  set X' : Subgroup (SL F) := X.comap (originalSlInH F a A hfix) with hX'
  have hX'le : X' ≤ rootGroup l := by
    intro Y hY
    obtain ⟨Z, hZ, hZY⟩ := hX hY
    rw [← slIn_injective hZY]
    exact hZ
  have hnorm : ∀ τ ∈ Torus F a, ∀ x ∈ X', τ * x * τ⁻¹ ∈ X' := by
    intro τ hτ x hx
    have hτC := (slIn_mem_cenU_iff (hfix := hfix) τ).mpr hτ
    change originalSlInH F a A hfix (τ * x * τ⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hCX hτC) _).mp hx
  have hXmap : X = X'.map (originalSlInH F a A hfix) := by
    rw [hX', Subgroup.map_comap_eq, inf_of_le_right (hX.trans (Subgroup.map_le_range _ _))]
  rcases rootGroup_irreducible hodd a hl X' hX'le hnorm with h | h
  · left
    rw [hXmap, h, Subgroup.map_bot]
  · right
    rw [hXmap, h]
    rfl

omit [Finite F] in
theorem layerM_sup_cenU : layerM F a A hfix ⊔ cenU F a A hfix = ⊤ := by
  rw [eq_top_iff]
  intro m _
  rw [decomp m, mul_assoc]
  refine Subgroup.mul_mem_sup ⟨_, rfl⟩ ?_
  rw [mem_cenU_iff]
  change (1 : SL F) * MatrixCoverData.action F a m.left.right
    (originalFieldAction F a A hfix 1 1).left ∈ Torus F a
  simp only [map_one, one_mul]
  rw [show ((1 : MatrixCoverData.M F a)).left = 1 from rfl, map_one]
  exact Subgroup.one_mem _

omit [Finite F] in
theorem exists_cenU_factor (m : OriginalH F a A hfix) :
    ∃ k ∈ cenU F a A hfix, m = originalSlInH F a A hfix m.left.left * k := by
  refine ⟨SemidirectProduct.inl (SemidirectProduct.inr m.left.right) *
    SemidirectProduct.inr m.right, ?_, by rw [← mul_assoc]; exact decomp m⟩
  rw [mem_cenU_iff]
  change (1 : SL F) * MatrixCoverData.action F a m.left.right
    (originalFieldAction F a A hfix 1 1).left ∈ Torus F a
  simp only [map_one, one_mul]
  rw [show ((1 : MatrixCoverData.M F a)).left = 1 from rfl, map_one]
  exact Subgroup.one_mem _

theorem relIndex_torus_comap {B : Subgroup (OriginalH F a A hfix)} (hCB : cenU F a A hfix ≤ B) :
    (Torus F a).relIndex (B.comap (originalSlInH F a A hfix)) = (cenU F a A hfix).relIndex B := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  have hMn : (layerM F a A hfix).Normal := layerM_normal
  have h1 : (Torus F a).relIndex (B.comap (originalSlInH F a A hfix)) =
      (cenU F a A hfix).relIndex (B ⊓ layerM F a A hfix) := by
    rw [torus_eq_comap, Subgroup.relIndex_comap, Subgroup.map_comap_eq, inf_comm]
    rfl
  have htop : layerM F a A hfix ⊔ cenU F a A hfix = ⊤ := layerM_sup_cenU
  have hBtop : B ⊔ layerM F a A hfix = ⊤ := by
    rw [eq_top_iff, ← htop, sup_comm (layerM F a A hfix)]
    exact sup_le_sup_right hCB _
  have hCtop : cenU F a A hfix ⊔ layerM F a A hfix = ⊤ := by rw [sup_comm]; exact htop
  have hMB : (layerM F a A hfix).relIndex B = (layerM F a A hfix).relIndex (cenU F a A hfix) := by
    rw [← Subgroup.relIndex_sup_right B (layerM F a A hfix),
      ← Subgroup.relIndex_sup_right (cenU F a A hfix) (layerM F a A hfix), hBtop, hCtop]
  have e1 := Subgroup.relIndex_inf_mul_relIndex (cenU F a A hfix) (layerM F a A hfix) B
  have e2 := Subgroup.relIndex_inf_mul_relIndex (layerM F a A hfix) (cenU F a A hfix) B
  rw [inf_comm (layerM F a A hfix) (cenU F a A hfix), inf_of_le_left hCB] at e2
  rw [inf_comm (layerM F a A hfix) B, ← e2, hMB] at e1
  rw [h1]
  have hne : (layerM F a A hfix).relIndex (cenU F a A hfix) ≠ 0 := by
    intro h0
    have hd := Subgroup.relIndex_dvd_card (layerM F a A hfix) (cenU F a A hfix)
    rw [h0] at hd
    exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd hd)
  rw [mul_comm ((layerM F a A hfix).relIndex (cenU F a A hfix))] at e1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) e1

theorem permutable_model_cases (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a)
    (hq : 7 ≤ Nat.card F) :
    ∀ U : Subgroup (OriginalH F a A hfix), Odd (Nat.card U) →
      (U : Set (OriginalH F a A hfix)) * (cenU F a A hfix : Set (OriginalH F a A hfix)) =
        (cenU F a A hfix : Set (OriginalH F a A hfix)) * (U : Set (OriginalH F a A hfix)) →
      U ≤ cenU F a A hfix ∨
        ∃ l : F, l ^ 2 = -(a : F) ∧ U ≤ cenU F a A hfix ⊔ rootM F a A hfix l := by
  have := finite_originalH (a := a) (A := A) (hfix := hfix)
  intro U hUodd hUC
  set Cc := cenU F a A hfix with hCc
  set Mm := layerM F a A hfix with hMm
  set B : Subgroup (OriginalH F a A hfix) := U ⊔ Cc with hB
  set K : Subgroup (SL F) := B.comap (originalSlInH F a A hfix) with hK
  have hCB : Cc ≤ B := le_sup_right
  have hTK : Torus F a ≤ K := by
    intro τ hτ
    exact hCB ((slIn_mem_cenU_iff τ).mpr hτ)
  have hidx : Odd ((Torus F a).relIndex K) := by
    rw [hK, relIndex_torus_comap hCB]
    exact hUodd.of_dvd_nat (relIndex_sup_dvd_card_of_permute hUC)
  have hβK : ∀ x ∈ K, beta F a x ∈ K := by
    intro x hx
    change originalSlInH F a A hfix (beta F a x) ∈ B
    rw [← conj_u_slIn]
    exact B.mul_mem (B.mul_mem (hCB u_mem_cenU) hx) (B.inv_mem (hCB u_mem_cenU))
  have hUfac : ∀ x ∈ U, x.left.left ∈ K ∧
      ∃ k ∈ Cc, x = originalSlInH F a A hfix x.left.left * k := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := exists_cenU_factor x
    refine ⟨?_, k, hk, hxk⟩
    change originalSlInH F a A hfix x.left.left ∈ B
    have : originalSlInH F a A hfix x.left.left = x * k⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact hxk.symm
    rw [this]
    exact B.mul_mem (le_sup_left (a := U) hx) (B.inv_mem (hCB hk))
  rcases torus_overgroup_structure hodd a ha hq hTK hidx hβK with hKT | ⟨l, hl, hKl⟩
  · left
    intro x hx
    obtain ⟨hxK, k, hk, hxk⟩ := hUfac x hx
    rw [hxk]
    refine Cc.mul_mem ?_ hk
    exact (slIn_mem_cenU_iff _).mpr (hKT hxK)
  · refine Or.inr ⟨l, hl, ?_⟩
    intro x hx
    obtain ⟨hxK, k, hk, hxk⟩ := hUfac x hx
    rw [hxk]
    refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_left hk)
    have hmem := Subgroup.mem_map_of_mem (originalSlInH F a A hfix) (hKl hxK)
    rw [Subgroup.map_sup] at hmem
    have hle : (Torus F a).map (originalSlInH F a A hfix) ⊔ rootM F a A hfix l ≤
        Cc ⊔ rootM F a A hfix l := by
      refine sup_le_sup ?_ le_rfl
      rintro _ ⟨τ, hτ, rfl⟩
      exact (slIn_mem_cenU_iff τ).mpr hτ
    exact hle hmem

omit [Finite F] in
theorem bot_mem_signalizers (p : ℕ) :
    (⊥ : Subgroup (OriginalH F a A hfix)) ∈
      signalizers (layerM F a A hfix) (cenU F a A hfix) p := by
  refine ⟨bot_le, IsPGroup.of_bot, ?_, bot_inf_eq _⟩
  intro c _
  rw [Subgroup.mem_normalizer_iff]
  intro g
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl
    group
  · intro h
    have h' : g = c⁻¹ * (c * g * c⁻¹) * c := by group
    rw [h', h]
    group

theorem permutable_model (hodd : Odd (Nat.card F)) (ha : ¬IsSquare a) (hq : 7 ≤ Nat.card F)
    (hA : Odd (Nat.card A)) {p f : ℕ} (hp : p.Prime) (hcard : Nat.card F = p ^ f) :
    ∀ U : Subgroup (OriginalH F a A hfix), Odd (Nat.card U) →
      (U : Set (OriginalH F a A hfix)) * (cenU F a A hfix : Set (OriginalH F a A hfix)) =
        (cenU F a A hfix : Set (OriginalH F a A hfix)) * (U : Set (OriginalH F a A hfix)) →
      ∃ (p' : ℕ) (X : Subgroup (OriginalH F a A hfix)), p'.Prime ∧
        X ∈ signalizers (layerM F a A hfix) (cenU F a A hfix) p' ∧
        U ≤ cenU F a A hfix ⊔ X := by
  intro U hUodd hUC
  rcases permutable_model_cases hodd ha hq U hUodd hUC with h | ⟨l, hl, h⟩
  · exact ⟨p, ⊥, hp, bot_mem_signalizers p, h.trans le_sup_left⟩
  · exact ⟨p, rootM F a A hfix l, hp, rootM_mem_signalizers hodd hA hp hcard hl, h⟩

end

end CFSG.Semidihedral.AllPrime.QDTI
