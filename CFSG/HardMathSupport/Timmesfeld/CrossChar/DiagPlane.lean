module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.DiagFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def DiagAbelianPlaneBalance : Prop :=
  ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 3 ≤ n → ∀ p : ℕ, p.Prime → p ≠ 2 →
    p ∣ Nat.card F - 1 → p ∣ n → ∀ A B : GL (Fin n) F, A * B = B * A →
      conjAut n F A ^ p = 1 → conjAut n F B ^ p = 1 → conjAut n F A ≠ 1 →
      conjAut n F B ∉ Subgroup.zpowers (conjAut n F A) →
      ∀ H : Subgroup (MulAut (projectiveSL n F)), innerAut (projectiveSL n F) ≤ H →
        Subgroup.closure {conjAut n F A, conjAut n F B} ≤
          Subgroup.normalizer (H : Set (MulAut (projectiveSL n F))) →
        localDeltaIn p H (Subgroup.closure {conjAut n F A, conjAut n F B}) = ⊥

section Lift

variable {n : ℕ} {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem glScalar_injective (hn : 0 < n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Fˣ →* GL (Fin n) F) := by
  intro c d h
  have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩) h
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at this
  exact Units.ext this

theorem exists_scalar_eq_commutator (hn : 3 ≤ n) {A B : GL (Fin n) F}
    (h : conjAut n F A * conjAut n F B = conjAut n F B * conjAut n F A) :
    ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c = A * B * A⁻¹ * B⁻¹ := by
  refine (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 ?_).2
  rw [map_one, mul_one, map_mul, map_mul, map_mul, map_inv, map_inv, h]
  group

theorem exists_commuting_lifts (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {D : Subgroup (MulAut (projectiveSL n F))} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 3) (hDl : D ≤ linearAutGroup n F) :
    ∃ A B : GL (Fin n) F, A * B = B * A ∧ conjAut n F A ∈ D ∧ conjAut n F B ∈ D ∧
      conjAut n F A ≠ 1 ∧ conjAut n F B ∉ Subgroup.zpowers (conjAut n F A) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hDfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  have hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact absurd hcard.symm (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'
  obtain ⟨⟨X, hXD⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD1
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hDl hXD)
  have hlift : ∀ y : D, ∃ B : GL (Fin n) F, conjAut n F B = y := fun y =>
    mem_linearAutGroup_iff.1 (hDl y.2)
  let L : D → GL (Fin n) F := fun y => Classical.choose (hlift y)
  have hL : ∀ y, conjAut n F (L y) = y := fun y => Classical.choose_spec (hlift y)
  have hsc : ∀ y : D, ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c = A * L y * A⁻¹ * (L y)⁻¹ :=
    fun y => exists_scalar_eq_commutator hn (by rw [hA, hL]; exact hcomm _ hXD _ y.2)
  let c : D → Fˣ := fun y => Classical.choose (hsc y)
  have hc : ∀ y, GeneralLinearGroup.scalar (Fin n) (c y) = A * L y * A⁻¹ * (L y)⁻¹ :=
    fun y => Classical.choose_spec (hsc y)
  have hcentral : ∀ (u : Fˣ) (M : GL (Fin n) F),
      GeneralLinearGroup.scalar (Fin n) u * M = M * GeneralLinearGroup.scalar (Fin n) u :=
    fun u M => GeneralLinearGroup.scalar_commute u M
  have hdiff : ∀ M N : GL (Fin n) F, conjAut n F M = conjAut n F N →
      ∃ s : Fˣ, GeneralLinearGroup.scalar (Fin n) s = M * N⁻¹ := fun M N h =>
    (eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 (by rw [map_one, mul_one, map_mul, map_inv,
      h, mul_inv_cancel])).2
  have hcomm_scalar : ∀ (s : Fˣ) (M : GL (Fin n) F),
      A * (GeneralLinearGroup.scalar (Fin n) s * M) * A⁻¹ *
        (GeneralLinearGroup.scalar (Fin n) s * M)⁻¹ = A * M * A⁻¹ * M⁻¹ := fun s M => by
    rw [← mul_assoc A, ← hcentral s A]
    calc GeneralLinearGroup.scalar (Fin n) s * A * M * A⁻¹ *
          (GeneralLinearGroup.scalar (Fin n) s * M)⁻¹
        = GeneralLinearGroup.scalar (Fin n) s * (A * M * A⁻¹ * M⁻¹) *
          (GeneralLinearGroup.scalar (Fin n) s)⁻¹ := by group
      _ = A * M * A⁻¹ * M⁻¹ := by rw [hcentral, mul_inv_cancel_right]
  let α : D →* Fˣ :=
    { toFun := c
      map_one' := by
        apply glScalar_injective (by omega : 0 < n)
        obtain ⟨s, hs⟩ := hdiff (L 1) 1 (by rw [hL, map_one]; rfl)
        rw [inv_one, mul_one] at hs
        rw [hc, map_one, ← hs, ← mul_one (GeneralLinearGroup.scalar (Fin n) s),
          hcomm_scalar]
        group
      map_mul' := fun y z => by
        apply glScalar_injective (by omega : 0 < n)
        obtain ⟨s, hs⟩ := hdiff (L (y * z)) (L y * L z) (by
          rw [map_mul, hL, hL, hL]; rfl)
        have hLyz : L (y * z) = GeneralLinearGroup.scalar (Fin n) s * (L y * L z) := by
          rw [hs, inv_mul_cancel_right]
        rw [map_mul, hc, hc, hc, hLyz, hcomm_scalar]
        have hz := hc z
        calc A * (L y * L z) * A⁻¹ * (L y * L z)⁻¹
            = (A * L y * A⁻¹ * (L y)⁻¹) * (L y * (A * L z * A⁻¹ * (L z)⁻¹) * (L y)⁻¹) := by
              group
          _ = (A * L y * A⁻¹ * (L y)⁻¹) * (A * L z * A⁻¹ * (L z)⁻¹) := by
              rw [← hz, ← hcentral (c z) (L y), mul_inv_cancel_right] }
  have hle := card_le_mul_card_ker' hp (fun h : D => Subtype.ext (hD.2 h h.2)) α
  have hker : p ^ 2 ≤ Nat.card α.ker := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card D ≤ p * (p ^ 2 - 1) := hle.trans (Nat.mul_le_mul_left _ (by omega))
    have h2 : p * (p ^ 2 - 1) < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left (by
      have := Nat.one_le_pow 2 p hp.pos
      omega) hp.pos
    rw [hcard, show p ^ 3 = p * p ^ 2 by ring] at h1
    omega
  obtain ⟨y, hyk, hyx⟩ : ∃ y ∈ α.ker, (y : MulAut (projectiveSL n F)) ∉ Subgroup.zpowers X := by
    by_contra hall
    push Not at hall
    have hXp : X ^ p = 1 := hD.2 X hXD
    have : Finite (Subgroup.zpowers X) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [Nat.card_zpowers]
      exact (orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.pos, hXp⟩)).ne'
    have h1 := Subgroup.card_le_of_le (show α.ker ≤ (Subgroup.zpowers X).comap D.subtype from
      fun y hy => hall y hy)
    have h2 : Nat.card ((Subgroup.zpowers X).comap D.subtype) ≤ p := by
      have e1 := Subgroup.card_le_of_le (Subgroup.map_comap_le D.subtype (Subgroup.zpowers X))
      rw [Subgroup.card_map_of_injective D.subtype_injective, Nat.card_zpowers] at e1
      exact e1.trans (orderOf_le_of_pow_eq_one hp.pos hXp)
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  refine ⟨A, L y, ?_, hA ▸ hXD, (hL y).symm ▸ y.2, ?_, ?_⟩
  · have h1 : GeneralLinearGroup.scalar (Fin n) (c y) = 1 := by
      have : c y = 1 := hyk
      rw [this, map_one]
    rw [hc] at h1
    have h2 : A * L y * A⁻¹ = L y := mul_inv_eq_one.1 h1
    calc A * L y = A * L y * A⁻¹ * A := by group
      _ = L y * A := by rw [h2]
  · rw [hA]
    exact fun h => hx1 (Subtype.ext h)
  · rw [hA, hL]
    exact hyx

end Lift

theorem diagLinearBalance_of_plane (h : DiagAbelianPlaneBalance) : DiagLinearBalance := by
  intro n F _ _ hn p hp hp2 hpF hpn D hD hcard hDl H hH hDH
  obtain ⟨A, B, hAB, hAD, hBD, hA1, hBA⟩ := exists_commuting_lifts hn hp hD hcard hDl
  have hED : Subgroup.closure {conjAut n F A, conjAut n F B} ≤ D := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hAD
    · exact hBD
  have hbot := h n F hn p hp hp2 hpF hpn A B hAB (hD.2 _ hAD) (hD.2 _ hBD) hA1 hBA H hH
    (hED.trans hDH)
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans hbot.le)

theorem crossCharFamCat_A_of_plane (h : DiagAbelianPlaneBalance)
    (h32 : CrossCharFamAt .A regimeAThreeTwo) : CrossCharFamCat .A :=
  crossCharFamCat_A_of_linear (diagLinearBalance_of_plane h) h32

end CFSG.HardMathSupport.Timmesfeld.CrossChar
