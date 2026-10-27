module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14Map

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal CFSG.Open Module

theorem input28_14_of_dispatch (hN : TvNormalizer) (hC : TvCentralized) :
    UniquenessMaximal.Input28_14 := by
  intro V _ _ hV X hX τ hτX hτ r W hW p hp hp2 B hBX hBel hBcard hBW
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero]
    exact hV _
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  set Φ := i285_Φ (V := V) with hΦ
  obtain ⟨φ, a, hφa, hφ, ha, hτeq⟩ := (isF2Transvection_iff _).1 (i285_isF2Transvection_Φ hV hτ)
  let S : i285_Setup (Additive V) :=
    ⟨X.map Φ.toMonoidHom, φ, a, hφa, hφ, ha, hτeq ▸ ⟨τ, hτX, rfl⟩, i285_hO2_Φ hX⟩
  have hSτ : S.τ = Φ τ := hτeq.symm
  have hW' : i285_Decomp S.X S.τ r (fun i => (W i).map Φ.toMonoidHom) := by
    have := (show i285_Decomp X τ r W from hW).map Φ
    rw [hSτ]
    exact this
  have hmax : ∀ B' : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive V)),
      B' ≤ S.X → IsElemAbelian p B' → Nat.card B' ≤ Nat.card (B.map Φ.toMonoidHom) := by
    intro B' hB'X hB'el
    have hE := isElemAbelian_map_equiv Φ.symm hB'el
    have hEX : B'.map Φ.symm.toMonoidHom ≤ X := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hB'X hx
      have : Φ.symm x = y := by rw [← hyx]; simp
      simpa [this] using hy
    have hEp : IsPGroup p (B'.map Φ.symm.toMonoidHom) := fun g =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hkr := CFSG.SectionRank.le_pRank hp1 hEX hE hk
    rw [Subgroup.card_map_of_injective Φ.symm.injective] at hk
    rw [Subgroup.card_map_of_injective Φ.injective, hBcard, hk]
    exact Nat.pow_le_pow_right hp.pos hkr
  have hBW' : B.map Φ.toMonoidHom ≤ Subgroup.normalizer
      (((fun i => (W i).map Φ.toMonoidHom) 0 : Subgroup _) : Set _) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp only [Subgroup.mem_map_equiv, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 (hBW hb) _
  obtain ⟨y', hy'W, Q', hQ'B, hQcard, hQcomm⟩ := i285_conc hN hC S hW' hp hp2
    (Subgroup.map_mono hBX) (isElemAbelian_map_equiv Φ hBel) hmax hBW'
  obtain ⟨y, hyW, rfl⟩ := hy'W
  set Q : Subgroup (MulAut V) := Q'.map Φ.symm.toMonoidHom with hQ
  have hQB : Q ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hbx⟩ := hQ'B hx
    have : Φ.symm x = b := by rw [← hbx]; simp
    simpa [this] using hb
  have hQel : IsElemAbelian p Q := ⟨⟨⟨fun x y => Subtype.ext (by
      have := hBel.1.1.comm ⟨x.1, hQB x.2⟩ ⟨y.1, hQB y.2⟩
      exact congrArg (fun z : ↥B => (z : MulAut V)) this)⟩⟩,
    fun x hx => hBel.2 x (hQB hx)⟩
  have hQp : IsPGroup p Q := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hQel.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hQcard' : Nat.card Q = Nat.card Q' := Subgroup.card_map_of_injective Φ.symm.injective
  have hBcard' : Nat.card (B.map Φ.toMonoidHom) = p ^ CFSG.Open.pRank p X := by
    rw [Subgroup.card_map_of_injective Φ.injective, hBcard]
  have hkr : k ≤ CFSG.Open.pRank p Q := CFSG.SectionRank.le_pRank hp1 le_rfl hQel hk
  have hmk : CFSG.Open.pRank p X ≤ k + 1 := by
    have h1 : p ^ CFSG.Open.pRank p X ≤ p ^ (k + 1) := by
      rw [← hBcard', pow_succ, mul_comm, ← hk, hQcard']
      exact hQcard
    exact (Nat.pow_le_pow_iff_right hp1).1 h1
  refine ⟨y, hyW, ?_⟩
  have hzX : y⁻¹ * τ * y ∈ X := X.mul_mem (X.mul_mem (X.inv_mem (hW.2.1 0 hyW)) hτX) (hW.2.1 0 hyW)
  have hcom : ∀ q ∈ Q, q * (y⁻¹ * τ * y) = (y⁻¹ * τ * y) * q := by
    rintro _ ⟨q', hq', rfl⟩
    apply Φ.injective
    have := hQcomm q' hq'
    rw [hSτ] at this
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply] at this ⊢
    exact this
  have hzN : y⁻¹ * τ * y ∈ Subgroup.normalizer (Q : Set (MulAut V)) := by
    set z := y⁻¹ * τ * y with hz
    have hzfix : ∀ w ∈ Q, z * w * z⁻¹ = w := fun w hw => by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hcom w hw).symm
    have hzfix' : ∀ w ∈ Q, z⁻¹ * w * z = w := fun w hw => by
      have := hzfix w hw
      calc z⁻¹ * w * z = z⁻¹ * (z * w * z⁻¹) * z := by rw [this]
        _ = w := by group
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · rw [hzfix q hq]
      exact hq
    · have h1 := hzfix' _ hq
      rw [show z⁻¹ * (z * q * z⁻¹) * z = q by group] at h1
      rw [h1]
      exact hq
  exact Subgroup.mem_iSup_of_mem Q (Subgroup.mem_iSup_of_mem ⟨hQB, by omega⟩ ⟨hzX, hzN⟩)

end CFSG.HardMathSupport.Solomon.Coordinator
