module

public import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverAltBlock

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup

theorem cycleType_swap_mul_swap {a b c d : Fin 10} (h : [a, b, c, d].Nodup) :
    (Equiv.swap a b * Equiv.swap c d).cycleType = {2, 2} := by
  have hab : a ≠ b := by
    intro hab
    simp [hab] at h
  have hcd : c ≠ d := by
    intro hcd
    simp [hcd] at h
  rw [(Equiv.Perm.disjoint_swap_swap h).cycleType_mul, (Equiv.Perm.isCycle_swap hab).cycleType,
    (Equiv.Perm.isCycle_swap hcd).cycleType, Equiv.Perm.card_support_swap hab,
    Equiv.Perm.card_support_swap hcd]
  rfl

theorem a10DoubleTransLift :
    ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → center Y ≠ ⊥ →
      ∀ (e : Y ⧸ center Y ≃* alternatingGroup (Fin 10)) (y : Y) (a b c d : Fin 10),
        [a, b, c, d].Nodup →
        ((e (QuotientGroup.mk y) : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) =
          Equiv.swap a b * Equiv.swap c d →
        y ^ 2 ≠ 1 := by
  intro Y _ _ hq hZ e y a b c d hnd hy
  have : Group.IsPerfect Y := hq.1
  set η : Y →* alternatingGroup (Fin 10) := e.toMonoidHom.comp (QuotientGroup.mk' (center Y))
    with hηdef
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Y := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hle := OddStandard.GlueAlt.card_center_le_two_of_alt (by norm_num) e
  have hZ2 : Nat.card (center Y) = 2 := by
    have h1 : 1 < Nat.card (center Y) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
    omega
  have hK2 : IsPGroup 2 η.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  obtain ⟨x, z, hxη, -, hzc, hz1, -, hxx⟩ :=
    QuasithinUnique.Ch1.alt_cover_structure (m := 8) (by norm_num) η hη hker.le hK2 (hker ▸ hZ)
  have hw : ((η (x 0 * x 1) : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) =
      Equiv.swap 0 2 * Equiv.swap 1 3 := by
    rw [map_mul, hxη, hxη]
    exact LocalAnalysis.ComponentInitial.coe_altThreeCycle_mul (n := 8) (i := 0) (j := 1)
      (by decide)
  have hηy : ((η y : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) =
      Equiv.swap a b * Equiv.swap c d := hy
  have hconj : IsConj (η (x 0 * x 1)) (η y) := by
    apply alternatingGroup.isConj_of
    · rw [Equiv.Perm.isConj_iff_cycleType_eq, hw, hηy, cycleType_swap_mul_swap hnd,
        cycleType_swap_mul_swap (by decide)]
    · rw [hw]
      decide
  obtain ⟨σ, hσ⟩ := isConj_iff.mp hconj
  obtain ⟨g, rfl⟩ := hη σ
  set w := x 0 * x 1 with hwdef
  have hk : (g * w * g⁻¹)⁻¹ * y ∈ center Y := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hσ,
      inv_mul_cancel]
  have hk2 : ((g * w * g⁻¹)⁻¹ * y) ^ 2 = 1 := by
    have h := congrArg Subtype.val
      (pow_card_eq_one' (G := ↥(center Y)) (x := ⟨(g * w * g⁻¹)⁻¹ * y, hk⟩))
    rw [hZ2, SubmonoidClass.coe_pow, OneMemClass.coe_one] at h
    exact h
  have hkc : Commute (g * w * g⁻¹) ((g * w * g⁻¹)⁻¹ * y) := mem_center_iff.mp hk _
  have hw2 : w ^ 2 = z := hxx 0 1 (by decide)
  have hgz : g * z * g⁻¹ = z := by rw [mem_center_iff.mp hzc g, mul_inv_cancel_right]
  intro hy2
  apply hz1
  calc z = g * w ^ 2 * g⁻¹ := by rw [hw2, hgz]
    _ = (g * w * g⁻¹) ^ 2 := by rw [conj_pow]
    _ = (g * w * g⁻¹) ^ 2 * ((g * w * g⁻¹)⁻¹ * y) ^ 2 := by rw [hk2, mul_one]
    _ = (g * w * g⁻¹ * ((g * w * g⁻¹)⁻¹ * y)) ^ 2 := (hkc.mul_pow 2).symm
    _ = y ^ 2 := by rw [mul_inv_cancel_left]
    _ = 1 := hy2

end CFSG.ComponentClassification.GrSLit.L34Facts
