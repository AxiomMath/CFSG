module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverTorus

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace UnitaryCoord

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K]

theorem mul_comm_iff {n : ℕ} (J : HermitianForm n K) (z w : hermitianUnipotentCoord J) :
    w * z = z * w ↔ w.1.1 * J.conj z.1.1 = z.1.1 * J.conj w.1.1 := by
  constructor
  · intro h
    have h2 := congrArg (fun v : hermitianUnipotentCoord J => v.1.2) h
    change w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1 = z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 at h2
    linear_combination -h2
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · change w.1.1 + z.1.1 = z.1.1 + w.1.1
      ring
    · change w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1 = z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1
      rw [h]
      ring

theorem inv_mul_mul_fst {n : ℕ} (J : HermitianForm n K) (c v : hermitianUnipotentCoord J) :
    (c⁻¹ * v * c).1.1 = v.1.1 := by
  change -c.1.1 + v.1.1 + c.1.1 = v.1.1
  ring

theorem inv_mul_mul_snd {n : ℕ} (J : HermitianForm n K) (c v : hermitianUnipotentCoord J) :
    (c⁻¹ * v * c).1.2 = v.1.2 + c.1.1 * J.conj v.1.1 - v.1.1 * J.conj c.1.1 := by
  change J.conj c.1.2 + v.1.2 - -c.1.1 * J.conj v.1.1 + c.1.2 -
    (-c.1.1 + v.1.1) * J.conj c.1.1 = _
  linear_combination c.2

theorem exists_add_conj_eq [Finite K] [CharP K 2] {n : ℕ} (J : HermitianForm n K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q) {t : K}
    (ht : J.conj t = t) : ∃ u : K, u + J.conj u = t := by
  classical
  let tr : K →+ K :=
    { toFun := fun u => u + J.conj u
      map_zero' := by simp
      map_add' := fun u v => by
        rw [map_add]
        ring }
  have hmemker : ∀ u : K, u ∈ tr.ker ↔ J.conj u = u := by
    intro u
    rw [AddMonoidHom.mem_ker]
    change u + J.conj u = 0 ↔ _
    rw [CharTwo.add_eq_zero]
    exact eq_comm
  have hker : Nat.card tr.ker = q := by
    rw [← hfixed]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmemker)
  have hqpos : 0 < q := by
    have h := Nat.card_pos (α := K)
    rw [hcard] at h
    rcases Nat.eq_zero_or_pos q with hq | hq
    · rw [hq] at h
      simp at h
    · exact hq
  have hrange : Nat.card tr.range = q := by
    have h := AddSubgroup.card_ker_mul_card_range tr
    rw [hker, hcard, sq] at h
    exact Nat.eq_of_mul_eq_mul_left hqpos h
  have hsub : (tr.range : Set K) ⊆ {x | J.conj x = x} := by
    rintro _ ⟨u, rfl⟩
    change J.conj (u + J.conj u) = u + J.conj u
    rw [map_add, J.conj_involutive, add_comm]
  have heq : (tr.range : Set K) = {x | J.conj x = x} := by
    apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    have h1 : Nat.card ({x | J.conj x = x} : Set K) = q := hfixed
    have h2 : Nat.card (tr.range : Set K) = q := hrange
    rw [h1, h2]
  have htr : t ∈ (tr.range : Set K) := by
    rw [heq]
    exact ht
  obtain ⟨u, hu⟩ := htr
  exact ⟨u, hu⟩

theorem card_firstCoord_ker [CharP K 2] (J : HermitianForm 3 K) (q : ℕ)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) :
    Nat.card (unitaryCoverFirstCoord J).ker = q := by
  have hfixcard : Nat.card (unitaryCoverFixedField J) = q := by
    let c : unitaryCoverFixedField J ≃ {x : K // J.conj x = x} :=
      { toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr c).trans hfixed
  exact (Nat.card_congr (unitaryCoverZeroFirstEquiv J).toEquiv).trans
    ((Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (unitaryCoverFixedField J) ≃ _)).trans hfixcard)

theorem exists_inv_mul_mul_eq [Finite K] [CharP K 2] (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (v w : hermitianUnipotentCoord J)
    (hvw : v.1.1 = w.1.1) (hv : v.1.1 ≠ 0) : ∃ c : hermitianUnipotentCoord J, c⁻¹ * v * c = w := by
  have ht : J.conj (w.1.2 - v.1.2) = w.1.2 - v.1.2 := by
    have hv2 := v.2
    have hw2 := w.2
    rw [hvw] at hv2
    have h2 := CharTwo.add_self_eq_zero (w.1.2 - v.1.2)
    rw [map_sub]
    linear_combination hw2 - hv2 - h2
  obtain ⟨u, hu⟩ := exists_add_conj_eq J q hcard hfixed ht
  have hcv : J.conj v.1.1 ≠ 0 := (map_ne_zero J.conj).2 hv
  obtain ⟨c, hc⟩ := unitaryCoverFirstCoord_surjective J q hcard hfixed hJ
    (Multiplicative.ofAdd (u / J.conj v.1.1))
  have hc1 : c.1.1 = u / J.conj v.1.1 := congrArg Multiplicative.toAdd hc
  refine ⟨c, Subtype.ext (Prod.ext ?_ ?_)⟩
  · rw [inv_mul_mul_fst]
    exact hvw
  · have e1 : u / J.conj v.1.1 * J.conj v.1.1 = u := div_mul_cancel₀ u hcv
    have e2 : v.1.1 * (J.conj u / v.1.1) = J.conj u := by field_simp
    rw [inv_mul_mul_snd, hc1, map_div₀, J.conj_involutive, e1, e2]
    have h2 := CharTwo.add_self_eq_zero (J.conj u)
    linear_combination hu - h2

theorem card_centralizer_le [Finite K] [CharP K 2] (J : HermitianForm 3 K) (q : ℕ)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (z : hermitianUnipotentCoord J)
    (hz : z.1.1 ≠ 0) :
    Nat.card (Subgroup.centralizer ({z} : Set (hermitianUnipotentCoord J))) ≤ q ^ 2 := by
  set C := Subgroup.centralizer ({z} : Set (hermitianUnipotentCoord J)) with hC
  let φ := (unitaryCoverFirstCoord J).comp C.subtype
  have hkr := Subgroup.card_ker_mul_card_range φ
  have hker : Nat.card φ.ker ≤ q := by
    let ι : φ.ker → (unitaryCoverFirstCoord J).ker := fun w =>
      ⟨((w : C) : hermitianUnipotentCoord J), MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp w.2)⟩
    have hι : Function.Injective ι := by
      intro w w' h
      have h1 := congrArg Subtype.val h
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    calc Nat.card φ.ker ≤ Nat.card (unitaryCoverFirstCoord J).ker :=
          Nat.card_le_card_of_injective ι hι
      _ = q := card_firstCoord_ker J q hfixed
  have hcz : J.conj z.1.1 ≠ 0 := (map_ne_zero J.conj).2 hz
  have hfix : ∀ r : φ.range,
      J.conj (Multiplicative.toAdd (r : Multiplicative K) * J.conj z.1.1) =
        Multiplicative.toAdd (r : Multiplicative K) * J.conj z.1.1 := by
    rintro ⟨r, w, rfl⟩
    have hw : ((w : C) : hermitianUnipotentCoord J) * z = z * (w : C) :=
      Subgroup.mem_centralizer_singleton_iff.mp w.2
    have h := (mul_comm_iff J z (w : C)).mp hw
    change J.conj (((w : C) : hermitianUnipotentCoord J).1.1 * J.conj z.1.1) =
      ((w : C) : hermitianUnipotentCoord J).1.1 * J.conj z.1.1
    rw [map_mul, J.conj_involutive, h, mul_comm]
  have hrange : Nat.card φ.range ≤ q := by
    let ι : φ.range → {x : K // J.conj x = x} := fun r =>
      ⟨Multiplicative.toAdd (r : Multiplicative K) * J.conj z.1.1, hfix r⟩
    have hι : Function.Injective ι := by
      intro r r' h
      have h1 := congrArg Subtype.val h
      change Multiplicative.toAdd (r : Multiplicative K) * J.conj z.1.1 =
        Multiplicative.toAdd (r' : Multiplicative K) * J.conj z.1.1 at h1
      exact Subtype.ext (Multiplicative.toAdd.injective (mul_right_cancel₀ hcz h1))
    rw [← hfixed]
    exact Nat.card_le_card_of_injective ι hι
  calc Nat.card C = Nat.card φ.ker * Nat.card φ.range := hkr.symm
    _ ≤ q * q := Nat.mul_le_mul hker hrange
    _ = q ^ 2 := (sq q).symm

theorem hermitianTorusAction_fst_eq (J : HermitianForm 3 K) (k : Kˣ)
    (z : hermitianUnipotentCoord J) :
    (hermitianTorusAction J k z).1.1 = z.1.1 * (unitaryCoverScalar J k : K) := by
  rw [hermitianTorusAction_fst, unitaryCoverScalar_val]
  ring

end UnitaryCoord

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
