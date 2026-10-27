module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsSuzuki
public import CFSG.StronglyEmbedded.BenderUnitaryCenter

public section

namespace CFSG.ProperTwoGeneratedCore.BenderFacts

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

variable {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K) {q : ℕ}
  (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q)
include hcard hfixed

theorem card_add_conj_eq [CharP K 2] {r : K} (hr : J.conj r = r) :
    Nat.card {b : K // b + J.conj b = r} = q := by
  classical
  have := Fintype.ofFinite K
  let T : K →+ K :=
    { toFun := fun b => b + J.conj b
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add]; abel }
  obtain ⟨b₀, hb₀⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed r hr
  have h := AddMonoidHom.card_fiber_eq_of_mem_range T ⟨b₀, hb₀⟩ ⟨0, map_zero T⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (Finset.univ.filter fun b => T b = r).card = q
  rw [h, ← hfixed, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, T, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  rw [CharTwo.add_eq_zero, eq_comm]

theorem card_mul_conj_eq {r : K} (hr : J.conj r = r) (hr0 : r ≠ 0) :
    Nat.card {a : K // a * J.conj a = r} = q + 1 := by
  classical
  have := Fintype.ofFinite K
  let N : Kˣ →* Kˣ :=
    { toFun := fun u => u * Units.map (J.conj : K →* K) u
      map_one' := by simp
      map_mul' := fun u v => by simp only [map_mul]; exact mul_mul_mul_comm u v _ _ }
  have hN : ∀ u : Kˣ, (N u : K) = u * J.conj u := fun u => rfl
  have hrange : ∀ u : Kˣ, u ∈ N.range ↔ J.conj (u : K) = u := by
    intro u
    constructor
    · rintro ⟨v, rfl⟩
      rw [hN, map_mul, J.conj_involutive, mul_comm]
    · intro hu
      obtain ⟨b, hb0, hb⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed u hu u.ne_zero
      exact ⟨Units.mk0 b hb0, Units.ext (by rw [hN, Units.val_mk0, hb])⟩
  have hq : 1 < q := by
    have h1 := Finite.one_lt_card (α := K)
    rw [hcard] at h1
    by_contra! hq
    interval_cases q <;> simp at h1
  have hcardRange : Nat.card N.range = q - 1 := by
    have e : N.range ≃ {x : K // J.conj x = x ∧ x ≠ 0} :=
      { toFun := fun u => ⟨u.1, (hrange u.1).mp u.2, u.1.ne_zero⟩
        invFun := fun x => ⟨Units.mk0 x.1 x.2.2, (hrange _).mpr x.2.1⟩
        left_inv := fun u => Subtype.ext (Units.ext rfl)
        right_inv := fun x => Subtype.ext rfl }
    rw [Nat.card_congr e, ← hfixed, Nat.card_eq_fintype_card, Fintype.card_subtype,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hset : (Finset.univ.filter fun x : K => J.conj x = x) =
        insert 0 (Finset.univ.filter fun x : K => J.conj x = x ∧ x ≠ 0) := by
      ext x
      by_cases hx : x = 0 <;> simp [hx]
    rw [hset, Finset.card_insert_of_notMem (by simp)]
    rfl
  have hker : Nat.card N.ker = q + 1 := by
    have h := Subgroup.card_ker_mul_card_range N
    rw [hcardRange, Nat.card_units, hcard] at h
    have h' : (q + 1) * (q - 1) = q ^ 2 - 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_two]
      ring_nf
      omega
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q - 1) (h.trans h'.symm)
  have hfib := MonoidHom.card_fiber_eq_of_mem_range N
    (x := Units.mk0 r hr0) (y := 1) ((hrange _).mpr hr) ⟨1, map_one N⟩
  have e : {a : K // a * J.conj a = r} ≃ {u : Kˣ // N u = Units.mk0 r hr0} :=
    { toFun := fun a => ⟨Units.mk0 a.1 (fun h => hr0 (by rw [← a.2, h, zero_mul])),
        Units.ext (by rw [hN, Units.val_mk0, Units.val_mk0, a.2])⟩
      invFun := fun u => ⟨u.1, by rw [← hN, u.2, Units.val_mk0]⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun u => Subtype.ext (Units.ext rfl) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, hfib, ← hker,
    Nat.card_eq_fintype_card]
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun u => by simp [MonoidHom.mem_ker])

theorem card_sq_eq_coord [CharP K 2] {w : hermitianUnipotentCoord J} (hw0 : w.1.1 = 0)
    (hw : w.1.2 ≠ 0) : Nat.card {z : hermitianUnipotentCoord J // z ^ 2 = w} = q * (q + 1) := by
  have hr : J.conj w.1.2 = w.1.2 := conj_snd_of_fst_eq_zero J hw0
  have hsq : ∀ z : hermitianUnipotentCoord J, z ^ 2 = w ↔ z.1.1 * J.conj z.1.1 = w.1.2 := by
    intro z
    constructor
    · intro h
      rw [← snd_pow_two, h]
    · intro h
      exact coord_ext (by rw [fst_pow_two, hw0]) (by rw [snd_pow_two, h])
  have e : {z : hermitianUnipotentCoord J // z ^ 2 = w} ≃
      {a : K // a * J.conj a = w.1.2} × {b : K // b + J.conj b = w.1.2} :=
    { toFun := fun z => (⟨z.1.1.1, (hsq z.1).mp z.2⟩, ⟨z.1.1.2, by
        have h := z.1.2
        rw [(hsq z.1).mp z.2] at h
        exact CharTwo.add_eq_zero.mp h⟩)
      invFun := fun p => ⟨⟨(p.1.1, p.2.1), by
        change p.2.1 + J.conj p.2.1 + p.1.1 * J.conj p.1.1 = 0
        rw [p.1.2, p.2.2, CharTwo.add_self_eq_zero]⟩, (hsq _).mpr p.1.2⟩
      left_inv := fun z => Subtype.ext (coord_ext rfl rfl)
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_mul_conj_eq J hcard hfixed hr hw,
    card_add_conj_eq J hcard hfixed hr, mul_comm]

theorem card_sq_eq_coord_of_sq_eq_one [CharP K 2] {w : hermitianUnipotentCoord J} (hw1 : w ≠ 1)
    (hw2 : w ^ 2 = 1) : Nat.card {z : hermitianUnipotentCoord J // z ^ 2 = w} = q * (q + 1) := by
  have hw0 : w.1.1 = 0 := (pow_two_eq_one_iff J w).mp hw2
  refine card_sq_eq_coord J hcard hfixed hw0 fun h => hw1 ?_
  exact coord_ext (by rw [hw0, fst_one]) (by rw [h, snd_one])

omit hcard hfixed

theorem card_sq_eq_of_mulEquiv_projectiveSpecialUnitary [CharP K 2] {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {L : Type*} [Group L]
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) (R : Sylow 2 L) {z : (R : Subgroup L)}
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    Nat.card {x : (R : Subgroup L) // x ^ 2 = z} = 2 ^ f * (2 ^ f + 1) := by
  have := Fintype.ofFinite K
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
      (x : Matrix.ProjGenLinGroup (Fin 3) K)) Subtype.coe_injective
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨θ⟩ : Nonempty ((R : Subgroup L) ≃* unitaryCoverRoot J hJ) :=
    nonempty_sylow_mulEquiv_of_mulEquiv e R (unitaryCoverSylow J f hf hcard hfixed hJ)
  set θ' := θ.trans (unitaryCoverRootEquiv J hJ).symm
  rw [card_sq_eq_congr θ' z]
  refine card_sq_eq_coord_of_sq_eq_one J hcard hfixed (fun h => hz1 ?_) ?_
  · exact θ'.injective (h.trans (map_one θ').symm)
  · rw [← map_pow, hz2, map_one]

end CFSG.ProperTwoGeneratedCore.BenderFacts
