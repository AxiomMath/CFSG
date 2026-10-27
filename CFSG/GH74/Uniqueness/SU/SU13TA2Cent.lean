module

public import CFSG.GH74.Uniqueness.SU.SU13TA1Basic
public import CFSG.GH74.Uniqueness.SU.SU13TA1Three

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Subgroup

namespace TwoCover

variable {H : Type} [Group H] {n : ℕ} {π : H →* alternatingGroup (Fin n)}

theorem eq_of_odd_orderOf_of_map_eq (hπ : TwoCover π) {x y : H} (hx : Odd (orderOf x))
    (hy : Odd (orderOf y)) (h : π x = π y) : x = y := by
  have hk : x⁻¹ * y ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hkc : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp (hπ.ker_le_center hk) x
  have hk2 := hπ.sq_eq_one_of_mem_ker' hk
  obtain ⟨j, hj⟩ : Odd (orderOf x * orderOf y) := hx.mul hy
  have hxm : x ^ (orderOf x * orderOf y) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hym : y ^ (orderOf x * orderOf y) = 1 := by
    rw [mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hkm : (x⁻¹ * y) ^ (orderOf x * orderOf y) = 1 := by
    have hym' : (x * (x⁻¹ * y)) ^ (orderOf x * orderOf y) = 1 := by
      rwa [mul_inv_cancel_left]
    rwa [hkc.mul_pow, hxm, one_mul] at hym'
  have hk1 : x⁻¹ * y = 1 := by
    calc x⁻¹ * y = (x⁻¹ * y) ^ (orderOf x * orderOf y) := by
          rw [hj, pow_succ, pow_mul, hk2, one_pow, one_mul]
      _ = 1 := hkm
  exact inv_mul_eq_one.mp hk1

theorem commute_of_odd_orderOf (hπ : TwoCover π) {x u : H} (hx : Odd (orderOf x))
    (h : Commute (π u) (π x)) : Commute u x := by
  have hord : orderOf x = orderOf (u * x * u⁻¹) :=
    SemiconjBy.orderOf_eq u (show u * x = u * x * u⁻¹ * u by group)
  have hconj : u * x * u⁻¹ = x := hπ.eq_of_odd_orderOf_of_map_eq (hord ▸ hx) hx (by
    rw [map_mul, map_mul, map_inv, h.eq, mul_inv_cancel_right])
  exact mul_inv_eq_iff_eq_mul.mp hconj

theorem centralizer_singleton_eq_comap (hπ : TwoCover π) {x : H} (hx : Odd (orderOf x)) :
    centralizer ({x} : Set H) =
      (centralizer ({π x} : Set (alternatingGroup (Fin n)))).comap π := by
  ext u
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    exact (hπ.commute_of_odd_orderOf hx h).eq

theorem card_comap (hπ : TwoCover π) (B : Subgroup (alternatingGroup (Fin n))) :
    Nat.card (B.comap π) = 2 * Nat.card B := by
  have h1 := Subgroup.card_mul_index (B.comap π)
  rw [Subgroup.index_comap_of_surjective B hπ.surj, hπ.card] at h1
  have h2 := Subgroup.card_mul_index B
  have hi : 0 < B.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hi ?_
  rw [h1, mul_assoc, h2]

theorem card_centralizer_singleton (hπ : TwoCover π) {x : H} (hx : Odd (orderOf x)) :
    Nat.card (centralizer ({x} : Set H)) =
      2 * Nat.card (centralizer ({π x} : Set (alternatingGroup (Fin n)))) := by
  rw [hπ.centralizer_singleton_eq_comap hx, hπ.card_comap]

theorem odd_orderOf_of_mem_isPGroup_three {Q : Subgroup H} (hQ : IsPGroup 3 Q) {x : H}
    (hx : x ∈ Q) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
  have h : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h)

theorem card_map_of_isPGroup_three (hπ : TwoCover π) {Q : Subgroup H} (hQ : IsPGroup 3 Q) :
    Nat.card (Q.map π) = Nat.card Q := by
  have hinj : Function.Injective (π.comp Q.subtype) := fun x y h =>
    Subtype.ext (hπ.eq_of_odd_orderOf_of_map_eq (odd_orderOf_of_mem_isPGroup_three hQ x.2)
      (odd_orderOf_of_mem_isPGroup_three hQ y.2) h)
  have hr : (π.comp Q.subtype).range = Q.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (Equiv.ofInjective _ hinj)).symm

theorem eq_of_map_eq_of_isPGroup_three (hπ : TwoCover π) {Q Q' : Subgroup H} (hQ : IsPGroup 3 Q)
    (hQ' : IsPGroup 3 Q') (h : Q.map π = Q'.map π) : Q = Q' := by
  have key : ∀ {R R' : Subgroup H}, IsPGroup 3 R → IsPGroup 3 R' → R.map π = R'.map π → R ≤ R' := by
    intro R R' hR hR' hRR' x hx
    have hπx : π x ∈ R'.map π := hRR' ▸ Subgroup.mem_map_of_mem π hx
    obtain ⟨x', hx', hxx'⟩ := hπx
    have : x' = x := hπ.eq_of_odd_orderOf_of_map_eq (odd_orderOf_of_mem_isPGroup_three hR' hx')
      (odd_orderOf_of_mem_isPGroup_three hR hx) hxx'
    rw [← this]
    exact hx'
  exact le_antisymm (key hQ hQ' h) (key hQ' hQ h.symm)

theorem exists_lift_isPGroup_three [Finite H] (hπ : TwoCover π)
    {B : Subgroup (alternatingGroup (Fin n))} (hB : IsPGroup 3 B) :
    ∃ Q : Subgroup H, IsPGroup 3 Q ∧ Q.map π = B := by
  classical
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB
  obtain ⟨S⟩ : Nonempty (Sylow 3 (B.comap π)) := inferInstance
  set Q : Subgroup H := (S : Subgroup (B.comap π)).map (B.comap π).subtype with hQdef
  have hQ3 : IsPGroup 3 Q := IsPGroup.map S.isPGroup' (B.comap π).subtype
  have hPcard : Nat.card (B.comap π) = 2 * 3 ^ m := by rw [hπ.card_comap, hm]
  have hS : Nat.card S = 3 ^ m := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (by norm_num) (by positivity)]
    simp [Nat.Prime.factorization_pow Nat.prime_three, Nat.factorization_eq_zero_of_not_dvd]
  refine ⟨Q, hQ3, ?_⟩
  have hle : Q.map π ≤ B := by
    rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact y.2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hπ.card_map_of_isPGroup_three hQ3, hm, hQdef, Subgroup.card_map_of_injective
    (B.comap π).subtype_injective]
  exact hS.ge

theorem centralizer_eq_comap_of_isPGroup_three (hπ : TwoCover π) {Q : Subgroup H}
    (hQ : IsPGroup 3 Q) :
    centralizer (Q : Set H) =
      (centralizer ((Q.map π : Subgroup (alternatingGroup (Fin n))) : Set (alternatingGroup (Fin n)))).comap π := by
  ext u
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_comap, SetLike.mem_coe, Subgroup.mem_map]
  constructor
  · rintro h _ ⟨q, hq, rfl⟩
    rw [← map_mul, ← map_mul, h q hq]
  · intro h q hq
    have h1 := h (π q) ⟨q, hq, rfl⟩
    exact (hπ.commute_of_odd_orderOf (odd_orderOf_of_mem_isPGroup_three hQ hq) h1.symm).eq.symm

theorem normalizer_eq_comap_of_isPGroup_three (hπ : TwoCover π) {Q : Subgroup H}
    (hQ : IsPGroup 3 Q) :
    normalizer (Q : Set H) =
      (normalizer ((Q.map π : Subgroup (alternatingGroup (Fin n))) : Set (alternatingGroup (Fin n)))).comap π := by
  have hmap : ∀ u : H, (Q.map π).map (MulAut.conj (π u)) = (Q.map (MulAut.conj u)).map π :=
    fun u => by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
  ext u
  rw [Subgroup.mem_comap, mem_normalizer_iff_map_conj_eq, mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    rw [hmap, h]
  · intro h
    have h3 : IsPGroup 3 (Q.map (MulAut.conj u : H →* H)) := IsPGroup.map hQ _
    exact hπ.eq_of_map_eq_of_isPGroup_three h3 hQ ((hmap u).symm.trans h)

end TwoCover

end CFSG.GH74.Uniqueness.SU.SU13.TA
