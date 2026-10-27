module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.A5OddBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem oddInv5_sigma_ne_one :
    (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

private theorem oddInv5_sigma_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by decide

private def oddInv5_swapW : A5WrTwo := ⟨1, Multiplicative.ofAdd (1 : ZMod 2)⟩

private theorem oddInv5_swapW_right :
    oddInv5_swapW.right = Multiplicative.ofAdd (1 : ZMod 2) := rfl

private theorem oddInv5_baseEmb_right (p q : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (p, q)).right = 1 := by
  have hmem : A5WrTwo.baseEmb (p, q) ∈
      (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).ker := by
    rw [← A5WrTwo.commutator_eq_ker, ← A5WrTwo.range_baseEmb]
    exact MonoidHom.mem_range.mpr ⟨(p, q), rfl⟩
  exact hmem

private theorem oddInv5_swapW_sq : oddInv5_swapW * oddInv5_swapW = 1 := by
  apply RegularWreathProduct.ext
  · funext i
    simp [oddInv5_swapW, RegularWreathProduct.mul_def, oddInv5_sigma_mul_self]
  · simp [oddInv5_swapW, RegularWreathProduct.mul_def, oddInv5_sigma_mul_self]

private theorem oddInv5_swapW_mul_baseEmb_mul_inv (x y : alternatingGroup (Fin 5)) :
    oddInv5_swapW * A5WrTwo.baseEmb (x, y) * oddInv5_swapW⁻¹ = A5WrTwo.baseEmb (y, x) :=
  A5WrTwo.swap_mul_baseEmb_mul_inv x y

private theorem oddInv5_not_mem_commutator_of_right_eq_sigma {g : A5WrTwo}
    (hg : g.right = Multiplicative.ofAdd (1 : ZMod 2)) : g ∉ commutator A5WrTwo := by
  intro h
  rw [A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker] at h
  have h1 : g.right = 1 := h
  rw [hg] at h1
  exact oddInv5_sigma_ne_one h1

private theorem oddInv5_baseEmb_mul_swapW_mul_baseEmb_mul_swapW
    (x y x' y' : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (x, y) * oddInv5_swapW) *
        (A5WrTwo.baseEmb (x', y') * oddInv5_swapW)
      = A5WrTwo.baseEmb (x * y', y * x') := by
  calc (A5WrTwo.baseEmb (x, y) * oddInv5_swapW) *
        (A5WrTwo.baseEmb (x', y') * oddInv5_swapW)
      = A5WrTwo.baseEmb (x, y) * (oddInv5_swapW * A5WrTwo.baseEmb (x', y') *
          oddInv5_swapW⁻¹) * (oddInv5_swapW * oddInv5_swapW) := by group
    _ = A5WrTwo.baseEmb (x, y) * A5WrTwo.baseEmb (y', x') * 1 := by
          rw [oddInv5_swapW_mul_baseEmb_mul_inv, oddInv5_swapW_sq]
    _ = A5WrTwo.baseEmb (x * y', y * x') := by
          rw [mul_one, ← A5WrTwo.baseEmb.map_mul, Prod.mk_mul_mk]

private theorem oddInv5_baseEmb_mul_swapW_sq (x y : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (x, y) * oddInv5_swapW) ^ 2 = A5WrTwo.baseEmb (x * y, y * x) := by
  rw [pow_two, oddInv5_baseEmb_mul_swapW_mul_baseEmb_mul_swapW]

private theorem oddInv5_baseEmb_pair_pow (a b : alternatingGroup (Fin 5)) (n : ℕ) :
    (A5WrTwo.baseEmb (a, b)) ^ n = A5WrTwo.baseEmb (a ^ n, b ^ n) := by
  rw [← A5WrTwo.baseEmb.map_pow,
    show (a, b) ^ n = (a ^ n, b ^ n) from
      Prod.ext (map_pow (MonoidHom.fst _ _) (a, b) n)
        (map_pow (MonoidHom.snd _ _) (a, b) n)]

private theorem oddInv5_baseEmb_conj (p q : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    A5WrTwo.baseEmb p * A5WrTwo.baseEmb q * (A5WrTwo.baseEmb p)⁻¹ =
      A5WrTwo.baseEmb (p * q * p⁻¹) := by
  rw [← map_mul, ← map_inv, ← map_mul]

private theorem oddInv5_baseEmb_mul_swap_conj (g h x y : alternatingGroup (Fin 5)) :
    (A5WrTwo.baseEmb (g, h) * oddInv5_swapW) * A5WrTwo.baseEmb (x, y) *
        (A5WrTwo.baseEmb (g, h) * oddInv5_swapW)⁻¹ =
      A5WrTwo.baseEmb (g * y * g⁻¹, h * x * h⁻¹) := by
  have h1 : (A5WrTwo.baseEmb (g, h) * oddInv5_swapW) * A5WrTwo.baseEmb (x, y) *
        (A5WrTwo.baseEmb (g, h) * oddInv5_swapW)⁻¹ =
      A5WrTwo.baseEmb (g, h) * (oddInv5_swapW * A5WrTwo.baseEmb (x, y) *
        oddInv5_swapW⁻¹) * (A5WrTwo.baseEmb (g, h))⁻¹ := by
    group
  rw [h1, oddInv5_swapW_mul_baseEmb_mul_inv]
  exact oddInv5_baseEmb_conj (g, h) (y, x)

private theorem oddInv5_orderOf_eq_of_isConj {k k' : alternatingGroup (Fin 5)}
    (h : IsConj k k') : orderOf k = orderOf k' := by
  obtain ⟨c, hc⟩ := h
  exact SemiconjBy.orderOf_eq (c : alternatingGroup (Fin 5)) hc

private theorem oddInv5_a5_inv_five_sq (m k : alternatingGroup (Fin 5)) (hk5 : k ^ 5 = 1)
    (hk1 : k ≠ 1) (hmk : m * k * m⁻¹ = k⁻¹) : m ^ 2 = 1 := by
  revert m k
  decide +kernel

private theorem oddInv5_invol_inv_mul {u v : A5WrTwo} (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) :
    u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
  have huu : u * u = 1 := by simpa [pow_two] using hu2
  have huu' : u⁻¹ = u := inv_eq_of_mul_eq_one_left huu
  have hvv' : v⁻¹ = v := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hv2)
  calc u * (u * v) * u⁻¹ = (u * u) * v * u⁻¹ := by group
    _ = v * u⁻¹ := by rw [huu]; group
    _ = (u * v)⁻¹ := by rw [mul_inv_rev, huu', hvv']

theorem oddInv_wr_exists_outer {u v : A5WrTwo} (hu : u ∉ _root_.commutator A5WrTwo)
    (hv : v ∉ _root_.commutator A5WrTwo) (hu2 : u ^ 2 = 1) (hv2 : v ^ 2 = 1) :
    ∃ w : A5WrTwo, w ^ 2 = 1 ∧ w ∉ _root_.commutator A5WrTwo ∧ w * (u * v) = u * v * w := by
  obtain ⟨k, k', huv, hkk'⟩ := oddInv_wr_outer_mul hu hv hu2 hv2
  obtain ⟨p, hp⟩ := isConj_iff.mp hkk'.symm
  let w : A5WrTwo := A5WrTwo.baseEmb (p, p⁻¹) * oddInv5_swapW
  refine ⟨w, ?_, ?_, ?_⟩
  · dsimp only [w]
    rw [oddInv5_baseEmb_mul_swapW_sq, mul_inv_cancel, inv_mul_cancel]
    exact A5WrTwo.baseEmb.map_one
  · apply oddInv5_not_mem_commutator_of_right_eq_sigma
    show w.right = Multiplicative.ofAdd (1 : ZMod 2)
    dsimp only [w]
    rw [RegularWreathProduct.mul_right, oddInv5_swapW_right, oddInv5_baseEmb_right, one_mul]
  · have hconj : w * A5WrTwo.baseEmb (k, k') * w⁻¹ = A5WrTwo.baseEmb (k, k') := by
      dsimp only [w]
      rw [oddInv5_baseEmb_mul_swap_conj, inv_inv]
      have hpk : p⁻¹ * k * p = k' := by
        calc p⁻¹ * k * p = p⁻¹ * (p * k' * p⁻¹) * p := by rw [hp]
          _ = k' := by group
      rw [hp, hpk]
    calc w * (u * v) = w * A5WrTwo.baseEmb (k, k') := by rw [huv]
      _ = A5WrTwo.baseEmb (k, k') * w := by
          calc w * A5WrTwo.baseEmb (k, k')
              = (w * A5WrTwo.baseEmb (k, k') * w⁻¹) * w := by group
            _ = A5WrTwo.baseEmb (k, k') * w := by rw [hconj]
      _ = u * v * w := by rw [huv]

theorem oddInv_wr_sq_mul {u v w : A5WrTwo} (hu : u ∉ _root_.commutator A5WrTwo)
    (hv : v ∉ _root_.commutator A5WrTwo) (hw : w ∉ _root_.commutator A5WrTwo) (hu2 : u ^ 2 = 1)
    (hv2 : v ^ 2 = 1) (hw2 : w ^ 2 = 1) (h5 : orderOf (u * v) = 5)
    (hwc : w * (u * v) = u * v * w) : (u * w) ^ 2 = 1 := by
  obtain ⟨k, k', huv, hkk'⟩ := oddInv_wr_outer_mul hu hv hu2 hv2
  obtain ⟨m, m', huw, _⟩ := oddInv_wr_outer_mul hu hw hu2 hw2
  have hbase5 : orderOf (A5WrTwo.baseEmb (k, k')) = 5 := by rw [← huv]; exact h5
  have hordk : orderOf k = 5 := (oddInv_wr_orderOf_baseEmb hkk').symm.trans hbase5
  have hordk' : orderOf k' = 5 := (oddInv5_orderOf_eq_of_isConj hkk').symm.trans hordk
  have hk5 : k ^ 5 = 1 := by
    have h := pow_orderOf_eq_one k
    rwa [hordk] at h
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordk
    exact absurd hordk (by norm_num)
  have hk'5 : k' ^ 5 = 1 := by
    have h := pow_orderOf_eq_one k'
    rwa [hordk'] at h
  have hk'1 : k' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordk'
    exact absurd hordk' (by norm_num)
  have hwu : w * (u * v) * w⁻¹ = u * v := by rw [hwc]; group
  have hconj1 : (u * w) * (u * v) * (u * w)⁻¹ = (u * v)⁻¹ := by
    calc (u * w) * (u * v) * (u * w)⁻¹ = u * (w * (u * v) * w⁻¹) * u⁻¹ := by group
      _ = u * (u * v) * u⁻¹ := by rw [hwu]
      _ = (u * v)⁻¹ := oddInv5_invol_inv_mul hu2 hv2
  have hbase_eq : A5WrTwo.baseEmb ((m, m') * (k, k') * (m, m')⁻¹) =
      A5WrTwo.baseEmb ((k, k')⁻¹) := by
    have h := hconj1
    rwa [huw, huv, oddInv5_baseEmb_conj, ← map_inv] at h
  have hpair : (m * k * m⁻¹, m' * k' * m'⁻¹) = (k⁻¹, k'⁻¹) :=
    A5WrTwo.baseEmb_injective (by simpa using hbase_eq)
  have hmk : m * k * m⁻¹ = k⁻¹ := congrArg Prod.fst hpair
  have hmk' : m' * k' * m'⁻¹ = k'⁻¹ := congrArg Prod.snd hpair
  have hm2 : m ^ 2 = 1 := oddInv5_a5_inv_five_sq m k hk5 hk1 hmk
  have hm'2 : m' ^ 2 = 1 := oddInv5_a5_inv_five_sq m' k' hk'5 hk'1 hmk'
  calc (u * w) ^ 2 = (A5WrTwo.baseEmb (m, m')) ^ 2 := by rw [huw]
    _ = A5WrTwo.baseEmb (m ^ 2, m' ^ 2) := oddInv5_baseEmb_pair_pow m m' 2
    _ = 1 := by rw [hm2, hm'2]; exact A5WrTwo.baseEmb.map_one

end CFSG.EvenSporadicStandard.HNRecog.Section3
