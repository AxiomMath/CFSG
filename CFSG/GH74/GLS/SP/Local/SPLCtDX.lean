module

public import CFSG.GH74.GLS.IVK.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.GH74.GLS.SP.Local

section Parity

open DihedralGroup Subgroup

variable {k : ℕ}

private def dihPar (hk : 2 ∣ k) (c : ZMod k) : DihedralGroup k →* Multiplicative (ZMod 2) where
  toFun g :=
    match g with
    | r a => Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) a)
    | sr a => Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (a - c))
  map_one' := by
    show Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) 0) = 1
    rw [map_zero]
    rfl
  map_mul' := by
    rintro (a | a) (b | b)
    · show Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (a + b)) =
        Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) a) *
          Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) b)
      rw [map_add, ofAdd_add]
    · show Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (b - a - c)) =
        Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) a) *
          Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (b - c))
      rw [← ofAdd_add]
      congr 1
      simp only [map_sub]
      generalize ZMod.castHom hk (ZMod 2) a = u
      generalize ZMod.castHom hk (ZMod 2) b = v
      generalize ZMod.castHom hk (ZMod 2) c = w
      revert u v w
      decide
    · show Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (a + b - c)) =
        Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (a - c)) *
          Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) b)
      rw [← ofAdd_add]
      congr 1
      simp only [map_sub, map_add]
      generalize ZMod.castHom hk (ZMod 2) a = u
      generalize ZMod.castHom hk (ZMod 2) b = v
      generalize ZMod.castHom hk (ZMod 2) c = w
      revert u v w
      decide
    · show Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (b - a)) =
        Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (a - c)) *
          Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) (b - c))
      rw [← ofAdd_add]
      congr 1
      simp only [map_sub]
      generalize ZMod.castHom hk (ZMod 2) a = u
      generalize ZMod.castHom hk (ZMod 2) b = v
      generalize ZMod.castHom hk (ZMod 2) c = w
      revert u v w
      decide

private theorem dihPar_r_eq_one (hk : 2 ∣ k) (c a : ZMod k) :
    dihPar hk c (r a) = 1 ↔ ZMod.castHom hk (ZMod 2) a = 0 :=
  ofAdd_eq_one

private theorem dihPar_sr_eq_one (hk : 2 ∣ k) (c a : ZMod k) :
    dihPar hk c (sr a) = 1 ↔ ZMod.castHom hk (ZMod 2) (a - c) = 0 :=
  ofAdd_eq_one

private theorem dihEven [NeZero k] (hk : 2 ∣ k) {a : ZMod k}
    (ha : ZMod.castHom hk (ZMod 2) a = 0) : ∃ b : ZMod k, a = 2 * b := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at ha
  obtain ⟨b, hb⟩ := ha
  refine ⟨(b : ZMod k), ?_⟩
  rw [← ZMod.natCast_zmod_val a, hb, Nat.cast_mul, Nat.cast_ofNat]

private theorem dihUnitMod (hk : 2 ∣ k) {i : ZMod k} (hi : IsUnit i) :
    ZMod.castHom hk (ZMod 2) i = 1 := by
  have h1 : IsUnit (ZMod.castHom hk (ZMod 2) i) := hi.map _
  rcases (by decide : ∀ u : ZMod 2, u = 0 ∨ u = 1) (ZMod.castHom hk (ZMod 2) i) with h | h
  · rw [h] at h1
    exact absurd h1 not_isUnit_zero
  · exact h

private theorem dihUnit [NeZero k] {i : ZMod k} (h : orderOf (r i) = k) : IsUnit i := by
  rw [orderOf_r] at h
  have hpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hg : Nat.gcd k i.val = 1 := by
    by_contra hne
    have h1 : 0 < Nat.gcd k i.val := Nat.gcd_pos_of_pos_left _ hpos
    have h2 : 1 < Nat.gcd k i.val := by omega
    have := Nat.div_lt_self hpos h2
    omega
  have h3 : IsUnit ((i.val : ℕ) : ZMod k) :=
    (ZMod.isUnit_iff_coprime i.val k).mpr (Nat.Coprime.symm hg)
  rwa [ZMod.natCast_zmod_val] at h3

private theorem dihTwoNeZero (hk : 3 ≤ k) : (2 : ZMod k) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

private theorem dihInvol [NeZero k] {m : ℕ} (hk : k = 2 * m) {b : ZMod k}
    (h : orderOf (r b) = 2) : b = (m : ZMod k) := by
  have h2 : r b * r b = 1 := by
    have := pow_orderOf_eq_one (r b)
    rwa [h, sq] at this
  rw [r_mul_r] at h2
  have h3 : b + b = 0 := r.inj (h2.trans r_zero.symm)
  have h4 : -b = b := neg_eq_of_add_eq_zero_right h3
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [r_zero, orderOf_one] at h
    omega
  rcases (ZMod.neg_eq_self_iff b).mp h4 with h5 | h5
  · exact absurd h5 hb0
  · have hv : b.val = m := by omega
    rw [← hv, ZMod.natCast_zmod_val]

private theorem dihCentral [NeZero k] {m : ℕ} (hk : k = 2 * m) (hm : 2 ≤ m)
    {g : DihedralGroup k} (hc : ∀ h : DihedralGroup k, g * h = h * g) (hg : orderOf g = 2) :
    g = r (m : ZMod k) := by
  rcases g with b | b
  · exact congrArg r (dihInvol hk hg)
  · exfalso
    have h1 := hc (r 1)
    rw [sr_mul_r, r_mul_sr] at h1
    exact dihTwoNeZero (k := k) (by omega) (by linear_combination sr.inj h1)

private theorem dihReflection [NeZero k] {m : ℕ} (hk : k = 2 * m) {g : DihedralGroup k}
    (hg : orderOf g = 2) (hne : g ≠ r (m : ZMod k)) : ∃ c : ZMod k, g = sr c := by
  rcases g with b | b
  · exact absurd (congrArg r (dihInvol hk hg)) hne
  · exact ⟨b, rfl⟩

private theorem dih_sup_eq_ker {Q : Type} [Group Q] [NeZero k] (hk : 2 ∣ k)
    (φ : Q ≃* DihedralGroup k) {x z : Q} {i j : ZMod k} (hi : IsUnit i) (hx : φ x = r i)
    (hz : φ z = sr j) :
    zpowers (x ^ 2) ⊔ zpowers z = ((dihPar hk j).comp φ.toMonoidHom).ker := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [zpowers_le, MonoidHom.mem_ker]
      show dihPar hk j (φ (x ^ 2)) = 1
      rw [map_pow, hx, map_pow]
      show (Multiplicative.ofAdd (ZMod.castHom hk (ZMod 2) i)) ^ 2 = 1
      rw [dihUnitMod hk hi]
      decide
    · rw [zpowers_le, MonoidHom.mem_ker]
      show dihPar hk j (φ z) = 1
      rw [hz, dihPar_sr_eq_one, sub_self, map_zero]
  · intro g hg
    rw [MonoidHom.mem_ker] at hg
    obtain ⟨s, hs⟩ := hi.exists_right_inv
    obtain ⟨w, rfl⟩ := φ.symm.surjective g
    have hg' : dihPar hk j w = 1 := by
      have : dihPar hk j (φ (φ.symm w)) = 1 := hg
      rwa [MulEquiv.apply_symm_apply] at this
    rcases w with a | a
    · obtain ⟨b, rfl⟩ := dihEven hk ((dihPar_r_eq_one hk j a).mp hg')
      have h1 : φ.symm (r (2 * b)) = (x ^ 2) ^ (b * s).val := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, map_pow, map_pow, hx, r_pow, r_pow,
          ZMod.natCast_zmod_val]
        congr 1
        push_cast
        linear_combination (-(2 * b)) * hs
      rw [h1]
      exact mem_sup_left (pow_mem (mem_zpowers _) _)
    · obtain ⟨b, hb⟩ := dihEven hk ((dihPar_sr_eq_one hk j a).mp hg')
      have h1 : φ.symm (sr a) = z * (x ^ 2) ^ (b * s).val := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, map_mul, map_pow, map_pow, hx, hz, r_pow, r_pow,
          ZMod.natCast_zmod_val, sr_mul_r]
        congr 1
        push_cast
        linear_combination hb + (-(2 * b)) * hs
      rw [h1]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (pow_mem (mem_zpowers _) _))

private theorem dih_rotation_abs {Q : Type} [Group Q] {m : ℕ} (hk : k = 2 * m) (hm : 2 ≤ m)
    (φ : Q ≃* DihedralGroup k) (t z : Q) (ht : orderOf t = 2) (htc : ∀ a : Q, t * a = a * t)
    (hz : orderOf z = 2) (hzt : z ≠ t) :
    ∃ x : Q, orderOf x = k ∧ x ^ m = t ∧ z * x * z⁻¹ = x⁻¹ ∧ zpowers x ⊔ zpowers z = ⊤ ∧
      x ∉ zpowers (x ^ 2) ⊔ zpowers z := by
  have : NeZero k := ⟨by omega⟩
  have hk2 : 2 ∣ k := ⟨m, hk⟩
  have hφt : φ t = r (m : ZMod k) := by
    refine dihCentral hk hm (fun h => ?_) (by rw [MulEquiv.orderOf_eq]; exact ht)
    have := congrArg φ (htc (φ.symm h))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  obtain ⟨c, hc⟩ : ∃ c : ZMod k, φ z = sr c :=
    dihReflection hk (by rw [MulEquiv.orderOf_eq]; exact hz)
      (by rw [← hφt]; exact fun h => hzt (φ.injective h))
  have hx1 : φ (φ.symm (r 1)) = r 1 := MulEquiv.apply_symm_apply _ _
  refine ⟨φ.symm (r 1), ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_r_one
  · apply φ.injective
    rw [map_pow, hx1, r_one_pow, hφt]
  · apply φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, hx1, hc]
    simp only [sr_mul_r, inv_sr, sr_mul_sr, inv_r]
    congr 1
    ring
  · rw [eq_top_iff]
    intro g _
    obtain ⟨w, rfl⟩ := φ.symm.surjective g
    rcases w with a | a
    · have h1 : φ.symm (r a) = (φ.symm (r 1)) ^ a.val := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, map_pow, hx1, r_one_pow, ZMod.natCast_zmod_val]
      rw [h1]
      exact mem_sup_left (pow_mem (mem_zpowers _) _)
    · have h1 : φ.symm (sr a) = z * (φ.symm (r 1)) ^ (a - c).val := by
        apply φ.injective
        rw [MulEquiv.apply_symm_apply, map_mul, map_pow, hx1, hc, r_one_pow,
          ZMod.natCast_zmod_val, sr_mul_r]
        congr 1
        ring
      rw [h1]
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (pow_mem (mem_zpowers _) _))
  · intro hxmem
    have hker := dih_sup_eq_ker hk2 φ (x := φ.symm (r 1)) (z := z) (i := 1) isUnit_one hx1 hc
    rw [hker, MonoidHom.mem_ker] at hxmem
    have h1 : dihPar hk2 c (r 1) = 1 := by
      have h2 : dihPar hk2 c (φ (φ.symm (r 1))) = 1 := hxmem
      rwa [hx1] at h2
    have h3 := (dihPar_r_eq_one hk2 c 1).mp h1
    rw [map_one] at h3
    exact one_ne_zero h3

private theorem dih_index_two_abs {Q : Type} [Group Q] {m : ℕ} (hk : k = 2 * m) (hm : 2 ≤ m)
    (φ : Q ≃* DihedralGroup k) {x z : Q} (hx : orderOf x = k) (hzz : z * z = 1)
    (hzx : z * x * z = x⁻¹) (S : Subgroup Q) (hS : Nat.card S = k) (hzS : z ∈ S) :
    S = zpowers (x ^ 2) ⊔ zpowers z := by
  have : NeZero k := ⟨by omega⟩
  have : Finite Q := Finite.of_equiv _ φ.symm.toEquiv
  have hk2 : 2 ∣ k := ⟨m, hk⟩
  obtain ⟨i, hi⟩ : ∃ i : ZMod k, φ x = r i := by
    rcases hφx : φ x with i | i
    · exact ⟨i, rfl⟩
    · exfalso
      have h := MulEquiv.orderOf_eq φ x
      rw [hφx, orderOf_sr, hx] at h
      omega
  have hiu : IsUnit i := dihUnit (by rw [← hi, MulEquiv.orderOf_eq]; exact hx)
  obtain ⟨j, hj⟩ : ∃ j : ZMod k, φ z = sr j := by
    rcases hφz : φ z with j | j
    · exfalso
      have h0 := congrArg φ hzz
      have h1 := congrArg φ hzx
      rw [map_mul, hφz, r_mul_r, map_one, ← r_zero] at h0
      rw [map_mul, map_mul, map_inv, hφz, hi, inv_r, r_mul_r, r_mul_r] at h1
      have h2 : i + i = 0 := by linear_combination r.inj h1 - r.inj h0
      have h3 : (r i) ^ 2 = 1 := by rw [sq, r_mul_r, h2, r_zero]
      have h4 := orderOf_dvd_of_pow_eq_one h3
      rw [← hi, MulEquiv.orderOf_eq, hx] at h4
      have := Nat.le_of_dvd (by norm_num) h4
      omega
    · exact ⟨j, rfl⟩
  have hker : zpowers (x ^ 2) ⊔ zpowers z = ((dihPar hk2 j).comp φ.toMonoidHom).ker :=
    dih_sup_eq_ker hk2 φ hiu hi hj
  have hQcard : Nat.card Q = 2 * k := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
  have hkpos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkerc : k ≤ Nat.card ((dihPar hk2 j).comp φ.toMonoidHom).ker := by
    have h1 := ((dihPar hk2 j).comp φ.toMonoidHom).ker.card_mul_index
    have h2 : ((dihPar hk2 j).comp φ.toMonoidHom).ker.index ≤ 2 := by
      rw [Subgroup.index_ker]
      calc Nat.card ((dihPar hk2 j).comp φ.toMonoidHom).range
          ≤ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_le_card_group _
        _ = 2 := by
          rw [Nat.card_congr Multiplicative.toAdd]
          exact Nat.card_zmod 2
    rw [hQcard] at h1
    by_contra hlt
    have hlt' := not_le.mp hlt
    have h3 := Nat.mul_le_mul_left (Nat.card ((dihPar hk2 j).comp φ.toMonoidHom).ker) h2
    omega
  have hSidx : S.index = 2 := by
    have h1 := S.card_mul_index
    rw [hS, hQcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hkpos (by rw [h1, mul_comm])
  have hx2 : x ^ 2 ∈ S := Subgroup.sq_mem_of_index_two hSidx x
  have hle : zpowers (x ^ 2) ⊔ zpowers z ≤ S := sup_le (zpowers_le.2 hx2) (zpowers_le.2 hzS)
  have hcard : Nat.card S ≤ Nat.card (zpowers (x ^ 2) ⊔ zpowers z : Subgroup Q) := by
    rw [hS, hker]
    exact hkerc
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end Parity

private theorem zpowers_sup_map {G : Type} [Group G] (Y : Subgroup G) (a b : ↥Y) :
    (Subgroup.zpowers a ⊔ Subgroup.zpowers b).map Y.subtype =
      Subgroup.zpowers (a : G) ⊔ Subgroup.zpowers (b : G) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

private theorem two_pow_dihedral {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ^ n = 2 * k) :
    k = 2 ^ (n - 1) ∧ 2 ^ (n - 1) = 2 * 2 ^ (n - 2) ∧ 2 ≤ 2 ^ (n - 2) := by
  have hn1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hn2 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  refine ⟨by omega, hn2, ?_⟩
  calc (2 : ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

open Subgroup CFSG.GH74.GLS.IVK in
theorem dihedral_rotation {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n) (Y : Subgroup G)
    (hY : IsDihedralOrder ↥Y (2 ^ n)) (t z : G) (htY : t ∈ Y) (hzY : z ∈ Y)
    (ht : orderOf t = 2) (htc : ∀ a ∈ Y, t * a = a * t) (hz : orderOf z = 2) (hzt : z ≠ t) :
    ∃ x : G, x ∈ Y ∧ orderOf x = 2 ^ (n - 1) ∧ x ^ (2 ^ (n - 2)) = t ∧ z * x * z⁻¹ = x⁻¹ ∧
      zpowers x ⊔ zpowers z = Y ∧ x ∉ zpowers (x ^ 2) ⊔ zpowers z := by
  obtain ⟨k, hk2n, -, ⟨φ⟩⟩ := hY
  obtain ⟨hkn, hn2, hm⟩ := two_pow_dihedral hn hk2n
  obtain ⟨x, hx1, hx2, hx3, hx4, hx5⟩ := dih_rotation_abs (Q := ↥Y) (k := k) (m := 2 ^ (n - 2))
    (by omega) hm φ ⟨t, htY⟩ ⟨z, hzY⟩ (by rw [Subgroup.orderOf_mk, ht])
    (fun a => Subtype.ext (htc a a.2)) (by rw [Subgroup.orderOf_mk, hz])
    (fun h => hzt (congrArg Subtype.val h))
  refine ⟨(x : G), x.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hx1, hkn]
  · exact congrArg Subtype.val hx2
  · exact congrArg Subtype.val hx3
  · have h1 := zpowers_sup_map Y x ⟨z, hzY⟩
    rw [hx4, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1.symm
  · intro hmem
    have h1 := zpowers_sup_map Y (x ^ 2) ⟨z, hzY⟩
    have h2 : ((x ^ 2 : ↥Y) : G) = (x : G) ^ 2 := rfl
    rw [h2] at h1
    rw [← h1] at hmem
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmem
    exact hx5 (Subtype.ext hyx ▸ hy)

open Subgroup CFSG.GH74.GLS.IVK in
theorem dihedral_index_two_sub {G : Type} [Group G] {n : ℕ} (hn : 3 ≤ n) (Y X : Subgroup G)
    (hXY : X ≤ Y) (hY : IsDihedralOrder ↥Y (2 ^ n)) (hX : IsDihedralOrder ↥X (2 ^ (n - 1)))
    (x z : G) (hx : orderOf x = 2 ^ (n - 1)) (hzx : z * x * z⁻¹ = x⁻¹)
    (hYgen : zpowers x ⊔ zpowers z = Y) (hzX : z ∈ X) (hz : orderOf z = 2) :
    X = zpowers (x ^ 2) ⊔ zpowers z := by
  obtain ⟨k, hk2n, -, ⟨φ⟩⟩ := hY
  obtain ⟨k', hk'2n, -, ⟨ψ⟩⟩ := hX
  obtain ⟨hkn, hn2, hm⟩ := two_pow_dihedral hn hk2n
  have hxY : x ∈ Y := hYgen ▸ mem_sup_left (mem_zpowers x)
  have hzY : z ∈ Y := hYgen ▸ mem_sup_right (mem_zpowers z)
  have hzz : z * z = 1 := by
    rw [← sq]
    exact hz ▸ pow_orderOf_eq_one z
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hXcard : Nat.card X = k := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
    omega
  have hScard : Nat.card (X.subgroupOf Y) = k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv]
    exact hXcard
  have key := dih_index_two_abs (Q := ↥Y) (k := k) (m := 2 ^ (n - 2)) (by omega) hm φ
    (x := ⟨x, hxY⟩) (z := ⟨z, hzY⟩) (by rw [Subgroup.orderOf_mk, hx, hkn])
    (Subtype.ext hzz) (Subtype.ext (by simpa [hzinv] using hzx)) (X.subgroupOf Y) hScard hzX
  have h1 := congrArg (Subgroup.map Y.subtype) key
  rw [Subgroup.map_subgroupOf_eq_of_le hXY, zpowers_sup_map] at h1
  exact h1

end CFSG.GH74.GLS.SP.Local
