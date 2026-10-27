module

public import CFSG.GF2Type.Smith1980Orth.LocalAssembly
public import CFSG.GF2Type.Smith1980Orth.Transport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

variable {G : Type} [Group G]

@[expose] def OOdd (T : Setting G) : Prop :=
  ∀ k : G, k * T.z * k⁻¹ ∈ T.M → k * T.z * k⁻¹ ∉ T.QG →
    Odd {c : G | IsConj T.z c ∧ c ∈ T.QG ⊓ T.Qa k}.ncard

@[expose] def OF3 (T : Setting G) : Prop :=
  ∀ w y : G, IsConj T.z w → w ∈ T.M → w ∉ T.QG → IsConj T.z y → y ∈ T.QG → y ≠ T.z →
    T.cl (w * y * w⁻¹ * y⁻¹) = 0 ∨
      ∃ c, IsConj T.z c ∧ c ∈ T.QG ∧ T.cl c = T.cl (w * y * w⁻¹ * y⁻¹)

@[expose] def FourOne (T : Setting G) : Prop :=
  ∀ x y : G, IsConj T.z x → IsConj T.z y → 4 ∣ orderOf (x * y) →
    orderOf (x * y) = 4 ∧ IsConj T.z ((x * y) ^ 2)

private theorem mul_mul_mul_left {x y : G} (hx : x * x = 1) (hy : y * y = 1) :
    x * y * x * (x * y) = x := by
  calc x * y * x * (x * y) = x * (y * (x * x) * y) := by simp only [mul_assoc]
    _ = x := by rw [hx, mul_one, hy, mul_one]

private theorem mul_mul_mul_right {x y : G} (hx : x * x = 1) (hy : y * y = 1) :
    x * y * y * (x * y) = y := by
  calc x * y * y * (x * y) = x * (y * y) * x * y := by simp only [mul_assoc]
    _ = y := by rw [hy, mul_one, hx, one_mul]

private theorem pow_mul_mul_pow {r u : G} (h : r * u * r = u) (j : ℕ) :
    r ^ j * u * r ^ j = u := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc r ^ (j + 1) * u * r ^ (j + 1) = (r ^ j * r) * u * (r * r ^ j) := by
          rw [← pow_succ r j, ← pow_succ' r j]
      _ = r ^ j * (r * u * r) * r ^ j := by simp only [mul_assoc]
      _ = u := by rw [h, ih]

private theorem isConj_mul_pow_two {r u : G} (h : r * u * r = u) (j : ℕ) :
    IsConj u (u * r ^ (2 * j)) := by
  have h1 := pow_mul_mul_pow h j
  have h2 : (r ^ j)⁻¹ * u = u * r ^ j := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc]
    exact h1.symm
  refine isConj_iff.mpr ⟨(r ^ j)⁻¹, ?_⟩
  calc (r ^ j)⁻¹ * u * ((r ^ j)⁻¹)⁻¹ = (r ^ j)⁻¹ * u * r ^ j := by rw [inv_inv]
    _ = u * r ^ j * r ^ j := by rw [h2]
    _ = u * r ^ (2 * j) := by rw [mul_assoc, ← pow_add, two_mul]

private theorem commute_of_mul_mul_eq {a u : G} (haa : a * a = 1) (h : a * u * a = u) :
    Commute u a := by
  show u * a = a * u
  calc u * a = a * u * a * a := by rw [h]
    _ = a * u * (a * a) := by simp only [mul_assoc]
    _ = a * u := by rw [haa, mul_one]

private theorem exists_fixed_of_odd_ncard {α : Type*} [Finite α] (X : Set α) (φ : α → α)
    (hφ : ∀ c, φ (φ c) = c) (hX : ∀ c ∈ X, φ c ∈ X) (hodd : Odd X.ncard) :
    ∃ c ∈ X, φ c = c := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  let σ : Equiv.Perm X :=
    { toFun := fun c => ⟨φ c, hX c c.2⟩
      invFun := fun c => ⟨φ c, hX c c.2⟩
      left_inv := fun c => Subtype.ext (hφ c)
      right_inv := fun c => Subtype.ext (hφ c) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext c
    simp only [pow_one, _root_.sq, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hφ c
  have hcard : ¬ 2 ∣ Fintype.card X := by
    rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, ← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  obtain ⟨c, hc⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

private theorem mem_QG_conjBy_of_isConj_mul (S : Setting G) {g x : G}
    (h34a : OE34a (S.conjBy g)) (hx : IsConj S.z x) (hxa : Commute x (S.conjBy g).z)
    (hxa' : IsConj S.z (x * (S.conjBy g).z)) : x ∈ (S.conjBy g).QG := by
  by_contra hQ
  exact h34a x ((S.isConj_conjBy_z_iff g).mpr hx)
    ((S.conjBy g).mem_M_iff.mpr hxa.symm.eq.symm) hQ ((S.isConj_conjBy_z_iff g).mpr hxa')

variable [Finite G]

private theorem pow_four_of_isConj (S : Setting G)
    (hall : ∀ g : G, OE34a (S.conjBy g) ∧ OOdd (S.conjBy g) ∧ OF3 (S.conjBy g)) {x y a : G}
    (hx : IsConj S.z x) (hy : IsConj S.z y) (ha : IsConj S.z a) (hxa : Commute x a)
    (hya : Commute y a) (hxa' : IsConj S.z (x * a)) (hya' : IsConj S.z (y * a)) :
    (x * y) ^ 4 = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  have hTz : (S.conjBy g).z = a := hg
  have hxQ := mem_QG_conjBy_of_isConj_mul S (hall g).1 hx (by rw [hTz]; exact hxa)
    (by rw [hTz]; exact hxa')
  have hyQ := mem_QG_conjBy_of_isConj_mul S (hall g).1 hy (by rw [hTz]; exact hya)
    (by rw [hTz]; exact hya')
  exact (S.conjBy g).pow_four_eq_one ((S.conjBy g).QG.mul_mem hxQ hyQ)

theorem isConj_of_swap (S : Setting G)
    (hall : ∀ g : G, OE34a (S.conjBy g) ∧ OOdd (S.conjBy g) ∧ OF3 (S.conjBy g)) {x w a : G}
    (hx : IsConj S.z x) (hw : IsConj S.z w) (ha1 : a ≠ 1) (hxa : Commute x a)
    (hwxw : w * x * w = x * a) : IsConj S.z a := by
  by_contra hna
  have hxi := SME.inv_eq_of_isConj S hx
  have hwi := SME.inv_eq_of_isConj S hw
  have hxx := SmithQ.mul_self_eq_one_of_isConj S hx
  have hww := SmithQ.mul_self_eq_one_of_isConj S hw
  obtain ⟨gx, hgx⟩ := isConj_iff.mp hx
  obtain ⟨-, hOddx, -⟩ := hall gx
  have hTxz : (S.conjBy gx).z = x := hgx
  have hxQx : x ∈ (S.conjBy gx).QG := hTxz ▸ (S.conjBy gx).z_mem_QG
  have haQx : a ∉ (S.conjBy gx).QG := by
    intro haQ
    have hd : gx⁻¹ * a * gx ∈ S.QG := (SME.mem_Qa_iff S gx a).mp haQ
    have hne : a ≠ gx * S.z * gx⁻¹ := by
      rw [hgx]
      exact fun h => hna (h ▸ hx)
    have hc := SME.isConj_mul_of_mem_Qa S hd ha1 hne
    rw [hgx] at hc
    have hax : IsConj x (a * x) := isConj_iff.mpr ⟨w, by rw [hwi, hwxw, hxa.eq]⟩
    exact hna ((hx.trans hax).trans hc.symm)
  have hxaQx : x * a ∉ (S.conjBy gx).QG := by
    intro h
    apply haQx
    have := (S.conjBy gx).QG.mul_mem ((S.conjBy gx).QG.inv_mem hxQx) h
    rwa [inv_mul_cancel_left] at this
  have hxaM : x * a ∈ (S.conjBy gx).M :=
    (S.conjBy gx).mem_M_iff.mpr (by rw [hTxz, mul_assoc, ← hxa.eq])
  have hk1 : w * (S.conjBy gx).z * w⁻¹ ∈ (S.conjBy gx).M := by
    rw [hTxz, hwi, hwxw]
    exact hxaM
  have hk2 : w * (S.conjBy gx).z * w⁻¹ ∉ (S.conjBy gx).QG := by
    rw [hTxz, hwi, hwxw]
    exact hxaQx
  have hconj : ∀ c, IsConj (S.conjBy gx).z c → IsConj (S.conjBy gx).z (w * c * w) :=
    fun c hc => hc.trans (isConj_iff.mpr ⟨w, by rw [hwi]⟩)
  have hinv : ∀ c, w * (w * c * w) * w = c := fun c => by
    calc w * (w * c * w) * w = (w * w) * c * (w * w) := by simp only [mul_assoc]
      _ = c := by rw [hww, one_mul, mul_one]
  obtain ⟨v, ⟨hvc, hvQ, hvw⟩, hvfix⟩ := exists_fixed_of_odd_ncard
    {c : G | IsConj (S.conjBy gx).z c ∧ c ∈ (S.conjBy gx).QG ⊓ (S.conjBy gx).Qa w}
    (fun c => w * c * w) hinv
    (fun c ⟨hc, hcQ, hcw⟩ => by
      have h1 : w⁻¹ * c * w ∈ (S.conjBy gx).QG := (SME.mem_Qa_iff _ w c).mp hcw
      rw [hwi] at h1
      refine ⟨hconj c hc, h1, (SME.mem_Qa_iff _ w _).mpr ?_⟩
      rw [hwi, hinv]
      exact hcQ)
    (hOddx w hk1 hk2)
  have hvfix : w * v * w = v := hvfix
  have hvS : IsConj S.z v := (S.isConj_conjBy_z_iff gx).mp hvc
  obtain ⟨gv, hgv⟩ := isConj_iff.mp hvS
  obtain ⟨-, -, hF3v⟩ := hall gv
  have hTvz : (S.conjBy gv).z = v := hgv
  have hnav : a ≠ v := fun h => hna (by rw [h]; exact hvS)
  have hvx : v ≠ x := by
    intro h
    apply hxaQx
    have h1 : w⁻¹ * v * w ∈ (S.conjBy gx).QG := (SME.mem_Qa_iff _ w v).mp hvw
    rwa [hwi, h, hwxw] at h1
  have hvxa : v ≠ x * a := fun h => hxaQx (by rw [← h]; exact hvQ)
  have hxQv : x ∈ (S.conjBy gv).QG := by
    have hQ : gx⁻¹ * (gv * S.z * gv⁻¹) * gx ∈ S.QG := by
      rw [hgv]
      exact (SME.mem_Qa_iff S gx v).mp hvQ
    have hne : gv * S.z * gv⁻¹ ≠ gx * S.z * gx⁻¹ := by
      rw [hgv, hgx]
      exact hvx
    have h := SME.mem_Qa_symm S hQ hne
    rw [hgx] at h
    exact (SME.mem_Qa_iff S gv x).mpr h
  have hxaQv : x * a ∈ (S.conjBy gv).QG := by
    have hQ : (w * gx)⁻¹ * (gv * S.z * gv⁻¹) * (w * gx) ∈ S.QG := by
      rw [hgv, mul_inv_rev, hwi]
      have e : gx⁻¹ * w * v * (w * gx) = gx⁻¹ * v * gx := by
        calc gx⁻¹ * w * v * (w * gx) = gx⁻¹ * (w * v * w) * gx := by simp only [mul_assoc]
          _ = gx⁻¹ * v * gx := by rw [hvfix]
      rw [e]
      exact (SME.mem_Qa_iff S gx v).mp hvQ
    have hwgx : (w * gx) * S.z * (w * gx)⁻¹ = x * a := by
      calc (w * gx) * S.z * (w * gx)⁻¹ = w * (gx * S.z * gx⁻¹) * w⁻¹ := by group
        _ = x * a := by rw [hgx, hwi, hwxw]
    have hne : gv * S.z * gv⁻¹ ≠ (w * gx) * S.z * (w * gx)⁻¹ := by
      rw [hgv, hwgx]
      exact hvxa
    have h := SME.mem_Qa_symm S hQ hne
    rw [hwgx] at h
    exact (SME.mem_Qa_iff S gv (x * a)).mpr h
  have haQv : a ∈ (S.conjBy gv).QG := by
    have := (S.conjBy gv).QG.mul_mem ((S.conjBy gv).QG.inv_mem hxQv) hxaQv
    rwa [inv_mul_cancel_left] at this
  have hwMv : w ∈ (S.conjBy gv).M := by
    refine (S.conjBy gv).mem_M_iff.mpr ?_
    rw [hTvz]
    calc w * v = w * v * (w * w) := by rw [hww, mul_one]
      _ = (w * v * w) * w := by simp only [mul_assoc]
      _ = v * w := by rw [hvfix]
  have hcomm : w * x * w⁻¹ * x⁻¹ = a := by
    rw [hwi, hxi, hwxw, hxa.eq, mul_assoc, hxx, mul_one]
  by_cases hwQv : w ∈ (S.conjBy gv).QG
  · rcases (S.conjBy gv).commutator_eq_one_or_z hwQv hxQv with h | h
    · exact ha1 (hcomm.symm.trans h)
    · exact hnav ((hcomm.symm.trans h).trans hTvz)
  · rcases hF3v w x ((S.isConj_conjBy_z_iff gv).mpr hw) hwMv hwQv
        ((S.isConj_conjBy_z_iff gv).mpr hx) hxQv
        (by rw [hTvz]; exact hvx.symm) with h0 | ⟨c, hcC, hcQ, hcl⟩
    · rw [hcomm] at h0
      rcases ((S.conjBy gv).cl_eq_zero_iff haQv).mp h0 with h | h
      · exact ha1 h
      · exact hnav (h.trans hTvz)
    · rw [hcomm] at hcl
      have hcS : IsConj S.z c := (S.isConj_conjBy_z_iff gv).mp hcC
      rcases ((S.conjBy gv).cl_eq_cl_iff hcQ haQv).mp hcl with h | h
      · exact hna (by rw [h]; exact hcS)
      · have hc1 : c ≠ 1 := SME.ne_one_of_isConj S hcS
        have hcv : c ≠ gv * S.z * gv⁻¹ := by
          intro hce
          apply ha1
          rw [h, hce]
          exact (S.conjBy gv).z_mul_z
        have hd : gv⁻¹ * c * gv ∈ S.QG := (SME.mem_Qa_iff S gv c).mp hcQ
        have hconj := SME.isConj_mul_of_mem_Qa S hd hc1 hcv
        exact hna (hcS.trans (by rw [h]; exact hconj))

theorem fourOne_of [IsSimpleGroup G] (S : Setting G)
    (hall : ∀ g : G, OE34a (S.conjBy g) ∧ OOdd (S.conjBy g) ∧ OF3 (S.conjBy g)) :
    FourOne S := by
  intro x y hx hy h4
  have hxx := SmithQ.mul_self_eq_one_of_isConj S hx
  have hyy := SmithQ.mul_self_eq_one_of_isConj S hy
  obtain ⟨m, hm⟩ := h4
  obtain ⟨r, hr⟩ : ∃ r, r = x * y := ⟨_, rfl⟩
  rw [← hr] at hm ⊢
  have hpos : 0 < orderOf r := orderOf_pos r
  have hm1 : 1 ≤ m := by omega
  have hrx : r * x * r = x := by rw [hr]; exact mul_mul_mul_left hxx hyy
  have hry : r * y * r = y := by rw [hr]; exact mul_mul_mul_right hxx hyy
  have hr4 : r ^ (4 * m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one r
  have haa : r ^ (2 * m) * r ^ (2 * m) = 1 := by
    rw [← pow_add, show 2 * m + 2 * m = 4 * m by ring]
    exact hr4
  have ha1 : r ^ (2 * m) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hxa : Commute x (r ^ (2 * m)) := commute_of_mul_mul_eq haa (pow_mul_mul_pow hrx _)
  have hya : Commute y (r ^ (2 * m)) := commute_of_mul_mul_eq haa (pow_mul_mul_pow hry _)
  have hxa' : IsConj S.z (x * r ^ (2 * m)) := hx.trans (isConj_mul_pow_two hrx m)
  have hya' : IsConj S.z (y * r ^ (2 * m)) := hy.trans (isConj_mul_pow_two hry m)
  have hw : IsConj S.z (x * r ^ m) := by
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' m
    · rw [hj]
      exact hx.trans (isConj_mul_pow_two hrx j)
    · rw [hj, pow_succ', ← mul_assoc, show x * r = y by rw [hr, ← mul_assoc, hxx, one_mul]]
      exact hy.trans (isConj_mul_pow_two hry j)
  have hwxw : x * r ^ m * x * (x * r ^ m) = x * r ^ (2 * m) := by
    calc x * r ^ m * x * (x * r ^ m) = x * r ^ m * (x * x) * r ^ m := by simp only [mul_assoc]
      _ = x * r ^ (2 * m) := by rw [hxx, mul_one, mul_assoc, ← pow_add, two_mul]
  have ha : IsConj S.z (r ^ (2 * m)) := isConj_of_swap S hall hx hw ha1 hxa hwxw
  have h44 : (x * y) ^ 4 = 1 := pow_four_of_isConj S hall hx hy ha hxa hya hxa' hya'
  rw [← hr] at h44
  have hd : 4 * m ∣ 4 := hm ▸ orderOf_dvd_of_pow_eq_one h44
  have hm' : m = 1 := by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  subst hm'
  exact ⟨hm, by simpa using ha⟩

theorem oe44_of_fourOne (S : Setting G) (h : FourOne S) : OE44 S := by
  intro x y hx hy _ _ _ _ h2 h4
  refine h x y hx hy ?_
  have h16 : (x * y) ^ 16 = 1 := by
    have := S.pow_four_eq_one h4
    rwa [← pow_mul] at this
  have hd : orderOf (x * y) ∣ 16 := orderOf_dvd_of_pow_eq_one h16
  have hn2 : ¬ orderOf (x * y) ∣ 2 := by
    intro h2'
    apply h2
    rw [orderOf_dvd_iff_pow_eq_one.mp h2']
    exact S.QG.one_mem
  have hle : orderOf (x * y) < 17 := Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hd)
  have key : ∀ n < 17, n ∣ 16 → ¬ n ∣ 2 → 4 ∣ n := by decide
  exact key _ hle hd hn2

end CFSG.GF2Type.Smith1980Orth
