module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi22No65
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveSylow
public import Certificates.Certificate17220

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.Th.Native CFSG.Perm CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
  CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23ThirteenNative
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_common_fixed {X : Type*} [Finite X] {p : ℕ} [Fact p.Prime] (f g : Equiv.Perm X)
    (hfg : f * g = g * f) (hg : g ^ p = 1) (hp : ¬ p ∣ Nat.card {x : X // f x = x}) :
    ∃ x : X, f x = x ∧ g x = x := by
  classical
  have : Fintype X := Fintype.ofFinite X
  have : Fintype {x : X // f x = x} := Fintype.ofFinite _
  have hk : ∀ k : ℕ, ∀ x : X, f x = x → f ((g ^ k) x) = (g ^ k) x := by
    intro k x hx
    have hc : f * g ^ k = g ^ k * f := (Commute.pow_right (show Commute f g from hfg) k).eq
    have := congrArg (fun h : Equiv.Perm X => h x) hc
    simp only [Equiv.Perm.mul_apply] at this
    rw [this, hx]
  let σ : Equiv.Perm {x : X // f x = x} :=
    { toFun := fun x => ⟨g x.1, by simpa using hk 1 x.1 x.2⟩
      invFun := fun x => ⟨g⁻¹ x.1, by
        have := hk (p - 1) x.1 x.2
        have hgi : g⁻¹ = g ^ (p - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le,
            hg]
        rw [hgi]; exact this⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hσk : ∀ k : ℕ, ∀ x : {x : X // f x = x}, ((σ ^ k) x).1 = (g ^ k) x.1 := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      show g ((σ ^ k) x).1 = _
      rw [ih, pow_succ', Equiv.Perm.mul_apply]
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext x
    show ((σ ^ p) x).1 = x.1
    rw [hσk p x, hg]
    rfl
  have hcard : ¬ p ∣ Fintype.card {x : X // f x = x} := by
    rwa [← Nat.card_eq_fintype_card]
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

theorem false_of_commuting_of_noOrder {G : Type*} [Group G] (h : NoOrder 65 G) (t v : G)
    (hto : orderOf t = 5) (hvo : orderOf v = 13) (htv : t * v = v * t) : False := by
  have hcomm : Commute t v := htv
  have hcop : Nat.Coprime (orderOf t) (orderOf v) := by rw [hto, hvo]; norm_num
  have h65 : orderOf (t * v) = orderOf t * orderOf v :=
    hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  rw [hto, hvo] at h65
  exact h (t * v) h65

section Fi23


theorem mem_fixList_iff_smul {W : Table} {w : CFSG.Sporadic.Fi23.J} (hW : Rep 31671 W w) {j : ℕ} :
    j ∈ fixList W ↔ ∃ hj : j < 31671, w • (⟨j, hj⟩ : Fin 31671) = ⟨j, hj⟩ := by
  unfold fixList
  rw [List.mem_filter, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨hj, h⟩
    refine ⟨hj, Fin.ext ?_⟩
    rw [← idx_of_lt w hj, ← hW j hj]
    exact h
  · rintro ⟨hj, h⟩
    refine ⟨hj, ?_⟩
    rw [hW j hj, idx_of_lt w hj]
    exact congrArg Fin.val h

theorem card_fixed_eq_length {W : Table} {w : CFSG.Sporadic.Fi23.J} (hW : Rep 31671 W w) :
    Nat.card {i : Fin 31671 // w • i = i} = (fixList W).length := by
  have hnd : (fixList W).Nodup := List.Nodup.filter _ List.nodup_range
  let e : {i : Fin 31671 // w • i = i} ≃ {j : ℕ // j ∈ (fixList W).toFinset} :=
    { toFun := fun i => ⟨i.1.val, List.mem_toFinset.2 ((mem_fixList_iff_smul hW).2 ⟨i.1.2, i.2⟩)⟩
      invFun := fun j =>
        ⟨⟨j.1, ((mem_fixList_iff_smul hW).1 (List.mem_toFinset.1 j.2)).1⟩,
          ((mem_fixList_iff_smul hW).1 (List.mem_toFinset.1 j.2)).2⟩
      left_inv := fun i => Subtype.ext (Fin.ext rfl)
      right_inv := fun j => Subtype.ext rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

theorem exists_fixed_conj (w y : CFSG.Sporadic.Fi23.J) (hwy : w * y = y * w) (hy13 : y ^ 13 = 1)
    (hcard : ¬ 13 ∣ Nat.card {i : Fin 31671 // w • i = i}) :
    ∃ i : Fin 31671, conjPt i.val * w = w * conjPt i.val ∧ conjPt i.val * y = y * conjPt i.val := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let π : CFSG.Sporadic.Fi23.J →* Equiv.Perm (Fin 31671) := MulAction.toPermHom CFSG.Sporadic.Fi23.J (Fin 31671)
  have hπ : ∀ (g : CFSG.Sporadic.Fi23.J) (i : Fin 31671), π g i = g • i := fun g i => rfl
  have hfg : π w * π y = π y * π w := by rw [← map_mul, ← map_mul, hwy]
  have hg : π y ^ 13 = 1 := by rw [← map_pow, hy13, map_one]
  have hcard' : ¬ 13 ∣ Nat.card {i : Fin 31671 // π w i = i} := hcard
  obtain ⟨i, hwi, hyi⟩ := exists_common_fixed (π w) (π y) hfg hg hcard'
  refine ⟨i, ?_, ?_⟩
  · have h := (smul_eq_iff w i i).1 hwi
    calc conjPt i.val * w = (w * conjPt i.val * w⁻¹) * w := by rw [h]
      _ = w * conjPt i.val := by group
  · have h := (smul_eq_iff y i i).1 hyi
    calc conjPt i.val * y = (y * conjPt i.val * y⁻¹) * y := by rw [h]
      _ = y * conjPt i.val := by group

theorem noOrder65_J22 : NoOrder 65 ↥CFSG.Sporadic.Fi22.J := fun g hg =>
  noOrder65_Fi22 (CFSG.Sporadic.Fi22.fi22EquivJ.symm g) (by rw [MulEquiv.orderOf_eq]; exact hg)

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five in
theorem noOrder65_J23 : NoOrder 65 ↥CFSG.Sporadic.Fi23.J := by
  have hfin : Finite CFSG.Sporadic.Fi23.J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  obtain ⟨-, hc⟩ := fi23Five_parts
  unfold fi23FiveCore at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h5e', he1'⟩, h5f'⟩, hcomm'⟩, hpow'⟩, -⟩ := hc
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h5e := eq_of_eqTab (rep_eFive.powT hn 5) (Rep.idT hn) h5e'
  have h5f := eq_of_eqTab (rep_fFive.powT hn 5) (Rep.idT hn) h5f'
  have hcomm := eq_of_eqTab (rep_eFive.compT rep_fFive) (rep_fFive.compT rep_eFive) hcomm'
  have he1 := ne_one_of_rep rep_eFive he1'
  have hpow : ∀ k < 5, fFive ≠ eFive ^ k := fun k hk =>
    ne_pow_of_rep rep_fFive rep_eFive k (hpow' k hk)
  have hQ := card_closure_pair_eq_sq hcomm h5e h5f he1 hpow (by rw [card_J]; norm_num)
  have hQfull : Nat.card (Subgroup.closure ({eFive, fFive} : Set CFSG.Sporadic.Fi23.J)) =
      5 ^ (Nat.card (⊤ : Subgroup CFSG.Sporadic.Fi23.J)).factorization 5 := by
    rw [hQ, Subgroup.card_top, card_J,
      show (4089470473293004800 : ℕ) = 5 ^ 2 * 163578818931720192 by norm_num,
      factorization_pow_mul Nat.prime_five 2 _ (by norm_num)]
  have h17 : fi23ThirteenOK orb = true := Certificates.certificate17220
  unfold fi23ThirteenOK at h17
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq] at h17
  intro g hg
  have hg' : orderOf g = 5 * 13 := hg
  have hs : orderOf (g ^ 13) = 5 := by
    rw [orderOf_pow' _ (by norm_num), hg', Nat.gcd_eq_right (dvd_mul_left 13 5)]
  have hy : orderOf (g ^ 5) = 13 := by
    rw [orderOf_pow' _ (by norm_num), hg', Nat.gcd_eq_right (dvd_mul_right 5 13)]
  have hsy : Commute (g ^ 13) (g ^ 5) := Commute.pow_pow_self g 13 5
  obtain ⟨m, -, hmQ⟩ := Co3T.exists_conj_mem_of_full le_top hQfull (Subgroup.mem_top _) hs
  obtain ⟨a, ha, b, hb, hw⟩ := exists_pow_mul_pow_of_mem (by norm_num) hcomm h5e h5f hmQ
  set w : CFSG.Sporadic.Fi23.J := m⁻¹ * g ^ 13 * m with hwdef
  set y' : CFSG.Sporadic.Fi23.J := m⁻¹ * g ^ 5 * m with hy'def
  have hwo : orderOf w = 5 := by rw [hwdef, orderOf_inv_mul_mul, hs]
  have hy'o : orderOf y' = 13 := by rw [hy'def, orderOf_inv_mul_mul, hy]
  have hwy : w * y' = y' * w := by
    calc w * y' = m⁻¹ * (g ^ 13 * g ^ 5) * m := by rw [hwdef, hy'def]; group
      _ = m⁻¹ * (g ^ 5 * g ^ 13) * m := by rw [hsy.eq]
      _ = y' * w := by rw [hwdef, hy'def]; group
  have hab : a + b ≠ 0 := by
    intro h0
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    rw [ha0, hb0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact absurd hwo (by norm_num)
  have hW := (rep_eFive.powT hn a).compT (rep_fFive.powT hn b)
  rw [← hw] at hW
  have hlen := (h17 a ha b hb).resolve_left hab
  have hcard : ¬ 13 ∣ Nat.card {i : Fin 31671 // w • i = i} := by
    rw [card_fixed_eq_length hW]
    intro h13
    exact hlen (Nat.mod_eq_zero_of_dvd h13)
  have hy'13 : y' ^ 13 = 1 := by
    have h := pow_orderOf_eq_one y'
    rw [hy'o] at h
    exact h
  obtain ⟨i, hxw, hxy⟩ := exists_fixed_conj w y' hwy hy'13 hcard
  obtain ⟨n, hn'⟩ := isConj_iff.1 ((isConj_d_iff (conjPt i.val)).2 ⟨i, rfl⟩)
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : CFSG.Sporadic.Fi23.J, s₁ = n⁻¹ * w * n := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : CFSG.Sporadic.Fi23.J, y₁ = n⁻¹ * y' * n := ⟨_, rfl⟩
  have hs₁o : orderOf s₁ = 5 := by rw [hs₁, orderOf_inv_mul_mul, hwo]
  have hy₁o : orderOf y₁ = 13 := by rw [hy₁, orderOf_inv_mul_mul, hy'o]
  have hs₁y₁ : s₁ * y₁ = y₁ * s₁ := by
    calc s₁ * y₁ = n⁻¹ * (w * y') * n := by rw [hs₁, hy₁]; group
      _ = n⁻¹ * (y' * w) * n := by rw [hwy]
      _ = y₁ * s₁ := by rw [hs₁, hy₁]; group
  have hxw' : n * d * n⁻¹ * w = w * (n * d * n⁻¹) := by rw [hn']; exact hxw
  have hxy' : n * d * n⁻¹ * y' = y' * (n * d * n⁻¹) := by rw [hn']; exact hxy
  have hs₁d : s₁ * d = d * s₁ := by
    calc s₁ * d = n⁻¹ * (w * (n * d * n⁻¹)) * n := by rw [hs₁]; group
      _ = n⁻¹ * (n * d * n⁻¹ * w) * n := by rw [hxw']
      _ = d * s₁ := by rw [hs₁]; group
  have hy₁d : y₁ * d = d * y₁ := by
    calc y₁ * d = n⁻¹ * (y' * (n * d * n⁻¹)) * n := by rw [hy₁]; group
      _ = n⁻¹ * (n * d * n⁻¹ * y') * n := by rw [hxy']
      _ = d * y₁ := by rw [hy₁]; group
  let s₀ : Cd := ⟨s₁, mem_Cd.2 hs₁d⟩
  let y₀ : Cd := ⟨y₁, mem_Cd.2 hy₁d⟩
  have hs₀o : orderOf s₀ = 5 := by rw [← Subgroup.orderOf_coe]; exact hs₁o
  have hy₀o : orderOf y₀ = 13 := by rw [← Subgroup.orderOf_coe]; exact hy₁o
  have hs₀y₀ : s₀ * y₀ = y₀ * s₀ := Subtype.ext hs₁y₁
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1
    (show rho s₀ ∈ pi22.range by rw [← range_rho]; exact MonoidHom.mem_range.2 ⟨s₀, rfl⟩)
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.1
    (show rho y₀ ∈ pi22.range by rw [← range_rho]; exact MonoidHom.mem_range.2 ⟨y₀, rfl⟩)
  have hkerne : ∀ u : Cd, orderOf u ≠ 1 → orderOf u ≠ 2 → rho u ≠ 1 := by
    intro u hu1 hu2 h
    have hmem : u ∈ rho.ker := h
    rw [ker_rho] at hmem
    have h2 := orderOf_dvd_of_mem_zpowers hmem
    rw [orderOf_dCd] at h2
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact hu1 h
    · exact hu2 h
  have ht5 : t ^ 5 = 1 := by
    apply pi22_injective
    rw [map_pow, ht, ← map_pow, ← hs₀o, pow_orderOf_eq_one, map_one, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    exact hkerne s₀ (by rw [hs₀o]; norm_num) (by rw [hs₀o]; norm_num) (by rw [← ht, h, map_one])
  have hv13 : v ^ 13 = 1 := by
    apply pi22_injective
    rw [map_pow, hv, ← map_pow, ← hy₀o, pow_orderOf_eq_one, map_one, map_one]
  have hv1 : v ≠ 1 := by
    intro h
    exact hkerne y₀ (by rw [hy₀o]; norm_num) (by rw [hy₀o]; norm_num) (by rw [← hv, h, map_one])
  have htv : t * v = v * t := by
    apply pi22_injective
    rw [map_mul, map_mul, ht, hv, ← map_mul, ← map_mul, hs₀y₀]
  have hto : orderOf t = 5 := orderOf_eq_prime ht5 ht1
  have hvo : orderOf v = 13 := orderOf_eq_prime hv13 hv1
  exact false_of_commuting_of_noOrder noOrder65_J22 t v hto hvo htv

theorem noOrder65_Fi23 : NoOrder 65 NativeSporadic.Fi23 := fun g hg =>
  noOrder65_J23 (fi23EquivJ g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end Fi23

end CFSG.HardMathSupport.Dickson.Sec6.I1431
