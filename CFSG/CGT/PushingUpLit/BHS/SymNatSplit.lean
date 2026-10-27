module

public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatThree
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.RankThree.PartOne

section Norm

variable {V : Type*} [CommGroup V]

theorem inv_eq_self_of_sq (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, hV])

theorem apply_three_of_pow_three {d : MulAut V} (hd : d ^ 3 = 1) (v : V) : d (d (d v)) = v := by
  have h := congrArg (fun f : MulAut V => f v) hd
  simpa [pow_succ, MulAut.mul_apply] using h

theorem norm_eq_one_of_mem_commV {d : MulAut V} (hd : d ^ 3 = 1) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers d)) : w * d w * d (d w) = 1 := by
  let N : V →* V := MonoidHom.mk' (fun v => v * d v * d (d v)) fun x y => by
    simp only [map_mul]
    ac_rfl
  have hN : ∀ v, N (d v) = N v := by
    intro v
    show d v * d (d v) * d (d (d v)) = v * d v * d (d v)
    rw [apply_three_of_pow_three hd]
    ac_rfl
  have hle : commV (Subgroup.zpowers d) ≤ N.ker := by
    rw [G6.commV_le_iff]
    intro x hx v
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases zpow_eq_one_or_self_or_sq hd k with h | h | h
    · rw [h, MulAut.one_apply]
    · rw [h]
      exact hN v
    · rw [h, pow_two, MulAut.mul_apply, hN, hN]
  exact hle hw

theorem eq_one_of_mem_commV_of_apply_eq (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V}
    (hd : d ^ 3 = 1) {w : V} (hw : w ∈ commV (Subgroup.zpowers d)) (hfix : d w = w) : w = 1 := by
  have h := norm_eq_one_of_mem_commV hd hw
  rw [hfix, hfix, mul_assoc, ← pow_two, hV, mul_one] at h
  exact h

theorem eq_comm_of_mem_commV (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V} (hd : d ^ 3 = 1) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers d)) : d (d w) * (d w)⁻¹ = w := by
  have h := norm_eq_one_of_mem_commV hd hw
  rw [eq_inv_of_mul_eq_one_right h, inv_eq_self_of_sq hV, inv_eq_self_of_sq hV, mul_assoc,
    ← pow_two, hV, mul_one]

theorem apply_mem_commV_zpowers {d : MulAut V} {w : V} (hw : w ∈ commV (Subgroup.zpowers d)) :
    d w ∈ commV (Subgroup.zpowers d) :=
  G6.apply_mem_commV (fun _ hx => Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_zpowers d) hx) (Subgroup.inv_mem _ (Subgroup.mem_zpowers d))) hw

theorem apply_mem_commV_zpowers_conj {a : MulAut V} (h : MulAut V) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers a)) : h w ∈ commV (Subgroup.zpowers (h * a * h⁻¹)) := by
  have hle : commV (Subgroup.zpowers a) ≤
      (commV (Subgroup.zpowers (h * a * h⁻¹))).comap h.toMonoidHom := by
    rw [G6.commV_le_iff]
    intro x hx v
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h1 := G6.mem_commV_of_mem (Subgroup.zpow_mem_zpowers (h * a * h⁻¹) k) (h v)
    have h2 : (h * a * h⁻¹) ^ k = h * a ^ k * h⁻¹ := by
      rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
    rw [h2] at h1
    simpa [Subgroup.mem_comap, MulAut.mul_apply] using h1
  exact hle hw

@[expose] def commLe (R : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v, g v * v⁻¹ ∈ R}
  mul_mem' := fun {a b} ha hb v => by
    have h : (a * b) v * v⁻¹ = (a (b v) * (b v)⁻¹) * (b v * v⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [h]
    exact R.mul_mem (ha (b v)) (hb v)
  one_mem' := fun v => by simp
  inv_mem' := fun {a} ha v => by
    have h := R.inv_mem (ha (a⁻¹ v))
    rw [MulAut.apply_inv_self, mul_inv_rev, inv_inv] at h
    exact h

theorem commV_le_of_le_commLe {K : Subgroup (MulAut V)} {R : Subgroup V} (h : K ≤ commLe R) :
    commV K ≤ R :=
  G6.commV_le_iff.2 fun _ hx v => h hx v

end Norm

section Perm

variable {n : ℕ}

@[expose] def cyc (i j k : Fin n) : Equiv.Perm (Fin n) := Equiv.swap i j * Equiv.swap i k

theorem cyc_isThreeCycle {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (cyc i j k).IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same hij hik hjk

theorem conj_cyc (g : Equiv.Perm (Fin n)) (i j k : Fin n) :
    g * cyc i j k * g⁻¹ = cyc (g i) (g j) (g k) := by
  rw [cyc, cyc, Equiv.swap_apply_apply, Equiv.swap_apply_apply]
  group

theorem cyc_inv (i j k : Fin n) : (cyc i j k)⁻¹ = cyc i k j := by
  simp [cyc, mul_inv_rev, Equiv.swap_inv]

theorem cyc_swap12 {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    cyc j i k = cyc i k j := by
  ext m
  simp only [cyc, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem cyc_apply_of_ne {i j k m : Fin n} (hi : m ≠ i) (hj : m ≠ j) (hk : m ≠ k) :
    cyc i j k m = m := by
  simp [cyc, Equiv.swap_apply_of_ne_of_ne, hi, hj, hk]

theorem cyc_apply_first {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) :
    cyc i j k i = k := by
  simp [cyc, Equiv.swap_apply_of_ne_of_ne hik.symm hjk.symm]

theorem cyc_apply_third (i j k : Fin n) : cyc i j k k = j := by
  simp [cyc]

@[expose] def pairVec (a b : Fin n) : ↥(coreMod n) :=
  mkEven (fun m => (if m = a then 1 else 0) + (if m = b then 1 else 0)) (by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact CharTwo.add_self_eq_zero 1)

theorem vcoord_pairVec (a b m : Fin n) :
    vcoord (pairVec a b) m = (if m = a then 1 else 0) + (if m = b then 1 else 0) := rfl

theorem pairVec_comm (a b : Fin n) : pairVec a b = pairVec b a :=
  vcoord_ext fun m => by rw [vcoord_pairVec, vcoord_pairVec, add_comm]

theorem pairVec_self (a : Fin n) : pairVec a a = 1 :=
  vcoord_ext fun m => by rw [vcoord_pairVec, vcoord_one, CharTwo.add_self_eq_zero]

theorem pairVec_mul (a b c : Fin n) : pairVec a b * pairVec a c = pairVec b c := by
  refine vcoord_ext fun m => ?_
  rw [vcoord_mul, vcoord_pairVec, vcoord_pairVec, vcoord_pairVec]
  have h : ∀ x y z : ZMod 2, x + y + (x + z) = y + z := fun x y z => by
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]
  exact h _ _ _

theorem coreAct_pairVec (σ : Equiv.Perm (Fin n)) (a b : Fin n) :
    coreAct n σ (pairVec a b) = pairVec (σ a) (σ b) := by
  refine vcoord_ext fun m => ?_
  rw [vcoord_coreAct, vcoord_pairVec, vcoord_pairVec]
  simp only [Equiv.Perm.inv_eq_iff_eq]

theorem coreMod_inv_eq (v : ↥(coreMod n)) : v⁻¹ = v := vcoord_ext fun m => vcoord_inv v m

theorem coreAct_cyc_pairVec {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) :
    coreAct n (cyc i j k) (pairVec i k) * (pairVec i k)⁻¹ = pairVec i j := by
  rw [coreAct_pairVec, cyc_apply_first hik hjk, cyc_apply_third, coreMod_inv_eq, pairVec_comm i k,
    pairVec_mul, pairVec_comm]

theorem vcoord_comm_eq_zero {σ : Equiv.Perm (Fin n)} (u : ↥(coreMod n)) {m : Fin n}
    (hm : σ⁻¹ m = m) : vcoord (coreAct n σ u * u⁻¹) m = 0 := by
  rw [vcoord_mul, vcoord_inv, vcoord_coreAct, hm, CharTwo.add_self_eq_zero]

theorem cyc_inv_apply_of_ne {i j k m : Fin n} (hi : m ≠ i) (hj : m ≠ j) (hk : m ≠ k) :
    (cyc i j k)⁻¹ m = m := by
  rw [cyc_inv]
  exact cyc_apply_of_ne hi hk hj

theorem eq_of_vcoord_three {i j k : Fin n} {v w : ↥(coreMod n)}
    (hv : ∀ m, m ≠ i → m ≠ j → m ≠ k → vcoord v m = 0)
    (hw : ∀ m, m ≠ i → m ≠ j → m ≠ k → vcoord w m = 0)
    (hi : vcoord v i = vcoord w i) (hj : vcoord v j = vcoord w j)
    (hk : vcoord v k = vcoord w k) : v = w := by
  refine vcoord_ext fun m => ?_
  by_cases hmi : m = i
  · rw [hmi, hi]
  by_cases hmj : m = j
  · rw [hmj, hj]
  by_cases hmk : m = k
  · rw [hmk, hk]
  rw [hv m hmi hmj hmk, hw m hmi hmj hmk]

theorem eq_one_or_pairVec {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {v : ↥(coreMod n)} (hv : ∀ m, m ≠ i → m ≠ j → m ≠ k → vcoord v m = 0) :
    v = 1 ∨ v = pairVec i j ∨ v = pairVec i k ∨ v = pairVec j k := by
  have hs : vcoord v i + vcoord v j + vcoord v k = 0 := by
    have h1 : ∑ m ∈ ({i, j, k} : Finset (Fin n)), vcoord v m = ∑ m, vcoord v m :=
      Finset.sum_subset (Finset.subset_univ _) fun m _ hm => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
        exact hv m hm.1 hm.2.1 hm.2.2
    rw [sum_vcoord, Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
      Finset.sum_singleton, ← add_assoc] at h1
    exact h1
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hp : ∀ a b : Fin n, (a = i ∨ a = j ∨ a = k) → (b = i ∨ b = j ∨ b = k) →
      ∀ m, m ≠ i → m ≠ j → m ≠ k → vcoord (pairVec a b) m = 0 := by
    intro a b ha hb m hmi hmj hmk
    have hma : m ≠ a := by rcases ha with rfl | rfl | rfl <;> assumption
    have hmb : m ≠ b := by rcases hb with rfl | rfl | rfl <;> assumption
    simp [vcoord_pairVec, hma, hmb]
  have h1 : ∀ m, m ≠ i → m ≠ j → m ≠ k → vcoord (1 : ↥(coreMod n)) m = 0 :=
    fun m _ _ _ => vcoord_one m
  have hpij := hp i j (Or.inl rfl) (Or.inr (Or.inl rfl))
  have hpik := hp i k (Or.inl rfl) (Or.inr (Or.inr rfl))
  have hpjk := hp j k (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  rcases key (vcoord v i) with hi | hi <;> rcases key (vcoord v j) with hj | hj <;>
    rcases key (vcoord v k) with hk | hk <;> rw [hi, hj, hk] at hs
  · exact Or.inl (eq_of_vcoord_three hv h1 (by simp [hi, vcoord_one])
      (by simp [hj, vcoord_one]) (by simp [hk, vcoord_one]))
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact Or.inr (Or.inr (Or.inr (eq_of_vcoord_three hv hpjk
      (by simp [hi, vcoord_pairVec, hij, hik])
      (by simp [hj, vcoord_pairVec, hjk])
      (by simp [hk, vcoord_pairVec, hjk.symm]))))
  · exact absurd hs (by decide)
  · exact Or.inr (Or.inr (Or.inl (eq_of_vcoord_three hv hpik
      (by simp [hi, vcoord_pairVec, hik])
      (by simp [hj, vcoord_pairVec, hij.symm, hjk])
      (by simp [hk, vcoord_pairVec, hik.symm]))))
  · exact Or.inr (Or.inl (eq_of_vcoord_three hv hpij
      (by simp [hi, vcoord_pairVec, hij])
      (by simp [hj, vcoord_pairVec, hij.symm])
      (by simp [hk, vcoord_pairVec, hik.symm, hjk.symm])))
  · exact absurd hs (by decide)

theorem cyc_apply_second {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) : cyc i j k j = i := by
  simp [cyc, Equiv.swap_apply_of_ne_of_ne hij.symm hjk]

theorem exists_notMem_finset {s : Finset (Fin n)} (hs : s.card < n) : ∃ m, m ∉ s := by
  have h : s.card < (Finset.univ : Finset (Fin n)).card := by simpa using hs
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨m, hm⟩

theorem exists_ne_ne (h3 : 3 ≤ n) (a b : Fin n) : ∃ k, k ≠ a ∧ k ≠ b := by
  obtain ⟨k, hk⟩ := exists_notMem_finset (s := {a, b}) (lt_of_le_of_lt Finset.card_le_two h3)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk⟩

theorem exists_ne_four (hn : Odd n) {i j k k' : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hik' : i ≠ k') (hjk : j ≠ k) (hjk' : j ≠ k') (hkk' : k ≠ k') :
    ∃ m, m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ k' := by
  have h4 : 4 < n := by
    obtain ⟨r, hr⟩ := hn
    have := i.isLt
    have := j.isLt
    have := k.isLt
    have := k'.isLt
    have := Fin.val_ne_of_ne hij
    have := Fin.val_ne_of_ne hik
    have := Fin.val_ne_of_ne hik'
    have := Fin.val_ne_of_ne hjk
    have := Fin.val_ne_of_ne hjk'
    have := Fin.val_ne_of_ne hkk'
    omega
  obtain ⟨m, hm⟩ := exists_notMem_finset (s := {i, j, k, k'})
    (lt_of_le_of_lt Finset.card_le_four h4)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact ⟨m, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2⟩

theorem exists_eq_cyc (h3 : 3 ≤ n) {τ : Equiv.Perm (Fin n)} (hτ : τ.IsThreeCycle) :
    ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ τ = cyc a b c := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hc := cyc_isThreeCycle h01 h02 h12
  obtain ⟨g, hg⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (hc.trans hτ.symm))
  refine ⟨g ⟨0, by omega⟩, g ⟨1, by omega⟩, g ⟨2, by omega⟩, fun h => h01 (g.injective h),
    fun h => h02 (g.injective h), fun h => h12 (g.injective h), ?_⟩
  rw [← hg, conj_cyc]

theorem sign_eq_one_of_odd_orderOf {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h : Odd (orderOf σ)) : Equiv.Perm.sign σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact h1
  · have h2 := congrArg Equiv.Perm.sign (pow_orderOf_eq_one σ)
    rw [map_pow, h1, h.neg_one_pow, map_one] at h2
    exact absurd h2 (by decide)

theorem opResidual_perm_eq_alternating (α : Type*) [Fintype α] [DecidableEq α] :
    opResidual 2 (⊤ : Subgroup (Equiv.Perm α)) = alternatingGroup α := by
  apply le_antisymm
  · rw [opResidual, Subgroup.closure_le]
    rintro σ ⟨-, hodd⟩
    exact Equiv.Perm.mem_alternatingGroup.2
      (sign_eq_one_of_odd_orderOf (Nat.coprime_two_right.1 hodd))
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro σ hσ
    exact mem_opResidual_of_coprime (Subgroup.mem_top σ) (by rw [hσ.orderOf]; decide)

end Perm

section Sum

variable {G : Type*} [CommGroup G] {n : ℕ}

@[expose] def vsum (Y : Fin n → G) (v : ↥(coreMod n)) : G := ∏ m, Y m ^ (vcoord v m).val

theorem pow_val_add (hG : ∀ g : G, g ^ 2 = 1) (g : G) (a b : ZMod 2) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  have h11 : (1 + 1 : ZMod 2) = 0 := rfl
  rcases key a with rfl | rfl <;> rcases key b with rfl | rfl
  · rw [add_zero, hv0, pow_zero, one_mul]
  · rw [zero_add, hv0, pow_zero, one_mul]
  · rw [add_zero, hv0, pow_zero, mul_one]
  · rw [h11, hv0, hv1, pow_zero, pow_one, ← pow_two, hG]

theorem vsum_mul (hG : ∀ g : G, g ^ 2 = 1) (Y : Fin n → G) (u v : ↥(coreMod n)) :
    vsum Y (u * v) = vsum Y u * vsum Y v := by
  simp only [vsum, vcoord_mul, pow_val_add hG, Finset.prod_mul_distrib]

theorem vsum_one (Y : Fin n → G) : vsum Y 1 = 1 := by
  simp only [vsum, vcoord_one]
  exact Finset.prod_eq_one fun m _ => pow_zero (Y m)

theorem vsum_pairVec (Y : Fin n → G) {a b : Fin n} (hab : a ≠ b) :
    vsum Y (pairVec a b) = Y a * Y b := by
  have hv0 : (0 : ZMod 2).val = 0 := rfl
  have hv1 : (1 : ZMod 2).val = 1 := rfl
  rw [vsum, Finset.prod_eq_mul a b hab]
  · simp [vcoord_pairVec, hab, hab.symm, hv1]
  · intro c _ hc
    simp [vcoord_pairVec, hc.1, hc.2, hv0]
  · simp
  · simp

theorem vcoord_map_prod (f : G →* ↥(coreMod n)) (s : Finset (Fin n)) (g : Fin n → G)
    (q : Fin n) : vcoord (f (∏ m ∈ s, g m)) q = ∑ m ∈ s, vcoord (f (g m)) q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, map_one, Finset.sum_empty]
    rfl
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih, map_mul]
    rfl

theorem vcoord_map_pow (f : G →* ↥(coreMod n)) (g : G) (k : ℕ) (q : Fin n) :
    vcoord (f (g ^ k)) q = k • vcoord (f g) q := by
  induction k with
  | zero =>
    rw [pow_zero, map_one, zero_smul]
    rfl
  | succ k ih =>
    rw [pow_succ, succ_nsmul, ← ih, map_mul]
    rfl

theorem vcoord_map_vsum (f : G →* ↥(coreMod n)) (Y : Fin n → G) (v : ↥(coreMod n))
    (q : Fin n) : vcoord (f (vsum Y v)) q = ∑ m, vcoord v m * vcoord (f (Y m)) q := by
  rw [vsum, vcoord_map_prod]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [vcoord_map_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]

end Sum

section Split

variable {V : Type*} [CommGroup V] {n : ℕ}

structure SymSplitData (X K : Subgroup (MulAut V)) (n : ℕ) where
  θ : X ≃* Equiv.Perm (Fin n)
  β : ↥(commV K) →* coreMod n
  surj : Function.Surjective β
  ker_fix : ∀ w : ↥(commV K), β w = 1 → (w : V) ∈ fixV K
  map_apply : ∀ (x : X) (p : ↥(commV K)) (hp : (x : MulAut V) p ∈ commV K),
    β ⟨(x : MulAut V) p, hp⟩ = coreAct n (θ x) (β p)
  apply_mem : ∀ x ∈ X, ∀ p ∈ commV K, x p ∈ commV K
  three_mem : ∀ σ : Equiv.Perm (Fin n), σ.IsThreeCycle → ((θ.symm σ : X) : MulAut V) ∈ K

theorem opResidual_le_of_three_cycles {X H : Subgroup (MulAut V)} (θ : X ≃* Equiv.Perm (Fin n))
    (h : ∀ σ : Equiv.Perm (Fin n), σ.IsThreeCycle → ((θ.symm σ : X) : MulAut V) ∈ H) :
    opResidual 2 X ≤ H := by
  rw [opResidual, Subgroup.closure_le]
  rintro x ⟨hxX, hodd⟩
  have hodd' : Odd (orderOf (θ ⟨x, hxX⟩)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact Nat.coprime_two_right.1 hodd
  have hA : θ ⟨x, hxX⟩ ∈ Subgroup.closure {σ : Equiv.Perm (Fin n) | σ.IsThreeCycle} := by
    rw [Equiv.Perm.closure_three_cycles_eq_alternating, Equiv.Perm.mem_alternatingGroup]
    exact sign_eq_one_of_odd_orderOf hodd'
  have hle : Subgroup.closure {σ : Equiv.Perm (Fin n) | σ.IsThreeCycle} ≤
      (H.subgroupOf X).map θ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro σ hσ
    exact ⟨θ.symm σ, Subgroup.mem_subgroupOf.2 (h σ hσ), by simp⟩
  obtain ⟨y, hy, hyx⟩ := hle hA
  have hyx' : y = ⟨x, hxX⟩ := θ.injective hyx
  rw [hyx'] at hy
  exact hy

namespace SymSplitData

variable {X K : Subgroup (MulAut V)} (D : SymSplitData X K n)

@[expose] def dc (σ : Equiv.Perm (Fin n)) : MulAut V := ((D.θ.symm σ : X) : MulAut V)

@[expose] def wt (σ : Equiv.Perm (Fin n)) : Subgroup V := commV (Subgroup.zpowers (D.dc σ))

theorem dc_mul (σ τ : Equiv.Perm (Fin n)) : D.dc (σ * τ) = D.dc σ * D.dc τ := by
  simp [dc]

theorem dc_inv (σ : Equiv.Perm (Fin n)) : D.dc σ⁻¹ = (D.dc σ)⁻¹ := by
  simp [dc]

theorem dc_pow_three {σ : Equiv.Perm (Fin n)} (hσ : σ.IsThreeCycle) : D.dc σ ^ 3 = 1 := by
  have h : σ ^ 3 = 1 := by
    rw [← hσ.orderOf]
    exact pow_orderOf_eq_one σ
  simp only [dc]
  rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]

theorem wt_inv (σ : Equiv.Perm (Fin n)) : D.wt σ⁻¹ = D.wt σ := by
  rw [wt, wt, dc_inv, Subgroup.zpowers_inv]

theorem wt_le {σ : Equiv.Perm (Fin n)} (hσ : σ.IsThreeCycle) : D.wt σ ≤ commV K :=
  G6.commV_mono (Subgroup.zpowers_le.2 (D.three_mem σ hσ))

theorem inj (hV : ∀ v : V, v ^ 2 = 1) {σ : Equiv.Perm (Fin n)} (hσ : σ.IsThreeCycle)
    {y y' : ↥(commV K)} (hy : (y : V) ∈ D.wt σ) (hy' : (y' : V) ∈ D.wt σ)
    (h : D.β y = D.β y') : y = y' := by
  have hz : D.β (y * y'⁻¹) = 1 := by
    rw [map_mul, map_inv, h]
    exact mul_inv_cancel _
  have hfix := D.ker_fix _ hz
  have hmem : ((y * y'⁻¹ : ↥(commV K)) : V) ∈ D.wt σ :=
    Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hy')
  have h1 := eq_one_of_mem_commV_of_apply_eq hV (D.dc_pow_three hσ) hmem
    (hfix _ (D.three_mem σ hσ))
  have h2 : y * y'⁻¹ = 1 := Subtype.ext h1
  exact mul_inv_eq_one.1 h2

theorem exists_lift (σ : Equiv.Perm (Fin n)) (u : ↥(coreMod n)) :
    ∃ y : ↥(commV K), (y : V) ∈ D.wt σ ∧ D.β y = coreAct n σ u * u⁻¹ := by
  obtain ⟨w, rfl⟩ := D.surj u
  have hxw : (D.θ.symm σ : MulAut V) w ∈ commV K := D.apply_mem _ (D.θ.symm σ).2 _ w.2
  refine ⟨⟨_, hxw⟩ * w⁻¹, G6.mem_commV_of_mem (Subgroup.mem_zpowers _) (w : V), ?_⟩
  rw [map_mul, map_inv, D.map_apply, MulEquiv.apply_symm_apply]
  rfl

theorem map_dc (σ : Equiv.Perm (Fin n)) (p : ↥(commV K)) (hp : D.dc σ p ∈ commV K) :
    D.β ⟨D.dc σ p, hp⟩ = coreAct n σ (D.β p) := by
  have h := D.map_apply (D.θ.symm σ) p hp
  rw [MulEquiv.apply_symm_apply] at h
  exact h

theorem exists_eq_comm (hV : ∀ v : V, v ^ 2 = 1) {σ : Equiv.Perm (Fin n)}
    (hσ : σ.IsThreeCycle) {y : ↥(commV K)} (hy : (y : V) ∈ D.wt σ) :
    ∃ u : ↥(coreMod n), D.β y = coreAct n σ u * u⁻¹ := by
  have hd : D.dc σ (y : V) ∈ D.wt σ := apply_mem_commV_zpowers hy
  have hdW : D.dc σ (y : V) ∈ commV K := D.wt_le hσ hd
  have hddW : D.dc σ (D.dc σ (y : V)) ∈ commV K := D.apply_mem _ (D.θ.symm σ).2 _ hdW
  refine ⟨D.β ⟨_, hdW⟩, ?_⟩
  have hy' : y = ⟨_, hddW⟩ * (⟨_, hdW⟩ : ↥(commV K))⁻¹ :=
    Subtype.ext (eq_comm_of_mem_commV hV (D.dc_pow_three hσ) hy).symm
  rw [congrArg D.β hy', map_mul, map_inv, D.map_dc σ ⟨_, hdW⟩ hddW]
  rfl

theorem vcoord_eq_zero (hV : ∀ v : V, v ^ 2 = 1) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {y : ↥(commV K)} (hy : (y : V) ∈ D.wt (cyc i j k)) {m : Fin n} (hi : m ≠ i)
    (hj : m ≠ j) (hk : m ≠ k) : vcoord (D.β y) m = 0 := by
  obtain ⟨u, hu⟩ := D.exists_eq_comm hV (cyc_isThreeCycle hij hik hjk) hy
  rw [hu]
  exact vcoord_comm_eq_zero u (cyc_inv_apply_of_ne hi hj hk)

theorem wt_cyc_swap23 (i j k : Fin n) : D.wt (cyc i k j) = D.wt (cyc i j k) := by
  rw [← cyc_inv, wt_inv]

theorem wt_cyc_swap12 {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    D.wt (cyc j i k) = D.wt (cyc i j k) := by
  rw [cyc_swap12 hij hik hjk, wt_cyc_swap23]

theorem exists_lift_pairVec {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ y : ↥(commV K), (y : V) ∈ D.wt (cyc i j k) ∧ D.β y = pairVec i j := by
  obtain ⟨y, hy, h⟩ := D.exists_lift (cyc i j k) (pairVec i k)
  exact ⟨y, hy, h.trans (coreAct_cyc_pairVec hik hjk)⟩

theorem coherent (hV : ∀ v : V, v ^ 2 = 1) (hn : Odd n) {i j k k' : Fin n} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hik' : i ≠ k') (hjk' : j ≠ k') {y y' : ↥(commV K)}
    (hy : (y : V) ∈ D.wt (cyc i j k)) (hy' : (y' : V) ∈ D.wt (cyc i j k'))
    (hβ : D.β y = pairVec i j) (hβ' : D.β y' = pairVec i j) : y = y' := by
  by_cases hkk : k = k'
  · subst hkk
    exact D.inj hV (cyc_isThreeCycle hij hik hjk) hy hy' (hβ.trans hβ'.symm)
  obtain ⟨m, hmi, hmj, hmk, hmk'⟩ := exists_ne_four hn hij hik hik' hjk hjk' hkk
  have hg3 : (cyc k' k m).IsThreeCycle :=
    cyc_isThreeCycle (Ne.symm hkk) (Ne.symm hmk') (Ne.symm hmk)
  have hgi : cyc k' k m i = i := cyc_apply_of_ne hik' hik hmi.symm
  have hgj : cyc k' k m j = j := cyc_apply_of_ne hjk' hjk hmj.symm
  have hgk : cyc k' k m k = k' := cyc_apply_second (Ne.symm hkk) (Ne.symm hmk)
  have hconj :
      D.dc (cyc i j k') = D.dc (cyc k' k m) * D.dc (cyc i j k) * (D.dc (cyc k' k m))⁻¹ := by
    rw [← D.dc_inv, ← D.dc_mul, ← D.dc_mul, conj_cyc, hgi, hgj, hgk]
  have hgK : D.dc (cyc k' k m) ∈ K := D.three_mem _ hg3
  have hhy : D.dc (cyc k' k m) (y : V) ∈ D.wt (cyc i j k') := by
    rw [wt, hconj]
    exact apply_mem_commV_zpowers_conj _ hy
  have hhyW : D.dc (cyc k' k m) (y : V) ∈ commV K :=
    D.apply_mem _ (D.θ.symm (cyc k' k m)).2 _ y.2
  have hβh : D.β ⟨_, hhyW⟩ = pairVec i j := by
    rw [D.map_dc, hβ, coreAct_pairVec, hgi, hgj]
  have hz : D.β (⟨_, hhyW⟩ * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hβh, hβ]
    exact mul_inv_cancel _
  obtain ⟨a, ha⟩ : ∃ a, a = D.dc (cyc k' k m) (y : V) * (y : V)⁻¹ := ⟨_, rfl⟩
  have hafix : D.dc (cyc k' k m) a = a := by
    rw [ha]
    exact D.ker_fix _ hz _ hgK
  have h1 : D.dc (cyc k' k m) (y : V) = a * y := by rw [ha, inv_mul_cancel_right]
  have h2 : D.dc (cyc k' k m) (D.dc (cyc k' k m) (y : V)) = y := by
    rw [h1, map_mul, hafix, h1, ← mul_assoc, ← pow_two, hV, one_mul]
  have hfix : D.dc (cyc k' k m) (y : V) = y := by
    have h3 := apply_three_of_pow_three (D.dc_pow_three hg3) (y : V)
    rw [h2] at h3
    exact h3
  have h5 : (⟨_, hhyW⟩ : ↥(commV K)) = y' :=
    D.inj hV (cyc_isThreeCycle hij hik' hjk') hhy hy' (hβh.trans hβ'.symm)
  rw [← h5]
  exact Subtype.ext hfix.symm

@[expose] def IsPairLift (a b : Fin n) (y : ↥(commV K)) : Prop :=
  D.β y = pairVec a b ∧ ∀ k, k ≠ a → k ≠ b → (y : V) ∈ D.wt (cyc a b k)

theorem exists_isPairLift (hV : ∀ v : V, v ^ 2 = 1) (hn : Odd n) (h3 : 3 ≤ n) {a b : Fin n}
    (hab : a ≠ b) : ∃ y, D.IsPairLift a b y := by
  obtain ⟨k₀, hk₀a, hk₀b⟩ := exists_ne_ne h3 a b
  obtain ⟨y, hy, hβ⟩ := D.exists_lift_pairVec (Ne.symm hk₀a) (Ne.symm hk₀b)
  refine ⟨y, hβ, fun k hka hkb => ?_⟩
  obtain ⟨y', hy', hβ'⟩ := D.exists_lift_pairVec (Ne.symm hka) (Ne.symm hkb)
  rw [D.coherent hV hn hab (Ne.symm hk₀a) (Ne.symm hk₀b) (Ne.symm hka) (Ne.symm hkb) hy hy' hβ
    hβ']
  exact hy'

theorem isPairLift_symm {a b : Fin n} (hab : a ≠ b) {y : ↥(commV K)}
    (h : D.IsPairLift a b y) : D.IsPairLift b a y := by
  refine ⟨h.1.trans (pairVec_comm a b), fun k hkb hka => ?_⟩
  rw [D.wt_cyc_swap12 hab (Ne.symm hka) (Ne.symm hkb)]
  exact h.2 k hka hkb

theorem isPairLift_mul (hV : ∀ v : V, v ^ 2 = 1) (hn : Odd n) {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) {y y' : ↥(commV K)} (h : D.IsPairLift a b y)
    (h' : D.IsPairLift a c y') : D.IsPairLift b c (y * y') := by
  have hβ : D.β (y * y') = pairVec b c := by
    rw [map_mul, h.1, h'.1]
    exact pairVec_mul a b c
  refine ⟨hβ, fun k hkb hkc => ?_⟩
  have h1 : ((y * y' : ↥(commV K)) : V) ∈ D.wt (cyc b c a) := by
    rw [D.wt_cyc_swap23 b a c, D.wt_cyc_swap12 hab hac hbc]
    have hy' := h'.2 b (Ne.symm hab) hbc
    rw [D.wt_cyc_swap23 a b c] at hy'
    exact Subgroup.mul_mem _ (h.2 c (Ne.symm hac) (Ne.symm hbc)) hy'
  obtain ⟨y'', hy'', hβ''⟩ := D.exists_lift_pairVec (Ne.symm hkb) (Ne.symm hkc)
  rw [D.coherent hV hn hbc (Ne.symm hab) (Ne.symm hac) (Ne.symm hkb) (Ne.symm hkc) h1 hy'' hβ
    hβ'']
  exact hy''

theorem exists_family (hV : ∀ v : V, v ^ 2 = 1) (hn : Odd n) (h3 : 3 ≤ n) (o : Fin n) :
    ∃ Y : Fin n → ↥(commV K), (∀ m, D.β (Y m) = pairVec o m) ∧
      ∀ a b, a ≠ b → D.IsPairLift a b (Y a * Y b) := by
  have hY : ∀ m : Fin n, ∃ y : ↥(commV K), (m = o → y = 1) ∧ (m ≠ o → D.IsPairLift o m y) := by
    intro m
    by_cases hm : m = o
    · exact ⟨1, fun _ => rfl, fun h => absurd hm h⟩
    · obtain ⟨y, hy⟩ := D.exists_isPairLift hV hn h3 (Ne.symm hm)
      exact ⟨y, fun h => absurd h hm, fun _ => hy⟩
  choose Y hY1 hYL using hY
  refine ⟨Y, fun m => ?_, fun a b hab => ?_⟩
  · by_cases hm : m = o
    · rw [hY1 m hm, hm, pairVec_self]
      exact map_one D.β
    · exact (hYL m hm).1
  · by_cases ha : a = o
    · have hb : b ≠ o := fun h => hab (ha.trans h.symm)
      rw [hY1 a ha, one_mul, ha]
      exact hYL b hb
    · by_cases hb : b = o
      · rw [hY1 b hb, mul_one, hb]
        exact D.isPairLift_symm (Ne.symm ha) (hYL a ha)
      · exact D.isPairLift_mul hV hn (Ne.symm ha) (Ne.symm hb) hab (hYL a ha) (hYL b hb)

theorem mem_range_vsum (hV : ∀ v : V, v ^ 2 = 1) (h3 : 3 ≤ n) {Y : Fin n → ↥(commV K)}
    (hY : ∀ a b, a ≠ b → D.IsPairLift a b (Y a * Y b)) {τ : Equiv.Perm (Fin n)}
    (hτ : τ.IsThreeCycle) {w : V} (hw : w ∈ D.wt τ) :
    ∃ v : ↥(coreMod n), ((vsum Y v : ↥(commV K)) : V) = w := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := exists_eq_cyc h3 hτ
  have hwW : w ∈ commV K := D.wt_le hτ hw
  have hw' : ((⟨w, hwW⟩ : ↥(commV K)) : V) ∈ D.wt (cyc a b c) := hw
  have key : ∀ v : ↥(coreMod n), ((vsum Y v : ↥(commV K)) : V) ∈ D.wt (cyc a b c) →
      D.β (vsum Y v) = D.β ⟨w, hwW⟩ → ∃ v', ((vsum Y v' : ↥(commV K)) : V) = w :=
    fun v hv hβ => ⟨v, congrArg Subtype.val (D.inj hV hτ hv hw' hβ)⟩
  rcases eq_one_or_pairVec hab hac hbc (fun m hma hmb hmc =>
      D.vcoord_eq_zero hV hab hac hbc hw' hma hmb hmc) with h | h | h | h
  · refine key 1 ?_ ?_
    · rw [vsum_one]
      exact Subgroup.one_mem _
    · rw [vsum_one, h]
      exact map_one D.β
  · obtain ⟨hβ, hmem⟩ := hY a b hab
    refine key (pairVec a b) ?_ ?_
    · rw [vsum_pairVec Y hab]
      exact hmem c (Ne.symm hac) (Ne.symm hbc)
    · rw [vsum_pairVec Y hab, hβ, h]
  · obtain ⟨hβ, hmem⟩ := hY a c hac
    refine key (pairVec a c) ?_ ?_
    · rw [vsum_pairVec Y hac, ← D.wt_cyc_swap23 a b c]
      exact hmem b (Ne.symm hab) hbc
    · rw [vsum_pairVec Y hac, hβ, h]
  · obtain ⟨hβ, hmem⟩ := hY b c hbc
    refine key (pairVec b c) ?_ ?_
    · rw [vsum_pairVec Y hbc, ← D.wt_cyc_swap12 hab hac hbc, ← D.wt_cyc_swap23 b a c]
      exact hmem a hab hac
    · rw [vsum_pairVec Y hbc, hβ, h]

theorem β_injective (hV : ∀ v : V, v ^ 2 = 1) (hn : Odd n) (h3 : 3 ≤ n)
    (hgen : ∀ H : Subgroup (MulAut V),
      (∀ σ : Equiv.Perm (Fin n), σ.IsThreeCycle → D.dc σ ∈ H) → K ≤ H) :
    Function.Injective D.β := by
  obtain ⟨Y, hβY, hY⟩ := D.exists_family hV hn h3 ⟨0, by omega⟩
  have hG : ∀ g : ↥(commV K), g ^ 2 = 1 := fun g =>
    Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hV g)
  let R : Subgroup V :=
    { carrier := {x | ∃ v : ↥(coreMod n), ((vsum Y v : ↥(commV K)) : V) = x}
      mul_mem' := fun {x y} ⟨u, hu⟩ ⟨v, hv⟩ =>
        ⟨u * v, by rw [vsum_mul hG, Subgroup.coe_mul, hu, hv]⟩
      one_mem' := ⟨1, by rw [vsum_one]; rfl⟩
      inv_mem' := fun {x} ⟨v, hv⟩ => ⟨v, by rw [hv, inv_eq_self_of_sq hV]⟩ }
  have hKR : K ≤ commLe R := hgen _ fun σ hσ v =>
    D.mem_range_vsum hV h3 hY hσ (G6.mem_commV_of_mem (Subgroup.mem_zpowers _) v)
  have hWR := commV_le_of_le_commLe hKR
  have hsec : ∀ v, D.β (vsum Y v) = v := by
    intro v
    refine vcoord_ext fun q => ?_
    rw [vcoord_map_vsum]
    simp only [hβY, vcoord_pairVec, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, sum_vcoord, zero_mul, zero_add]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [injective_iff_map_eq_one]
  intro w hw
  obtain ⟨v, hv⟩ := hWR w.2
  have hv' : vsum Y v = w := Subtype.ext hv
  have h1 : v = 1 := (hsec v).symm.trans ((congrArg D.β hv').trans hw)
  rw [← hv', h1, vsum_one]

end SymSplitData

end Split

section Trace

variable {V : Type*} [CommGroup V]

theorem sup_fixV_eq_top [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X T : Subgroup (MulAut V)}
    (hT : IsSylowOf 2 T X) (hU : commV (opResidual 2 X) ⊔ fixV T = ⊤)
    (hXW : ∀ x ∈ X, ∀ p ∈ commV (opResidual 2 X), x p ∈ commV (opResidual 2 X)) :
    commV (opResidual 2 X) ⊔ fixV (opResidual 2 X) = ⊤ := by
  classical
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  refine eq_top_iff.2 (hU ▸ sup_le le_sup_left ?_)
  intro c hc
  have hmod : ∀ g ∈ X, g c * c⁻¹ ∈ commV (opResidual 2 X) := by
    intro g hg
    obtain ⟨s, hs, k, hk, rfl⟩ := exists_mul_eq_of_pow_mem (opResidual_normal 2 X)
      (fun x hx => exists_pow_mem_opResidual hx) ⟨hT.1, hT.2.1, hT.2.2⟩ g hg
    have h1 : (s * k) c * c⁻¹ = s (k c * c⁻¹) := by
      rw [MulAut.mul_apply, map_mul, map_inv, hc s hs]
    rw [h1]
    exact hXW s (hT.1 hs) _ (G6.mem_commV_of_mem hk c)
  let O := MulAction.orbit X c
  have : Fintype O := Fintype.ofFinite O
  have hodd : Odd (Fintype.card O) := by
    have h1 : (MulAction.stabilizer X c).index ∣ T.relIndex X := by
      apply Subgroup.index_dvd_of_le
      intro t ht
      rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, MulAut.smul_def]
      exact hc _ (Subgroup.mem_subgroupOf.1 ht)
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at h1
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h2 => hT.2.2 (h2.trans h1))
  have hTr : (∏ x : O, (x : V)) ∈ fixV (opResidual 2 X) := by
    intro g hg
    rw [map_prod]
    exact Fintype.prod_equiv (MulAction.toPerm (⟨g, opResidual_le 2 X hg⟩ : X)) _ _
      (fun x => rfl)
  have hQ : (∏ x : O, ((x : V) * c⁻¹)) ∈ commV (opResidual 2 X) := by
    refine Subgroup.prod_mem _ fun x _ => ?_
    obtain ⟨g, hg⟩ := x.2
    rw [← hg]
    exact hmod g g.2
  have hpow : c⁻¹ ^ Fintype.card O = c⁻¹ := by
    obtain ⟨r, hr⟩ := hodd
    rw [hr, pow_succ, pow_mul, hV, one_pow, one_mul]
  have hc' : (∏ x : O, ((x : V) * c⁻¹))⁻¹ * ∏ x : O, (x : V) = c := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hpow, mul_inv_rev, inv_inv,
      inv_mul_cancel_right]
  rw [← hc']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hQ))
    (Subgroup.mem_sup_right hTr)

end Trace

section Main

variable {V : Type*} [CommGroup V]

theorem two_thirteen [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n)
    {X T : Subgroup (MulAut V)} (hT : IsSylowOf 2 T X)
    (hU : commV (opResidual 2 X) ⊔ fixV T = ⊤)
    (hnat : IsSymNatSection X (commV (opResidual 2 X))
      (commV (opResidual 2 X) ⊓ fixV (opResidual 2 X)) n) :
    commV (opResidual 2 X) ⊓ fixV (opResidual 2 X) = ⊥ ∧
      commV (opResidual 2 X) ⊔ fixV (opResidual 2 X) = ⊤ ∧
      IsSymNatSection X (commV (opResidual 2 X)) ⊥ n := by
  obtain ⟨hXW, θ, β, hsurj, hker, hβ⟩ := hnat
  let D : SymSplitData X (opResidual 2 X) n :=
    { θ := θ
      β := β
      surj := hsurj
      ker_fix := fun w hw => by
        have h1 : w ∈ β.ker := hw
        rw [hker, Subgroup.mem_subgroupOf] at h1
        exact h1.2
      map_apply := hβ
      apply_mem := hXW
      three_mem := fun σ hσ => mem_opResidual_of_coprime (θ.symm σ).2 (by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hσ.orderOf]
        decide) }
  have hinj := D.β_injective hV hn h3 fun H hH => opResidual_le_of_three_cycles θ hH
  have hZ : commV (opResidual 2 X) ⊓ fixV (opResidual 2 X) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have h1 : (⟨z, hz.1⟩ : ↥(commV (opResidual 2 X))) ∈ β.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hz
    have h2 : (⟨z, hz.1⟩ : ↥(commV (opResidual 2 X))) = 1 :=
      hinj ((MonoidHom.mem_ker.1 h1).trans (map_one β).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  refine ⟨hZ, sup_fixV_eq_top hV hT hU hXW, ?_⟩
  rw [← hZ]
  exact ⟨hXW, θ, β, hsurj, hker, hβ⟩

end Main

end CFSG.CGT.PushingUpLit.BHS
