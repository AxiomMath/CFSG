module

public import CFSG.GH74.Uniqueness.SU.SU2Odd
public import CFSG.GH74.Uniqueness.SU.SU2Count
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GH74.Uniqueness.SU.SU2Trans

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section Final

theorem exists_abelian_normal {X : Type*} [Group X] [Finite X] [Nontrivial X]
    (hs : Group.IsSolvable X) :
    ∃ Z : Subgroup X, Z.Normal ∧ Z ≠ ⊥ ∧ ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
  classical
  have hex : ∃ n : ℕ, derivedSeries X n = ⊥ := hs.solvable
  let m := Nat.find hex
  have hm : derivedSeries X m = ⊥ := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hm
    exact (top_ne_bot (α := Subgroup X)) hm
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  have hne : derivedSeries X j ≠ ⊥ := Nat.find_min hex (by omega)
  refine ⟨derivedSeries X j, inferInstance, hne, fun a ha b hb => ?_⟩
  have hc := Subgroup.commutator_mem_commutator ha hb
  rw [← derivedSeries_succ, ← hj, hm] at hc
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.1 hc
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem eq_three_of_succ_eq_two_pow {n : ℕ} (hn : 1 ≤ n) (h : n + 1 = 2 ^ (n - 1)) : n = 3 := by
  have key : ∀ m : ℕ, 4 ≤ m → m + 1 < 2 ^ (m - 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have h1 : 2 ^ (j + 1 + 1 - 1) = 2 * 2 ^ (j + 1 - 1) := by
        rw [Nat.add_sub_cancel, Nat.add_sub_cancel, pow_succ, mul_comm]
      rw [h1]
      omega
  by_cases h4 : 4 ≤ n
  · have := key n h4
    omega
  · have h3 : n ≤ 3 := by omega
    interval_cases n <;> simp_all

theorem comm_of_odd_order {X : Type*} [Group X] [Finite X] (hodd : Odd (Nat.card X))
    {Y : Subgroup X} (hY : Nat.card Y = 3) (hcyc : IsCyclic Y) {g : X}
    (hg : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : ∀ y ∈ Y, g * y = y * g := by
  obtain ⟨y₀, hy₀⟩ := hcyc.exists_generator
  have hord : orderOf y₀ = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hy₀, hY]
  set y : X := (y₀ : X) with hy
  have hyord : orderOf y = 3 := by rw [hy, Subgroup.orderOf_coe, hord]
  have hy3 : y ^ 3 = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    omega
  obtain ⟨j, hj⟩ : ∃ j : ℤ, y ^ j = g * y * g⁻¹ := by
    have := hy₀ ⟨g * y * g⁻¹, hg y y₀.2⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 this
    exact ⟨j, by simpa [hy] using congrArg Subtype.val hj⟩
  have hjmod : y ^ j = y ^ (j % 3) := by
    rw [← zpow_mod_orderOf, hyord]; norm_cast
  have hgy : g * y * g⁻¹ = y := by
    have hm : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hm with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hjmod
      have : g * y * g⁻¹ = 1 := by rw [← hj, hjmod]
      apply hy1
      simpa using this
    · rw [h1, zpow_one] at hjmod
      rw [← hj, hjmod]
    · exfalso
      have hyy : y * y = y⁻¹ := eq_inv_of_mul_eq_one_left (by
        calc y * y * y = y ^ 3 := by rw [pow_succ, pow_two]
          _ = 1 := hy3)
      have hinv : g * y * g⁻¹ = y⁻¹ := by
        rw [← hj, hjmod, h2, zpow_two, hyy]
      have hinv' : g * y⁻¹ * g⁻¹ = y := by
        have := congrArg (fun x => x⁻¹) hinv
        simpa [mul_inv_rev, mul_assoc] using this
      have hc2 : Commute (g ^ 2) y := by
        rw [pow_two]
        show g * g * y = y * (g * g)
        calc g * g * y = g * (g * y * g⁻¹) * g := by group
          _ = g * y⁻¹ * g := by rw [hinv]
          _ = (g * y⁻¹ * g⁻¹) * (g * g) := by group
          _ = y * (g * g) := by rw [hinv']
      have hoddg : Odd (orderOf g) := hodd.of_dvd_nat (orderOf_dvd_natCard g)
      obtain ⟨m, hm⟩ := hoddg
      have hg1 : g = (g ^ 2) ^ (m + 1) := by
        have h : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
        calc g = g * g ^ (2 * m + 1) := by rw [h, mul_one]
          _ = g ^ (2 * (m + 1)) := by rw [← pow_succ']; ring_nf
          _ = (g ^ 2) ^ (m + 1) := by rw [pow_mul]
      have hcomm : Commute g y := by
        rw [hg1]
        exact hc2.pow_left (m + 1)
      have hyeq : y = y⁻¹ := by
        rw [← hinv, hcomm.eq, mul_inv_cancel_right]
      have hyy1 : y * y = 1 := mul_eq_one_iff_eq_inv.2 hyeq
      apply hy1
      calc y = y * (y * y) := by rw [hyy1, mul_one]
        _ = y ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
        _ = 1 := hy3
  intro z hz
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hy₀ ⟨z, hz⟩)
  have hzn : z = y ^ n := by simpa [hy] using (congrArg Subtype.val hn).symm
  have hcomm : Commute g y := by
    show g * y = y * g
    calc g * y = (g * y * g⁻¹) * g := by group
      _ = y * g := by rw [hgy]
  rw [hzn]
  exact (hcomm.zpow_right n).eq

theorem smul_eq_one_iff' {X V : Type*} [Group X] [Group V] [MulDistribMulAction X V] (g : X)
    (v : V) : g • v = 1 ↔ v = 1 := by
  constructor
  · intro h
    have := congrArg (fun x => g⁻¹ • x) h
    simpa [smul_one] using this
  · rintro rfl
    exact smul_one g

theorem smul_eq_of_smul_le {X V : Type} [Group X] [Group V] [MulDistribMulAction X V] [Finite V]
    {z : X} {S : Subgroup V} (h : z • S ≤ S) : z • S = S :=
  Subgroup.eq_of_le_of_card_ge h (Nat.card_congr (Subgroup.equivSMul z S).toEquiv).le

namespace GOPair

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V] {Y : Subgroup X}

theorem odd_case [Finite X] [Finite V] (hGO : GOPair V Y) (hodd : Odd (Nat.card X))
    {W₁ W₂ : Subgroup V} (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) :
    shapeK V Y = 1 ∧ shapeN V = 3 ∧ Nat.card X = 21 ∧ ∃ a b : X, a * b ≠ b * a := by
  classical
  have hk2 := hGO.card_fixSub_eq_two hodd hW₁ hW₂
  have hk1 : shapeK V Y = 1 := by
    have h := hGO.card_fixSub
    rw [hk2] at h
    exact (Nat.pow_right_injective (le_refl 2) (h.symm.trans (pow_one 2).symm))
  have htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ x : X, x • v = w :=
    fun v w hv hw => hGO.transitive_on_V hW₁ hW₂ hv hw
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_ne_bot hGO.fixSub_ne_bot
  have hV0 : ∀ c ∈ fixSub V Y, c = 1 ∨ c = a := by
    have hnc : ((fixSub V Y : Subgroup V) : Set V).ncard = 2 := by
      rw [← Nat.card_coe_set_eq]; exact hk2
    obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.1 hnc
    have h1 : (1 : V) ∈ ({x, y} : Set V) := hset ▸ (fixSub V Y).one_mem
    have ha' : a ∈ ({x, y} : Set V) := hset ▸ ha
    intro c hc
    have hc' : c ∈ ({x, y} : Set V) := hset ▸ hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ha' hc'
    rcases h1 with h1 | h1 <;> rcases ha' with ha' | ha' <;> rcases hc' with hc' | hc' <;>
      simp_all
  have hfixa : ∀ x : X, x • fixSub V Y = fixSub V Y → x • a = a := by
    intro x hx
    have : x • a ∈ fixSub V Y := by
      rw [← hx]; exact Subgroup.smul_mem_pointwise_smul a x _ ha
    rcases hV0 _ this with h | h
    · exact absurd ((smul_eq_one_iff' x a).1 h) ha1
    · exact h
  have hfixc : ∀ x : X, x • fixSub V Y = fixSub V Y → ∀ c ∈ fixSub V Y, x • c = c := by
    intro x hx c hc
    rcases hV0 c hc with rfl | rfl
    · exact smul_one x
    · exact hfixa x hx
  have hstab : ∀ x : X, x • a = a → x • fixSub V Y = fixSub V Y := by
    intro x hxa
    ext m
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rcases hV0 c hc with rfl | rfl
      · rw [smul_one]; exact (fixSub V Y).one_mem
      · rw [hxa]; exact ha
    · intro hm
      rcases hV0 m hm with rfl | rfl
      · exact ⟨1, (fixSub V Y).one_mem, smul_one x⟩
      · exact ⟨m, hm, hxa⟩
  obtain ⟨y₀, hy₀, hy₀1⟩ := exists_ne_one_of_ne_bot hGO.ne_bot
  have : Nontrivial X := ⟨⟨y₀, 1, hy₀1⟩⟩
  obtain ⟨Z, hZn, hZ1, hZc⟩ := exists_abelian_normal (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)
  have hZodd : Odd (Nat.card Z) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card Z)
  have hZfix : ∀ v : V, (∀ z ∈ Z, z • v = v) → v = 1 := by
    intro v hv
    by_contra hv1
    apply hZ1
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    apply hGO.faithful
    intro w
    by_cases hw1 : w = 1
    · rw [hw1, smul_one]
    obtain ⟨x, hx⟩ := htr v w hv1 hw1
    have hconj : x⁻¹ * z * x ∈ Z := by
      have := hZn.conj_mem z hz x⁻¹
      rwa [inv_inv] at this
    rw [← hx]
    calc z • x • v = (x * (x⁻¹ * z * x)) • v := by rw [← mul_smul]; group
      _ = x • ((x⁻¹ * z * x) • v) := mul_smul _ _ _
      _ = x • v := by rw [hv _ hconj]
  have hZY : ∀ t ∈ Z, t ∈ Y → t = 1 := by
    intro t htZ htY
    by_contra ht1
    have hz0 : ∀ z ∈ Z, z • fixSub V Y = fixSub V Y := by
      intro z hz
      apply smul_eq_of_smul_le
      intro m hm
      obtain ⟨c, hc, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm
      apply hGO.mem_fixSub_of_smul_eq htY ht1
      calc t • z • c = (t * z) • c := (mul_smul _ _ _).symm
        _ = (z * t) • c := by rw [hZc t htZ z hz]
        _ = z • t • c := mul_smul _ _ _
        _ = z • c := by rw [hc t htY]
    exact ha1 (hZfix a fun z hz => hfixa z (hz0 z hz))
  have hcent : ∀ g : X, g • fixSub V Y = fixSub V Y → (∀ y ∈ Y, g * y = y * g) → g ∈ Y := by
    intro g hg hgc
    obtain ⟨v₀, hv₀, hv₀1⟩ := exists_ne_one_of_ne_bot hGO.commSub_ne_bot
    have hgv₀ : g • v₀ ∈ commSub V Y := hGO.smul_commSub_of_stab hg hv₀
    have hgv₀1 : g • v₀ ≠ 1 := fun h => hv₀1 ((smul_eq_one_iff' g v₀).1 h)
    obtain ⟨y₁, hy₁, hy₁v⟩ := hGO.transitive v₀ hv₀ hv₀1 _ hgv₀ hgv₀1
    have hgy : ∀ u ∈ commSub V Y, g • u = y₁ • u := by
      intro u hu
      by_cases hu1 : u = 1
      · rw [hu1, smul_one, smul_one]
      obtain ⟨y, hy, hyv⟩ := hGO.transitive v₀ hv₀ hv₀1 u hu hu1
      rw [← hyv]
      calc g • y • v₀ = (g * y) • v₀ := (mul_smul _ _ _).symm
        _ = (y * g) • v₀ := by rw [hgc y hy]
        _ = y • g • v₀ := mul_smul _ _ _
        _ = y • y₁ • v₀ := by rw [hy₁v]
        _ = (y * y₁) • v₀ := (mul_smul _ _ _).symm
        _ = (y₁ * y) • v₀ := by rw [hGO.comm_Y hy hy₁]
        _ = y₁ • y • v₀ := mul_smul _ _ _
    have hgall : ∀ v : V, g • v = y₁ • v := by
      intro v
      obtain ⟨c, hc, hp⟩ := hGO.exists_decomp v
      obtain ⟨p, hpdef⟩ : ∃ p : V, p = v * c⁻¹ := ⟨_, rfl⟩
      have hp' : p ∈ commSub V Y := hpdef ▸ hp
      have hv : v = p * c := by rw [hpdef]; simp
      rw [hv, smul_mul', smul_mul', hgy p hp', hfixc g hg c hc, hc y₁ hy₁]
    have h1 : y₁⁻¹ * g = 1 :=
      hGO.faithful _ (fun v => by rw [mul_smul, hgall v, inv_smul_smul])
    have hgeq : g = y₁ := by rw [inv_mul_eq_one] at h1; exact h1.symm
    rw [hgeq]; exact hy₁
  have hZ₀ : ∀ z ∈ Z, z • fixSub V Y = fixSub V Y → z = 1 := by
    intro z hz hz0
    have hcomm : ∀ y ∈ Y, z * y = y * z := by
      intro y hy
      have h1 : z * y * z⁻¹ ∈ Y := hGO.normal_in_stab z hz0 y hy
      have h2 : y * z⁻¹ * y⁻¹ ∈ Z := hZn.conj_mem z⁻¹ (Z.inv_mem hz) y
      have h3 : z * y * z⁻¹ * y⁻¹ ∈ Y := Y.mul_mem h1 (Y.inv_mem hy)
      have h4 : z * y * z⁻¹ * y⁻¹ ∈ Z := by
        have : z * (y * z⁻¹ * y⁻¹) ∈ Z := Z.mul_mem hz h2
        simpa [mul_assoc] using this
      have h5 := hZY _ h4 h3
      calc z * y = (z * y * z⁻¹ * y⁻¹) * (y * z) := by group
        _ = y * z := by rw [h5, one_mul]
    exact hZY z hz (hcent z hz0 hcomm)
  have hfpf : ∀ y ∈ Y, y ≠ 1 → ∀ z ∈ Z, y * z = z * y → z = 1 := by
    intro y hy hy1 z hz hyz
    apply hZ₀ z hz
    apply smul_eq_of_smul_le
    intro m hm
    obtain ⟨c, hc, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hm
    apply hGO.mem_fixSub_of_smul_eq hy hy1
    calc y • z • c = (y * z) • c := (mul_smul _ _ _).symm
      _ = (z * y) • c := by rw [hyz]
      _ = z • y • c := mul_smul _ _ _
      _ = z • c := by rw [hc y hy]
  have hcount := hGO.shapeK_mul_card hZc hZodd hZfix hfpf
  have hYn : Nat.card Y = shapeN V := by rw [hk1, one_mul] at hcount; exact hcount
  have hYcard : Nat.card Y + 1 = 2 ^ (shapeN V - 1) := by
    rw [hGO.card_Y_add_one, hGO.card_commSub, hk1]
  have hn1 : 1 ≤ shapeN V := by
    rw [← hYn]; exact Nat.card_pos
  have hn3 : shapeN V = 3 := by
    apply eq_three_of_succ_eq_two_pow hn1
    have h' := hYcard
    rw [hYn] at h'
    exact h'
  have hY3 : Nat.card Y = 3 := by rw [hYn, hn3]
  have hX₀Y : ∀ g : X, g • fixSub V Y = fixSub V Y → g ∈ Y := by
    intro g hg
    refine hcent g hg ?_
    exact comm_of_odd_order hodd hY3 hGO.isCyclic (hGO.normal_in_stab g hg)
  have hstabY : MulAction.stabilizer X a = Y := by
    ext x
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hx
      exact hX₀Y x (hstab x hx)
    · intro hx
      exact ha x hx
  have horb : MulAction.orbit X a = {v : V | v ≠ 1} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩ h
      exact ha1 ((smul_eq_one_iff' x a).1 h)
    · intro hv
      exact htr a v ha1 hv
  have hVcard : Nat.card V = 8 := by rw [hGO.card_V, hn3]; norm_num
  have hindex : (MulAction.stabilizer X a).index = 7 := by
    rw [MulAction.index_stabilizer, horb]
    have h1 : {v : V | v ≠ 1} = (Set.univ : Set V) \ {1} := by
      ext v; simp
    rw [h1, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ, hVcard]
  have hXcard : Nat.card X = 21 := by
    have := Subgroup.index_mul_card (MulAction.stabilizer X a)
    rw [hindex, hstabY, hY3] at this
    omega
  refine ⟨hk1, hn3, hXcard, ?_⟩
  by_contra hab
  push Not at hab
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := ⟨y₀, hy₀, hy₀1⟩
  apply hy1
  apply hGO.faithful
  intro v
  by_cases hv1 : v = 1
  · rw [hv1, smul_one]
  obtain ⟨x, hx⟩ := htr a v ha1 hv1
  rw [← hx]
  calc y • x • a = (y * x) • a := (mul_smul _ _ _).symm
    _ = (x * y) • a := by rw [hab y x]
    _ = x • y • a := mul_smul _ _ _
    _ = x • a := by rw [ha y hy]

end GOPair

end Final

end CFSG.GH74.Uniqueness.SU.SU2
