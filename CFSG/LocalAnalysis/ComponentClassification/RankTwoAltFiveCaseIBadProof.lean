module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseID
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseIBad

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv Equiv.Perm CFSG.Open CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

section ActionE

variable {M : Type*} [Group M] {v w : M}

theorem ew_pow (hvw : Commute v w) (hv : v ^ 3 = 1) (hw : w ^ 3 = 1) (p : ZMod 3 × ZMod 3)
    (n : ℕ) : ew v w p ^ n = ew v w ((n : ZMod 3) • p) := by
  induction n with
  | zero => simp [ew]
  | succ n ih =>
    rw [pow_succ, ih, ew_mul hvw hv hw]
    congr 1
    push_cast
    rw [add_smul, one_smul]

@[expose] def ActsBy (v w g : M) (L : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3) : Prop :=
  ∀ p, g * ew v w p * g⁻¹ = ew v w (L p)

theorem actsBy_of (hvw : Commute v w) (hv : v ^ 3 = 1) (hw : w ^ 3 = 1) {g : M}
    {P Q : ZMod 3 × ZMod 3} (h1 : g * v * g⁻¹ = ew v w P) (h2 : g * w * g⁻¹ = ew v w Q) :
    ActsBy v w g (fun p => p.1 • P + p.2 • Q) := by
  intro p
  have hc : g * ew v w p * g⁻¹ = (g * v * g⁻¹) ^ p.1.val * (g * w * g⁻¹) ^ p.2.val := by
    rw [← MulAut.conj_apply, ew, map_mul, map_pow, map_pow, MulAut.conj_apply,
      MulAut.conj_apply]
  rw [hc, h1, h2, ew_pow hvw hv hw, ew_pow hvw hv hw, ew_mul hvw hv hw, ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val]

theorem ActsBy.mul {g g' : M} {L L' : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (h : ActsBy v w g L)
    (h' : ActsBy v w g' L') : ActsBy v w (g * g') (L ∘ L') := by
  intro p
  rw [Function.comp_apply, ← h, ← h' p]
  group

theorem ActsBy.pow {g : M} {L : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (h : ActsBy v w g L)
    (n : ℕ) : ActsBy v w (g ^ n) L^[n] := by
  induction n with
  | zero => intro p; simp
  | succ n ih =>
    rw [pow_succ', Function.iterate_succ']
    exact h.mul ih

theorem ActsBy.pow_four_mul_odd {g : M} {L : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3}
    (h : ActsBy v w g L) (h4 : ∀ p, L^[4] p = -p) {m : ℕ} (hm : Odd m) :
    ActsBy v w (g ^ (4 * m)) Neg.neg := by
  have hL4 : L^[4] = Neg.neg := funext h4
  have hneg : (Neg.neg : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3)^[m] = Neg.neg :=
    Function.Involutive.iterate_odd (fun p => neg_neg p) hm
  have := h.pow (4 * m)
  rwa [Function.iterate_mul, hL4, hneg] at this

theorem ew_one_zero : ew v w (1, 0) = v := by
  show v ^ (1 : ZMod 3).val * w ^ (0 : ZMod 3).val = v
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    mul_one]

theorem ew_zero_one : ew v w (0, 1) = w := by
  show v ^ (0 : ZMod 3).val * w ^ (1 : ZMod 3).val = w
  rw [show (1 : ZMod 3).val = 1 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_one, pow_zero,
    one_mul]

theorem ew_one_one : ew v w (1, 1) = v * w := by
  show v ^ (1 : ZMod 3).val * w ^ (1 : ZMod 3).val = v * w
  rw [show (1 : ZMod 3).val = 1 from rfl, pow_one, pow_one]

theorem ew_neg_one_zero (hv : v ^ 3 = 1) : ew v w (-1, 0) = v⁻¹ := by
  show v ^ (-1 : ZMod 3).val * w ^ (0 : ZMod 3).val = v⁻¹
  rw [show (-1 : ZMod 3).val = 2 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_zero, mul_one,
    eq_inv_iff_mul_eq_one, ← pow_succ, hv]

theorem ew_zero_neg_one (hw : w ^ 3 = 1) : ew v w (0, -1) = w⁻¹ := by
  show v ^ (0 : ZMod 3).val * w ^ (-1 : ZMod 3).val = w⁻¹
  rw [show (-1 : ZMod 3).val = 2 from rfl, show (0 : ZMod 3).val = 0 from rfl, pow_zero, one_mul,
    eq_inv_iff_mul_eq_one, ← pow_succ, hw]

theorem ew_one_neg_one (hw : w ^ 3 = 1) : ew v w (1, -1) = v * w⁻¹ := by
  show v ^ (1 : ZMod 3).val * w ^ (-1 : ZMod 3).val = v * w⁻¹
  rw [show (1 : ZMod 3).val = 1 from rfl, show (-1 : ZMod 3).val = 2 from rfl, pow_one,
    eq_inv_of_mul_eq_one_left (show w ^ 2 * w = 1 by rw [← pow_succ]; exact hw)]

theorem ew_neg_one_one (hv : v ^ 3 = 1) : ew v w (-1, 1) = v⁻¹ * w := by
  show v ^ (-1 : ZMod 3).val * w ^ (1 : ZMod 3).val = v⁻¹ * w
  rw [show (1 : ZMod 3).val = 1 from rfl, show (-1 : ZMod 3).val = 2 from rfl, pow_one,
    eq_inv_of_mul_eq_one_left (show v ^ 2 * v = 1 by rw [← pow_succ]; exact hv)]

theorem iterate_four_eq_neg : ∀ e ∈ [(1 : ZMod 3), -1], ∀ f ∈ [(1 : ZMod 3), -1],
    ∀ p : ZMod 3 × ZMod 3,
      (((fun p : ZMod 3 × ZMod 3 => p.1 • ((1 : ZMod 3), e) + p.2 • ((0 : ZMod 3), 1)) ∘
        (fun p : ZMod 3 × ZMod 3 => p.1 • ((1 : ZMod 3), 0) + p.2 • (f, (1 : ZMod 3)))) ∘
        (fun p : ZMod 3 × ZMod 3 => p.1 • ((1 : ZMod 3), 0) + p.2 • ((0 : ZMod 3), -1)))^[4] p =
        -p := by
  decide

theorem sq_mul_of_conj_eq_inv {g a : M} (h : g * a * g⁻¹ = a⁻¹) : g ^ 2 * a = a * g ^ 2 := by
  have h1 : g * a⁻¹ * g⁻¹ = a := by
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group, h, inv_inv]
  rw [sq]
  calc g * g * a = g * (g * a * g⁻¹) * g := by group
    _ = g * a⁻¹ * g⁻¹ * (g * g) := by rw [h]; group
    _ = a * (g * g) := by rw [h1]

end ActionE

theorem odd_orderOf_of_commute_a6c012 {g : alternatingGroup (Fin 6)}
    (hg : g * a6c012 = a6c012 * g) : Odd (orderOf g) := by
  have hC : Nat.card (centralizer ({(a6c012 : Perm (Fin 6))} : Set (Perm (Fin 6)))) = 18 := by
    rw [nat_card_centralizer, isThreeCycle_a6c012.cycleType]
    simp [Nat.factorial]
  set C := centralizer ({(a6c012 : Perm (Fin 6))} : Set (Perm (Fin 6))) with hCdef
  set f : C →* ℤˣ := Perm.sign.comp C.subtype with hf
  have hs : swap (3 : Fin 6) 4 ∈ C := by
    rw [hCdef, mem_centralizer_singleton_iff]
    decide
  have hsurj : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨_, hs⟩, by simp [hf, sign_swap (show (3 : Fin 6) ≠ 4 by decide)]⟩
  have hker : Nat.card f.ker = 9 := by
    have h := f.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr hsurj, card_top,
      Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int, hC] at h
    omega
  have hgC : (⟨(g : Perm (Fin 6)), mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val hg)⟩ : C) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact mem_alternatingGroup.mp g.2
  have hd := Subgroup.orderOf_dvd_natCard _ hgC
  rw [hker, Subgroup.orderOf_mk, Subgroup.orderOf_coe] at hd
  exact Odd.of_dvd_nat (by decide) hd

theorem pow_four_of_two_pow {σ : Perm (Fin 5)} {j : ℕ} (h : σ ^ 2 ^ j = 1) : σ ^ 4 = 1 := by
  have hsum : σ.cycleType.sum ≤ 5 := by
    rw [sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hd : σ.cycleType.lcm ∣ 4 := Multiset.lcm_dvd.mpr fun n hn => by
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      ((dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h))
    have hle : 2 ^ i ≤ 5 := (Multiset.le_sum_of_mem hn).trans hsum
    have hi : i ≤ 2 := by
      by_contra hi
      have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact pow_dvd_pow 2 hi
  rw [lcm_cycleType] at hd
  exact orderOf_dvd_iff_pow_eq_one.mp hd

@[expose] def a6sig : alternatingGroup (Fin 6) :=
  ⟨swap 0 4 * swap 0 1 * swap 0 3 * swap 2 5, mem_alternatingGroup.mpr (by decide)⟩

theorem a6sig_conj : a6sig * a6c012 * a6sig⁻¹ = a6c345 := by decide

theorem exists_conj_x0_k1 : ∃ a : A5, a * x0 * a⁻¹ = k1 :=
  ⟨⟨swap 2 3 * swap 2 4, by decide⟩, by decide⟩

namespace CaseICoords

variable {G : Type} [Group G] [Finite G] {A B R T : Subgroup G} (c : CaseICoords A B R T)

include c in
theorem mul_self_of_two_elt {k : G} (hk : k ∈ centralizer (A : Set G)) {j : ℕ}
    (hkj : k ^ 2 ^ j = 1) : k * k = 1 := by
  obtain ⟨g, -, hg⟩ := exists_conj_mem_of_isSylowOf c.pair.sylowR hk hkj
  have h1 := c.mul_self_of_mem_R hg
  calc k * k = g⁻¹ * ((g * k * g⁻¹) * (g * k * g⁻¹)) * g := by group
    _ = 1 := by rw [h1, mul_one, inv_mul_cancel]

include c in
theorem pow_four_of_mem_normalizer {n : G} (hn : n ∈ normalizer (A : Set G)) {j : ℕ}
    (hnj : n ^ 2 ^ j = 1) : n ^ 4 = 1 := by
  set σ := autPerm c.ψA.symm ⟨n, hn⟩ with hσ
  have hσj : σ ^ 2 ^ j = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨n, hn⟩ : normalizer (A : Set G)) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hnj)
    rw [this, map_one]
  have hσ4 : σ ^ 4 = 1 := pow_four_of_two_pow hσj
  have hσ2 : σ ^ 2 ∈ alternatingGroup (Fin 5) := by
    rw [mem_alternatingGroup, map_pow, sq]
    exact Int.units_mul_self _
  set a : G := (c.ψA ⟨σ ^ 2, hσ2⟩ : G) with ha
  have haA : a ∈ A := (c.ψA ⟨σ ^ 2, hσ2⟩).2
  have hσa : autPerm c.ψA.symm ⟨a, le_normalizer haA⟩ = σ ^ 2 := by
    rw [autPerm_of_mem c.ψA.symm haA]
    simp [ha]
  have hkN : n ^ 2 * a⁻¹ ∈ normalizer (A : Set G) :=
    mul_mem (pow_mem hn 2) (inv_mem (le_normalizer haA))
  have hkA : n ^ 2 * a⁻¹ ∈ centralizer (A : Set G) := by
    apply (autPerm_eq_one_iff c.ψA.symm ⟨_, hkN⟩).mp
    have : (⟨n ^ 2 * a⁻¹, hkN⟩ : normalizer (A : Set G)) =
        ⟨n, hn⟩ ^ 2 * (⟨a, le_normalizer haA⟩ : normalizer (A : Set G))⁻¹ :=
      Subtype.ext (by simp)
    rw [this, map_mul, map_inv, map_pow, ← hσ, hσa, mul_inv_cancel]
  set k := n ^ 2 * a⁻¹ with hk
  have hak : a * k = k * a := mem_centralizer_iff.mp hkA a haA
  have ha2 : a * a = 1 := by
    have h1 : (⟨σ ^ 2, hσ2⟩ : A5) * ⟨σ ^ 2, hσ2⟩ = 1 :=
      Subtype.ext (show σ ^ 2 * σ ^ 2 = 1 by rw [← pow_add]; exact hσ4)
    rw [ha, ← Subgroup.coe_mul, ← map_mul, h1, map_one, Subgroup.coe_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hn2 : n ^ 2 = k * a := by rw [hk]; group
  have hna : n ^ 2 * a = a * n ^ 2 := by
    rw [hn2, mul_assoc, ha2, mul_one, ← mul_assoc, hak, mul_assoc, ha2, mul_one]
  have hkj : k ^ 2 ^ (j + 1) = 1 := by
    rw [show k = n ^ 2 * a by rw [hk, hainv], Commute.mul_pow hna (2 ^ (j + 1))]
    have h1 : (n ^ 2) ^ 2 ^ (j + 1) = 1 := by
      rw [← pow_mul, pow_succ, show 2 * (2 ^ j * 2) = 2 ^ j * 4 by ring, pow_mul, hnj, one_pow]
    have h2 : a ^ 2 ^ (j + 1) = 1 := by
      rw [pow_succ, pow_mul', show a ^ 2 = 1 by rw [sq]; exact ha2, one_pow]
    rw [h1, h2, one_mul]
  have hk2 := c.mul_self_of_two_elt hkA hkj
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hn2, sq,
    show k * a * (k * a) = (k * k) * (a * a) by rw [mul_assoc, ← mul_assoc a, hak]; group,
    hk2, ha2, one_mul]

omit [Finite G] in
theorem vB_pow_three : c.vB ^ 3 = 1 := by
  rw [vB, ← SubgroupClass.coe_pow, ← map_pow, ← orderOf_y0, pow_orderOf_eq_one, map_one,
    OneMemClass.coe_one]

theorem commute_vB_w : Commute c.vB c.w :=
  (mem_centralizer_iff.mp c.vB_mem_centralizer c.w c.w_mem).symm

theorem eq_one_of_commute_vB_w {θ : c.Hbar ≃* alternatingGroup (Fin 6)}
    (hθ : ∀ σ : A5, θ (c.barOf c.B_le_H (c.ψB σ)) = ι56 σ) {j : G} (hj : j * j = 1)
    (hjv : j * c.vB = c.vB * j) (hjw : j * c.w = c.w * j) : j = 1 := by
  have hjH : j ∈ c.H := mem_centralizer_singleton_iff.mpr hjw
  have hvb : θ (c.barOf c.B_le_H (c.ψB y0)) = a6c012 := by rw [hθ, ι56_y0]
  have hcomm : θ ((⟨j, hjH⟩ : c.H) : c.Hbar) * a6c012 =
      a6c012 * θ ((⟨j, hjH⟩ : c.H) : c.Hbar) := by
    rw [← hvb, ← map_mul, ← map_mul, barOf_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext hjv
  have hodd := odd_orderOf_of_commute_a6c012 hcomm
  have h2 : θ ((⟨j, hjH⟩ : c.H) : c.Hbar) ^ 2 = 1 := by
    rw [← map_pow, sq, ← QuotientGroup.mk_mul,
      show (⟨j, hjH⟩ : c.H) * ⟨j, hjH⟩ = 1 from Subtype.ext hj, QuotientGroup.mk_one, map_one]
  have h1 : θ ((⟨j, hjH⟩ : c.H) : c.Hbar) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h' | h'
    · exact orderOf_eq_one_iff.mp h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  have hjO : j ∈ c.O := (c.mk_eq_one_iff ⟨j, hjH⟩).mp (θ.injective (by rw [h1, map_one]))
  have hoddj : Odd (orderOf j) := by
    have h1 : orderOf j ∣ Nat.card c.O := by
      rw [← Subgroup.orderOf_mk j hjO]
      exact orderOf_dvd_natCard _
    exact c.odd_card_O.of_dvd_nat h1
  rcases (Nat.dvd_prime Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show j ^ 2 = 1 by rw [sq]; exact hj)) with h' | h'
  · exact orderOf_eq_one_iff.mp h'
  · rw [h'] at hoddj
    exact absurd hoddj (by decide)

theorem odd_orderOf_of_commute_vB_w {θ : c.Hbar ≃* alternatingGroup (Fin 6)}
    (hθ : ∀ σ : A5, θ (c.barOf c.B_le_H (c.ψB σ)) = ι56 σ) {n : G}
    (hnv : n * c.vB = c.vB * n) (hnw : n * c.w = c.w * n) : Odd (orderOf n) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' (G := zpowers n) 2
    (by rw [Nat.card_zpowers]; exact even_iff_two_dvd.mp hev)
  have hj2 : (j : G) * j = 1 := by
    have := pow_orderOf_eq_one j
    rw [hj, sq] at this
    exact congrArg Subtype.val this
  have hj1 : (j : G) ≠ 1 := fun h => by
    have : j = 1 := Subtype.ext h
    rw [this, orderOf_one] at hj
    omega
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp j.2
  apply hj1
  refine c.eq_one_of_commute_vB_w hθ hj2 ?_ ?_
  · rw [← hk]
    exact (Commute.zpow_left hnv k).eq
  · rw [← hk]
    exact (Commute.zpow_left hnw k).eq

theorem x_conj_eq_inv_of_mem
    (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) {θ : c.Hbar ≃* alternatingGroup (Fin 6)}
    (hθ : ∀ σ : A5, θ (c.barOf c.B_le_H (c.ψB σ)) = ι56 σ) (hw : c.w ∈ c.D) {h : c.D}
    (hh : θ (c.barOf c.D_le_H h) = a6c345) : c.x * (h : G) * c.x⁻¹ = (h : G)⁻¹ := by
  set z := c.x * (h : G) * c.x⁻¹ * h with hz
  have hzO := x_conj_mul_mem_O hθ hh
  have hzD : z ∈ c.D := mul_mem ((mem_normalizer_iff.mp c.x_mem_normalizer_D h).mp h.2) h.2
  set Z := (c.barOf c.D_le_H).ker with hZ
  have hwZ : (⟨c.w, hw⟩ : c.D) ∈ Z := by
    rw [hZ, MonoidHom.mem_ker, barOf_apply, c.mk_eq_one_iff]
    exact c.w_mem_O
  have hzZ : (⟨z, hzD⟩ : c.D) ∈ Z := by
    rw [hZ, MonoidHom.mem_ker, barOf_apply, c.mk_eq_one_iff]
    exact hzO
  have hZ3 : Nat.card Z ∣ 3 := c.card_ker_dvd_three hA6
  have hwo : orderOf (⟨c.w, hw⟩ : c.D) = 3 := by rw [Subgroup.orderOf_mk, c.orderOf_w]
  have hZeq : zpowers (⟨⟨c.w, hw⟩, hwZ⟩ : Z) = ⊤ := by
    apply eq_top_of_card_eq
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hwo]
    have h3 : 3 ∣ Nat.card Z := by
      rw [← hwo, ← Subgroup.orderOf_mk _ hwZ]
      exact orderOf_dvd_natCard _
    exact Nat.dvd_antisymm h3 hZ3
  have hzmem : (⟨⟨z, hzD⟩, hzZ⟩ : Z) ∈ zpowers (⟨⟨c.w, hw⟩, hwZ⟩ : Z) := by
    rw [hZeq]
    exact mem_top _
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hzmem
  have hzi : z = c.w ^ i := by
    have := congrArg (fun q : Z => ((q : c.D) : G)) hi
    simpa using this.symm
  have hzh : (h : G) * z = z * h := mem_centralizer_iff.mp (c.O_le_centralizer_D hzO) h h.2
  have hxz : c.x * z * c.x⁻¹ = z := by
    calc c.x * z * c.x⁻¹ = (h : G) * (c.x * h * c.x⁻¹ * h) * (h : G)⁻¹ := by
          rw [hz, c.x_inv]
          calc c.x * (c.x * (h : G) * c.x * h) * c.x = (c.x * c.x) * h * c.x * h * c.x := by
                group
            _ = (h : G) * c.x * h * c.x := by rw [c.x_mul_self, one_mul]
            _ = (h : G) * (c.x * h * c.x * h) * (h : G)⁻¹ := by group
      _ = z := by rw [← hz, hzh, mul_inv_cancel_right]
  have hz1 : z = 1 := by
    have h1 : c.x * c.w ^ i * c.x⁻¹ = (c.w ^ i)⁻¹ := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, c.x_conj_w, inv_zpow]
    rw [hzi, h1] at hxz
    have h2 : (c.w ^ i) ^ 2 = 1 := by
      rw [sq]
      calc c.w ^ i * c.w ^ i = c.w ^ i * (c.w ^ i)⁻¹ := by rw [hxz]
        _ = 1 := mul_inv_cancel _
    have hd3 : orderOf (c.w ^ i) ∣ 3 := orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.w_pow_three, one_zpow])
    have h1' : orderOf (c.w ^ i) = 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) hd3
      rwa [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one] at this
    rw [hzi]
    exact orderOf_eq_one_iff.mp h1'
  rw [hz] at hz1
  calc c.x * (h : G) * c.x⁻¹ = c.x * (h : G) * c.x⁻¹ * h * (h : G)⁻¹ := by group
    _ = (h : G)⁻¹ := by rw [hz1, one_mul]

theorem false_of_double_bad
    (hw : c.w ∈ c.D) (hv : c.symm.w ∈ c.symm.D) : False := by
  obtain ⟨u, hu⟩ := c.exists_isOuter
  obtain ⟨u', hu'⟩ := c.symm.exists_isOuter
  have hA6 := hu.nonempty_equiv_alt6
  have hA6' := hu'.nonempty_equiv_alt6
  obtain ⟨θ, hθ⟩ := c.exists_label hA6
  obtain ⟨θ', hθ'⟩ := c.symm.exists_label hA6'
  have hvw := c.commute_vB_w
  have hv3 := c.vB_pow_three
  have hw3 := c.w_pow_three
  obtain ⟨d, hd⟩ := c.map_D_surjective hA6 (θ.symm a6sig)
  set h : c.D := d * ⟨c.vB, c.vB_mem_D⟩ * d⁻¹ with hhdef
  have hh : θ (c.barOf c.D_le_H h) = a6c345 := by
    rw [hhdef]
    simp only [map_mul, map_inv]
    rw [hd, MulEquiv.apply_symm_apply, theta_vB hθ, a6sig_conj]
  have hc1 := commutator_eq_of_mem hθ hA6 hw hh
  have hxh := c.x_conj_eq_inv_of_mem hA6 hθ hw hh
  obtain ⟨d', hd'⟩ := c.symm.map_D_surjective hA6' (θ'.symm a6sig)
  set h' : c.symm.D := d' * ⟨c.symm.vB, c.symm.vB_mem_D⟩ * d'⁻¹ with hh'def
  have hh' : θ' (c.symm.barOf c.symm.D_le_H h') = a6c345 := by
    rw [hh'def]
    simp only [map_mul, map_inv]
    rw [hd', MulEquiv.apply_symm_apply, theta_vB hθ', a6sig_conj]
  have hc2 : ⁅c.w, (h' : G)⁆ = c.vB ∨ ⁅c.w, (h' : G)⁆ = c.vB⁻¹ :=
    commutator_eq_of_mem hθ' hA6' hv hh'
  have hhw : (h : G) * c.w * (h : G)⁻¹ = ew c.vB c.w (0, 1) := by
    rw [ew_zero_one, mem_centralizer_singleton_iff.mp (c.D_le_H h.2), mul_inv_cancel_right]
  have hh'v : (h' : G) * c.vB * (h' : G)⁻¹ = ew c.vB c.w (1, 0) := by
    have h1 : (h' : G) * c.vB = c.vB * (h' : G) :=
      mem_centralizer_singleton_iff.mp (c.symm.D_le_H h'.2)
    rw [ew_one_zero, h1, mul_inv_cancel_right]
  have hxv : c.x * c.vB * c.x⁻¹ = ew c.vB c.w (1, 0) := by
    rw [ew_one_zero, c.x_comm_vB, mul_inv_cancel_right]
  have hxw : c.x * c.w * c.x⁻¹ = ew c.vB c.w (0, -1) := by
    rw [ew_zero_neg_one hw3, c.x_conj_w]
  obtain ⟨e, he, hhv⟩ : ∃ e ∈ [(1 : ZMod 3), -1],
      (h : G) * c.vB * (h : G)⁻¹ = ew c.vB c.w (1, e) := by
    have key : (h : G) * c.vB * (h : G)⁻¹ = ⁅c.vB, (h : G)⁆⁻¹ * c.vB := by
      rw [commutatorElement_def]
      group
    rcases hc1 with h1 | h1
    · exact ⟨-1, by simp, by rw [key, h1, ew_one_neg_one hw3, hvw.inv_right.eq]⟩
    · exact ⟨1, by simp, by rw [key, h1, inv_inv, ew_one_one, hvw.eq]⟩
  obtain ⟨f, hf, hh'w⟩ : ∃ f ∈ [(1 : ZMod 3), -1],
      (h' : G) * c.w * (h' : G)⁻¹ = ew c.vB c.w (f, 1) := by
    have key : (h' : G) * c.w * (h' : G)⁻¹ = ⁅c.w, (h' : G)⁆⁻¹ * c.w := by
      rw [commutatorElement_def]
      group
    rcases hc2 with h1 | h1
    · exact ⟨-1, by simp, by rw [key, h1, ew_neg_one_one hv3]⟩
    · exact ⟨1, by simp, by rw [key, h1, inv_inv, ew_one_one]⟩
  have hLt := ((actsBy_of hvw hv3 hw3 hhv hhw).mul (actsBy_of hvw hv3 hw3 hh'v hh'w)).mul
    (actsBy_of hvw hv3 hw3 hxv hxw)
  obtain ⟨a, m, hmodd, hom⟩ :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos ((h : G) * h' * c.x)).ne'
  obtain ⟨s, hs⟩ : ∃ s, s = ((h : G) * h' * c.x) ^ m := ⟨_, rfl⟩
  have hs2 : s ^ 2 ^ a = 1 := by
    rw [hs, ← pow_mul, mul_comm m, ← hom, pow_orderOf_eq_one]
  have hs4 : ActsBy c.vB c.w (s ^ 4) Neg.neg := by
    have := hLt.pow_four_mul_odd (iterate_four_eq_neg e he f hf) hmodd
    rwa [pow_mul', ← hs] at this
  have hjv : s ^ 4 * c.vB * (s ^ 4)⁻¹ = c.vB⁻¹ := by
    have := hs4 (1, 0)
    rwa [ew_one_zero, show -((1 : ZMod 3), (0 : ZMod 3)) = (-1, 0) by decide,
      ew_neg_one_zero hv3] at this
  have hjw : s ^ 4 * c.w * (s ^ 4)⁻¹ = c.w⁻¹ := by
    have := hs4 (0, 1)
    rwa [ew_zero_one, show -((0 : ZMod 3), (1 : ZMod 3)) = (0, -1) by decide,
      ew_zero_neg_one hw3] at this
  have hs8 : s ^ 8 = 1 := by
    have h48 : s ^ 8 = (s ^ 4) ^ 2 := by rw [← pow_mul]
    have hodd := c.odd_orderOf_of_commute_vB_w hθ (h48 ▸ sq_mul_of_conj_eq_inv hjv)
      (h48 ▸ sq_mul_of_conj_eq_inv hjw)
    have h1 : (s ^ 8) ^ 2 ^ a = 1 := by rw [← pow_mul, mul_comm, pow_mul, hs2, one_pow]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    rcases i with _ | i
    · rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · rw [hi, pow_succ] at hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_mul.mpr (Or.inr even_two)))
  have hj2 : s ^ 4 * s ^ 4 = 1 := by rw [← pow_add]; exact hs8
  have hjinv : (s ^ 4)⁻¹ = s ^ 4 := inv_eq_of_mul_eq_one_right hj2
  obtain ⟨x', hx'⟩ : ∃ x', x' = (d : G)⁻¹ * c.x * d := ⟨_, rfl⟩
  have hhG : (h : G) = (d : G) * c.vB * (d : G)⁻¹ := rfl
  have hx'v : x' * c.vB * x'⁻¹ = c.vB⁻¹ := by
    rw [hhG] at hxh
    calc x' * c.vB * x'⁻¹ = (d : G)⁻¹ * (c.x * ((d : G) * c.vB * (d : G)⁻¹) * c.x⁻¹) * d := by
          rw [hx']
          group
      _ = c.vB⁻¹ := by
          rw [hxh]
          group
  have hdw : (d : G) * c.w = c.w * d := mem_centralizer_singleton_iff.mp (c.D_le_H d.2)
  have hx'w : x' * c.w * x'⁻¹ = c.w⁻¹ := by
    have h1 : (d : G) * c.w * (d : G)⁻¹ = c.w := by rw [hdw, mul_inv_cancel_right]
    have h2 : (d : G)⁻¹ * c.w⁻¹ * d = c.w⁻¹ := by
      calc (d : G)⁻¹ * c.w⁻¹ * d = ((d : G)⁻¹ * (c.w * d))⁻¹ := by group
        _ = c.w⁻¹ := by rw [← hdw, inv_mul_cancel_left]
    calc x' * c.w * x'⁻¹ = (d : G)⁻¹ * (c.x * ((d : G) * c.w * (d : G)⁻¹) * c.x⁻¹) * d := by
          rw [hx']
          group
      _ = c.w⁻¹ := by rw [h1, c.x_conj_w, h2]
  have hx'x' : x' * x' = 1 := by
    rw [hx']
    calc (d : G)⁻¹ * c.x * d * ((d : G)⁻¹ * c.x * d) = (d : G)⁻¹ * (c.x * c.x) * d := by group
      _ = 1 := by rw [c.x_mul_self, mul_one, inv_mul_cancel]
  have hx'inv : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'x'
  obtain ⟨n, hn⟩ : ∃ n, n = x' * s ^ 4 := ⟨_, rfl⟩
  have hnv : n * c.vB = c.vB * n := by
    refine mul_inv_eq_iff_eq_mul.mp ?_
    calc n * c.vB * n⁻¹ = x' * (s ^ 4 * c.vB * (s ^ 4)⁻¹) * x'⁻¹ := by
          rw [hn]
          group
      _ = (x' * c.vB * x'⁻¹)⁻¹ := by
          rw [hjv]
          group
      _ = c.vB := by rw [hx'v, inv_inv]
  have hnw : n * c.w = c.w * n := by
    refine mul_inv_eq_iff_eq_mul.mp ?_
    calc n * c.w * n⁻¹ = x' * (s ^ 4 * c.w * (s ^ 4)⁻¹) * x'⁻¹ := by
          rw [hn]
          group
      _ = (x' * c.w * x'⁻¹)⁻¹ := by
          rw [hjw]
          group
      _ = c.w := by rw [hx'w, inv_inv]
  obtain ⟨k, hk⟩ := c.odd_orderOf_of_commute_vB_w hθ hnv hnw
  have hx'n : x' * n * x'⁻¹ = n⁻¹ := by
    rw [hn, mul_inv_rev, hjinv, hx'inv, ← mul_assoc, hx'x', one_mul]
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ = n ^ (k + 1) := ⟨_, rfl⟩
  have hm₀2 : m₀ * m₀ = n := by
    rw [hm₀, ← pow_add, show k + 1 + (k + 1) = orderOf n + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hx'm : x' * m₀ * x'⁻¹ = m₀⁻¹ := by
    rw [hm₀, ← MulAut.conj_apply, map_pow, MulAut.conj_apply, hx'n, inv_pow]
  have hj : s ^ 4 = m₀⁻¹ * x' * m₀ := by
    calc s ^ 4 = (x' * s ^ 4)⁻¹ * x' := by rw [mul_inv_rev, inv_mul_cancel_right, hjinv]
      _ = (m₀ * m₀)⁻¹ * x' := by rw [hm₀2, hn]
      _ = m₀⁻¹ * (x' * m₀ * x'⁻¹) * x' := by
          rw [hx'm]
          group
      _ = m₀⁻¹ * x' * m₀ := by group
  obtain ⟨a₀, ha₀⟩ := exists_conj_x0_k1
  obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ = (c.ψA k1 : G) := ⟨_, rfl⟩
  have hxt : (c.ψA a₀ : G) * c.x * (c.ψA a₀ : G)⁻¹ = t₀ := by
    rw [ht₀, show c.x = (c.ψA x0 : G) from rfl, ← Subgroup.coe_inv, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, ← map_inv, ← map_mul, ← map_mul, ha₀]
  have ht₀A : t₀ ∈ A := ht₀ ▸ (c.ψA k1).2
  have ht₀T : t₀ ∈ T := by
    rw [c.mem_T_iff ht₀A]
    have : c.ψA.symm ⟨t₀, ht₀A⟩ = k1 := by
      apply c.ψA.injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext ht₀
    rw [this, mem_P0]
    decide
  have ht₀2 : t₀ * t₀ = 1 := c.mul_self_of_mem_T ht₀T
  have ht₀1 : t₀ ≠ 1 := by
    rw [ht₀]
    intro h1
    have := congrArg c.ψA.symm (Subtype.ext h1 : c.ψA k1 = 1)
    rw [MulEquiv.symm_apply_apply, map_one] at this
    exact absurd this (by decide)
  have ht₀C : t₀ ∈ centralizer (B : Set G) := by
    obtain ⟨Q, hQ⟩ := c.pair.sylowT
    rw [← hQ] at ht₀T
    obtain ⟨y, -, rfl⟩ := ht₀T
    exact y.2
  have hCN := c.pair.symm.centralizer_le_normalizer_of_mem ht₀C ht₀1 ht₀2
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, g₀ = (c.ψA a₀ : G) * d * m₀ := ⟨_, rfl⟩
  have hs₀4 : (g₀ * s * g₀⁻¹) ^ 4 = t₀ := by
    rw [conj_pow, hj, hx', ← hxt, hg₀]
    group
  have hs₀C : g₀ * s * g₀⁻¹ ∈ centralizer ({t₀} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hs₀4]
    exact (Commute.self_pow _ 4).eq
  have hs₀2 : (g₀ * s * g₀⁻¹) ^ 2 ^ a = 1 := by
    rw [conj_pow, hs2, mul_one, mul_inv_cancel]
  have h4 := c.symm.pow_four_of_mem_normalizer (hCN hs₀C) hs₀2
  rw [hs₀4] at h4
  exact ht₀1 h4

end CaseICoords

theorem caseIDoubleBad :
    CaseIDoubleBad :=
  fun _ _ _ _ _ _ _ _ _ c hw hv => c.false_of_double_bad hw hv

end CFSG.ComponentClassification.RankTwoAltFive
