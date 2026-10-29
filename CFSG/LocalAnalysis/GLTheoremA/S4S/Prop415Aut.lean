module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.CharacterTheory.OddOrderBasics.Solvability

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem commutator_le_of_normalizes {M : Type*} [Group M] {S B : Subgroup M}
    (hB : B ≤ Subgroup.normalizer (S : Set M)) : (⁅S, B⁆ : Subgroup M) ≤ S := by
  rw [Subgroup.commutator_le]
  intro s hs b hb
  rw [commutatorElement_def]
  have h1 : b * s⁻¹ * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hB hb) s⁻¹).1 (S.inv_mem hs)
  simpa [mul_assoc] using S.mul_mem hs h1

theorem localDeltaIn_zpowers {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M] {x : M} (hx : x ^ p = 1)
    (hx1 : x ≠ 1) (H : Subgroup M) :
    localDeltaIn p H (Subgroup.zpowers x) =
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set M)) := by
  have hcard : Nat.card (Subgroup.zpowers x) = p := card_zpowers_eq_of_pow hp hx hx1
  apply le_antisymm
  · exact iInf₂_le_of_le x (Subgroup.mem_zpowers x) (iInf_le_of_le hx1 le_rfl)
  · refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
    have hdle : Subgroup.zpowers d ≤ Subgroup.zpowers x := Subgroup.zpowers_le.2 hd
    have hdcard : Nat.card (Subgroup.zpowers d) = p := by
      have hdp : d ^ p = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
      exact card_zpowers_eq_of_pow hp hdp hd1
    have heq : Subgroup.zpowers d = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hdle (by rw [hcard, hdcard])
    have hC : Subgroup.centralizer ({d} : Set M) = Subgroup.centralizer ({x} : Set M) := by
      rw [← Subgroup.centralizer_closure ({d} : Set M), ← Subgroup.centralizer_closure ({x} : Set M),
        ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure, heq]
    rw [hC]

theorem card_inf_centralizer_modEq {q : ℕ} (hq : q.Prime) {M : Type} [Group M] [Finite M]
    {H U : Subgroup M} (hH : IsPGroup q H) (hHU : H ≤ Subgroup.normalizer (U : Set M)) :
    Nat.card ↥(U ⊓ Subgroup.centralizer (H : Set M)) ≡ Nat.card U [MOD q] := by
  haveI : Fact q.Prime := ⟨hq⟩
  letI : MulAction H U := MulAction.compHom U (Subgroup.inclusion hHU)
  have hact : ∀ (h : H) (u : U), ((h • u : U) : M) = (h : M) * (u : M) * (h : M)⁻¹ :=
    fun h u => rfl
  have hcong := hH.card_modEq_card_fixedPoints U
  have hfix : ∀ u : U, u ∈ MulAction.fixedPoints H U ↔ (u : M) ∈ Subgroup.centralizer (H : Set M) := by
    intro u
    rw [MulAction.mem_fixedPoints, Subgroup.mem_centralizer_iff]
    constructor
    · intro hu h hh
      have h1 := congrArg Subtype.val (hu ⟨h, hh⟩)
      rw [hact] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1)
    · intro hu h
      apply Subtype.ext
      rw [hact, hu (h : M) h.2, mul_inv_cancel_right]
  have e1 : Nat.card ↥(MulAction.fixedPoints H U) =
      Nat.card ↥((U ⊓ Subgroup.centralizer (H : Set M)).subgroupOf U) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hu
      exact ⟨u.2, (hfix u).1 hu⟩
    · intro hu
      exact (hfix u).2 hu.2
  have e2 : Nat.card ↥((U ⊓ Subgroup.centralizer (H : Set M)).subgroupOf U) =
      Nat.card ↥(U ⊓ Subgroup.centralizer (H : Set M)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← e2, ← e1]
  exact hcong.symm

private theorem p415_two_mul_card_le_of_lt {P : Type} [Group P] [Finite P] {H K : Subgroup P}
    (hHK : H < K) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hHK.le
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le (le_of_eq (by rw [hk, mul_one])))
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  calc 2 * Nat.card H = Nat.card H * 2 := by ring
    _ ≤ Nat.card H * k := Nat.mul_le_mul_left _ hk2

private theorem p415_three_le_index {P : Type} [Group P] [Finite P] (C : Subgroup P)
    (u v w : P) (h1 : u⁻¹ * v ∉ C) (h2 : u⁻¹ * w ∉ C) (h3 : v⁻¹ * w ∉ C) : 3 ≤ C.index := by
  classical
  show 3 ≤ Nat.card (P ⧸ C)
  haveI : Fintype (P ⧸ C) := Fintype.ofFinite _
  have hcard : ({(u : P ⧸ C), (v : P ⧸ C), (w : P ⧸ C)} : Finset (P ⧸ C)).card = 3 :=
    Finset.card_eq_three.2 ⟨(u : P ⧸ C), (v : P ⧸ C), (w : P ⧸ C),
      fun h => h1 (QuotientGroup.eq.1 h), fun h => h2 (QuotientGroup.eq.1 h),
      fun h => h3 (QuotientGroup.eq.1 h), rfl⟩
  have hle := Finset.card_le_univ ({(u : P ⧸ C), (v : P ⧸ C), (w : P ⧸ C)} : Finset (P ⧸ C))
  rw [hcard, Fintype.card_eq_nat_card] at hle
  exact hle

theorem card_commutator_le_two {P : Type} [Group P] [Finite P]
    (hP : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P) ≤ Subgroup.center P)
    (hcard : Nat.card P ≤ 4 * Nat.card (Subgroup.center P)) :
    Nat.card (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P) ≤ 2 := by
  have hcen : ∀ a b g : P, g * ⁅a, b⁆ = ⁅a, b⁆ * g := fun a b g =>
    Subgroup.mem_center_iff.1 (hP (Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
      (Subgroup.mem_top b))) g
  have hmulR : ∀ a b b' : P, ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
    intro a b b'
    have key : ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [key, hcen a b' b, mul_inv_cancel_right]
  have hmulL : ∀ a a' b : P, ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
    intro a a' b
    have key : ⁅a * a', b⁆ = (a * ⁅a', b⁆ * a⁻¹) * ⁅a, b⁆ := by
      simp only [commutatorElement_def]
      group
    rw [key, hcen a' b a, mul_inv_cancel_right]
  have hinvL : ∀ a b : P, ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
    intro a b
    have h := hmulL a⁻¹ a b
    rw [inv_mul_cancel, commutatorElement_one_left] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hinvR : ∀ a b : P, ⁅a, b⁆⁻¹ = ⁅b, a⁆ := fun a b => commutatorElement_inv a b
  have hmemC : ∀ a g : P, g ∈ Subgroup.centralizer ({a} : Set P) ↔ ⁅a, g⁆ = 1 := by
    intro a g
    rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_eq_one_iff_mul_comm]
    exact eq_comm
  have hidx : ∀ a b : P, ⁅a, b⁆ ≠ 1 → (Subgroup.centralizer ({a} : Set P)).index ≤ 2 := by
    intro a b hab
    have haZ : a ∉ Subgroup.center P := by
      intro h
      apply hab
      exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 h b).symm
    have hlt : Subgroup.center P < Subgroup.centralizer ({a} : Set P) := by
      refine lt_of_le_of_ne (Subgroup.center_le_centralizer _) ?_
      intro h
      apply haZ
      rw [h]
      exact (hmemC a a).2 (commutatorElement_self a)
    have h2 := p415_two_mul_card_le_of_lt hlt
    have hmul : Nat.card (Subgroup.centralizer ({a} : Set P)) *
        (Subgroup.centralizer ({a} : Set P)).index = Nat.card P := Subgroup.card_mul_index _
    have hpos : 0 < Nat.card (Subgroup.center P) := Nat.card_pos
    have key : 2 * Nat.card (Subgroup.center P) * (Subgroup.centralizer ({a} : Set P)).index ≤
        2 * Nat.card (Subgroup.center P) * 2 := by
      calc 2 * Nat.card (Subgroup.center P) * (Subgroup.centralizer ({a} : Set P)).index
          = (2 * Nat.card (Subgroup.center P)) * (Subgroup.centralizer ({a} : Set P)).index := rfl
        _ ≤ Nat.card (Subgroup.centralizer ({a} : Set P)) *
            (Subgroup.centralizer ({a} : Set P)).index := Nat.mul_le_mul_right _ h2
        _ = Nat.card P := hmul
        _ ≤ 4 * Nat.card (Subgroup.center P) := hcard
        _ = 2 * Nat.card (Subgroup.center P) * 2 := by ring
    exact Nat.le_of_mul_le_mul_left key (by omega)
  have hGL : ∀ a b : P, ⁅a, b⁆ ≠ 1 → ∀ g : P, ⁅a, g⁆ = 1 ∨ ⁅a, g⁆ = ⁅a, b⁆ := by
    intro a b hab g
    by_contra hcon
    push Not at hcon
    obtain ⟨hg1, hg2⟩ := hcon
    have hbC : b⁻¹ * g ∉ Subgroup.centralizer ({a} : Set P) := by
      rw [hmemC]
      intro h
      apply hg2
      have h' : ⁅a, b * (b⁻¹ * g)⁆ = ⁅a, b⁆ * ⁅a, b⁻¹ * g⁆ := hmulR a b (b⁻¹ * g)
      rw [mul_inv_cancel_left, h, mul_one] at h'
      exact h'
    have h3 := p415_three_le_index (Subgroup.centralizer ({a} : Set P)) 1 b g
      (by rw [inv_one, one_mul, hmemC]; exact hab) (by rw [inv_one, one_mul, hmemC]; exact hg1) hbC
    have := hidx a b hab
    omega
  obtain ⟨c, hc2, hcom⟩ : ∃ c : P, c ^ 2 = 1 ∧ ∀ a b : P, ⁅a, b⁆ ∈ Subgroup.zpowers c := by
    by_cases hab : ∀ a b : P, ⁅a, b⁆ = 1
    · exact ⟨1, one_pow 2, fun a b => by rw [hab a b]; exact Subgroup.one_mem _⟩
    push Not at hab
    obtain ⟨x, y, hxy⟩ := hab
    have hyx : ⁅y, x⁆ ≠ 1 := by
      intro h
      apply hxy
      have h' := hinvR x y
      rw [h] at h'
      exact inv_eq_one.1 h'
    have hxZ : x ∉ Subgroup.center P := fun h =>
      hxy (commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 h y).symm)
    have hsq : ⁅x, y⁆ ^ 2 = 1 := by
      have h1 := hGL x y hxy (y * y)
      rw [hmulR] at h1
      rcases h1 with h | h
      · rw [pow_two]
        exact h
      · exfalso
        apply hxy
        have h2 := congrArg (fun t => t * ⁅x, y⁆⁻¹) h
        simpa using h2
    let S : Subgroup P :=
      { carrier := {g | ∀ b : P, ⁅g, b⁆ ∈ Subgroup.zpowers ⁅x, y⁆}
        mul_mem' := fun {g g'} hg hg' b => by
          show ⁅g * g', b⁆ ∈ Subgroup.zpowers ⁅x, y⁆
          rw [hmulL]
          exact Subgroup.mul_mem _ (hg' b) (hg b)
        one_mem' := fun b => by
          show ⁅(1 : P), b⁆ ∈ Subgroup.zpowers ⁅x, y⁆
          rw [commutatorElement_one_left]
          exact Subgroup.one_mem _
        inv_mem' := fun {g} hg b => by
          show ⁅g⁻¹, b⁆ ∈ Subgroup.zpowers ⁅x, y⁆
          rw [hinvL]
          exact Subgroup.inv_mem _ (hg b) }
    have hS : ∀ g : P, g ∈ S ↔ ∀ b : P, ⁅g, b⁆ ∈ Subgroup.zpowers ⁅x, y⁆ := fun g => Iff.rfl
    have hZS : ∀ z ∈ Subgroup.center P, z ∈ S := fun z hz => (hS z).2 fun b => by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz b).symm]
      exact Subgroup.one_mem _
    have hxS : x ∈ S := (hS x).2 fun b => by
      rcases hGL x y hxy b with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    have hyS : y ∈ S := (hS y).2 fun b => by
      have hyxmem : ⁅y, x⁆ ∈ Subgroup.zpowers ⁅x, y⁆ := by
        rw [← hinvR x y]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      rcases hGL y x hyx b with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact hyxmem
    have hyCx : y ∉ Subgroup.centralizer ({x} : Set P) := by
      rw [hmemC]
      exact hxy
    have hCx_idx : 2 ≤ (Subgroup.centralizer ({x} : Set P)).index := by
      have h1 : (Subgroup.centralizer ({x} : Set P)).index ≠ 1 := fun h =>
        hyCx (by rw [Subgroup.index_eq_one.1 h]; exact Subgroup.mem_top y)
      have h0 : (Subgroup.centralizer ({x} : Set P)).index ≠ 0 := by
        intro h
        have hm := Subgroup.card_mul_index (Subgroup.centralizer ({x} : Set P))
        rw [h, mul_zero] at hm
        have hP0 : 0 < Nat.card P := Nat.card_pos
        omega
      omega
    have hCx_le : Nat.card (Subgroup.centralizer ({x} : Set P)) ≤
        2 * Nat.card (Subgroup.center P) := by
      have hm : Nat.card (Subgroup.centralizer ({x} : Set P)) *
          (Subgroup.centralizer ({x} : Set P)).index = Nat.card P := Subgroup.card_mul_index _
      have h2 : Nat.card (Subgroup.centralizer ({x} : Set P)) * 2 ≤
          Nat.card (Subgroup.centralizer ({x} : Set P)) *
            (Subgroup.centralizer ({x} : Set P)).index :=
        Nat.mul_le_mul_left _ hCx_idx
      linarith
    have hZltZx : Subgroup.center P < Subgroup.center P ⊔ Subgroup.zpowers x := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro h
      apply hxZ
      have hx' : x ∈ Subgroup.center P ⊔ Subgroup.zpowers x :=
        (le_sup_right : Subgroup.zpowers x ≤ Subgroup.center P ⊔ Subgroup.zpowers x) (Subgroup.mem_zpowers x)
      rw [← h] at hx'
      exact hx'
    have hZx_card : 2 * Nat.card (Subgroup.center P) ≤ Nat.card ↥(Subgroup.center P ⊔ Subgroup.zpowers x) :=
      p415_two_mul_card_le_of_lt hZltZx
    have hxC : x ∈ Subgroup.centralizer ({x} : Set P) := (hmemC x x).2 (commutatorElement_self x)
    have hsup_le : Subgroup.center P ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set P) :=
      sup_le (Subgroup.center_le_centralizer _) (Subgroup.zpowers_le.2 hxC)
    have hCx_eq : Subgroup.center P ⊔ Subgroup.zpowers x = Subgroup.centralizer ({x} : Set P) :=
      Subgroup.eq_of_le_of_card_ge hsup_le (by omega)
    have hCxS : Subgroup.centralizer ({x} : Set P) ≤ S := by
      rw [← hCx_eq]
      exact sup_le (fun z hz => hZS z hz) (Subgroup.zpowers_le.2 hxS)
    have hallS : ∀ g : P, g ∈ S := by
      intro g
      rcases hGL x y hxy g with h | h
      · exact hCxS ((hmemC x g).2 h)
      · have hyinv : ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
          have h1 : ⁅x, y * y⁻¹⁆ = ⁅x, y⁆ * ⁅x, y⁻¹⁆ := hmulR x y y⁻¹
          rw [mul_inv_cancel, commutatorElement_one_right] at h1
          exact eq_inv_of_mul_eq_one_right h1.symm
        have hk : y⁻¹ * g ∈ Subgroup.centralizer ({x} : Set P) := by
          rw [hmemC, hmulR x y⁻¹ g, hyinv, h, inv_mul_cancel]
        have h4 := Subgroup.mul_mem _ hyS (hCxS hk)
        rwa [mul_inv_cancel_left] at h4
    exact ⟨⁅x, y⁆, hsq, fun a b => (hS a).1 (hallS a) b⟩
  have hT : (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P) ≤ Subgroup.zpowers c :=
    Subgroup.commutator_le.2 fun a _ b _ => hcom a b
  have hord : orderOf c ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc2)
  calc Nat.card (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ : Subgroup P)
      ≤ Nat.card (Subgroup.zpowers c) := Subgroup.card_le_of_le hT
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 2 := hord

private theorem p415_three_le_card {G : Type} [Group G] [Finite G] (U : Subgroup G) {x y z : G}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 ≤ Nat.card U := by
  classical
  haveI : Fintype U := Fintype.ofFinite _
  have hcard : ({(⟨x, hx⟩ : U), ⟨y, hy⟩, ⟨z, hz⟩} : Finset U).card = 3 :=
    Finset.card_eq_three.2 ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩,
      fun h => hxy (congrArg Subtype.val h), fun h => hxz (congrArg Subtype.val h),
      fun h => hyz (congrArg Subtype.val h), rfl⟩
  have hle := Finset.card_le_univ ({(⟨x, hx⟩ : U), ⟨y, hy⟩, ⟨z, hz⟩} : Finset U)
  rw [hcard, Fintype.card_eq_nat_card] at hle
  exact hle

private theorem p415_comm_bot_of_card_le_two {M : Type} [Group M] [Finite M] {B U : Subgroup M}
    (hBU : B ≤ Subgroup.normalizer (U : Set M)) (hU : Nat.card U ≤ 2) : ⁅B, U⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  by_contra hne
  have hv : b * u * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hBU hb) u).1 hu
  have hu1 : u ≠ 1 := by
    rintro rfl
    apply hne
    simp
  have hv1 : b * u * b⁻¹ ≠ 1 := by
    intro h
    apply hu1
    simpa using h
  have hvu : b * u * b⁻¹ ≠ u := by
    intro h
    apply hne
    have h' : b * u = u * b := mul_inv_eq_iff_eq_mul.1 h
    exact h'.symm
  have h3 := p415_three_le_card U (x := 1) (y := u) (z := b * u * b⁻¹) U.one_mem hu hv
    (fun h => hu1 h.symm) (fun h => hv1 h.symm) (fun h => hvu h.symm)
  omega

private theorem p415_isCyclic_of_card_le_three {G : Type} [Group G] [Finite G]
    (h : Nat.card G ≤ 3) : IsCyclic G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 3) with h1 | h2 | h3
  · haveI : Subsingleton G := Finite.card_le_one_iff_subsingleton.1 (by omega)
    infer_instance
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card h2
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card h3

private theorem p415_commutator_bot_of_isCyclic {G : Type} [Group G] [Finite G] [IsCyclic G] :
    (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ : Subgroup G) = ⊥ :=
  (commutator_eq_bot_iff G).2 inferInstance

private theorem p415_dvd_four {X : ℕ} (hX : 0 < X) (hd : X ∣ 4) : X = 1 ∨ X = 2 ∨ X = 4 := by
  have hle : X ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  interval_cases X <;> omega

theorem small_two_group {M : Type} [Group M] [Finite M] {B S : Subgroup M} (hB : IsPGroup 3 B)
    (hS : IsPGroup 2 S) (hBS : B ≤ Subgroup.normalizer (S : Set M))
    (hBSS : (⁅B, S⁆ : Subgroup M) = S) (hcard : Nat.card S ≤ 16) :
    (⁅B, (⁅S, S⁆ : Subgroup M)⁆ : Subgroup M) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS : (⁅S, S⁆ : Subgroup M) ≤ S := commutator_self_le S
  have hBT : B ≤ Subgroup.normalizer ((⁅S, S⁆ : Subgroup M) : Set M) :=
    le_normalizer_commutator hBS hBS
  have hSN : S ≤ Subgroup.normalizer ((⁅S, S⁆ : Subgroup M) : Set M) :=
    le_normalizer_commutator Subgroup.le_normalizer Subgroup.le_normalizer
  have hT2 : IsPGroup 2 (⁅S, S⁆ : Subgroup M) := hS.to_le hTS
  by_contra hne
  have hT4 : 4 ≤ Nat.card (⁅S, S⁆ : Subgroup M) := by
    by_contra hlt
    apply hne
    apply p415_comm_bot_of_card_le_two hBT
    have hlt' : Nat.card (⁅S, S⁆ : Subgroup M) < 4 := not_le.1 hlt
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hk2 : k < 2 := by
      by_contra h
      push Not at h
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      norm_num at h4
      omega
    interval_cases k <;> simp only [pow_zero, pow_one] at hk <;> omega
  have hS'card : Nat.card (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) =
      Nat.card (⁅S, S⁆ : Subgroup M) := by
    have htop : (⊤ : Subgroup S).map S.subtype = S := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hmap : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S).map S.subtype = ⁅S, S⁆ := by
      rw [Subgroup.map_commutator, htop]
    rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective S)]
  have hidx4 : 4 ≤ (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S).index := by
    by_contra hlt
    push Not at hlt
    have hcyc : IsCyclic S := by
      apply CFSG.OddOrderBasics.p_group_cyclic_abelianization hS
      apply p415_isCyclic_of_card_le_three
      unfold Subgroup.index at hlt
      exact Nat.lt_succ_iff.1 hlt
    haveI := hcyc
    have h1 : Nat.card (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) = 1 := by
      rw [p415_commutator_bot_of_isCyclic]
      simp
    rw [hS'card] at h1
    omega
  have hT_le4 : Nat.card (⁅S, S⁆ : Subgroup M) ≤ 4 := by
    have hm := Subgroup.card_mul_index (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S)
    rw [hS'card] at hm
    have h5 : Nat.card (⁅S, S⁆ : Subgroup M) * 4 ≤
        Nat.card (⁅S, S⁆ : Subgroup M) * (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S).index :=
      Nat.mul_le_mul_left _ hidx4
    linarith
  have hT4' : Nat.card (⁅S, S⁆ : Subgroup M) = 4 := le_antisymm hT_le4 hT4
  have hWB : Nat.card ↥((⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (B : Set M)) = 1 := by
    have hmod := card_inf_centralizer_modEq (q := 3) (by norm_num) hB hBT
    rw [hT4'] at hmod
    have hdvd : Nat.card ↥((⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (B : Set M)) ∣ 4 := by
      rw [← hT4']
      exact Subgroup.card_dvd_of_le inf_le_left
    have hpos : 0 < Nat.card ↥((⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (B : Set M)) :=
      Nat.card_pos
    rcases p415_dvd_four hpos hdvd with h1 | h2 | h4
    · exact h1
    · exfalso
      unfold Nat.ModEq at hmod
      rw [h2] at hmod
      norm_num at hmod
    · exfalso
      apply hne
      have hEq : (⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (B : Set M) = ⁅S, S⁆ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hT4', h4]))
      have hTC : (⁅S, S⁆ : Subgroup M) ≤ Subgroup.centralizer (B : Set M) :=
        le_trans (le_of_eq hEq.symm) inf_le_right
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hTC
  have hBCS : ∀ b ∈ B, ∀ w ∈ Subgroup.centralizer (S : Set M),
      b * w * b⁻¹ ∈ Subgroup.centralizer (S : Set M) := by
    intro b hb w hw
    rw [Subgroup.mem_centralizer_iff] at hw ⊢
    intro s hs
    have hs' : b⁻¹ * s * b ∈ (S : Set M) := by
      have h6 := (Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.inv_mem _ hb)) s).1 hs
      rwa [inv_inv] at h6
    have hw' := hw _ hs'
    calc s * (b * w * b⁻¹) = b * ((b⁻¹ * s * b) * w) * b⁻¹ := by group
      _ = b * (w * (b⁻¹ * s * b)) * b⁻¹ := by rw [hw']
      _ = (b * w * b⁻¹) * s := by group
  have hBW : ∀ b ∈ B, ∀ h : M, h ∈ (⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (S : Set M) →
      b * h * b⁻¹ ∈ (⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (S : Set M) := by
    intro b hb h hh
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hh
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hBT hb) h).1 h1, hBCS b hb h h2⟩
  have hBWN : B ≤ Subgroup.normalizer
      (((⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (S : Set M) : Subgroup M) : Set M) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hBW b hb h
    · intro hh
      have h7 := hBW b⁻¹ (Subgroup.inv_mem _ hb) _ hh
      have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rw [e] at h7
      exact h7
  have hW : (⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (S : Set M) = ⁅S, S⁆ := by
    have hmod := card_inf_centralizer_modEq (q := 2) (by norm_num) hS hSN
    rw [hT4'] at hmod
    have hdvd : Nat.card ↥((⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (S : Set M)) ∣ 4 := by
      rw [← hT4']
      exact Subgroup.card_dvd_of_le inf_le_left
    have hpos : 0 < Nat.card ↥((⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (S : Set M)) :=
      Nat.card_pos
    rcases p415_dvd_four hpos hdvd with h1 | h2 | h4
    · exfalso
      unfold Nat.ModEq at hmod
      rw [h1] at hmod
      norm_num at hmod
    · exfalso
      have hcomm := p415_comm_bot_of_card_le_two hBWN (le_of_eq h2)
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      have hle : (⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (S : Set M) ≤
          (⁅S, S⁆ : Subgroup M) ⊓ Subgroup.centralizer (B : Set M) :=
        le_inf inf_le_left hcomm
      have h8 := Subgroup.card_le_of_le hle
      rw [hWB, h2] at h8
      omega
    · exact Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hT4', h4]))
  have hTCS : (⁅S, S⁆ : Subgroup M) ≤ Subgroup.centralizer (S : Set M) :=
    le_trans (le_of_eq hW.symm) inf_le_right
  have hS'Z : (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) ≤ Subgroup.center S := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have ht : (⁅(a : M), (b : M)⁆ : M) ∈ (⁅S, S⁆ : Subgroup M) :=
      Subgroup.commutator_mem_commutator a.2 b.2
    have hc := (Subgroup.mem_centralizer_iff.1 (hTCS ht)) (g : M) g.2
    rw [commutatorElement_def] at hc
    simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv]
    exact hc
  have hcardS : Nat.card S ≤ 4 * Nat.card (Subgroup.center S) := by
    have h1 : Nat.card (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S) ≤
        Nat.card (Subgroup.center S) := Subgroup.card_le_of_le hS'Z
    rw [hS'card, hT4'] at h1
    omega
  have h2 := card_commutator_le_two hS'Z hcardS
  rw [hS'card, hT4'] at h2
  omega

theorem step10_aut {K : Type} [Group K] [Finite K] (hKq : CFSG.Open.IsQuasisimple K)
    (h1913 : I1913At) (h2027 : I2027At) {Bt St Sst V : Subgroup (MulAut K)} {xt : MulAut K}
    (hBt : IsElemAbelian 3 Bt) (hSt : IsPGroup 2 St)
    (hBS : Bt ≤ Subgroup.normalizer (St : Set (MulAut K)))
    (hBSS : (⁅Bt, St⁆ : Subgroup (MulAut K)) = St) (hSst : Sst ≤ St)
    (hBSst : Bt ≤ Subgroup.normalizer (Sst : Set (MulAut K)))
    (hidx : Nat.card St ≤ 4 * Nat.card Sst) (hSSle : (⁅St, St⁆ : Subgroup (MulAut K)) ≤ Sst)
    (hne : (⁅Bt, (⁅St, St⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) ≠ ⊥)
    (hVinn : innerAut K ≤ V) (hBV : Bt ≤ V) (hBnV : Bt ≤ Subgroup.normalizer (V : Set (MulAut K)))
    (hxB : xt ∈ Bt) (hx1 : xt ≠ 1)
    (hSx : Sst ≤ GLAPPrimeCoreOf 3 (V ⊓ Subgroup.centralizer ({xt} : Set (MulAut K))))
    (hlevel : ¬ IsTwoPrimaryWeaklyLocallyBalanced 3 1 Bt →
      catalogIs (K ⧸ Subgroup.center K) (k3 3)) : False := by
  have hpp : Nat.Prime 3 := Nat.prime_three
  have hx3 : xt ^ 3 = 1 := hBt.2 xt hxB
  have hBpg : IsPGroup 3 Bt := isPGroup_of_isElemAbelian hBt
  have hSS' : (⁅St, St⁆ : Subgroup (MulAut K)) ≤ St := commutator_self_le St
  have hBS' : Bt ≤ Subgroup.normalizer ((⁅St, St⁆ : Subgroup (MulAut K)) : Set (MulAut K)) :=
    le_normalizer_commutator hBS hBS
  by_cases hbal : IsTwoPrimaryWeaklyLocallyBalanced 3 1 Bt
  ·
    have hEk : IsEkIn 3 1 Bt (Subgroup.zpowers xt) :=
      ⟨Subgroup.zpowers_le.2 hxB, isElemAbelian_zpowers_of_mem hBt hxB, by
        rw [pow_one]
        exact card_zpowers_eq_of_pow hpp hx3 hx1⟩
    have hodd := hbal (Subgroup.zpowers xt) hEk V hVinn hBnV
    rw [localDeltaIn_zpowers hpp hx3 hx1 V] at hodd
    have hle : (⁅Bt, (⁅St, St⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) ≤
        ⁅GLAPPrimeCoreOf 3 (V ⊓ Subgroup.centralizer ({xt} : Set (MulAut K))), Bt⁆ :=
      calc (⁅Bt, (⁅St, St⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) ≤ ⁅Bt, Sst⁆ :=
            Subgroup.commutator_mono le_rfl hSSle
        _ = ⁅Sst, Bt⁆ := Subgroup.commutator_comm _ _
        _ ≤ _ := Subgroup.commutator_mono hSx le_rfl
    have h2sub : (⁅Bt, (⁅St, St⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) ≤ St := by
      rw [Subgroup.commutator_comm]
      exact (commutator_le_of_normalizes hBS').trans hSS'
    have h2 : 2 ∣ Nat.card (⁅Bt, (⁅St, St⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hP : IsPGroup 2 (⁅Bt, (⁅St, St⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) :=
        hSt.to_le h2sub
      haveI : Nontrivial (⁅Bt, (⁅St, St⁆ : Subgroup (MulAut K))⁆ : Subgroup (MulAut K)) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hne
      obtain ⟨n, hn, hcard⟩ := hP.nontrivial_iff_card.1 inferInstance
      rw [hcard]
      exact dvd_pow_self 2 hn.ne'
    exact (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hle)))
  ·
    have hcat := hlevel hbal
    have hsmall : catalogIs (K ⧸ Subgroup.center K) isSmallThree ∨
        catalogIs (K ⧸ Subgroup.center K) (onLie k3Lie) := by
      obtain ⟨i, hi, he⟩ := hcat
      cases i with
      | alternating n hn => exact Or.inl ⟨TauCeti.CFSGIndex.alternating n hn, hi.2, he⟩
      | lie j => exact Or.inr ⟨TauCeti.CFSGIndex.lie j, hi.2, he⟩
      | sporadic s => exact Or.inl ⟨TauCeti.CFSGIndex.sporadic s, hi.2, he⟩
      | cyclic n hn => exact hi.elim
    rcases hsmall with hsm | hL3
    ·
      have hxord : orderOf xt = 3 := by
        haveI : Fact (Nat.Prime 3) := ⟨hpp⟩
        exact orderOf_eq_prime hx3 hx1
      have h4 := h1913 K hKq hsm V hVinn xt (hBV hxB) hxord
      have h4' : Nat.card Sst ≤ 4 :=
        (Subgroup.card_le_of_le hSx).trans h4
      have h16 : Nat.card St ≤ 16 := by omega
      exact hne (small_two_group hBpg hSt hBS hBSS h16)
    ·
      exact hne (h2027 K hKq hL3 Bt St hBpg hSt hBS hBSS)

end CFSG.LocalAnalysis.GLTheoremA
