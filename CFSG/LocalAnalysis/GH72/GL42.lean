module

public import CFSG.LocalAnalysis.GH72.Vocabulary
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public section

namespace CFSG.GH72

open Subgroup MulAction

section Generic

variable {V : Type*} [Group V]

theorem exists_subgroup_eq_fixedBy (g : MulAut V) : ∃ W : Subgroup V, (W : Set V) = fixedBy V g :=
  ⟨{ carrier := fixedBy V g
     mul_mem' := fun {a b} ha hb => by
       rw [mem_fixedBy, MulAut.smul_def] at ha hb ⊢
       rw [map_mul, ha, hb]
     one_mem' := by rw [mem_fixedBy, MulAut.smul_def, map_one]
     inv_mem' := fun {a} ha => by
       rw [mem_fixedBy, MulAut.smul_def] at ha ⊢
       rw [map_inv, ha] }, rfl⟩

theorem exists_subgroup_eq_fixedPoints (Q : Subgroup (MulAut V)) :
    ∃ W : Subgroup V, (W : Set V) = fixedPoints Q V :=
  ⟨{ carrier := fixedPoints Q V
     mul_mem' := fun {a b} ha hb => by
       rw [mem_fixedPoints] at ha hb ⊢
       intro q
       change (q : MulAut V) (a * b) = a * b
       rw [map_mul]
       exact congrArg₂ (· * ·) (ha q) (hb q)
     one_mem' := by
       rw [mem_fixedPoints]
       intro q
       change (q : MulAut V) 1 = 1
       rw [map_one]
     inv_mem' := fun {a} ha => by
       rw [mem_fixedPoints] at ha ⊢
       intro q
       change (q : MulAut V) a⁻¹ = a⁻¹
       rw [map_inv]
       exact congrArg (·⁻¹) (ha q) }, rfl⟩

theorem card_fixedBy_dvd [Finite V] (g : MulAut V) : Nat.card (fixedBy V g) ∣ Nat.card V := by
  obtain ⟨W, hW⟩ := exists_subgroup_eq_fixedBy g
  rw [← hW]
  exact W.card_subgroup_dvd_card

theorem card_fixedPoints_dvd [Finite V] (Q : Subgroup (MulAut V)) :
    Nat.card (fixedPoints Q V) ∣ Nat.card V := by
  obtain ⟨W, hW⟩ := exists_subgroup_eq_fixedPoints Q
  rw [← hW]
  exact W.card_subgroup_dvd_card

theorem fixedPoints_zpowers (g : MulAut V) : fixedPoints (zpowers g) V = fixedBy V g := by
  ext v
  rw [mem_fixedPoints, mem_fixedBy]
  constructor
  · intro h
    exact h ⟨g, mem_zpowers g⟩
  · rintro h ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact mem_fixedBy_zpow (α := V) h n

theorem eq_one_of_forall_apply_eq {g : MulAut V} (h : ∀ v, g v = v) : g = 1 :=
  MulEquiv.ext fun v => (h v).trans rfl

theorem eq_bot_of_forall_mem_fixedPoints {Q : Subgroup (MulAut V)}
    (h : ∀ v : V, v ∈ fixedPoints Q V) : Q = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  rw [mem_bot]
  exact eq_one_of_forall_apply_eq fun v => mem_fixedPoints.mp (h v) ⟨q, hq⟩

theorem eq_univ_of_ncard_eq [Finite V] {s : Set V} (h : s.ncard = Nat.card V) : s = Set.univ := by
  by_contra hs
  exact (Set.ncard_lt_card hs).ne h

theorem card_dvd_ncard_of_free {H X : Type*} [Group H] [Finite H] [MulAction H X] {S : Set X}
    (hSf : S.Finite) (hS : ∀ h : H, ∀ x ∈ S, h • x ∈ S)
    (hfree : ∀ h : H, ∀ x ∈ S, h • x = x → h = 1) : Nat.card H ∣ S.ncard := by
  classical
  let T : SubMulAction H X := ⟨S, fun {h x} hx => hS h x hx⟩
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Finite T := hSf.to_subtype
  haveI : Fintype T := Fintype.ofFinite T
  haveI : ∀ h : H, Fintype (fixedBy T h) := fun h => Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel H T)) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H T
  have hsum : ∑ h : H, Fintype.card (fixedBy T h) = Fintype.card T := by
    rw [Finset.sum_eq_single (1 : H)]
    · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, fixedBy_one_eq_univ,
        Nat.card_univ]
    · intro h _ h1
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨x, hx⟩ => h1 (hfree h x x.2 ?_)⟩
      exact congrArg Subtype.val hx
    · intro h
      exact absurd (Finset.mem_univ 1) h
  rw [hsum] at hB
  have hT : Fintype.card T = S.ncard := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    rfl
  rw [← hT, hB, Nat.card_eq_fintype_card]
  exact dvd_mul_left _ _

theorem ncard_modEq_ncard_inter_fixedPoints {P X : Type*} [Group P] [MulAction P X] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) {O : Set X} (hOf : O.Finite)
    (hO : ∀ g : P, ∀ x ∈ O, g • x ∈ O) : O.ncard ≡ (O ∩ fixedPoints P X).ncard [MOD p] := by
  let T : SubMulAction P X := ⟨O, fun {g x} hx => hO g x hx⟩
  haveI : Finite T := hOf.to_subtype
  have h := hP.card_modEq_card_fixedPoints T
  have e1 : Nat.card T = O.ncard := rfl
  have e2 : Nat.card (fixedPoints P T) = (O ∩ fixedPoints P X).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, fun g => congrArg Subtype.val (x.2 g)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun g => Subtype.ext (x.2.2 g)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  rw [e1, e2] at h
  exact h

theorem fixedPoints_stabilizer_map {Q : Subgroup (MulAut V)} (v : V) :
    fixedPoints Q V ∪ {v} ⊆ fixedPoints ((stabilizer Q v).map Q.subtype) V := by
  rintro w (hw | hw)
  · rw [mem_fixedPoints] at hw ⊢
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hs
    exact hw t
  · rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [mem_fixedPoints]
    rintro ⟨s, hs⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
    exact ht

theorem card_stabilizer_mul_ncard_orbit {H X : Type*} [Group H] [MulAction H X] (x : X) :
    Nat.card (stabilizer H x) * (orbit H x).ncard = Nat.card H := by
  rw [← index_stabilizer]
  exact card_mul_index _

theorem orbit_subset_compl_fixedPoints {H X : Type*} [Group H] [MulAction H X] {x : X}
    (hx : x ∉ fixedPoints H X) : orbit H x ⊆ (fixedPoints H X)ᶜ := by
  intro w hw hwF
  obtain ⟨h, rfl⟩ := mem_orbit_iff.mp hw
  apply hx
  rw [mem_fixedPoints] at hwF ⊢
  have hx' : h • x = x := by
    have := hwF h⁻¹
    rw [inv_smul_smul] at this
    exact this.symm
  intro k
  have := hwF k
  rwa [hx'] at this

theorem exists_orderOf_eq_prime [Finite V] {Q : Subgroup (MulAut V)} (hodd : Odd (Nat.card Q))
    {r : ℕ} (hr : r.Prime) (hrd : r ∣ Nat.card Q) :
    ∃ g ∈ Q, orderOf g = r ∧ r ≠ 2 ∧ fixedPoints Q V ⊆ fixedBy V g := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) r hrd
  have hr2 : r ≠ 2 := fun h => by
    rw [h] at hrd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx, hr2, fun w hw => (mem_fixedPoints.mp hw) x⟩

theorem smul_mem_compl_fixedPoints {H X : Type*} [Group H] [MulAction H X] (h : H) {x : X}
    (hx : x ∈ (fixedPoints H X)ᶜ) : h • x ∈ (fixedPoints H X)ᶜ := by
  intro hhx
  apply hx
  rw [mem_fixedPoints] at hhx ⊢
  have hx' : h • x = x := by
    have := hhx h⁻¹
    rw [inv_smul_smul] at this
    exact this.symm
  intro k
  have := hhx k
  rwa [hx'] at this

theorem fixedBy_subset_fixedBy_npow (g : MulAut V) (m : ℕ) : fixedBy V g ⊆ fixedBy V (g ^ m) :=
  fun v hv => by
    have := mem_fixedBy_zpow (α := V) hv (m : ℤ)
    rwa [zpow_natCast] at this

theorem exists_pow_orderOf_eq_prime {G : Type*} [Group G] [Finite G] {g : G} (hg : g ≠ 1)
    {p : ℕ} (hpg : ∃ k, orderOf g = p ^ k) : ∃ m : ℕ, orderOf (g ^ m) = p := by
  obtain ⟨k, hk⟩ := hpg
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hg (orderOf_eq_one_iff.mp hk)
  refine ⟨orderOf g / p, orderOf_pow_orderOf_div (orderOf_pos g).ne' ?_⟩
  rw [hk]
  exact dvd_pow_self p hk0

theorem smul_eq_of_odd_of_ncard_le_two {H X : Type*} [Group H] [Finite H] [MulAction H X]
    (hodd : Odd (Nat.card H)) {O : Set X} (hOf : O.Finite) (hO : ∀ h : H, ∀ x ∈ O, h • x ∈ O)
    (h2 : O.ncard ≤ 2) : ∀ h : H, ∀ x ∈ O, h • x = x := by
  intro h x hx
  have hsub : orbit H x ⊆ O := by
    rintro w ⟨k, rfl⟩
    exact hO k x hx
  have hle : (orbit H x).ncard ≤ 2 := (Set.ncard_le_ncard hsub hOf).trans h2
  have hos := card_stabilizer_mul_ncard_orbit (H := H) x
  have hoddO : Odd (orbit H x).ncard := hodd.of_dvd_nat ⟨_, by rw [← hos, mul_comm]⟩
  have hpos : 0 < (orbit H x).ncard :=
    (Set.ncard_pos (hOf.subset hsub)).mpr ⟨x, mem_orbit_self x⟩
  have h1 : (orbit H x).ncard = 1 := by
    obtain ⟨j, hj⟩ := hoddO
    omega
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
  have hxa : x = a := by
    have := mem_orbit_self (M := H) x
    rw [ha] at this
    exact this
  have hha : h • x = a := by
    have : h • x ∈ orbit H x := mem_orbit x h
    rw [ha] at this
    exact this
  rw [hha, hxa]

theorem card_sylow_eq_of_card {G : Type*} [Group G] [Finite G] {p k m : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) (hG : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m) :
    Nat.card P = p ^ k ∧ (P : Subgroup G).index = m := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have hcard : Nat.card P = p ^ k := by
    rw [P.card_eq_multiplicity, hG, Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) hm0,
      Finsupp.add_apply, hp.out.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  refine ⟨hcard, ?_⟩
  have := (P : Subgroup G).card_mul_index
  rw [hcard, hG] at this
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos k) this

theorem sylow_normal_of_card {G : Type*} [Group G] [Finite G] {p k m : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) (hG : Nat.card G = p ^ k * m) (hm : ¬ p ∣ m)
    (h : ∀ n, n ∣ m → n % p = 1 → n = 1) : (P : Subgroup G).Normal := by
  have h1 := card_sylow_modEq_one p G
  have h2 := P.card_dvd_index
  rw [(card_sylow_eq_of_card P hG hm).2] at h2
  have hn : Nat.card (Sylow p G) = 1 := by
    refine h _ h2 ?_
    rw [Nat.ModEq] at h1
    rw [h1, Nat.one_mod_eq_one.mpr hp.out.ne_one]
  haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hn).1
  exact Sylow.normal_of_subsingleton P

theorem exists_subgroup_card_eq_of_isSolvable {G : Type*} [Group G] [Finite G]
    (hG : Group.IsSolvable G) {d : ℕ} (hd : d ∣ Nat.card G)
    (hcop : Nat.Coprime d (Nat.card G / d)) : ∃ H : Subgroup G, Nat.card H = d := by
  obtain ⟨e, he⟩ := hd
  have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_mul] at he
    exact hG0 he
  have he' : Nat.card G / d = e := by
    rw [he, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  rw [he'] at hcop
  obtain ⟨H, hH⟩ := SolvableHall.solvable_hall_existence hG {p : Nat.Primes | (p : ℕ) ∣ d}
  have hcard : Nat.card H * H.index = d * e := by rw [H.card_mul_index, he]
  have h1 : Nat.Coprime (Nat.card H) e := Nat.coprime_of_dvd fun p hp hpH hpe => by
    have hpd : (p : ℕ) ∣ d := hH.p_in_pi_of_p_dvd_card ⟨p, hp⟩ hpH
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpd hcop) hpe)
  have h2 : Nat.Coprime H.index d := Nat.coprime_of_dvd fun p hp hpi hpd =>
    hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpi hpd
  have hHd : Nat.card H ∣ d := h1.dvd_of_dvd_mul_right ⟨H.index, hcard.symm⟩
  have hie : H.index ∣ e :=
    h2.dvd_of_dvd_mul_left ⟨Nat.card H, by rw [← hcard, mul_comm]⟩
  obtain ⟨s, hs⟩ := hHd
  obtain ⟨t, ht⟩ := hie
  have hpos : 0 < Nat.card H * H.index := by
    rw [hcard]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hd0) (Nat.pos_of_ne_zero (by
      rintro rfl
      rw [mul_zero] at he
      exact hG0 he))
  have hst : s * t = 1 := by
    have : Nat.card H * H.index * (s * t) = Nat.card H * H.index * 1 := by
      calc Nat.card H * H.index * (s * t) = (Nat.card H * s) * (H.index * t) := by ring
        _ = d * e := by rw [← hs, ← ht]
        _ = Nat.card H * H.index * 1 := by rw [mul_one, hcard]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hs1 : s = 1 := Nat.eq_one_of_mul_eq_one_right hst
  rw [hs1, mul_one] at hs
  exact ⟨H, hs.symm⟩

theorem le_normalizer_map_of_normal {G : Type*} [Group G] {H : Subgroup G} {N : Subgroup H}
    (hN : N.Normal) : H ≤ normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  have h : (N.map H.subtype).subgroupOf H = N :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer (map_subtype_le N), h]
  exact hN

theorem exists_mul_eq_of_inf_eq_bot [Finite V] {X Y : Subgroup V} (hXY : X ⊓ Y = ⊥)
    (hcard : Nat.card X * Nat.card Y = Nat.card V) (v : V) : ∃ x ∈ X, ∃ y ∈ Y, x * y = v := by
  let f : X × Y → V := fun p => (p.1 : V) * p.2
  have hinj : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    change (x : V) * y = x' * y' at h
    have hmem : (x' : V)⁻¹ * x ∈ X ⊓ Y := by
      refine ⟨X.mul_mem (X.inv_mem x'.2) x.2, ?_⟩
      have : (x' : V)⁻¹ * x = y' * (y : V)⁻¹ := by
        calc (x' : V)⁻¹ * x = (x' : V)⁻¹ * (x * y) * (y : V)⁻¹ := by group
          _ = y' * (y : V)⁻¹ := by rw [h]; group
      rw [this]
      exact Y.mul_mem y'.2 (Y.inv_mem y.2)
    rw [hXY, mem_bot, inv_mul_eq_one] at hmem
    have hy : (y : V) = y' := by
      rw [hmem] at h
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hy)
  obtain ⟨⟨x, y⟩, hxy⟩ := (hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, hcard])).2 v
  exact ⟨x, x.2, y, y.2, hxy⟩

theorem eq_of_mul_eq_mul_of_inf_eq_bot {X Y : Subgroup V} (hXY : X ⊓ Y = ⊥) {x x' y y' : V}
    (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y) (h : x * y = x' * y') :
    x = x' ∧ y = y' := by
  have hmem : x'⁻¹ * x ∈ X ⊓ Y := by
    refine ⟨X.mul_mem (X.inv_mem hx') hx, ?_⟩
    have : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = y' * y⁻¹ := by rw [h]; group
    rw [this]
    exact Y.mul_mem hy' (Y.inv_mem hy)
  rw [hXY, mem_bot, inv_mul_eq_one] at hmem
  refine ⟨hmem.symm, ?_⟩
  rw [hmem] at h
  exact mul_left_cancel h

theorem mul_ncard_le_of_orbits {H X : Type*} [Group H] [MulAction H X] [Finite X] {S T : Set X}
    (m : ℕ) (hS : ∀ s ∈ S, ∀ s' ∈ S, s' ∈ orbit H s → s = s')
    (hST : ∀ s ∈ S, orbit H s ⊆ T) (hm : ∀ s ∈ S, m ≤ (orbit H s).ncard) :
    m * S.ncard ≤ T.ncard := by
  classical
  haveI := Fintype.ofFinite X
  have hdisj : (S.toFinset : Set X).PairwiseDisjoint (fun s => (orbit H s).toFinset) := by
    intro s hs s' hs' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    rw [Finset.mem_coe, Set.mem_toFinset] at hs hs'
    rw [Set.mem_toFinset] at hw hw'
    apply hne
    have e₁ : orbit H w = orbit H s := orbit_eq_iff.mpr hw
    have e₂ : orbit H w = orbit H s' := orbit_eq_iff.mpr hw'
    exact hS s hs s' hs' (by rw [← e₁, e₂]; exact mem_orbit_self s')
  have hcard := Finset.card_biUnion hdisj
  have hsub : S.toFinset.biUnion (fun s => (orbit H s).toFinset) ⊆ T.toFinset := by
    intro w hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨s, hs, hws⟩ := hw
    rw [Set.mem_toFinset] at hs hws ⊢
    exact hST s hs hws
  have hle := Finset.card_le_card hsub
  have hsum : m * S.toFinset.card ≤ ∑ s ∈ S.toFinset, (orbit H s).toFinset.card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun s hs => by
      rw [← Set.ncard_eq_toFinset_card']
      exact hm s (Set.mem_toFinset.mp hs)
  rw [Set.ncard_eq_toFinset_card' S, Set.ncard_eq_toFinset_card' T]
  omega

theorem three_le_ncard_orbit {H X : Type*} [Group H] [Finite H] [MulAction H X]
    (hodd : Odd (Nat.card H)) {x : X} (hx : x ∉ fixedPoints H X) : 3 ≤ (orbit H x).ncard := by
  have hos := card_stabilizer_mul_ncard_orbit (H := H) x
  have hoddO : Odd (orbit H x).ncard := hodd.of_dvd_nat ⟨_, by rw [← hos, mul_comm]⟩
  have hfin : (orbit H x).Finite := Set.finite_range _
  have hpos : 0 < (orbit H x).ncard := (Set.ncard_pos hfin).mpr ⟨x, mem_orbit_self x⟩
  have hne : (orbit H x).ncard ≠ 1 := by
    intro h1
    apply hx
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    rw [mem_fixedPoints]
    intro h
    have h₁ : h • x ∈ orbit H x := mem_orbit x h
    have h₂ : x ∈ orbit H x := mem_orbit_self x
    rw [ha] at h₁ h₂
    exact h₁.trans h₂.symm
  obtain ⟨j, hj⟩ := hoddO
  omega

end Generic

theorem eq_of_dvd_sixteen {n : ℕ} (h : n ∣ 16) : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 := by
  have : n ≤ 16 := Nat.le_of_dvd (by norm_num) h
  interval_cases n <;> first | omega | (norm_num at h)

section Sixteen

variable {V : Type*} [Group V] [Finite V] (h16 : Nat.card V = 16)
include h16

theorem card_fixedBy_cases_of_prime {g : MulAut V} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hg : orderOf g = r) :
    (Nat.card (fixedBy V g) = 1 ∧ (r = 3 ∨ r = 5)) ∨ (Nat.card (fixedBy V g) = 2 ∧ r = 7) ∨
      (Nat.card (fixedBy V g) = 4 ∧ r = 3) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hP : IsPGroup r (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hP.card_modEq_card_fixedPoints V
  rw [fixedPoints_zpowers, h16] at hmod
  have hdvd := card_fixedBy_dvd g
  rw [h16] at hdvd
  have hne : Nat.card (fixedBy V g) ≠ 16 := by
    intro h
    have huniv : fixedBy V g = Set.univ :=
      eq_univ_of_ncard_eq (by rw [← Nat.card_coe_set_eq, h, h16])
    have h1 : g = 1 := eq_one_of_forall_apply_eq fun v => by
      have hv : v ∈ fixedBy V g := huniv ▸ Set.mem_univ v
      exact hv
    rw [h1, orderOf_one] at hg
    exact hr.one_lt.ne' hg.symm
  have hle : Nat.card (fixedBy V g) ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have key : r ∣ 16 - Nat.card (fixedBy V g) := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  rcases eq_of_dvd_sixteen hdvd with hc | hc | hc | hc | hc
  · left
    refine ⟨hc, ?_⟩
    rw [hc] at key
    have hr15 : r ≤ 15 := Nat.le_of_dvd (by norm_num) key
    interval_cases r <;> first | omega | (norm_num at hr) | (norm_num at key)
  · right; left
    refine ⟨hc, ?_⟩
    rw [hc] at key
    have hr14 : r ≤ 14 := Nat.le_of_dvd (by norm_num) key
    interval_cases r <;> first | omega | (norm_num at hr) | (norm_num at key)
  · right; right
    refine ⟨hc, ?_⟩
    rw [hc] at key
    have hr12 : r ≤ 12 := Nat.le_of_dvd (by norm_num) key
    interval_cases r <;> first | omega | (norm_num at hr) | (norm_num at key)
  · exfalso
    rw [hc] at key
    have hr8 : r ≤ 8 := Nat.le_of_dvd (by norm_num) key
    interval_cases r <;> first | omega | (norm_num at hr) | (norm_num at key)
  · exact absurd hc hne


theorem card_fixedBy_le_four {g : MulAut V} (hg1 : g ≠ 1) (hodd : Odd (orderOf g)) :
    Nat.card (fixedBy V g) ≤ 4 := by
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hne1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne1
  have hr2 : r ≠ 2 := fun h => by
    rw [h] at hrd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrd)
  have hg' : orderOf (g ^ (orderOf g / r)) = r := orderOf_pow_orderOf_div hpos hrd
  have hsub : fixedBy V g ⊆ fixedBy V (g ^ (orderOf g / r)) := fun v hv => by
    have := mem_fixedBy_zpow (α := V) hv ((orderOf g / r : ℕ) : ℤ)
    rwa [zpow_natCast] at this
  have hle : (fixedBy V g).ncard ≤ (fixedBy V (g ^ (orderOf g / r))).ncard :=
    Set.ncard_le_ncard hsub
  rw [Nat.card_coe_set_eq]
  rcases card_fixedBy_cases_of_prime h16 hr hr2 hg' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    · rw [Nat.card_coe_set_eq] at h
      omega

theorem card_dvd_three_of_four_le {Q : Subgroup (MulAut V)} (hodd : Odd (Nat.card Q))
    (h4 : 4 ≤ Nat.card (fixedPoints Q V)) :
    Nat.card Q ∣ 3 ∧ (Q ≠ ⊥ → Nat.card (fixedPoints Q V) = 4 ∧
      ∀ q ∈ Q, q ≠ 1 → fixedBy V q = fixedPoints Q V) := by
  have hq : ∀ q ∈ Q, q ≠ 1 →
      fixedBy V q = fixedPoints Q V ∧ Nat.card (fixedPoints Q V) = 4 := by
    intro q hq hq1
    have hoddq : Odd (orderOf q) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Q hq)
    have hsub : fixedPoints Q V ⊆ fixedBy V q := fun v hv => (mem_fixedPoints.mp hv) ⟨q, hq⟩
    have hle := card_fixedBy_le_four h16 hq1 hoddq
    rw [Nat.card_coe_set_eq] at hle h4 ⊢
    have hle' := Set.ncard_le_ncard hsub
    have heq : fixedPoints Q V = fixedBy V q := Set.eq_of_subset_of_ncard_le hsub (by omega)
    exact ⟨heq.symm, by omega⟩
  by_cases hQ : Q = ⊥
  · refine ⟨by rw [hQ, card_bot]; exact one_dvd 3, fun h => absurd hQ h⟩
  obtain ⟨⟨q, hqQ⟩, hq1⟩ := Q.ne_bot_iff_exists_ne_one.mp hQ
  have hq1' : q ≠ 1 := fun h => hq1 (Subtype.ext h)
  obtain ⟨-, h4'⟩ := hq q hqQ hq1'
  refine ⟨?_, fun _ => ⟨h4', fun q' hq' hq1'' => (hq q' hq' hq1'').1⟩⟩
  have hinv : ∀ h : Q, ∀ x ∈ (fixedPoints Q V)ᶜ, h • x ∈ (fixedPoints Q V)ᶜ := by
    intro h x hx hhx
    apply hx
    rw [mem_fixedPoints] at hhx ⊢
    have hx' : h • x = x := by
      have := hhx h⁻¹
      rw [inv_smul_smul] at this
      exact this.symm
    intro k
    have := hhx k
    rwa [hx'] at this
  have hfree : ∀ h : Q, ∀ x ∈ (fixedPoints Q V)ᶜ, h • x = x → h = 1 := by
    intro h x hx hhx
    by_contra hh1
    have hh1' : (h : MulAut V) ≠ 1 := fun e => hh1 (Subtype.ext e)
    have := (hq h h.2 hh1').1
    apply hx
    rw [← this]
    exact hhx
  have hdvd := card_dvd_ncard_of_free (Set.toFinite _) hinv hfree
  rw [Set.ncard_compl, h16, ← Nat.card_coe_set_eq, h4'] at hdvd
  have hle : Nat.card Q ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  have hoddQ := hodd
  interval_cases (Nat.card Q) <;>
    first | omega | exact absurd hoddQ (by decide) | exact absurd hdvd (by decide)

theorem ncard_compl_one : ({1}ᶜ : Set V).ncard = 15 := by
  rw [Set.ncard_compl, h16, Set.ncard_singleton]

theorem eq_one_of_mem_fixedBy_of_card_eq_one {g : MulAut V} (hg : Nat.card (fixedBy V g) = 1)
    {v : V} (hv : v ∈ fixedBy V g) : v = 1 := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (by rwa [← Nat.card_coe_set_eq])
  have h1 : (1 : V) ∈ fixedBy V g := by rw [mem_fixedBy, MulAut.smul_def, map_one]
  rw [ha] at hv h1
  exact hv.trans h1.symm

theorem card_dvd_five_of_isPGroup {Q : Subgroup (MulAut V)} (hP : IsPGroup 5 Q) :
    Nat.card Q ∣ 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hinv : ∀ q : Q, ∀ v ∈ ({1}ᶜ : Set V), q • v ∈ ({1}ᶜ : Set V) := by
    intro q v hv hqv
    apply hv
    have : (q : MulAut V) v = (q : MulAut V) 1 := by
      rw [map_one]
      exact hqv
    exact (q : MulAut V).injective this
  have hfree : ∀ q : Q, ∀ v ∈ ({1}ᶜ : Set V), q • v = v → q = 1 := by
    intro q v hv hqv
    by_contra hq1
    have hq1' : (q : MulAut V) ≠ 1 := fun h => hq1 (Subtype.ext h)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) q
    obtain ⟨m, hm⟩ := exists_pow_orderOf_eq_prime hq1' ⟨k, (Subgroup.orderOf_coe q).trans hk⟩
    have hv' : v ∈ fixedBy V ((q : MulAut V) ^ m) := fixedBy_subset_fixedBy_npow _ m hqv
    rcases card_fixedBy_cases_of_prime h16 (by norm_num) (by norm_num) hm with
      ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact hv (eq_one_of_mem_fixedBy_of_card_eq_one h16 h hv')
    · norm_num at h
    · norm_num at h
  have hdvd := card_dvd_ncard_of_free (Set.toFinite _) hinv hfree
  rw [ncard_compl_one h16] at hdvd
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn] at hdvd ⊢
  have hle : 5 ^ n ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
  have hn1 : n ≤ 1 := by
    by_contra h
    have : 5 ^ 2 ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> norm_num

theorem card_fixedPoints_eq_two_of_isPGroup {Q : Subgroup (MulAut V)} (hP : IsPGroup 7 Q)
    (hQ : Q ≠ ⊥) : Nat.card (fixedPoints Q V) = 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := hP.card_modEq_card_fixedPoints V
  rw [h16] at hmod
  have hdvd := card_fixedPoints_dvd Q
  rw [h16] at hdvd
  rcases eq_of_dvd_sixteen hdvd with h | h | h | h | h <;> rw [h] at hmod ⊢
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · exfalso
    apply hQ
    apply eq_bot_of_forall_mem_fixedPoints
    intro v
    have huniv : fixedPoints Q V = Set.univ :=
      eq_univ_of_ncard_eq (by rw [← Nat.card_coe_set_eq, h, h16])
    rw [huniv]
    exact Set.mem_univ v

theorem card_dvd_seven_of_isPGroup {Q : Subgroup (MulAut V)} (hP : IsPGroup 7 Q) :
    Nat.card Q ∣ 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_cases hQ : Q = ⊥
  · rw [hQ, card_bot]
    exact one_dvd _
  have hF2 := card_fixedPoints_eq_two_of_isPGroup h16 hP hQ
  have hfree : ∀ q : Q, ∀ v ∈ (fixedPoints Q V)ᶜ, q • v = v → q = 1 := by
    intro q v hv hqv
    by_contra hq1
    have hq1' : (q : MulAut V) ≠ 1 := fun h => hq1 (Subtype.ext h)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) q
    obtain ⟨m, hm⟩ := exists_pow_orderOf_eq_prime hq1' ⟨k, (Subgroup.orderOf_coe q).trans hk⟩
    have hsub : fixedPoints Q V ∪ {v} ⊆ fixedBy V ((q : MulAut V) ^ m) := by
      rintro w (hw | hw)
      · exact fixedBy_subset_fixedBy_npow _ m ((mem_fixedPoints.mp hw) q)
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        exact fixedBy_subset_fixedBy_npow _ m hqv
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hv), Set.ncard_singleton,
      ← Nat.card_coe_set_eq, hF2, ← Nat.card_coe_set_eq] at hle
    rcases card_fixedBy_cases_of_prime h16 (by norm_num) (by norm_num) hm with
      ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · norm_num at h
    · omega
    · norm_num at h
  have hdvd := card_dvd_ncard_of_free (Set.toFinite _)
    (fun q x hx => smul_mem_compl_fixedPoints q hx)
    hfree
  rw [Set.ncard_compl, h16, ← Nat.card_coe_set_eq, hF2] at hdvd
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  rw [hn] at hdvd ⊢
  have hle : 7 ^ n ≤ 14 := Nat.le_of_dvd (by norm_num) hdvd
  have hn1 : n ≤ 1 := by
    by_contra h
    have : 7 ^ 2 ≤ 7 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n <;> norm_num

theorem four_le_card_fixedPoints_of_isPGroup {Q : Subgroup (MulAut V)} (hP : IsPGroup 3 Q)
    {v : V} (hv : v ≠ 1) (hvQ : v ∈ fixedPoints Q V) : 4 ≤ Nat.card (fixedPoints Q V) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := hP.card_modEq_card_fixedPoints V
  rw [h16] at hmod
  have hdvd := card_fixedPoints_dvd Q
  rw [h16] at hdvd
  have h2 : 2 ≤ Nat.card (fixedPoints Q V) := by
    have h1 : (1 : V) ∈ fixedPoints Q V := by
      rw [mem_fixedPoints]
      intro q
      change (q : MulAut V) 1 = 1
      rw [map_one]
    have hsub : ({1, v} : Set V) ⊆ fixedPoints Q V := by
      rintro w (rfl | hw)
      · exact h1
      · rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hvQ
    have := Set.ncard_le_ncard hsub
    rwa [Set.ncard_pair (Ne.symm hv), ← Nat.card_coe_set_eq] at this
  rcases eq_of_dvd_sixteen hdvd with h | h | h | h | h <;> rw [h] at hmod h2 ⊢ <;>
    first | omega | exact absurd hmod (by decide)

theorem card_dvd_nine_of_isPGroup {Q : Subgroup (MulAut V)} (hP : IsPGroup 3 Q) :
    Nat.card Q ∣ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hodd : Odd (Nat.card Q) := by
    rw [hn]
    exact Odd.pow (by decide)
  by_contra h9
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> norm_num [hn] at h9
  have hstab : ∀ v : V, v ≠ 1 → Nat.card (stabilizer Q v) ∣ 3 := by
    intro v hv
    set S : Subgroup (MulAut V) := (stabilizer Q v).map Q.subtype with hS
    have hSc : Nat.card S = Nat.card (stabilizer Q v) :=
      card_map_of_injective Q.subtype_injective
    have hSp : IsPGroup 3 S := (hP.to_subgroup (stabilizer Q v)).map Q.subtype
    have hvS : v ∈ fixedPoints S V :=
      fixedPoints_stabilizer_map (Q := Q) v (Set.mem_union_right _ rfl)
    have hSodd : Odd (Nat.card S) := hSc ▸ hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
    rw [← hSc]
    exact (card_dvd_three_of_four_le h16 hSodd
      (four_le_card_fixedPoints_of_isPGroup h16 hSp hv hvS)).1
  have horb : ∀ v : V, v ≠ 1 → (orbit Q v).ncard = 9 ∧ orbit Q v ⊆ {1}ᶜ := by
    intro v hv
    have hsub : orbit Q v ⊆ {1}ᶜ := by
      rintro w ⟨q, rfl⟩ hw
      apply hv
      have : (q : MulAut V) v = (q : MulAut V) 1 := by
        rw [map_one]
        exact hw
      exact (q : MulAut V).injective this
    refine ⟨?_, hsub⟩
    have hos := card_stabilizer_mul_ncard_orbit (H := Q) v
    have hle : (orbit Q v).ncard ≤ 15 := by
      have := Set.ncard_le_ncard hsub
      rwa [ncard_compl_one h16] at this
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (⟨_, by rw [hn] at hos; rw [← hos, mul_comm]⟩ : (orbit Q v).ncard ∣ 3 ^ n)
    have h3 := hstab v hv
    have hS : Nat.card (stabilizer Q v) ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    have hge : 9 ≤ (orbit Q v).ncard := by
      by_contra hlt
      push Not at hlt
      have : Nat.card (stabilizer Q v) * (orbit Q v).ncard < 27 := by
        calc Nat.card (stabilizer Q v) * (orbit Q v).ncard ≤ 3 * 8 :=
              Nat.mul_le_mul hS (by omega)
          _ < 27 := by norm_num
      rw [hos, hn] at this
      have : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
      omega
    rw [hjeq] at hle hge ⊢
    have hj2 : j = 2 := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j <;> norm_num at hge
      · rcases Nat.lt_or_ge j 3 with h' | h'
        · omega
        · have : 3 ^ 3 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h'
          omega
    rw [hj2]
    norm_num
  obtain ⟨v₁, hv₁⟩ : ∃ v : V, v ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card V = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  obtain ⟨h₁, hs₁⟩ := horb v₁ hv₁
  have hrest : (({1}ᶜ : Set V) \ orbit Q v₁).ncard = 6 := by
    rw [Set.ncard_diff hs₁, ncard_compl_one h16, h₁]
  obtain ⟨v₂, hv₂, hv₂O⟩ : ∃ v, v ∈ ({1}ᶜ : Set V) ∧ v ∉ orbit Q v₁ := by
    obtain ⟨v, hv⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 <
      (({1}ᶜ : Set V) \ orbit Q v₁).ncard)
    exact ⟨v, hv.1, hv.2⟩
  obtain ⟨h₂, hs₂⟩ := horb v₂ hv₂
  have hsub : orbit Q v₂ ⊆ ({1}ᶜ : Set V) \ orbit Q v₁ := by
    intro w hw
    refine ⟨hs₂ hw, fun hw₁ => hv₂O ?_⟩
    have e₁ : orbit Q w = orbit Q v₁ := orbit_eq_iff.mpr hw₁
    have e₂ : orbit Q w = orbit Q v₂ := orbit_eq_iff.mpr hw
    rw [← e₁, e₂]
    exact mem_orbit_self v₂
  have := Set.ncard_le_ncard hsub
  omega


theorem false_of_commute_of_orderOf_five {g k : MulAut V} (hg : orderOf g = 5)
    (hgk : Commute g k) {v : V} (hv : v ≠ 1) (hkv : k v = v)
    (hk4 : Nat.card (fixedBy V k) ≤ 4) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hg1 : Nat.card (fixedBy V g) = 1 := by
    rcases card_fixedBy_cases_of_prime h16 (by norm_num) (by norm_num) hg with
      ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · norm_num at h
    · norm_num at h
  set O : Set V := fixedBy V k \ {1} with hO
  have hP : IsPGroup 5 (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hinv : ∀ q : zpowers g, ∀ w ∈ O, q • w ∈ O := by
    rintro ⟨q, hq⟩ w ⟨hwk, hw1⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hq
    have hc : (g ^ n) * k = k * (g ^ n) := (hgk.zpow_left n).eq
    refine ⟨?_, ?_⟩
    · change (g ^ n) w ∈ fixedBy V k
      rw [mem_fixedBy, MulAut.smul_def] at hwk ⊢
      have := congrArg (fun f : MulAut V => f w) hc
      simp only [MulAut.mul_apply] at this
      rw [← this, hwk]
    · intro h1
      apply hw1
      have : (g ^ n) w = (g ^ n) 1 := by
        rw [map_one]
        exact h1
      exact (g ^ n).injective this
  have hmod := ncard_modEq_ncard_inter_fixedPoints hP (Set.toFinite O) hinv
  rw [fixedPoints_zpowers] at hmod
  have hempty : O ∩ fixedBy V g = ∅ := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨-, hw1⟩ hwg
    exact hw1 (eq_one_of_mem_fixedBy_of_card_eq_one h16 hg1 hwg)
  rw [hempty, Set.ncard_empty] at hmod
  have hOpos : 0 < O.ncard := (Set.ncard_pos (Set.toFinite O)).mpr ⟨v, hkv, hv⟩
  have h1k : (1 : V) ∈ fixedBy V k := by rw [mem_fixedBy, MulAut.smul_def, map_one]
  have hOle : O.ncard ≤ 3 := by
    rw [hO, Set.ncard_diff (Set.singleton_subset_iff.mpr h1k), Set.ncard_singleton,
      ← Nat.card_coe_set_eq]
    omega
  have h5 := Nat.modEq_zero_iff_dvd.mp hmod
  have := Nat.le_of_dvd hOpos h5
  omega

theorem apply_eq_of_le_normalizer_of_isPGroup_seven {H P : Subgroup (MulAut V)}
    (hP : IsPGroup 7 P) (hP1 : P ≠ ⊥) (hHP : H ≤ normalizer (P : Set (MulAut V))) {z : V}
    (hz : z ∈ fixedPoints P V) (hz1 : z ≠ 1) : ∀ h ∈ H, h z = z := by
  intro h hh
  have hF2 := card_fixedPoints_eq_two_of_isPGroup h16 hP hP1
  have hmem : h z ∈ fixedPoints P V := by
    rw [mem_fixedPoints]
    rintro ⟨t, ht⟩
    have hconj : h⁻¹ * t * h ∈ P := by
      have := (mem_normalizer_iff.mp (inv_mem (hHP hh)) t).mp ht
      rwa [inv_inv] at this
    have hzt := (mem_fixedPoints.mp hz) ⟨h⁻¹ * t * h, hconj⟩
    change h⁻¹ (t (h z)) = z at hzt
    change t (h z) = h z
    calc t (h z) = (h * h⁻¹) (t (h z)) := by rw [mul_inv_cancel, MulAut.one_apply]
      _ = h (h⁻¹ (t (h z))) := rfl
      _ = h z := by rw [hzt]
  have hne : h z ≠ 1 := by
    intro h1
    apply hz1
    have : h z = h 1 := by
      rw [map_one]
      exact h1
    exact h.injective this
  have hsub : ({1, z} : Set V) ⊆ fixedPoints P V := by
    rintro w (rfl | hw)
    · rw [mem_fixedPoints]
      intro s
      change (s : MulAut V) 1 = 1
      rw [map_one]
    · rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact hz
  have heq : ({1, z} : Set V) = fixedPoints P V :=
    Set.eq_of_subset_of_ncard_le hsub (by
      rw [← Nat.card_coe_set_eq, hF2, Set.ncard_pair (Ne.symm hz1)])
  rw [← heq] at hmem
  rcases hmem with h1 | h2
  · exact absurd h1 hne
  · exact h2

theorem not_card_eq_thirtyFive {H : Subgroup (MulAut V)} (hH : Nat.card H = 35) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P₅⟩ := (inferInstance : Nonempty (Sylow 5 H))
  obtain ⟨P₇⟩ := (inferInstance : Nonempty (Sylow 7 H))
  have hG₅ : Nat.card H = 5 ^ 1 * 7 := by rw [hH]; norm_num
  have hG₇ : Nat.card H = 7 ^ 1 * 5 := by rw [hH]; norm_num
  have hn₅ := sylow_normal_of_card P₅ hG₅ (by norm_num) fun n hn h => by
    have : n ≤ 7 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hn₇ := sylow_normal_of_card P₇ hG₇ (by norm_num) fun n hn h => by
    have : n ≤ 5 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hc₅ := (card_sylow_eq_of_card P₅ hG₅ (by norm_num)).1
  have hc₇ := (card_sylow_eq_of_card P₇ hG₇ (by norm_num)).1
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := (P₅ : Subgroup H)) 5 (by rw [hc₅]; norm_num)
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card' (G := (P₇ : Subgroup H)) 7 (by rw [hc₇]; norm_num)
  have hcomm : Commute ((x : H) : MulAut V) ((y : H) : MulAut V) :=
    (Subgroup.commute_of_normal_of_disjoint _ _ hn₅ hn₇
      (IsPGroup.disjoint_of_coprime P₅.isPGroup' P₇.isPGroup' (by norm_num)) _ _ x.2 y.2).map
      H.subtype
  have hx5 : orderOf ((x : H) : MulAut V) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hy7 : orderOf ((y : H) : MulAut V) = 7 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  have hy2 : Nat.card (fixedBy V ((y : H) : MulAut V)) = 2 := by
    rcases card_fixedBy_cases_of_prime h16 (by norm_num) (by norm_num) hy7 with
      ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> first | exact h | norm_num at h
  obtain ⟨v, hv, hv1⟩ := Set.exists_ne_of_one_lt_ncard
    (by rw [← Nat.card_coe_set_eq, hy2]; norm_num : 1 < (fixedBy V ((y : H) : MulAut V)).ncard) 1
  exact false_of_commute_of_orderOf_five h16 hx5 hcomm hv1 hv (by omega)

theorem not_card_eq_fortyFive {H : Subgroup (MulAut V)} (hH : Nat.card H = 45) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₅⟩ := (inferInstance : Nonempty (Sylow 5 H))
  obtain ⟨P₃⟩ := (inferInstance : Nonempty (Sylow 3 H))
  have hG₅ : Nat.card H = 5 ^ 1 * 9 := by rw [hH]; norm_num
  have hG₃ : Nat.card H = 3 ^ 2 * 5 := by rw [hH]; norm_num
  have hn₅ := sylow_normal_of_card P₅ hG₅ (by norm_num) fun n hn h => by
    have : n ≤ 9 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hn₃ := sylow_normal_of_card P₃ hG₃ (by norm_num) fun n hn h => by
    have : n ≤ 5 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hc₅ := (card_sylow_eq_of_card P₅ hG₅ (by norm_num)).1
  have hc₃ := (card_sylow_eq_of_card P₃ hG₃ (by norm_num)).1
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := (P₅ : Subgroup H)) 5 (by rw [hc₅]; norm_num)
  have hx5 : orderOf ((x : H) : MulAut V) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  set S : Subgroup (MulAut V) := (P₃ : Subgroup H).map H.subtype with hS
  have hSc : Nat.card S = 9 := by
    rw [hS, card_map_of_injective H.subtype_injective, hc₃]
    norm_num
  obtain ⟨q, w, hw, hqw, hq1⟩ : ∃ q : S, ∃ w ∈ ({1}ᶜ : Set V), q • w = w ∧ q ≠ 1 := by
    by_contra hfree
    push Not at hfree
    have hinv : ∀ q : S, ∀ v ∈ ({1}ᶜ : Set V), q • v ∈ ({1}ᶜ : Set V) := by
      intro q v hv hqv
      apply hv
      have : (q : MulAut V) v = (q : MulAut V) 1 := by
        rw [map_one]
        exact hqv
      exact (q : MulAut V).injective this
    have hdvd := card_dvd_ncard_of_free (Set.toFinite _) hinv fun q v hv hqv => by
      by_contra h
      exact h (hfree q v hv hqv)
    rw [ncard_compl_one h16, hSc] at hdvd
    norm_num at hdvd
  obtain ⟨y, hyP, hyq⟩ := Subgroup.mem_map.mp q.2
  have hq1' : (q : MulAut V) ≠ 1 := fun h => hq1 (Subtype.ext h)
  have hodd : Odd (orderOf (q : MulAut V)) := by
    have hd : orderOf (q : MulAut V) ∣ 9 := by
      rw [← hSc, Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard q
    exact (show Odd 9 by decide).of_dvd_nat hd
  have hk4 := card_fixedBy_le_four h16 hq1' hodd
  have hcomm : Commute ((x : H) : MulAut V) (q : MulAut V) := by
    rw [← hyq]
    exact (Subgroup.commute_of_normal_of_disjoint _ _ hn₅ hn₃
      (IsPGroup.disjoint_of_coprime P₅.isPGroup' P₃.isPGroup' (by norm_num)) _ _ x.2 hyP).map
      H.subtype
  exact false_of_commute_of_orderOf_five h16 hx5 hcomm hw hqw hk4

theorem not_card_eq_sixtyThree {H : Subgroup (MulAut V)} (hH : Nat.card H = 63) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₇⟩ := (inferInstance : Nonempty (Sylow 7 H))
  obtain ⟨P₃⟩ := (inferInstance : Nonempty (Sylow 3 H))
  have hG₇ : Nat.card H = 7 ^ 1 * 9 := by rw [hH]; norm_num
  have hG₃ : Nat.card H = 3 ^ 2 * 7 := by rw [hH]; norm_num
  have hn₇ := sylow_normal_of_card P₇ hG₇ (by norm_num) fun n hn h => by
    have : n ≤ 9 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hc₇ := (card_sylow_eq_of_card P₇ hG₇ (by norm_num)).1
  have hc₃ := (card_sylow_eq_of_card P₃ hG₃ (by norm_num)).1
  set S₇ : Subgroup (MulAut V) := (P₇ : Subgroup H).map H.subtype with hS₇
  set S₃ : Subgroup (MulAut V) := (P₃ : Subgroup H).map H.subtype with hS₃
  have hS₇c : Nat.card S₇ = 7 := by
    rw [hS₇, card_map_of_injective H.subtype_injective, hc₇, pow_one]
  have hS₃c : Nat.card S₃ = 9 := by
    rw [hS₃, card_map_of_injective H.subtype_injective, hc₃]
    norm_num
  have hS₇p : IsPGroup 7 S₇ := P₇.isPGroup'.map H.subtype
  have hS₃p : IsPGroup 3 S₃ := P₃.isPGroup'.map H.subtype
  have hS₇ne : S₇ ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hS₇c
    norm_num at hS₇c
  have hF2 := card_fixedPoints_eq_two_of_isPGroup h16 hS₇p hS₇ne
  obtain ⟨z, hz, hz1⟩ := Set.exists_ne_of_one_lt_ncard
    (by rw [← Nat.card_coe_set_eq, hF2]; norm_num : 1 < (fixedPoints S₇ V).ncard) 1
  have hfix : ∀ h : H, (h : MulAut V) z = z := fun h =>
    apply_eq_of_le_normalizer_of_isPGroup_seven h16 hS₇p hS₇ne (le_normalizer_map_of_normal hn₇)
      hz hz1 h h.2
  have hzS₃ : z ∈ fixedPoints S₃ V := by
    rw [mem_fixedPoints]
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hs
    exact hfix t
  have h4 := four_le_card_fixedPoints_of_isPGroup h16 hS₃p hz1 hzS₃
  have hodd : Odd (Nat.card S₃) := by
    rw [hS₃c]
    decide
  have := (card_dvd_three_of_four_le h16 hodd h4).1
  rw [hS₃c] at this
  norm_num at this

theorem card_mem_of_odd {Q : Subgroup (MulAut V)} (hodd : Odd (Nat.card Q)) :
    Nat.card Q = 1 ∨ Nat.card Q = 3 ∨ Nat.card Q = 5 ∨ Nat.card Q = 7 ∨ Nat.card Q = 9 ∨
      Nat.card Q = 15 ∨ Nat.card Q = 21 := by
  have hprime : ∀ p, p.Prime → p ∣ Nat.card Q → p = 3 ∨ p = 5 ∨ p = 7 := by
    intro p hp hpd
    obtain ⟨g, -, hg, hp2, -⟩ := exists_orderOf_eq_prime hodd hp hpd
    rcases card_fixedBy_cases_of_prime h16 hp hp2 hg with ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;>
      simp [h]
  have hpow : ∀ p k, p.Prime → p ^ k ∣ Nat.card Q → p ^ k ∣ 315 := by
    intro p k hp hpk
    rcases k with _ | k
    · simp
    have hpd : p ∣ Nat.card Q := (dvd_pow_self p (Nat.succ_ne_zero k)).trans hpk
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Q) p hpk
    have hK' : Nat.card (K.map Q.subtype) = p ^ (k + 1) :=
      (card_map_of_injective Q.subtype_injective).trans hK
    have hKp : IsPGroup p (K.map Q.subtype) := IsPGroup.of_card hK'
    rcases hprime p hp hpd with rfl | rfl | rfl
    · exact (hK' ▸ card_dvd_nine_of_isPGroup h16 hKp).trans (by norm_num)
    · exact (hK' ▸ card_dvd_five_of_isPGroup h16 hKp).trans (by norm_num)
    · exact (hK' ▸ card_dvd_seven_of_isPGroup h16 hKp).trans (by norm_num)
  have h315 : Nat.card Q ∣ 315 := (Nat.dvd_iff_prime_pow_dvd_dvd 315 (Nat.card Q)).mpr hpow
  have hsolv : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : ∀ d, d ∣ Nat.card Q → Nat.Coprime d (Nat.card Q / d) →
      (∀ H : Subgroup (MulAut V), Nat.card H = d → False) → False := by
    intro d hd hcop hno
    obtain ⟨K, hK⟩ := exists_subgroup_card_eq_of_isSolvable hsolv hd hcop
    exact hno (K.map Q.subtype) ((card_map_of_injective Q.subtype_injective).trans hK)
  have h35 : ¬ 35 ∣ Nat.card Q := by
    intro hd
    have hq : Nat.card Q / 35 ∣ 9 := by simpa using Nat.div_dvd_div hd h315
    exact hsub 35 hd (Nat.Coprime.coprime_dvd_right hq (by norm_num))
      fun H hH => not_card_eq_thirtyFive h16 hH
  have h45 : ¬ 45 ∣ Nat.card Q := by
    intro hd
    have hq : Nat.card Q / 45 ∣ 7 := by simpa using Nat.div_dvd_div hd h315
    exact hsub 45 hd (Nat.Coprime.coprime_dvd_right hq (by norm_num))
      fun H hH => not_card_eq_fortyFive h16 hH
  have h63 : ¬ 63 ∣ Nat.card Q := by
    intro hd
    have hq : Nat.card Q / 63 ∣ 5 := by simpa using Nat.div_dvd_div hd h315
    exact hsub 63 hd (Nat.Coprime.coprime_dvd_right hq (by norm_num))
      fun H hH => not_card_eq_sixtyThree h16 hH
  have hmem : Nat.card Q ∈ Nat.divisors 315 := Nat.mem_divisors.mpr ⟨h315, by norm_num⟩
  have hdiv : Nat.divisors 315 = {1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at h35 h45 h63 ⊢ <;>
    omega


theorem exists_apply_eq_of_card_eq_fifteen {Q : Subgroup (MulAut V)} (hQ : Nat.card Q = 15) :
    ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ q ∈ Q, q v = w := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₅⟩ := (inferInstance : Nonempty (Sylow 5 Q))
  obtain ⟨P₃⟩ := (inferInstance : Nonempty (Sylow 3 Q))
  have hG₅ : Nat.card Q = 5 ^ 1 * 3 := by rw [hQ]; norm_num
  have hG₃ : Nat.card Q = 3 ^ 1 * 5 := by rw [hQ]; norm_num
  have hn₅ := sylow_normal_of_card P₅ hG₅ (by norm_num) fun n hn h => by
    have : n ≤ 3 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hn₃ := sylow_normal_of_card P₃ hG₃ (by norm_num) fun n hn h => by
    have : n ≤ 5 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hc₅ := (card_sylow_eq_of_card P₅ hG₅ (by norm_num)).1
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := (P₅ : Subgroup Q)) 5 (by rw [hc₅]; norm_num)
  have hx5 : orderOf ((x : Q) : MulAut V) = 5 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hstab : ∀ v : V, v ≠ 1 → ∀ q : Q, q • v = v → q = 1 := by
    intro v hv q hqv
    by_contra hq1
    have hq1' : (q : MulAut V) ≠ 1 := fun h => hq1 (Subtype.ext h)
    have hdvd : orderOf q ∣ 15 := hQ ▸ orderOf_dvd_natCard q
    have hodd : Odd (orderOf (q : MulAut V)) := by
      rw [Subgroup.orderOf_coe]
      exact (show Odd 15 by decide).of_dvd_nat hdvd
    have hk4 := card_fixedBy_le_four h16 hq1' hodd
    have h3 : orderOf q = 3 := by
      have hle : orderOf q ≤ 15 := Nat.le_of_dvd (by norm_num) hdvd
      have hne1 : orderOf q ≠ 1 := fun h => hq1 (orderOf_eq_one_iff.mp h)
      rcases (show orderOf q = 1 ∨ orderOf q = 3 ∨ orderOf q = 5 ∨ orderOf q = 15 by
        interval_cases h : orderOf q <;> omega) with h | h | h | h
      · exact absurd h hne1
      · exact h
      all_goals
        exfalso
        have h5 : 5 ∣ orderOf (q : MulAut V) := by rw [Subgroup.orderOf_coe, h] <;> norm_num
        have hm := orderOf_pow_orderOf_div (orderOf_pos (q : MulAut V)).ne' h5
        have hfix : v ∈ fixedBy V ((q : MulAut V) ^ (orderOf (q : MulAut V) / 5)) :=
          fixedBy_subset_fixedBy_npow _ _ hqv
        rcases card_fixedBy_cases_of_prime h16 (by norm_num) (by norm_num) hm with
          ⟨hc, -⟩ | ⟨-, hc⟩ | ⟨-, hc⟩
        · exact hv (eq_one_of_mem_fixedBy_of_card_eq_one h16 hc hfix)
        · norm_num at hc
        · norm_num at hc
    have hqP : q ∈ (P₃ : Subgroup Q) := by
      have hZ : IsPGroup 3 (zpowers q) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
      obtain ⟨R, hR⟩ := hZ.exists_le_sylow
      letI := Sylow.unique_of_normal P₃ hn₃
      rw [Subsingleton.elim P₃ R]
      exact hR (mem_zpowers q)
    have hcomm : Commute ((x : Q) : MulAut V) (q : MulAut V) :=
      (Subgroup.commute_of_normal_of_disjoint _ _ hn₅ hn₃
        (IsPGroup.disjoint_of_coprime P₅.isPGroup' P₃.isPGroup' (by norm_num)) _ _ x.2 hqP).map
        Q.subtype
    exact false_of_commute_of_orderOf_five h16 hx5 hcomm hv hqv hk4
  intro v w hv hw
  have hos := card_stabilizer_mul_ncard_orbit (H := Q) v
  have hS : Nat.card (stabilizer Q v) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro q hq
    exact (Subgroup.mem_bot).mpr (hstab v hv q hq)
  rw [hS, one_mul, hQ] at hos
  have hsub : orbit Q v ⊆ ({1}ᶜ : Set V) := by
    rintro u ⟨q, rfl⟩ hu
    apply hv
    have : (q : MulAut V) v = (q : MulAut V) 1 := by
      rw [map_one]
      exact hu
    exact (q : MulAut V).injective this
  have heq : orbit Q v = ({1}ᶜ : Set V) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_compl_one h16, hos])
  have hw' : w ∈ orbit Q v := by
    rw [heq]
    exact hw
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp hw'
  exact ⟨q, q.2, hq⟩

theorem card_fixedPoints_eq_two_of_card_eq_twentyOne {Q : Subgroup (MulAut V)}
    (hQ : Nat.card Q = 21) :
    Nat.card (fixedPoints Q V) = 2 ∧ ∀ v ∉ fixedPoints Q V, (orbit Q v).ncard = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P₇⟩ := (inferInstance : Nonempty (Sylow 7 Q))
  have hG₇ : Nat.card Q = 7 ^ 1 * 3 := by rw [hQ]; norm_num
  have hn₇ := sylow_normal_of_card P₇ hG₇ (by norm_num) fun n hn h => by
    have : n ≤ 3 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have hc₇ := (card_sylow_eq_of_card P₇ hG₇ (by norm_num)).1
  set S₇ : Subgroup (MulAut V) := (P₇ : Subgroup Q).map Q.subtype with hS₇
  have hS₇c : Nat.card S₇ = 7 := by
    rw [hS₇, card_map_of_injective Q.subtype_injective, hc₇, pow_one]
  have hS₇p : IsPGroup 7 S₇ := P₇.isPGroup'.map Q.subtype
  have hS₇ne : S₇ ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hS₇c
    norm_num at hS₇c
  have hF2 := card_fixedPoints_eq_two_of_isPGroup h16 hS₇p hS₇ne
  obtain ⟨z, hz, hz1⟩ := Set.exists_ne_of_one_lt_ncard
    (by rw [← Nat.card_coe_set_eq, hF2]; norm_num : 1 < (fixedPoints S₇ V).ncard) 1
  have hfix := apply_eq_of_le_normalizer_of_isPGroup_seven h16 hS₇p hS₇ne
    (le_normalizer_map_of_normal hn₇) hz hz1
  have hS₇Q : S₇ ≤ Q := map_subtype_le _
  have hsubF : fixedPoints Q V ⊆ fixedPoints S₇ V := by
    intro w hw
    rw [mem_fixedPoints] at hw ⊢
    rintro ⟨s, hs⟩
    exact hw ⟨s, hS₇Q hs⟩
  have hzQ : z ∈ fixedPoints Q V := by
    rw [mem_fixedPoints]
    intro q
    exact hfix q q.2
  have h1Q : (1 : V) ∈ fixedPoints Q V := by
    rw [mem_fixedPoints]
    intro q
    change (q : MulAut V) 1 = 1
    rw [map_one]
  have hcard : Nat.card (fixedPoints Q V) = 2 := by
    have hle := Set.ncard_le_ncard hsubF
    have hge := Set.ncard_le_ncard (show ({1, z} : Set V) ⊆ fixedPoints Q V by
      rintro w (rfl | hw)
      · exact h1Q
      · rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact hzQ)
    rw [Set.ncard_pair (Ne.symm hz1)] at hge
    have hF2' : (fixedPoints S₇ V).ncard = 2 := hF2
    rw [hF2'] at hle
    rw [Nat.card_coe_set_eq]
    omega
  refine ⟨hcard, fun v hv => ?_⟩
  have hstab : ¬ 7 ∣ Nat.card (stabilizer Q v) := by
    intro h7
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer Q v) 7 h7
    have hk7 : orderOf (((k : Q) : MulAut V)) = 7 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hk]
    have hsub : fixedPoints Q V ∪ {v} ⊆ fixedBy V ((k : Q) : MulAut V) := by
      rintro w (hw | hw)
      · exact (mem_fixedPoints.mp hw) k
      · rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact k.2
    have hle := Set.ncard_le_ncard hsub
    have hcard' : (fixedPoints Q V).ncard = 2 := hcard
    rw [Set.ncard_union_eq (Set.disjoint_singleton_right.mpr hv), Set.ncard_singleton,
      hcard'] at hle
    rcases card_fixedBy_cases_of_prime h16 (by norm_num) (by norm_num) hk7 with
      ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨-, h⟩
    · norm_num at h
    · norm_num at h
    · rw [Nat.card_coe_set_eq] at h
      omega
    · norm_num at h
  have hos := card_stabilizer_mul_ncard_orbit (H := Q) v
  rw [hQ] at hos
  have hsub : orbit Q v ⊆ (fixedPoints Q V)ᶜ := orbit_subset_compl_fixedPoints hv
  have hle : (orbit Q v).ncard ≤ 14 := by
    have := Set.ncard_le_ncard hsub
    have hcard' : (fixedPoints Q V).ncard = 2 := hcard
    rwa [Set.ncard_compl, h16, hcard'] at this
  have hdvd : (orbit Q v).ncard ∣ 21 := ⟨_, by rw [← hos, mul_comm]⟩
  have hSdvd : Nat.card (stabilizer Q v) ∣ 21 := ⟨_, hos.symm⟩
  have hpos : 0 < (orbit Q v).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, mem_orbit_self v⟩
  have hO : (orbit Q v).ncard = 1 ∨ (orbit Q v).ncard = 3 ∨ (orbit Q v).ncard = 7 ∨
      (orbit Q v).ncard = 21 := by
    have : (orbit Q v).ncard ≤ 21 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : (orbit Q v).ncard <;> omega
  rcases hO with h | h | h | h
  · rw [h, mul_one] at hos
    exact absurd ⟨1, by omega⟩ hstab
  · rw [h] at hos
    exact absurd ⟨1, by omega⟩ hstab
  · exact h
  · omega

theorem card_fixedPoints_eq_one_of_card_eq_nine {Q : Subgroup (MulAut V)} (hQ : Nat.card Q = 9) :
    Nat.card (fixedPoints Q V) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 Q := IsPGroup.of_card (n := 2) (by rw [hQ]; norm_num)
  have hodd : Odd (Nat.card Q) := by
    rw [hQ]
    decide
  by_contra hne
  have h1Q : (1 : V) ∈ fixedPoints Q V := by
    rw [mem_fixedPoints]
    intro q
    change (q : MulAut V) 1 = 1
    rw [map_one]
  obtain ⟨v, hv, hv1⟩ := Set.exists_ne_of_one_lt_ncard (by
    have hpos : 0 < (fixedPoints Q V).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, h1Q⟩
    rw [← Nat.card_coe_set_eq] at hpos ⊢
    omega : 1 < (fixedPoints Q V).ncard) 1
  have h3 := (card_dvd_three_of_four_le h16 hodd
    (four_le_card_fixedPoints_of_isPGroup h16 hP hv1 hv)).1
  rw [hQ] at h3
  norm_num at h3

theorem orbit_eq_of_card_eq_nine {Q : Subgroup (MulAut V)} (hQ : Nat.card Q = 9) {q : MulAut V}
    (hqQ : q ∈ Q) (hq1 : q ≠ 1) {v : V} (hv1 : v ≠ 1) (hqv : q v = v) :
    Nat.card (fixedBy V q) = 4 ∧ (∀ g ∈ Q, ∀ w ∈ fixedBy V q, g w ∈ fixedBy V q) ∧
      orbit Q v = fixedBy V q \ {1} := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hab : ∀ a b : Q, a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hQ]; norm_num)
  have hodd : Odd (orderOf q) := by
    have hd : orderOf q ∣ 9 := by
      rw [← hQ, ← Subgroup.orderOf_mk q hqQ]
      exact orderOf_dvd_natCard (⟨q, hqQ⟩ : Q)
    exact (show Odd 9 by decide).of_dvd_nat hd
  have hZp : IsPGroup 3 (zpowers q) := by
    have hd : orderOf q ∣ 3 ^ 2 := by
      rw [← Subgroup.orderOf_mk q hqQ]
      have := orderOf_dvd_natCard (⟨q, hqQ⟩ : Q)
      rwa [hQ] at this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hvZ : v ∈ fixedPoints (zpowers q) V := by
    rw [fixedPoints_zpowers]
    exact hqv
  have h4 : 4 ≤ Nat.card (fixedBy V q) := by
    have := four_le_card_fixedPoints_of_isPGroup h16 hZp hv1 hvZ
    rwa [fixedPoints_zpowers] at this
  have hle4 := card_fixedBy_le_four h16 hq1 hodd
  have hc4 : Nat.card (fixedBy V q) = 4 := le_antisymm hle4 h4
  have hinv : ∀ g ∈ Q, ∀ w ∈ fixedBy V q, g w ∈ fixedBy V q := by
    intro g hg w hw
    have hgq : g * q = q * g := by
      have := hab ⟨g, hg⟩ ⟨q, hqQ⟩
      exact congrArg Subtype.val this
    rw [mem_fixedBy, MulAut.smul_def] at hw ⊢
    have := congrArg (fun e : MulAut V => e w) hgq
    simp only [MulAut.mul_apply] at this
    rw [← this, hw]
  refine ⟨hc4, hinv, ?_⟩
  have hsub : orbit Q v ⊆ fixedBy V q \ {1} := by
    rintro w ⟨g, rfl⟩
    refine ⟨hinv g g.2 v hqv, ?_⟩
    intro h
    apply hv1
    have : (g : MulAut V) v = (g : MulAut V) 1 := by
      rw [map_one]
      exact h
    exact (g : MulAut V).injective this
  have h1q : (1 : V) ∈ fixedBy V q := by rw [mem_fixedBy, MulAut.smul_def, map_one]
  have hcard3 : (fixedBy V q \ {1}).ncard = 3 := by
    rw [Set.ncard_diff (Set.singleton_subset_iff.mpr h1q), Set.ncard_singleton,
      ← Nat.card_coe_set_eq, hc4]
  have hvF : v ∉ fixedPoints Q V := by
    intro hv
    have hc1 := card_fixedPoints_eq_one_of_card_eq_nine h16 hQ
    have h1Q : (1 : V) ∈ fixedPoints Q V := by
      rw [mem_fixedPoints]
      intro g
      change (g : MulAut V) 1 = 1
      rw [map_one]
    have hsub' : ({1, v} : Set V) ⊆ fixedPoints Q V := by
      rintro u (rfl | hu)
      · exact h1Q
      · rw [Set.mem_singleton_iff] at hu
        rw [hu]
        exact hv
    have := Set.ncard_le_ncard hsub'
    rw [Set.ncard_pair (Ne.symm hv1), ← Nat.card_coe_set_eq, hc1] at this
    norm_num at this
  have h3 := three_le_ncard_orbit (by rw [hQ]; decide) hvF
  have hle : (orbit Q v).ncard ≤ 3 := (Set.ncard_le_ncard hsub).trans hcard3.le
  exact Set.eq_of_subset_of_ncard_le hsub (by omega)

theorem exists_apply_eq_of_card_eq_nine {Q : Subgroup (MulAut V)} (hQ : Nat.card Q = 9)
    {X Y : Subgroup V} (hX : Nat.card X = 4) (hY : Nat.card Y = 4) (hXY : X ⊓ Y = ⊥)
    (hQX : ∀ q ∈ Q, ∀ x ∈ X, q x ∈ X) (hQY : ∀ q ∈ Q, ∀ y ∈ Y, q y ∈ Y) :
    ∀ v w : V, v ∉ X → v ∉ Y → w ∉ X → w ∉ Y → ∃ q ∈ Q, q v = w := by
  have hXYc : Nat.card X * Nat.card Y = Nat.card V := by rw [hX, hY, h16]
  set W : Set V := ((X : Set V) ∪ Y)ᶜ with hW
  have hfix4 : ∀ q ∈ Q, ∀ Z : Subgroup V, Nat.card Z = 4 → (∀ z ∈ Z, q z ∈ Z) →
      ∀ z₀ ∈ Z, z₀ ≠ 1 → q z₀ = z₀ → ∀ z ∈ Z, q z = z := by
    intro q hq Z hZ hqZ z₀ hz₀ hz₀1 hqz₀
    have hodd : Odd (Nat.card (zpowers q)) := by
      rw [Nat.card_zpowers]
      have hd : orderOf q ∣ 9 := by
        rw [← hQ, ← Subgroup.orderOf_mk q hq]
        exact orderOf_dvd_natCard (⟨q, hq⟩ : Q)
      exact (show Odd 9 by decide).of_dvd_nat hd
    set O : Set V := (Z : Set V) \ {1, z₀} with hO
    have hOinv : ∀ r : zpowers q, ∀ z ∈ O, r • z ∈ O := by
      rintro ⟨r, hr⟩ z ⟨hzZ, hz⟩
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hr
      have hZn : ∀ m : ℤ, ∀ u ∈ Z, (q ^ m) u ∈ Z := by
        intro m
        induction m using Int.induction_on with
        | zero => intro u hu; simpa using hu
        | succ m ih =>
          intro u hu
          rw [zpow_add_one, MulAut.mul_apply]
          exact ih _ (hqZ u hu)
        | pred m ih =>
          intro u hu
          rw [zpow_sub_one, MulAut.mul_apply]
          apply ih
          have hbij : Set.BijOn (fun u => q u) (Z : Set V) (Z : Set V) :=
            Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite _) (fun u hu => hqZ u hu)
              |>.mp q.injective.injOn
          obtain ⟨u', hu', hqu'⟩ := hbij.surjOn hu
          rw [← hqu']
          change (q⁻¹ * q) u' ∈ Z
          rw [inv_mul_cancel, MulAut.one_apply]
          exact hu'
      refine ⟨hZn n z hzZ, ?_⟩
      have hfix1 : (q ^ n) 1 = 1 := map_one _
      have hfixz : (q ^ n) z₀ = z₀ := by
        have := mem_fixedBy_zpow (α := V) (show z₀ ∈ fixedBy V q from hqz₀) n
        exact this
      rintro (h | h)
      · apply hz
        left
        have : (q ^ n) z = (q ^ n) 1 := by rw [hfix1]; exact h
        exact (q ^ n).injective this
      · apply hz
        right
        rw [Set.mem_singleton_iff] at h ⊢
        have : (q ^ n) z = (q ^ n) z₀ := by rw [hfixz]; exact h
        exact (q ^ n).injective this
    have hOc : O.ncard ≤ 2 := by
      have h1Z : (1 : V) ∈ Z := Z.one_mem
      have hsub : ({1, z₀} : Set V) ⊆ Z := by
        rintro u (rfl | hu)
        · exact h1Z
        · rw [Set.mem_singleton_iff] at hu
          rw [hu]
          exact hz₀
      rw [hO, Set.ncard_diff hsub, Set.ncard_pair (Ne.symm hz₀1), ← Nat.card_coe_set_eq]
      change Nat.card Z - 2 ≤ 2
      omega
    have hall := smul_eq_of_odd_of_ncard_le_two hodd (Set.toFinite O) hOinv hOc
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1, map_one]
    by_cases hzz : z = z₀
    · rw [hzz, hqz₀]
    exact hall ⟨q, mem_zpowers q⟩ z ⟨hz, by
      rintro (h | h)
      · exact hz1 h
      · exact hzz h⟩
  have hfree : ∀ q : Q, ∀ w ∈ W, q • w = w → q = 1 := by
    intro q w hw hqw
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_eq_of_inf_eq_bot hXY hXYc w
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hw
      right
      simpa using hy
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hw
      left
      simpa using hx
    change (q : MulAut V) (x * y) = x * y at hqw
    rw [map_mul] at hqw
    obtain ⟨hqx, hqy⟩ := eq_of_mul_eq_mul_of_inf_eq_bot hXY (hQX q q.2 x hx) hx (hQY q q.2 y hy)
      hy hqw
    have hX' := hfix4 q q.2 X hX (hQX q q.2) x hx hx1 hqx
    have hY' := hfix4 q q.2 Y hY (hQY q q.2) y hy hy1 hqy
    apply Subtype.ext
    apply eq_one_of_forall_apply_eq
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_inf_eq_bot hXY hXYc v
    rw [map_mul, hX' a ha, hY' b hb]
  have hWinv : ∀ q : Q, ∀ w ∈ W, q • w ∈ W := by
    intro q w hw hqw
    apply hw
    have hqi : (q⁻¹ : Q) • (q • w) = w := inv_smul_smul q w
    rw [← hqi]
    rcases hqw with h | h
    · left
      exact hQX _ (q⁻¹).2 _ h
    · right
      exact hQY _ (q⁻¹).2 _ h
  have hWc : W.ncard = 9 := by
    have hunion : ((X : Set V) ∪ Y).ncard = 7 := by
      have h := Set.ncard_union_add_ncard_inter (X : Set V) (Y : Set V)
      have hinter : ((X : Set V) ∩ Y) = {1} := by
        ext u
        constructor
        · rintro ⟨hu₁, hu₂⟩
          have : u ∈ X ⊓ Y := ⟨hu₁, hu₂⟩
          rw [hXY, mem_bot] at this
          exact this
        · rintro rfl
          exact ⟨X.one_mem, Y.one_mem⟩
      have hXc : (X : Set V).ncard = 4 := hX
      have hYc : (Y : Set V).ncard = 4 := hY
      rw [hinter, Set.ncard_singleton, hXc, hYc] at h
      omega
    rw [hW, Set.ncard_compl, h16, hunion]
  intro v w hv₁ hv₂ hw₁ hw₂
  have hvW : v ∈ W := fun h => h.elim hv₁ hv₂
  have hwW : w ∈ W := fun h => h.elim hw₁ hw₂
  have hos := card_stabilizer_mul_ncard_orbit (H := Q) v
  have hS : Nat.card (stabilizer Q v) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro q hq
    exact (Subgroup.mem_bot).mpr (hfree q v hvW hq)
  rw [hS, one_mul, hQ] at hos
  have hsub : orbit Q v ⊆ W := by
    rintro u ⟨q, rfl⟩
    exact hWinv q v hvW
  have heq : orbit Q v = W := Set.eq_of_subset_of_ncard_le hsub (by rw [hWc, hos])
  rw [← heq] at hwW
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp hwW
  exact ⟨q, q.2, hq⟩


theorem orbits_of_isolated_subgroup {K Q : Subgroup (MulAut V)} (hQK : Q ≤ K)
    (hodd : Odd (Nat.card Q)) (hQ : Q ≠ ⊥) {W : Subgroup V} (hW : Nat.card W = 8)
    (hWK : ∀ w ∈ W, ∀ k ∈ K, k w ∈ W → k w = w) :
    Nat.card Q = 3 ∧ Nat.card (fixedPoints Q V) = 4 ∧ fixedPoints Q V ⊆ W ∧
      fixedPoints K V = fixedPoints Q V ∧ (∀ v ∉ fixedPoints Q V, (orbit Q v).ncard = 3) ∧
      ∀ v, ∀ k ∈ K, ∃ q ∈ Q, k v = q v := by
  set F : Set V := fixedPoints Q V with hF
  have hFc : ∀ n : ℕ, Nat.card F = n → Fᶜ.ncard = 16 - n := by
    intro n hn
    rw [Set.ncard_compl, h16, ← Nat.card_coe_set_eq, hn]
  have hWQ : ∀ s ∈ (W : Set V) \ F, ∀ s' ∈ (W : Set V) \ F, s' ∈ orbit Q s → s = s' := by
    rintro s ⟨hsW, -⟩ s' ⟨hs'W, -⟩ hs'
    obtain ⟨q, rfl⟩ := mem_orbit_iff.mp hs'
    exact (hWK s hsW q (hQK q.2) hs'W).symm
  have horbF : ∀ s ∈ (W : Set V) \ F, orbit Q s ⊆ Fᶜ := fun s hs =>
    orbit_subset_compl_fixedPoints hs.2
  have hW8 : (W : Set V).ncard = 8 := hW
  have hWF : ((W : Set V) \ F).ncard + ((W : Set V) ∩ F).ncard = 8 := by
    rw [← hW8, add_comm]
    exact Set.ncard_inter_add_ncard_diff_eq_ncard (W : Set V) F
  have hWFle : ((W : Set V) ∩ F).ncard ≤ Nat.card F := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard Set.inter_subset_right
  obtain ⟨⟨q₀, hq₀Q⟩, hq₀1⟩ := Q.ne_bot_iff_exists_ne_one.mp hQ
  have hq₀1' : q₀ ≠ 1 := fun h => hq₀1 (Subtype.ext h)
  have hF4 : Nat.card F ≤ 4 := by
    have hoddq : Odd (orderOf q₀) := hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Q hq₀Q)
    have hsub : F ⊆ fixedBy V q₀ := fun v hv => (mem_fixedPoints.mp hv) ⟨q₀, hq₀Q⟩
    have := card_fixedBy_le_four h16 hq₀1' hoddq
    rw [Nat.card_coe_set_eq] at this ⊢
    exact (Set.ncard_le_ncard hsub).trans this
  have hFeq : Nat.card F = 4 := by
    have hdvd : Nat.card F ∣ 16 := by
      have := card_fixedPoints_dvd Q
      rwa [h16] at this
    by_contra hne
    have hF2 : Nat.card F ≤ 2 := by
      rcases eq_of_dvd_sixteen hdvd with h | h | h | h | h <;> omega
    have hS6 : 6 ≤ ((W : Set V) \ F).ncard := by omega
    have := mul_ncard_le_of_orbits 3 hWQ horbF fun s hs => three_le_ncard_orbit hodd hs.2
    rw [hFc _ rfl] at this
    omega
  have hQ3 : Nat.card Q = 3 := by
    have h3 := (card_dvd_three_of_four_le h16 hodd hFeq.ge).1
    have hne1 : Nat.card Q ≠ 1 := fun h => hQ (Subgroup.card_eq_one.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd h hne1
    · exact h
  have hfreeF := (card_dvd_three_of_four_le h16 hodd hFeq.ge).2 hQ
  have horb3 : ∀ u ∉ F, (orbit Q u).ncard = 3 := by
    intro u hu
    have hos := card_stabilizer_mul_ncard_orbit (H := Q) u
    have hS : Nat.card (stabilizer Q u) = 1 := by
      rw [Subgroup.card_eq_one, eq_bot_iff]
      intro q hq
      rw [Subgroup.mem_bot]
      by_contra hq1
      have hq1' : (q : MulAut V) ≠ 1 := fun h => hq1 (Subtype.ext h)
      apply hu
      have hfq := hfreeF.2 q q.2 hq1'
      rw [hF, ← hfq]
      exact hq
    rw [hS, one_mul, hQ3] at hos
    exact hos
  have hS4 : ((W : Set V) \ F).ncard ≤ 4 := by
    have := mul_ncard_le_of_orbits 3 hWQ horbF fun s hs => (horb3 s hs.2).ge
    rw [hFc _ hFeq] at this
    omega
  have hFW : F ⊆ W := by
    have hinter : (W : Set V) ∩ F = F := by
      apply Set.eq_of_subset_of_ncard_le Set.inter_subset_right
      rw [← Nat.card_coe_set_eq, hFeq]
      omega
    rw [← hinter]
    exact Set.inter_subset_left
  have hcover : ∀ u ∉ F, ∃ s ∈ (W : Set V) \ F, u ∈ orbit Q s := by
    intro u hu
    by_contra hno
    push Not at hno
    have hS' : ∀ s ∈ insert u ((W : Set V) \ F), ∀ s' ∈ insert u ((W : Set V) \ F),
        s' ∈ orbit Q s → s = s' := by
      intro s hs s' hs' hss'
      rcases hs with rfl | hs <;> rcases hs' with rfl | hs'
      · rfl
      · exact absurd (orbit_eq_iff.mp ((orbit_eq_iff.mpr hss').symm) :) (hno s' hs')
      · exact absurd hss' (hno s hs)
      · exact hWQ s hs s' hs' hss'
    have hST : ∀ s ∈ insert u ((W : Set V) \ F), orbit Q s ⊆ Fᶜ := by
      intro s hs
      rcases hs with rfl | hs
      · exact orbit_subset_compl_fixedPoints hu
      · exact horbF s hs
    have hm : ∀ s ∈ insert u ((W : Set V) \ F), 3 ≤ (orbit Q s).ncard := by
      intro s hs
      rcases hs with rfl | hs
      · exact (horb3 s hu).ge
      · exact (horb3 s hs.2).ge
    have := mul_ncard_le_of_orbits 3 hS' hST hm
    have huS : u ∉ (W : Set V) \ F := fun h => hno u h (mem_orbit_self u)
    rw [Set.ncard_insert_of_notMem huS, hFc _ hFeq] at this
    omega
  have hKQ : ∀ v, ∀ k ∈ K, ∃ q ∈ Q, k v = q v := by
    intro v k hk
    by_cases hv : v ∈ F
    · refine ⟨1, Q.one_mem, ?_⟩
      rw [MulAut.one_apply]
      by_cases hkv : k v ∈ F
      · exact hWK v (hFW hv) k hk (hFW hkv)
      · obtain ⟨s, ⟨hsW, hsF⟩, hks⟩ := hcover (k v) hkv
        obtain ⟨q, hq⟩ := mem_orbit_iff.mp hks
        have hq' : ((q : MulAut V)⁻¹ * k) v = s := by
          rw [MulAut.mul_apply]
          change (q : MulAut V)⁻¹ (k v) = s
          rw [← hq]
          change ((q : MulAut V)⁻¹ * q) s = s
          rw [inv_mul_cancel, MulAut.one_apply]
        have hmem : (q : MulAut V)⁻¹ * k ∈ K := K.mul_mem (K.inv_mem (hQK q.2)) hk
        have := hWK v (hFW hv) _ hmem (hq' ▸ hsW)
        rw [hq'] at this
        exact absurd (this ▸ hv) hsF
    · obtain ⟨s₀, ⟨hs₀W, hs₀F⟩, hv₀⟩ := hcover v hv
      obtain ⟨q₀, rfl⟩ := mem_orbit_iff.mp hv₀
      have hkv : k (q₀ • s₀) ∉ F := by
        intro hkv
        have hmem : k * q₀ ∈ K := K.mul_mem hk (hQK q₀.2)
        have := hWK s₀ hs₀W _ hmem (hFW hkv)
        apply hs₀F
        change (k * q₀) s₀ = s₀ at this
        rw [← this]
        exact hkv
      obtain ⟨s₁, ⟨hs₁W, hs₁F⟩, hks₁⟩ := hcover _ hkv
      obtain ⟨q₁, hq₁⟩ := mem_orbit_iff.mp hks₁
      have hmem : (q₁ : MulAut V)⁻¹ * k * q₀ ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem (hQK q₁.2)) hk) (hQK q₀.2)
      have happ : ((q₁ : MulAut V)⁻¹ * k * q₀) s₀ = s₁ := by
        rw [MulAut.mul_apply, MulAut.mul_apply]
        change (q₁ : MulAut V)⁻¹ (k (q₀ • s₀)) = s₁
        rw [← hq₁]
        change ((q₁ : MulAut V)⁻¹ * q₁) s₁ = s₁
        rw [inv_mul_cancel, MulAut.one_apply]
      have heq := hWK s₀ hs₀W _ hmem (happ ▸ hs₁W)
      rw [happ] at heq
      refine ⟨(q₁ : MulAut V) * (q₀ : MulAut V)⁻¹, Q.mul_mem q₁.2 (Q.inv_mem q₀.2), ?_⟩
      change k ((q₀ : MulAut V) s₀) = (q₁ : MulAut V) ((q₀ : MulAut V)⁻¹ ((q₀ : MulAut V) s₀))
      rw [MulAut.inv_apply_self]
      calc k ((q₀ : MulAut V) s₀) = (q₁ : MulAut V) s₁ := hq₁.symm
        _ = (q₁ : MulAut V) s₀ := by rw [heq]
  refine ⟨hQ3, hFeq, hFW, ?_, horb3, hKQ⟩
  ext v
  constructor
  · intro hv
    rw [mem_fixedPoints] at hv ⊢
    intro q
    exact hv ⟨q, hQK q.2⟩
  · intro hv
    rw [mem_fixedPoints]
    rintro ⟨k, hk⟩
    obtain ⟨q, hq, hkq⟩ := hKQ v k hk
    change k v = v
    rw [hkq]
    exact (mem_fixedPoints.mp hv) ⟨q, hq⟩

end Sixteen


section ElemAbelian

variable {V : Type*} [Group V] (hV : ∀ v : V, v * v = 1)
include hV

theorem apply_apply_eq_of_commute_of_fixedBy_subset {f g : MulAut V} (hf : ∀ v, f (f v) = v)
    (hgf : g * f = f * g) (hg : ∀ v, f v = v → g v = v) : ∀ v, g (g v) = v := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  have hc : ∀ a b : V, a * b = b * a := fun a b => by
    rw [← hinv (a * b), mul_inv_rev, hinv, hinv]
  letI : CommGroup V := { (inferInstance : Group V) with mul_comm := hc }
  intro v
  have hgfv : ∀ x, g (f x) = f (g x) := fun x => by
    have := congrArg (fun e : MulAut V => e x) hgf
    simpa [MulAut.mul_apply] using this
  have ha : f (v * f v) = v * f v := by
    rw [map_mul, hf, mul_comm]
  have hb : g v * f (g v) = v * f v := by
    rw [← hgfv, ← map_mul, hg _ ha]
  have hfg : f (g v) = g v * v * f v := by
    calc f (g v) = (g v * g v) * f (g v) := by rw [hV, one_mul]
      _ = g v * (g v * f (g v)) := by rw [mul_assoc]
      _ = g v * (v * f v) := by rw [hb]
      _ = g v * v * f v := by rw [mul_assoc]
  have hw : f (v * g v) = v * g v := by
    rw [map_mul, hfg]
    calc f v * (g v * v * f v) = (f v * f v) * (g v * v) := by
          simp only [mul_comm, mul_assoc, mul_left_comm]
      _ = v * g v := by rw [hV, one_mul, mul_comm]
  have hgw := hg _ hw
  rw [map_mul] at hgw
  calc g (g v) = (g v * g v) * g (g v) := by rw [hV, one_mul]
    _ = g v * (g v * g (g v)) := by rw [mul_assoc]
    _ = g v * (v * g v) := by rw [hgw]
    _ = v * (g v * g v) := by simp only [mul_comm, mul_assoc, mul_left_comm]
    _ = v := by rw [hV, mul_one]

theorem eq_one_of_commute_of_fixedBy_subset {f g : MulAut V} (hf : ∀ v, f (f v) = v)
    (hgf : g * f = f * g) (hg : ∀ v, f v = v → g v = v) (hodd : Odd (orderOf g)) : g = 1 := by
  have h2 : g ^ 2 = 1 := by
    apply eq_one_of_forall_apply_eq
    intro v
    rw [pow_two, MulAut.mul_apply]
    exact apply_apply_eq_of_commute_of_fixedBy_subset hV hf hgf hg v
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem apply_ne_of_commute_of_card_fixedBy_eq_four [Finite V] {f g : MulAut V}
    (hf : ∀ v, f (f v) = v) (hcard : Nat.card (fixedBy V f) = 4) (hgf : g * f = f * g)
    (hodd : Odd (orderOf g)) (hg1 : g ≠ 1) {v : V} (hv : f v = v) (hv1 : v ≠ 1) : g v ≠ v := by
  intro hgv
  apply hg1
  have hgfv : ∀ x, g (f x) = f (g x) := fun x => by
    have := congrArg (fun e : MulAut V => e x) hgf
    simpa [MulAut.mul_apply] using this
  set O : Set V := fixedBy V f \ {1, v} with hO
  have hinvO : ∀ r : zpowers g, ∀ w ∈ O, r • w ∈ O := by
    rintro ⟨r, hr⟩ w ⟨hwf, hw⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hr
    have hc : Commute (g ^ n) f := (show Commute g f from hgf).zpow_left n
    refine ⟨?_, ?_⟩
    · change (g ^ n) w ∈ fixedBy V f
      rw [mem_fixedBy, MulAut.smul_def] at hwf ⊢
      have := congrArg (fun e : MulAut V => e w) hc.eq
      simp only [MulAut.mul_apply] at this
      rw [← this, hwf]
    · have hfix1 : (g ^ n) 1 = 1 := map_one _
      have hfixv : (g ^ n) v = v := mem_fixedBy_zpow (α := V) (show v ∈ fixedBy V g from hgv) n
      rintro (h | h)
      · apply hw
        left
        have : (g ^ n) w = (g ^ n) 1 := by rw [hfix1]; exact h
        exact (g ^ n).injective this
      · apply hw
        right
        rw [Set.mem_singleton_iff] at h ⊢
        have : (g ^ n) w = (g ^ n) v := by rw [hfixv]; exact h
        exact (g ^ n).injective this
  have hOc : O.ncard ≤ 2 := by
    have h1f : (1 : V) ∈ fixedBy V f := by rw [mem_fixedBy, MulAut.smul_def, map_one]
    have hsub : ({1, v} : Set V) ⊆ fixedBy V f := by
      rintro u (rfl | hu)
      · exact h1f
      · rw [Set.mem_singleton_iff] at hu
        rw [hu]
        exact hv
    rw [hO, Set.ncard_diff hsub, Set.ncard_pair (Ne.symm hv1), ← Nat.card_coe_set_eq, hcard]
  have hoddZ : Odd (Nat.card (zpowers g)) := by
    rw [Nat.card_zpowers]
    exact hodd
  have hall := smul_eq_of_odd_of_ncard_le_two hoddZ (Set.toFinite O) hinvO hOc
  refine eq_one_of_commute_of_fixedBy_subset hV hf hgf ?_ hodd
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1, map_one]
  by_cases hwv : w = v
  · rw [hwv, hgv]
  exact hall ⟨g, mem_zpowers g⟩ w ⟨hw, by
    rintro (h | h)
    · exact hw1 h
    · exact hwv h⟩

theorem exists_zpow_apply_eq_of_commute_of_card_fixedBy_eq_four [Finite V] {f g : MulAut V}
    (hf : ∀ v, f (f v) = v) (hcard : Nat.card (fixedBy V f) = 4) (hgf : g * f = f * g)
    (hodd : Odd (orderOf g)) (hg1 : g ≠ 1) {v w : V} (hv : f v = v) (hv1 : v ≠ 1)
    (hw : f w = w) (hw1 : w ≠ 1) : ∃ n : ℤ, (g ^ n) v = w := by
  set O : Set V := fixedBy V f \ {1} with hO
  have hinvO : ∀ r : zpowers g, ∀ u ∈ O, r • u ∈ O := by
    rintro ⟨r, hr⟩ u ⟨huf, hu⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hr
    have hc : Commute (g ^ n) f := (show Commute g f from hgf).zpow_left n
    refine ⟨?_, ?_⟩
    · change (g ^ n) u ∈ fixedBy V f
      rw [mem_fixedBy, MulAut.smul_def] at huf ⊢
      have := congrArg (fun e : MulAut V => e u) hc.eq
      simp only [MulAut.mul_apply] at this
      rw [← this, huf]
    · intro h
      apply hu
      rw [Set.mem_singleton_iff] at h ⊢
      have : (g ^ n) u = (g ^ n) 1 := by rw [map_one]; exact h
      exact (g ^ n).injective this
  have h1f : (1 : V) ∈ fixedBy V f := by rw [mem_fixedBy, MulAut.smul_def, map_one]
  have hOc : O.ncard = 3 := by
    rw [hO, Set.ncard_diff (Set.singleton_subset_iff.mpr h1f), Set.ncard_singleton,
      ← Nat.card_coe_set_eq, hcard]
  have hvO : v ∈ O := ⟨hv, hv1⟩
  have hwO : w ∈ O := ⟨hw, hw1⟩
  have hsub : orbit (zpowers g) v ⊆ O := by
    rintro u ⟨r, rfl⟩
    exact hinvO r v hvO
  have hvfix : v ∉ fixedPoints (zpowers g) V := by
    rw [fixedPoints_zpowers]
    exact apply_ne_of_commute_of_card_fixedBy_eq_four hV hf hcard hgf hodd hg1 hv hv1
  have hoddZ : Odd (Nat.card (zpowers g)) := by
    rw [Nat.card_zpowers]
    exact hodd
  have h3 := three_le_ncard_orbit hoddZ hvfix
  have heq : orbit (zpowers g) v = O :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hOc]; exact h3)
  rw [← heq] at hwO
  obtain ⟨⟨r, hr⟩, hrv⟩ := mem_orbit_iff.mp hwO
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hr
  exact ⟨n, hrv⟩

theorem apply_eq_of_commute_of_transvection {f : MulAut V} {z : V}
    (hfz : ∀ v, v⁻¹ * f v = 1 ∨ v⁻¹ * f v = z) (hf1 : f ≠ 1) :
    z ≠ 1 ∧ ∀ g : MulAut V, g * f = f * g → g z = z := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, f v₀ ≠ v₀ := by
    by_contra h
    push Not at h
    exact hf1 (eq_one_of_forall_apply_eq h)
  have hz : v₀⁻¹ * f v₀ = z := by
    rcases hfz v₀ with h | h
    · exact absurd (inv_mul_eq_one.mp h).symm hv₀
    · exact h
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, inv_mul_eq_one] at hz
    exact hv₀ hz.symm
  refine ⟨hz1, fun g hgf => ?_⟩
  have hgfv : g (f v₀) = f (g v₀) := by
    have := congrArg (fun e : MulAut V => e v₀) hgf
    simpa [MulAut.mul_apply] using this
  have hgz : g z = (g v₀)⁻¹ * f (g v₀) := by
    rw [← hz, map_mul, map_inv, hgfv]
  rcases hfz (g v₀) with h | h
  · rw [h] at hgz
    exact absurd (g.injective (hgz.trans (map_one g).symm)) hz1
  · rw [hgz, h]

theorem card_fixedBy_eq_eight_of_transvection [Finite V] (h16 : Nat.card V = 16) {f : MulAut V}
    {z : V} (hfz : ∀ v, v⁻¹ * f v = 1 ∨ v⁻¹ * f v = z) (hf1 : f ≠ 1) :
    (∀ v, f (f v) = v) ∧ Nat.card (fixedBy V f) = 8 := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  have hc : ∀ a b : V, a * b = b * a := fun a b => by
    rw [← hinv (a * b), mul_inv_rev, hinv, hinv]
  obtain ⟨hz1, hcomm⟩ := apply_eq_of_commute_of_transvection hV hfz hf1
  have hfz' : f z = z := hcomm f rfl
  have hinvol : ∀ v, f (f v) = v := by
    intro v
    rcases hfz v with h | h
    · rw [inv_mul_eq_one] at h
      rw [← h, ← h]
    · have hv : f v = v * z := by rw [← h, mul_inv_cancel_left]
      rw [hv, map_mul, hv, hfz', mul_assoc, hV, mul_one]
  refine ⟨hinvol, ?_⟩
  let n : V →* V := MonoidHom.mk' (fun v => v⁻¹ * f v) fun a b => by
    change (a * b)⁻¹ * f (a * b) = a⁻¹ * f a * (b⁻¹ * f b)
    rw [map_mul, mul_inv_rev]
    calc b⁻¹ * a⁻¹ * (f a * f b) = b⁻¹ * (a⁻¹ * f a) * f b := by group
      _ = (a⁻¹ * f a) * b⁻¹ * f b := by rw [hc b⁻¹]
      _ = a⁻¹ * f a * (b⁻¹ * f b) := by group
  have hker : (n.ker : Set V) = fixedBy V f := by
    ext v
    rw [SetLike.mem_coe, MonoidHom.mem_ker, mem_fixedBy, MulAut.smul_def]
    change v⁻¹ * f v = 1 ↔ f v = v
    rw [inv_mul_eq_one, eq_comm]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, f v₀ ≠ v₀ := by
    by_contra h
    push Not at h
    exact hf1 (eq_one_of_forall_apply_eq h)
  have hrange : (n.range : Set V) = {1, z} := by
    ext w
    rw [SetLike.mem_coe, MonoidHom.mem_range]
    constructor
    · rintro ⟨v, rfl⟩
      rcases hfz v with h | h
      · left
        exact h
      · right
        exact h
    · rintro (rfl | hw)
      · exact ⟨1, map_one n⟩
      · rw [Set.mem_singleton_iff] at hw
        refine ⟨v₀, ?_⟩
        change v₀⁻¹ * f v₀ = w
        rcases hfz v₀ with h | h
        · exact absurd (inv_mul_eq_one.mp h).symm hv₀
        · rw [h, hw]
  have hidx := n.ker.card_mul_index
  rw [Subgroup.index_ker, h16] at hidx
  have hr2 : Nat.card n.range = 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hrange, Set.ncard_pair (Ne.symm hz1)]
  rw [hr2] at hidx
  have hk : Nat.card n.ker = 8 := by omega
  rw [← hk, ← SetLike.coe_sort_coe, hker]


theorem card_fixedBy_mul_eq_four_of_transvections [Finite V] (h16 : Nat.card V = 16)
    {f₁ f₂ : MulAut V} (hf : f₁ * f₂ = f₂ * f₁) {z₁ z₂ : V}
    (h₁ : ∀ v, v⁻¹ * f₁ v = 1 ∨ v⁻¹ * f₁ v = z₁) (hf₁ : f₁ ≠ 1)
    (h₂ : ∀ v, v⁻¹ * f₂ v = 1 ∨ v⁻¹ * f₂ v = z₂) (hf₂ : f₂ ≠ 1) (hz : z₁ ≠ z₂) {c : V}
    (hc₁ : f₁ c = c) (hc₂ : f₂ c ≠ c) : Nat.card (fixedBy V (f₁ * f₂)) = 4 := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hV v)
  have hc : ∀ a b : V, a * b = b * a := fun a b => by
    rw [← hinv (a * b), mul_inv_rev, hinv, hinv]
  obtain ⟨hz₁, hcomm₁⟩ := apply_eq_of_commute_of_transvection hV h₁ hf₁
  obtain ⟨hz₂, hcomm₂⟩ := apply_eq_of_commute_of_transvection hV h₂ hf₂
  have hf₁z₂ : f₁ z₂ = z₂ := hcomm₂ f₁ hf
  have hom : ∀ f : MulAut V, ∃ n : V →* V, ∀ v, n v = v⁻¹ * f v := fun f =>
    ⟨MonoidHom.mk' (fun v => v⁻¹ * f v) fun a b => by
      change (a * b)⁻¹ * f (a * b) = a⁻¹ * f a * (b⁻¹ * f b)
      rw [map_mul, mul_inv_rev]
      calc b⁻¹ * a⁻¹ * (f a * f b) = b⁻¹ * (a⁻¹ * f a) * f b := by group
        _ = (a⁻¹ * f a) * b⁻¹ * f b := by rw [hc b⁻¹]
        _ = a⁻¹ * f a * (b⁻¹ * f b) := by group, fun v => rfl⟩
  obtain ⟨n₁, hn₁⟩ := hom f₁
  obtain ⟨n₂, hn₂⟩ := hom f₂
  let N : V →* V × V := n₁.prod n₂
  have hker : (N.ker : Set V) = fixedBy V (f₁ * f₂) := by
    ext v
    rw [SetLike.mem_coe, MonoidHom.mem_ker, mem_fixedBy, MulAut.smul_def, MulAut.mul_apply]
    change (n₁ v, n₂ v) = (1, 1) ↔ f₁ (f₂ v) = v
    rw [Prod.mk.injEq, hn₁, hn₂]
    have hfix₂ : f₁ (v⁻¹ * f₂ v) = v⁻¹ * f₂ v := by
      rcases h₂ v with h | h <;> rw [h]
      · exact map_one f₁
      · exact hf₁z₂
    have key : f₁ (f₂ v) = v * ((v⁻¹ * f₁ v) * (v⁻¹ * f₂ v)) := by
      calc f₁ (f₂ v) = f₁ (v * (v⁻¹ * f₂ v)) := by rw [mul_inv_cancel_left]
        _ = f₁ v * (v⁻¹ * f₂ v) := by rw [map_mul, hfix₂]
        _ = v * ((v⁻¹ * f₁ v) * (v⁻¹ * f₂ v)) := by group
    rw [key]
    constructor
    · rintro ⟨e₁, e₂⟩
      rw [e₁, e₂, mul_one, mul_one]
    · intro h
      have hprod : (v⁻¹ * f₁ v) * (v⁻¹ * f₂ v) = 1 := by
        have := congrArg (v⁻¹ * ·) h
        simpa only [inv_mul_cancel_left, inv_mul_cancel] using this
      rcases h₁ v with e₁ | e₁ <;> rcases h₂ v with e₂ | e₂ <;> rw [e₁, e₂] at hprod ⊢
      · exact ⟨rfl, rfl⟩
      · rw [one_mul] at hprod
        exact absurd hprod hz₂
      · rw [mul_one] at hprod
        exact absurd hprod hz₁
      · exfalso
        apply hz
        have := congrArg (· * z₂) hprod
        simpa only [mul_assoc, hV, mul_one, one_mul] using this
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, f₁ v₀ ≠ v₀ := by
    by_contra h
    push Not at h
    exact hf₁ (eq_one_of_forall_apply_eq h)
  have hv₀z : n₁ v₀ = z₁ := by
    rw [hn₁]
    rcases h₁ v₀ with h | h
    · exact absurd (inv_mul_eq_one.mp h).symm hv₀
    · exact h
  have hcn₁ : n₁ c = 1 := by rw [hn₁, hc₁, inv_mul_cancel]
  have hcn₂ : n₂ c = z₂ := by
    rw [hn₂]
    rcases h₂ c with h | h
    · exact absurd (inv_mul_eq_one.mp h).symm hc₂
    · exact h
  have hn₂v₀ : n₂ v₀ = 1 ∨ n₂ v₀ = z₂ := by rw [hn₂]; exact h₂ v₀
  have hrange : (N.range : Set (V × V)) = {(1, 1), (z₁, 1), (1, z₂), (z₁, z₂)} := by
    ext ⟨a, b⟩
    rw [SetLike.mem_coe, MonoidHom.mem_range]
    constructor
    · rintro ⟨v, hv⟩
      change (n₁ v, n₂ v) = (a, b) at hv
      rw [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      rcases h₁ v with e₁ | e₁ <;> rcases h₂ v with e₂ | e₂ <;> simp [hn₁, hn₂, e₁, e₂]
    · intro hab
      have hN : ∀ v, N v = (n₁ v, n₂ v) := fun v => rfl
      have hcases : (a, b) = (1, 1) ∨ (a, b) = (z₁, 1) ∨ (a, b) = (1, z₂) ∨
          (a, b) = (z₁, z₂) := hab
      rcases hcases with h | h | h | h <;> rw [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h
      · exact ⟨1, map_one N⟩
      · rcases hn₂v₀ with e | e
        · exact ⟨v₀, by rw [hN, hv₀z, e]⟩
        · exact ⟨v₀ * c, by rw [hN, map_mul, map_mul, hv₀z, hcn₁, e, hcn₂, mul_one, hV]⟩
      · exact ⟨c, by rw [hN, hcn₁, hcn₂]⟩
      · rcases hn₂v₀ with e | e
        · exact ⟨v₀ * c, by rw [hN, map_mul, map_mul, hv₀z, hcn₁, e, hcn₂, mul_one, one_mul]⟩
        · exact ⟨v₀, by rw [hN, hv₀z, e]⟩
  have hr4 : Nat.card N.range = 4 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hrange]
    have e₁ : ((1 : V), (1 : V)) ∉ ({(z₁, 1), (1, z₂), (z₁, z₂)} : Set (V × V)) := by
      rintro (h | h | h)
      · exact hz₁ (congrArg Prod.fst h).symm
      · exact hz₂ (congrArg Prod.snd h).symm
      · exact hz₁ (congrArg Prod.fst (show ((1 : V), (1 : V)) = (z₁, z₂) from h)).symm
    have e₂ : (z₁, (1 : V)) ∉ ({(1, z₂), (z₁, z₂)} : Set (V × V)) := by
      rintro (h | h)
      · exact hz₁ (congrArg Prod.fst h)
      · exact hz₂ (congrArg Prod.snd (show (z₁, (1 : V)) = (z₁, z₂) from h)).symm
    have e₃ : ((1 : V), z₂) ≠ (z₁, z₂) := fun h => hz₁ (congrArg Prod.fst h).symm
    rw [Set.ncard_insert_of_notMem e₁, Set.ncard_insert_of_notMem e₂, Set.ncard_pair e₃]
  have hidx := N.ker.card_mul_index
  rw [Subgroup.index_ker, hr4, h16] at hidx
  have hk : Nat.card N.ker = 4 := by omega
  rw [← hk, ← SetLike.coe_sort_coe, hker]

theorem card_dvd_three_and_card_eq_of_transvections [Finite V] (h16 : Nat.card V = 16)
    {f₁ f₂ : MulAut V} (hf : f₁ * f₂ = f₂ * f₁) {z₁ z₂ : V}
    (h₁ : ∀ v, v⁻¹ * f₁ v = 1 ∨ v⁻¹ * f₁ v = z₁) (hf₁ : f₁ ≠ 1)
    (h₂ : ∀ v, v⁻¹ * f₂ v = 1 ∨ v⁻¹ * f₂ v = z₂) (hf₂ : f₂ ≠ 1)
    (h₁₂ : Nat.card (fixedBy V (f₁ * f₂)) = 4) {Q : Subgroup (MulAut V)}
    (hodd : Odd (Nat.card Q)) (hQ₁ : f₁ ∈ normalizer (Q : Set (MulAut V)))
    (hQ₂ : f₂ ∈ normalizer (Q : Set (MulAut V))) :
    Nat.card (Q ⊓ C f₁ : Subgroup (MulAut V)) ∣ 3 ∧
      Nat.card (Q ⊓ C f₂ : Subgroup (MulAut V)) ∣ 3 ∧
      Nat.card (Q ⊓ C (f₁ * f₂) : Subgroup (MulAut V)) ∣ 3 ∧ Q ⊓ C f₁ ⊓ C f₂ = ⊥ ∧
      Nat.card Q = Nat.card (Q ⊓ C f₁ : Subgroup (MulAut V)) *
        Nat.card (Q ⊓ C f₂ : Subgroup (MulAut V)) *
        Nat.card (Q ⊓ C (f₁ * f₂) : Subgroup (MulAut V)) ∧
      (Nat.card Q = 1 ∨ Nat.card Q = 3 ∨ Nat.card Q = 9) ∧
      (Nat.card Q = 3 → Q ≤ C f₁ ∨ Q ≤ C f₂ ∨ Q ≤ C (f₁ * f₂)) ∧
      (Nat.card Q = 9 → Q ⊓ C (f₁ * f₂) = ⊥ →
        Nat.card (Q ⊓ C f₁ : Subgroup (MulAut V)) = 3 ∧
          Nat.card (Q ⊓ C f₂ : Subgroup (MulAut V)) = 3 ∧ (Q ⊓ C f₁) ⊔ (Q ⊓ C f₂) = Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hz₁, hcomm₁⟩ := apply_eq_of_commute_of_transvection hV h₁ hf₁
  obtain ⟨hz₂, hcomm₂⟩ := apply_eq_of_commute_of_transvection hV h₂ hf₂
  obtain ⟨hinv₁, hc₁⟩ := card_fixedBy_eq_eight_of_transvection hV h16 h₁ hf₁
  obtain ⟨hinv₂, hc₂⟩ := card_fixedBy_eq_eight_of_transvection hV h16 h₂ hf₂
  have hsq₁ : f₁ * f₁ = 1 := eq_one_of_forall_apply_eq fun v => hinv₁ v
  have hsq₂ : f₂ * f₂ = 1 := eq_one_of_forall_apply_eq fun v => hinv₂ v
  have hinv₁₂ : ∀ v, (f₁ * f₂) ((f₁ * f₂) v) = v := by
    intro v
    have : (f₁ * f₂) * (f₁ * f₂) = 1 := by
      calc (f₁ * f₂) * (f₁ * f₂) = f₁ * (f₂ * f₁) * f₂ := by group
        _ = f₁ * (f₁ * f₂) * f₂ := by rw [hf]
        _ = (f₁ * f₁) * (f₂ * f₂) := by group
        _ = 1 := by rw [hsq₁, hsq₂, mul_one]
    have h := congrArg (fun e : MulAut V => e v) this
    simpa [MulAut.mul_apply] using h
  have hne₁₂ : f₁ ≠ f₂ := by
    intro h
    rw [h, hsq₂] at h₁₂
    have : fixedBy V (1 : MulAut V) = Set.univ := fixedBy_one_eq_univ _ _
    rw [this, Nat.card_univ, h16] at h₁₂
    norm_num at h₁₂
  have hz₁fix : (f₁ * f₂) z₁ = z₁ := by
    rw [MulAut.mul_apply, hcomm₁ f₂ hf.symm, hcomm₁ f₁ rfl]
  have hoddel : ∀ q ∈ Q, Odd (orderOf q) := fun q hq =>
    hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Q hq)
  have hcommC : ∀ {f g : MulAut V}, g ∈ C f → g * f = f * g := fun hg =>
    (mem_centralizer_singleton_iff.mp hg)
  have htrans : ∀ (f : MulAut V) (z : V), (∀ v, v⁻¹ * f v = 1 ∨ v⁻¹ * f v = z) → f ≠ 1 →
      z ≠ 1 → Nat.card (fixedBy V f) = 8 → (∀ g : MulAut V, g * f = f * g → g z = z) →
      Nat.card (Q ⊓ C f : Subgroup (MulAut V)) ∣ 3 := by
    intro f z _ _ hz hcf hcz
    set R : Subgroup (MulAut V) := Q ⊓ C f with hR
    have hRodd : Odd (Nat.card R) := hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hzR : z ∈ fixedPoints R V := by
      rw [mem_fixedPoints]
      rintro ⟨r, hr⟩
      exact hcz r (hcommC hr.2)
    have hp : ∀ p, p.Prime → p ∣ Nat.card R → p = 3 := by
      intro p hp hpd
      obtain ⟨r, hrR, hr, hp2, hsub⟩ := exists_orderOf_eq_prime hRodd hp hpd
      have hrz : r z = z := hsub hzR
      rcases card_fixedBy_cases_of_prime h16 hp hp2 hr with ⟨hc, -⟩ | ⟨hc, rfl⟩ | ⟨-, h3⟩
      · exact absurd (eq_one_of_mem_fixedBy_of_card_eq_one h16 hc hrz) hz
      ·
        exfalso
        have hP : IsPGroup 7 (zpowers r) :=
          IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hr, pow_one])
        set O : Set V := fixedBy V f \ {1, z} with hO
        have hrf : r * f = f * r := hcommC hrR.2
        have hinvO : ∀ s : zpowers r, ∀ w ∈ O, s • w ∈ O := by
          rintro ⟨s, hs⟩ w ⟨hwf, hw⟩
          obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
          have hc' : Commute (r ^ n) f := (show Commute r f from hrf).zpow_left n
          refine ⟨?_, ?_⟩
          · change (r ^ n) w ∈ fixedBy V f
            rw [mem_fixedBy, MulAut.smul_def] at hwf ⊢
            have := congrArg (fun e : MulAut V => e w) hc'.eq
            simp only [MulAut.mul_apply] at this
            rw [← this, hwf]
          · have hfix1 : (r ^ n) 1 = 1 := map_one _
            have hfixz : (r ^ n) z = z :=
              mem_fixedBy_zpow (α := V) (show z ∈ fixedBy V r from hrz) n
            rintro (h | h)
            · apply hw
              left
              have : (r ^ n) w = (r ^ n) 1 := by rw [hfix1]; exact h
              exact (r ^ n).injective this
            · apply hw
              right
              rw [Set.mem_singleton_iff] at h ⊢
              have : (r ^ n) w = (r ^ n) z := by rw [hfixz]; exact h
              exact (r ^ n).injective this
        have hmod := ncard_modEq_ncard_inter_fixedPoints hP (Set.toFinite O) hinvO
        rw [fixedPoints_zpowers] at hmod
        have h1f : (1 : V) ∈ fixedBy V f := by rw [mem_fixedBy, MulAut.smul_def, map_one]
        have hzf : z ∈ fixedBy V f := by
          rw [mem_fixedBy, MulAut.smul_def]
          exact hcz f rfl
        have hOc : O.ncard = 6 := by
          have hsub : ({1, z} : Set V) ⊆ fixedBy V f := by
            rintro u (rfl | hu)
            · exact h1f
            · rw [Set.mem_singleton_iff] at hu
              rw [hu]
              exact hzf
          rw [hO, Set.ncard_diff hsub, Set.ncard_pair (Ne.symm hz), ← Nat.card_coe_set_eq, hcf]
        have hempty : O ∩ fixedBy V r = ∅ := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          rintro ⟨-, hw⟩ hwr
          apply hw
          have hsub : ({1, z} : Set V) ⊆ fixedBy V r := by
            rintro u (rfl | hu)
            · rw [mem_fixedBy, MulAut.smul_def, map_one]
            · rw [Set.mem_singleton_iff] at hu
              rw [hu]
              exact hrz
          have heq : ({1, z} : Set V) = fixedBy V r :=
            Set.eq_of_subset_of_ncard_le hsub (by
              rw [← Nat.card_coe_set_eq, hc, Set.ncard_pair (Ne.symm hz)])
          rw [← heq] at hwr
          exact hwr
        rw [hempty, Set.ncard_empty, hOc] at hmod
        exact absurd hmod (by decide)
      · exact h3
    have hpow : Nat.card R = 3 ^ (Nat.card R).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hp' hpd => hp _ hp' hpd
    have hRp : IsPGroup 3 R := IsPGroup.of_card hpow
    exact (card_dvd_three_of_four_le h16 hRodd
      (four_le_card_fixedPoints_of_isPGroup h16 hRp hz hzR)).1
  have hC₁ := htrans f₁ z₁ h₁ hf₁ hz₁ hc₁ hcomm₁
  have hC₂ := htrans f₂ z₂ h₂ hf₂ hz₂ hc₂ hcomm₂
  have hC₁₂ : Nat.card (Q ⊓ C (f₁ * f₂) : Subgroup (MulAut V)) ∣ 3 := by
    set R : Subgroup (MulAut V) := Q ⊓ C (f₁ * f₂) with hR
    set O : Set V := fixedBy V (f₁ * f₂) \ {1} with hO
    have hinvO : ∀ r : R, ∀ w ∈ O, r • w ∈ O := by
      rintro ⟨r, hr⟩ w ⟨hwf, hw⟩
      have hrf : r * (f₁ * f₂) = (f₁ * f₂) * r := hcommC hr.2
      refine ⟨?_, ?_⟩
      · change r w ∈ fixedBy V (f₁ * f₂)
        rw [mem_fixedBy, MulAut.smul_def] at hwf ⊢
        have := congrArg (fun e : MulAut V => e w) hrf
        simp only [MulAut.mul_apply] at this
        rw [MulAut.mul_apply] at hwf ⊢
        rw [← this, hwf]
      · intro h
        apply hw
        rw [Set.mem_singleton_iff] at h ⊢
        have : r w = r 1 := by rw [map_one]; exact h
        exact r.injective this
    have hfree : ∀ r : R, ∀ w ∈ O, r • w = w → r = 1 := by
      rintro ⟨r, hr⟩ w ⟨hwf, hw⟩ hrw
      by_contra hr1
      have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
      exact apply_ne_of_commute_of_card_fixedBy_eq_four hV hinv₁₂ h₁₂ (hcommC hr.2)
        (hoddel r hr.1) hr1' hwf hw hrw
    have hOc : O.ncard = 3 := by
      have h1f : (1 : V) ∈ fixedBy V (f₁ * f₂) := by rw [mem_fixedBy, MulAut.smul_def, map_one]
      rw [hO, Set.ncard_diff (Set.singleton_subset_iff.mpr h1f), Set.ncard_singleton,
        ← Nat.card_coe_set_eq, h₁₂]
    have := card_dvd_ncard_of_free (Set.toFinite O) hinvO hfree
    rwa [hOc] at this
  have hC₀ : Q ⊓ C f₁ ⊓ C f₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro q ⟨⟨hqQ, hq₁⟩, hq₂⟩
    rw [Subgroup.mem_bot]
    by_contra hq1
    have hq₁₂ : q * (f₁ * f₂) = (f₁ * f₂) * q := by
      rw [← mul_assoc, hcommC hq₁, mul_assoc, hcommC hq₂, mul_assoc]
    exact apply_ne_of_commute_of_card_fixedBy_eq_four hV hinv₁₂ h₁₂ hq₁₂ (hoddel q hqQ) hq1
      hz₁fix hz₁ (hcomm₁ q (hcommC hq₁))
  have hcard : Nat.card Q = Nat.card (Q ⊓ C f₁ : Subgroup (MulAut V)) *
      Nat.card (Q ⊓ C f₂ : Subgroup (MulAut V)) *
      Nat.card (Q ⊓ C (f₁ * f₂) : Subgroup (MulAut V)) := by
    let T := GorensteinWalter.kleinFourOfCommutingInvolutions f₁ f₂ hsq₁ hsq₂ hf
    haveI : IsKleinFour T := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions f₁ f₂
      hsq₁ hsq₂ hf₁ hf₂ hne₁₂ hf
    have hmemT : ∀ t ∈ T, t = f₁ * f₂ ∨ t = f₁ ∨ t = f₂ ∨ t = 1 := by
      intro t ht
      change t ∈ ({f₁ * f₂, f₁, f₂, 1} : Set (MulAut V)) at ht
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
    have hTQ : T ≤ normalizer (Q : Set (MulAut V)) := by
      intro t ht
      rcases hmemT t ht with rfl | rfl | rfl | rfl
      · exact mul_mem hQ₁ hQ₂
      · exact hQ₁
      · exact hQ₂
      · exact one_mem _
    have hf₁T : f₁ ∈ T := by
      change f₁ ∈ ({f₁ * f₂, f₁, f₂, 1} : Set (MulAut V))
      simp
    have hf₂T : f₂ ∈ T := by
      change f₂ ∈ ({f₁ * f₂, f₁, f₂, 1} : Set (MulAut V))
      simp
    have h := ABGLocalTools.card_mul_card_centralizer_four_sq hodd hTQ hf₁T hf₂T hf₁ hf₂ hne₁₂
    have hT1 : Nat.card (Q ⊓ centralizer (T : Set (MulAut V)) : Subgroup (MulAut V)) = 1 := by
      rw [Subgroup.card_eq_one, eq_bot_iff, ← hC₀]
      rintro q ⟨hqQ, hqT⟩
      exact ⟨⟨hqQ, mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hqT) f₁ hf₁T).symm⟩,
        mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hqT) f₂ hf₂T).symm⟩
    rw [hT1, one_pow, mul_one] at h
    exact h
  have h139 : Nat.card Q = 1 ∨ Nat.card Q = 3 ∨ Nat.card Q = 9 := by
    have e₁ := (Nat.dvd_prime Nat.prime_three).mp hC₁
    have e₂ := (Nat.dvd_prime Nat.prime_three).mp hC₂
    have e₃ := (Nat.dvd_prime Nat.prime_three).mp hC₁₂
    rcases e₁ with e₁ | e₁ <;> rcases e₂ with e₂ | e₂ <;> rcases e₃ with e₃ | e₃ <;>
      rw [hcard, e₁, e₂, e₃] <;> norm_num
    exfalso
    have h27 : Nat.card Q = 3 ^ 3 := by rw [hcard, e₁, e₂, e₃]; norm_num
    have := card_dvd_nine_of_isPGroup h16 (IsPGroup.of_card h27)
    rw [h27] at this
    norm_num at this
  refine ⟨hC₁, hC₂, hC₁₂, hC₀, hcard, h139, ?_, ?_⟩
  ·
    intro hQ3
    have e₁ := (Nat.dvd_prime Nat.prime_three).mp hC₁
    have e₂ := (Nat.dvd_prime Nat.prime_three).mp hC₂
    have e₃ := (Nat.dvd_prime Nat.prime_three).mp hC₁₂
    have hle : ∀ f : MulAut V, Nat.card (Q ⊓ C f : Subgroup (MulAut V)) = 3 → Q ≤ C f := by
      intro f hf3
      have heq : Q ⊓ C f = Q := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hf3, hQ3])
      rw [← heq]
      exact inf_le_right
    rcases e₁ with e₁ | e₁
    · rcases e₂ with e₂ | e₂
      · rcases e₃ with e₃ | e₃
        · rw [hcard, e₁, e₂, e₃] at hQ3
          norm_num at hQ3
        · exact Or.inr (Or.inr (hle _ e₃))
      · exact Or.inr (Or.inl (hle _ e₂))
    · exact Or.inl (hle _ e₁)
  ·
    intro hQ9 h₁₂Q
    have e₃ : Nat.card (Q ⊓ C (f₁ * f₂) : Subgroup (MulAut V)) = 1 := by
      rw [h₁₂Q, card_bot]
    have e₁ := (Nat.dvd_prime Nat.prime_three).mp hC₁
    have e₂ := (Nat.dvd_prime Nat.prime_three).mp hC₂
    have h3₁ : Nat.card (Q ⊓ C f₁ : Subgroup (MulAut V)) = 3 := by
      rcases e₁ with e₁ | e₁
      · rcases e₂ with e₂ | e₂ <;> rw [hcard, e₁, e₂, e₃] at hQ9 <;> norm_num at hQ9
      · exact e₁
    have h3₂ : Nat.card (Q ⊓ C f₂ : Subgroup (MulAut V)) = 3 := by
      rcases e₂ with e₂ | e₂
      · rw [hcard, h3₁, e₂, e₃] at hQ9
        norm_num at hQ9
      · exact e₂
    refine ⟨h3₁, h3₂, ?_⟩
    set J := (Q ⊓ C f₁) ⊔ (Q ⊓ C f₂) with hJ
    have hJQ : J ≤ Q := sup_le inf_le_left inf_le_left
    have hJdvd : Nat.card J ∣ 9 := hQ9 ▸ Subgroup.card_dvd_of_le hJQ
    have h1J : Q ⊓ C f₁ ≤ J := le_sup_left
    have h2J : Q ⊓ C f₂ ≤ J := le_sup_right
    have hJ9 : Nat.card J = 9 := by
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card J ∣ 3 ^ 2 by
        simpa using hJdvd) with ⟨j, hj, hjeq⟩
      interval_cases j
      ·
        have := Subgroup.card_le_of_le h1J
        rw [hjeq, h3₁] at this
        norm_num at this
      ·
        exfalso
        have heq : Q ⊓ C f₁ = J := Subgroup.eq_of_le_of_card_ge h1J (by rw [hjeq, h3₁]; norm_num)
        have h21 : Q ⊓ C f₂ ≤ Q ⊓ C f₁ := heq ▸ h2J
        have hbot : Q ⊓ C f₂ = ⊥ := by
          rw [eq_bot_iff, ← hC₀]
          intro q hq
          exact ⟨h21 hq, hq.2⟩
        rw [hbot, card_bot] at h3₂
        norm_num at h3₂
      · simpa using hjeq
    exact Subgroup.eq_of_le_of_card_ge hJQ (by rw [hJ9, hQ9])

end ElemAbelian

theorem apply_mem_of_commute_of_fixedBy {V : Type*} [Group V] [Finite V]
    (hc : ∀ a b : V, a * b = b * a) {u g : MulAut V} {X : Subgroup V}
    (hXu : ∀ x ∈ X, u x ∈ X) (hfree : ∀ x ∈ X, u x = x → x = 1)
    (hcard : Nat.card X * Nat.card (fixedBy V u) = Nat.card V) (hgu : g * u = u * g) :
    ∀ x ∈ X, g x ∈ X := by
  let n : V →* V := MonoidHom.mk' (fun v => v⁻¹ * u v) fun a b => by
    change (a * b)⁻¹ * u (a * b) = a⁻¹ * u a * (b⁻¹ * u b)
    rw [map_mul, mul_inv_rev]
    calc b⁻¹ * a⁻¹ * (u a * u b) = b⁻¹ * (a⁻¹ * u a) * u b := by group
      _ = (a⁻¹ * u a) * b⁻¹ * u b := by rw [hc b⁻¹]
      _ = a⁻¹ * u a * (b⁻¹ * u b) := by group
  have hn : ∀ v, n v = v⁻¹ * u v := fun v => rfl
  have hker : (n.ker : Set V) = fixedBy V u := by
    ext v
    rw [SetLike.mem_coe, MonoidHom.mem_ker, mem_fixedBy, MulAut.smul_def, hn, inv_mul_eq_one,
      eq_comm]
  have hXn : X ≤ n.range := by
    intro x hx
    let m : X → X := fun y => ⟨n y, X.mul_mem (X.inv_mem y.2) (hXu y y.2)⟩
    have hm : Function.Injective m := by
      intro y y' h
      have h' : n y = n y' := congrArg Subtype.val h
      have hmem : (y : V) * (y' : V)⁻¹ ∈ X := X.mul_mem y.2 (X.inv_mem y'.2)
      have hfix : u ((y : V) * (y' : V)⁻¹) = (y : V) * (y' : V)⁻¹ := by
        rw [hn, hn] at h'
        rw [map_mul, map_inv]
        calc u y * (u y')⁻¹ = y * ((y : V)⁻¹ * u y) * (u y')⁻¹ := by group
          _ = y * ((y' : V)⁻¹ * u y') * (u y')⁻¹ := by rw [h']
          _ = y * (y' : V)⁻¹ := by group
      exact Subtype.ext (mul_inv_eq_one.mp (hfree _ hmem hfix))
    obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hm) ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  have hidx := n.ker.card_mul_index
  rw [Subgroup.index_ker] at hidx
  have hkerc : Nat.card n.ker = Nat.card (fixedBy V u) := by
    rw [← SetLike.coe_sort_coe, hker]
  rw [hkerc] at hidx
  have hpos : 0 < Nat.card (fixedBy V u) := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, by rw [mem_fixedBy, MulAut.smul_def, map_one]⟩
  have hrange : Nat.card n.range = Nat.card X := by
    have : Nat.card (fixedBy V u) * Nat.card n.range =
        Nat.card (fixedBy V u) * Nat.card X := by rw [hidx, ← hcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have heq : X = n.range := Subgroup.eq_of_le_of_card_ge hXn hrange.le
  intro x hx
  rw [heq] at hx ⊢
  obtain ⟨v, rfl⟩ := hx
  refine ⟨g v, ?_⟩
  have hguv : g (u v) = u (g v) := by
    have := congrArg (fun e : MulAut V => e v) hgu
    simpa [MulAut.mul_apply] using this
  rw [hn, hn, map_mul, map_inv, hguv]

end CFSG.GH72
