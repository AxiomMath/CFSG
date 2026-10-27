module

public import CFSG.Certificates.Kernel.L34Syl.Sound
public import Mathlib.Tactic.NormNum.Prime
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KC.L34Syl

theorem exists_pow_lt_of_mem_zpowers {G : Type*} [Group G] {p : ℕ} {x y : G} (hx : orderOf x = p)
    (hp : 0 < p) (h : y ∈ Subgroup.zpowers x) : ∃ j < p, x ^ j = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  refine ⟨(k % (p : ℤ)).toNat, ?_, ?_⟩
  · have h1 : k % (p : ℤ) < p := Int.emod_lt_of_pos k (by exact_mod_cast hp)
    have h2 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg k (by exact_mod_cast hp.ne')
    omega
  · have h2 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg k (by exact_mod_cast hp.ne')
    rw [← zpow_natCast, Int.toNat_of_nonneg h2, ← hx, zpow_mod_orderOf]

theorem canonGen_unique {n p : ℕ} {x y : Equiv.Perm (Fin n)} (hx : orderOf x = p)
    (hy : orderOf y = p) (cx : CanonGen p x) (cy : CanonGen p y)
    (h : Subgroup.zpowers x = Subgroup.zpowers y) : x = y := by
  obtain ⟨a, ha, hax, hxa⟩ := cx
  obtain ⟨b, hb, hby, hyb⟩ := cy
  have hp : 0 < p := hx ▸ orderOf_pos x
  obtain ⟨j, hj, rfl⟩ := exists_pow_lt_of_mem_zpowers hx hp (h ▸ Subgroup.mem_zpowers y)
  obtain ⟨l, hl, hl'⟩ := exists_pow_lt_of_mem_zpowers hy hp (h.symm ▸ Subgroup.mem_zpowers x)
  have hfix : ∀ c : Fin n, x c = c ↔ (x ^ j) c = c := by
    intro c
    refine ⟨fun hc => Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hc j, fun hc => ?_⟩
    rw [← hl']
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hc l
  have hab : a = b := by
    rcases lt_trichotomy a b with hlt | heq | hgt
    · exact absurd ((hfix a).2 (hb a hlt)) hax
    · exact heq
    · exact absurd ((hfix b).1 (ha b hgt)) hby
  subst hab
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · interval_cases j
    · exact absurd (by simp : (x ^ 0) a = a) hby
    · exact (pow_one x).symm
  · have h1 := hxa j hj2 hj
    rcases Nat.lt_or_ge l 2 with hl2 | hl2
    · interval_cases l
      · rw [pow_zero] at hl'
        exact absurd (by rw [← hl']; rfl : x a = a) hax
      · rw [pow_one] at hl'
        exact hl'.symm
    · have h2 := hyb l hl2 hl
      rw [hl'] at h2
      omega

theorem card_sylow_dvd {G : Type*} [Group G] [Finite G] {p N : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p * N) (hpN : ¬ p ∣ N) : Nat.card (Sylow p G) ∣ N := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hP : Nat.card P = p := by
    rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hp.out.ne_zero
      (by rintro rfl; simp at hpN)]
    rw [Finsupp.add_apply, hp.out.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hpN, add_zero, pow_one]
  have hidx : P.index = N := by
    have := P.card_mul_index
    rw [hP, hG] at this
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos this
  rw [← hidx]
  exact P.card_dvd_index

theorem card_sylow_five_le {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 20160) :
    Nat.card (Sylow 5 G) ≤ 2016 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := card_sylow_dvd (p := 5) (N := 4032) (by rw [hG]) (by norm_num)
  have hm := card_sylow_modEq_one 5 G
  unfold Nat.ModEq at hm
  rcases Nat.lt_or_ge c 2 with h2 | h2
  · interval_cases c <;> omega
  · nlinarith

theorem card_sylow_seven_le {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 20160) :
    Nat.card (Sylow 7 G) ≤ 960 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := card_sylow_dvd (p := 7) (N := 2880) (by rw [hG]) (by norm_num)
  have hm := card_sylow_modEq_one 7 G
  unfold Nat.ModEq at hm
  rcases Nat.lt_or_ge c 3 with h3 | h3
  · interval_cases c <;> omega
  · nlinarith

theorem factorization_mul_self {p N : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) :
    (p * N).factorization p = 1 := by
  rw [Nat.factorization_mul hp.ne_zero (by rintro rfl; simp at hpN), Finsupp.add_apply,
    hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hpN]

noncomputable def sylowOf {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime] (S : Subgroup G)
    [Finite S] {N : ℕ} (hS : Nat.card S = p * N) (hpN : ¬ p ∣ N) (y : G) (hy : y ∈ S) (hyp : orderOf y = p) :
    Sylow p S :=
  Sylow.ofCard (Subgroup.zpowers (⟨y, hy⟩ : S)) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyp, hS, factorization_mul_self hp.out hpN, pow_one])

theorem zpowers_eq_of_sylowOf_eq {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    [Finite S] {N : ℕ} {hS : Nat.card S = p * N} {hpN : ¬ p ∣ N} {y z : G} {hy : y ∈ S} {hz : z ∈ S}
    {hyp : orderOf y = p} {hzp : orderOf z = p}
    (h : sylowOf S hS hpN y hy hyp = sylowOf S hS hpN z hz hzp) :
    Subgroup.zpowers y = Subgroup.zpowers z := by
  have e : Subgroup.zpowers (⟨y, hy⟩ : S) = Subgroup.zpowers (⟨z, hz⟩ : S) := by
    have e0 := congrArg (fun P : Sylow p S => (P : Subgroup S)) h
    simpa only [sylowOf, Sylow.coe_ofCard] using e0
  have := congrArg (Subgroup.map S.subtype) e
  rwa [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this

theorem exists_mem_zpowers_eq {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (S : Subgroup G)
    [Finite S] {N : ℕ} (hS : Nat.card S = p * N) (hpN : ¬ p ∣ N) (L : List G)
    (hLS : ∀ X ∈ L, X ∈ S ∧ orderOf X = p)
    (hnd : L.Pairwise fun X Y => Subgroup.zpowers X ≠ Subgroup.zpowers Y)
    (hcard : Nat.card (Sylow p S) ≤ L.length) {x : G} (hx : x ∈ S) (hxp : orderOf x = p) :
    ∃ X ∈ L, Subgroup.zpowers X = Subgroup.zpowers x := by
  have hmem : ∀ i : Fin L.length, L[i] ∈ L := fun i => List.getElem_mem i.2
  let f : Fin L.length → Sylow p S := fun i =>
    sylowOf S hS hpN L[i] (hLS _ (hmem i)).1 (hLS _ (hmem i)).2
  have hinj : Function.Injective f := by
    intro i j hij
    have e := zpowers_eq_of_sylowOf_eq hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact (List.pairwise_iff_getElem.1 hnd i j i.2 j.2 hlt) e
    · exact (List.pairwise_iff_getElem.1 hnd j i j.2 i.2 hlt) e.symm
  have hbij := hinj.bijective_of_nat_card_le (by simpa using hcard)
  obtain ⟨i, hi⟩ := hbij.2 (sylowOf S hS hpN x hx hxp)
  exact ⟨L[i], hmem i, zpowers_eq_of_sylowOf_eq hi⟩

theorem pp_inj {n w m x y : ℕ} (hw : 0 < w) (hm : m = CFSG.KS.mask w) (hx : PermN n w m x)
    (hy : PermN n w m y) (hx' : x < 2 ^ (n * w)) (hy' : y < 2 ^ (n * w))
    (h : pp n w m x = pp n w m y) : x = y := by
  subst hm
  refine CFSG.KS.PF.eq_of_fields hw ?_ ?_ ((CFSG.KS.PK.permOf_eq_iff hx hy).1 h)
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hx'
  · rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hy'

theorem card_gen_eq {n w m nw pm ng T N : ℕ} {L : ℕ → ℕ}
    (hinj : ∀ k < N, ∀ k' < N, pp n w m (lane nw pm T k) = pp n w m (lane nw pm T k') → k = k')
    (hmem : ∀ g, g ∈ gen n w m L ng ↔ ∃ k < N, pp n w m (lane nw pm T k) = g) :
    Nat.card (gen n w m L ng) = N := by
  let f : Fin N → gen n w m L ng := fun k =>
    ⟨pp n w m (lane nw pm T k), (hmem _).2 ⟨k, k.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Fin.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab)), fun g => ?_⟩
    obtain ⟨k, hk, he⟩ := (hmem g).1 g.2
    exact ⟨⟨k, hk⟩, Subtype.ext he⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem eq_stabilizer_of_card {G X : Type*} [Group G] [Finite G] [MulAction G X] (x : X)
    {M : Subgroup G} (hM : M ≤ MulAction.stabilizer G x)
    (h : Nat.card G ≤ Nat.card M * Nat.card (MulAction.orbit G x)) :
    M = MulAction.stabilizer G x := by
  have e := (MulAction.stabilizer G x).card_mul_index
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at e
  have hpos : 0 < Nat.card (MulAction.orbit G x) := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : Nat.card (MulAction.stabilizer G x) ≤ Nat.card M := by
    by_contra hlt
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt) hpos
    omega
  exact Subgroup.eq_of_le_of_card_ge hM hle

end CFSG.KC.L34Syl

end
