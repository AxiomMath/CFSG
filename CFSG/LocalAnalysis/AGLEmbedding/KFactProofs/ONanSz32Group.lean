module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28Group
public import CFSG.RankThree.PartOne.K159F.SzAbs

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sz32Local

open CFSG.RankThree.PartOne.K159.SzAbs CFSG.AGLEmbedding.KFactProofs
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

structure Sz32Data (G : Type*) [Group G] (T : Subgroup G) : Prop where
  card_group : Nat.card G = 32537600
  card_eq : Nat.card T = 25
  isCyclic : IsCyclic T
  centralizer_le : ∀ t ∈ T, t ≠ 1 → ∀ g : G, g * t = t * g → g ∈ T

theorem divisor_cases {m : ℕ} (hd : m ∣ 325376) (hm : m ≡ 1 [MOD 25]) : m = 1 ∨ m = 325376 := by
  have h : (325376 : ℕ) = 2 ^ 8 * (31 * 41) := by norm_num
  rw [h] at hd
  obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 hd
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 ha
  have hb' : b ∈ Nat.divisors (31 * 41) := Nat.mem_divisors.2 ⟨hb, by norm_num⟩
  have hdiv : Nat.divisors (31 * 41) = {1, 31, 41, 1271} := by decide +kernel
  rw [hdiv] at hb'
  have key : ∀ i < 9, ∀ b ∈ ({1, 31, 41, 1271} : Finset ℕ),
      2 ^ i * b ≡ 1 [MOD 25] → 2 ^ i * b = 1 ∨ 2 ^ i * b = 325376 := by decide +kernel
  exact key i (by omega) b hb' hm

theorem isPGroup_sup_of_commute {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G}
    (hA : IsPGroup p A) (hB : IsPGroup p B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsPGroup p ↥(A ⊔ B) := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = a⁻¹ * b⁻¹ := by
            have := hcomm a ha b hb
            rw [← mul_inv_rev, ← mul_inv_rev, this] }
  have hle : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  intro x
  obtain ⟨a, ha, b, hb, hx⟩ := hle x.2
  obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
  obtain ⟨l, hl⟩ := hB ⟨b, hb⟩
  have hk' : a ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hl' : b ^ (p ^ l) = 1 := by simpa using congrArg Subtype.val hl
  refine ⟨k + l, Subtype.ext ?_⟩
  have hab : Commute a b := hcomm a ha b hb
  have e1 : a ^ (p ^ (k + l)) = 1 := by
    rw [pow_add, pow_mul, hk', one_pow]
  have e2 : b ^ (p ^ (k + l)) = 1 := by
    rw [add_comm, pow_add, pow_mul, hl', one_pow]
  show (x : G) ^ (p ^ (k + l)) = 1
  rw [hx, hab.mul_pow, e1, e2, one_mul]

theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {p k : ℕ} (hp : p.Prime) {f : G}
    (hf : f ^ p ^ k = 1) : IsPGroup p (Subgroup.zpowers f) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hf)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

namespace Sz32Data

variable {G : Type*} [Group G] {T : Subgroup G}

theorem commute (h : Sz32Data G T) : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro x hx y hy
  have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (G := T)
    (by rw [h.card_eq]; norm_num)
  exact congrArg Subtype.val (this.is_comm.comm (⟨x, hx⟩ : T) ⟨y, hy⟩)

theorem exists_ne_one (h : Sz32Data G T) : ∃ t ∈ T, t ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  have : Nat.card T ≤ 1 := by
    rw [Finite.card_le_one_iff_subsingleton]
    exact ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
  rw [h.card_eq] at this
  omega

theorem mem_normalizer_of_conj_mem [Finite G] (h : Sz32Data G T) {x y : G} (hx : x ∈ T)
    (hx1 : x ≠ 1) (hy : y⁻¹ * x * y ∈ T) : y ∈ Subgroup.normalizer (T : Set G) := by
  have hx1' : y⁻¹ * x * y ≠ 1 := by
    intro h1
    apply hx1
    have h2 : y * (y⁻¹ * x * y) * y⁻¹ = y * 1 * y⁻¹ := by rw [h1]
    simpa [mul_assoc] using h2
  have key : ∀ w ∈ T, y⁻¹ * w * y ∈ T := by
    intro w hw
    refine h.centralizer_le (y⁻¹ * x * y) hy hx1' (y⁻¹ * w * y) ?_
    calc y⁻¹ * w * y * (y⁻¹ * x * y) = y⁻¹ * (w * x) * y := by group
      _ = y⁻¹ * (x * w) * y := by rw [h.commute w hw x hx]
      _ = y⁻¹ * x * y * (y⁻¹ * w * y) := by group
  have hinv : y⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.mem_normalizer_fintype (fun n hn => by simpa using key n hn)
  simpa using Subgroup.inv_mem _ hinv

theorem ker_normalizerMonoidHom (h : Sz32Data G T) :
    (T.normalizerMonoidHom).ker = T.subgroupOf (Subgroup.normalizer (T : Set G)) := by
  ext ⟨n, hn⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
    have h2 := congrArg (fun f : MulAut T => ((f ⟨t, ht⟩ : T) : G)) h1
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    refine h.centralizer_le t ht ht1 n ?_
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h2]
  · intro hnT
    refine MulEquiv.ext fun a => Subtype.ext ?_
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
    calc n * a * n⁻¹ = a * n * n⁻¹ := by rw [h.commute n hnT a a.2]
      _ = a := by group


theorem card_normalizer [Finite G] (h : Sz32Data G T) :
    Nat.card (Subgroup.normalizer (T : Set G)) = 100 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hTfin : Finite T := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  have := h.isCyclic
  have hTN : T ≤ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer
  have hker : Nat.card (T.normalizerMonoidHom).ker = 25 := by
    rw [h.ker_normalizerMonoidHom, ← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range (T.normalizerMonoidHom)
  rw [hker] at hmul
  have hrange : Nat.card (T.normalizerMonoidHom).range ∣ 20 := by
    have h1 : Nat.card (T.normalizerMonoidHom).range ∣ Nat.card (MulAut T) :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.totient 25 = 20 := by decide
    rwa [IsCyclic.card_mulAut, h.card_eq, h2] at h1
  have hdvd : Nat.card (Subgroup.normalizer (T : Set G)) ∣ 32537600 := by
    rw [← h.card_group]
    exact Subgroup.card_subgroup_dvd_card _
  generalize Nat.card (T.normalizerMonoidHom).range = r at hmul hrange
  have hr : r = 1 ∨ r = 2 ∨ r = 4 := by
    have hmem : r ∈ Nat.divisors 20 := Nat.mem_divisors.2 ⟨hrange, by norm_num⟩
    have hdiv : Nat.divisors 20 = {1, 2, 4, 5, 10, 20} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rw [← hmul] at hdvd
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hsyl : Nat.card T = 5 ^ (Nat.card G).factorization 5 := by
    rw [h.card_eq, h.card_group, factorization_five]
    norm_num
  let P : Sylow 5 G := Sylow.ofCard T hsyl
  have hmod := card_sylow_modEq_one 5 G
  have hidx : Nat.card (Sylow 5 G) = (Subgroup.normalizer (T : Set G)).index :=
    Sylow.card_eq_index_normalizer P
  have hcm := Subgroup.card_mul_index (Subgroup.normalizer (T : Set G))
  rw [h.card_group, ← hmul] at hcm
  rw [hidx] at hmod
  unfold Nat.ModEq at hmod
  rcases hr with rfl | rfl | rfl <;> omega

theorem exists_mem_normalizer_not_mem [Finite G] (h : Sz32Data G T) :
    ∃ s ∈ Subgroup.normalizer (T : Set G), s ∉ T := by
  by_contra hcon
  push Not at hcon
  have hle : Subgroup.normalizer (T : Set G) ≤ T := fun s hs => hcon s hs
  have hTfin : Finite T := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by rw [h.card_group]; norm_num)
  have := Subgroup.card_le_of_le hle
  rw [h.card_normalizer, h.card_eq] at this
  omega

theorem exists_fixed_point_free [Finite G] (h : Sz32Data G T) :
    ∃ s ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ T, s * x * s⁻¹ = x → x = 1 := by
  obtain ⟨s, hsN, hsT⟩ := h.exists_mem_normalizer_not_mem
  refine ⟨s, hsN, fun x hx hfix => ?_⟩
  by_contra hx1
  apply hsT
  refine h.centralizer_le x hx hx1 s ?_
  calc s * x = s * x * s⁻¹ * s := by group
    _ = x * s := by rw [hfix]

theorem mem_of_mem_normalizer_pow [Finite G] (h : Sz32Data G T) {z : G}
    (hz : z ∈ Subgroup.normalizer (T : Set G)) (hz25 : z ^ 25 = 1) : z ∈ T := by
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := T.subgroupOf N
  have hHcard : Nat.card H = 25 := by
    rw [← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hidx : H.index = 4 := by
    have := H.index_mul_card
    rw [hHcard, h.card_normalizer] at this
    omega
  have hq4 : ∀ q : N ⧸ H, q ^ 4 = 1 := by
    intro q
    have := pow_card_eq_one' (G := N ⧸ H) (x := q)
    rwa [show Nat.card (N ⧸ H) = 4 from hidx] at this
  have hq25 : ((⟨z, hz⟩ : N) : N ⧸ H) ^ 25 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨z, hz⟩ : N) ^ 25 = 1 := Subtype.ext (by simpa using hz25)
    rw [this]
    rfl
  have hq1 : ((⟨z, hz⟩ : N) : N ⧸ H) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hq25
    have h2 := orderOf_dvd_of_pow_eq_one (hq4 ((⟨z, hz⟩ : N) : N ⧸ H))
    have h3 : orderOf (((⟨z, hz⟩ : N) : N ⧸ H)) ∣ Nat.gcd 25 4 := Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (by simpa using h3))
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq1)

theorem pow_25_eq_one (h : Sz32Data G T) {x : G} (hx : x ∈ T) : x ^ 25 = 1 := by
  have hTfin : Finite T := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  have h25 := pow_card_eq_one' (G := T) (x := (⟨x, hx⟩ : T))
  rw [h.card_eq] at h25
  simpa using congrArg Subtype.val h25


theorem maximal [Finite G] (h : Sz32Data G T) {Y : Subgroup G}
    (hY : Subgroup.normalizer (T : Set G) ≤ Y) :
    Y = Subgroup.normalizer (T : Set G) ∨ Y = ⊤ := by
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hTY : T ≤ Y := hTN.trans hY
  let H : Subgroup Y := N.subgroupOf Y
  let S : Subgroup Y := T.subgroupOf Y
  have hScard : Nat.card S = 25 := by
    rw [← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv
  have hS : ∀ s : S, ((s : Y) : G) ∈ T := fun s => Subgroup.mem_subgroupOf.1 s.2
  have hfinS : Finite S := Nat.finite_of_card_ne_zero (by rw [hScard]; norm_num)
  have hmod : Nat.card (Y ⧸ H) ≡ 1 [MOD Nat.card S] := by
    refine L28Local.card_modEq_one_of_free (S := S) (X := Y ⧸ H) ((1 : Y) : Y ⧸ H) ?_ ?_
    · intro s
      change (((s : Y) * 1 : Y) : Y ⧸ H) = ((1 : Y) : Y ⧸ H)
      rw [QuotientGroup.eq]
      exact Subgroup.mem_subgroupOf.2 (by simpa using hTN (T.inv_mem (hS s)))
    · intro x hx s hsx
      by_contra hs1
      induction x using QuotientGroup.induction_on with
      | _ y =>
        change (((s : Y) * y : Y) : Y ⧸ H) = (y : Y ⧸ H) at hsx
        rw [QuotientGroup.eq] at hsx
        have hsx' : (y : G)⁻¹ * ((s : Y) : G)⁻¹ * (y : G) ∈ N := by
          have := Subgroup.mem_subgroupOf.1 hsx
          simpa [mul_assoc] using this
        have hs1' : ((s : Y) : G) ≠ 1 := fun h1 => hs1 (Subtype.ext (Subtype.ext h1))
        have hz25 : ((y : G)⁻¹ * ((s : Y) : G)⁻¹ * (y : G)) ^ 25 = 1 := by
          have h25 : (((s : Y) : G)⁻¹) ^ 25 = 1 := by
            rw [inv_pow, h.pow_25_eq_one (hS s), inv_one]
          have := conj_pow (a := (y : G)⁻¹) (b := ((s : Y) : G)⁻¹) (i := 25)
          simp only [inv_inv] at this
          rw [this, h25]
          group
        have hzT := h.mem_of_mem_normalizer_pow hsx' hz25
        have hyN := h.mem_normalizer_of_conj_mem (T.inv_mem (hS s)) (inv_ne_one.2 hs1') hzT
        apply hx
        rw [QuotientGroup.eq]
        exact Subgroup.mem_subgroupOf.2 (by simpa using N.inv_mem hyN)
  rw [hScard] at hmod
  have hidx : N.index = 325376 := by
    have := N.card_mul_index
    rw [h.card_normalizer, h.card_group] at this
    omega
  have hdvd : N.relIndex Y ∣ 325376 := hidx ▸ Subgroup.relIndex_dvd_index_of_le hY
  have hn : N.relIndex Y = Nat.card (Y ⧸ H) := rfl
  rw [← hn] at hmod
  rcases divisor_cases hdvd hmod with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h1) hY)
  · right
    have := Subgroup.relIndex_mul_index hY
    rw [h1, hidx] at this
    exact Subgroup.index_eq_one.1 (by omega)

theorem eq_bot_of_normal [Finite G] (h : Sz32Data G T) {M : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (T : Set G))
    (hM : (M.subgroupOf (Subgroup.normalizer (T : Set G))).Normal)
    (hcop : Nat.Coprime 5 (Nat.card M)) : M = ⊥ := by
  have hMT : M ⊓ T = ⊥ := by
    have h25 : Nat.Coprime 25 (Nat.card M) := by
      simpa using Nat.Coprime.pow_left 2 hcop
    have h1 : Nat.card (M ⊓ T : Subgroup G) ∣ Nat.card M := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (M ⊓ T : Subgroup G) ∣ 25 :=
      h.card_eq ▸ Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card (M ⊓ T : Subgroup G) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 h25) h1
    exact Subgroup.card_eq_one.1 h3
  have hcomm : ∀ m ∈ M, ∀ u ∈ T, m * u = u * m := by
    intro m hm u hu
    have huN : u ∈ Subgroup.normalizer (T : Set G) := Subgroup.le_normalizer hu
    have h1 : m * u * m⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hMN hm) u).1 hu
    have h2 : u * m⁻¹ * u⁻¹ ∈ M := by
      have := hM.conj_mem ⟨m⁻¹, hMN (M.inv_mem hm)⟩
        (Subgroup.mem_subgroupOf.2 (M.inv_mem hm)) ⟨u, huN⟩
      exact Subgroup.mem_subgroupOf.1 this
    have hc : m * u * m⁻¹ * u⁻¹ ∈ M ⊓ T :=
      ⟨by
        have := M.mul_mem hm h2
        simpa [mul_assoc] using this,
       T.mul_mem h1 (T.inv_mem hu)⟩
    rw [hMT, Subgroup.mem_bot] at hc
    have : m * u * m⁻¹ = u := by
      have := congrArg (· * u) hc
      simpa [mul_assoc] using this
    calc m * u = m * u * m⁻¹ * m := by group
      _ = u * m := by rw [this]
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  have hmT : m ∈ T := h.centralizer_le t ht ht1 m (hcomm m hm t ht)
  have : m ∈ M ⊓ T := ⟨hm, hmT⟩
  rwa [hMT] at this

theorem isSolvable_normalizer [Finite G] (h : Sz32Data G T) :
    Group.IsSolvable (Subgroup.normalizer (T : Set G)) := by
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  let H : Subgroup N := T.subgroupOf N
  have hHcard : Nat.card H = 25 := by
    rw [← h.card_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have hidx : H.index = 4 := by
    have := H.index_mul_card
    rw [hHcard, h.card_normalizer] at this
    omega
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinN : Finite N := Nat.finite_of_card_ne_zero (by rw [h.card_normalizer]; norm_num)
  have hH : Group.IsSolvable H :=
    haveI : IsPGroup 5 H := IsPGroup.of_card (n := 2) (by rw [hHcard]; norm_num)
    haveI := this.isNilpotent
    inferInstance
  have hQ : Group.IsSolvable (N ⧸ H) :=
    haveI : IsPGroup 2 (N ⧸ H) :=
      IsPGroup.of_card (n := 2) (by rw [show Nat.card (N ⧸ H) = 4 from hidx]; norm_num)
    haveI := this.isNilpotent
    inferInstance
  exact Group.isSolvable_of_ker_le_range H.subtype (QuotientGroup.mk' H)
    (by simp [QuotientGroup.ker_mk'])

theorem conj_injective [Finite G] (h : Sz32Data G T) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hc : ∀ x : G, g * x = x * g := fun x => by
    have := congrArg (fun α : MulAut G => α x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [this]
  obtain ⟨t, ht, ht1⟩ := h.exists_ne_one
  have hgT : g ∈ T := h.centralizer_le t ht ht1 g (hc t)
  obtain ⟨s, -, hs⟩ := h.exists_fixed_point_free
  rw [Subgroup.mem_bot]
  exact hs g hgT (by
    calc s * g * s⁻¹ = g * s * s⁻¹ := by rw [hc s]
      _ = g := by group)


theorem center_eq_bot [Finite G] (h : Sz32Data G T) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  refine h.conj_injective ?_
  rw [map_one]
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.conj_apply, MulAut.one_apply]
  have := Subgroup.mem_center_iff.1 hg x
  calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [this]
    _ = x := by group

theorem aut {K : Type} [Group K] [Finite K] {T : Subgroup K} (h : Sz32Data K T)
    (hSz : SzSylow K) (hsimple : IsSimpleGroup K)
    (hOut : (inner K).index ∣ 5)
    {f : MulAut K} (hf : ∀ x ∈ T, f x = x) : ∃ t ∈ T, f = MulAut.conj t := by
  classical
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfinM : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  obtain ⟨t₀, ht₀, ht₀1⟩ := h.exists_ne_one
  have hconj := h.conj_injective
  set I : Subgroup (MulAut K) := inner K with hI
  have hfk : ∀ k : ℕ, ∀ x ∈ T, (f ^ k) x = x := by
    intro k x hx
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hf x hx, ih]
  have hf5 : f ^ 5 ∈ I := by
    obtain ⟨c, hc⟩ := hOut
    rw [hc, pow_mul]
    exact I.pow_mem (Subgroup.pow_index_mem I f) c
  obtain ⟨n, hn⟩ := hf5
  have hnT : n ∈ T := by
    have h1 := hfk 5 t₀ ht₀
    rw [← hn] at h1
    simp only [MulAut.conj_apply] at h1
    refine h.centralizer_le t₀ ht₀ ht₀1 n ?_
    calc n * t₀ = n * t₀ * n⁻¹ * n := by group
      _ = t₀ * n := by rw [h1]
  have hf125 : f ^ 5 ^ 3 = 1 := by
    rw [show 5 ^ 3 = 5 * 25 by norm_num, pow_mul, ← hn, ← map_pow, h.pow_25_eq_one hnT, map_one]
  by_cases hfI : f ∈ I
  · obtain ⟨k, hk⟩ := hfI
    refine ⟨k, ?_, hk.symm⟩
    have h1 := hf t₀ ht₀
    rw [← hk] at h1
    simp only [MulAut.conj_apply] at h1
    refine h.centralizer_le t₀ ht₀ ht₀1 k ?_
    calc k * t₀ = k * t₀ * k⁻¹ * k := by group
      _ = t₀ * k := by rw [h1]
  · exfalso
    let eS : K ≃* ↥I := MonoidHom.ofInjective hconj
    have hSzI : SzSylow ↥I := SzSylow.of_mulEquiv eS.symm hSz
    have hsimpleI : IsSimpleGroup ↥I := by
      have := hsimple
      exact MulEquiv.isSimpleGroup eS.symm
    have hC : Subgroup.centralizer (I : Set (MulAut K)) = ⊥ :=
      CFSG.RankThree.PartOne.K159F.centralizer_inner_eq_bot h.center_eq_bot
    set Tbar : Subgroup (MulAut K) := T.map (MulAut.conj : K →* MulAut K) with hTbar
    have hTbarI : Tbar ≤ I := by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    have hTbarcard : Nat.card Tbar = 25 := by
      rw [hTbar, Subgroup.card_map_of_injective hconj, h.card_eq]
    have hTbarp : IsPGroup 5 Tbar := IsPGroup.of_card (n := 2) (by rw [hTbarcard]; norm_num)
    have hTcomm : ∀ x ∈ Tbar, ∀ y ∈ Tbar, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h.commute x hx y hy]
    have hfT : ∀ x ∈ Tbar, x * f = f * x := by
      rintro _ ⟨x, hx, rfl⟩
      refine MulEquiv.ext fun y => ?_
      show (MulAut.conj x) (f y) = f ((MulAut.conj x) y)
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hf x hx]
    have hfp : IsPGroup 5 (Subgroup.zpowers f) :=
      isPGroup_zpowers_of_pow_eq_one (k := 3) (by norm_num) hf125
    have hQcomm : ∀ a ∈ Tbar, ∀ b ∈ Subgroup.zpowers f, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((Commute.zpow_right (show Commute a f from hfT a ha) m)).eq
    set Q : Subgroup (MulAut K) := Tbar ⊔ Subgroup.zpowers f with hQ
    have hQp : IsPGroup 5 Q := isPGroup_sup_of_commute hTbarp hfp hQcomm
    have hTQ : Tbar ≤ Q := le_sup_left
    have hfQ : f ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
    have hfT' : f ∉ Tbar := fun hh => hfI (hTbarI hh)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hQp
    have hgt : 25 < Nat.card Q := by
      by_contra hle
      push Not at hle
      have : Tbar = Q := Subgroup.eq_of_le_of_card_ge hTQ (by rw [hTbarcard]; exact hle)
      exact hfT' (this ▸ hfQ)
    have h125 : 125 ∣ Nat.card Q := by
      rw [hm] at hgt ⊢
      have h3 : 3 ≤ m := by
        by_contra hh
        push Not at hh
        interval_cases m <;> omega
      have := pow_dvd_pow 5 h3
      simpa using this
    have hcommQ : ∀ x ∈ Q, ∀ t ∈ Tbar, x * t = t * x := by
      have hle : Q ≤ Subgroup.centralizer (Tbar : Set (MulAut K)) := by
        refine sup_le ?_ ?_
        · intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          exact (hTcomm t ht x hx)
        · intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          exact (hQcomm t ht x hx)
      intro x hx t ht
      exact (Subgroup.mem_centralizer_iff.1 (hle hx) t ht).symm
    exact sz_core hSzI hsimpleI hC hTbarI hTbarcard hQp hTQ h125 hcommQ

theorem eq_one_of_fixes_normalizer {K : Type} [Group K] [Finite K] {T : Subgroup K}
    (h : Sz32Data K T) (hSz : SzSylow K) (hsimple : IsSimpleGroup K)
    (hOut : (inner K).index ∣ 5) {f : MulAut K}
    (hf : ∀ k ∈ Subgroup.normalizer (T : Set K), f k = k) : f = 1 := by
  obtain ⟨t, htT, rfl⟩ := h.aut hSz hsimple hOut (fun x hx => hf x (Subgroup.le_normalizer hx))
  obtain ⟨s, hsN, hs⟩ := h.exists_fixed_point_free
  have h1 : t * s * t⁻¹ = s := by simpa [MulAut.conj_apply] using hf s hsN
  have h2 : t * s = s * t := by
    calc t * s = t * s * t⁻¹ * t := by group
      _ = s * t := by rw [h1]
  have : t = 1 := hs t htT (by
    calc s * t * s⁻¹ = t * s * s⁻¹ := by rw [h2]
      _ = t := by group)
  rw [this, map_one]

theorem isPGroup_stabilizer {K : Type*} [Group K] [Finite K]
    (hdata : ∀ T : Sylow 5 K, Sz32Data K (T : Subgroup K))
    (hOut : (inner K).index ∣ 5) {t : K} (ht : orderOf t = 5) :
    IsPGroup 5 (MulAction.stabilizer (MulAut K) t) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨T, htT⟩ : ∃ T : Sylow 5 K, t ∈ (T : Subgroup K) := by
    have hp : IsPGroup 5 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
    obtain ⟨T, hT⟩ := hp.exists_le_sylow
    exact ⟨T, hT (Subgroup.mem_zpowers t)⟩
  have hd := hdata T
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; omega
  intro f
  refine ⟨3, ?_⟩
  have hft : (f : MulAut K) t = t := by
    simpa [MulAut.smul_def] using MulAction.mem_stabilizer_iff.1 f.2
  have hfk : ∀ k : ℕ, ((f : MulAut K) ^ k) t = t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hft, ih]
  have h5 : (f : MulAut K) ^ 5 ∈ inner K := by
    obtain ⟨c, hc⟩ := hOut
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem (inner K) (f : MulAut K)) c
  obtain ⟨n, hn⟩ := h5
  have hnt : n * t = t * n := by
    have h1 := hfk 5
    rw [← hn] at h1
    simp only [MulAut.conj_apply] at h1
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h1]
  have hnT : n ∈ (T : Subgroup K) := hd.centralizer_le t htT ht1 n hnt
  have hn25 : n ^ 25 = 1 := hd.pow_25_eq_one hnT
  apply Subtype.ext
  rw [Subgroup.coe_pow, show 5 ^ 3 = 5 * 25 by norm_num, pow_mul, ← hn, ← map_pow, hn25, map_one]
  rfl

end Sz32Data

end CFSG.AGLEmbedding.KFactProofs.Sz32Local
