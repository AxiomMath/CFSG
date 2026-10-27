module

public import CFSG.Milestones.CTGMS_Bender_1971_even_rank_one_model_and_strong_embedding_input

public section

namespace CFSG.LargeExtraspecial.Asc77

open Subgroup CFSG.Open
open scoped MatrixGroups

theorem centralizer_le_of_stronglyEmbedded {B : Type*} [Group B] {N : Subgroup B}
    (hN : fusionStronglyEmbedded N) {x : B} (hx : orderOf x = 2) (hxN : x ∈ N) :
    centralizer ({x} : Set B) ≤ N := by
  intro g hg
  by_contra hgN
  have hodd := hN.2.2 g hgN
  have hgx : g⁻¹ * x * g = x := by
    rw [mem_centralizer_singleton_iff] at hg
    calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
      _ = g⁻¹ * (g * x) := by rw [hg]
      _ = x := by group
  have hx' : x ∈ N ⊓ N.map (MulAut.conj g⁻¹).toMonoidHom :=
    mem_inf.mpr ⟨hxN, ⟨x, hxN, by simp [hgx]⟩⟩
  have h2 : 2 ∣ Nat.card ↥(N ⊓ N.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rw [← hx, ← Subgroup.orderOf_mk x hx']
    exact orderOf_dvd_natCard _
  obtain ⟨r, hr⟩ := hodd
  omega

theorem isSolvable_of_sup_cyclic {B : Type*} [Group B] [Finite B] {T D N : Subgroup B}
    (hT : IsPGroup 2 T) (hTN : T ≤ N) (hDN : D ≤ N) (hTn : (T.subgroupOf N).Normal)
    (hD : IsCyclic D) (hsup : T ⊔ D = N) : Group.IsSolvable N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hTn
  have hT2 : IsPGroup 2 (T.subgroupOf N) :=
    hT.comap_of_injective (N.subtype) N.subtype_injective
  have : Group.IsNilpotent (T.subgroupOf N) := hT2.isNilpotent
  have hsup' : T.subgroupOf N ⊔ D.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTN hDN, hsup, subgroupOf_self]
  have hcomm : ∀ a b : N ⧸ T.subgroupOf N, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨t₁, ht₁, d₁, hd₁, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := T.subgroupOf N)).mp
      (hsup' ▸ mem_top a)
    obtain ⟨t₂, ht₂, d₂, hd₂, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := T.subgroupOf N)).mp
      (hsup' ▸ mem_top b)
    have hd : d₁ * d₂ = d₂ * d₁ := by
      have hc := hD.commGroup.mul_comm ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩
      apply Subtype.ext
      have := congrArg (fun x : D => (x : B)) hc
      simpa using this
    have e1 : ((t₁ * d₁ : N) : N ⧸ T.subgroupOf N) = (d₁ : N ⧸ T.subgroupOf N) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t₁).mpr ht₁, one_mul]
    have e2 : ((t₂ * d₂ : N) : N ⧸ T.subgroupOf N) = (d₂ : N ⧸ T.subgroupOf N) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t₂).mpr ht₂, one_mul]
    rw [e1, e2, ← QuotientGroup.mk_mul, hd, QuotientGroup.mk_mul]
  have : Group.IsSolvable (N ⧸ T.subgroupOf N) := Group.isSolvable_of_comm hcomm
  have : Group.IsSolvable (T.subgroupOf N) := inferInstance
  exact Group.isSolvable_of_ker_le_range (T.subgroupOf N).subtype
    (QuotientGroup.mk' (T.subgroupOf N)) (by rw [QuotientGroup.ker_mk', range_subtype])

theorem isSolvable_centralizer_of_fusionBenderBorel {B : Type*} [Group B] [Finite B] {q k : ℕ}
    (hB : fusionBenderBorel B q k) {x : B} (hx : orderOf x = 2) :
    Group.IsSolvable (centralizer ({x} : Set B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨T, hT⟩ := hx2.exists_le_sylow
  obtain ⟨hSE, ⟨D, hDc, -, -, hTDN⟩, -⟩ := hB T
  have hTN : (T : Subgroup B) ≤ normalizer ((T : Subgroup B) : Set B) := le_normalizer
  have hxN : x ∈ normalizer ((T : Subgroup B) : Set B) := hTN (hT (mem_zpowers x))
  have hDN : D ≤ normalizer ((T : Subgroup B) : Set B) := by
    rw [← hTDN]
    exact le_sup_right
  have hNs : Group.IsSolvable (normalizer ((T : Subgroup B) : Set B)) :=
    isSolvable_of_sup_cyclic T.isPGroup' hTN hDN normal_in_normalizer hDc hTDN
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (centralizer_le_of_stronglyEmbedded hSE hx hxN))

theorem isSolvable_centralizer_of_mulEquiv {K B : Type*} [Group K] [Group B] (e : K ≃* B)
    {x : K} (h : Group.IsSolvable (centralizer ({e x} : Set B))) :
    Group.IsSolvable (centralizer ({x} : Set K)) := by
  let f : centralizer ({x} : Set K) →* centralizer ({e x} : Set B) :=
    { toFun := fun c => ⟨e c, by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          mem_centralizer_singleton_iff.mp c.2]⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  exact Group.isSolvable_of_isSolvable_injective (f := f)
    fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab))

theorem isSolvable_centralizer_of_fusionIsBenderGroup {K : Type*}
    [Group K] [Finite K] (hK : fusionIsBenderGroup K) {x : K} (hx : orderOf x = 2) :
    Group.IsSolvable (centralizer ({x} : Set K)) := by
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv K e.toEquiv
    exact isSolvable_centralizer_of_mulEquiv e (isSolvable_centralizer_of_fusionBenderBorel
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf)
      (by rw [MulEquiv.orderOf_eq, hx]))
  · have : Finite (PSU3 2 f) := Finite.of_equiv K e.toEquiv
    exact isSolvable_centralizer_of_mulEquiv e (isSolvable_centralizer_of_fusionBenderBorel
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_2 f hf)
      (by rw [MulEquiv.orderOf_eq, hx]))
  · have : Finite (Sz a) := Finite.of_equiv K e.toEquiv
    exact isSolvable_centralizer_of_mulEquiv e (isSolvable_centralizer_of_fusionBenderBorel
      (CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_4 a ha)
      (by rw [MulEquiv.orderOf_eq, hx]))

theorem eq_of_sq_eq_one_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  classical
  have : Fintype C := Fintype.ofFinite C
  by_contra hxy
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hx
    · exact hy
  have hcard : ({1, x, y} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hx1, Ne.symm hy1⟩), Finset.card_pair hxy]
  have := Finset.card_le_card hsub
  change _ ≤ (Finset.univ.filter (fun a : C => a ^ 2 = 1)).card at this
  have h2 : (Finset.univ.filter (fun a : C => a ^ 2 = 1)).card ≤ 2 := by
    convert hle using 2
  omega

theorem eq_of_sq_eq_one_quaternion {n : ℕ} [NeZero n] {x y : QuaternionGroup n}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have han : (QuaternionGroup.a (n : ZMod (2 * n)) : QuaternionGroup n) ≠ 1 := by
    rw [← QuaternionGroup.a_one_pow]
    refine pow_ne_one_of_lt_orderOf (NeZero.ne n) ?_
    rw [QuaternionGroup.orderOf_a_one]
    have := NeZero.pos n
    omega
  have hmem : ∀ g : QuaternionGroup n, g ^ 2 = 1 → g ∈ zpowers (QuaternionGroup.a 1) := by
    intro g hg
    rcases g with i | i
    · refine Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), ?_⟩
      rw [zpow_natCast, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
    · rw [QuaternionGroup.xa_sq] at hg
      exact absurd hg han
  have := eq_of_sq_eq_one_of_isCyclic (C := zpowers (QuaternionGroup.a (1 : ZMod (2 * n))))
    (x := ⟨x, hmem x hx⟩) (y := ⟨y, hmem y hy⟩) (Subtype.ext (by simpa using hx))
    (Subtype.ext (by simpa using hy)) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem isSolvable_centralizer_of_stronglyEmbedded {L : Type}
    [Group L] [Finite L] [IsSimpleGroup L] {H : Subgroup L} (hH : fusionStronglyEmbedded H)
    {a b : L} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a * b = b * a) (hne : a ≠ b) {x : L} (hx : orderOf x = 2) :
    Group.IsSolvable (centralizer ({x} : Set L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2L : 2 ∣ Nat.card L := hx ▸ orderOf_dvd_natCard x
  rcases CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_3 L H
    hH with hS | ⟨M, N, hMn, hNn, hMNn, hMN, hModd, hNodd, hB⟩
  · exfalso
    set s : Set L := {a, b} with hsdef
    have hss : s ⊆ centralizer s := by
      intro u hu
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro v hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · rfl
      · exact hab.symm
      · exact hab
      · rfl
    have hEc : ∀ u ∈ closure s, ∀ v ∈ closure s, u * v = v * u := by
      intro u hu v hv
      have hu' := Subgroup.closure_le_centralizer_centralizer s hu
      have hv' : v ∈ centralizer s := (closure_le _).mpr hss hv
      exact (mem_centralizer_iff.mp hu' v hv').symm
    have hE2 : ∀ u ∈ closure s, u ^ 2 = 1 := by
      intro u hu
      induction hu using closure_induction with
      | mem u hu =>
        rcases hu with rfl | rfl
        · exact ha
        · exact hb
      | one => exact one_pow 2
      | mul u v hu hv ihu ihv =>
        rw [pow_two, show u * v * (u * v) = u * (v * u) * v by group, ← hEc u hu v hv,
          show u * (u * v) * v = (u * u) * (v * v) by group, ← pow_two, ← pow_two, ihu, ihv,
          one_mul]
      | inv u _ ih => rw [inv_pow, ih, inv_one]
    have hEp : IsPGroup 2 (closure s) := fun e =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (hE2 e e.2)⟩
    obtain ⟨S, hES⟩ := hEp.exists_le_sylow
    have haS : a ∈ (S : Subgroup L) := hES (subset_closure (Set.mem_insert a _))
    have hbS : b ∈ (S : Subgroup L) := hES (subset_closure (Set.mem_insert_of_mem a rfl))
    rcases hS S with hcyc | ⟨r, hr, ⟨e⟩⟩
    · have := eq_of_sq_eq_one_of_isCyclic (C := (S : Subgroup L)) (x := ⟨a, haS⟩)
        (y := ⟨b, hbS⟩) (Subtype.ext (by simpa using ha)) (Subtype.ext (by simpa using hb))
        (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
      exact hne (congrArg Subtype.val this)
    · have : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
      have := eq_of_sq_eq_one_quaternion (x := e ⟨a, haS⟩) (y := e ⟨b, hbS⟩)
        (by rw [← map_pow, show (⟨a, haS⟩ : (S : Subgroup L)) ^ 2 = 1 from
          Subtype.ext (by simpa using ha), map_one])
        (by rw [← map_pow, show (⟨b, hbS⟩ : (S : Subgroup L)) ^ 2 = 1 from
          Subtype.ext (by simpa using hb), map_one])
        (fun h => ha1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h)))
        (fun h => hb1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h)))
      exact hne (congrArg Subtype.val (e.injective this))
  · have hM : M = ⊥ := by
      rcases (haveI := hMn; IsSimpleGroup.eq_bot_or_eq_top_of_normal M) with h | h
      · exact h
      · exfalso
        rw [h, card_top] at hModd
        obtain ⟨k, hk⟩ := hModd
        omega
    have hN : N = ⊤ := by
      rcases (haveI := hNn; IsSimpleGroup.eq_bot_or_eq_top_of_normal N) with h | h
      · exfalso
        rw [h, index_bot] at hNodd
        obtain ⟨k, hk⟩ := hNodd
        omega
      · exact h
    subst hM hN
    have hbot : (⊥ : Subgroup L).subgroupOf ⊤ = ⊥ := bot_subgroupOf _
    let φ : L ≃* (↥(⊤ : Subgroup L) ⧸ (⊥ : Subgroup L).subgroupOf ⊤) :=
      Subgroup.topEquiv.symm.trans
        ((QuotientGroup.quotientBot).symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm))
    exact isSolvable_centralizer_of_mulEquiv φ
      (isSolvable_centralizer_of_fusionIsBenderGroup hB (by rw [MulEquiv.orderOf_eq, hx]))

end CFSG.LargeExtraspecial.Asc77
