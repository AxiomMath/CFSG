module

public import CFSG.GroupTheory.WielandtProductTools
public import CFSG.CharacterTheory.Burnside.CharacterObstruction

public section

namespace CFSG.GroupTheory.WielandtProduct

open Subgroup

@[expose] def WielandtFor (X : Type) [Group X] [Finite X] : Prop :=
  ∀ A B : Subgroup X, Group.IsNilpotent A → Group.IsNilpotent B →
    Nat.Coprime (Nat.card A) (Nat.card B) → (∀ g : X, ∃ a ∈ A, ∃ b ∈ B, g = a * b) →
      Group.IsSolvable X

structure MinCounter (G : Type) [Group G] [Finite G] (A B : Subgroup G) : Prop where
  nilA : Group.IsNilpotent A
  nilB : Group.IsNilpotent B
  cop : Nat.Coprime (Nat.card A) (Nat.card B)
  mul : ∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b
  not_solvable : ¬ Group.IsSolvable G
  ih : ∀ (X : Type) [Group X] [Finite X], Nat.card X < Nat.card G → WielandtFor X

@[expose] def zOf {G : Type*} [Group G] (A : Subgroup G) : Subgroup G :=
  A ⊓ centralizer (A : Set G)

theorem mem_zOf {G : Type*} [Group G] {A : Subgroup G} {z : G} :
    z ∈ zOf A ↔ z ∈ A ∧ ∀ y ∈ A, Commute z y := by
  rw [zOf, mem_inf, mem_centralizer_iff]
  exact and_congr_right fun _ => forall₂_congr fun y _ => eq_comm

theorem exists_pow_prime_orderOf {G : Type*} [Group G] [Finite G] {x : G} (hx : x ≠ 1) :
    ∃ k : ℕ, (orderOf (x ^ k)).Prime := by
  have h0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  have h1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd h1
  exact ⟨orderOf x / p, by rw [orderOf_pow_orderOf_div h0 hpx]; exact hp⟩

theorem mem_sylowOf_subgroupOf {G : Type*} [Group G] [Finite G] {A K : Subgroup G} {p : ℕ}
    [Fact p.Prime] [Group.IsNilpotent A] [Group.IsNilpotent (A.subgroupOf K)] {x : K} :
    x ∈ sylowOf (A.subgroupOf K) p ↔ (x : G) ∈ sylowOf A p := by
  rw [mem_sylowOf_iff, mem_sylowOf_iff, mem_subgroupOf]
  refine and_congr_right fun _ => exists_congr fun k => ?_
  constructor
  · intro hk
    simpa using congrArg Subtype.val hk
  · intro hk
    exact Subtype.ext (by simpa using hk)

theorem le_normalizer_zpowers {G : Type*} [Group G] {A : Subgroup G} {a : G} (ha : a ∈ zOf A) :
    A ≤ normalizer (zpowers a : Set G) := by
  intro y hy
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  exact (((mem_zOf.mp ha).2 y hy).zpow_left n).eq

theorem subgroupOf_nilpotent_dvd {G : Type*} [Group G] (K : Subgroup G) (A' : Subgroup G)
    [Group.IsNilpotent A'] :
    Group.IsNilpotent (A'.subgroupOf K) ∧ Nat.card (A'.subgroupOf K) ∣ Nat.card A' := by
  let f : A'.subgroupOf K →* A' :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y hxy => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A' => (z : G)) hxy
  exact ⟨Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hf).symm,
    Subgroup.card_dvd_of_injective f hf⟩

theorem sylowOf_ne_bot {G : Type*} [Group G] [Finite G] {A : Subgroup G} {p : ℕ}
    [hp : Fact p.Prime] (hpA : p ∣ Nat.card A) :
    sylowOf A p ≠ ⊥ := by
  intro hb
  have hc := WielandtProduct.card_sylowOf (A := A) (p := p)
  rw [hb, card_bot] at hc
  have h0 : (Nat.card A).factorization p ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd hp.out Nat.card_pos.ne' hpA).ne'
  have := (Nat.pow_right_injective hp.out.two_le) (hc.symm.trans (pow_zero p).symm)
  exact h0 this

theorem exists_pow_mem_zOf {G : Type*} [Group G] [Finite G] {A : Subgroup G} {a : G}
    (ha : a ∈ zOf A) (ha1 : a ≠ 1) :
    ∃ k : ℕ, (orderOf (a ^ k)).Prime ∧ a ^ k ∈ zOf A ∧ a ^ k ≠ 1 ∧
      orderOf (a ^ k) ∣ Nat.card A := by
  obtain ⟨k, hk⟩ := exists_pow_prime_orderOf ha1
  refine ⟨k, hk, pow_mem ha k, fun h1 => hk.one_lt.ne' (by rw [h1, orderOf_one]), ?_⟩
  exact Subgroup.orderOf_dvd_natCard A (pow_mem (mem_zOf.mp ha).1 k)

namespace MinCounter

variable {G : Type} [Group G] [Finite G] {A B : Subgroup G} (h : MinCounter G A B)
include h

theorem symm : MinCounter G B A :=
  ⟨h.nilB, h.nilA, h.cop.symm, forall_mul_swap h.mul, h.not_solvable, h.ih⟩

theorem inf_eq_bot : A ⊓ B = ⊥ :=
  disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard h.cop)

theorem card_eq : Nat.card G = Nat.card A * Nat.card B :=
  card_eq_mul_of_forall_mul h.inf_eq_bot h.mul

theorem isSolvable_of_factorized {K : Subgroup G} (hK : K ≠ ⊤)
    (hfac : ∀ x ∈ K, ∃ a ∈ A ⊓ K, ∃ b ∈ B ⊓ K, x = a * b) : Group.IsSolvable K := by
  have := h.nilA
  have := h.nilB
  have hlt : Nat.card K < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group K) fun he =>
      hK ((Subgroup.card_eq_iff_eq_top K).mp he)
  obtain ⟨hnA, hdA⟩ := subgroupOf_nilpotent_dvd K A
  obtain ⟨hnB, hdB⟩ := subgroupOf_nilpotent_dvd K B
  refine h.ih K hlt (A.subgroupOf K) (B.subgroupOf K) hnA hnB
    (Nat.Coprime.of_dvd hdA hdB h.cop) fun x => ?_
  obtain ⟨a, ⟨ha, haK⟩, b, ⟨hb, hbK⟩, hx⟩ := hfac x x.2
  exact ⟨⟨a, haK⟩, ha, ⟨b, hbK⟩, hb, Subtype.ext hx⟩

theorem isSimpleGroup : IsSimpleGroup G := by
  have := h.nilA
  have := h.nilB
  have hnt : Nontrivial G := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact h.not_solvable (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)
  refine ⟨fun N hN => ?_⟩
  by_cases hNb : N = ⊥
  · exact Or.inl hNb
  right
  have hQ : Group.IsSolvable (G ⧸ N) := by
    have hlt : Nat.card (G ⧸ N) < Nat.card G := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
      exact lt_mul_of_one_lt_right Nat.card_pos
        ((Subgroup.one_lt_card_iff_ne_bot N).mpr hNb)
    refine h.ih (G ⧸ N) hlt (A.map (QuotientGroup.mk' N)) (B.map (QuotientGroup.mk' N))
      (Group.nilpotent_of_surjective _ ((QuotientGroup.mk' N).subgroupMap_surjective A))
      (Group.nilpotent_of_surjective _ ((QuotientGroup.mk' N).subgroupMap_surjective B))
      (Nat.Coprime.of_dvd (Subgroup.card_map_dvd _ _) (Subgroup.card_map_dvd _ _) h.cop)
      fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨a, ha, b, hb, rfl⟩ := h.mul g
    exact ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, map_mul _ _ _⟩
  have hNs : ¬ Group.IsSolvable N := fun hNs =>
    h.not_solvable (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', N.range_subtype]))
  have hsup : ∀ {A' B' : Subgroup G}, MinCounter G A' B' → A' ⊔ N = ⊤ := by
    intro A' B' h'
    by_contra hne
    have hsolv := h'.isSolvable_of_factorized hne (factorized_of_le h'.mul le_sup_left)
    exact hNs (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_right : N ≤ A' ⊔ N)))
  have hidx : ∀ {A' B' : Subgroup G}, MinCounter G A' B' → N.index ∣ Nat.card A' := by
    intro A' B' h'
    have e := Subgroup.relIndex_sup_right A' N
    rw [hsup h', Subgroup.relIndex_top_right] at e
    rw [e]
    exact Subgroup.relIndex_dvd_card N A'
  exact Subgroup.index_eq_one.mp (Nat.eq_one_of_dvd_coprimes h.cop (hidx h) (hidx h.symm))

theorem not_comm : ¬ ∀ x y : G, x * y = y * x := fun hc =>
  h.not_solvable (Group.isSolvable_of_comm hc)

theorem center_eq_bot : center G = ⊥ := by
  have := h.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
  · exact hc
  · exfalso
    apply h.not_comm
    intro x y
    have hx : x ∈ center G := hc ▸ mem_top x
    exact (mem_center_iff.mp hx y).symm

theorem ne_bot_left : A ≠ ⊥ := by
  have := h.nilB
  intro hA
  have hB : B = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨a, ha, b, hb, rfl⟩ := h.mul g
    rw [hA, mem_bot] at ha
    rw [ha, one_mul]
    exact hb
  have hn : Group.IsNilpotent G :=
    Group.nilpotent_of_mulEquiv ((MulEquiv.subgroupCongr hB).trans Subgroup.topEquiv)
  exact h.not_solvable inferInstance

theorem ne_bot_right : B ≠ ⊥ := h.symm.ne_bot_left

theorem ne_top_left : A ≠ ⊤ := by
  intro hA
  apply h.ne_bot_right
  have := h.inf_eq_bot
  rwa [hA, top_inf_eq] at this

theorem ne_top_right : B ≠ ⊤ := h.symm.ne_top_left

theorem normalizer_ne_top {N : Subgroup G} (hN : N ≠ ⊥) (hNAB : N ≤ A ∨ N ≤ B) :
    normalizer (N : Set G) ≠ ⊤ := by
  have := h.isSimpleGroup
  intro htop
  have hNn : N.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
  · exact hN hb
  · rcases hNAB with hA | hB
    · exact h.ne_top_left (top_le_iff.mp (ht ▸ hA))
    · exact h.ne_top_right (top_le_iff.mp (ht ▸ hB))

theorem not_dvd_right {p : ℕ} (hp : p.Prime) (hpA : p ∣ Nat.card A) : ¬ p ∣ Nat.card B :=
  fun hpB => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h.cop hpA hpB)

theorem card_sylowOf {p : ℕ} [hp : Fact p.Prime] (hpA : p ∣ Nat.card A) :
    Nat.card (sylowOf A p) = p ^ (Nat.card G).factorization p := by
  rw [WielandtProduct.card_sylowOf, h.card_eq,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (h.not_dvd_right hp.out hpA), add_zero]

noncomputable def sylow {p : ℕ} [Fact p.Prime] (hpA : p ∣ Nat.card A) : Sylow p G :=
  Sylow.ofCard (sylowOf A p) (h.card_sylowOf hpA)

theorem coe_sylow {p : ℕ} [Fact p.Prime] (hpA : p ∣ Nat.card A) :
    ((h.sylow hpA : Sylow p G) : Subgroup G) = sylowOf A p :=
  Sylow.coe_ofCard _ _

theorem le_normalizer_of_le_sylowOf {p : ℕ} [Fact p.Prime] {N : Subgroup G}
    (hN : N ≤ sylowOf A p) (hPN : sylowOf A p ≤ normalizer (N : Set G)) :
    A ≤ normalizer (N : Set G) := by
  have := h.nilA
  refine le_of_forall_sylowOf_le fun r hr => ?_
  have : Fact r.Prime := ⟨hr⟩
  by_cases hrp : r = p
  · subst hrp
    exact hPN
  · intro y hy
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro x hx
    exact (commute_of_mem_sylowOf_of_ne (A := A) hrp hy (hN hx)).eq.symm

theorem sylowOf_le_normalizer {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hrp : r ≠ p)
    {N : Subgroup G} (hN : N ≤ sylowOf A p) : sylowOf A r ≤ normalizer (N : Set G) := by
  have := h.nilA
  intro y hy
  apply centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro x hx
  exact (commute_of_mem_sylowOf_of_ne (A := A) hrp hy (hN hx)).eq.symm

theorem exists_mem_zOf_orderOf {p : ℕ} [hp : Fact p.Prime] (hpA : p ∣ Nat.card A) :
    ∃ z ∈ zOf A, orderOf z = p := by
  have := h.nilA
  have hc := Group.IsNilpotent.prime_dvd_card_center (G := A) hpA
  have := Fintype.ofFinite (center A)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := center A) p
    (by rwa [← Nat.card_eq_fintype_card])
  refine ⟨((z : A) : G), ?_, ?_⟩
  · rw [mem_zOf]
    refine ⟨(z : A).2, fun y hy => ?_⟩
    have := (mem_center_iff.mp z.2) ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  · rw [← hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe]

theorem exists_prime_ne {p : ℕ} (hp : p.Prime) :
    ∃ q : ℕ, q.Prime ∧ q ∣ Nat.card A ∧ q ≠ p := by
  by_contra hall
  push Not at hall
  have hAp : Nat.card A = p ^ (Nat.card A).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdA => hall _ hd hdA
  obtain ⟨r, hr, hrB⟩ := Nat.exists_prime_and_dvd fun h1 =>
    h.ne_bot_right ((Subgroup.card_eq_one).mp h1)
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hbZ, hbr⟩ := h.symm.exists_mem_zOf_orderOf hrB
  have hb1 : b ≠ 1 := fun hb => hr.one_lt.ne' (by rw [← hbr, hb, orderOf_one])
  have hBC : B ≤ centralizer ({b} : Set G) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    exact ((mem_zOf.mp hbZ).2 y hy).eq.symm
  have hidxB : B.index = Nat.card A := by
    have := B.card_mul_index
    rw [h.card_eq, mul_comm] at this
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
  have hdvd : (centralizer ({b} : Set G)).index ∣ p ^ (Nat.card A).primeFactorsList.length := by
    rw [← hAp, ← hidxB]
    exact Subgroup.index_dvd_of_le hBC
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have := h.isSimpleGroup
  have := Fintype.ofFinite G
  exact CFSG.Burnside.CharacterObstruction.no_prime_pow_conjClass h.not_comm b hb1 p k hp
    (by rw [card_conjClass_eq_index, hk])

theorem swap_of_factorized {K : Subgroup G} (hK : K ≠ ⊤)
    (hfac : ∀ x ∈ K, ∃ a ∈ A ⊓ K, ∃ b ∈ B ⊓ K, x = a * b) {p q : ℕ} [hp : Fact p.Prime]
    [hq : Fact q.Prime] (hpA : p ∣ Nat.card A) (hqB : q ∣ Nat.card B) :
    ∀ x ∈ (sylowOf A p ⊓ K) ⊔ (sylowOf B q ⊓ K),
      ∃ s ∈ sylowOf A p ⊓ K, ∃ t ∈ sylowOf B q ⊓ K, x = s * t := by
  have := h.nilA
  have := h.nilB
  obtain ⟨hnA, hdA⟩ := subgroupOf_nilpotent_dvd K A
  obtain ⟨hnB, hdB⟩ := subgroupOf_nilpotent_dvd K B
  have hsolv := h.isSolvable_of_factorized hK hfac
  have hmulK : ∀ g : K, ∃ a ∈ A.subgroupOf K, ∃ b ∈ B.subgroupOf K, g = a * b := by
    intro g
    obtain ⟨a, ⟨ha, haK⟩, b, ⟨hb, hbK⟩, hg⟩ := hfac g g.2
    exact ⟨⟨a, haK⟩, ha, ⟨b, hbK⟩, hb, Subtype.ext hg⟩
  have hcopK := Nat.Coprime.of_dvd hdA hdB h.cop
  have hcardK : Nat.card K = Nat.card (A.subgroupOf K) * Nat.card (B.subgroupOf K) :=
    card_eq_mul_of_forall_mul (disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopK)) hmulK
  have hpq : p ≠ q := fun he => h.not_dvd_right hp.out hpA (he ▸ hqB)
  have hpB' : ¬ p ∣ Nat.card (B.subgroupOf K) := fun hd =>
    h.not_dvd_right hp.out hpA (hd.trans hdB)
  have hqA' : ¬ q ∣ Nat.card (A.subgroupOf K) := fun hd =>
    h.symm.not_dvd_right hq.out hqB (hd.trans hdA)
  have hsw := swap_sylowOf_of_isSolvable hsolv hmulK hcardK hpq hpB' hqA'
  apply forall_mem_sup_of_swap
  rintro t ⟨htT, htK⟩ s ⟨hsS, hsK⟩
  obtain ⟨s', hs', t', ht', he⟩ := hsw ⟨t, htK⟩ (mem_sylowOf_subgroupOf.2 htT) ⟨s, hsK⟩
    (mem_sylowOf_subgroupOf.2 hsS)
  exact ⟨s', ⟨mem_sylowOf_subgroupOf.1 hs', s'.2⟩, t', ⟨mem_sylowOf_subgroupOf.1 ht', t'.2⟩,
    congrArg Subtype.val he⟩

theorem exists_normal_le_sylowOf {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpA : p ∣ Nat.card A) (hqB : q ∣ Nat.card B) {A₀ B₀ : Subgroup G}
    (hA₀ : A₀ ≤ sylowOf A p) (hA₀n : A ≤ normalizer (A₀ : Set G))
    (hB₀ : B₀ ≤ sylowOf B q) (hB₀n : B ≤ normalizer (B₀ : Set G))
    (hne : A₀ ⊔ B₀ ≠ ⊥) (hnt : A₀ ⊔ B₀ ≠ ⊤) :
    ∃ N : Subgroup G, N ≠ ⊥ ∧ A₀ ⊔ B₀ ≤ normalizer (N : Set G) ∧
      (N ≤ sylowOf A p ∨ N ≤ sylowOf B q) := by
  have := h.nilA
  have := h.nilB
  have := h.isSimpleGroup
  have hfac := factorized_normalizer_sup h.mul hA₀n hB₀n
  have hK : normalizer ((A₀ ⊔ B₀ : Subgroup G) : Set G) ≠ ⊤ := by
    intro hK
    have hHn : (A₀ ⊔ B₀).Normal := normalizer_eq_top_iff.mp hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A₀ ⊔ B₀) with hb | ht
    · exact hne hb
    · exact hnt ht
  have hsolv := h.isSolvable_of_factorized hK hfac
  set K := normalizer ((A₀ ⊔ B₀ : Subgroup G) : Set G) with hKdef
  have hHK : A₀ ⊔ B₀ ≤ K := le_normalizer
  have hH'n : ((A₀ ⊔ B₀).subgroupOf K).Normal := normal_in_normalizer
  have hH'ne : (A₀ ⊔ B₀).subgroupOf K ≠ ⊥ := by
    intro hb
    rw [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hHK] at hb
    exact hne hb
  obtain ⟨N', hN'n, hN'b, hN'H, r, hr, hN'r⟩ := exists_isPGroup_normal_le hsolv hH'n hH'ne
  have : Fact r.Prime := ⟨hr⟩
  set N := N'.map K.subtype with hNdef
  have hNH : N ≤ A₀ ⊔ B₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hN'H hx
  have hKN : K ≤ normalizer (N : Set G) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, hN'n.conj_mem y hy ⟨k, hk⟩, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩, ?_, ?_⟩
      · have := hN'n.conj_mem y hy ⟨k, hk⟩⁻¹
        simpa using this
      · have hyx' : (y : G) = k * x * k⁻¹ := hyx
        simp only [coe_subtype, coe_mul, coe_inv, hyx']
        group
  have hNb : N ≠ ⊥ := fun hb =>
    hN'b ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp hb)
  have hNr : IsPGroup r N := hN'r.map K.subtype
  have hpq : p ≠ q := fun he => h.not_dvd_right hp.out hpA (he ▸ hqB)
  have hsw := h.swap_of_factorized hK hfac hpA hqB
  have hHX : A₀ ⊔ B₀ ≤ (sylowOf A p ⊓ K) ⊔ (sylowOf B q ⊓ K) :=
    sup_le (le_sup_of_le_left (le_inf hA₀ (le_sup_left.trans hHK)))
      (le_sup_of_le_right (le_inf hB₀ (le_sup_right.trans hHK)))
  have hXK : (sylowOf A p ⊓ K) ⊔ (sylowOf B q ⊓ K) ≤ K := sup_le inf_le_right inf_le_right
  rcases le_or_le_of_isPGroup hpq (isPGroup_sylowOf.to_le inf_le_left)
      (isPGroup_sylowOf.to_le inf_le_left) hsw (hNH.trans hHX) (hXK.trans hKN) hNr hNb
    with hN | hN
  · exact ⟨N, hNb, hHK.trans hKN, Or.inl (hN.trans inf_le_left)⟩
  · exact ⟨N, hNb, hHK.trans hKN, Or.inr (hN.trans inf_le_left)⟩

theorem sylowOf_sup_sylowOf {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hpA : p ∣ Nat.card A) (hqB : q ∣ Nat.card B) : sylowOf A p ⊔ sylowOf B q = ⊤ := by
  have := h.nilA
  have := h.nilB
  have := h.isSimpleGroup
  by_contra hnt
  have hne : sylowOf A p ⊔ sylowOf B q ≠ ⊥ := fun hb =>
    sylowOf_ne_bot hpA (le_bot_iff.mp (hb ▸ le_sup_left))
  obtain ⟨N, hNb, hN, hNP | hNQ⟩ := h.exists_normal_le_sylowOf hpA hqB le_rfl
    le_normalizer_sylowOf le_rfl le_normalizer_sylowOf hne hnt
  · have hAN := h.le_normalizer_of_le_sylowOf hNP (le_sup_left.trans hN)
    have htop : A ⊔ sylowOf B q = ⊤ :=
      sup_eq_top_of_le_normalizer h.mul (sylowOf_ne_bot hqB) le_normalizer_sylowOf
    exact h.normalizer_ne_top hNb (Or.inl (hNP.trans sylowOf_le))
      (top_le_iff.mp (htop ▸ sup_le hAN (le_sup_right.trans hN)))
  · have hBN := h.symm.le_normalizer_of_le_sylowOf hNQ (le_sup_right.trans hN)
    have htop : B ⊔ sylowOf A p = ⊤ :=
      sup_eq_top_of_le_normalizer h.symm.mul (sylowOf_ne_bot hpA) le_normalizer_sylowOf
    exact h.normalizer_ne_top hNb (Or.inr (hNQ.trans sylowOf_le))
      (top_le_iff.mp (htop ▸ sup_le hBN (le_sup_left.trans hN)))

theorem zpowers_sup_sylowOf {a : G} (ha : a ∈ zOf A) (ha1 : a ≠ 1) {q : ℕ} [hq : Fact q.Prime]
    (hqB : q ∣ Nat.card B) : zpowers a ⊔ sylowOf B q = ⊤ := by
  have := h.nilA
  have := h.nilB
  have := h.isSimpleGroup
  obtain ⟨k, hk, ha'Z, ha'1, hpA⟩ := exists_pow_mem_zOf ha ha1
  have : Fact (orderOf (a ^ k)).Prime := ⟨hk⟩
  have ha'P : a ^ k ∈ sylowOf A (orderOf (a ^ k)) :=
    mem_sylowOf_of_orderOf_eq (mem_zOf.mp ha'Z).1 rfl
  have hle : zpowers (a ^ k) ≤ zpowers a := zpowers_le.mpr (pow_mem (mem_zpowers a) k)
  suffices hs : zpowers (a ^ k) ⊔ sylowOf B q = ⊤ from
    top_le_iff.mp (hs ▸ sup_le_sup_right hle _)
  have hZb : zpowers (a ^ k) ≠ ⊥ := fun hb => ha'1 (zpowers_eq_bot.mp hb)
  by_contra hnt
  have hne : zpowers (a ^ k) ⊔ sylowOf B q ≠ ⊥ := fun hb =>
    hZb (le_bot_iff.mp (hb ▸ le_sup_left))
  obtain ⟨N, hNb, hN, hNP | hNQ⟩ := h.exists_normal_le_sylowOf hpA hqB
    (zpowers_le.mpr ha'P) (le_normalizer_zpowers ha'Z) le_rfl le_normalizer_sylowOf hne hnt
  · obtain ⟨r, hr, hrA, hrp⟩ := h.exists_prime_ne hk
    have : Fact r.Prime := ⟨hr⟩
    have htop := h.sylowOf_sup_sylowOf hrA hqB
    exact h.normalizer_ne_top hNb (Or.inl (hNP.trans sylowOf_le))
      (top_le_iff.mp (htop ▸ sup_le (h.sylowOf_le_normalizer hrp hNP) (le_sup_right.trans hN)))
  · have hBN := h.symm.le_normalizer_of_le_sylowOf hNQ (le_sup_right.trans hN)
    have htop : B ⊔ zpowers (a ^ k) = ⊤ :=
      sup_eq_top_of_le_normalizer h.symm.mul hZb (le_normalizer_zpowers ha'Z)
    exact h.normalizer_ne_top hNb (Or.inr (hNQ.trans sylowOf_le))
      (top_le_iff.mp (htop ▸ sup_le hBN (le_sup_left.trans hN)))

theorem zpowers_sup_zpowers {a b : G} (ha : a ∈ zOf A) (ha1 : a ≠ 1) (hb : b ∈ zOf B)
    (hb1 : b ≠ 1) : zpowers a ⊔ zpowers b = ⊤ := by
  have := h.nilA
  have := h.nilB
  have := h.isSimpleGroup
  obtain ⟨k, hk, ha'Z, ha'1, hpA⟩ := exists_pow_mem_zOf ha ha1
  obtain ⟨l, hl, hb'Z, hb'1, hqB⟩ := exists_pow_mem_zOf hb hb1
  have : Fact (orderOf (a ^ k)).Prime := ⟨hk⟩
  have : Fact (orderOf (b ^ l)).Prime := ⟨hl⟩
  have ha'P : a ^ k ∈ sylowOf A (orderOf (a ^ k)) :=
    mem_sylowOf_of_orderOf_eq (mem_zOf.mp ha'Z).1 rfl
  have hb'Q : b ^ l ∈ sylowOf B (orderOf (b ^ l)) :=
    mem_sylowOf_of_orderOf_eq (mem_zOf.mp hb'Z).1 rfl
  have hlea : zpowers (a ^ k) ≤ zpowers a := zpowers_le.mpr (pow_mem (mem_zpowers a) k)
  have hleb : zpowers (b ^ l) ≤ zpowers b := zpowers_le.mpr (pow_mem (mem_zpowers b) l)
  suffices hs : zpowers (a ^ k) ⊔ zpowers (b ^ l) = ⊤ from
    top_le_iff.mp (hs ▸ sup_le_sup hlea hleb)
  have hZb : zpowers (a ^ k) ≠ ⊥ := fun hb => ha'1 (zpowers_eq_bot.mp hb)
  by_contra hnt
  have hne : zpowers (a ^ k) ⊔ zpowers (b ^ l) ≠ ⊥ := fun hb =>
    hZb (le_bot_iff.mp (hb ▸ le_sup_left))
  obtain ⟨N, hNb, hN, hNP | hNQ⟩ := h.exists_normal_le_sylowOf hpA hqB
    (zpowers_le.mpr ha'P) (le_normalizer_zpowers ha'Z) (zpowers_le.mpr hb'Q)
    (le_normalizer_zpowers hb'Z) hne hnt
  · obtain ⟨r, hr, hrA, hrp⟩ := h.exists_prime_ne hk
    have : Fact r.Prime := ⟨hr⟩
    have htop := h.symm.zpowers_sup_sylowOf hb'Z hb'1 hrA
    exact h.normalizer_ne_top hNb (Or.inl (hNP.trans sylowOf_le))
      (top_le_iff.mp (htop ▸ sup_le (le_sup_right.trans hN) (h.sylowOf_le_normalizer hrp hNP)))
  · obtain ⟨r, hr, hrB, hrq⟩ := h.symm.exists_prime_ne hl
    have : Fact r.Prime := ⟨hr⟩
    have htop := h.zpowers_sup_sylowOf ha'Z ha'1 hrB
    exact h.normalizer_ne_top hNb (Or.inr (hNQ.trans sylowOf_le))
      (top_le_iff.mp (htop ▸ sup_le (le_sup_left.trans hN)
        (h.symm.sylowOf_le_normalizer hrq hNQ)))

theorem centralizer_eq {a : G} (ha : a ∈ zOf A) (ha1 : a ≠ 1) :
    centralizer ({a} : Set G) = A := by
  have := h.nilA
  have := h.nilB
  have hAC : A ≤ centralizer ({a} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr ((mem_zOf.mp ha).2 y hy).eq.symm
  refine le_antisymm (fun x hx => ?_) hAC
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h.mul x
  have hb₁C : b₁ ∈ centralizer ({a} : Set G) := by
    have := mul_mem (inv_mem (hAC ha₁)) hx
    simpa using this
  by_cases hb1 : b₁ = 1
  · rw [hb1, mul_one]
    exact ha₁
  exfalso
  obtain ⟨k, hk⟩ := exists_pow_prime_orderOf hb1
  have : Fact (orderOf (b₁ ^ k)).Prime := ⟨hk⟩
  have hb₂B : b₁ ^ k ∈ B := pow_mem hb₁ k
  have hb₂1 : b₁ ^ k ≠ 1 := fun h1 => hk.one_lt.ne' (by rw [h1, orderOf_one])
  have hqB : orderOf (b₁ ^ k) ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B hb₂B
  have hb₂Q : b₁ ^ k ∈ sylowOf B (orderOf (b₁ ^ k)) := mem_sylowOf_of_orderOf_eq hb₂B rfl
  obtain ⟨r, hr, hrB, hrq⟩ := h.symm.exists_prime_ne hk
  have : Fact r.Prime := ⟨hr⟩
  have hle : zpowers a ⊔ sylowOf B r ≤ centralizer ({b₁ ^ k} : Set G) := by
    refine sup_le (zpowers_le.mpr ?_) fun y hy => ?_
    · rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_singleton_iff.mp (pow_mem hb₁C k)).symm
    · rw [mem_centralizer_singleton_iff]
      exact (commute_of_mem_sylowOf_of_ne (A := B) hrq hy hb₂Q).eq
  have htop := h.zpowers_sup_sylowOf ha ha1 hrB
  have hcen : b₁ ^ k ∈ center G := by
    rw [mem_center_iff]
    intro g
    exact mem_centralizer_singleton_iff.mp (top_le_iff.mp (htop ▸ hle) ▸ mem_top g)
  rw [h.center_eq_bot, mem_bot] at hcen
  exact hb₂1 hcen

end MinCounter

end CFSG.GroupTheory.WielandtProduct
