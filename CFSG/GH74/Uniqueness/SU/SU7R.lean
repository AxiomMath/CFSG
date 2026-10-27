module

public import CFSG.GH74.Uniqueness.SU.SU7Claim
public import CFSG.GH74.Uniqueness.SU.SU7L191
public import CFSG.GH74.Uniqueness.SU.SU7Gen3

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5

namespace RF

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

theorem R_facts (hc : Ctx19 S U M V x z A B R) :
    Nat.card R = 32 ∧ z ∈ R ∧ ∀ n ∈ R, n * n = 1 ∨ n * n = z := by
  obtain ⟨hcard, ζ, hζR, hζ1, hcen, hsq⟩ := hc.c19.R_iso.facts
  have hzR : z ∈ R := (hc.c19.R_invol z hc.conf.hz).2 (Or.inl hc.c19.z_mem)
  have hzc : ∀ m ∈ R, z * m = m * z := fun m hm =>
    (hc.conf.z_center m (hc.c19.R_le hm)).symm
  have hzζ : z = ζ := by
    rcases (hcen z hzR).1 hzc with h | h
    · exact absurd h (Base.z_ne_one hc.conf)
    · exact h
  refine ⟨hcard, hzR, ?_⟩
  rw [hzζ]
  exact hsq

theorem mem_R_iff (hc : Ctx19 S U M V x z A B R) {r : G} (hr : r ∈ (S : Subgroup G)) :
    r ∈ R ↔ ((r * r = 1 ∧ (r ∈ U ∨ r ∉ Tsub S U)) ∨ r * r = z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 := Base.z_mul_self hc.conf
  have hz1 := Base.z_ne_one hc.conf
  obtain ⟨-, -, hsq⟩ := R_facts hc
  constructor
  · intro hrR
    rcases hsq r hrR with h | h
    · left
      refine ⟨h, ?_⟩
      by_cases hr1 : r = 1
      · left; rw [hr1]; exact U.one_mem
      · have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hr1
        rcases (hc.c19.R_invol r hord).1 hrR with hU | ⟨-, hT⟩
        · exact Or.inl hU
        · exact Or.inr hT
    · exact Or.inr h
  · rintro (⟨h, hUT⟩ | h)
    · by_cases hr1 : r = 1
      · rw [hr1]; exact R.one_mem
      · have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact h) hr1
        refine (hc.c19.R_invol r hord).2 ?_
        rcases hUT with hU | hT
        · exact Or.inl hU
        · exact Or.inr ⟨hr, hT⟩
    · have hr1 : r * r ≠ 1 := by rw [h]; exact hz1
      have h1 : r ^ 2 ≠ 1 := by rw [pow_two]; exact hr1
      have h2 : r ^ 4 = 1 := by
        have : r ^ 4 = (r * r) * (r * r) := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        rw [this, h, hz2]
      have hord : orderOf r = 4 := by
        have := orderOf_eq_prime_pow (x := r) (p := 2) (n := 1) (by simpa using h1)
          (by simpa using h2)
        simpa using this
      refine (hc.c19.R_four r hord).2 ⟨hr, ?_⟩
      rw [pow_two]; exact h

omit [Finite G] in
theorem cent_comm {g : G} (hg : g ∈ centralizer ({z} : Set G)) : g * z = z * g :=
  (mem_centralizer_iff.1 hg z (Set.mem_singleton z)).symm

theorem exists_u₀ (hc : Ctx19 S U M V x z A B R) : ∃ u ∈ U, u ≠ 1 ∧ u ≠ z := by
  have hU4 : Nat.card U = 4 := by rw [hc.hyp.four.2.2]; norm_num
  obtain ⟨t₁, ht₁, ht₁1, t₂, ht₂, ht₂1, ht₂₁⟩ := Gen.exists_two_ne_one_of_card_four hU4
  by_cases h : t₁ = z
  · exact ⟨t₂, ht₂, ht₂1, by rw [h] at ht₂₁; exact ht₂₁⟩
  · exact ⟨t₁, ht₁, ht₁1, h⟩

theorem U_cases (hc : Ctx19 S U M V x z A B R) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∀ p ∈ U, p = 1 ∨ p = z ∨ p = u ∨ p = z * u := by
  have hU4 : Nat.card U = 4 := by rw [hc.hyp.four.2.2]; norm_num
  have hzU := hc.c19.z_mem
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := (isElemAbelian_iff.1 hc.hyp.four.2.1).1
  exact Gen.eq_four_of_card hU4 hzU hu (Base.z_ne_one hc.conf) hu1 huz (Base.z_mul_self hc.conf)
    (hUc z hzU u hu)

theorem I_conj (hc : Ctx19 S U M V x z A B R) {u₀ : G} (hu₀U : u₀ ∈ U) (hu₀1 : u₀ ≠ 1)
    (hu₀z : u₀ ≠ z) {r : G} (hrR : r ∈ R) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hrz : r ≠ z) :
    ∃ g : G, g * z = z * g ∧ g⁻¹ * r * g = u₀ := by
  have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  have hxS := Base.x_mem_S hc.conf
  have hxT : x ∉ Tsub S U := hJ.x_not_mem
  have hx2 := hc.conf.hx
  have hl191 := lemma191 G S U M V x z A B R hc
  rcases (hc.c19.R_invol r hord).1 hrR with hrU | ⟨hrS, hrT⟩
  · rcases U_cases hc hu₀U hu₀1 hu₀z r hrU with h | h | h | h
    · exact absurd h hr1
    · exact absurd h hrz
    · exact ⟨1, by simp, by rw [h]; simp⟩
    · obtain ⟨g₁, hg₁C, hg₁⟩ := hl191 x hxS hxT hx2 r hrU hr1 hrz
      obtain ⟨g₂, hg₂C, hg₂⟩ := hl191 x hxS hxT hx2 u₀ hu₀U hu₀1 hu₀z
      have hg₁z : Commute g₁ z := cent_comm hg₁C
      have hg₂z : Commute g₂ z := cent_comm hg₂C
      refine ⟨g₁⁻¹ * g₂, (hg₁z.inv_left.mul_left hg₂z).eq, ?_⟩
      have h1 : g₁ * r * g₁⁻¹ = x := by rw [← hg₁]; group
      calc (g₁⁻¹ * g₂)⁻¹ * r * (g₁⁻¹ * g₂) = g₂⁻¹ * (g₁ * r * g₁⁻¹) * g₂ := by group
        _ = u₀ := by rw [h1]; exact hg₂
  · obtain ⟨g, hgC, hg⟩ := hl191 r hrS hrT hord u₀ hu₀U hu₀1 hu₀z
    exact ⟨g, cent_comm hgC, hg⟩

theorem sc (hKI3 : K.KI3) (hc : Ctx19 S U M V x z A B R) {r h : G} (hr : r ∈ R)
    (hhz : h * z = z * h) (hy : h⁻¹ * r * h ∈ (S : Subgroup G)) : h⁻¹ * r * h ∈ R := by
  have hz2 := Base.z_mul_self hc.conf
  have hzy : h⁻¹ * z * h = z := by
    calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
      _ = h⁻¹ * (h * z) := by rw [hhz]
      _ = z := by group
  have hhc : Commute h z := hhz
  obtain ⟨-, -, hsq⟩ := R_facts hc
  refine (mem_R_iff hc hy).2 ?_
  rcases hsq r hr with hr2 | hr2
  · left
    have hyy : (h⁻¹ * r * h) * (h⁻¹ * r * h) = 1 := by
      calc (h⁻¹ * r * h) * (h⁻¹ * r * h) = h⁻¹ * (r * r) * h := by group
        _ = 1 := by rw [hr2]; group
    refine ⟨hyy, ?_⟩
    by_cases hyT : h⁻¹ * r * h ∈ Tsub S U
    · left
      by_cases hr1 : r = 1
      · have : h⁻¹ * r * h = 1 := by rw [hr1]; group
        rw [this]; exact U.one_mem
      · have hord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
        obtain ⟨u₀, hu₀U, hu₀1, hu₀z⟩ := exists_u₀ hc
        rcases (hc.c19.R_invol r hord).1 hr with hrU | ⟨hrS, hrT⟩
        · by_cases hrz : r = z
          · have : h⁻¹ * r * h = z := by rw [hrz]; exact hzy
            rw [this]; exact hc.c19.z_mem
          · refine Claim.claim hKI3 hc.hyp hc.conf hc.concl hyT hyy (g₀ := h⁻¹) (u := r)
              hhc.inv_left.eq ?_ hrU hr1 hrz
            group
        · obtain ⟨g₁, hg₁C, hg₁⟩ := lemma191 G S U M V x z A B R hc r hrS hrT hord u₀ hu₀U hu₀1
            hu₀z
          have hg₁z : Commute g₁ z := cent_comm hg₁C
          refine Claim.claim hKI3 hc.hyp hc.conf hc.concl hyT hyy (g₀ := h⁻¹ * g₁) (u := u₀)
            (hhc.inv_left.mul_left hg₁z).eq ?_ hu₀U hu₀1 hu₀z
          calc (h⁻¹ * g₁)⁻¹ * (h⁻¹ * r * h) * (h⁻¹ * g₁) = g₁⁻¹ * r * g₁ := by group
            _ = u₀ := hg₁
    · right; exact hyT
  · right
    calc (h⁻¹ * r * h) * (h⁻¹ * r * h) = h⁻¹ * (r * r) * h := by group
      _ = z := by rw [hr2]; exact hzy

theorem I_eq (hc : Ctx19 S U M V x z A B R) :
    {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} =
      {g : G | g ∈ U ∧ g ≠ 1 ∧ g ≠ z} ∪
        {g : G | g ∈ (S : Subgroup G) ∧ g ∉ Tsub S U ∧ g ^ 2 = 1} := by
  have hz1 := Base.z_ne_one hc.conf
  have hUT : U ≤ Tsub S U := Base.U_le_T hc.hyp hc.conf hc.concl
  have hzT : z ∈ Tsub S U := hUT hc.c19.z_mem
  have hU2 : ∀ a ∈ U, a * a = 1 := fun a ha => by
    rw [← pow_two]; exact (isElemAbelian_iff.1 hc.hyp.four.2.1).2 a ha
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hgR, hg2, hg1, hgz⟩
    have hgS := hc.c19.R_le hgR
    have := (mem_R_iff hc hgS).1 hgR
    have hord : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
    rcases (hc.c19.R_invol g hord).1 hgR with hU | ⟨hgS', hT⟩
    · exact Or.inl ⟨hU, hg1, hgz⟩
    · exact Or.inr ⟨hgS', hT, by rw [pow_two]; exact hg2⟩
  · rintro (⟨hU, hg1, hgz⟩ | ⟨hgS, hT, hg2⟩)
    · have hgS : g ∈ (S : Subgroup G) := Base.T_le_S (hUT hU)
      exact ⟨(mem_R_iff hc hgS).2 (Or.inl ⟨hU2 g hU, Or.inl hU⟩), hU2 g hU, hg1, hgz⟩
    · have hg2' : g * g = 1 := by rw [← pow_two]; exact hg2
      have hg1 : g ≠ 1 := fun h => hT (by rw [h]; exact (Tsub S U).one_mem)
      have hgz : g ≠ z := fun h => hT (by rw [h]; exact hzT)
      exact ⟨(mem_R_iff hc hgS).2 (Or.inl ⟨hg2', Or.inr hT⟩), hg2', hg1, hgz⟩

theorem card_I (hc : Ctx19 S U M V x z A B R) :
    {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z}.ncard = 10 := by
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  have hz1 := Base.z_ne_one hc.conf
  have hUT : U ≤ Tsub S U := Base.U_le_T hc.hyp hc.conf hc.concl
  rw [I_eq hc, Set.ncard_union_eq]
  · have h2 : {g : G | g ∈ U ∧ g ≠ 1 ∧ g ≠ z}.ncard = 2 := by
      obtain ⟨u₀, hu₀U, hu₀1, hu₀z⟩ := exists_u₀ hc
      have hall := U_cases hc hu₀U hu₀1 hu₀z
      have hzu1 : z * u₀ ≠ 1 := by
        intro h
        apply hu₀z
        have : u₀ = z⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [this]; exact inv_eq_of_mul_eq_one_right (Base.z_mul_self hc.conf)
      have hzuz : z * u₀ ≠ z := by intro h; apply hu₀1; simpa using h
      have hne : u₀ ≠ z * u₀ := by
        intro h; apply hz1
        have : z * u₀ = 1 * u₀ := by rw [one_mul]; exact h.symm
        exact mul_right_cancel this
      have hset : {g : G | g ∈ U ∧ g ≠ 1 ∧ g ≠ z} = {u₀, z * u₀} := by
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hgU, hg1, hgz⟩
          rcases hall g hgU with h | h | h | h
          · exact absurd h hg1
          · exact absurd h hgz
          · exact Or.inl h
          · exact Or.inr h
        · rintro (rfl | rfl)
          · exact ⟨hu₀U, hu₀1, hu₀z⟩
          · exact ⟨U.mul_mem hc.c19.z_mem hu₀U, hzu1, hzuz⟩
      rw [hset, Set.ncard_pair hne]
    rw [h2, hJ.card_invol]
  · rw [Set.disjoint_left]
    rintro g ⟨hgU, -, -⟩ ⟨-, hgT, -⟩
    exact hgT (hUT hgU)

theorem I_gen (hc : Ctx19 S U M V x z A B R) :
    Subgroup.closure {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} = R := by
  have hJ := Base.j2facts hc.hyp hc.conf hc.concl
  have hemb := (Base.emb_zgen hc.hyp hc.conf hc.concl).1
  have hzgen := (Base.emb_zgen hc.hyp hc.conf hc.concl).2
  have hz1 := Base.z_ne_one hc.conf
  have hz2 := Base.z_mul_self hc.conf
  have hxS := Base.x_mem_S hc.conf
  have hxT : x ∉ Tsub S U := hJ.x_not_mem
  have hx2 := Base.x_mul_self hc.conf
  have hUT : U ≤ Tsub S U := Base.U_le_T hc.hyp hc.conf hc.concl
  have hzT : z ∈ Tsub S U := hUT hc.c19.z_mem
  have hmemZ := Base.mem_Zc_iff hc.hyp hc.conf hc.concl
  obtain ⟨-, hzR, hsq⟩ := R_facts hc
  have hxzc : x * z = z * x := hc.conf.z_center x hxS
  have hxI : x ∈ {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} := by
    refine ⟨(mem_R_iff hc hxS).2 (Or.inl ⟨hx2, Or.inr hxT⟩), hx2, Base.x_ne_one hc.conf, ?_⟩
    intro h; exact hxT (by rw [h]; exact hzT)
  have hxzI : x * z ∈ {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} := by
    have hxzS : x * z ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hxS (Base.z_mem_S hc.conf)
    have hxz2 : x * z * (x * z) = 1 := by
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [← hxzc]
        _ = (x * x) * (z * z) := by group
        _ = 1 := by rw [hx2, hz2, one_mul]
    have hxzT : x * z ∉ Tsub S U := by
      intro h
      apply hxT
      have : x = (x * z) * z⁻¹ := by group
      rw [this]; exact (Tsub S U).mul_mem h ((Tsub S U).inv_mem hzT)
    refine ⟨(mem_R_iff hc hxzS).2 (Or.inl ⟨hxz2, Or.inr hxzT⟩), hxz2, ?_, ?_⟩
    · intro h; exact hxzT (by rw [h]; exact (Tsub S U).one_mem)
    · intro h; apply Base.x_ne_one hc.conf
      have : x * z = 1 * z := by rw [h, one_mul]
      exact mul_right_cancel this
  have hzcl : z ∈ Subgroup.closure {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} := by
    have h := (Subgroup.closure _).mul_mem (Subgroup.subset_closure hxI)
      (Subgroup.subset_closure hxzI)
    have e : x * (x * z) = z := by
      calc x * (x * z) = (x * x) * z := by group
        _ = z := by rw [hx2, one_mul]
    rw [e] at h; exact h
  apply le_antisymm
  · rw [Subgroup.closure_le]; intro g hg; exact hg.1
  · intro r hr
    rcases hsq r hr with h | h
    · by_cases hr1 : r = 1
      · rw [hr1]; exact one_mem _
      · by_cases hrz : r = z
        · rw [hrz]; exact hzcl
        · exact Subgroup.subset_closure ⟨hr, h, hr1, hrz⟩
    · have hrS := hc.c19.R_le hr
      obtain ⟨s, hsS, hs2, hs1, hsz, hsU, hs'2, hs'1, hs'z, hs'U⟩ :=
        Model.gen_Rp hemb hzgen r hrS h
      have hss : s ∈ {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} := by
        refine ⟨(mem_R_iff hc hsS).2 (Or.inl ⟨hs2, ?_⟩), hs2, hs1, hsz⟩
        rcases hsU with h' | h'
        · exact Or.inl ((hmemZ s).1 h')
        · exact Or.inr h'
      have hs'S : s⁻¹ * r ∈ (S : Subgroup G) :=
        (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hsS) hrS
      have hs'I : s⁻¹ * r ∈ {g : G | g ∈ R ∧ g * g = 1 ∧ g ≠ 1 ∧ g ≠ z} := by
        refine ⟨(mem_R_iff hc hs'S).2 (Or.inl ⟨hs'2, ?_⟩), hs'2, hs'1, hs'z⟩
        rcases hs'U with h' | h'
        · exact Or.inl ((hmemZ _).1 h')
        · exact Or.inr h'
      have e : r = s * (s⁻¹ * r) := by group
      rw [e]
      exact (Subgroup.closure _).mul_mem (Subgroup.subset_closure hss)
        (Subgroup.subset_closure hs'I)

theorem sq_mem_R (hc : Ctx19 S U M V x z A B R) {s : G} (hs : s ∈ (S : Subgroup G)) :
    s * s ∈ R := by
  have hemb := (Base.emb_zgen hc.hyp hc.conf hc.concl).1
  have hzgen := (Base.emb_zgen hc.hyp hc.conf hc.concl).2
  have hmemZ := Base.mem_Zc_iff hc.hyp hc.conf hc.concl
  have hss : s * s ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hs hs
  refine (mem_R_iff hc hss).2 ?_
  rcases Model.sq_mem_Rp hemb hzgen s hs with ⟨h1, h2⟩ | h1
  · left
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl ((hmemZ _).1 h2)
    · exact Or.inr h2
  · right; exact h1

theorem faithful (hc : Ctx19 S U M V x z A B R) {s : G} (hs : s ∈ (S : Subgroup G))
    (hcomm : ∀ r ∈ R, s * r * s⁻¹ * r⁻¹ = 1 ∨ s * r * s⁻¹ * r⁻¹ = z) : s ∈ R := by
  have hemb := (Base.emb_zgen hc.hyp hc.conf hc.concl).1
  have hzgen := (Base.emb_zgen hc.hyp hc.conf hc.concl).2
  have hmemZ := Base.mem_Zc_iff hc.hyp hc.conf hc.concl
  have key := Model.faithful_Rp hemb hzgen s hs (fun r hrS hrc => by
    have hrR : r ∈ R := by
      refine (mem_R_iff hc hrS).2 ?_
      rcases hrc with ⟨h1, h2⟩ | h1
      · left
        refine ⟨h1, ?_⟩
        rcases h2 with h2 | h2
        · exact Or.inl ((hmemZ _).1 h2)
        · exact Or.inr h2
      · right; exact h1
    exact hcomm r hrR)
  refine (mem_R_iff hc hs).2 ?_
  rcases key with ⟨h1, h2⟩ | h1
  · left
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl ((hmemZ _).1 h2)
    · exact Or.inr h2
  · right; exact h1

end RF

end CFSG.GH74.Uniqueness.SU.SU7
