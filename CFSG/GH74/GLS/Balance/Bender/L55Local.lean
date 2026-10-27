module

public import CFSG.GH74.GLS.Balance.Bender.Ambient

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem l55_le_normalizer_of_normal {G : Type*} [Group G] (N P : Subgroup G) [N.Normal] :
    P ≤ normalizer (N : Set G) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

theorem l55_exists_minimal_normal {G : Type*} [Group G] [Finite G] {X : Subgroup G} [X.Normal]
    (hX : X ≠ ⊥) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≤ X ∧
      ∀ M : Subgroup G, M ≤ N → M.Normal → M = ⊥ ∨ M = N := by
  classical
  have hex : ∃ k : ℕ, ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≤ X ∧ Nat.card N = k :=
    ⟨Nat.card X, X, inferInstance, hX, le_rfl, rfl⟩
  obtain ⟨N, hNn, hN1, hNX, hNk⟩ := Nat.find_spec hex
  refine ⟨N, hNn, hN1, hNX, fun M hMN hMn => ?_⟩
  by_contra hcon
  push Not at hcon
  have hM1 : M ≠ ⊥ := hcon.1
  have hMlt : Nat.card M < Nat.find hex := by
    rw [← hNk]
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hMN hcon.2)
  exact Nat.find_min hex hMlt ⟨M, hMn, hM1, hMN.trans hNX, rfl⟩

theorem l55_isPGroup_of_abelian {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {N : Subgroup G} [N.Normal] (hmin : ∀ M : Subgroup G, M ≤ N → M.Normal → M = ⊥ ∨ M = N)
    (hdvd : p ∣ Nat.card N) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) : IsPGroup p ↥N := by
  let T : Subgroup G :=
    { carrier := {x | x ∈ N ∧ x ^ p = 1}
      one_mem' := ⟨N.one_mem, one_pow p⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨N.mul_mem ha.1 hb.1, by
          rw [Commute.mul_pow (hab a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨N.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hTN : T ≤ N := fun x hx => hx.1
  have hTn : T.Normal :=
    ⟨fun n hn g => ⟨Subgroup.Normal.conj_mem inferInstance n hn.1 g, by
      rw [conj_pow, hn.2]; simp⟩⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hdvd
  have hxT : (x : G) ∈ T := by
    refine ⟨x.2, ?_⟩
    have : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg Subtype.val this
  have hT1 : T ≠ ⊥ := by
    intro h
    have : (x : G) = 1 := by
      have := hxT; rw [h] at this; simpa using this
    have hx1 : x = 1 := Subtype.ext this
    rw [hx1, orderOf_one] at hx
    exact (Fact.out : p.Prime).one_lt.ne hx
  have hTeq : T = N := (hmin T hTN hTn).resolve_left hT1
  intro y
  refine ⟨1, ?_⟩
  have hyT : (y : G) ∈ T := hTeq.ge y.2
  exact Subtype.ext (by simpa using hyT.2)

theorem l55_central_of_pgroup {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {X P N : Subgroup G} [N.Normal] (hP : IsPGroup p ↥P) (hNp : IsPGroup p ↥N) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M ≤ N → M.Normal → M = ⊥ ∨ M = N)
    (hXc : ∀ n ∈ N, ∀ x ∈ X, n * x = x * n) (hsup : X ⊔ P = ⊤) : N ≤ centralizer (P : Set G) := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hNS : N ≤ (S : Subgroup G) := hNp.le_sylow_of_normal S
  have hN'1 : N.subgroupOf (S : Subgroup G) ≠ ⊥ := by
    intro h
    apply hN1
    rw [← Subgroup.map_subgroupOf_eq_of_le hNS, h, Subgroup.map_bot]
  have : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'1
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hgN : (z : G) ∈ N := hz.1
  have hg1 : (z : G) ≠ 1 := by
    intro h
    apply hz1
    exact Subtype.ext (Subtype.ext h)
  have hPc : ∀ q ∈ P, q * (z : G) = (z : G) * q := by
    intro q hq
    have := Subgroup.mem_center_iff.mp hz.2 ⟨q, hPS hq⟩
    exact congrArg Subtype.val this
  have hgc : ∀ h : G, h * (z : G) = (z : G) * h := by
    intro h
    have hh : h ∈ centralizer ({(z : G)} : Set G) := by
      have : (X ⊔ P) ≤ centralizer ({(z : G)} : Set G) := by
        refine sup_le (fun x hx => ?_) (fun q hq => ?_)
        · rw [mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hXc _ hgN x hx
        · rw [mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact (hPc q hq).symm
      exact this (hsup ▸ Subgroup.mem_top h)
    exact (mem_centralizer_iff.mp hh _ rfl).symm
  have hcen : (z : G) ∈ center G := Subgroup.mem_center_iff.mpr hgc
  have hzle : Subgroup.zpowers (z : G) ≤ center G := (Subgroup.zpowers_le).mpr hcen
  have hzn : (Subgroup.zpowers (z : G)).Normal := Subgroup.normal_of_le_center hzle
  have hzN : Subgroup.zpowers (z : G) ≤ N := (Subgroup.zpowers_le).mpr hgN
  have hzeq : Subgroup.zpowers (z : G) = N := by
    rcases hmin _ hzN hzn with h | h
    · exact absurd ((Subgroup.zpowers_eq_bot).mp h) hg1
    · exact h
  intro n hn
  rw [mem_centralizer_iff]
  intro q _
  have hnc : n ∈ center G := hzle (hzeq ▸ hn)
  exact Subgroup.mem_center_iff.mp hnc q

theorem l55_normalizer_inf {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ normalizer (A : Set G)) (hB : g ∈ normalizer (B : Set G)) :
    g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hB h]

theorem l55_mem_normalizer_centralizer {G : Type*} [Group G] {Q : Subgroup G} {g : G}
    (hg : g ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (Q : Set G) → ∀ c ∈ centralizer (Q : Set G),
      g * c * g⁻¹ ∈ centralizer (Q : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro q hq
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
      simpa using this
    have h1 := mem_centralizer_iff.mp hc _ hq'
    calc q * (g * c * g⁻¹) = g * ((g⁻¹ * q * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * q := by group
  rw [mem_normalizer_iff]
  intro c
  refine ⟨key hg c, fun hc => ?_⟩
  have := key (Subgroup.inv_mem _ hg) _ hc
  simpa [mul_assoc] using this

theorem l55_sylow_ne_bot {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Q N : Subgroup G}
    (hQ : IsSylowIn p Q N) (hdvd : p ∣ Nat.card N) : Q ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hdvd
  have hxo : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hzN : Subgroup.zpowers (x : G) ≤ N := (Subgroup.zpowers_le).mpr x.2
  have hcard : Nat.card (Subgroup.zpowers (x : G)) = p ^ 1 := by
    rw [Nat.card_zpowers, hxo, pow_one]
  have hzp : IsPGroup p ↥(Subgroup.zpowers (x : G)) := IsPGroup.of_card hcard
  have h1 := hQ.2.2 _ hzN hzp
  intro hQ1
  have h2 : Nat.card ↥Q = 1 := by rw [hQ1]; exact Subgroup.card_bot
  rw [hcard, h2, pow_one] at h1
  have := (Fact.out : p.Prime).one_lt
  omega

theorem l55_exists_invariant_sylow {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    {N P : Subgroup G} [N.Normal] (hP : IsPGroup p ↥P) :
    ∃ Q : Subgroup G, IsSylowIn p Q N ∧ P ≤ normalizer (Q : Set G) := by
  set K : Subgroup G := N ⊔ P with hK
  have hP' : IsPGroup p ↥(P.subgroupOf K) := hP.comap_subtype
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  set S : Subgroup G := (S' : Subgroup ↥K).map K.subtype with hS
  have hPS : P ≤ S := by
    intro q hq
    have hq' : (⟨q, (le_sup_right : P ≤ K) hq⟩ : ↥K) ∈ P.subgroupOf K := hq
    exact ⟨_, hS' hq', rfl⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf p S K := ⟨S', rfl⟩
  have hQ := hSyl.inf_of_le_normalizer (le_sup_left : N ≤ K) (l55_le_normalizer_of_normal N K)
  obtain ⟨Q', hQ'⟩ := hQ
  refine ⟨S ⊓ N, ?_, ?_⟩
  · rw [← hQ']
    exact isSylowIn_of_sylow p Q'
  · intro g hg
    exact l55_normalizer_inf (Subgroup.le_normalizer (hPS hg)) (l55_le_normalizer_of_normal N P hg)

end CFSG.GH74.GLS.Balance
