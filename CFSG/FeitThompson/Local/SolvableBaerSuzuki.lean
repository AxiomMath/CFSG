module

public import CFSG.FeitThompson.Foundations.NormalContainsMinimalNormal
public import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
public import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
public import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
public import CFSG.FeitThompson.Local.CoprimeNormalComplementPrimeCore
public import CFSG.FeitThompson.Local.PrimePowerConjugatePairsCentralize

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

universe u

variable {G : Type*} [Group G] {p : ℕ}

private theorem mem_pCore_aux (hp : p.Prime) :
    ∀ (n : ℕ) (G : Type u) [Group G] [Finite G] [Group.IsSolvable G], Nat.card G = n →
      ∀ x : G, (∃ k, orderOf x = p ^ k) →
        (∀ g : G, IsPGroup p (closure ({x, g⁻¹ * x * g} : Set G))) → x ∈ pCore p G := by
  have : Fact p.Prime := ⟨hp⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ _ hcard x hx hconj
    rcases subsingleton_or_nontrivial G with _ | _
    ·
      have hx1 : x = 1 := Subsingleton.elim _ _
      rw [hx1]; exact one_mem _
    ·
      obtain ⟨N, hNn, hNb, hNmin⟩ := exists_normal_ne_bot_forall_lt_eq_bot (G := G)
      have := hNn
      obtain ⟨q, d, hq, hd, hNcard⟩ :=
        exists_prime_card_eq_pow_of_isSolvable_of_forall_normal_lt_eq_bot hNb hNmin
      set f := QuotientGroup.mk' N with hfdef
      have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective N
      have hqcard : Nat.card (G ⧸ N) < n := by
        rw [← hcard]
        exact natCard_quotient_lt_natCard_of_bot_lt N (bot_lt_iff_ne_bot.2 hNb)
      have hxq : f x ∈ pCore p (G ⧸ N) := by
        refine ih _ hqcard (G ⧸ N) rfl (f x) ?_ ?_
        · obtain ⟨k, hk⟩ := hx
          obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 (hk ▸ orderOf_map_dvd f x)
          exact ⟨m, hm⟩
        · intro gq
          obtain ⟨g, rfl⟩ := hfsurj gq
          have himg : closure ({f x, (f g)⁻¹ * f x * f g} : Set (G ⧸ N))
              = (closure ({x, g⁻¹ * x * g} : Set G)).map f := by
            rw [MonoidHom.map_closure]
            congr 1
            simp [Set.image_insert_eq]
          rw [himg]
          exact (hconj g).map f
      set H := (pCore p (G ⧸ N)).comap f with hHdef
      have hHn : H.Normal := (pCore_normal p (G ⧸ N)).comap f
      have := hHn
      have hxH : x ∈ H := hxq
      rcases eq_or_ne H ⊤ with hHtop | hHtop
      ·
        have hcore : pCore p (G ⧸ N) = ⊤ :=
          comap_injective hfsurj (by rw [← hHdef, hHtop, comap_top])
        have hQ : IsPGroup p (G ⧸ N) := by
          have h1 : IsPGroup p (pCore p (G ⧸ N)) := isPGroup_pCore hp _
          rw [hcore] at h1
          exact h1.of_equiv topEquiv
        rcases eq_or_ne q p with hqp | hqp
        ·
          rw [hqp] at hNcard
          have hGp : IsPGroup p G := by
            obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ
            refine IsPGroup.of_card (n := a + d) ?_
            rw [pow_add, ← ha, ← hNcard, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
          rw [pCore_eq_top_of_isPGroup hp hGp]
          trivial
        ·
          have hcop : (Nat.card N).Coprime p := by
            rw [hNcard]
            exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hq hp).2 hqp)
          exact mem_pCore_of_mem_centralizer_of_orderOf_eq_pow hp hcop hQ hx
            (mem_centralizer_of_isPGroup_closure_conj hcop fun m _ => hconj m)
      ·
        have hlt : Nat.card H < n := by
          rw [← hcard]
          exact lt_of_le_of_ne (card_le_card_group H) fun h => hHtop (eq_top_of_card_eq H h)
        have hxH' : (⟨x, hxH⟩ : H) ∈ pCore p H := by
          refine ih _ hlt H rfl _ ?_ ?_
          · obtain ⟨k, hk⟩ := hx
            exact ⟨k, (Subgroup.orderOf_mk x hxH).trans hk⟩
          · intro h
            refine IsPGroup.to_le
              (K := comap H.subtype (closure ({x, (h : G)⁻¹ * x * (h : G)} : Set G)))
              ((hconj (h : G)).comap_of_injective _ H.subtype_injective) ?_
            rw [Subgroup.closure_le]
            intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl
            · exact subset_closure (by simp)
            · exact subset_closure (by simp)
        exact le_pCore hp ConjAct.normal_of_characteristic_of_normal
          ((isPGroup_pCore hp H).map H.subtype) ⟨⟨x, hxH⟩, hxH', rfl⟩

theorem mem_pCore_of_forall_isPGroup_closure_conj [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    {x : G} (hx : ∃ k, orderOf x = p ^ k)
    (hconj : ∀ g : G, IsPGroup p (closure ({x, g⁻¹ * x * g} : Set G))) :
    x ∈ pCore p G :=
  mem_pCore_aux hp _ G rfl x hx hconj

theorem mem_pCore_of_forall_isPGroup_closure_conj_zpowers [Finite G] [Group.IsSolvable G]
    (hp : p.Prime) {x : G} (hx : IsPGroup p (zpowers x))
    (hconj : ∀ g : G, IsPGroup p (closure ({x, g⁻¹ * x * g} : Set G))) :
    x ∈ pCore p G :=
  mem_pCore_of_forall_isPGroup_closure_conj hp
    ((isPGroup_zpowers_iff_exists_orderOf_eq_pow hp).1 hx) hconj

theorem isPGroup_closure_conj_of_mem_pCore [Finite G] (hp : p.Prime) {x : G}
    (hx : x ∈ pCore p G) (g : G) : IsPGroup p (closure ({x, g⁻¹ * x * g} : Set G)) := by
  refine (isPGroup_pCore hp G).to_le ?_
  rw [Subgroup.closure_le]
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact hx
  · simpa using (pCore_normal p G).conj_mem x hx g⁻¹

theorem mem_pCore_iff_forall_isPGroup_closure_conj [Finite G] [Group.IsSolvable G] (hp : p.Prime)
    {x : G} :
    x ∈ pCore p G ↔
      (∃ k, orderOf x = p ^ k) ∧ ∀ g : G, IsPGroup p (closure ({x, g⁻¹ * x * g} : Set G)) :=
  ⟨fun hx => ⟨exists_orderOf_eq_pow_of_mem_isPGroup hp (isPGroup_pCore hp G) hx,
      fun g => isPGroup_closure_conj_of_mem_pCore hp hx g⟩,
    fun ⟨hx, hconj⟩ => mem_pCore_of_forall_isPGroup_closure_conj hp hx hconj⟩

end

end CFSG.FeitThompson
