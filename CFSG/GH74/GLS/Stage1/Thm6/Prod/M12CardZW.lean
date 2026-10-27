module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.Fusion
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6.M12Facts
  CFSG.GH74.GLS.Stage1.Thm6.Sec13 CFSG.GH74.GLS.Stage1.Thm6.Sec14 CFSG.GH74.GLS.Stage2.Local

@[expose] def zType (p : NF) : Prop :=
  pU p ∨ (p.2.2.1 = 0 ∧ p.2.2.2 = 1 ∧ ¬ (p.1.val % 2 = 0 ∧ p.2.1.val % 2 = 0))

@[expose] def xType (p : NF) : Prop :=
  ¬ pQ0 p ∨ (p.2.2.1 = 0 ∧ p.2.2.2 = 1 ∧ p.1.val % 2 = 0 ∧ p.2.1.val % 2 = 0)

instance : DecidablePred zType := fun p => by unfold zType; infer_instance
instance : DecidablePred xType := fun p => by unfold xType; infer_instance

theorem inv_zType_or_xType : ∀ p : NF, nfMul p p = (0, 0, 0, 0) → p ≠ (0, 0, 0, 0) →
    zType p ∨ xType p := by
  decide +kernel

theorem card_zType_R :
    Nat.card {p : NF // pR p ∧ nfMul p p = (0, 0, 0, 0) ∧ p ≠ (0, 0, 0, 0) ∧ zType p} = 7 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} {a b y : G}

theorem isConj_z_iff {x' : G} {T V : Subgroup G} (o : Out13 G x' T V S a b y)
    (hfus : ∀ i j : Fin 4, ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0) →
      IsConj (a ^ 2 * b ^ 2) (nu a b y x' (i, j, 0, 1)))
    (p : NF) (hsq : nfMul p p = (0, 0, 0, 0)) (hne : p ≠ (0, 0, 0, 0)) :
    IsConj (a ^ 2 * b ^ 2) (nu a b y x' p) ↔ zType p := by
  have h := o.data
  have hne' : nu a b y x' p ≠ 1 := fun e => hne (nu_injective h (e.trans nu_zero.symm))
  have hsq' : nu a b y x' p * nu a b y x' p = 1 := by rw [nu_mul h, hsq, nu_zero]
  have hxz : ¬ IsConj (a ^ 2 * b ^ 2) x' := by
    intro hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    exact x_not_conj_z o g hg
  have hx : xType p → IsConj x' (nu a b y x' p) := by
    rintro (hnot | ⟨hk0, hl1, hi, hj⟩)
    · have hvP : nu a b y x' p ∉ nfSub o.data pQ0 closed_pQ0 := fun hm =>
        hnot ((nu_mem_nfSub h closed_pQ0 p).1 hm)
      obtain ⟨c, hc⟩ := involutions_conj_x o (nu_mem h p) hsq' hvP
      exact isConj_iff.2 ⟨c, hc⟩
    · have key : ∀ p : NF, p.2.2.1 = 0 → p.2.2.2 = 1 → p.1.val % 2 = 0 → p.2.1.val % 2 = 0 →
          ∃ q : NF, nfMul (nfMul q xNF) (nfInv q) = p := by decide +kernel
      obtain ⟨q, hq⟩ := key p hk0 hl1 hi hj
      have hx' : nu a b y x' xNF = x' := by simp [nu, xNF]
      have e1 : nu a b y x' q * x' * (nu a b y x' q)⁻¹ = nu a b y x' p := by
        have h2 : nu a b y x' q * nu a b y x' xNF * (nu a b y x' q)⁻¹ =
            nu a b y x' (nfMul (nfMul q xNF) (nfInv q)) := by
          rw [← nu_mul h, ← nu_mul h, nu_inv h]
        rw [hx', hq] at h2
        exact h2
      exact isConj_iff.2 ⟨nu a b y x' q, e1⟩
  have hz : zType p → IsConj (a ^ 2 * b ^ 2) (nu a b y x' p) := by
    rintro (hU | ⟨hk0, hl1, hij⟩)
    · have hmemU : nu a b y x' p ∈ nfSub h pU closed_pU := (nu_mem_nfSub h closed_pU p).2 hU
      obtain ⟨f, hf3, hfN, -, v, hv, hfv⟩ := o.f3
      have hvU : v ∈ nfSub h pU closed_pU := by rw [← U_eq h, ← o.V_eq]; exact hv
      obtain ⟨n, -, hn⟩ := exists_conj_U_to_z o hf3 hfN hvU hfv hmemU hne'
      exact (isConj_iff.2 ⟨n, hn⟩).symm
    · obtain ⟨i, j, k, l⟩ := p
      simp only at hk0 hl1
      subst hk0
      subst hl1
      exact hfus i j hij
  constructor
  · intro hconj
    rcases inv_zType_or_xType p hsq hne with hzt | hxt
    · exact hzt
    · exact absurd (hconj.trans (hx hxt).symm) hxz
  · exact hz

theorem cardZW_field {x' : G} {T V : Subgroup G} (o : Out13 G x' T V S a b y)
    (hW : ∀ p : NF, nu a b y x' p ∈ WC (a ^ 2 * b ^ 2) ↔ pR p)
    (hfus : ∀ i j : Fin 4, ¬ (i.val % 2 = 0 ∧ j.val % 2 = 0) →
      IsConj (a ^ 2 * b ^ 2) (nu a b y x' (i, j, 0, 1))) :
    Nat.card {u : G // u ∈ S ∧ u ∈ WC (a ^ 2 * b ^ 2) ∧ orderOf u = 2 ∧
      IsConj (a ^ 2 * b ^ 2) u} = 7 := by
  have h := o.data
  have hord : ∀ p : NF, nfMul p p = (0, 0, 0, 0) → p ≠ (0, 0, 0, 0) →
      orderOf (nu a b y x' p) = 2 := by
    intro p hsq hne
    apply orderOf_eq_prime
    · rw [pow_two, nu_mul h, hsq, nu_zero]
    · intro e
      exact hne (nu_injective h (e.trans nu_zero.symm))
  rw [← card_zType_R]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : {p : NF // pR p ∧ nfMul p p = (0, 0, 0, 0) ∧ p ≠ (0, 0, 0, 0) ∧ zType p} =>
      (⟨nu a b y x' p.1, nu_mem h p.1, (hW p.1).2 p.2.1, hord p.1 p.2.2.1 p.2.2.2.1,
        (isConj_z_iff o hfus p.1 p.2.2.1 p.2.2.2.1).2 p.2.2.2.2⟩ :
          {u : G // u ∈ S ∧ u ∈ WC (a ^ 2 * b ^ 2) ∧ orderOf u = 2 ∧
            IsConj (a ^ 2 * b ^ 2) u})) ⟨?_, ?_⟩)
  · intro p q hpq
    exact Subtype.ext (nu_injective h (congrArg Subtype.val hpq))
  · rintro ⟨u, huS, huW, hu2, huc⟩
    obtain ⟨p, rfl⟩ := exists_nf h huS
    have hsq : nfMul p p = (0, 0, 0, 0) := by
      have h1 : nu a b y x' p * nu a b y x' p = 1 := by
        have := pow_orderOf_eq_one (nu a b y x' p)
        rwa [hu2, pow_two] at this
      rw [nu_mul h] at h1
      exact nu_injective h (h1.trans nu_zero.symm)
    have hne : p ≠ (0, 0, 0, 0) := by
      intro e
      rw [e, nu_zero, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
    exact ⟨⟨p, (hW p).1 huW, hsq, hne, (isConj_z_iff o hfus p hsq hne).1 huc⟩, rfl⟩

end CFSG.GH74.GLS.Stage1.Thm6.Prod
