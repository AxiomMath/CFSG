module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem commutator_mem_of_sq_mem {K S : Subgroup G} (hsq : ∀ s ∈ S, s * s ∈ K) {x y : G}
    (hx : x ∈ S) (hy : y ∈ S) : x⁻¹ * y⁻¹ * x * y ∈ K := by
  have h := mul_mem (mul_mem (hsq _ (inv_mem hx)) (hsq _ (mul_mem hx (inv_mem hy)))) (hsq _ hy)
  rwa [show x⁻¹ * x⁻¹ * (x * y⁻¹ * (x * y⁻¹)) * (y * y) = x⁻¹ * y⁻¹ * x * y by group] at h

theorem exists_relIndex_two [Finite G] {K S : Subgroup G} (hKS : K ≤ S)
    (hsq : ∀ s ∈ S, s * s ∈ K) {c : G} (hcS : c ∈ S) (hcK : c ∉ K) :
    ∃ Q : Subgroup G, K ≤ Q ∧ Q ≤ S ∧ c ∉ Q ∧ Q.relIndex S = 2 := by
  obtain ⟨Q, hKQ, ⟨-, hQS, hcQ⟩, hmax⟩ :=
    Finite.exists_le_maximal (p := fun Q : Subgroup G => K ≤ Q ∧ Q ≤ S ∧ c ∉ Q) (a := K)
      ⟨le_rfl, hKS, hcK⟩
  have hsc : ∀ s ∈ S, s ∉ Q → s * c ∈ Q := by
    intro s hs hsQ
    have hsN : zpowers s ≤ normalizer (Q : Set G) := by
      rw [zpowers_le, mem_normalizer_iff]
      intro q
      have key : ∀ q' ∈ S, q' ∈ Q ↔ s * q' * s⁻¹ ∈ Q := by
        intro q' hq'
        have hk := hKQ (commutator_mem_of_sq_mem hsq hq' (inv_mem hs))
        rw [inv_inv] at hk
        constructor
        · intro h
          have := mul_mem h hk
          rwa [show q' * (q'⁻¹ * s * q' * s⁻¹) = s * q' * s⁻¹ by group] at this
        · intro h
          have := mul_mem h (inv_mem hk)
          rwa [show s * q' * s⁻¹ * (q'⁻¹ * s * q' * s⁻¹)⁻¹ = q' by group] at this
      constructor
      · intro h
        exact (key q (hQS h)).mp h
      · intro h
        have hqS : q ∈ S := by
          have := mul_mem (mul_mem (inv_mem hs) (hQS h)) hs
          rwa [show s⁻¹ * (s * q * s⁻¹) * s = q by group] at this
        exact (key q hqS).mpr h
    have hcmem : c ∈ Q ⊔ zpowers s := by
      by_contra hc
      exact hsQ (hmax ⟨hKQ.trans le_sup_left, sup_le hQS (zpowers_le.mpr hs), hc⟩ le_sup_left
        ((le_sup_right : zpowers s ≤ Q ⊔ zpowers s) (mem_zpowers s)))
    have hc' : c ∈ ((Q : Set G) * (zpowers s : Set G)) := by
      rw [← coe_mul_of_right_le_normalizer_left Q (zpowers s) hsN]
      exact hcmem
    obtain ⟨q, hq, u, hu, hqu⟩ := hc'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    have hs2 : s ^ (2 : ℤ) ∈ Q := by
      rw [show s ^ (2 : ℤ) = s * s by rw [zpow_two]]
      exact hKQ (hsq s hs)
    have hcc : c * c ∈ Q := hKQ (hsq c hcS)
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · exfalso
      apply hcQ
      rw [← hqu, zpow_mul]
      exact mul_mem hq (zpow_mem hs2 j)
    · have h1 : s = (s ^ (2 : ℤ)) ^ (-j) * q⁻¹ * c := by
        rw [← hqu, zpow_add, zpow_mul, zpow_one, zpow_neg]
        group
      rw [h1, show (s ^ (2 : ℤ)) ^ (-j) * q⁻¹ * c * c = (s ^ (2 : ℤ)) ^ (-j) * q⁻¹ * (c * c) by
        group]
      exact mul_mem (mul_mem (zpow_mem hs2 _) (inv_mem hq)) hcc
  refine ⟨Q, hKQ, hQS, hcQ, relIndex_eq_two_iff.mpr ⟨c, hcS, fun b hb => ?_⟩⟩
  by_cases hbQ : b ∈ Q
  · refine Or.inr ⟨hbQ, fun h => hcQ ?_⟩
    have := mul_mem (inv_mem hbQ) h
    rwa [inv_mul_cancel_left] at this
  · exact Or.inl ⟨hsc b hb hbQ, hbQ⟩

theorem card_modEq_card_fixed [Finite G] {p : ℕ} [Fact p.Prime] {h : G} {e : ℕ}
    (hh : h ^ p ^ e = 1) (X : Set G) (hX : ∀ x ∈ X, h * x * h⁻¹ ∈ X) :
    Nat.card X ≡ Nat.card {x : X // h * (x : G) = x * h} [MOD p] := by
  classical
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End X := fun x => ⟨h * x * h⁻¹, hX x x.2⟩
  have hpow : ∀ n : ℕ, ∀ x : X, ((f ^ n) x : G) = h ^ n * x * (h ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Function.End.mul_def]
      show h * ((f ^ n) x : G) * h⁻¹ = _
      rw [ih, pow_succ']
      group
  have hf : f ^ p ^ e = 1 := by
    funext x
    apply Subtype.ext
    rw [hpow, hh]
    simp
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hmod
  convert hmod using 1
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1, Subtype.ext (by
        show h * (x.1 : G) * h⁻¹ = x.1
        rw [x.2, mul_inv_cancel_right])⟩
      invFun := fun x => ⟨x.1, by
        have h1 : h * (x.1 : G) * h⁻¹ = x.1 := congrArg Subtype.val x.2
        calc h * (x.1 : G) = h * (x.1 : G) * h⁻¹ * h := by group
          _ = x.1 * h := by rw [h1]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_modEq_card_inf_centralizer [Finite G] {p : ℕ} [Fact p.Prime] {h : G} {e : ℕ}
    (hh : h ^ p ^ e = 1) {D : Subgroup G} (hD : h ∈ normalizer (D : Set G)) :
    Nat.card D ≡ Nat.card ↥(D ⊓ centralizer ({h} : Set G)) [MOD p] := by
  have hmod := card_modEq_card_fixed hh (D : Set G) fun x hx => (mem_normalizer_iff.mp hD x).mp hx
  convert hmod using 1
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨x, x.2.1⟩, (mem_centralizer_singleton_iff.mp x.2.2).symm⟩
      invFun := fun x => ⟨x.1, x.1.2, mem_centralizer_singleton_iff.mpr x.2.symm⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_eq_one_or_eight [Finite G] {h : G} {e : ℕ} (hh : h ^ 7 ^ e = 1) {D : Subgroup G}
    (hD : h ∈ normalizer (D : Set G)) (h8 : Nat.card D ∣ 8)
    (hfix : D ⊓ centralizer ({h} : Set G) = ⊥) : Nat.card D = 1 ∨ Nat.card D = 8 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hmod := card_modEq_card_inf_centralizer hh hD
  rw [hfix, card_bot] at hmod
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card D ∣ 2 ^ 3 from h8)
  rw [hk'] at hmod ⊢
  interval_cases k
  · left; rfl
  · exact absurd hmod (by decide)
  · exact absurd hmod (by decide)
  · right; rfl

@[expose] def oddGen (L : Subgroup G) : Subgroup G :=
  closure {g | g ∈ L ∧ Odd (orderOf g)}

theorem oddGen_le (L : Subgroup G) : oddGen L ≤ L :=
  (closure_le _).mpr fun _ hg => hg.1

theorem mem_oddGen {L : Subgroup G} {g : G} (hg : g ∈ L) (hodd : Odd (orderOf g)) :
    g ∈ oddGen L :=
  subset_closure ⟨hg, hodd⟩

theorem exists_sq_eq_of_odd {g : G} (hodd : Odd (orderOf g)) : ∃ k : ℕ, (g ^ k) ^ 2 = g := by
  obtain ⟨m, hm⟩ := hodd
  refine ⟨m + 1, ?_⟩
  rw [← pow_mul, show (m + 1) * 2 = orderOf g + 1 by omega, pow_succ, pow_orderOf_eq_one,
    one_mul]

theorem oddGen_le_of_sq {L N : Subgroup G} (h : ∀ x ∈ oddGen L, x ^ 2 ∈ N) : oddGen L ≤ N := by
  refine (closure_le _).mpr ?_
  rintro g ⟨hg, hodd⟩
  obtain ⟨k, hk⟩ := exists_sq_eq_of_odd hodd
  rw [← hk]
  exact h _ (pow_mem (mem_oddGen hg hodd) k)

theorem orderOf_conj_eq (n g : G) : orderOf (n * g * n⁻¹) = orderOf g := by
  have h := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective g
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h

theorem conj_mem_oddGen {L : Subgroup G} {n x : G} (hn : n ∈ L) (hx : x ∈ oddGen L) :
    n * x * n⁻¹ ∈ oddGen L := by
  have hle : (oddGen L).map (MulAut.conj n).toMonoidHom ≤ oddGen L := by
    rw [oddGen, MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, ⟨hg, hodd⟩, rfl⟩
    refine subset_closure ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hn hg) (inv_mem hn)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, orderOf_conj_eq]
      exact hodd
  exact hle ⟨x, hx, rfl⟩

theorem le_normalizer_oddGen (L : Subgroup G) : L ≤ normalizer (oddGen L : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_oddGen hn
  · intro h
    have := conj_mem_oddGen (inv_mem hn) h
    rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

theorem le_oddGen_of_fixed [Finite G] {L T : Subgroup G} {h : G} (hhL : h ∈ L)
    (hodd : Odd (orderOf h)) (hTL : T ≤ L) (hhT : ∀ t ∈ T, h⁻¹ * t * h ∈ T)
    (hfix : ∀ t ∈ T, h⁻¹ * t * h = t → t = 1) : T ≤ oddGen L := by
  let f : T → T := fun s => ⟨(s : G)⁻¹ * (h⁻¹ * s * h), mul_mem (inv_mem s.2) (hhT s s.2)⟩
  have hinj : Function.Injective f := by
    intro s t hst
    have h1 : (s : G)⁻¹ * (h⁻¹ * s * h) = (t : G)⁻¹ * (h⁻¹ * t * h) := congrArg Subtype.val hst
    have hu : h⁻¹ * ((t : G) * (s : G)⁻¹) * h = (t : G) * (s : G)⁻¹ := by
      calc h⁻¹ * ((t : G) * (s : G)⁻¹) * h
          = (t : G) * ((t : G)⁻¹ * (h⁻¹ * t * h)) * ((s : G)⁻¹ * (h⁻¹ * s * h))⁻¹ *
            (s : G)⁻¹ := by group
        _ = (t : G) * (s : G)⁻¹ := by rw [← h1]; group
    have h2 := hfix _ (mul_mem t.2 (inv_mem s.2)) hu
    exact Subtype.ext (mul_inv_eq_one.mp h2).symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro t ht
  obtain ⟨s, hs⟩ := hsurj ⟨t, ht⟩
  have ht' : t = (s : G)⁻¹ * h⁻¹ * s * h := by
    have h2 : (s : G)⁻¹ * (h⁻¹ * s * h) = t := congrArg Subtype.val hs
    rw [← h2]
    group
  rw [ht']
  refine mul_mem (mem_oddGen ?_ ?_) (mem_oddGen hhL hodd)
  · exact mul_mem (mul_mem (inv_mem (hTL s.2)) (inv_mem hhL)) (hTL s.2)
  · rw [show (s : G)⁻¹ * h⁻¹ * s = (s : G)⁻¹ * h⁻¹ * (s : G)⁻¹⁻¹ by rw [inv_inv],
      orderOf_conj_eq, orderOf_inv]
    exact hodd

theorem false_of_isEightGroup_le {E C : Subgroup G} (hE : IsEightGroup E) (hC : IsCyclic C)
    (hEC : E ≤ C) : False := by
  have : IsCyclic E := isCyclic_of_le hEC
  have h1 := IsCyclic.exponent_eq_card (α := E)
  have h2 : Monoid.exponent E ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by
      rw [SubmonoidClass.coe_pow, pow_two]
      exact hE.1.2 g g.2)
  rw [h1, hE.2] at h2
  exact absurd h2 (by decide)

end CFSG.ComponentClassification.GrSLit.FinalG
