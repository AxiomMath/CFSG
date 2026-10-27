module

public import CFSG.Holt.H78.Data
import CFSG.Holt.H78.Conjugacy
import CFSG.Holt.H78.OddCore
import CFSG.Holt.H78.SEModelFive
import CFSG.Holt.H78.DataSylow
public import CFSG.Holt.H78.Count

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt Equiv
open scoped Pointwise

namespace CCL

section LongInv

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

theorem exists_ne_ne_of_three_le (h3 : 3 ≤ Fintype.card Λ) (a b : Λ) :
    ∃ x : Λ, x ≠ a ∧ x ≠ b := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b} : Finset Λ)) (t := Finset.univ)
    (Finset.card_le_two.trans_lt (by rw [Finset.card_univ]; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  exact ⟨x, hx⟩

theorem exists_ne_ne_ne_of_four_le (h4 : 4 ≤ Fintype.card Λ) (a b c : Λ) :
    ∃ x : Λ, x ≠ a ∧ x ≠ b ∧ x ≠ c := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset Λ)) (t := Finset.univ)
    (Finset.card_le_three.trans_lt (by rw [Finset.card_univ]; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  exact ⟨x, hx⟩

omit [Fintype Λ] [DecidableEq Λ] in
theorem apply_apply_of_mem_longInv {y : Perm Λ} (hy : y ∈ longInv (Perm Λ) Λ) (x : Λ) :
    y (y x) = x := by
  rw [← Perm.mul_apply, mul_self_eq_one_of_mem_longInv hy, Perm.one_apply]

theorem exists_mem_longInv_perm_apply_eq_of_odd (hodd : Odd (Fintype.card Λ))
    (h3 : 3 ≤ Fintype.card Λ) (p q : Λ) : ∃ y ∈ longInv (Perm Λ) Λ, y p = q := by
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨y, hy⟩ := exists_mem_longInvAt_perm hodd h3 p
    exact ⟨y, hy.1, hy.2⟩
  · obtain ⟨r, hrp, hrq⟩ := exists_ne_ne_of_three_le h3 p q
    obtain ⟨s, hs⟩ := exists_mem_longInvAt_perm hodd h3 r
    obtain ⟨y, hy, hyp⟩ := exists_mem_longInvAt_perm_apply_eq hs (Ne.symm hrp) (Ne.symm hrq)
      (Ne.symm hpq)
    exact ⟨y, hy.1, hyp⟩

theorem exists_mem_longInvAt_perm_apply_apply_eq (hodd : Odd (Fintype.card Λ))
    (h5 : 5 ≤ Fintype.card Λ) {p q μ : Λ} (hqp : q ≠ p) (hμp : μ ≠ p) :
    ∃ y ∈ longInvAt (Perm Λ) Λ p, ∃ y' ∈ longInvAt (Perm Λ) Λ p, y (y' q) = μ := by
  obtain ⟨ν, hνp, hνq, hνμ⟩ := exists_ne_ne_ne_of_four_le (by omega) p q μ
  obtain ⟨s, hs⟩ := exists_mem_longInvAt_perm hodd (by omega) p
  obtain ⟨y', hy', hy'q⟩ := exists_mem_longInvAt_perm_apply_eq hs hqp hνp hνq
  obtain ⟨y, hy, hyν⟩ := exists_mem_longInvAt_perm_apply_eq hs hνp hμp (Ne.symm hνμ)
  exact ⟨y, hy, y', hy', by rw [hy'q, hyν]⟩

theorem exists_mem_longInvAt_perm_mul_mul_self_eq_one (hodd : Odd (Fintype.card Λ))
    (h5 : 5 ≤ Fintype.card Λ) {p μ : Λ} (hμp : μ ≠ p) :
    ∃ y ∈ longInvAt (Perm Λ) Λ p, ∃ y' ∈ longInvAt (Perm Λ) Λ p,
      y * y' * (y * y') = 1 ∧ (y * y') μ ≠ μ := by
  obtain ⟨s, hs⟩ := exists_mem_longInvAt_perm hodd (by omega) p
  have hfix := fun z => apply_eq_self_iff_of_mem_longInvAt_perm (x := z) hs
  have hss := apply_apply_of_mem_longInv hs.1
  have haμ : s μ ≠ μ := fun h => hμp ((hfix μ).1 h)
  have hap : s μ ≠ p := fun h => hμp (by rw [← hss μ, h, (hfix p).2 rfl])
  obtain ⟨x, hxp, hxμ, hxa⟩ := exists_ne_ne_ne_of_four_le (by omega) p μ (s μ)
  have hsx : s x ≠ x := fun h => hxp ((hfix x).1 h)
  have hsxμ : s x ≠ μ := fun h => hxa (by rw [← h, hss x])
  have hsxa : s x ≠ s μ := fun h => hxμ (s.injective h)
  have hgp : swap (s μ) x p = p := swap_apply_of_ne_of_ne (Ne.symm hap) (Ne.symm hxp)
  have hy' := conj_mem_longInvAt_perm hs (swap (s μ) x)
  rw [hgp] at hy'
  have hw : s * (swap (s μ) x * s * (swap (s μ) x)⁻¹) = swap μ (s x) * swap (s μ) x := by
    have h1 : s * (swap (s μ) x * s * (swap (s μ) x)⁻¹) =
        s * swap (s μ) x * s⁻¹ * swap (s μ) x := by
      rw [inv_eq_self_of_mem_longInv hs.1, swap_inv]
      simp only [mul_assoc]
    rw [h1, ← swap_apply_apply, hss μ]
  have hnd : [μ, s x, s μ, x].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_or]
    exact ⟨⟨hsxμ.symm, haμ.symm, hxμ.symm⟩, ⟨hsxa, hsx⟩, hxa.symm, not_false, trivial⟩
  have hc := (Perm.disjoint_swap_swap hnd).commute
  refine ⟨s, hs, _, hy', ?_, ?_⟩
  · rw [hw]
    calc swap μ (s x) * swap (s μ) x * (swap μ (s x) * swap (s μ) x)
        = swap μ (s x) * (swap (s μ) x * swap μ (s x)) * swap (s μ) x := by
          simp only [mul_assoc]
      _ = swap μ (s x) * swap μ (s x) * (swap (s μ) x * swap (s μ) x) := by
          rw [← hc.eq]; simp only [mul_assoc]
      _ = 1 := by rw [swap_mul_self, swap_mul_self, one_mul]
  · rw [hw, Perm.mul_apply, swap_apply_of_ne_of_ne haμ.symm hxμ.symm, swap_apply_left]
    exact hsxμ

end LongInv

section Block

variable {ι : Type*} [DecidableEq ι] {Λ : ι → Type*} {Z : Type*}

@[expose] def coordSupport (f : (∀ i, Λ i) → Z) : Set ι :=
  {i | ∃ (x : ∀ i, Λ i) (μ : Λ i), f (Function.update x i μ) ≠ f x}

theorem apply_update_eq_of_notMem_coordSupport {f : (∀ i, Λ i) → Z} {i : ι}
    (hi : i ∉ coordSupport f) (x : ∀ i, Λ i) (μ : Λ i) : f (Function.update x i μ) = f x := by
  by_contra h
  exact hi ⟨x, μ, h⟩

theorem eq_of_forall_mem_coordSupport [Finite ι] {f : (∀ i, Λ i) → Z} {x x' : ∀ i, Λ i}
    (h : ∀ i ∈ coordSupport f, x i = x' i) : f x = f x' := by
  classical
  have := Fintype.ofFinite ι
  suffices key : ∀ s : Finset ι, ∀ x : ∀ i, Λ i, (∀ i ∉ s, x i = x' i) →
      (∀ i ∈ s, i ∉ coordSupport f) → f x = f x' by
    refine key (Finset.univ.filter fun i => i ∉ coordSupport f) x (fun i hi => h i ?_)
      (fun i hi => (Finset.mem_filter.mp hi).2)
    simpa using hi
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro x hx _
    rw [show x = x' from funext fun i => hx i (Finset.notMem_empty i)]
  | insert a s has ih =>
    intro x hx hS
    have h1 : f (Function.update x a (x' a)) = f x' := by
      refine ih _ (fun i hi => ?_) (fun i hi => hS i (Finset.mem_insert_of_mem hi))
      by_cases hia : i = a
      · subst hia
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hia]
        exact hx i (by simp [hia, hi])
    rw [← h1, apply_update_eq_of_notMem_coordSupport (hS a (Finset.mem_insert_self a s))]

variable [∀ i, Fintype (Λ i)] [∀ i, DecidableEq (Λ i)]

private theorem apply_update_eq_of_apply_eq_of_ne (hodd : ∀ i, Odd (Fintype.card (Λ i)))
    (h5 : ∀ i, 5 ≤ Fintype.card (Λ i)) {f : (∀ i, Λ i) → Z}
    (hf : ∀ y : ∀ i, Perm (Λ i), (∀ i, y i ∈ longInv (Perm (Λ i)) (Λ i)) →
      ∀ x x', f x = f x' → f (fun i => y i (x i)) = f (fun i => y i (x' i)))
    {x x' : ∀ i, Λ i} (hxx' : f x = f x') {i : ι} (hi : x i ≠ x' i) {μ : Λ i}
    (hμ : μ ≠ x i) : f (Function.update x' i μ) = f x' := by
  obtain ⟨y, hy, y', hy', hyy'⟩ :=
    exists_mem_longInvAt_perm_apply_apply_eq (hodd i) (h5 i) (Ne.symm hi) hμ
  choose z hz using fun k => exists_mem_longInvAt_perm (hodd k) (by have := h5 k; omega) (x k)
  have hJ : ∀ w : Perm (Λ i), w ∈ longInv (Perm (Λ i)) (Λ i) →
      ∀ k, Function.update z i w k ∈ longInv (Perm (Λ k)) (Λ k) := by
    intro w hw k
    by_cases hk : k = i
    · subst hk
      rwa [Function.update_self]
    · rw [Function.update_of_ne hk]
      exact (hz k).1
  have h2 := hf _ (hJ y hy.1) _ _ (hf _ (hJ y' hy'.1) x x' hxx')
  have e1 : (fun k => Function.update z i y k (Function.update z i y' k (x k))) = x := by
    funext k
    by_cases hk : k = i
    · subst hk
      have h1 : y' (x k) = x k := hy'.2
      have h2 : y (x k) = x k := hy.2
      rw [Function.update_self, Function.update_self, h1, h2]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk,
        apply_apply_of_mem_longInv (hz k).1]
  have e2 : (fun k => Function.update z i y k (Function.update z i y' k (x' k))) =
      Function.update x' i μ := by
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self, Function.update_self, Function.update_self, hyy']
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, Function.update_of_ne hk,
        apply_apply_of_mem_longInv (hz k).1]
  rw [e1, e2] at h2
  rw [← h2, hxx']

private theorem apply_update_eq_of_apply_eq (hodd : ∀ i, Odd (Fintype.card (Λ i)))
    (h5 : ∀ i, 5 ≤ Fintype.card (Λ i)) {f : (∀ i, Λ i) → Z}
    (hf : ∀ y : ∀ i, Perm (Λ i), (∀ i, y i ∈ longInv (Perm (Λ i)) (Λ i)) →
      ∀ x x', f x = f x' → f (fun i => y i (x i)) = f (fun i => y i (x' i)))
    {x x' : ∀ i, Λ i} (hxx' : f x = f x') {i : ι} (hi : x i ≠ x' i) (μ : Λ i) :
    f (Function.update x' i μ) = f x' := by
  obtain ⟨μ₀, hμ₀x, hμ₀x'⟩ := exists_ne_ne_of_three_le (by have := h5 i; omega) (x i) (x' i)
  have h1 := apply_update_eq_of_apply_eq_of_ne hodd h5 hf hxx' hi hμ₀x
  by_cases hμ : μ = x i
  · subst hμ
    have h2 : Function.update x' i μ₀ i ≠ x' i := by rw [Function.update_self]; exact hμ₀x'
    have h3 : x i ≠ Function.update x' i μ₀ i := by rw [Function.update_self]; exact hμ₀x.symm
    exact apply_update_eq_of_apply_eq_of_ne hodd h5 hf h1 h2 h3
  · exact apply_update_eq_of_apply_eq_of_ne hodd h5 hf hxx' hi hμ

theorem eq_iff_forall_mem_coordSupport [Finite ι] (hodd : ∀ i, Odd (Fintype.card (Λ i)))
    (h5 : ∀ i, 5 ≤ Fintype.card (Λ i)) {f : (∀ i, Λ i) → Z}
    (hf : ∀ y : ∀ i, Perm (Λ i), (∀ i, y i ∈ longInv (Perm (Λ i)) (Λ i)) →
      ∀ x x', f x = f x' → f (fun i => y i (x i)) = f (fun i => y i (x' i)))
    {x x' : ∀ i, Λ i} : f x = f x' ↔ ∀ i ∈ coordSupport f, x i = x' i := by
  refine ⟨fun hxx' i hi => ?_, eq_of_forall_mem_coordSupport⟩
  by_contra hne
  obtain ⟨z, μ, hzμ⟩ := hi
  apply hzμ
  choose Y hY hYz using fun k =>
    exists_mem_longInv_perm_apply_eq_of_odd (hodd k) (by have := h5 k; omega) (x' k) (z k)
  have h := hf Y hY _ x' (apply_update_eq_of_apply_eq hodd h5 hf hxx' hne (Y i μ))
  have e1 : (fun k => Y k (Function.update x' i (Y i μ) k)) = Function.update z i μ := by
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Function.update_self, Function.update_self, apply_apply_of_mem_longInv (hY k)]
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, hYz k]
  rwa [e1, show (fun k => Y k (x' k)) = z from funext hYz] at h

end Block

section Tuple

variable {ι : Type*} [DecidableEq ι] {Λ : ι → Type*}

theorem update_mem_longInvAt {x : ∀ i, Λ i} {z : ∀ k, Perm (Λ k)}
    (hz : ∀ k, z k ∈ longInvAt (Perm (Λ k)) (Λ k) (x k)) {i : ι} {w : Perm (Λ i)}
    (hw : w ∈ longInvAt (Perm (Λ i)) (Λ i) (x i)) (k : ι) :
    Function.update z i w k ∈ longInvAt (Perm (Λ k)) (Λ k) (x k) := by
  by_cases hk : k = i
  · subst hk
    rwa [Function.update_self]
  · rw [Function.update_of_ne hk]
    exact hz k

omit [DecidableEq ι] in
theorem apply_eq_self_of_forall_mem_longInvAt {x : ∀ i, Λ i} {y : ∀ k, Perm (Λ k)}
    (hy : ∀ k, y k ∈ longInvAt (Perm (Λ k)) (Λ k) (x k)) : (fun k => y k (x k)) = x :=
  funext fun k => (hy k).2

omit [DecidableEq ι] in
theorem exists_forall_mem_longInvAt [∀ i, Fintype (Λ i)] [∀ i, DecidableEq (Λ i)]
    (hodd : ∀ i, Odd (Fintype.card (Λ i))) (h3 : ∀ i, 3 ≤ Fintype.card (Λ i))
    (x : ∀ i, Λ i) : ∃ z : ∀ k, Perm (Λ k), ∀ k, z k ∈ longInvAt (Perm (Λ k)) (Λ k) (x k) :=
  ⟨fun k => (exists_mem_longInvAt_perm (hodd k) (h3 k) (x k)).choose,
    fun k => (exists_mem_longInvAt_perm (hodd k) (h3 k) (x k)).choose_spec⟩

end Tuple

end CCL

section OddOrbits

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem exists_odd_pow_smul_eq_of_mem_longInvAt (hG : IsStarGroup G Ω) {α : Ω} {u v : G}
    (hu : u ∈ longInvAt G Ω α) (hv : v ∈ longInvAt G Ω α) :
    ∃ m : ℕ, Odd m ∧ ∀ ω ∈ orbit (jOddCore G Ω) α, (v * u) ^ m • ω = ω := by
  have := hG.isPretransitive
  set N := CFSG.pPrimeCore 2 G
  set K := stabilizer G α ⊔ N
  have hK : stabilizer G α ≤ K := le_sup_left
  have huK : u ∈ K := hK hu.2
  have hvK : v ∈ K := hK hv.2
  have hB : ∀ ω ∈ orbit (jOddCore G Ω) α, ∃ k : K, (k : G) • α = ω := by
    intro ω hω
    rw [orbit_jOddCore_eq hG] at hω
    obtain ⟨⟨n, hn⟩, rfl⟩ := hω
    exact ⟨⟨n, Subgroup.mem_sup_right hn⟩, rfl⟩
  by_cases h1B : 1 < (stabilizer G α).relIndex K
  · set f := (toPermHom K (K ⧸ (stabilizer G α).subgroupOf K)).rangeRestrict
    have hvB := rangeRestrict_mem_longInv_block hG.odd_card hK h1B hvK hv.1
    have huB := rangeRestrict_mem_longInv_block hG.odd_card hK h1B huK hu.1
    have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf K)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : N ≤ K)).toEquiv]
      exact CFSG.pPrimeCore_coprime_card
    have : (N.subgroupOf K).Normal := Subgroup.Normal.subgroupOf CFSG.pPrimeCore_normal K
    have hOB := isPretransitive_pPrimeCore_range hcop
      (isPretransitive_subgroupOf_quotient_sup (stabilizer G α) N)
    refine ⟨_, odd_orderOf_mul_of_isPretransitive hOB hvB huB, fun ω hω => ?_⟩
    obtain ⟨k, rfl⟩ := hB ω hω
    set w : K := ⟨v, hvK⟩ * ⟨u, huK⟩
    set m := orderOf (f ⟨v, hvK⟩ * f ⟨u, huK⟩)
    have hw1 : toPermHom K (K ⧸ (stabilizer G α).subgroupOf K) (w ^ m) = 1 := by
      have hfw : f (w ^ m) = 1 := by rw [map_pow, map_mul, pow_orderOf_eq_one]
      exact congrArg Subtype.val hfw
    have h2 : (w ^ m) • ((k : K) : K ⧸ (stabilizer G α).subgroupOf K) =
        ((k : K) : K ⧸ (stabilizer G α).subgroupOf K) :=
      congrArg (fun π : Perm (K ⧸ (stabilizer G α).subgroupOf K) =>
        π ((k : K) : K ⧸ (stabilizer G α).subgroupOf K)) hw1
    have h3 := (smul_eq_iff_blockPoint _ _).mp h2
    rw [blockPoint_mk] at h3
    simpa [w] using h3
  · have hpos : (stabilizer G α).relIndex K ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : K ≤ stabilizer G α := Subgroup.relIndex_eq_one.mp (by omega)
    refine ⟨1, odd_one, fun ω hω => ?_⟩
    obtain ⟨k, rfl⟩ := hB ω hω
    have hk : (k : G) • α = α := hle k.2
    rw [hk, pow_one, mul_smul, hu.2, hv.2]

end OddOrbits

section Box

variable (G : Type*) [Group G] {Ω : Type*} [MulAction G Ω] {ι' : Type*}
  (Λc : ι' → Type*) [∀ i, Fintype (Λc i)]

structure CCLBox (ε : (∀ i, Λc i) → Ω) (α β : Ω) : Prop where
  injective : Function.Injective ε
  range_eq : Set.range ε = holtDelta G Ω α β
  five_le : ∀ i, 5 ≤ Fintype.card (Λc i)
  smul_eq : ∀ c ∈ longInvSwap G Ω α β, ∃ y : ∀ i, Perm (Λc i),
    (∀ i, y i ∈ longInv (Perm (Λc i)) (Λc i)) ∧ ∀ x, c • ε x = ε fun i => y i (x i)
  exists_smul_eq : ∀ y : ∀ i, Perm (Λc i), (∀ i, y i ∈ longInv (Perm (Λc i)) (Λc i)) →
    ∃ c ∈ longInvSwap G Ω α β, ∀ x, c • ε x = ε fun i => y i (x i)

variable {G Λc}

namespace CCL

omit [∀ i, Fintype (Λc i)] in
theorem pow_smul_eq_of_forall_smul_eq {ε : (∀ i, Λc i) → Ω} {g : G} {P : ∀ i, Perm (Λc i)}
    (hg : ∀ x, g • ε x = ε fun i => P i (x i)) (m : ℕ) (x : ∀ i, Λc i) :
    g ^ m • ε x = ε fun i => (P i ^ m) (x i) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_smul, hg, ih]
    simp only [pow_succ, Perm.mul_apply]

omit [∀ i, Fintype (Λc i)] in
theorem mul_smul_eq_of_forall_smul_eq {ε : (∀ i, Λc i) → Ω} {g g' : G}
    {P P' : ∀ i, Perm (Λc i)} (hg : ∀ x, g • ε x = ε fun i => P i (x i))
    (hg' : ∀ x, g' • ε x = ε fun i => P' i (x i)) (x : ∀ i, Λc i) :
    (g * g') • ε x = ε fun i => (P i * P' i) (x i) := by
  rw [mul_smul, hg', hg]
  rfl

end CCL

namespace CCLBox

variable {ε : (∀ i, Λc i) → Ω} {α β : Ω}

theorem mem_holtDelta (hbox : CCLBox G Λc ε α β) (x : ∀ i, Λc i) :
    ε x ∈ holtDelta G Ω α β :=
  hbox.range_eq ▸ ⟨x, rfl⟩

theorem nonempty (hbox : CCLBox G Λc ε α β) : Nonempty (∀ i, Λc i) := by
  have : ∀ i, Nonempty (Λc i) := fun i =>
    Fintype.card_pos_iff.mp (by have := hbox.five_le i; omega)
  infer_instance

theorem odd_card [∀ i, DecidableEq (Λc i)] (hbox : CCLBox G Λc ε α β) (i : ι') :
    Odd (Fintype.card (Λc i)) := by
  obtain ⟨x⟩ := hbox.nonempty
  obtain ⟨c, hc, -⟩ := hbox.mem_holtDelta x
  obtain ⟨y, hy, -⟩ := hbox.smul_eq c hc
  exact odd_card_of_mem_longInv_perm (hy i)

theorem eq_of_mem_orbit [Finite G] [DecidableEq ι'] [∀ i, DecidableEq (Λc i)]
    (hG : IsStarGroup G Ω) (hbox : CCLBox G Λc ε α β) {x x' : ∀ i, Λc i}
    (h : ε x' ∈ orbit (jOddCore G Ω) (ε x)) : x = x' := by
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hodd := hbox.odd_card
  obtain ⟨y, hy, y', hy', hww, hw⟩ :=
    CCL.exists_mem_longInvAt_perm_mul_mul_self_eq_one (hodd i) (hbox.five_le i) (Ne.symm hi)
  obtain ⟨z, hz⟩ := CCL.exists_forall_mem_longInvAt hodd
    (fun k => by have := hbox.five_le k; omega) x
  have hJ := fun w (hw : w ∈ longInvAt (Perm (Λc i)) (Λc i) (x i)) =>
    CCL.update_mem_longInvAt hz hw
  obtain ⟨c, hc, hcε⟩ := hbox.exists_smul_eq _ fun k => (hJ y hy k).1
  obtain ⟨c', hc', hc'ε⟩ := hbox.exists_smul_eq _ fun k => (hJ y' hy' k).1
  have hcx : c • ε x = ε x := by
    rw [hcε, CCL.apply_eq_self_of_forall_mem_longInvAt (hJ y hy)]
  have hc'x : c' • ε x = ε x := by
    rw [hc'ε, CCL.apply_eq_self_of_forall_mem_longInvAt (hJ y' hy')]
  obtain ⟨m, hm, hmB⟩ := exists_odd_pow_smul_eq_of_mem_longInvAt hG ⟨hc'.1, hc'x⟩ ⟨hc.1, hcx⟩
  have h1 := hmB _ h
  rw [CCL.pow_smul_eq_of_forall_smul_eq (CCL.mul_smul_eq_of_forall_smul_eq hcε hc'ε)] at h1
  have h2 := congrFun (hbox.injective h1) i
  simp only [Function.update_self] at h2
  obtain ⟨r, rfl⟩ := hm
  rw [pow_succ, pow_mul, sq, hww, one_pow, one_mul] at h2
  exact hw h2

theorem of_equiv {e : holtDelta G Ω α β ≃ ∀ i, Λc i} (h5 : ∀ i, 5 ≤ Fintype.card (Λc i))
    (hcoord : ∀ c ∈ longInvSwap G Ω α β, ∃ y : ∀ i, Perm (Λc i),
      (∀ i, y i ∈ longInv (Perm (Λc i)) (Λc i)) ∧ ∀ δ δ' : holtDelta G Ω α β,
        (δ' : Ω) = c • (δ : Ω) → e δ' = fun i => y i (e δ i))
    (hreal : ∀ y : ∀ i, Perm (Λc i), (∀ i, y i ∈ longInv (Perm (Λc i)) (Λc i)) →
      ∃ c ∈ longInvSwap G Ω α β, ∀ δ : holtDelta G Ω α β, ∀ δ' : holtDelta G Ω α β,
        (δ' : Ω) = c • (δ : Ω) → e δ' = fun i => y i (e δ i)) :
    CCLBox G Λc (fun x => (e.symm x : Ω)) α β := by
  have key : ∀ c ∈ longInvSwap G Ω α β, ∀ y : ∀ i, Perm (Λc i),
      (∀ δ δ' : holtDelta G Ω α β, (δ' : Ω) = c • (δ : Ω) → e δ' = fun i => y i (e δ i)) →
        ∀ x, c • (e.symm x : Ω) = (e.symm fun i => y i (x i) : Ω) := by
    intro c hc y hy x
    have hmem : c • (e.symm x : Ω) ∈ holtDelta G Ω α β := by
      have h := mem_stabilizer_iff.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hc)
      have h1 : c • (e.symm x : Ω) ∈ c • holtDelta G Ω α β :=
        Set.smul_mem_smul_set (e.symm x).2
      rwa [h] at h1
    have h1 := hy (e.symm x) ⟨_, hmem⟩ rfl
    rw [e.apply_symm_apply] at h1
    exact congrArg Subtype.val (e.eq_symm_apply.mpr h1)
  refine ⟨fun x x' h => e.symm.injective (Subtype.ext h), ?_, h5, fun c hc => ?_,
    fun y hy => ?_⟩
  · ext ω
    refine ⟨?_, fun hω => ⟨e ⟨ω, hω⟩, by simp⟩⟩
    rintro ⟨x, rfl⟩
    exact (e.symm x).2
  · obtain ⟨y, hy, hyc⟩ := hcoord c hc
    exact ⟨y, hy, key c hc y hyc⟩
  · obtain ⟨c, hc, hcy⟩ := hreal y hy
    exact ⟨c, hc, key c hc y hcy⟩

end CCLBox

end Box

section SE

variable {Δ : Type*} [Finite Δ] {M : Subgroup (Perm Δ)}

theorem IsNaturalSE.eq_of_mem_longInvAt_of_apply_eq (hM : IsNaturalSE M) {x x' : Perm Δ}
    (hxM : x ∈ M) (hx'M : x' ∈ M) {p : Δ} (hx : x ∈ longInvAt (Perm Δ) Δ p)
    (hx' : x' ∈ longInvAt (Perm Δ) Δ p) {a : Δ} (hap : a ≠ p) (hxa : x a = x' a) :
    x = x' := by
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer p
  have h1 : (⟨x, hxM⟩ : M) ∈ longInvAt M Δ p := mem_longInvAt_subgroup_perm_iff.mpr hx
  have h2 : (⟨x', hx'M⟩ : M) ∈ longInvAt M Δ p := mem_longInvAt_subgroup_perm_iff.mpr hx'
  have hq1 := CFSG.GH74.Uniqueness.Bender.rootCenter_le _ ((hA.mem_longInvAt_iff hQ).mp h1).1
  have hq2 := CFSG.GH74.Uniqueness.Bender.rootCenter_le _ ((hA.mem_longInvAt_iff hQ).mp h2).1
  have h3 := hA.eq_one_of_smul_eq hQ (mul_mem (inv_mem hq1) hq2) hap (by
    show (x⁻¹ * x') a = a
    rw [Perm.mul_apply, ← hxa]
    simp)
  exact congrArg Subtype.val (inv_mul_eq_one.mp h3)

end SE

section Involution

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem HoltData.exists_mem_L_orderOf_eq_two [Finite G] (D : HoltData G Ω) (k : D.ι)
    (a : D.Ψc k) : ∃ v : jHull G Ω, (v : G) ∈ D.L k ∧ orderOf v = 2 ∧ D.ρ k v a = a ∧
      ∀ j, j ≠ k → D.ρ j v = 1 := by
  have hM := D.factor k
  have := hM.isPretransitive
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (stabilizer (D.M k) a) := by
    have hc := (stabilizer (D.M k) a).card_mul_index
    rw [index_stabilizer_of_transitive, Nat.card_eq_fintype_card (α := D.Ψc k)] at hc
    have h2M := hM.two_dvd_card
    rw [← hc] at h2M
    exact (Nat.Coprime.dvd_mul_right (Nat.coprime_two_left.mpr (D.odd_card_Ψc k))).mp h2M
  obtain ⟨⟨⟨x, hxM⟩, hxa⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxa' : x a = a := hxa
  have hx2' : orderOf x = 2 := by
    rw [← hx2, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  obtain ⟨h, hhL, hhx⟩ := D.mem_M.mp hxM
  have hxx : x * x = 1 := by rw [← sq, ← hx2', pow_orderOf_eq_one]
  have hsq : ((h ^ 2 : jHull G Ω) : G) ∈ jOddCore G Ω := by
    have hker : h ^ 2 ∈ (D.ρ k).ker := by rw [MonoidHom.mem_ker, map_pow, hhx, sq, hxx]
    have hmem : h ^ 2 ∈ (D.L k).subgroupOf (jHull G Ω) ⊓ (D.ρ k).ker :=
      Subgroup.mem_inf.mpr ⟨pow_mem (Subgroup.mem_subgroupOf.mpr hhL) 2, hker⟩
    rw [D.inf_ker k] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  set r := orderOf (h ^ 2)
  have hr : Odd r := by
    have h1 : orderOf ((h ^ 2 : jHull G Ω) : G) ∣ Nat.card (jOddCore G Ω) :=
      Subgroup.orderOf_dvd_natCard _ hsq
    rw [Subgroup.orderOf_coe] at h1
    exact odd_card_jOddCore.of_dvd_nat h1
  have hvx : D.ρ k (h ^ r) = x := by
    obtain ⟨s, hs⟩ := hr
    rw [map_pow, hhx, hs, pow_succ, pow_mul, sq, hxx, one_pow, one_mul]
  refine ⟨h ^ r, pow_mem hhL r, orderOf_eq_prime ?_ ?_, by rw [hvx]; exact hxa', ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
  · intro h1
    rw [h1, map_one] at hvx
    rw [← hvx, orderOf_one] at hx2'
    exact absurd hx2' (by norm_num)
  · intro j hjk
    exact D.le_ker k j (Ne.symm hjk) (pow_mem (Subgroup.mem_subgroupOf.mpr hhL) r)

end Involution

end CFSG.Holt.H78
