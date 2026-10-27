module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118R

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open Equiv Equiv.Perm

namespace AltInputs

open CFSG.Open MulAction Subgroup

variable {α : Type} [Fintype α] [DecidableEq α]

theorem mul_le_pow_of_two_le {p : ℕ} (hp : 2 ≤ p) (j : ℕ) : p * j ≤ p ^ j := by
  cases j with
  | zero => simp
  | succ i =>
    have h1 : i < p ^ i := Nat.lt_pow_self (by omega)
    rw [pow_succ, mul_comm (p ^ i) p]
    exact Nat.mul_le_mul_left p h1

theorem mul_add_le_pow_of_three_le {p : ℕ} (hp : 3 ≤ p) {j : ℕ} (hj : 2 ≤ j) :
    p * j + p ≤ p ^ j := by
  induction j, hj using Nat.le_induction with
  | base => nlinarith
  | succ i hi ih =>
    rw [pow_succ]
    have h2 := Nat.mul_le_mul_right p ih
    have h3 : (p * i + p) * 3 ≤ (p * i + p) * p := Nat.mul_le_mul_left _ hp
    nlinarith

def IsPCycle (p : ℕ) (g : Perm α) : Prop := g.IsCycle ∧ g.support.card = p

section Orbits

variable (E : Subgroup (Perm α))

noncomputable instance orbQuotFintype : Fintype (MulAction.orbitRel.Quotient E α) :=
  Fintype.ofFinite _

noncomputable def orbRep (ω : MulAction.orbitRel.Quotient E α) : α := Quotient.out ω

noncomputable def orbStab (ω : MulAction.orbitRel.Quotient E α) : Subgroup E :=
  MulAction.stabilizer E (orbRep E ω)

noncomputable def orbSet (ω : MulAction.orbitRel.Quotient E α) : Set α :=
  MulAction.orbit E (orbRep E ω)

variable {E}

theorem fixes_iff_of_mem_orbit (hc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) {g : Perm α}
    (hg : g ∈ E) {o y : α} (hy : y ∈ orbit E o) : g y = y ↔ g o = o := by
  obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 hy
  show (g : Perm α) ((h : Perm α) o) = (h : Perm α) o ↔ (g : Perm α) o = o
  have hcomm : (g : Perm α) * (h : Perm α) = (h : Perm α) * (g : Perm α) := hc g hg h h.2
  have key : (g : Perm α) ((h : Perm α) o) = (h : Perm α) ((g : Perm α) o) := by
    rw [← Equiv.Perm.mul_apply, hcomm, Equiv.Perm.mul_apply]
  rw [key, Equiv.apply_eq_iff_eq]

theorem orbStab_index (ω : MulAction.orbitRel.Quotient E α) :
    (orbStab E ω).index = Nat.card (orbSet E ω) := by
  rw [Nat.card_coe_set_eq]
  exact MulAction.index_stabilizer E (orbRep E ω)

theorem sum_card_orbSet :
    ∑ ω : MulAction.orbitRel.Quotient E α, Nat.card (orbSet E ω) = Fintype.card α := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (MulAction.selfEquivSigmaOrbits E α),
    Nat.card_sigma]
  rfl

theorem index_inf_orbStab_le (s : Finset (MulAction.orbitRel.Quotient E α)) :
    (s.inf (orbStab E)).index ≤ ∏ ω ∈ s, (orbStab E ω).index := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.prod_insert ha]
    exact (Subgroup.index_inf_le).trans (Nat.mul_le_mul_left _ ih)

theorem inf_orbStab_eq_bot (hc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) :
    (Finset.univ : Finset (MulAction.orbitRel.Quotient E α)).inf (orbStab E) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hfix : ∀ y : α, (g : Perm α) y = y := by
    intro y
    have hy : y ∈ orbSet E (Quotient.mk (MulAction.orbitRel E α) y) :=
      MulAction.mem_orbit_symm.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel E α) y))
    refine (fixes_iff_of_mem_orbit hc g.2 hy).2 ?_
    have := (Finset.inf_le (Finset.mem_univ (Quotient.mk (MulAction.orbitRel E α) y)) :
      _ ≤ orbStab E (Quotient.mk (MulAction.orbitRel E α) y)) hg
    exact (MulAction.mem_stabilizer_iff).1 this
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Equiv.ext hfix)

end Orbits

theorem comm_of_isElemAbelian {p : ℕ} {E : Subgroup (Perm α)} (hE : IsElemAbelian p E) :
    ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := fun g hg h hh =>
  congrArg Subtype.val (hE.1.is_comm.comm ⟨g, hg⟩ ⟨h, hh⟩)

section Bound

variable {p : ℕ} [hp : Fact p.Prime] {E : Subgroup (Perm α)}

theorem exists_exponents (hc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) {m : ℕ}
    (hm : Nat.card E = p ^ m) :
    ∃ J : MulAction.orbitRel.Quotient E α → ℕ, (∀ ω, (orbStab E ω).index = p ^ J ω) ∧
      Nat.card E ≤ p ^ (∑ ω, J ω) ∧ (∑ ω, J ω) * p ≤ Fintype.card α := by
  have hdvd : ∀ ω, (orbStab E ω).index ∣ p ^ m := fun ω => by
    rw [← hm]
    exact Subgroup.index_dvd_card _
  choose J _ hJ using fun ω => (Nat.dvd_prime_pow hp.out).1 (hdvd ω)
  refine ⟨J, hJ, ?_, ?_⟩
  · have hle : Nat.card E ≤ ∏ ω, (orbStab E ω).index := by
      have := index_inf_orbStab_le (E := E) Finset.univ
      rw [inf_orbStab_eq_bot hc, Subgroup.index_bot] at this
      exact this
    calc Nat.card E ≤ ∏ ω, (orbStab E ω).index := hle
      _ = p ^ (∑ ω, J ω) := by
        simp_rw [hJ]
        rw [Finset.prod_pow_eq_pow_sum]
  · rw [← sum_card_orbSet, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ω _
    rw [← orbStab_index, hJ ω, mul_comm]
    exact mul_le_pow_of_two_le hp.out.two_le (J ω)

theorem card_le_pow_div {E : Subgroup (Perm α)} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (Fintype.card α / p) := by
  obtain ⟨m, hm⟩ := Lemma118R.card_eq_pow_of_elemAb hE
  obtain ⟨J, _, hle, hsum⟩ := exists_exponents (comm_of_isElemAbelian hE) hm
  have hJdiv : ∑ ω, J ω ≤ Fintype.card α / p :=
    (Nat.le_div_iff_mul_le hp.out.pos).2 hsum
  exact hle.trans (Nat.pow_le_pow_right hp.out.pos hJdiv)

end Bound

theorem isCycle_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {x : Perm α} (hx : x ^ p = 1)
    (hcard : x.support.card = p) : x.IsCycle := by
  have h1 := Equiv.Perm.cycleType_of_pow_prime_eq_one hx
  have h2 := Equiv.Perm.sum_cycleType x
  rw [h1, Multiset.sum_replicate, smul_eq_mul, hcard] at h2
  have h3 : Multiset.card x.cycleType = 1 :=
    Nat.eq_of_mul_eq_mul_right hp.out.pos (h2.trans (one_mul p).symm)
  exact Equiv.Perm.card_cycleType_eq_one.1 h3


theorem mem_orbSet_mk {E : Subgroup (Perm α)} (y : α) :
    y ∈ orbSet E (Quotient.mk (MulAction.orbitRel E α) y) := by
  exact MulAction.mem_orbit_symm.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel E α) y))

theorem exists_pcycles {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {E : Subgroup (Perm α)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ (Fintype.card α / p)) :
    ∃ (k : ℕ) (x : Fin k → Perm α), k = Fintype.card α / p ∧ (∀ i, x i ∈ E) ∧
      (∀ i, IsPCycle p (x i)) ∧ ∀ i j, i ≠ j → Equiv.Perm.Disjoint (x i) (x j) := by
  classical
  have hc := comm_of_isElemAbelian hE
  obtain ⟨m, hm⟩ := Lemma118R.card_eq_pow_of_elemAb hE
  obtain ⟨J, hJ, hle, hsum⟩ := exists_exponents (p := p) (E := E) hc hm
  set k := Fintype.card α / p with hk
  have hp1 : 1 < p := hp.out.one_lt
  have hJk : ∑ ω, J ω = k := by
    have h1 : ∑ ω, J ω ≤ k := (Nat.le_div_iff_mul_le hp.out.pos).2 hsum
    have h2 : k ≤ ∑ ω, J ω := by
      have : p ^ k ≤ p ^ (∑ ω, J ω) := hcard ▸ hle
      exact (Nat.pow_le_pow_iff_right hp1).1 this
    omega
  have hJ1 : ∀ ω, J ω ≤ 1 := by
    intro ω0
    by_contra hcon
    have h2 : 2 ≤ J ω0 := by omega
    have hsumcard : ∑ ω, p ^ J ω = Fintype.card α := by
      rw [← sum_card_orbSet]
      apply Finset.sum_congr rfl
      intro ω _
      rw [← orbStab_index, hJ ω]
    have key : p * ∑ ω, J ω + p ≤ ∑ ω, p ^ J ω := by
      rw [Finset.mul_sum, ← Finset.add_sum_erase Finset.univ (fun ω => p * J ω) (Finset.mem_univ ω0),
        ← Finset.add_sum_erase Finset.univ (fun ω => p ^ J ω) (Finset.mem_univ ω0)]
      have h1 := mul_add_le_pow_of_three_le hp3 h2
      have h3 : ∑ ω ∈ Finset.univ.erase ω0, p * J ω ≤ ∑ ω ∈ Finset.univ.erase ω0, p ^ J ω :=
        Finset.sum_le_sum fun ω _ => mul_le_pow_of_two_le hp.out.two_le (J ω)
      omega
    have hlt : Fintype.card α < p * k + p := by
      have h4 := Nat.div_add_mod (Fintype.card α) p
      have h5 := Nat.mod_lt (Fintype.card α) hp.out.pos
      rw [← hk] at h4
      omega
    rw [hJk, hsumcard] at key
    omega
  have hJ01 : ∀ ω, J ω = 0 ∨ J ω = 1 := fun ω => by
    have := hJ1 ω
    omega
  set S : Finset (MulAction.orbitRel.Quotient E α) := Finset.univ.filter (fun ω => J ω = 1)
    with hS
  have hScard : S.card = k := by
    rw [← hJk, hS, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro ω _
    rcases hJ01 ω with h | h <;> simp [h]
  have hex : ∀ ω, J ω = 1 → ∃ x : Perm α, x ∈ E ∧ IsPCycle p x ∧
      (∀ ω', ω' ≠ ω → ∀ y ∈ orbSet E ω', x y = y) ∧ (∀ y, y ∉ orbSet E ω → x y = y) := by
    intro ω hω
    have hωle : 1 ≤ k := by
      have : J ω ≤ ∑ ω', J ω' := Finset.single_le_sum (fun ω' _ => Nat.zero_le _) (Finset.mem_univ ω)
      omega
    set M : Subgroup E := (Finset.univ.erase ω).inf (orbStab E) with hM
    have hindexM : M.index ≤ p ^ (k - 1) := by
      have h1 := index_inf_orbStab_le (E := E) (Finset.univ.erase ω)
      have h2 : ∏ ω' ∈ Finset.univ.erase ω, (orbStab E ω').index = p ^ (k - 1) := by
        simp_rw [hJ]
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        have := Finset.add_sum_erase Finset.univ J (Finset.mem_univ ω)
        omega
      exact h1.trans h2.le
    have hsplit : (Finset.univ : Finset (MulAction.orbitRel.Quotient E α)).inf (orbStab E) =
        orbStab E ω ⊓ M := by
      have hins : insert ω (Finset.univ.erase ω) = Finset.univ :=
        Finset.insert_erase (Finset.mem_univ ω)
      conv_lhs => rw [← hins]
      rw [Finset.inf_insert]
    have hcardE : Nat.card E = p ^ k := hcard
    have hcardM : p ≤ Nat.card M := by
      have h3 := Subgroup.index_mul_card (H := M)
      rw [hcardE] at h3
      have h4 : p ^ k = p * p ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      apply Nat.le_of_mul_le_mul_right (c := p ^ (k - 1)) _ (pow_pos hp.out.pos (k - 1))
      calc p * p ^ (k - 1) = p ^ k := h4.symm
        _ = M.index * Nat.card M := h3.symm
        _ ≤ p ^ (k - 1) * Nat.card M := Nat.mul_le_mul_right _ hindexM
        _ = Nat.card M * p ^ (k - 1) := mul_comm _ _
    have hMne : M ≠ ⊥ := by
      rintro h
      rw [h, Subgroup.card_bot] at hcardM
      have := hp.out.two_le
      omega
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hMne
    set g0 : E := (a : E) with hg0
    have hg0M : g0 ∈ M := a.2
    have hg0ne : g0 ≠ 1 := fun h => ha (Subtype.ext h)
    have hg0E : ((g0 : E) : Perm α) ∈ E := g0.2
    have hxM : ∀ ω', ω' ≠ ω → g0 ∈ orbStab E ω' := fun ω' hne =>
      (Finset.inf_le (Finset.mem_erase.2 ⟨hne, Finset.mem_univ ω'⟩) :
        (Finset.univ.erase ω).inf (orbStab E) ≤ orbStab E ω') hg0M
    have hxnot : g0 ∉ orbStab E ω := by
      intro hmem
      have h5 : g0 ∈ (Finset.univ : Finset (MulAction.orbitRel.Quotient E α)).inf (orbStab E) := by
        rw [hsplit]
        exact ⟨hmem, hg0M⟩
      rw [inf_orbStab_eq_bot (E := E) hc, Subgroup.mem_bot] at h5
      exact hg0ne h5
    have hfixit : ∀ ω', ω' ≠ ω → ∀ y ∈ orbSet E ω', (g0 : Perm α) y = y := by
      intro ω' hne y hy
      have hstab := (MulAction.mem_stabilizer_iff).1 (hxM ω' hne)
      exact (fixes_iff_of_mem_orbit hc g0.2 hy).2 hstab
    have hmoves : ∀ y ∈ orbSet E ω, (g0 : Perm α) y ≠ y := by
      intro y hy hfix
      apply hxnot
      exact MulAction.mem_stabilizer_iff.2 ((fixes_iff_of_mem_orbit hc g0.2 hy).1 hfix)
    have hout : ∀ y, y ∉ orbSet E ω → (g0 : Perm α) y = y := by
      intro y hy
      have hne : Quotient.mk (MulAction.orbitRel E α) y ≠ ω := by
        intro h
        rw [← h] at hy
        exact hy (mem_orbSet_mk y)
      exact hfixit _ hne y (mem_orbSet_mk y)
    have hsupp : ((g0 : Perm α).support : Set α) = orbSet E ω := by
      ext y
      rw [Finset.mem_coe, Equiv.Perm.mem_support]
      constructor
      · intro hy
        by_contra hny
        exact hy (hout y hny)
      · intro hy
        exact hmoves y hy
    have hcardsupp : (g0 : Perm α).support.card = p := by
      rw [← Set.ncard_coe_finset, hsupp, ← Nat.card_coe_set_eq, ← orbStab_index, hJ ω, hω, pow_one]
    have hpow : (g0 : Perm α) ^ p = 1 := hE.2 _ g0.2
    refine ⟨(g0 : Perm α), g0.2, ⟨isCycle_of_pow_eq_one hpow hcardsupp, hcardsupp⟩, ?_, ?_⟩
    · intro ω' hne y hy
      exact hfixit ω' hne y hy
    · exact hout
  choose! xw hxw using hex
  have hScard' : Fintype.card S = k := by rw [Fintype.card_coe]; exact hScard
  let e : S ≃ Fin k := Fintype.equivFinOfCardEq hScard'
  have hJω : ∀ i : Fin k, J (e.symm i).1 = 1 := fun i =>
    (Finset.mem_filter.1 (e.symm i).2).2
  refine ⟨k, fun i => xw (e.symm i).1, rfl, fun i => (hxw _ (hJω i)).1,
    fun i => (hxw _ (hJω i)).2.1, ?_⟩
  intro i j hij y
  have hne : (e.symm i).1 ≠ (e.symm j).1 := fun h => hij (e.symm.injective (Subtype.ext h))
  by_cases hy : y ∈ orbSet E (e.symm i).1
  · exact Or.inr ((hxw _ (hJω j)).2.2.1 (e.symm i).1 hne y hy)
  · exact Or.inl ((hxw _ (hJω i)).2.2.2 y hy)


section Closure

theorem commute_closure {S : Set (Perm α)} (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {y z : Perm α}
    (hy : y ∈ Subgroup.closure S) (hz : z ∈ Subgroup.closure S) : Commute y z := by
  have h1 : ∀ s ∈ S, ∀ w ∈ Subgroup.closure S, Commute s w := by
    intro s hs w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact hS s hs x hx
    | one => exact Commute.one_right s
    | mul x y _ _ ihx ihy => exact ihx.mul_right ihy
    | inv x _ ihx => exact ihx.inv_right
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx z hz
  | one => exact Commute.one_left z
  | mul x y _ _ ihx ihy => exact ihx.mul_left ihy
  | inv x _ ihx => exact ihx.inv_left

theorem pow_closure {p : ℕ} {S : Set (Perm α)} (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hp : ∀ a ∈ S, a ^ p = 1) {y : Perm α} (hy : y ∈ Subgroup.closure S) : y ^ p = 1 := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    rw [(commute_closure hS hx hy).mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem closure_pcycles {p : ℕ} [hp : Fact p.Prime] {k : ℕ} {x : Fin k → Perm α}
    (hx : ∀ i, IsPCycle p (x i)) (hdisj : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (x i) (x j)) :
    Nat.card (Subgroup.closure (Set.range x)) = p ^ k ∧
      IsElemAbelian p (Subgroup.closure (Set.range x)) := by
  have hcomm : ∀ i j, Commute (x i) (x j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · exact (hdisj i j hij).commute
  have hSc : ∀ a ∈ Set.range x, ∀ b ∈ Set.range x, Commute a b := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j
  have hord : ∀ i, orderOf (x i) = p := fun i => by
    rw [(hx i).1.orderOf, (hx i).2]
  have hH : ∀ i, Disjoint (Subgroup.zpowers (x i))
      (⨆ (j) (_ : j ≠ i), Subgroup.zpowers (x j)) := by
    intro i
    rw [Subgroup.disjoint_def]
    intro g hg hg'
    set F : Subgroup (Perm α) := fixingSubgroup (Perm α) (((x i).support : Set α))
      with hF
    have hle : (⨆ (j) (_ : j ≠ i), Subgroup.zpowers (x j)) ≤ F := by
      refine iSup₂_le fun j hj => Subgroup.zpowers_le.2 ?_
      rw [hF, mem_fixingSubgroup_iff]
      intro y hy
      rw [Finset.mem_coe, Equiv.Perm.mem_support] at hy
      exact (hdisj i j (Ne.symm hj) y).resolve_left hy
    have hgF : g ∈ F := hle hg'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    ext y
    rw [Equiv.Perm.one_apply]
    by_cases hy : y ∈ (x i).support
    · have := (mem_fixingSubgroup_iff _).1 hgF y (by simpa using hy)
      exact this
    · have hy' : (x i) y = y := by simpa using hy
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hy' m
  have hind : iSupIndep (fun i => Subgroup.zpowers (x i)) := iSupIndep_def.2 hH
  have hcommH : Pairwise fun i j : Fin k => ∀ a b : Perm α,
      a ∈ Subgroup.zpowers (x i) → b ∈ Subgroup.zpowers (x j) → Commute a b := by
    intro i j hij a b ha hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (hcomm i j).zpow_zpow m n
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcommH) hind
  have hcl : Subgroup.closure (Set.range x) = ⨆ i, Subgroup.zpowers (x i) := by
    rw [← Set.iUnion_singleton_eq_range, Subgroup.closure_iUnion]
    simp_rw [Subgroup.zpowers_eq_closure]
  have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcommH)
  have hcard : Nat.card (Subgroup.closure (Set.range x)) = p ^ k := by
    have h1 : Nat.card (Subgroup.closure (Set.range x)) =
        Nat.card (Set.range (Subgroup.noncommPiCoprod hcommH)) := by
      rw [hcl, ← hrange]
      rfl
    rw [h1, Nat.card_range_of_injective hinj, Nat.card_pi]
    simp only [Nat.card_zpowers, hord]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨hcard, ⟨?_, fun y hy => pow_closure hSc (fun a ha => ?_) hy⟩⟩
  · exact IsMulCommutative.of_comm fun a b => Subtype.ext (commute_closure hSc a.2 b.2)
  · obtain ⟨i, rfl⟩ := ha
    rw [← hord i]
    exact pow_orderOf_eq_one _

end Closure

section Conj

theorem isPCycle_subtypePerm {p : ℕ} {β : Type} [Fintype β] [DecidableEq β] {q : β → Prop}
    [DecidablePred q] {f : Perm β} (hf : IsPCycle p f) (h1 : ∀ a, q (f a) ↔ q a)
    (h2 : ∀ a, f a ≠ a → q a) : IsPCycle p (subtypePerm f h1) := by
  have hof : ofSubtype (subtypePerm f h1) = f := ofSubtype_subtypePerm h1 h2
  constructor
  · have hct : Multiset.card (subtypePerm f h1).cycleType = 1 := by
      rw [← Equiv.Perm.cycleType_ofSubtype, hof]
      exact Equiv.Perm.card_cycleType_eq_one.2 hf.1
    exact Equiv.Perm.card_cycleType_eq_one.1 hct
  · have hs : (subtypePerm f h1).support.card = f.support.card := by
      rw [← Finset.card_map (Function.Embedding.subtype q), ← Equiv.Perm.support_ofSubtype, hof]
    exact hs.trans hf.2

theorem conj_pcycles_aux {p : ℕ} [hp : Fact p.Prime] (k : ℕ) :
    ∀ {β : Type} [Fintype β] [DecidableEq β] (x c : Fin k → Perm β),
      (∀ i, IsPCycle p (x i)) → (∀ i, IsPCycle p (c i)) →
      (∀ i j, i ≠ j → Equiv.Perm.Disjoint (x i) (x j)) →
      (∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i) (c j)) →
      ∃ σ : Perm β, ∀ i, σ * x i * σ⁻¹ = c i := by
  induction k with
  | zero =>
    intro β _ _ x c _ _ _ _
    exact ⟨1, fun i => i.elim0⟩
  | succ k ih =>
    intro β _ _ x c hx hc hxd hcd
    classical
    obtain ⟨τ, hτ⟩ := isConj_iff.1
      ((hx 0).1.isConj (hc 0).1 ((hx 0).2.trans (hc 0).2.symm))
    set T : Finset β := (c 0).support with hT
    let x' : Fin k → Perm β := fun i => τ * x i.succ * τ⁻¹
    have hfixT : ∀ i : Fin k, ∀ a, a ∈ T → x' i a = a := by
      intro i a ha
      have hca : c 0 a ≠ a := Equiv.Perm.mem_support.1 ha
      have hs : x 0 (τ⁻¹ a) ≠ τ⁻¹ a := by
        intro h
        apply hca
        rw [← hτ]
        simp only [Equiv.Perm.mul_apply]
        rw [h]
        simp
      have hx1 : x i.succ (τ⁻¹ a) = τ⁻¹ a :=
        ((hxd 0 i.succ (Fin.succ_ne_zero i).symm (τ⁻¹ a)).resolve_left hs)
      show τ (x i.succ (τ⁻¹ a)) = a
      rw [hx1]
      simp
    have hfixTc : ∀ i : Fin k, ∀ a, a ∈ T → c i.succ a = a := by
      intro i a ha
      have hca : c 0 a ≠ a := Equiv.Perm.mem_support.1 ha
      exact (hcd 0 i.succ (Fin.succ_ne_zero i).symm a).resolve_left hca
    have hcomp : ∀ i : Fin k, ∀ a, a ∉ T → x' i a ∉ T := by
      intro i a ha hmem
      have h1 := hfixT i _ hmem
      apply ha
      have h2 : x' i a = x' i (x' i a) := h1.symm
      have h3 : a = x' i a := (x' i).injective h2
      exact (congrArg (fun z => z ∈ T) h3).mpr hmem
    have hcompc : ∀ i : Fin k, ∀ a, a ∉ T → c i.succ a ∉ T := by
      intro i a ha hmem
      have h1 := hfixTc i _ hmem
      apply ha
      have h2 : c i.succ a = c i.succ (c i.succ a) := h1.symm
      have h3 : a = c i.succ a := (c i.succ).injective h2
      exact (congrArg (fun z => z ∈ T) h3).mpr hmem
    have hpx : ∀ i : Fin k, ∀ a, (fun b => b ∉ T) (x' i a) ↔ (fun b => b ∉ T) a := by
      intro i a
      constructor
      · intro h hmem
        exact h (by rw [hfixT i a hmem]; exact hmem)
      · intro h
        exact hcomp i a h
    have hpc : ∀ i : Fin k, ∀ a, (fun b => b ∉ T) (c i.succ a) ↔ (fun b => b ∉ T) a := by
      intro i a
      constructor
      · intro h hmem
        exact h (by rw [hfixTc i a hmem]; exact hmem)
      · intro h
        exact hcompc i a h
    have hx'cyc : ∀ i : Fin k, IsPCycle p (x' i) := fun i =>
      ⟨(hx i.succ).1.conj, by rw [Equiv.Perm.support_conj, Finset.card_map, (hx i.succ).2]⟩
    have hx'd : ∀ i j : Fin k, i ≠ j → Equiv.Perm.Disjoint (x' i) (x' j) := by
      intro i j hij a
      rcases hxd i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) (τ⁻¹ a) with h | h
      · left
        simp only [x', Equiv.Perm.mul_apply]
        rw [h]
        simp
      · right
        simp only [x', Equiv.Perm.mul_apply]
        rw [h]
        simp
    let xs : Fin k → Perm {a // a ∉ T} := fun i =>
      subtypePerm (p := fun b => b ∉ T) (x' i) (hpx i)
    let cs : Fin k → Perm {a // a ∉ T} := fun i =>
      subtypePerm (p := fun b => b ∉ T) (c i.succ) (hpc i)
    have hxs : ∀ i, IsPCycle p (xs i) := fun i =>
      isPCycle_subtypePerm (q := fun b => b ∉ T) (hx'cyc i) (hpx i)
        (fun a ha hT => ha (hfixT i a hT))
    have hcs : ∀ i, IsPCycle p (cs i) := fun i =>
      isPCycle_subtypePerm (q := fun b => b ∉ T) (hc i.succ) (hpc i)
        (fun a ha hT => ha (hfixTc i a hT))
    have hxsd : ∀ i j : Fin k, i ≠ j → Equiv.Perm.Disjoint (xs i) (xs j) := by
      intro i j hij b
      rcases hx'd i j hij (b : β) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    have hcsd : ∀ i j : Fin k, i ≠ j → Equiv.Perm.Disjoint (cs i) (cs j) := by
      intro i j hij b
      rcases hcd i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) (b : β) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    obtain ⟨σ'', hσ''⟩ := ih (β := {a // a ∉ T}) xs cs hxs hcs hxsd hcsd
    let σ : Perm β := ofSubtype σ''
    have hσT : ∀ a ∈ T, σ a = a := fun a ha =>
      ofSubtype_apply_of_not_mem σ'' (fun h => h ha)
    have hσout : ∀ a, a ∉ T → σ a ∉ T := by
      intro a ha hb
      have h1 : σ (σ a) = σ a := hσT _ hb
      have h2 : a = σ a := σ.injective h1.symm
      exact ha ((congrArg (fun z => z ∈ T) h2).mpr hb)
    have hxsOf : ∀ i, ofSubtype (xs i) = x' i := fun i =>
      ofSubtype_subtypePerm (hpx i) (fun a ha hT => ha (hfixT i a hT))
    have hcsOf : ∀ i, ofSubtype (cs i) = c i.succ := fun i =>
      ofSubtype_subtypePerm (hpc i) (fun a ha hT => ha (hfixTc i a hT))
    have hσc : ∀ i : Fin k, σ * x' i * σ⁻¹ = c i.succ := by
      intro i
      have h := congrArg ofSubtype (hσ'' i)
      rw [map_mul, map_mul, map_inv, hxsOf, hcsOf] at h
      exact h
    have hσc0 : σ * c 0 = c 0 * σ := by
      ext a
      simp only [Equiv.Perm.mul_apply]
      by_cases ha : a ∈ T
      · have hmem : c 0 a ∈ T := Equiv.Perm.apply_mem_support.2 ha
        rw [hσT _ hmem, hσT a ha]
      · have hca : c 0 a = a := by
          by_contra hne
          exact ha (Equiv.Perm.mem_support.2 hne)
        have hcfix : c 0 (σ a) = σ a := by
          by_contra hne
          exact hσout a ha (Equiv.Perm.mem_support.2 hne)
        rw [hca, hcfix]
    refine ⟨σ * τ, ?_⟩
    intro i
    cases i using Fin.cases with
    | zero =>
      show σ * τ * x 0 * (σ * τ)⁻¹ = c 0
      calc σ * τ * x 0 * (σ * τ)⁻¹ = σ * (τ * x 0 * τ⁻¹) * σ⁻¹ := by group
        _ = σ * c 0 * σ⁻¹ := by rw [hτ]
        _ = c 0 := by rw [hσc0]; group
    | succ i =>
      show σ * τ * x i.succ * (σ * τ)⁻¹ = c i.succ
      calc σ * τ * x i.succ * (σ * τ)⁻¹ = σ * (τ * x i.succ * τ⁻¹) * σ⁻¹ := by group
        _ = σ * x' i * σ⁻¹ := rfl
        _ = c i.succ := hσc i

end Conj

section Model

variable {p k r : ℕ}

@[expose] def addFun (i : Fin k) (s : ZMod p) : (Fin k × ZMod p) ⊕ Fin r → (Fin k × ZMod p) ⊕ Fin r
  | Sum.inl (j, t) => Sum.inl (j, if j = i then t + s else t)
  | Sum.inr u => Sum.inr u

theorem addFun_addFun (i : Fin k) (s s' : ZMod p) (z : (Fin k × ZMod p) ⊕ Fin r) :
    addFun i s (addFun i s' z) = addFun i (s + s') z := by
  rcases z with ⟨j, t⟩ | u
  · by_cases h : j = i
    · simp only [addFun, h, if_true]
      congr 1
      ring
    · simp [addFun, h]
  · rfl

theorem addFun_zero (i : Fin k) (z : (Fin k × ZMod p) ⊕ Fin r) : addFun i 0 z = z := by
  rcases z with ⟨j, t⟩ | u
  · by_cases h : j = i <;> simp [addFun, h]
  · rfl

@[expose] def addBlock (i : Fin k) (s : ZMod p) : Perm ((Fin k × ZMod p) ⊕ Fin r) where
  toFun := addFun i s
  invFun := addFun i (-s)
  left_inv z := by
    rw [addFun_addFun, neg_add_cancel, addFun_zero]
  right_inv z := by
    rw [addFun_addFun, add_neg_cancel, addFun_zero]

theorem addBlock_apply (i : Fin k) (s : ZMod p) (z : (Fin k × ZMod p) ⊕ Fin r) :
    addBlock (r := r) i s z = addFun i s z := rfl

theorem addBlock_mul (i : Fin k) (s s' : ZMod p) :
    addBlock (r := r) i s * addBlock i s' = addBlock i (s + s') :=
  Equiv.ext fun z => addFun_addFun i s s' z

theorem addBlock_zero (i : Fin k) : addBlock (p := p) (r := r) i 0 = 1 :=
  Equiv.ext fun z => addFun_zero i z

theorem addBlock_pow (i : Fin k) (s : ZMod p) (n : ℕ) :
    addBlock (r := r) i s ^ n = addBlock i ((n : ZMod p) * s) := by
  induction n with
  | zero => simp [addBlock_zero]
  | succ n ih =>
    rw [pow_succ, ih, addBlock_mul]
    congr 1
    push_cast
    ring

@[expose] def mulFun (i : Fin k) (a : ZMod p) : (Fin k × ZMod p) ⊕ Fin r → (Fin k × ZMod p) ⊕ Fin r
  | Sum.inl (j, t) => Sum.inl (j, if j = i then a * t else t)
  | Sum.inr u => Sum.inr u

@[expose] def mulBlock [Fact p.Prime] (i : Fin k) (a : ZMod p) (ha : a ≠ 0) :
    Perm ((Fin k × ZMod p) ⊕ Fin r) where
  toFun := mulFun i a
  invFun := mulFun i a⁻¹
  left_inv z := by
    rcases z with ⟨j, t⟩ | u
    · by_cases h : j = i <;> simp [mulFun, h, ha]
    · rfl
  right_inv z := by
    rcases z with ⟨j, t⟩ | u
    · by_cases h : j = i <;> simp [mulFun, h, ha]
    · rfl

theorem mulBlock_apply_inr [Fact p.Prime] (i : Fin k) (a : ZMod p) (ha : a ≠ 0) (u : Fin r) :
    mulBlock (p := p) (r := r) i a ha (Sum.inr u) = Sum.inr u := rfl

theorem mulBlock_apply_inl [Fact p.Prime] (i j : Fin k) (a : ZMod p) (ha : a ≠ 0) (t : ZMod p) :
    mulBlock (r := r) i a ha (Sum.inl (j, t)) = Sum.inl (j, if j = i then a * t else t) := rfl

theorem mulBlock_pow_apply [Fact p.Prime] (i j : Fin k) (a : ZMod p) (ha : a ≠ 0) (n : ℕ)
    (t : ZMod p) :
    (mulBlock (r := r) i a ha ^ n) (Sum.inl (j, t)) =
      Sum.inl (j, if j = i then a ^ n * t else t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, mulBlock_apply_inl]
    by_cases h : j = i
    · simp [h, pow_succ]
      ring
    · simp [h]

theorem mulBlock_conj_addBlock [Fact p.Prime] (i0 i : Fin k) (a : ZMod p) (ha : a ≠ 0)
    (s : ZMod p) :
    mulBlock (r := r) i0 a ha * addBlock i s =
      addBlock i (if i = i0 then a * s else s) * mulBlock i0 a ha := by
  ext z
  rcases z with ⟨j, t⟩ | u
  · simp only [Equiv.Perm.mul_apply, addBlock_apply, mulBlock_apply_inl]
    by_cases h1 : j = i <;> by_cases h2 : j = i0 <;> by_cases h3 : i = i0 <;>
      simp [addFun, mulBlock_apply_inl, h1, h2, h3, mul_add] <;>
      split_ifs with h4 <;> simp_all
  · rfl

section ModelProps

variable [hp : Fact p.Prime]

theorem addBlock_isPCycle [NeZero p] (i : Fin k) : IsPCycle p (addBlock (p := p) (r := r) i 1) := by
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hsupp : (addBlock (p := p) (r := r) i 1).support = Finset.univ.image
      (fun t : ZMod p => (Sum.inl (i, t) : (Fin k × ZMod p) ⊕ Fin r)) := by
    ext z
    rcases z with ⟨j, t⟩ | u
    · by_cases h : j = i
      · subst h
        simp [Equiv.Perm.mem_support, addBlock_apply, addFun, h10]
      · simp [Equiv.Perm.mem_support, addBlock_apply, addFun, h, Ne.symm h]
    · simp [Equiv.Perm.mem_support, addBlock_apply, addFun]
  refine ⟨⟨Sum.inl (i, 0), ?_, ?_⟩, ?_⟩
  · simp [addBlock_apply, addFun, h10]
  · rintro (⟨j, t⟩ | u) hy
    · have hj : j = i := by
        by_contra hj
        apply hy
        simp [addBlock_apply, addFun, hj]
      subst hj
      refine ⟨(t.val : ℤ), ?_⟩
      rw [zpow_natCast, addBlock_pow, addBlock_apply]
      simp [addFun, ZMod.natCast_zmod_val]
    · exact absurd (by simp [addBlock_apply, addFun]) hy
  · rw [hsupp, Finset.card_image_of_injective _ (fun t t' h => by simpa using h),
      Finset.card_univ, ZMod.card]

theorem addBlock_disjoint {i j : Fin k} (hij : i ≠ j) :
    Equiv.Perm.Disjoint (addBlock (p := p) (r := r) i 1) (addBlock (p := p) j 1) := by
  rintro (⟨l, t⟩ | u)
  · by_cases hl : l = i
    · subst hl
      right
      simp [addBlock_apply, addFun, hij]
    · left
      simp [addBlock_apply, addFun, hl]
  · left
    rfl

theorem addBlock_sign [NeZero p] (hp2 : p ≠ 2) (i : Fin k) :
    sign (addBlock (p := p) (r := r) i 1) = 1 := by
  rw [(addBlock_isPCycle i).1.sign, (addBlock_isPCycle i).2, (hp.out.odd_of_ne_two hp2).neg_one_pow]
  simp

theorem mulBlock_isCycle [NeZero p] (i : Fin k) (a : ZMod p) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (hgen : ∀ t : ZMod p, t ≠ 0 → ∃ m : ℕ, a ^ m = t) :
    (mulBlock (p := p) (r := r) i a ha).IsCycle := by
  refine ⟨Sum.inl (i, 1), ?_, ?_⟩
  · simp [mulBlock_apply_inl, ha1]
  · rintro (⟨j, t⟩ | u) hy
    · have hj : j = i := by
        by_contra hj
        apply hy
        simp [mulBlock_apply_inl, hj]
      subst hj
      have ht : t ≠ 0 := by
        rintro rfl
        apply hy
        simp [mulBlock_apply_inl]
      obtain ⟨m, hm⟩ := hgen t ht
      refine ⟨(m : ℤ), ?_⟩
      rw [zpow_natCast, mulBlock_pow_apply]
      simp [hm]
    · exact absurd (mulBlock_apply_inr i a ha u) hy

theorem mulBlock_support_card [NeZero p] (i : Fin k) (a : ZMod p) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    (mulBlock (p := p) (r := r) i a ha).support.card = p - 1 := by
  have key : ∀ t : ZMod p, a * t = t ↔ t = 0 := by
    intro t
    constructor
    · intro h
      have h2 : (a - 1) * t = 0 := by rw [sub_mul, h, one_mul, sub_self]
      rcases mul_eq_zero.1 h2 with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) ha1
      · exact h1
    · rintro rfl
      simp
  have hsupp : (mulBlock (p := p) (r := r) i a ha).support = (Finset.univ.erase (0 : ZMod p)).image
      (fun t : ZMod p => (Sum.inl (i, t) : (Fin k × ZMod p) ⊕ Fin r)) := by
    ext z
    rcases z with ⟨j, t⟩ | u
    · by_cases h : j = i
      · subst h
        simp [Equiv.Perm.mem_support, mulBlock_apply_inl, key]
      · simp [Equiv.Perm.mem_support, mulBlock_apply_inl, h, Ne.symm h]
    · simp [Equiv.Perm.mem_support, mulBlock_apply_inl, mulBlock_apply_inr]
  rw [hsupp, Finset.card_image_of_injective _ (fun t t' h => by simpa using h),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

theorem mulBlock_sign [NeZero p] (hp2 : p ≠ 2) (i : Fin k) (a : ZMod p) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (hgen : ∀ t : ZMod p, t ≠ 0 → ∃ m : ℕ, a ^ m = t) :
    sign (mulBlock (p := p) (r := r) i a ha) = -1 := by
  rw [(mulBlock_isCycle i a ha ha1 hgen).sign, mulBlock_support_card i a ha ha1]
  have heven : Even (p - 1) := hp.out.even_sub_one hp2
  rw [heven.neg_one_pow]

end ModelProps

end Model

section Standard

theorem exists_gen_units {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ a : ZMod p, a ≠ 0 ∧ a ≠ 1 ∧ ∀ t : ZMod p, t ≠ 0 → ∃ m : ℕ, a ^ m = t := by
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hgp : ∀ x : (ZMod p)ˣ, x ∈ Submonoid.powers g := fun x =>
    mem_powers_iff_mem_zpowers.2 (hg x)
  refine ⟨(g : ZMod p), g.ne_zero, ?_, ?_⟩
  · intro h1
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 (hgp (-1))
    have h2 : ((g ^ m : (ZMod p)ˣ) : ZMod p) = ((-1 : (ZMod p)ˣ) : ZMod p) := by rw [hm]
    rw [Units.val_pow_eq_pow_val, h1, one_pow] at h2
    haveI : Fact (2 < p) := ⟨by have := hp.out.two_le; omega⟩
    exact ZMod.neg_one_ne_one h2.symm
  · intro t ht
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 (hgp (Units.mk0 t ht))
    refine ⟨m, ?_⟩
    have h2 : ((g ^ m : (ZMod p)ˣ) : ZMod p) = t := by rw [hm]; rfl
    rwa [Units.val_pow_eq_pow_val] at h2

theorem conj_closure_le {α : Type} [Group α] (f : α) (S : Set α)
    (h : ∀ s ∈ S, f * s * f⁻¹ ∈ Subgroup.closure S) :
    ∀ g ∈ Subgroup.closure S, f * g * f⁻¹ ∈ Subgroup.closure S := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have : f * (x * y) * f⁻¹ = (f * x * f⁻¹) * (f * y * f⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  | inv x _ hx =>
    have : f * x⁻¹ * f⁻¹ = (f * x * f⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

end Standard

section Transport

variable {β α : Type} [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]

theorem permCongr_pow_apply (ψ : β ≃ α) (σ : Perm β) (n : ℤ) (x : β) :
    ((ψ.permCongr σ) ^ n) (ψ x) = ψ ((σ ^ n) x) := by
  have h : ψ.permCongr (σ ^ n) = (ψ.permCongr σ) ^ n := map_zpow ψ.permCongrHom σ n
  rw [← h, Equiv.permCongr_apply, Equiv.symm_apply_apply]

theorem permCongr_isCycle_iff (ψ : β ≃ α) (σ : Perm β) :
    (ψ.permCongr σ).IsCycle ↔ σ.IsCycle := by
  constructor
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨x, rfl⟩ := ψ.surjective y
    refine ⟨x, ?_, ?_⟩
    · intro h
      apply hy1
      rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, h]
    · intro z hz
      have hz' : (ψ.permCongr σ) (ψ z) ≠ ψ z := by
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
        exact fun h => hz (ψ.injective h)
      obtain ⟨n, hn⟩ := hy2 hz'
      rw [permCongr_pow_apply] at hn
      exact ⟨n, ψ.injective hn⟩
  · rintro ⟨x, hx1, hx2⟩
    refine ⟨ψ x, ?_, ?_⟩
    · rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      exact fun h => hx1 (ψ.injective h)
    · intro w hw
      obtain ⟨z, rfl⟩ := ψ.surjective w
      have hz : σ z ≠ z := by
        intro h
        apply hw
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, h]
      obtain ⟨n, hn⟩ := hx2 hz
      refine ⟨n, ?_⟩
      rw [permCongr_pow_apply, hn]

theorem permCongr_disjoint (ψ : β ≃ α) {f g : Perm β} (h : Equiv.Perm.Disjoint f g) :
    Equiv.Perm.Disjoint (ψ.permCongr f) (ψ.permCongr g) := by
  intro x
  rcases h (ψ.symm x) with h1 | h1
  · exact Or.inl (by rw [Equiv.permCongr_apply, h1, Equiv.apply_symm_apply])
  · exact Or.inr (by rw [Equiv.permCongr_apply, h1, Equiv.apply_symm_apply])

theorem permCongr_support_card (ψ : β ≃ α) (σ : Perm β) :
    (ψ.permCongr σ).support.card = σ.support.card := by
  have h : (ψ.permCongr σ).support = σ.support.map ψ.toEmbedding := by
    ext z
    rw [Equiv.Perm.mem_support, Finset.mem_map]
    constructor
    · intro hz
      refine ⟨ψ.symm z, ?_, by simp⟩
      rw [Equiv.Perm.mem_support]
      intro h
      apply hz
      rw [Equiv.permCongr_apply, h, Equiv.apply_symm_apply]
    · rintro ⟨w, hw, rfl⟩
      rw [Equiv.Perm.mem_support] at hw
      show (ψ.permCongr σ) (ψ w) ≠ ψ w
      rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
      exact fun h => hw (ψ.injective h)
  rw [h, Finset.card_map]

end Transport

section StdFamily

theorem permCongr_inv' {β α : Type} [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]
    (ψ : β ≃ α) (σ : Perm β) : ψ.permCongr σ⁻¹ = (ψ.permCongr σ)⁻¹ :=
  map_inv ψ.permCongrHom σ

theorem permCongr_pow' {β α : Type} [Fintype β] [DecidableEq β] [Fintype α] [DecidableEq α]
    (ψ : β ≃ α) (σ : Perm β) (n : ℕ) : ψ.permCongr (σ ^ n) = (ψ.permCongr σ) ^ n :=
  map_pow ψ.permCongrHom σ n

theorem addBlock_eq_pow {p k r : ℕ} [NeZero p] (i : Fin k) (s : ZMod p) :
    addBlock (r := r) i s = addBlock (r := r) i 1 ^ s.val := by
  rw [addBlock_pow, ZMod.natCast_zmod_val, mul_one]

theorem mulBlock_conj_addBlock' {p k r : ℕ} [Fact p.Prime] (i0 i : Fin k) (a : ZMod p)
    (ha : a ≠ 0) (s : ZMod p) :
    mulBlock (r := r) i0 a ha * addBlock i s * (mulBlock i0 a ha)⁻¹ =
      addBlock i (if i = i0 then a * s else s) := by
  rw [mulBlock_conj_addBlock, mul_inv_cancel_right]

theorem map_conj_closure_eq {G : Type} [Group G] [Finite G] (S : Set G) (f : G)
    (h : ∀ s ∈ S, f * s * f⁻¹ ∈ Subgroup.closure S) :
    (Subgroup.closure S).map (MulAut.conj f).toMonoidHom = Subgroup.closure S := by
  have hle : (Subgroup.closure S).map (MulAut.conj f).toMonoidHom ≤ Subgroup.closure S := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact conj_closure_le f S h y hy
  have hinj : Function.Injective (MulAut.conj f).toMonoidHom := fun x y hxy =>
    (MulAut.conj f).injective hxy
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (Subgroup.card_map_of_injective hinj).symm)

theorem std_family {p k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hkp : k * p ≤ Fintype.card α) :
    ∃ (c : Fin k → Perm α) (π : Perm α),
      (∀ i, IsPCycle p (c i)) ∧ (∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i) (c j)) ∧
      sign π = -1 ∧ (∀ i, π * c i * π⁻¹ ∈ Subgroup.closure (Set.range c)) := by
  obtain ⟨a, ha0, ha1, hgen⟩ := exists_gen_units hp2
  have hcard : Fintype.card ((Fin k × ZMod p) ⊕ Fin (Fintype.card α - k * p)) =
      Fintype.card α := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card]
    omega
  let e : ((Fin k × ZMod p) ⊕ Fin (Fintype.card α - k * p)) ≃ α :=
    Fintype.equivOfCardEq hcard
  let i0 : Fin k := ⟨0, hk⟩
  refine ⟨fun i => e.permCongr (addBlock (p := p) (r := Fintype.card α - k * p) i 1),
    e.permCongr (mulBlock (p := p) (r := Fintype.card α - k * p) i0 a ha0), ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(permCongr_isCycle_iff e _).2 (addBlock_isPCycle i).1, ?_⟩
    rw [permCongr_support_card]
    exact (addBlock_isPCycle i).2
  · intro i j hij
    exact permCongr_disjoint e (addBlock_disjoint hij)
  · rw [Equiv.Perm.sign_permCongr]
    exact mulBlock_sign hp2 i0 a ha0 ha1 hgen
  · intro i
    have hc : e.permCongr (mulBlock (p := p) (r := Fintype.card α - k * p) i0 a ha0) *
        e.permCongr (addBlock (p := p) (r := Fintype.card α - k * p) i 1) *
        (e.permCongr (mulBlock (p := p) (r := Fintype.card α - k * p) i0 a ha0))⁻¹ =
        e.permCongr (addBlock (p := p) (r := Fintype.card α - k * p) i
          (if i = i0 then a * 1 else 1)) := by
      rw [← mulBlock_conj_addBlock', ← permCongr_inv', ← Equiv.permCongr_mul,
        ← Equiv.permCongr_mul]
    show _ ∈ Subgroup.closure (Set.range fun i => e.permCongr
      (addBlock (p := p) (r := Fintype.card α - k * p) i 1))
    rw [hc, addBlock_eq_pow, permCongr_pow']
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

end StdFamily

section Core

variable {α : Type} [Fintype α] [DecidableEq α]

theorem mem_iff_conj_mem {G : Type} [Group G] {σ : G} {E F : Subgroup G}
    (h : E.map (MulAut.conj σ).toMonoidHom = F) (x : G) : x ∈ E ↔ σ * x * σ⁻¹ ∈ F := by
  rw [← h, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := (MulAut.conj σ).injective hyx
    rw [← hyx']
    exact hy

theorem pcycle_sign {p : ℕ} (hp2 : p ≠ 2) [hp : Fact p.Prime] {x : Perm α} (hx : IsPCycle p x) :
    sign x = 1 := by
  rw [hx.1.sign, hx.2, (hp.out.odd_of_ne_two hp2).neg_one_pow]
  simp

theorem standard_props {p k : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {c : Fin k → Perm α}
    (hc : ∀ i, IsPCycle p (c i)) (hcd : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i) (c j)) :
    Nat.card (Subgroup.closure (Set.range c)) = p ^ k ∧
      IsElemAbelian p (Subgroup.closure (Set.range c)) ∧
      Subgroup.closure (Set.range c) ≤ alternatingGroup α := by
  refine ⟨(closure_pcycles hc hcd).1, (closure_pcycles hc hcd).2, ?_⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact (mem_alternatingGroup).2 (pcycle_sign hp2 (hc i))

theorem conj_to_std {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup (Perm α)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ (Fintype.card α / p))
    (hEA : E ≤ alternatingGroup α) {c : Fin (Fintype.card α / p) → Perm α} {π : Perm α}
    (hc : ∀ i, IsPCycle p (c i)) (hcd : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i) (c j))
    (hπ : sign π = -1) (hπn : ∀ i, π * c i * π⁻¹ ∈ Subgroup.closure (Set.range c)) :
    ∃ σ : Perm α, sign σ = 1 ∧ ∀ y : Perm α, y ∈ E ↔ σ * y * σ⁻¹ ∈ Subgroup.closure (Set.range c) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.out.two_le
    omega
  obtain ⟨k, x, hk, hxE, hx, hxd⟩ := exists_pcycles hp3 hE hcard
  subst hk
  have hEx : Subgroup.closure (Set.range x) = E := by
    have hle : Subgroup.closure (Set.range x) ≤ E := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hxE i
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, (closure_pcycles hx hxd).1])
  obtain ⟨σ₀, hσ₀⟩ := conj_pcycles_aux (Fintype.card α / p) x c hx hc hxd hcd
  have hmap : E.map (MulAut.conj σ₀).toMonoidHom = Subgroup.closure (Set.range c) := by
    rw [← hEx, MonoidHom.map_closure]
    congr 1
    rw [← Set.range_comp]
    congr 1
    funext i
    exact hσ₀ i
  have hE0 : ∀ z : Perm α, z ∈ Subgroup.closure (Set.range c) ↔
      π * z * π⁻¹ ∈ Subgroup.closure (Set.range c) :=
    mem_iff_conj_mem (map_conj_closure_eq (Set.range c) π (by rintro _ ⟨i, rfl⟩; exact hπn i))
  have hchar : ∀ y : Perm α, y ∈ E ↔ σ₀ * y * σ₀⁻¹ ∈ Subgroup.closure (Set.range c) :=
    fun y => mem_iff_conj_mem hmap y
  rcases Int.units_eq_one_or (sign σ₀) with h1 | h1
  · exact ⟨σ₀, h1, hchar⟩
  · refine ⟨π * σ₀, ?_, ?_⟩
    · rw [map_mul, hπ, h1]
      rfl
    · intro y
      have heq : π * σ₀ * y * (π * σ₀)⁻¹ = π * (σ₀ * y * σ₀⁻¹) * π⁻¹ := by group
      rw [heq]
      exact (hchar y).trans (hE0 _)

end Core

section Core2

variable {α : Type} [Fintype α] [DecidableEq α]

theorem isElemAbelian_map {G H : Type} [Group G] [Group H] {p : ℕ} {E : Subgroup G}
    (f : G →* H) (hf : Function.Injective f) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · rintro a b
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    have hcomm : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    show (a : H) * (b : H) = (b : H) * (a : H)
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hcomm]
  · rintro _ hx
    obtain ⟨x, hx', rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 x hx', map_one]

theorem conj_symm_mem {G : Type} [Group G] {σ : G} {E : Subgroup G}
    (h : E.map (MulAut.conj σ).toMonoidHom = E) {z : G} (hz : z ∈ E) : σ⁻¹ * z * σ ∈ E := by
  have hz' : z ∈ E.map (MulAut.conj σ).toMonoidHom := by rw [h]; exact hz
  rw [Subgroup.mem_map_equiv] at hz'
  simpa [MulAut.conj_symm_apply] using hz'

theorem mem_map_conj_iff {G : Type} [Group G] (σ : G) (E : Subgroup G) (y : G) :
    y ∈ E.map (MulAut.conj σ).toMonoidHom ↔ σ⁻¹ * y * σ ∈ E := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem standard_product_cycleType {p k : ℕ} [hp : Fact p.Prime] {c : Fin k → Perm α}
    (hc : ∀ i, IsPCycle p (c i)) (hcd : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (c i) (c j))
    (s : Finset (Fin k)) :
    ∃ z : Perm α, z ∈ Subgroup.closure (Set.range c) ∧ z.cycleType = Multiset.replicate s.card p := by
  have hcomm : (s : Set (Fin k)).Pairwise fun i j => Commute (c i) (c j) :=
    fun i _ j _ hij => (hcd i j hij).commute
  have hdisj : (s : Set (Fin k)).Pairwise fun i j => Equiv.Perm.Disjoint (c i) (c j) :=
    fun i _ j _ hij => hcd i j hij
  refine ⟨s.noncommProd c hcomm, ?_, ?_⟩
  · exact Subgroup.noncommProd_mem _ _ (fun i _ => Subgroup.subset_closure (Set.mem_range_self i))
  · rw [Equiv.Perm.Disjoint.cycleType_noncommProd hdisj hcomm]
    have h1 : s.sum (fun i => (c i).cycleType) = s.sum (fun _ => ({p} : Multiset ℕ)) :=
      Finset.sum_congr rfl fun i _ => by rw [(hc i).1.cycleType, (hc i).2]
    rw [h1, Finset.sum_const, Multiset.nsmul_singleton]

end Core2

section Core3

variable {α : Type} [Fintype α] [DecidableEq α]

theorem isElemAbelian_bot {p : ℕ} : IsElemAbelian p (⊥ : Subgroup (Perm α)) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · rintro a b
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    rw [Subgroup.mem_bot] at ha hb
    subst ha
    subst hb
    rfl
  · rintro x hx
    rw [Subgroup.mem_bot] at hx
    rw [hx, one_pow]

theorem core_exists {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ E : Subgroup (Perm α), E ≤ alternatingGroup α ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ (Fintype.card α / p) := by
  by_cases hk0 : Fintype.card α / p = 0
  · refine ⟨⊥, bot_le, isElemAbelian_bot, ?_⟩
    rw [Subgroup.card_bot, hk0, pow_zero]
  · obtain ⟨c, π, hc, hcd, -, -⟩ :=
      std_family hp2 (Nat.one_le_iff_ne_zero.2 hk0) (Nat.div_mul_le_self _ _)
    obtain ⟨h1, h2, h3⟩ := standard_props hp2 hc hcd
    exact ⟨_, h3, h2, h1⟩

theorem core_conj {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {E₁ E₂ : Subgroup (Perm α)}
    (h₁ : IsElemAbelian p E₁) (h₂ : IsElemAbelian p E₂)
    (c₁ : Nat.card E₁ = p ^ (Fintype.card α / p)) (c₂ : Nat.card E₂ = p ^ (Fintype.card α / p))
    (A₁ : E₁ ≤ alternatingGroup α) (A₂ : E₂ ≤ alternatingGroup α) :
    ∃ g ∈ alternatingGroup α, E₂ = E₁.map (MulAut.conj g).toMonoidHom := by
  by_cases hk0 : Fintype.card α / p = 0
  · have e₁ : E₁ = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [c₁, hk0, pow_zero])
    have e₂ : E₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [c₂, hk0, pow_zero])
    refine ⟨1, one_mem _, ?_⟩
    rw [e₁, e₂, Subgroup.map_bot]
  · obtain ⟨c, π, hc, hcd, hπ, hπn⟩ :=
      std_family hp2 (Nat.one_le_iff_ne_zero.2 hk0) (Nat.div_mul_le_self _ _)
    obtain ⟨σ₁, hσ₁, hch₁⟩ := conj_to_std hp2 h₁ c₁ A₁ hc hcd hπ hπn
    obtain ⟨σ₂, hσ₂, hch₂⟩ := conj_to_std hp2 h₂ c₂ A₂ hc hcd hπ hπn
    refine ⟨σ₂⁻¹ * σ₁, ?_, ?_⟩
    · rw [mem_alternatingGroup, map_mul, map_inv, hσ₁, hσ₂, inv_one, mul_one]
    · ext y
      rw [mem_map_conj_iff, hch₁, hch₂]
      have key : σ₁ * ((σ₂⁻¹ * σ₁)⁻¹ * y * (σ₂⁻¹ * σ₁)) * σ₁⁻¹ = σ₂ * y * σ₂⁻¹ := by group
      rw [key]

end Core3

section Core4

variable {α : Type} [Fintype α] [DecidableEq α]

theorem core_order {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {y : Perm α}
    (hy : y ∈ alternatingGroup α) (hyp : y ^ p = 1) :
    ∃ E : Subgroup (Perm α), E ≤ alternatingGroup α ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ (Fintype.card α / p) ∧ y ∈ E := by
  have hyt := Equiv.Perm.cycleType_of_pow_prime_eq_one hyp
  have hsum := Equiv.Perm.sum_cycleType y
  have hsupp : y.support.card ≤ Fintype.card α := Finset.card_le_univ _
  set m := Multiset.card y.cycleType with hm
  have hmp : m * p ≤ Fintype.card α := by
    rw [hyt, Multiset.sum_replicate, smul_eq_mul] at hsum
    omega
  have hmk : m ≤ Fintype.card α / p := (Nat.le_div_iff_mul_le hp.out.pos).2 hmp
  by_cases hk0 : Fintype.card α / p = 0
  · have hm0 : m = 0 := by omega
    have hy1 : y = 1 := by
      rw [← Equiv.Perm.cycleType_eq_zero, hyt, hm0]
      rfl
    refine ⟨⊥, bot_le, isElemAbelian_bot, by rw [Subgroup.card_bot, hk0, pow_zero], ?_⟩
    rw [hy1]
    exact Subgroup.one_mem _
  · obtain ⟨c, π, hc, hcd, hπ, hπn⟩ :=
      std_family hp2 (Nat.one_le_iff_ne_zero.2 hk0) (Nat.div_mul_le_self _ _)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (show m ≤ (Finset.univ : Finset (Fin (Fintype.card α / p))).card by simpa using hmk)
    obtain ⟨z, hzE, hzt⟩ := standard_product_cycleType hc hcd s
    have hconj : IsConj z y := isConj_iff_cycleType_eq.2 (by rw [hzt, hs, hyt])
    obtain ⟨g, hg⟩ := isConj_iff.1 hconj
    obtain ⟨h1, h2, h3⟩ := standard_props hp2 hc hcd
    have hmapπ : (Subgroup.closure (Set.range c)).map (MulAut.conj π).toMonoidHom =
        Subgroup.closure (Set.range c) :=
      map_conj_closure_eq (Set.range c) π (by rintro _ ⟨i, rfl⟩; exact hπn i)
    obtain ⟨σ, hσsign, hσy⟩ : ∃ σ : Perm α, sign σ = 1 ∧
        σ⁻¹ * y * σ ∈ Subgroup.closure (Set.range c) := by
      by_cases hg1 : sign g = 1
      · refine ⟨g, hg1, ?_⟩
        rw [← hg]
        have : g⁻¹ * (g * z * g⁻¹) * g = z := by group
        rw [this]
        exact hzE
      · refine ⟨g * π, ?_, ?_⟩
        · rw [map_mul]
          have hg' : sign g = -1 := by
            rcases Int.units_eq_one_or (sign g) with h | h
            · exact absurd h hg1
            · exact h
          rw [hg', hπ]
          rfl
        · rw [← hg]
          have : (g * π)⁻¹ * (g * z * g⁻¹) * (g * π) = π⁻¹ * z * π := by group
          rw [this]
          exact conj_symm_mem hmapπ hzE
    refine ⟨(Subgroup.closure (Set.range c)).map (MulAut.conj σ).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx
      have hwA : sign w = 1 := (mem_alternatingGroup).1 (h3 hw)
      rw [mem_alternatingGroup]
      show sign (σ * w * σ⁻¹) = 1
      rw [map_mul, map_mul, map_inv, hwA, hσsign]
      simp
    · exact isElemAbelian_map (MulAut.conj σ).toMonoidHom (fun x x' hxx' => (MulAut.conj σ).injective hxx') h2
    · rw [Subgroup.card_map_of_injective (fun x x' hxx' => (MulAut.conj σ).injective hxx')]
      exact h1.trans (by rfl)
    · rw [mem_map_conj_iff]
      exact hσy

end Core4

section Transport2

theorem isElemAbelian_subgroupOf {X : Type} [Group X] {p : ℕ} {K E : Subgroup X}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.subgroupOf K) := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    apply Subtype.ext
    have ha' : (a : X) ∈ E := Subgroup.mem_subgroupOf.1 ha
    have hb' : (b : X) ∈ E := Subgroup.mem_subgroupOf.1 hb
    have hc := congrArg Subtype.val (hE.1.is_comm.comm ⟨(a : X), ha'⟩ ⟨(b : X), hb'⟩)
    exact hc
  · rintro ⟨a, ha⟩ hx
    apply Subtype.ext
    exact hE.2 _ (Subgroup.mem_subgroupOf.1 hx)

theorem isElemAbelian_of_map_injective {G H : Type} [Group G] [Group H] {p : ℕ} {F : Subgroup G}
    {f : G →* H} (hf : Function.Injective f) (h : IsElemAbelian p (F.map f)) :
    IsElemAbelian p F := by
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    apply hf
    have := congrArg Subtype.val (h.1.is_comm.comm ⟨f a, Subgroup.mem_map_of_mem f ha⟩
      ⟨f b, Subgroup.mem_map_of_mem f hb⟩)
    simpa [map_mul] using this
  · rintro x hx
    apply hf
    rw [map_pow, map_one]
    exact h.2 _ (Subgroup.mem_map_of_mem f hx)

@[expose] noncomputable def toPerm {X : Type} [Group X] {n : ℕ} (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin n)) : K →* Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom

theorem toPerm_injective {X : Type} [Group X] {n : ℕ} (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin n)) : Function.Injective (toPerm K e) :=
  fun x y h => e.injective (Subtype.ext h)

theorem toPerm_mem {X : Type} [Group X] {n : ℕ} (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin n)) (y : K) :
    toPerm K e y ∈ alternatingGroup (Fin n) :=
  (e y).2

theorem toPerm_apply {X : Type} [Group X] {n : ℕ} (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin n)) (y : K) :
    toPerm K e y = ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) := rfl

theorem map_comap_toPerm {X : Type} [Group X] {n : ℕ} (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin n)) {E₀ : Subgroup (Perm (Fin n))}
    (hA : E₀ ≤ alternatingGroup (Fin n)) :
    (E₀.comap (toPerm K e)).map (toPerm K e) = E₀ := by
  rw [Subgroup.map_comap_eq]
  refine inf_eq_right.2 ?_
  intro x hx
  refine ⟨e.symm ⟨x, hA hx⟩, ?_⟩
  simp [toPerm_apply]

theorem card_map_subtype_eq {X : Type} [Group X] {K : Subgroup X} {F : Subgroup K} :
    Nat.card (F.map K.subtype) = Nat.card F :=
  Subgroup.card_map_of_injective Subtype.val_injective

end Transport2


section KFinal

theorem map_conj_comm {G H : Type} [Group G] [Group H] (f : G →* H) (g : G) (F : Subgroup G) :
    (F.map (MulAut.conj g).toMonoidHom).map f = (F.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun x => by simp [MulAut.conj_apply, map_mul, map_inv]

theorem transport_card_le {X : Type} [Group X] {n p : ℕ} [Fact p.Prime] (K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin n)) {E : Subgroup X} (hEK : E ≤ K) (hE : IsElemAbelian p E) :
    IsElemAbelian p ((E.subgroupOf K).map (toPerm K e)) ∧
      Nat.card ((E.subgroupOf K).map (toPerm K e)) = Nat.card E := by
  refine ⟨isElemAbelian_map _ (toPerm_injective K e) (isElemAbelian_subgroupOf hE), ?_⟩
  rw [Subgroup.card_map_of_injective (toPerm_injective K e)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv

end KFinal


end AltInputs

namespace Lemma118R

theorem Input10_6AltRank_holds : Lemma118R.Input10_6AltRank := by
  intro n p X _ _ K hn hp hp2 hK
  obtain ⟨e⟩ := hK
  haveI := Fact.mk hp
  refine ⟨?_, ?_⟩
  · intro E hEK hE
    have hT := AltInputs.transport_card_le K e hEK hE
    have hc := AltInputs.card_le_pow_div hT.1
    rw [hT.2, Fintype.card_fin] at hc
    exact hc
  · obtain ⟨E₀, hA, hE₀, hc₀⟩ := AltInputs.core_exists (α := Fin n) hp2
    have h1 : Nat.card ((E₀.comap (AltInputs.toPerm K e)).map (AltInputs.toPerm K e)) =
        Nat.card (E₀.comap (AltInputs.toPerm K e)) :=
      Subgroup.card_map_of_injective (AltInputs.toPerm_injective K e)
    rw [AltInputs.map_comap_toPerm K e hA] at h1
    refine ⟨(E₀.comap (AltInputs.toPerm K e)).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · apply AltInputs.isElemAbelian_map K.subtype Subtype.val_injective
      apply AltInputs.isElemAbelian_of_map_injective (AltInputs.toPerm_injective K e)
      rw [AltInputs.map_comap_toPerm K e hA]
      exact hE₀
    · rw [AltInputs.card_map_subtype_eq, ← h1, hc₀, Fintype.card_fin]

theorem Input10_5AltMax_holds : Lemma118R.Input10_5AltMax := by
  intro n p X _ _ K hn hp hp2 hK
  obtain ⟨e⟩ := hK
  haveI := Fact.mk hp
  constructor
  · intro E₁ E₂ hE₁K hE₂K hE₁ hE₂ hc₁ hc₂
    have T₁ := AltInputs.transport_card_le K e hE₁K hE₁
    have T₂ := AltInputs.transport_card_le K e hE₂K hE₂
    have hA₁ : (E₁.subgroupOf K).map (AltInputs.toPerm K e) ≤ alternatingGroup (Fin n) := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
      exact AltInputs.toPerm_mem K e y
    have hA₂ : (E₂.subgroupOf K).map (AltInputs.toPerm K e) ≤ alternatingGroup (Fin n) := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
      exact AltInputs.toPerm_mem K e y
    have c₁ : Nat.card ((E₁.subgroupOf K).map (AltInputs.toPerm K e)) =
        p ^ (Fintype.card (Fin n) / p) := by
      rw [T₁.2, hc₁, Fintype.card_fin]
    have c₂ : Nat.card ((E₂.subgroupOf K).map (AltInputs.toPerm K e)) =
        p ^ (Fintype.card (Fin n) / p) := by
      rw [T₂.2, hc₂, Fintype.card_fin]
    obtain ⟨g₀, hg₀, hEq⟩ := AltInputs.core_conj hp2 T₁.1 T₂.1 c₁ c₂ hA₁ hA₂
    obtain ⟨g', hg'⟩ : ∃ g' : K, g' = e.symm ⟨g₀, hg₀⟩ := ⟨_, rfl⟩
    have hφg' : AltInputs.toPerm K e g' = g₀ := by
      rw [AltInputs.toPerm_apply, hg', MulEquiv.apply_symm_apply]
    have hconj : E₂.subgroupOf K = (E₁.subgroupOf K).map (MulAut.conj g').toMonoidHom := by
      apply Subgroup.map_injective (AltInputs.toPerm_injective K e)
      rw [AltInputs.map_conj_comm, hφg']
      exact hEq
    refine ⟨(g' : X), g'.2, ?_⟩
    have hE₂eq : (E₂.subgroupOf K).map K.subtype = E₂ := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hE₂K]
    have hE₁eq : (E₁.subgroupOf K).map K.subtype = E₁ := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hE₁K]
    rw [← hE₂eq, hconj, AltInputs.map_conj_comm, hE₁eq]
    rfl
  · intro y hy hyp
    have hyK : (⟨y, hy⟩ : K) ^ p = 1 := Subtype.ext (by simpa using hyp)
    have hpe : (AltInputs.toPerm K e ⟨y, hy⟩) ^ p = 1 := by
      rw [← map_pow, hyK, map_one]
    obtain ⟨E₀, hA, hE₀, hc₀, hyE₀⟩ := AltInputs.core_order hp2
      (AltInputs.toPerm_mem K e ⟨y, hy⟩) hpe
    have h1 : Nat.card ((E₀.comap (AltInputs.toPerm K e)).map (AltInputs.toPerm K e)) =
        Nat.card (E₀.comap (AltInputs.toPerm K e)) :=
      Subgroup.card_map_of_injective (AltInputs.toPerm_injective K e)
    rw [AltInputs.map_comap_toPerm K e hA] at h1
    refine ⟨(E₀.comap (AltInputs.toPerm K e)).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
    · apply AltInputs.isElemAbelian_map K.subtype Subtype.val_injective
      apply AltInputs.isElemAbelian_of_map_injective (AltInputs.toPerm_injective K e)
      rw [AltInputs.map_comap_toPerm K e hA]
      exact hE₀
    · rw [AltInputs.card_map_subtype_eq, ← h1, hc₀, Fintype.card_fin]
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 hyE₀)

end Lemma118R

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
