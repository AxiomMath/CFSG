module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open MulAction Subgroup Equiv
open scoped Pointwise
open AltInputs

namespace AltInputs2

section PCycles

variable {α : Type} [Fintype α] [DecidableEq α]

@[expose] def PCyc (p : ℕ) (g : Equiv.Perm α) : Prop := g.IsCycle ∧ g.support.card = p

section Orbits

variable (E : Subgroup (Equiv.Perm α))

noncomputable def oRep (ω : MulAction.orbitRel.Quotient E α) : α := Quotient.out ω

noncomputable def oStab (ω : MulAction.orbitRel.Quotient E α) : Subgroup E :=
  MulAction.stabilizer E (oRep E ω)

noncomputable def oSet (ω : MulAction.orbitRel.Quotient E α) : Set α :=
  MulAction.orbit E (oRep E ω)

variable {E}

theorem oStab_index (ω : MulAction.orbitRel.Quotient E α) :
    (oStab E ω).index = Nat.card (oSet E ω) := by
  rw [Nat.card_coe_set_eq]
  exact MulAction.index_stabilizer E (oRep E ω)

theorem sum_card_oSet :
    ∑ ω : MulAction.orbitRel.Quotient E α, Nat.card (oSet E ω) = Fintype.card α := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (MulAction.selfEquivSigmaOrbits E α),
    Nat.card_sigma]
  rfl

theorem index_inf_oStab_le (s : Finset (MulAction.orbitRel.Quotient E α)) :
    (s.inf (oStab E)).index ≤ ∏ ω ∈ s, (oStab E ω).index := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.prod_insert ha]
    exact (Subgroup.index_inf_le).trans (Nat.mul_le_mul_left _ ih)

theorem inf_oStab_eq_bot (hc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) :
    (Finset.univ : Finset (MulAction.orbitRel.Quotient E α)).inf (oStab E) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have hfix : ∀ y : α, (g : Equiv.Perm α) y = y := by
    intro y
    have hy : y ∈ oSet E (Quotient.mk (MulAction.orbitRel E α) y) :=
      MulAction.mem_orbit_symm.1
        (MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel E α) y))
    refine (fixes_iff_of_mem_orbit hc g.2 hy).2 ?_
    have := (Finset.inf_le (Finset.mem_univ (Quotient.mk (MulAction.orbitRel E α) y)) :
      _ ≤ oStab E (Quotient.mk (MulAction.orbitRel E α) y)) hg
    exact (MulAction.mem_stabilizer_iff).1 this
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Equiv.ext hfix)

theorem mem_oSet_mk {E : Subgroup (Equiv.Perm α)} (y : α) :
    y ∈ oSet E (Quotient.mk (MulAction.orbitRel E α) y) := by
  exact MulAction.mem_orbit_symm.1
    (MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel E α) y))

end Orbits

theorem exists_exponents_o {p : ℕ} [hp : Fact p.Prime] (E : Subgroup (Equiv.Perm α))
    (hc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) {m : ℕ}
    (hm : Nat.card E = p ^ m) :
    ∃ J : MulAction.orbitRel.Quotient E α → ℕ, (∀ ω, (oStab E ω).index = p ^ J ω) ∧
      Nat.card E ≤ p ^ (∑ ω, J ω) ∧ (∑ ω, J ω) * p ≤ Fintype.card α := by
  have hdvd : ∀ ω, (oStab E ω).index ∣ p ^ m := fun ω => by
    rw [← hm]
    exact Subgroup.index_dvd_card _
  choose J _ hJ using fun ω => (Nat.dvd_prime_pow hp.out).1 (hdvd ω)
  refine ⟨J, hJ, ?_, ?_⟩
  · have hle : Nat.card E ≤ ∏ ω, (oStab E ω).index := by
      have := index_inf_oStab_le (E := E) Finset.univ
      rw [inf_oStab_eq_bot hc, Subgroup.index_bot] at this
      exact this
    calc Nat.card E ≤ ∏ ω, (oStab E ω).index := hle
      _ = p ^ (∑ ω, J ω) := by
        simp_rw [hJ]
        rw [Finset.prod_pow_eq_pow_sum]
  · rw [← sum_card_oSet, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ω _
    rw [← oStab_index, hJ ω, mul_comm]
    exact mul_le_pow_of_two_le hp.out.two_le (J ω)

theorem exists_pcyc {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) {E : Subgroup (Perm α)}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ (Fintype.card α / p)) :
    ∃ (k : ℕ) (x : Fin k → Perm α), k = Fintype.card α / p ∧ (∀ i, x i ∈ E) ∧
      (∀ i, PCyc p (x i)) ∧ ∀ i j, i ≠ j → Equiv.Perm.Disjoint (x i) (x j) := by
  classical
  have hc := comm_of_isElemAbelian hE
  obtain ⟨m, hm⟩ := Lemma118R.card_eq_pow_of_elemAb hE
  obtain ⟨J, hJ, hle, hsum⟩ := exists_exponents_o (p := p) (E := E) hc hm
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
      rw [← sum_card_oSet]
      apply Finset.sum_congr rfl
      intro ω _
      rw [← oStab_index, hJ ω]
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
  have hex : ∀ ω, J ω = 1 → ∃ x : Perm α, x ∈ E ∧ PCyc p x ∧
      (∀ ω', ω' ≠ ω → ∀ y ∈ oSet E ω', x y = y) ∧ (∀ y, y ∉ oSet E ω → x y = y) := by
    intro ω hω
    have hωle : 1 ≤ k := by
      have : J ω ≤ ∑ ω', J ω' := Finset.single_le_sum (fun ω' _ => Nat.zero_le _) (Finset.mem_univ ω)
      omega
    set M : Subgroup E := (Finset.univ.erase ω).inf (oStab E) with hM
    have hindexM : M.index ≤ p ^ (k - 1) := by
      have h1 := index_inf_oStab_le (E := E) (Finset.univ.erase ω)
      have h2 : ∏ ω' ∈ Finset.univ.erase ω, (oStab E ω').index = p ^ (k - 1) := by
        simp_rw [hJ]
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        have := Finset.add_sum_erase Finset.univ J (Finset.mem_univ ω)
        omega
      exact h1.trans h2.le
    have hsplit : (Finset.univ : Finset (MulAction.orbitRel.Quotient E α)).inf (oStab E) =
        oStab E ω ⊓ M := by
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
    have hxM : ∀ ω', ω' ≠ ω → g0 ∈ oStab E ω' := fun ω' hne =>
      (Finset.inf_le (Finset.mem_erase.2 ⟨hne, Finset.mem_univ ω'⟩) :
        (Finset.univ.erase ω).inf (oStab E) ≤ oStab E ω') hg0M
    have hxnot : g0 ∉ oStab E ω := by
      intro hmem
      have h5 : g0 ∈ (Finset.univ : Finset (MulAction.orbitRel.Quotient E α)).inf (oStab E) := by
        rw [hsplit]
        exact ⟨hmem, hg0M⟩
      rw [inf_oStab_eq_bot (E := E) hc, Subgroup.mem_bot] at h5
      exact hg0ne h5
    have hfixit : ∀ ω', ω' ≠ ω → ∀ y ∈ oSet E ω', (g0 : Perm α) y = y := by
      intro ω' hne y hy
      have hstab := (MulAction.mem_stabilizer_iff).1 (hxM ω' hne)
      exact (fixes_iff_of_mem_orbit hc g0.2 hy).2 hstab
    have hmoves : ∀ y ∈ oSet E ω, (g0 : Perm α) y ≠ y := by
      intro y hy hfix
      apply hxnot
      exact MulAction.mem_stabilizer_iff.2 ((fixes_iff_of_mem_orbit hc g0.2 hy).1 hfix)
    have hout : ∀ y, y ∉ oSet E ω → (g0 : Perm α) y = y := by
      intro y hy
      have hne : Quotient.mk (MulAction.orbitRel E α) y ≠ ω := by
        intro h
        rw [← h] at hy
        exact hy (mem_oSet_mk y)
      exact hfixit _ hne y (mem_oSet_mk y)
    have hsupp : ((g0 : Perm α).support : Set α) = oSet E ω := by
      ext y
      rw [Finset.mem_coe, Equiv.Perm.mem_support]
      constructor
      · intro hy
        by_contra hny
        exact hy (hout y hny)
      · intro hy
        exact hmoves y hy
    have hcardsupp : (g0 : Perm α).support.card = p := by
      rw [← Set.ncard_coe_finset, hsupp, ← Nat.card_coe_set_eq, ← oStab_index, hJ ω, hω, pow_one]
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
  by_cases hy : y ∈ oSet E (e.symm i).1
  · exact Or.inr ((hxw _ (hJω j)).2.2.1 (e.symm i).1 hne y hy)
  · exact Or.inl ((hxw _ (hJω i)).2.2.2 y hy)

theorem closure_pcyc {p : ℕ} [hp : Fact p.Prime] {k : ℕ} {x : Fin k → Perm α}
    (hx : ∀ i, PCyc p (x i)) (hdisj : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (x i) (x j)) :
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


theorem fixOut_closure {U : Finset α} {S : Set (Equiv.Perm α)}
    (hS : ∀ g ∈ S, ∀ x, x ∉ U → g x = x) :
    ∀ g ∈ Subgroup.closure S, ∀ x, x ∉ U → g x = x := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => intro x _; rfl
  | mul x y _ _ hx hy =>
    intro z hz
    rw [Equiv.Perm.mul_apply, hy z hz, hx z hz]
  | inv x _ hx =>
    intro z hz
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hx z hz).symm

theorem mapsTo_of_fixOut {U : Finset α} {g : Equiv.Perm α} (hg : ∀ x, x ∉ U → g x = x) {x : α}
    (hx : x ∈ U) : g x ∈ U := by
  by_contra h
  have h1 : g (g x) = g x := hg (g x) h
  have h2 : g x = x := g.injective h1
  exact h (by rw [h2]; exact hx)

theorem pow_dvd_factorial_le_one {p m : ℕ} (hp : p.Prime) (h : p ^ m ∣ p.factorial) : m ≤ 1 := by
  by_contra hm
  push_neg at hm
  have h2 : p ^ 2 ∣ p.factorial := (Nat.pow_dvd_pow p (by omega : 2 ≤ m)).trans h
  have hpf : p.factorial = p * (p - 1).factorial := (Nat.mul_factorial_pred hp.ne_zero).symm
  rw [hpf, pow_two] at h2
  have h3 : p ∣ (p - 1).factorial := Nat.dvd_of_mul_dvd_mul_left hp.pos h2
  have h4 := (Nat.Prime.dvd_factorial hp).1 h3
  have h5 := hp.two_le
  omega

theorem pcycle_mem_zpowers {p : ℕ} [hp : Fact p.Prime] {P : Subgroup (Equiv.Perm α)}
    (hP : ∀ g ∈ P, ∃ k : ℕ, g ^ p ^ k = 1)
    {c d : Equiv.Perm α} (hc : PCyc p c) (hd : PCyc p d)
    (hcP : c ∈ P) (hdP : d ∈ P) {x0 : α} (hxc : x0 ∈ c.support) (hxd : x0 ∈ d.support) :
    d ∈ Subgroup.zpowers c := by
  classical
  replace hc : c.IsCycle ∧ c.support.card = p := hc
  replace hd : d.IsCycle ∧ d.support.card = p := hd
  set H : Subgroup (Equiv.Perm α) := Subgroup.closure {c, d} with hHdef
  have hcH : c ∈ H := Subgroup.subset_closure (by simp)
  have hdH : d ∈ H := Subgroup.subset_closure (by simp)
  have hHP : H ≤ P :=
    (Subgroup.closure_le P).2 (Set.insert_subset_iff.2 ⟨hcP, Set.singleton_subset_iff.2 hdP⟩)
  have hHgp : IsPGroup p H := by
    intro g
    obtain ⟨k, hk⟩ := hP (g : Equiv.Perm α) (hHP g.2)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hHgp
  have hcyc : Nat.card (Subgroup.zpowers c) = p := by
    rw [Nat.card_zpowers, hc.1.orderOf, hc.2]
  have hle : Subgroup.zpowers c ≤ H := Subgroup.zpowers_le.2 hcH
  by_cases hST : c.support = d.support
  ·
    have hfix : ∀ g ∈ H, ∀ x, x ∉ c.support → g x = x := by
      apply fixOut_closure
      intro g hg x hx
      rcases Set.mem_insert_iff.1 hg with rfl | hg'
      · exact Equiv.Perm.notMem_support.1 hx
      · obtain rfl := Set.mem_singleton_iff.1 hg'
        exact Equiv.Perm.notMem_support.1 (hST ▸ hx)
    have hrange : H ≤ (Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support)).range := by
      intro g hg
      have h1 : ∀ x, g x ∈ c.support ↔ x ∈ c.support := by
        intro x
        constructor
        · intro hgx
          by_contra hx
          have := hfix g hg x hx
          rw [this] at hgx
          exact hx hgx
        · intro hx
          exact mapsTo_of_fixOut (U := c.support) (fun y hy => hfix g hg y hy) hx
      have h2 : ∀ x, g x ≠ x → x ∈ c.support := by
        intro x hx
        by_contra hx'
        exact hx (hfix g hg x hx')
      exact MonoidHom.mem_range.2 ⟨Equiv.Perm.subtypePerm g h1, Equiv.Perm.ofSubtype_subtypePerm h1 h2⟩
    have hmap : (H.comap (Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support))).map
        (Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support)) = H := by
      rw [Subgroup.map_comap_eq, inf_eq_right.2 hrange]
    have hcardH : Nat.card H =
        Nat.card (H.comap (Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support))) := by
      have := Subgroup.card_map_of_injective
        (f := Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support))
        (K := H.comap (Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support)))
        Equiv.Perm.ofSubtype_injective
      rw [hmap] at this
      exact this
    have hSc : Nat.card {x // x ∈ c.support} = p := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hc.2]
    have hdvd : Nat.card H ∣ p.factorial := by
      have h1 := Subgroup.card_subgroup_dvd_card
        (H.comap (Equiv.Perm.ofSubtype (p := fun x => x ∈ c.support)))
      rw [← hcardH, Nat.card_perm, hSc] at h1
      exact h1
    rw [hm] at hdvd
    have hm1 : m ≤ 1 := pow_dvd_factorial_le_one hp.out hdvd
    have hHle : Nat.card H ≤ p := by
      rw [hm]
      calc p ^ m ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hm1
        _ = p := pow_one p
    have hEq : Subgroup.zpowers c = H :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcyc]; exact hHle)
    rw [← hEq] at hdH
    exact hdH
  ·
    exfalso
    set U : Finset α := c.support ∪ d.support with hU
    have hfixU : ∀ g ∈ H, ∀ x, x ∉ U → g x = x := by
      apply fixOut_closure
      intro g hg x hx
      have hxc' : x ∉ c.support := fun h => hx (Finset.mem_union_left _ h)
      have hxd' : x ∉ d.support := fun h => hx (Finset.mem_union_right _ h)
      rcases Set.mem_insert_iff.1 hg with rfl | hg'
      · exact Equiv.Perm.notMem_support.1 hxc'
      · obtain rfl := Set.mem_singleton_iff.1 hg'
        exact Equiv.Perm.notMem_support.1 hxd'
    have hx0U : x0 ∈ U := Finset.mem_union_left _ hxc
    have hOU : MulAction.orbit (↥H) x0 = (U : Set α) := by
      ext y
      constructor
      · intro hy
        obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
        rw [Finset.mem_coe]
        exact mapsTo_of_fixOut (hfixU (g : Equiv.Perm α) g.2) hx0U
      · intro hy
        rw [Finset.mem_coe] at hy
        rcases Finset.mem_union.1 hy with hyc | hyd
        · have hcx0 : c x0 ≠ x0 := Equiv.Perm.mem_support.1 hxc
          have hcy : c y ≠ y := Equiv.Perm.mem_support.1 hyc
          obtain ⟨i, hi⟩ := hc.1.exists_pow_eq hcx0 hcy
          refine MulAction.mem_orbit_iff.2 ⟨⟨c ^ i, Subgroup.pow_mem H hcH i⟩, ?_⟩
          exact hi
        · have hdx0 : d x0 ≠ x0 := Equiv.Perm.mem_support.1 hxd
          have hdy : d y ≠ y := Equiv.Perm.mem_support.1 hyd
          obtain ⟨i, hi⟩ := hd.1.exists_pow_eq hdx0 hdy
          refine MulAction.mem_orbit_iff.2 ⟨⟨d ^ i, Subgroup.pow_mem H hdH i⟩, ?_⟩
          exact hi
    have hidx := MulAction.index_stabilizer (↥H) x0
    have hmul := Subgroup.card_mul_index (MulAction.stabilizer (↥H) x0)
    have hdvd : (MulAction.stabilizer (↥H) x0).index ∣ p ^ m := by
      rw [← hm]
      exact Dvd.intro_left _ hmul
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    have hUi : U.card = p ^ i := by
      rw [← Set.ncard_coe_finset, ← hOU, ← hidx, hi]
    have hUc := Finset.card_union_add_card_inter c.support d.support
    rw [← hU, hc.2, hd.2] at hUc
    have hinter : 0 < (c.support ∩ d.support).card :=
      Finset.card_pos.2 ⟨x0, Finset.mem_inter.2 ⟨hxc, hxd⟩⟩
    have hUlt : U.card < 2 * p := by omega
    have hUgt : p < U.card := by
      by_contra hcon
      push_neg at hcon
      have hSU : c.support ⊆ U := Finset.subset_union_left
      have hTU : d.support ⊆ U := Finset.subset_union_right
      have hUS : c.support = U := Finset.eq_of_subset_of_card_le hSU (by rw [hc.2]; exact hcon)
      have hTS : d.support ⊆ c.support := by rw [hUS]; exact hTU
      exact hST (Finset.eq_of_subset_of_card_le hTS (le_of_eq (by rw [hc.2, hd.2]))).symm
    have hp2 := hp.out.two_le
    have hpow : ∀ j, U.card = p ^ j → False := by
      intro j hj
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · interval_cases j
        · simp at hj; omega
        · simp at hj; omega
      · have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.out.pos hj2
        nlinarith
    exact hpow i hUi

theorem exists_meet {p k : ℕ} (hp : 2 ≤ p) {x : Fin k → Equiv.Perm α} {y : Equiv.Perm α}
    (hy : y.support.card = p) (hx : ∀ i, (x i).support.card = p)
    (hxd : ∀ i j, i ≠ j → Equiv.Perm.Disjoint (x i) (x j))
    (hk : Fintype.card α < (k + 1) * p) : ∃ i, ∃ z, z ∈ y.support ∧ z ∈ (x i).support := by
  by_contra hcon
  push_neg at hcon
  have hdisjS : ∀ i ∈ (Finset.univ : Finset (Fin k)), ∀ j ∈ (Finset.univ : Finset (Fin k)),
      i ≠ j → Disjoint (x i).support (x j).support := fun i _ j _ hij =>
    Equiv.Perm.disjoint_iff_disjoint_support.1 (hxd i j hij)
  have hA : (Finset.univ.biUnion fun i => (x i).support).card = k * p := by
    rw [Finset.card_biUnion hdisjS]
    simp [hx]
  have hsub : y.support ⊆ (Finset.univ.biUnion fun i => (x i).support)ᶜ := by
    intro z hz
    simp only [Finset.mem_compl, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
    intro i hi
    exact hcon i z hz hi
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_compl, hA, hy] at h1
  have h2 : (k + 1) * p = k * p + p := by ring
  rw [h2] at hk
  generalize k * p = t at h1 hk
  omega

theorem elemAb_eq_of_pgroup {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    {P : Subgroup (Equiv.Perm α)} (hP : ∀ g ∈ P, ∃ k : ℕ, g ^ p ^ k = 1)
    {E F : Subgroup (Equiv.Perm α)} (hEP : E ≤ P) (hFP : F ≤ P)
    (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hEc : Nat.card E = p ^ (Fintype.card α / p)) (hFc : Nat.card F = p ^ (Fintype.card α / p)) :
    E = F := by
  obtain ⟨k, x, hk, hxE, hxc, hxd⟩ := exists_pcyc hp3 hE hEc
  obtain ⟨k', y, hk', hyF, hyc, hyd⟩ := exists_pcyc hp3 hF hFc
  have hlt : Fintype.card α < (k + 1) * p := by
    rw [hk, mul_comm]
    exact Nat.lt_mul_div_succ _ hp.out.pos
  have hyE : ∀ j, y j ∈ E := by
    intro j
    obtain ⟨i, z, hz1, hz2⟩ :=
      exists_meet hp.out.two_le (hyc j).2 (fun i => (hxc i).2) hxd hlt
    have hzp : y j ∈ Subgroup.zpowers (x i) :=
      pcycle_mem_zpowers hP (hxc i) (hyc j) (hEP (hxE i)) (hFP (hyF j)) hz2 hz1
    exact (Subgroup.zpowers_le.2 (hxE i)) hzp
  have hcl_le : Subgroup.closure (Set.range y) ≤ E :=
    (Subgroup.closure_le E).2 (by rintro _ ⟨j, rfl⟩; exact hyE j)
  have hcl_F : Subgroup.closure (Set.range y) = F := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.closure_le F).2 (by rintro _ ⟨j, rfl⟩; exact hyF j)
    · rw [(closure_pcyc hyc hyd).1, hFc, hk']
  have hFE : F ≤ E := by
    rw [← hcl_F]
    exact hcl_le
  exact (Subgroup.eq_of_le_of_card_ge hFE (le_of_eq (by rw [hEc, hFc]))).symm

end PCycles

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem isPGroup_of_pow_forall {G : Type} [Group G] {p : ℕ} (H : Subgroup G)
    (h : ∀ g ∈ H, ∃ k : ℕ, g ^ p ^ k = 1) : IsPGroup p H := by
  intro g
  obtain ⟨k, hk⟩ := h g.1 g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem card_map_of_injOn (f : X →* Y) (K : Subgroup X) (hK : ∀ x ∈ K, f x = 1 → x = 1) :
    Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective
      (fun x : K => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : K.map f)) := by
    intro x y hxy
    have h1 : f x = f y := congrArg Subtype.val hxy
    have h2 : f ((x : X)⁻¹ * y) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : (x : X)⁻¹ * y = 1 := hK _ (K.mul_mem (K.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  have hsurj : Function.Surjective
      (fun x : K => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : K.map f)) := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.1 hz
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

theorem isElemAbelian_map_hom {p : ℕ} (f : X →* Y) {E : Subgroup X} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    have hxz : x * z = z * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hzb, ← map_mul, ← map_mul, hxz]
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

theorem isElemAbelian_of_map_injOn {p : ℕ} (f : X →* Y) {E : Subgroup X}
    (hinj : ∀ x ∈ E, f x = 1 → x = 1) (hE : IsElemAbelian p (E.map f)) :
    IsElemAbelian p E := by
  have hcomm : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := by
    intro x hx z hz
    have h1 : f x * f z = f z * f x :=
      congrArg Subtype.val
        (hE.1.is_comm.comm ⟨f x, Subgroup.mem_map_of_mem f hx⟩ ⟨f z, Subgroup.mem_map_of_mem f hz⟩)
    have h2 : f (x * z) = f (z * x) := by rw [map_mul, map_mul]; exact h1
    have h3 : (z * x)⁻¹ * (x * z) = 1 :=
      hinj _ (E.mul_mem (E.inv_mem (E.mul_mem hz hx)) (E.mul_mem hx hz))
        (by rw [map_mul, map_inv, h2, inv_mul_cancel])
    exact (inv_mul_eq_one.1 h3).symm
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2), fun x hx => ?_⟩
  have hfp : f (x ^ p) = 1 := by
    rw [map_pow]
    exact hE.2 _ (Subgroup.mem_map_of_mem f hx)
  exact hinj _ (E.pow_mem hx p) hfp

end Transport

section Core

theorem core_of_hom {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    (Φ : X →* Equiv.Perm (Fin n)) (hrange : Φ.range = alternatingGroup (Fin n))
    (hker : Nat.Coprime p (Nat.card Φ.ker))
    {Q : Subgroup X} (hQ : IsPGroup p Q) (hmax : ∀ R : Subgroup X, IsPGroup p R → Q ≤ R → R = Q) :
    ∃! E : Subgroup X, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ (n / p) := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ x : X, Φ x = σ := by
    intro σ hσ
    rw [← hrange] at hσ
    exact MonoidHom.mem_range.1 hσ
  have hnd : ¬ p ∣ Nat.card Φ.ker := fun hd => hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hker hd)
  have hkerne : Nat.card Φ.ker ≠ 0 := Nat.card_pos.ne'
  have hpowne : p ^ (n / p) ≠ 0 := (pow_pos hp.out.pos _).ne'
  have hinjP : ∀ H : Subgroup X, IsPGroup p H → ∀ x ∈ H, Φ x = 1 → x = 1 := by
    intro H hH x hxH hx1
    obtain ⟨k, hk⟩ := hH ⟨x, hxH⟩
    have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one hk')
    have hxker : x ∈ Φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hx1
    have hdvd : orderOf (⟨x, hxker⟩ : Φ.ker) ∣ Nat.card Φ.ker := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hj] at hdvd
    have h1 : p ^ j = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left j hker) hdvd
    exact orderOf_eq_one_iff.1 (by rw [hj, h1])
  have hinj : ∀ x ∈ Q, Φ x = 1 → x = 1 := hinjP Q hQ
  have hinjQ : ∀ x ∈ Q, ∀ y ∈ Q, Φ x = Φ y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ = 1 :=
      hinjP Q hQ _ (Q.mul_mem hx (Q.inv_mem hy)) (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.1 h1
  obtain ⟨S, hQS⟩ := IsPGroup.exists_le_sylow hQ
  have hSQ : S.toSubgroup = Q := hmax S.toSubgroup S.isPGroup' hQS
  obtain ⟨E₀, hE₀A, hE₀ab, hE₀card⟩ := AltInputs.core_exists (α := Fin n) hp2
  rw [Fintype.card_fin] at hE₀card
  set W : Subgroup X := E₀.comap Φ with hWdef
  have hWmem : ∀ x : X, x ∈ W ↔ Φ x ∈ E₀ := fun x => Iff.rfl
  have hkerW : Φ.ker ≤ W := fun x hx => by
    rw [hWmem, MonoidHom.mem_ker.1 hx]
    exact E₀.one_mem
  have hcardW : Nat.card W = Nat.card Φ.ker * p ^ (n / p) := by
    have hrangeΦ' : (Φ.comp W.subtype).range = E₀ := by
      ext e
      constructor
      · rintro ⟨w, rfl⟩
        exact w.2
      · intro he
        obtain ⟨x, hx⟩ := hsurj e (hE₀A he)
        exact ⟨⟨x, (hWmem x).2 (by rw [hx]; exact he)⟩, hx⟩
    have hkerΦ' : (Φ.comp W.subtype).ker = Φ.ker.subgroupOf W := by
      ext w
      exact Iff.rfl
    have hcardker : Nat.card (Φ.comp W.subtype).ker = Nat.card Φ.ker := by
      rw [hkerΦ']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerW).toEquiv
    have hdecomp := Subgroup.card_ker_mul_card_range (Φ.comp W.subtype)
    rw [hrangeΦ', hcardker, hE₀card] at hdecomp
    exact hdecomp.symm
  obtain ⟨T⟩ : Nonempty (Sylow p W) := Sylow.nonempty
  have hTcard : Nat.card T = p ^ (n / p) := by
    rw [Sylow.card_eq_multiplicity T, hcardW, Nat.factorization_mul hkerne hpowne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, Nat.factorization_pow_self hp.out, zero_add]
  set R : Subgroup X := T.toSubgroup.map W.subtype with hRdef
  have hRW : R ≤ W := Subgroup.map_subtype_le _
  have hRp : IsPGroup p R := by
    refine isPGroup_of_pow_forall R ?_
    intro g hg
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hg
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    have hk' : t ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, by rw [← map_pow, hk', map_one]⟩
  have hRcard : Nat.card R = p ^ (n / p) := by
    rw [hRdef, Subgroup.card_map_of_injective (f := W.subtype) Subtype.val_injective]
    exact hTcard
  have hinjR : ∀ x ∈ R, Φ x = 1 → x = 1 := hinjP R hRp
  have hRmapE : R.map Φ = E₀ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact (hWmem x).1 (hRW hx)
    · exact le_of_eq (by rw [card_map_of_injOn Φ R hinjR, hRcard, hE₀card])
  have hRab : IsElemAbelian p R := by
    apply isElemAbelian_of_map_injOn Φ hinjR
    rw [hRmapE]
    exact hE₀ab
  obtain ⟨S', hRS'⟩ := IsPGroup.exists_le_sylow hRp
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S' S
  have hSconj : (S.toSubgroup : Subgroup X) = MulAut.conj g • (S'.toSubgroup : Subgroup X) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hE₁Q : R.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hSQ]
    have hmem : MulAut.conj g • x ∈ MulAut.conj g • (S'.toSubgroup : Subgroup X) :=
      Subgroup.smul_mem_pointwise_smul x _ _ (hRS' hx)
    rw [← hSconj] at hmem
    exact hmem
  have hE₁ab : IsElemAbelian p (R.map (MulAut.conj g).toMonoidHom) :=
    isElemAbelian_map_hom _ hRab
  have hE₁card : Nat.card (R.map (MulAut.conj g).toMonoidHom) = p ^ (n / p) := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      hRcard]
  have hPbar : ∀ y ∈ Q.map Φ, ∃ k : ℕ, y ^ p ^ k = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, by rw [← map_pow, hk', map_one]⟩
  have hmapEq : ∀ E F : Subgroup X, E ≤ Q → F ≤ Q → E.map Φ = F.map Φ → E = F := by
    intro E F hE hF hEF
    ext x
    constructor
    · intro hx
      have hm : Φ x ∈ F.map Φ := hEF ▸ Subgroup.mem_map_of_mem Φ hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hm
      have hxy : x = y := hinjQ x (hE hx) y (hF hy) hyx.symm
      rw [hxy]
      exact hy
    · intro hx
      have hm : Φ x ∈ E.map Φ := hEF.symm ▸ Subgroup.mem_map_of_mem Φ hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hm
      have hxy : x = y := hinjQ x (hF hx) y (hE hy) hyx.symm
      rw [hxy]
      exact hy
  refine ⟨R.map (MulAut.conj g).toMonoidHom, ⟨hE₁Q, hE₁ab, hE₁card⟩, ?_⟩
  rintro F ⟨hFQ, hFab, hFcard⟩
  apply hmapEq F _ hFQ hE₁Q
  apply elemAb_eq_of_pgroup hp3 hPbar (Subgroup.map_mono hFQ) (Subgroup.map_mono hE₁Q)
    (isElemAbelian_map_hom Φ hFab) (isElemAbelian_map_hom Φ hE₁ab)
  · rw [card_map_of_injOn Φ F (fun x hx => hinj x (hFQ hx)), hFcard, Fintype.card_fin]
  · rw [card_map_of_injOn Φ _ (fun x hx => hinj x (hE₁Q hx)), hE₁card, Fintype.card_fin]

end Core

theorem exists_unique_transfer {G : Type} [Group G] [Finite G] {p m : ℕ} [hp : Fact p.Prime]
    {K P : Subgroup G} (hPK : P ≤ K)
    (h : ∃! E : Subgroup K, E ≤ P.subgroupOf K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ m) :
    ∃! E : Subgroup G, E ≤ P ∧ IsElemAbelian p E ∧ CFSG.Open.pRank p E = m := by
  obtain ⟨E₀, ⟨h1, h2, h3⟩, huniq⟩ := h
  have hE₀ : IsElemAbelian p (E₀.map K.subtype) :=
    isElemAbelian_map K.subtype Subtype.val_injective h2
  refine ⟨E₀.map K.subtype, ⟨?_, hE₀, ?_⟩, ?_⟩
  · have h4 := Subgroup.map_mono (f := K.subtype) h1
    rw [Subgroup.subgroupOf_map_subtype] at h4
    exact h4.trans inf_le_left
  · exact Lemma118T.pRank_eq_of_isElemAbelian_card hE₀ (by rw [card_map_subtype_eq, h3])
  · rintro E ⟨hEP, hE, hpr⟩
    have hEK : E ≤ K := hEP.trans hPK
    obtain ⟨j, hj⟩ := Lemma118R.card_eq_pow_of_elemAb hE
    have hjm : j = m := (Lemma118T.pRank_eq_of_isElemAbelian_card hE hj).symm.trans hpr
    have hE' : E.subgroupOf K ≤ P.subgroupOf K := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hEP hx
    have hcardE' : Nat.card (E.subgroupOf K) = p ^ m := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hj, hjm]
    have hEq : E.subgroupOf K = E₀ := huniq _ ⟨hE', isElemAbelian_subgroupOf hE K, hcardE'⟩
    have hE_eq : E = (E.subgroupOf K).map K.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEK]
    rw [hE_eq, hEq]

end AltInputs2

namespace Lemma118T

theorem Input10_5K_holds : Input10_5K := by
  intro G _ _ p n hp hp2 K hK P hP
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hK
  let Φ : K →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.GLAPPrimeCore p K)))
  have hrange : Φ.range = alternatingGroup (Fin n) := by
    ext σ
    constructor
    · rintro ⟨x, rfl⟩
      exact (e (QuotientGroup.mk x)).2
    · intro hσ
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
      refine ⟨y, ?_⟩
      show ((e (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = σ
      rw [hy, MulEquiv.apply_symm_apply]
  have hkerEq : Φ.ker = CFSG.Open.GLAPPrimeCore p K := by
    ext x
    rw [MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h' : e (QuotientGroup.mk x) = 1 := Subtype.ext h
      exact (map_eq_one_iff e e.injective).1 h'
    · intro h
      show ((e (QuotientGroup.mk x) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 1
      rw [h, map_one]
      rfl
  have hker : Nat.Coprime p (Nat.card Φ.ker) := by
    rw [hkerEq]
    exact CFSG.pPrimeCore_coprime_card
  have hQ : IsPGroup p (P.subgroupOf K) := by
    refine AltInputs2.isPGroup_of_pow_forall (P.subgroupOf K) ?_
    intro g hg
    have hgP : (g : G) ∈ P := Subgroup.mem_subgroupOf.1 hg
    obtain ⟨k, hk⟩ := hP.2.1 ⟨(g : G), hgP⟩
    have hk' : (g : G) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, Subtype.ext (by simpa using hk')⟩
  have hmax : ∀ R : Subgroup K, IsPGroup p R → P.subgroupOf K ≤ R → R = P.subgroupOf K := by
    intro R hR hle
    have hRG : IsPGroup p (R.map K.subtype : Subgroup G) := by
      refine AltInputs2.isPGroup_of_pow_forall _ ?_
      intro g hg
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
      have hk' : r ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact ⟨k, by rw [← map_pow, hk', map_one]⟩
    have hPR : P ≤ R.map K.subtype := by
      intro x hx
      have hxK : x ∈ K := hP.1 hx
      have hmem : (⟨x, hxK⟩ : K) ∈ P.subgroupOf K := Subgroup.mem_subgroupOf.2 hx
      exact Subgroup.mem_map.2 ⟨⟨x, hxK⟩, hle hmem, rfl⟩
    have hRP : R.map K.subtype = P := hP.2.2 (R.map K.subtype) (Subgroup.map_subtype_le R) hRG hPR
    have key : ∀ T : Subgroup K, (T.map K.subtype).subgroupOf K = T := by
      intro T
      ext y
      rw [Subgroup.mem_subgroupOf]
      constructor
      · intro hy
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
        have hzy' : z = y := Subtype.ext hzy
        exact hzy' ▸ hz
      · intro hy
        exact Subgroup.mem_map_of_mem K.subtype hy
    calc R = (R.map K.subtype).subgroupOf K := (key R).symm
      _ = P.subgroupOf K := by rw [hRP]
  exact AltInputs2.exists_unique_transfer hP.1 (AltInputs2.core_of_hom hp2 Φ hrange hker hQ hmax)

end Lemma118T

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
