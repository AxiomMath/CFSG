module

public import CFSG.Certificates.Kernel.E27Lie.Sound
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.E27Lie

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KS.PF
open CFSG.HardMathSupport.Foote.E27 Subgroup

structure KeyRep {G : Type*} [Group G] (R : ℕ → G → Prop) (mm : ℕ → ℕ → ℕ) (one : ℕ) : Prop where
  one : R one 1
  mul : ∀ {a b : ℕ} {x y : G}, R a x → R b y → R (mm a b) (x * y)
  elt : ∀ {a : ℕ} {x y : G}, R a x → R a y → x = y
  key : ∀ {a b : ℕ} {x : G}, R a x → R b x → a = b

variable {G : Type*} [Group G] {R : ℕ → G → Prop} {mm : ℕ → ℕ → ℕ} {ONE : ℕ} {g : ℕ → G}
variable {gk key pp pj : ℕ → ℕ} {m n : ℕ}

theorem tree_specR (hR : KeyRep R mm ONE) (hg : ∀ j < m, R (gk j) (g j))
    (ht : ∀ i < n, treeC mm key pp pj gk ONE m i = true) :
    ∀ i < n, (0 < i → pp i < i ∧ pj i < m) ∧ R (key i) (tabElt g (parOf n pp pj) i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have h := ht i hi
    unfold treeC at h
    rw [bRec_eq] at h
    by_cases h0 : i = 0
    · subst h0
      have e0 : Nat.beq 0 0 = true := rfl
      rw [if_pos e0] at h
      have e := beq_of h
      refine ⟨fun h => absurd h (Nat.lt_irrefl 0), ?_⟩
      rw [e, tabElt_zero]
      exact hR.one
    · have hb : (Nat.beq i 0 = true) = False := by
        simp only [Nat.beq_eq, h0]
      rw [if_neg (by rw [hb]; exact id), sB_eq, sB_eq, bRec_eq] at h
      split_ifs at h with h1
      · rw [bRec_eq] at h
        split_ifs at h with h2
        · have hp := blt_of h1
          have hj := blt_of h2
          have e := beq_of h
          have hpar : (parOf n pp pj)[i]! = (pp i, pj i) := ofFnG (fun i => (pp i, pj i)) hi
          obtain ⟨-, hv⟩ := ih (pp i) hp (by omega)
          refine ⟨fun _ => ⟨hp, hj⟩, ?_⟩
          have hpi : ((parOf n pp pj)[i]!).1 < i := by rw [hpar]; exact hp
          rw [tabElt_succ g (parOf n pp pj) hpi, hpar, e]
          exact hR.mul (hg _ hj) hv

theorem tabData_ofR (hR : KeyRep R mm ONE) (hg : ∀ j < m, R (gk j) (g j))
    (ht : ∀ i < n, treeC mm key pp pj gk ONE m i = true)
    {lt : ℕ → ℕ → ℕ} (hl : ∀ i < n, ∀ j < m, leftC mm key lt gk n j i = true)
    {sg : ℕ → ℕ} (hs : ∀ q < n, sortC key sg n q = true) :
    TabData g (parOf n pp pj) (ltOf m n lt) n m := by
  have hE := tree_specR hR hg ht
  have hs' : ∀ q < n, sg q < n ∧ (q + 1 < n → key (sg q) < key (sg (q + 1))) := by
    intro q hq
    have h := hs q hq
    unfold sortC at h
    rw [sB_eq, bRec_eq] at h
    split_ifs at h with h1
    · rw [bRec_eq] at h
      refine ⟨blt_of h1, fun hq1 => ?_⟩
      rw [if_pos (Eq.mpr Nat.blt_eq hq1), sB_eq] at h
      exact blt_of h
  have mono : ∀ q q', q < q' → q' < n → key (sg q) < key (sg q') := by
    intro q q' hqq hq'
    induction q' with
    | zero => omega
    | succ q' ih =>
      rcases Nat.lt_or_ge q q' with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((hs' q' (by omega)).2 hq')
      · have : q = q' := by omega
        subst this
        exact (hs' q (by omega)).2 hq'
  have sinj : ∀ q < n, ∀ q' < n, sg q = sg q' → q = q' := by
    intro q hq q' hq' e
    rcases Nat.lt_trichotomy q q' with h | h | h
    · have := mono q q' h hq'
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
    · exact h
    · have := mono q' q h hq
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
  have ssurj : ∀ i < n, ∃ q < n, sg q = i := by
    let F : Fin n → Fin n := fun q => ⟨sg q.val, (hs' q.val q.isLt).1⟩
    have hF : Function.Injective F := fun a b e =>
      Fin.ext (sinj a.val a.isLt b.val b.isLt (congrArg Fin.val e))
    intro i hi
    obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.mp hF) ⟨i, hi⟩
    exact ⟨q.val, q.isLt, congrArg Fin.val hq⟩
  have kinj : ∀ i < n, ∀ k < n, key i = key k → i = k := by
    intro i hi k hk e
    obtain ⟨q, hq, rfl⟩ := ssurj i hi
    obtain ⟨q', hq', rfl⟩ := ssurj k hk
    have hqq : q = q' := by
      rcases Nat.lt_trichotomy q q' with h | h | h
      · exact absurd e (Nat.ne_of_lt (mono q q' h hq'))
      · exact h
      · exact absurd e.symm (Nat.ne_of_lt (mono q' q h hq))
    rw [hqq]
  refine ⟨fun i hi0 hi => ?_, fun j hj i hi => ?_, fun i hi k hk e => ?_⟩
  · rw [ofFnG (fun i => (pp i, pj i)) hi]
    exact (hE i hi).1 hi0
  · have h := hl i hi j hj
    unfold leftC at h
    rw [sB_eq, bRec_eq] at h
    split_ifs at h with h1
    · have hl1 := blt_of h1
      have e := beq_of h
      have hL : ((ltOf m n lt)[j]!)[i]! = lt j i := by
        rw [ofFnG (fun j => Array.ofFn (n := n) fun i => lt j i.val) hj,
          ofFnG (fun i => lt j i) hi]
      rw [hL]
      refine ⟨hl1, hR.elt (hR.mul (hg j hj) (hE i hi).2) ?_⟩
      rw [← e]
      exact (hE _ hl1).2
  · refine kinj i hi k hk (hR.key (hE i hi).2 ?_)
    rw [e]
    exact (hE k hk).2

theorem sylow_ofR [Finite G] (hR : KeyRep R mm ONE) (hg : ∀ j < m, R (gk j) (g j))
    (ht : ∀ i < n, treeC mm key pp pj gk ONE m i = true)
    {lt : ℕ → ℕ → ℕ} (hl : ∀ i < n, ∀ j < m, leftC mm key lt gk n j i = true)
    {sg : ℕ → ℕ} (hs : ∀ q < n, sortC key sg n q = true)
    {W CI REP CB : ℕ → ℕ} {cw : ℕ → ℕ → ℕ} {nr : ℕ}
    (hk : ∀ a < n, killC mm key W CI REP n nr a = true)
    (hr : ∀ c < nr, repC mm key REP CB cw ONE n 81 c = true)
    (hn : n = 3 ^ (Nat.card G).factorization 3) :
    ∃ S₀ : Subgroup G, Nat.card S₀ = 3 ^ (Nat.card G).factorization 3 ∧
      ∀ s ∈ S₀, orderOf s = 3 → 81 ∣ Nat.card ↥(S₀ ⊓ centralizer ({s} : Set G)) := by
  have hT := tabData_ofR hR hg ht hl hs
  have hE := tree_specR hR hg ht
  have hn0 : 0 < n := by rw [hn]; positivity
  obtain ⟨S₀, hS, -⟩ := hT.exists_subgroup hn0
  have hcS := hT.card_subgroup hS
  set E := tabElt g (parOf n pp pj) with hEdef
  have prod : ∀ a < n, ∀ b < n, R (mm (key a) (key b)) (E a * E b) := fun a ha b hb =>
    hR.mul (hE a ha).2 (hE b hb).2
  have prodEq : ∀ a < n, ∀ b < n, ∀ c < n, ∀ e < n,
      mm (key a) (key b) = mm (key c) (key e) → E a * E b = E c * E e := by
    intro a ha b hb c hc' e he h
    have h1 := prod a ha b hb
    rw [h] at h1
    exact hR.elt h1 (prod c hc' e he)
  refine ⟨S₀, hcS.trans hn, fun s hs3 hord => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (hS s).1 hs3
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [hEdef, tabElt_zero] at hord
    simp at hord
  have h := hk a ha
  unfold killC at h
  have hb0 : (Nat.beq a 0 = true) = False := by simp only [Nat.beq_eq, ha0]
  rw [bRec_eq, if_neg (by rw [hb0]; exact id), sB_eq, sB_eq, bRec_eq] at h
  split_ifs at h with h1
  rw [bRec_eq] at h
  split_ifs at h with h2
  rw [sB_eq] at h
  have hw := blt_of h1
  have hci := blt_of h2
  have hrc := hr (CI a) hci
  unfold repC at hrc
  rw [sB_eq, bRec_eq] at hrc
  split_ifs at hrc with h3
  have hx := blt_of h3
  have hconj : E (W a) * E a = E (REP (CI a)) * E (W a) :=
    prodEq _ hw _ ha _ hx _ hw (beq_of h)
  have hcard := card_inf_centralizer_conj ((hS _).2 ⟨_, hw, rfl⟩) hconj
  have hcube : E (REP (CI a)) ^ 3 = 1 := by
    have hy : E (REP (CI a)) = E (W a) * E a * (E (W a))⁻¹ := by
      rw [hconj, mul_inv_cancel_right]
    rw [hy, conj_pow, ← hord, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hr0 : REP (CI a) ≠ 0 := by
    intro e
    have : E (W a) * E a * (E (W a))⁻¹ = 1 := by
      rw [hconj, mul_inv_cancel_right, e, hEdef, tabElt_zero]
    have : E a = 1 := by
      have := congrArg (fun z => (E (W a))⁻¹ * z * E (W a)) this
      simpa [mul_assoc] using this
    rw [this] at hord
    simp at hord
  have hb0' : (Nat.beq (REP (CI a)) 0 = true) = False := by simp only [Nat.beq_eq, hr0]
  rw [bRec_eq, if_neg (by rw [hb0']; exact id), sB_eq, bRec_eq] at hrc
  have h81 : 81 ≤ Nat.card ↥(S₀ ⊓ centralizer ({E (REP (CI a))} : Set G)) := by
    split_ifs at hrc with h4
    · exfalso
      rw [notB_eq, Bool.not_eq_true'] at hrc
      have hx3 : R (mm (key (REP (CI a))) (mm (key (REP (CI a))) (key (REP (CI a)))))
          (E (REP (CI a)) * (E (REP (CI a)) * E (REP (CI a)))) :=
        hR.mul (hE _ hx).2 (prod _ hx _ hx)
      rw [← pow_three, hcube] at hx3
      rw [hR.key hx3 hR.one] at hrc
      exact absurd (Nat.beq_refl ONE) (by rw [hrc]; simp)
    · have hall := CFSG.KS.allN_spec hrc
      have hw' : ∀ t < 81, cw (CI a) t < n ∧ (t ≠ 0 → cw (CI a) (t - 1) < cw (CI a) t) ∧
          E (cw (CI a) t) * E (REP (CI a)) = E (REP (CI a)) * E (cw (CI a) t) := by
        intro t ht
        have h5 := hall t ht
        rw [sB_eq, bRec_eq] at h5
        split_ifs at h5 with h6
        rw [bRec_eq] at h5
        split_ifs at h5 with h7
        rw [sB_eq] at h5
        have hcw := blt_of h6
        refine ⟨hcw, fun ht0 => ?_, prodEq _ hcw _ hx _ hx _ hcw (beq_of h5)⟩
        have hb : (Nat.beq t 0 = true) = False := by simp only [Nat.beq_eq, ht0]
        rw [bRec_eq, if_neg (by rw [hb]; exact id)] at h7
        exact blt_of h7
      have mono : ∀ t t', t < t' → t' < 81 → cw (CI a) t < cw (CI a) t' := by
        intro t t' htt ht'
        induction t' with
        | zero => omega
        | succ t' ih =>
          have := (hw' (t' + 1) ht').2.1 (by omega)
          rw [Nat.add_sub_cancel] at this
          rcases Nat.lt_or_ge t t' with h | h
          · exact Nat.lt_trans (ih h (by omega)) this
          · have : t = t' := by omega
            subst this
            exact this
      let F : Fin 81 → ↥(S₀ ⊓ centralizer ({E (REP (CI a))} : Set G)) := fun t =>
        ⟨E (cw (CI a) t.val), Subgroup.mem_inf.2 ⟨(hS _).2 ⟨_, (hw' t.val t.isLt).1, rfl⟩,
          mem_centralizer_singleton_iff.2 (hw' t.val t.isLt).2.2⟩⟩
      have hF : Function.Injective F := by
        intro t t' e
        have e' := hT.inj _ (hw' t.val t.isLt).1 _ (hw' t'.val t'.isLt).1 (congrArg Subtype.val e)
        rcases Nat.lt_trichotomy t.val t'.val with h | h | h
        · exact absurd e' (Nat.ne_of_lt (mono _ _ h t'.isLt))
        · exact Fin.ext h
        · exact absurd e'.symm (Nat.ne_of_lt (mono _ _ h t.isLt))
      have := Nat.card_le_card_of_injective F hF
      simpa using this
  rw [← hcard] at h81
  have hdvd : Nat.card ↥(S₀ ⊓ centralizer ({E a} : Set G)) ∣ 3 ^ (Nat.card G).factorization 3 := by
    rw [← hcS.trans hn]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, -, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hkeq] at h81 ⊢
  have : 4 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = 4 + j := ⟨k - 4, by omega⟩
  exact ⟨3 ^ j, by rw [pow_add]; norm_num⟩

@[expose] def PRep (n w : ℕ) (ψ : G →* Equiv.Perm (Fin n)) (P : ℕ) (x : G) : Prop :=
  P >>> (n * w) = 0 ∧ ∀ i : Fin n, pg w (mask w) P i = (ψ x i : ℕ)

theorem permRep {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {ψ : G →* Equiv.Perm (Fin n)}
    (hψ : Function.Injective ψ) : KeyRep (PRep n w ψ) (pcomp n w (mask w)) (pidn n w) := by
  have hn32 : n < 2 ^ 32 := by
    have : (16777216 : ℕ) ≤ 2 ^ 32 := by norm_num
    omega
  have hw0 := w_pos hw
  refine ⟨⟨pidn_shr hn hw, fun i => by rw [pg_pidn hn hw i.isLt, map_one]; rfl⟩, ?_, ?_, ?_⟩
  · rintro a b x y ⟨-, ha⟩ ⟨-, hb⟩
    refine ⟨pcomp_shr a b hn32 hw0, fun i => ?_⟩
    rw [pg_pcomp hn32 i.isLt, hb i, ha, map_mul, Equiv.Perm.mul_apply]
  · rintro a x y ⟨-, hx⟩ ⟨-, hy⟩
    refine hψ (Equiv.ext fun i => Fin.ext ?_)
    rw [← hx i, ← hy i]
  · rintro a b x ⟨ha0, ha⟩ ⟨hb0, hb⟩
    exact eq_of_fields hw0 ha0 hb0 fun i hi => by rw [ha ⟨i, hi⟩, hb ⟨i, hi⟩]

end CFSG.KS.E27Lie

end
