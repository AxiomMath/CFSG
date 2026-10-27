module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAction

public section

namespace CFSG.QuasithinUnique.Setup.X1

section Aut

variable {G : Type*} [Group G] [Finite G]

theorem autInner_of_card_le (hc : Subgroup.center G = ⊥) (hcard : Nat.card (MulAut G) ≤ Nat.card G) :
    ∀ φ : G ≃* G, ∃ s : G, ∀ x, φ x = s * x * s⁻¹ := by
  have hconj := CFSG.QuasithinUnique.Setup.Family.conj_injective_of_center_eq_bot hc
  have hcard2 : Nat.card G ≤ Nat.card (MulAut G) := Nat.card_le_card_of_injective _ hconj
  have hbij : Function.Bijective (MulAut.conj : G →* MulAut G) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hconj, le_antisymm hcard2 hcard⟩
  intro φ
  obtain ⟨s, hs⟩ := hbij.2 φ
  exact ⟨s, fun x => by rw [← hs]; rfl⟩

theorem inner_of_outer_mul (hc : Subgroup.center G = ⊥)
    (hcard : Nat.card (MulAut G) ≤ 2 * Nat.card G) {φ ψ : MulAut G}
    (hφ : φ ∉ (MulAut.conj : G →* MulAut G).range) (hψ : ψ ∉ (MulAut.conj : G →* MulAut G).range) :
    φ⁻¹ * ψ ∈ (MulAut.conj : G →* MulAut G).range := by
  have hconj := CFSG.QuasithinUnique.Setup.Family.conj_injective_of_center_eq_bot hc
  set H := (MulAut.conj : G →* MulAut G).range with hH
  have hHcard : Nat.card H = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hmul := Subgroup.card_mul_index H
  have hidx : H.index ≤ 2 := by
    have hpos : 0 < Nat.card G := Nat.card_pos
    rw [hHcard] at hmul
    nlinarith
  have hne1 : H.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    exact hφ (h1 ▸ Subgroup.mem_top φ)
  have hidx2 : H.index = 2 := by
    have : H.index ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hmul
      exact Nat.card_pos.ne' hmul.symm
    omega
  have hφ' : φ⁻¹ ∉ H := fun h => hφ (by simpa using H.inv_mem h)
  exact (Subgroup.mul_mem_iff_of_index_two hidx2).2 (iff_of_false hφ' hψ)

end Aut

section Conj

variable {S : Type*} [Group S]

@[expose] def conjSet (cs : List S) (T : Set S) : Set S :=
  {y | ∃ c ∈ cs, ∃ t ∈ T, y = c * t * c⁻¹}

theorem conjSet_mono {cs : List S} {T T' : Set S} (h : T ⊆ T') : conjSet cs T ⊆ conjSet cs T' :=
  fun _ ⟨c, hc, t, ht, hy⟩ => ⟨c, hc, t, h ht, hy⟩

theorem closure_conjSet_transfer {T T' : Set S} (g : S) (h : ∀ t' ∈ T', ∃ t ∈ T, g * t * g⁻¹ = t')
    (cs : List S) {x : S} (hx : x ∈ Subgroup.closure (conjSet cs T')) :
    x ∈ Subgroup.closure (conjSet (cs.map (· * g)) T) := by
  refine Subgroup.closure_mono ?_ hx
  rintro _ ⟨c, hc, t', ht', rfl⟩
  obtain ⟨t, ht, rfl⟩ := h t' ht'
  exact ⟨c * g, List.mem_map.2 ⟨c, hc, rfl⟩, t, ht, by group⟩

end Conj

section Sylow

variable {P : Type*} [Group P] [Finite P]

theorem exists_subgroup_of_list (Rl : List P) (h1 : (1 : P) ∈ Rl)
    (hmul : ∀ x ∈ Rl, ∀ y ∈ Rl, x * y ∈ Rl) : ∃ R : Subgroup P, ∀ x, x ∈ R ↔ x ∈ Rl := by
  have hpow : ∀ x ∈ Rl, ∀ n : ℕ, x ^ n ∈ Rl := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  have hinv : ∀ x ∈ Rl, x⁻¹ ∈ Rl := by
    intro x hx
    have hpos := orderOf_pos x
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel hpos,
        pow_orderOf_eq_one]
    rw [this]
    exact hpow x hx _
  let R : Subgroup P :=
    { carrier := {x | x ∈ Rl}
      one_mem' := h1
      mul_mem' := by
        intro a b ha hb
        exact hmul a ha b hb
      inv_mem' := by
        intro x hx
        exact hinv x hx }
  exact ⟨R, fun x => Iff.rfl⟩

theorem exists_subgroup_of_gens (rg Rl : List P) (h1 : (1 : P) ∈ Rl)
    (hgen : ∀ x ∈ Rl, ∀ g ∈ rg, x * g ∈ Rl)
    (hRl : ∀ x ∈ Rl, x ∈ Subgroup.closure {g | g ∈ rg}) :
    ∃ R : Subgroup P, ∀ x, x ∈ R ↔ x ∈ Rl := by
  refine ⟨Subgroup.closure {g | g ∈ rg}, fun x => ⟨fun hx => ?_, hRl x⟩⟩
  have key : ∀ x ∈ Subgroup.closure {g | g ∈ rg}, ∀ y ∈ Rl, y * x ∈ Rl := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact fun y hy => hgen y hy g hg
    | one => exact fun y hy => by simpa using hy
    | mul a b _ _ ha hb => exact fun y hy => by rw [← mul_assoc]; exact hb _ (ha y hy)
    | inv a _ ha =>
      intro y hy
      have hpow : ∀ n : ℕ, y * a ^ n ∈ Rl := by
        intro n
        induction n with
        | zero => simpa using hy
        | succ n ih => rw [pow_succ, ← mul_assoc]; exact ha _ ih
      have hpos := orderOf_pos a
      have : a⁻¹ = a ^ (orderOf a - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv', ← pow_succ', Nat.sub_add_cancel hpos,
          pow_orderOf_eq_one]
      rw [this]
      exact hpow _
  simpa using key x hx 1 h1

theorem exists_conj_mem_of_subgroup (R : Subgroup P) (Rl : List P) (hR : ∀ x, x ∈ R ↔ x ∈ Rl)
    {a m : ℕ} (hpow : ∀ x ∈ Rl, x ^ (2 ^ a) = 1) (hnd : Rl.Nodup) (hlen : Rl.length = 2 ^ a)
    (hS : Nat.card P = 2 ^ a * m) (hm : Odd m) (B : Subgroup P) (hB : ∀ x ∈ B, x * x = 1) :
    ∃ g : P, ∀ x ∈ B, g * x * g⁻¹ ∈ Rl := by
  have hRcard : Nat.card R = 2 ^ a := by
    classical
    have hset : (R : Set P) = ↑(Rl.toFinset) := by
      ext x
      simp [hR x]
    calc Nat.card R = (R : Set P).ncard := Nat.card_coe_set_eq (R : Set P)
      _ = Rl.toFinset.card := by rw [hset, Set.ncard_coe_finset]
      _ = Rl.length := List.toFinset_card_of_nodup hnd
      _ = 2 ^ a := hlen
  have hidx : R.index = m := by
    have := Subgroup.card_mul_index R
    rw [hRcard, hS] at this
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hodd : ¬ 2 ∣ R.index := by
    rw [hidx]
    intro hd
    obtain ⟨k, hk⟩ := hm
    omega
  have hpg : IsPGroup 2 R := by
    intro x
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have hx : (x : P) ∈ Rl := (hR x).1 x.2
    simpa using hpow _ hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 B := by
    intro x
    refine ⟨1, ?_⟩
    have := hB x x.2
    apply Subtype.ext
    simpa [sq] using this
  obtain ⟨Q, hQ⟩ := hBp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P Q (hpg.toSylow hodd)
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup P) := hQ hx
  have hmem : g * x * g⁻¹ ∈ ((g • Q : Sylow 2 P) : Set P) := by
    rw [Sylow.coe_smul]
    exact ⟨x, hxQ, rfl⟩
  rw [hg] at hmem
  exact (hR _).1 hmem

theorem exists_conj_mem_list (Rl : List P) (h1 : (1 : P) ∈ Rl)
    (hmul : ∀ x ∈ Rl, ∀ y ∈ Rl, x * y ∈ Rl) {a m : ℕ}
    (hpow : ∀ x ∈ Rl, x ^ (2 ^ a) = 1) (hnd : Rl.Nodup) (hlen : Rl.length = 2 ^ a)
    (hS : Nat.card P = 2 ^ a * m) (hm : Odd m) (B : Subgroup P) (hB : ∀ x ∈ B, x * x = 1) :
    ∃ g : P, ∀ x ∈ B, g * x * g⁻¹ ∈ Rl := by
  obtain ⟨R, hR⟩ := exists_subgroup_of_list Rl h1 hmul
  exact exists_conj_mem_of_subgroup R Rl hR hpow hnd hlen hS hm B hB

end Sylow

section Indep

theorem IndepList.of_append_right {P : Type*} [Group P] {l' l : List P}
    (h : IndepList (l' ++ l)) : IndepList l := by
  induction l' with
  | nil => simpa using h
  | cons a l' ih =>
    cases h with
    | cons _ _ _ _ _ _ h' => exact ih h'

variable {P : Type*} [Group P] [DecidableEq P]

@[expose] def indepExt (Rinv : List P) (l : List P) : List P :=
  let sp := subprods l
  Rinv.filter fun x => decide (∀ y ∈ l, x * y = y * x) && !(decide (x ∈ sp))

@[expose] def forallIndep (Rinv : List P) (pred : List P → Bool) : ℕ → List P → Bool
  | 0, l => pred l
  | k + 1, l => (indepExt Rinv l).all fun x => forallIndep Rinv pred k (x :: l)

theorem forallIndep_sound (Rinv : List P) (pred : List P → Bool) :
    ∀ (k : ℕ) (l : List P), forallIndep Rinv pred k l = true → ∀ l' : List P, l'.length = k →
      (∀ y ∈ l', y ∈ Rinv) → IndepList (l' ++ l) → pred (l' ++ l) = true := by
  intro k
  induction k with
  | zero =>
    intro l h l' hlen _ _
    have : l' = [] := List.length_eq_zero_iff.1 hlen
    subst this
    simpa [forallIndep] using h
  | succ k ih =>
    intro l h l' hlen hmem hind
    obtain ⟨l'', z, rfl⟩ : ∃ l'' z, l' = l'' ++ [z] := by
      have hne : l' ≠ [] := by
        intro h0; subst h0; simp at hlen
      exact ⟨l'.dropLast, l'.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hrw : l'' ++ [z] ++ l = l'' ++ (z :: l) := by simp
    rw [hrw] at hind ⊢
    have hz : IndepList (z :: l) := IndepList.of_append_right hind
    have hzmem : z ∈ Rinv := hmem z (by simp)
    have hzext : z ∈ indepExt Rinv l := by
      cases hz with
      | cons _ _ _ _ hc hs _ =>
        simp only [indepExt, List.mem_filter]
        refine ⟨hzmem, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        exact ⟨hc, hs⟩
    have hnext : forallIndep Rinv pred k (z :: l) = true := by
      rw [forallIndep, List.all_eq_true] at h
      exact h z hzext
    exact ih (z :: l) hnext l'' (by simpa using hlen) (fun y hy => hmem y (by simp [hy])) hind

end Indep


section Witness

variable {G : Type*} [Group G]

@[expose] def prodWord (gens : List G) (w : List ℕ) : G := (w.map fun i => gens.getD i 1).prod

theorem prodWord_mem_closure (gens : List G) (w : List ℕ) :
    prodWord gens w ∈ Subgroup.closure {g : G | g ∈ gens} := by
  unfold prodWord
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [List.getD_eq_getElem?_getD]
  cases h : gens[i]? with
  | none => exact Subgroup.one_mem _
  | some g => exact Subgroup.subset_closure (List.mem_of_getElem? h)

theorem exists_mem_closure_conjSet {cs : List G} {T : Set G} {gens : List G}
    (hg : ∀ g ∈ gens, g ∈ conjSet cs T) (w : List ℕ) {p : ℕ}
    (hp : orderOf (prodWord gens w) = p) :
    ∃ x ∈ Subgroup.closure (conjSet cs T), orderOf x = p :=
  ⟨prodWord gens w, Subgroup.closure_mono (fun g hg' => hg g hg') (prodWord_mem_closure gens w), hp⟩

end Witness

section IndepLemmas

variable {S : Type*} [Group S]

theorem exists_indepList_of_lt_card [Finite S] (B : Subgroup S)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) (n : ℕ)
    (hgt : 2 ^ n < Nat.card B) :
    ∃ l : List S, IndepList l ∧ l.length = n + 1 ∧ ∀ y ∈ l, y ∈ B := by
  have key : ∀ m, m ≤ n + 1 → ∃ l : List S, IndepList l ∧ l.length = m ∧ ∀ y ∈ l, y ∈ B := by
    intro m
    induction m with
    | zero => intro _; exact ⟨[], IndepList.nil, rfl, by simp⟩
    | succ m ih =>
      intro hm
      obtain ⟨l, hl, hlen, hlB⟩ := ih (by omega)
      classical
      have hsub : ∃ x ∈ B, x ∉ subprods l := by
        by_contra hno
        push Not at hno
        have : Nat.card B ≤ (subprods l).toFinset.card := by
          have hle : (B : Set S) ⊆ ((subprods l).toFinset : Set S) := fun x hx => by
            simpa using hno x hx
          calc Nat.card B = (B : Set S).ncard := Nat.card_coe_set_eq _
            _ ≤ ((subprods l).toFinset : Set S).ncard := Set.ncard_le_ncard hle
            _ = (subprods l).toFinset.card := Set.ncard_coe_finset _
        have h2 : (subprods l).toFinset.card ≤ 2 ^ m := by
          calc (subprods l).toFinset.card ≤ (subprods l).length := List.toFinset_card_le _
            _ = 2 ^ l.length := length_subprods l
            _ = 2 ^ m := by rw [hlen]
        have h3 : 2 ^ m ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨x, hxB, hx⟩ := hsub
      refine ⟨x :: l, IndepList.cons x l (hsq x hxB) ?_ (fun y hy => hcomm x hxB y (hlB y hy)) hx hl,
        by simp [hlen], ?_⟩
      · intro h1
        exact hx (h1 ▸ one_mem_subprods l)
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hxB
        · exact hlB y hy
  exact key (n + 1) le_rfl

theorem indepList_two {x y : S} (h : IndepList [x, y]) :
    x * x = 1 ∧ y * y = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧ x * y = y * x ∧ x ≠ y := by
  have e1 : subprods [y] = [1, y] := by simp [subprods]
  cases h with
  | cons _ _ hx2 hx1 hxc hxs hl =>
    cases hl with
    | cons _ _ hy2 hy1 hyc hys hl' =>
      rw [e1] at hxs
      refine ⟨hx2, hy2, hx1, hy1, hxc y (by simp), ?_⟩
      intro h
      exact hxs (by simp [h])

theorem IndepList.ne_one {l : List S} (h : IndepList l) : ∀ y ∈ l, y ≠ 1 := by
  induction h with
  | nil => simp
  | cons x l hx2 hx1 hc hs hl ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx1
    · exact ih y hy

end IndepLemmas

end CFSG.QuasithinUnique.Setup.X1
