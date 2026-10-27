module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FMonoCount

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sec4F_sgn_eq_neg_one_of_ne_zero {u : ZMod 2} (hu : u ≠ 0) :
    sec4ISgn u = -1 := by
  revert u
  decide

private abbrev sec4FOffIdx (a b : Fin 7) (u : Fin 7 → ZMod 2) : Type :=
  Option {k : Fin 7 // k ≠ a ∧ k ≠ b ∧ u k ≠ 0}

private abbrev sec4FOnIdx (a b : Fin 7) (u : Fin 7 → ZMod 2) : Type :=
  Option {k : Fin 7 // k ≠ a ∧ k ≠ b ∧ u k = 0}

private noncomputable def sec4FOffFam (fr : Sec4IFrame Q) (a b : Fin 7) (eps : ZMod 3)
    (u : Fin 7 → ZMod 2) : sec4FOffIdx a b u → V
  | none => fr.b a - eps • fr.b b
  | some k => fr.b k

private noncomputable def sec4FOnFam (fr : Sec4IFrame Q) (a b : Fin 7) (eps : ZMod 3)
    (u : Fin 7 → ZMod 2) : sec4FOnIdx a b u → V
  | none => fr.b a + eps • fr.b b
  | some k => fr.b k

private def sec4FOffPiv {a b : Fin 7} {u : Fin 7 → ZMod 2} : sec4FOffIdx a b u → Fin 7
  | none => a
  | some k => k.1

private def sec4FOnPiv {a b : Fin 7} {u : Fin 7 → ZMod 2} : sec4FOnIdx a b u → Fin 7
  | none => a
  | some k => k.1

private lemma sec4F_repr_sub (fr : Sec4IFrame Q) {a b : Fin 7} (eps : ZMod 3) (j : Fin 7) :
    fr.b.repr (fr.b a - eps • fr.b b) j =
      (if a = j then 1 else 0) - eps * (if b = j then 1 else 0) := by
  simp only [map_sub, map_smul, Module.Basis.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]

private lemma sec4F_repr_add (fr : Sec4IFrame Q) {a b : Fin 7} (eps : ZMod 3) (j : Fin 7) :
    fr.b.repr (fr.b a + eps • fr.b b) j =
      (if a = j then 1 else 0) + eps * (if b = j then 1 else 0) := by
  simp only [map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul]

private lemma sec4F_linearIndependent_of_pivot (fr : Sec4IFrame Q) {ι : Type} [Fintype ι]
    (v : ι → V) (p : ι → Fin 7) (hdiag : ∀ i, fr.b.repr (v i) (p i) = 1)
    (hoff : ∀ i j, i ≠ j → fr.b.repr (v i) (p j) = 0) :
    LinearIndependent (ZMod 3) v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (fun x => fr.b.repr x (p j)) hc
  simp only [map_zero, Finsupp.zero_apply] at h
  have hsum : fr.b.repr (∑ i, c i • v i) (p j) = c j := by
    rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_apply']
    simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [hdiag j, mul_one]
    · intro i _ hij
      rw [hoff i j hij, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hsum] at h
  exact h

private lemma sec4F_card_le_finrank {ι : Type} [Fintype ι] {v : ι → V}
    (hv : LinearIndependent (ZMod 3) v) {W : Submodule (ZMod 3) V} (hW : ∀ i, v i ∈ W) :
    Fintype.card ι ≤ Module.finrank (ZMod 3) W := by
  have hle : Submodule.span (ZMod 3) (Set.range v) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hW i
  calc Fintype.card ι
      = Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range v)) :=
        (finrank_span_eq_card hv).symm
    _ ≤ Module.finrank (ZMod 3) W := Submodule.finrank_mono hle

private lemma sec4F_offFam_diag (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b)
    (eps : ZMod 3) (u : Fin 7 → ZMod 2) (i : sec4FOffIdx a b u) :
    fr.b.repr (sec4FOffFam fr a b eps u i) (sec4FOffPiv i) = 1 := by
  cases i with
  | none =>
    change fr.b.repr (fr.b a - eps • fr.b b) a = 1
    rw [sec4F_repr_sub, if_pos rfl, if_neg (Ne.symm hab)]
    simp
  | some k =>
    change fr.b.repr (fr.b (k : Fin 7)) (k : Fin 7) = 1
    rw [Module.Basis.repr_self]
    simp

private lemma sec4F_offFam_off (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b)
    (eps : ZMod 3) (u : Fin 7 → ZMod 2) {i j : sec4FOffIdx a b u} (hij : i ≠ j) :
    fr.b.repr (sec4FOffFam fr a b eps u i) (sec4FOffPiv j) = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some k =>
      change fr.b.repr (fr.b a - eps • fr.b b) (k : Fin 7) = 0
      rw [sec4F_repr_sub, if_neg (Ne.symm k.2.1), if_neg (Ne.symm k.2.2.1)]
      simp
  | some k =>
    cases j with
    | none =>
      change fr.b.repr (fr.b (k : Fin 7)) a = 0
      rw [Module.Basis.repr_self]
      simp [Finsupp.single_apply, k.2.1]
    | some k' =>
      change fr.b.repr (fr.b (k : Fin 7)) (k' : Fin 7) = 0
      rw [Module.Basis.repr_self]
      have hkk' : (k : Fin 7) ≠ (k' : Fin 7) :=
        fun h => hij (congrArg Option.some (Subtype.ext h))
      simp [Finsupp.single_apply, hkk']

private lemma sec4F_onFam_diag (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b)
    (eps : ZMod 3) (u : Fin 7 → ZMod 2) (i : sec4FOnIdx a b u) :
    fr.b.repr (sec4FOnFam fr a b eps u i) (sec4FOnPiv i) = 1 := by
  cases i with
  | none =>
    change fr.b.repr (fr.b a + eps • fr.b b) a = 1
    rw [sec4F_repr_add, if_pos rfl, if_neg (Ne.symm hab)]
    simp
  | some k =>
    change fr.b.repr (fr.b (k : Fin 7)) (k : Fin 7) = 1
    rw [Module.Basis.repr_self]
    simp

private lemma sec4F_onFam_off (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b)
    (eps : ZMod 3) (u : Fin 7 → ZMod 2) {i j : sec4FOnIdx a b u} (hij : i ≠ j) :
    fr.b.repr (sec4FOnFam fr a b eps u i) (sec4FOnPiv j) = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact absurd rfl hij
    | some k =>
      change fr.b.repr (fr.b a + eps • fr.b b) (k : Fin 7) = 0
      rw [sec4F_repr_add, if_neg (Ne.symm k.2.1), if_neg (Ne.symm k.2.2.1)]
      simp
  | some k =>
    cases j with
    | none =>
      change fr.b.repr (fr.b (k : Fin 7)) a = 0
      rw [Module.Basis.repr_self]
      simp [Finsupp.single_apply, k.2.1]
    | some k' =>
      change fr.b.repr (fr.b (k : Fin 7)) (k' : Fin 7) = 0
      rw [Module.Basis.repr_self]
      have hkk' : (k : Fin 7) ≠ (k' : Fin 7) :=
        fun h => hij (congrArg Option.some (Subtype.ext h))
      simp [Finsupp.single_apply, hkk']

private lemma sec4F_card_offpair {a b : Fin 7} (hab : a ≠ b) :
    (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b)).card = 5 := by
  have hT : Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b) =
      (Finset.univ.erase a).erase b := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [hT, Finset.card_erase_of_mem (by simp [Ne.symm hab]),
    Finset.card_erase_of_mem (by simp)]
  norm_num

private lemma sec4F_offCount_add (a b : Fin 7) (hab : a ≠ b) (u : Fin 7 → ZMod 2) :
    sec4FOffCount a b u +
      (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k = 0)).card = 5 := by
  have hp1 : (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k ≠ 0)).card =
      sec4FOffCount a b u := rfl
  rw [← hp1]
  have hdisj : Disjoint (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k ≠ 0))
      (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k = 0)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
    exact hk1.2.2 hk2.2.2
  rw [← Finset.card_union_of_disjoint hdisj]
  have hunion : (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k ≠ 0)) ∪
      (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k = 0)) =
      Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b) := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨ha, hb, _⟩ | ⟨ha, hb, _⟩) <;> exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      by_cases h : u k = 0
      · exact Or.inr ⟨ha, hb, h⟩
      · exact Or.inl ⟨ha, hb, h⟩
  rw [hunion]
  exact sec4F_card_offpair hab

theorem sec4F_invDim_mono_swap (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b)
    {u : Fin 7 → ZMod 2} (hu : u a = u b) :
    invDim (sec4IMono fr (Equiv.swap a b) u) = 1 + sec4FOffCount a b u := by
  set g : OGroup Q := sec4IMono fr (Equiv.swap a b) u with hg
  set eps : ZMod 3 := ((sec4ISgn (u a) : (ZMod 3)ˣ) : ZMod 3) with heps
  change Module.finrank (ZMod 3) (commSp g) = 1 + sec4FOffCount a b u
  have heps2 : eps * eps = 1 := by
    rw [heps, ← pow_two]
    exact sec4ISgn_sq (u a)
  have hga : (g : V ≃ₗ[ZMod 3] V) (fr.b a) = eps • fr.b b := by
    rw [hg, sec4IMono_apply, Equiv.swap_apply_left, heps]
  have hgb : (g : V ≃ₗ[ZMod 3] V) (fr.b b) = eps • fr.b a := by
    rw [hg, sec4IMono_apply, Equiv.swap_apply_right, ← hu, heps]
  have hgk : ∀ k : Fin 7, k ≠ a → k ≠ b → (g : V ≃ₗ[ZMod 3] V) (fr.b k) =
      ((sec4ISgn (u k) : (ZMod 3)ˣ) : ZMod 3) • fr.b k := by
    intro k hka hkb
    rw [hg, sec4IMono_apply, Equiv.swap_apply_of_ne_of_ne hka hkb]
  have huu : (fun i => u i + u (Equiv.swap a b i)) = 0 := by
    funext i
    have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, hu]
      exact h2 (u b)
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, ← hu]
        exact h2 (u a)
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
        exact h2 (u i)
  have hss : Equiv.swap a b * Equiv.swap a b = 1 := by
    ext i
    simp
  have hgg : g * g = 1 := by
    rw [hg, sec4IMono_mul, hss, huu, sec4IMono_one]
  have hcb_comm : (g : V ≃ₗ[ZMod 3] V) (fr.b a - eps • fr.b b) =
      -(fr.b a - eps • fr.b b) := by
    rw [map_sub, map_smul, hga, hgb, smul_smul, heps2, one_smul, neg_sub]
  have hca_fix : (g : V ≃ₗ[ZMod 3] V) (fr.b a + eps • fr.b b) = fr.b a + eps • fr.b b := by
    rw [map_add, map_smul, hga, hgb, smul_smul, heps2, one_smul]
    abel
  have hcb_mem : fr.b a - eps • fr.b b ∈ commSp g :=
    (mem_commSp_iff hgg).mpr hcb_comm
  have hca_mem : fr.b a + eps • fr.b b ∈ fixSp g :=
    mem_fixSp_iff.mpr hca_fix
  have hbk_comm : ∀ k : Fin 7, k ≠ a → k ≠ b → u k ≠ 0 → fr.b k ∈ commSp g := by
    intro k hka hkb hku
    rw [mem_commSp_iff hgg]
    rw [hgk k hka hkb, sec4F_sgn_eq_neg_one_of_ne_zero hku, Units.val_neg, Units.val_one,
      neg_one_smul]
  have hbk_fix : ∀ k : Fin 7, k ≠ a → k ≠ b → u k = 0 → fr.b k ∈ fixSp g := by
    intro k hka hkb hku
    rw [mem_fixSp_iff]
    rw [hgk k hka hkb, hku, sec4ISgn_zero, Units.val_one, one_smul]
  have hSli : LinearIndependent (ZMod 3) (sec4FOffFam fr a b eps u) :=
    sec4F_linearIndependent_of_pivot fr (sec4FOffFam fr a b eps u) sec4FOffPiv
      (sec4F_offFam_diag fr hab eps u)
      (fun i j hij => sec4F_offFam_off fr hab eps u hij)
  have hTli : LinearIndependent (ZMod 3) (sec4FOnFam fr a b eps u) :=
    sec4F_linearIndependent_of_pivot fr (sec4FOnFam fr a b eps u) sec4FOnPiv
      (sec4F_onFam_diag fr hab eps u)
      (fun i j hij => sec4F_onFam_off fr hab eps u hij)
  have hcardS : Fintype.card (sec4FOffIdx a b u) = 1 + sec4FOffCount a b u := by
    change Fintype.card (Option {k : Fin 7 // k ≠ a ∧ k ≠ b ∧ u k ≠ 0}) =
      1 + sec4FOffCount a b u
    rw [Fintype.card_option, Fintype.card_subtype]
    simp only [sec4FOffCount]
    omega
  have hcardT : Fintype.card (sec4FOnIdx a b u) =
      1 + (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k = 0)).card := by
    change Fintype.card (Option {k : Fin 7 // k ≠ a ∧ k ≠ b ∧ u k = 0}) =
      1 + (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k = 0)).card
    rw [Fintype.card_option, Fintype.card_subtype]
    omega
  have hSle : 1 + sec4FOffCount a b u ≤ Module.finrank (ZMod 3) (commSp g) := by
    calc 1 + sec4FOffCount a b u
        = Fintype.card (sec4FOffIdx a b u) := hcardS.symm
      _ ≤ Module.finrank (ZMod 3) (commSp g) :=
        sec4F_card_le_finrank hSli (fun i => by
          cases i with
          | none => exact hcb_mem
          | some k => exact hbk_comm (k : Fin 7) k.2.1 k.2.2.1 k.2.2.2)
  have hTle : 1 + (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k = 0)).card ≤
      Module.finrank (ZMod 3) (fixSp g) := by
    calc 1 + (Finset.univ.filter (fun k : Fin 7 => k ≠ a ∧ k ≠ b ∧ u k = 0)).card
        = Fintype.card (sec4FOnIdx a b u) := hcardT.symm
      _ ≤ Module.finrank (ZMod 3) (fixSp g) :=
        sec4F_card_le_finrank hTli (fun i => by
          cases i with
          | none => exact hca_mem
          | some k => exact hbk_fix (k : Fin 7) k.2.1 k.2.2.1 k.2.2.2)
  have hsum : Module.finrank (ZMod 3) (fixSp g) + Module.finrank (ZMod 3) (commSp g) = 7 := by
    rw [finrank_fixSp_add_finrank_commSp, Module.finrank_eq_card_basis fr.b]
    simp
  have hnm := sec4F_offCount_add a b hab u
  omega

end CFSG.OddStandard.SmallF3.Omega
