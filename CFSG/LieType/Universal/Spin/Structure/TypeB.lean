module

public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Steinberg.Extras
import CFSG.LieType.Universal.Spin.Structure.Levels
import CFSG.LieType.Universal.Spin.Structure.Spinor
import CFSG.LieType.Universal.Spin.Structure.Entries

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap CFSG.LieType.Steinberg

variable {n : ℕ} {K : Type} [Field K]

private def idxB (m : Fin n) : Bool → Fin n ⊕ Fin n ⊕ Unit
  | true => .inl m
  | false => .inr (.inl m)

private def zB : Fin n ⊕ Fin n ⊕ Unit := .inr (.inr ())

private def lvlB : Fin n ⊕ Fin n ⊕ Unit → ℤ
  | .inl m => (n : ℤ) - m
  | .inr (.inl m) => -((n : ℤ) - m)
  | .inr (.inr _) => 0

private theorem lvlB_idxB (m : Fin n) (r : Bool) :
    lvlB (idxB m r) = boolSign r * ((n : ℤ) - m) := by
  cases r <;> simp [lvlB, idxB]

private theorem lvlB_zB : lvlB (zB (n := n)) = 0 := rfl

private theorem idxB_surj (a : Fin n ⊕ Fin n ⊕ Unit) : (∃ m r, idxB m r = a) ∨ a = zB := by
  rcases a with m | m | ⟨⟩
  · exact Or.inl ⟨m, true, rfl⟩
  · exact Or.inl ⟨m, false, rfl⟩
  · exact Or.inr rfl

private theorem idxB_ne {i j : Fin n} (hij : i ≠ j) (s t : Bool) : idxB i s ≠ idxB j t := by
  intro h
  cases s <;> cases t <;> simp_all [idxB]

private theorem idxB_ne_zB (m : Fin n) (r : Bool) : idxB m r ≠ zB := by
  cases r <;> simp [idxB, zB]

private theorem isCoord_oddFrame : (oddFrame n K).IsCoord (idxB (n := n)) zB where
  idx_inj {m r m' r'} h := by
    cases r <;> cases r' <;> simp_all [idxB]
  vec_eq m r := by cases r <;> rfl
  polar_vec v m r := by
    cases r
    · exact polar_quadOdd_single_inr_inl n K v m
    · exact polar_quadOdd_single_inl n K v m
  idx_ne := idxB_ne_zB
  z_eq := rfl
  polar_z v := polar_quadOdd_single_inr_inr n K v

private theorem exists_oddRootGroup_eq {γ : Fin n → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅) :
    (∃ (i j : Fin n) (hij : i ≠ j) (s t : Bool),
        toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) ∧
          oddRootGroup n K γ = ((oddFrame n K).longRoot hij s t).range) ∨
      ∃ (i : Fin n) (s : Bool), toStdB n γ = Pi.single i (boolSign s) ∧
        oddRootGroup n K γ = ((oddFrame n K).shortRoot i s).range := by
  rw [rootsB_eq] at hγ
  rcases hγ with ⟨i, j, s, t, hij, hs, ht, h⟩ | ⟨i, s, hs, h⟩
  · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
    obtain ⟨t', rfl⟩ := exists_boolSign_eq ht
    exact Or.inl ⟨i, j, hij, s', t', h, oddRootGroup_eq_long hij s' t' h⟩
  · obtain ⟨s', rfl⟩ := exists_boolSign_eq hs
    exact Or.inr ⟨i, s', h, oddRootGroup_eq_short i s' h⟩

private theorem lvlB_sub_long₁ {γ : Fin n → ℤ} {i j : Fin n} {s t : Bool}
    (hstd : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    lvlB (idxB i s) - lvlB (idxB j (!t)) = ht γ := by
  rw [ht_of_toStdB_eq_add n hstd, lvlB_idxB, lvlB_idxB, boolSign_not]
  ring

private theorem lvlB_sub_long₂ {γ : Fin n → ℤ} {i j : Fin n} {s t : Bool}
    (hstd : toStdB n γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    lvlB (idxB j t) - lvlB (idxB i (!s)) = ht γ := by
  rw [ht_of_toStdB_eq_add n hstd, lvlB_idxB, lvlB_idxB, boolSign_not]
  ring

private theorem lvlB_sub_short₁ {γ : Fin n → ℤ} {i : Fin n} {s : Bool}
    (hstd : toStdB n γ = Pi.single i (boolSign s)) :
    lvlB (zB (n := n)) - lvlB (idxB i (!s)) = ht γ := by
  rw [ht_of_toStdB_eq_single n hstd, lvlB_zB, lvlB_idxB, boolSign_not]
  ring

private theorem lvlB_sub_short₂ {γ : Fin n → ℤ} {i : Fin n} {s : Bool}
    (hstd : toStdB n γ = Pi.single i (boolSign s)) :
    lvlB (idxB i s) - lvlB (zB (n := n)) = ht γ := by
  rw [ht_of_toStdB_eq_single n hstd, lvlB_zB, lvlB_idxB]
  ring

private theorem lvlB_sub_short₃ {γ : Fin n → ℤ} {i : Fin n} {s : Bool}
    (hstd : toStdB n γ = Pi.single i (boolSign s)) :
    lvlB (idxB i s) - lvlB (idxB i (!s)) = 2 * ht γ := by
  rw [ht_of_toStdB_eq_single n hstd, lvlB_idxB, lvlB_idxB, boolSign_not]
  ring

private theorem idBelow_of_mem (ε : ℤ) {γ : Fin n → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅) (hε : 0 ≤ ε * ht γ)
    {x : spinGroup (quadOdd n K)} (hx : x ∈ oddRootGroup n K γ) :
    IdBelow (fun a => ε * lvlB a) (ε * ht γ) (spinMat (quadOdd n K) x) := by
  have hF := isCoord_oddFrame (n := n) (K := K)
  intro a b hab
  change ε * lvlB a - ε * lvlB b < ε * ht γ at hab
  rw [← mul_sub] at hab
  rcases exists_oddRootGroup_eq (K := K) hγ with ⟨i, j, hij, s, t, hstd, hX⟩ | ⟨i, s, hstd, hX⟩
  · rw [hX] at hx
    obtain ⟨c, rfl⟩ := hx
    have h1 : ¬(a = idxB i s ∧ b = idxB j (!t)) := by
      rintro ⟨rfl, rfl⟩
      rw [lvlB_sub_long₁ hstd] at hab
      exact lt_irrefl _ hab
    have h2 : ¬(a = idxB j t ∧ b = idxB i (!s)) := by
      rintro ⟨rfl, rfl⟩
      rw [lvlB_sub_long₂ hstd] at hab
      exact lt_irrefl _ hab
    rw [← ofAdd_toAdd c, hF.spinMat_longRoot hij s t, ite_eq_right h1, ite_eq_right h2,
      add_zero, sub_zero]
  · rw [hX] at hx
    obtain ⟨c, rfl⟩ := hx
    have h1 : ¬(a = zB ∧ b = idxB i (!s)) := by
      rintro ⟨rfl, rfl⟩
      rw [lvlB_sub_short₁ hstd] at hab
      exact lt_irrefl _ hab
    have h2 : ¬(a = idxB i s ∧ b = zB) := by
      rintro ⟨rfl, rfl⟩
      rw [lvlB_sub_short₂ hstd] at hab
      exact lt_irrefl _ hab
    have h3 : ¬(a = idxB i s ∧ b = idxB i (!s)) := by
      rintro ⟨rfl, rfl⟩
      rw [lvlB_sub_short₃ hstd] at hab
      linarith
    rw [← ofAdd_toAdd c, hF.spinMat_shortRoot i s, ite_eq_right h1, ite_eq_right h2,
      ite_eq_right h3, add_zero, sub_zero, sub_zero]

private theorem exists_pos (ε : ℤ) {γ : Fin n → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅) :
    ∃ a b : Fin n ⊕ Fin n ⊕ Unit, a ≠ b ∧ ε * lvlB a - ε * lvlB b ≤ ε * ht γ ∧
      (∀ δ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅, δ ≠ γ →
        ∀ x ∈ oddRootGroup n K δ, spinMat (quadOdd n K) x a b = 0) ∧
      ∀ x ∈ oddRootGroup n K γ, ∀ y ∈ oddRootGroup n K γ,
        spinMat (quadOdd n K) x a b = spinMat (quadOdd n K) y a b → x = y := by
  have hF := isCoord_oddFrame (n := n) (K := K)
  rcases exists_oddRootGroup_eq (K := K) hγ with ⟨i, j, hij, s, t, hstd, hX⟩ | ⟨i, s, hstd, hX⟩
  · have hab : idxB i s ≠ idxB j (!t) := idxB_ne hij s (!t)
    refine ⟨idxB i s, idxB j (!t), hab, by rw [← mul_sub, lvlB_sub_long₁ hstd], ?_, ?_⟩
    · intro δ hδ hne x hx
      rcases exists_oddRootGroup_eq (K := K) hδ with
        ⟨i', j', hij', s', t', hstd', hX'⟩ | ⟨i', s', hstd', hX'⟩
      · rw [hX'] at hx
        obtain ⟨c, rfl⟩ := hx
        have h1 : ¬(idxB i s = idxB i' s' ∧ idxB j (!t) = idxB j' (!t')) := by
          rintro ⟨e1, e2⟩
          obtain ⟨rfl, rfl⟩ := hF.idx_inj e1
          obtain ⟨rfl, e3⟩ := hF.idx_inj e2
          obtain rfl := Bool.not_inj e3
          exact hne (toStdB_injective n (hstd'.trans hstd.symm))
        have h2 : ¬(idxB i s = idxB j' t' ∧ idxB j (!t) = idxB i' (!s')) := by
          rintro ⟨e1, e2⟩
          obtain ⟨rfl, rfl⟩ := hF.idx_inj e1
          obtain ⟨rfl, e3⟩ := hF.idx_inj e2
          obtain rfl := Bool.not_inj e3
          exact hne (toStdB_injective n (hstd'.trans (hstd.trans (add_comm _ _)).symm))
        rw [← ofAdd_toAdd c, hF.spinMat_longRoot hij' s' t', Matrix.one_apply_ne hab,
          ite_eq_right h1, ite_eq_right h2, add_zero, sub_zero]
      · rw [hX'] at hx
        obtain ⟨c, rfl⟩ := hx
        have h1 : ¬(idxB i s = zB ∧ idxB j (!t) = idxB i' (!s')) :=
          fun h => idxB_ne_zB i s h.1
        have h2 : ¬(idxB i s = idxB i' s' ∧ idxB j (!t) = zB) :=
          fun h => idxB_ne_zB j (!t) h.2
        have h3 : ¬(idxB i s = idxB i' s' ∧ idxB j (!t) = idxB i' (!s')) := by
          rintro ⟨e1, e2⟩
          exact hij ((hF.idx_inj e1).1.trans (hF.idx_inj e2).1.symm)
        rw [← ofAdd_toAdd c, hF.spinMat_shortRoot i' s', Matrix.one_apply_ne hab,
          ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, add_zero, sub_zero, sub_zero]
    · intro x hx y hy hxy
      rw [hX] at hx hy
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      have h1 : idxB i s = idxB i s ∧ idxB j (!t) = idxB j (!t) := ⟨rfl, rfl⟩
      have h2 : ¬(idxB i s = idxB j t ∧ idxB j (!t) = idxB i (!s)) :=
        fun h => idxB_ne hij s t h.1
      rw [← ofAdd_toAdd c, ← ofAdd_toAdd d, hF.spinMat_longRoot hij s t,
        hF.spinMat_longRoot hij s t, ite_eq_left h1, ite_eq_left h1, ite_eq_right h2,
        ite_eq_right h2] at hxy
      have hcd : Multiplicative.toAdd c = Multiplicative.toAdd d := by simpa using hxy
      rw [Multiplicative.toAdd.injective hcd]
  · have hab : (zB : Fin n ⊕ Fin n ⊕ Unit) ≠ idxB i (!s) := (idxB_ne_zB i (!s)).symm
    refine ⟨zB, idxB i (!s), hab, by rw [← mul_sub, lvlB_sub_short₁ hstd], ?_, ?_⟩
    · intro δ hδ hne x hx
      rcases exists_oddRootGroup_eq (K := K) hδ with
        ⟨i', j', hij', s', t', hstd', hX'⟩ | ⟨i', s', hstd', hX'⟩
      · rw [hX'] at hx
        obtain ⟨c, rfl⟩ := hx
        have h1 : ¬((zB : Fin n ⊕ Fin n ⊕ Unit) = idxB i' s' ∧ idxB i (!s) = idxB j' (!t')) :=
          fun h => idxB_ne_zB i' s' h.1.symm
        have h2 : ¬((zB : Fin n ⊕ Fin n ⊕ Unit) = idxB j' t' ∧ idxB i (!s) = idxB i' (!s')) :=
          fun h => idxB_ne_zB j' t' h.1.symm
        rw [← ofAdd_toAdd c, hF.spinMat_longRoot hij' s' t', Matrix.one_apply_ne hab,
          ite_eq_right h1, ite_eq_right h2, add_zero, sub_zero]
      · rw [hX'] at hx
        obtain ⟨c, rfl⟩ := hx
        have h1 : ¬((zB : Fin n ⊕ Fin n ⊕ Unit) = zB ∧ idxB i (!s) = idxB i' (!s')) := by
          rintro ⟨-, e⟩
          obtain ⟨rfl, e3⟩ := hF.idx_inj e
          obtain rfl := Bool.not_inj e3
          exact hne (toStdB_injective n (hstd'.trans hstd.symm))
        have h2 : ¬((zB : Fin n ⊕ Fin n ⊕ Unit) = idxB i' s' ∧ idxB i (!s) = zB) :=
          fun h => idxB_ne_zB i' s' h.1.symm
        have h3 : ¬((zB : Fin n ⊕ Fin n ⊕ Unit) = idxB i' s' ∧ idxB i (!s) = idxB i' (!s')) :=
          fun h => idxB_ne_zB i' s' h.1.symm
        rw [← ofAdd_toAdd c, hF.spinMat_shortRoot i' s', Matrix.one_apply_ne hab,
          ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, add_zero, sub_zero, sub_zero]
    · intro x hx y hy hxy
      rw [hX] at hx hy
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      have h1 : (zB : Fin n ⊕ Fin n ⊕ Unit) = zB ∧ idxB i (!s) = idxB i (!s) := ⟨rfl, rfl⟩
      have h2 : ¬((zB : Fin n ⊕ Fin n ⊕ Unit) = idxB i s ∧ idxB i (!s) = zB) :=
        fun h => idxB_ne_zB i s h.1.symm
      have h3 : ¬((zB : Fin n ⊕ Fin n ⊕ Unit) = idxB i s ∧ idxB i (!s) = idxB i (!s)) :=
        fun h => idxB_ne_zB i s h.1.symm
      rw [← ofAdd_toAdd c, ← ofAdd_toAdd d, hF.spinMat_shortRoot i s, hF.spinMat_shortRoot i s,
        ite_eq_left h1, ite_eq_left h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h3,
        ite_eq_right h3] at hxy
      have hcd : Multiplicative.toAdd c = Multiplicative.toAdd d := by simpa using hxy
      rw [Multiplicative.toAdd.injective hcd]

private theorem prodInjectiveB (ε : ℤ) (L : List (Fin n → ℤ)) (hL : L.Nodup)
    (hroots : ∀ γ ∈ L, γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅)
    (hpos : ∀ γ ∈ L, 0 < ε * ht γ) (hsort : L.Pairwise fun γ δ => ε * ht γ ≤ ε * ht δ) :
    ProdInjectiveFor (oddRootGroup n K) L :=
  prodInjectiveFor_of_idBelow (fun a => ε * lvlB a) (spinMat (quadOdd n K))
    (oddRootGroup n K) (fun γ => ε * ht γ) L hL hpos
    (fun γ hγ _ hx => idBelow_of_mem ε (hroots γ hγ) (hpos γ hγ).le hx)
    (fun γ hγ => by
      obtain ⟨a, b, h1, h2, h3, h4⟩ := exists_pos (K := K) ε (hroots γ hγ)
      exact ⟨a, b, h1, h2, fun δ hδ hne x hx => h3 δ (hroots δ hδ) hne x hx, h4⟩)
    hsort

private theorem idBelow_of_mem_iSup (ε : ℤ) (P : Set (Fin n → ℤ))
    (hP : ∀ γ ∈ P, γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅ ∧ 0 < ε * ht γ)
    {x : spinGroup (quadOdd n K)} (hx : x ∈ ⨆ γ ∈ P, oddRootGroup n K γ) :
    IdBelow (fun a => ε * lvlB a) 1 (spinMat (quadOdd n K) x) := by
  rw [iSup_subtype'] at hx
  refine Subgroup.iSup_induction _ hx (C := fun x : spinGroup (quadOdd n K) =>
    IdBelow (fun a => ε * lvlB a) 1 (spinMat (quadOdd n K) x)) (fun γ y hy => ?_) ?_
    fun y z hy hz => ?_
  · exact (idBelow_of_mem ε (hP γ.1 γ.2).1 (hP γ.1 γ.2).2.le hy).mono
      (by have := (hP γ.1 γ.2).2; omega)
  · rw [map_one]
    exact idBelow_one _ 1
  · rw [map_mul]
    exact idBelow_mul _ one_pos hy hz

private noncomputable abbrev omegaB : CliffordAlgebra (quadOdd n K) :=
  (oddFrame n K).spinor fun _ => true

private theorem posPart_le_stab :
    (⨆ γ ∈ {γ | γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅ ∧ 0 < ht γ},
      oddRootGroup n K γ) ≤ stabSubgroup (quadOdd n K) (omegaB (n := n) (K := K)) := by
  refine iSup₂_le fun γ hγ => ?_
  have h0 : 0 < ht γ := hγ.2
  rcases exists_oddRootGroup_eq (K := K) hγ.1 with ⟨i, j, hij, s, t, hstd, hX⟩ | ⟨i, s, hstd, hX⟩
  · rw [hX]
    rintro _ ⟨c, rfl⟩
    rw [mem_stabSubgroup, ← ofAdd_toAdd c]
    refine (oddFrame n K).coe_longRoot_mul_spinor _ hij ?_ _
    show s = true ∨ t = true
    by_contra h
    rw [not_or, Bool.not_eq_true, Bool.not_eq_true] at h
    have hht := ht_of_toStdB_eq_add n hstd
    rw [h.1, h.2, boolSign_false] at hht
    have hi := i.isLt
    have hj := j.isLt
    omega
  · rw [hX]
    rintro _ ⟨c, rfl⟩
    rw [mem_stabSubgroup, ← ofAdd_toAdd c]
    refine (oddFrame n K).coe_shortRoot_mul_spinor _ ?_ _
    show s = true
    by_contra h
    rw [Bool.not_eq_true] at h
    have hht := ht_of_toStdB_eq_single n hstd
    rw [h, boolSign_false] at hht
    have hi := i.isLt
    omega

private theorem eq_one_of_mem_posPart (h2 : (2 : K) ≠ 0) {x : spinGroup (quadOdd n K)}
    (hx : x ∈ ⨆ γ ∈ {γ | γ ∈ RootSystem.roots (isFiniteType_cartanB n) ∅ ∧ 0 < ht γ},
      oddRootGroup n K γ)
    (h : spinMat (quadOdd n K) x = 1) : x = 1 :=
  eq_one_of_mul_eq_self _
    (eq_one_or_eq_neg_one_of_spinAction_eq_one_odd n K h2 x
      (spinAction_eq_one_of_spinMat_eq_one h))
    ((oddFrame n K).spinor_ne_zero _) (posPart_le_stab hx)

private def corootB (k m : Fin n) (r : Bool) : ℤ :=
  if h : k.val + 1 < n then longCoroot k ⟨k.val + 1, h⟩ true false m r
  else shortCoroot k true m r

private theorem spinAction_torusB_single (k : Fin n) (τ : Kˣ) (m : Fin n) (r : Bool) :
    spinAction (quadOdd n K) (torusB K k τ) (Pi.single (idxB m r) 1) =
      ((τ ^ corootB k m r : Kˣ) : K) • Pi.single (idxB m r) 1 := by
  rw [← (isCoord_oddFrame (n := n) (K := K)).vec_eq]
  by_cases hk : k.val + 1 < n
  · rw [torusB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp)), corootB,
      dite_eq_left hk]
    exact HypFrame.spinAction_longTorus_vec _ _ _ _ τ m r
  · rw [torusB_of_not_lt K hk, corootB, dite_eq_right hk]
    exact OddFrame.spinAction_shortTorus_vec _ _ _ τ m r

private theorem spinAction_torusB_z (k : Fin n) (τ : Kˣ) :
    spinAction (quadOdd n K) (torusB K k τ) (Pi.single zB 1) = (1 : K) • Pi.single zB 1 := by
  rw [← (isCoord_oddFrame (n := n) (K := K)).z_eq, one_smul]
  by_cases hk : k.val + 1 < n
  · rw [torusB_of_lt K hk (j := ⟨k.val + 1, hk⟩) rfl (Fin.ne_of_val_ne (by simp)),
      HypFrame.spinAction_longTorus]
    simp only [OddFrame.polar_z_vec, zero_smul, smul_zero, add_zero]
  · rw [torusB_of_not_lt K hk]
    exact OddFrame.spinAction_shortTorus_z _ _ _ τ

private theorem isDiag_torusB (k : Fin n) (τ : Kˣ) :
    (spinMat (quadOdd n K) (torusB K k τ)).IsDiag := by
  refine isDiag_spinMat fun b => ?_
  rcases idxB_surj b with ⟨m, r, rfl⟩ | rfl
  · exact ⟨_, spinAction_torusB_single k τ m r⟩
  · exact ⟨_, spinAction_torusB_z k τ⟩

private theorem isDiag_of_mem_iSup {x : spinGroup (quadOdd n K)}
    (hx : x ∈ ⨆ k, (torusB K k).range) : (spinMat (quadOdd n K) x).IsDiag := by
  refine Subgroup.iSup_induction _ hx (C := fun x : spinGroup (quadOdd n K) =>
    (spinMat (quadOdd n K) x).IsDiag) (fun k y hy => ?_) ?_ fun y z hy hz => ?_
  · obtain ⟨τ, rfl⟩ := hy
    exact isDiag_torusB k τ
  · rw [map_one]
    exact Matrix.isDiag_one
  · rw [map_mul]
    exact isDiag_mul hy hz

private theorem sum_longCoroot (k i j : Fin n) (t : Bool) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), longCoroot i j true t m true =
      (if i.val ≤ k.val then 1 else 0) + (if j.val ≤ k.val then boolSign t else 0) := by
  simp only [longCoroot, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases t <;> simp

private theorem sum_shortCoroot (k i : Fin n) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), shortCoroot i true m true =
      if i.val ≤ k.val then 2 else 0 := by
  simp only [shortCoroot]
  rw [Finset.sum_ite_eq']
  simp

private theorem sum_corootB {k : Fin n} (hk : k.val + 1 < n) (j : Fin n) :
    ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), corootB j m true =
      if j = k then 1 else 0 := by
  by_cases hj : j.val + 1 < n
  · simp only [corootB, dite_eq_left hj]
    rw [sum_longCoroot, boolSign_false]
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
      rw [ite_eq_right hjk]
      simp only
      split_ifs <;> omega
  · simp only [corootB, dite_eq_right hj]
    rw [sum_shortCoroot, ite_eq_right (fun h => by omega : ¬(j.val ≤ k.val)),
      ite_eq_right (fun h => by rw [h] at hj; omega : ¬j = k)]

private theorem prod_diag_torusB (k j : Fin n) (τ : Kˣ) :
    ∏ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      spinMat (quadOdd n K) (torusB K j τ) (idxB m true) (idxB m true) =
        ((τ ^ ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
          corootB j m true : Kˣ) : K) := by
  rw [← prod_zpow_eq_zpow_sum, Units.coe_prod]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [spinMat_apply_of_eq_smul (spinAction_torusB_single j τ m true), ite_eq_left rfl]

private theorem coe_torusB_mul_spinor_self {k : Fin n} (hk : ¬k.val + 1 < n) (τ : Kˣ) :
    (torusB K k τ : CliffordAlgebra (quadOdd n K)) * omegaB (n := n) (K := K) =
      (τ : K) • omegaB (n := n) (K := K) := by
  rw [torusB_of_not_lt K hk]
  exact (oddFrame n K).coe_shortTorus_mul_spinor (fun _ => true) (i := k) (s := true) rfl τ

private theorem coe_torusB_mul_spinor_of_lt {j : Fin n} (hj : j.val + 1 < n) (τ : Kˣ) :
    (torusB K j τ : CliffordAlgebra (quadOdd n K)) * omegaB (n := n) (K := K) =
      omegaB (n := n) (K := K) := by
  rw [torusB_of_lt K hj (j := ⟨j.val + 1, hj⟩) rfl (Fin.ne_of_val_ne (by simp))]
  exact (oddFrame n K).coe_longTorus_mul_spinor_of_ne (fun _ => true) (i := j)
    (j := ⟨j.val + 1, hj⟩) (s := true) (t := false) _ (Or.inl ⟨rfl, by decide⟩) τ

variable (n K)

theorem oddDatum_prodInjective_pos :
    ∀ L : List (Fin (oddDatum n K).rank → ℤ), L.Nodup →
      (∀ γ, γ ∈ L ↔ γ ∈ (oddDatum n K).roots ∧ 0 < ht γ ∧
        ∀ δ ∈ (oddDatum n K).roots, γ ≠ 2 • δ) →
      L.Pairwise (fun γ δ => ht γ ≤ ht δ) → ProdInjectiveFor (oddDatum n K).rootGroup L := by
  intro L hL hmem hsort
  refine prodInjectiveB (n := n) (K := K) 1 L hL (fun γ hγ => ((hmem γ).1 hγ).1) (fun γ hγ => ?_) ?_
  · have : 0 < ht (ι := Fin n) γ := ((hmem γ).1 hγ).2.1
    omega
  · refine hsort.imp fun {γ δ} h => ?_
    have h' : ht (ι := Fin n) γ ≤ ht (ι := Fin n) δ := h
    omega

theorem oddDatum_prodInjective_neg :
    ∀ L : List (Fin (oddDatum n K).rank → ℤ), L.Nodup →
      (∀ γ, γ ∈ L ↔ γ ∈ (oddDatum n K).roots ∧ ht γ < 0 ∧
        ∀ δ ∈ (oddDatum n K).roots, γ ≠ 2 • δ) →
      L.Pairwise (fun γ δ => ht δ ≤ ht γ) → ProdInjectiveFor (oddDatum n K).rootGroup L := by
  intro L hL hmem hsort
  refine prodInjectiveB (n := n) (K := K) (-1) L hL (fun γ hγ => ((hmem γ).1 hγ).1) (fun γ hγ => ?_) ?_
  · have : ht (ι := Fin n) γ < 0 := ((hmem γ).1 hγ).2.1
    omega
  · refine hsort.imp fun {γ δ} h => ?_
    have h' : ht (ι := Fin n) δ ≤ ht (ι := Fin n) γ := h
    omega

theorem oddDatum_posPart_inf_negPart (h2 : (2 : K) ≠ 0) :
    (⨆ γ ∈ {γ | γ ∈ (oddDatum n K).roots ∧ 0 < ht γ}, (oddDatum n K).rootGroup γ) ⊓
      (⨆ γ ∈ {γ | γ ∈ (oddDatum n K).roots ∧ ht γ < 0}, (oddDatum n K).rootGroup γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxp, hxn⟩
  rw [Subgroup.mem_bot]
  have h1 := idBelow_of_mem_iSup (n := n) (K := K) 1 _
    (fun γ hγ => ⟨hγ.1, by have : 0 < ht (ι := Fin n) γ := hγ.2; omega⟩) hxp
  have h2' := idBelow_of_mem_iSup (n := n) (K := K) (-1) _
    (fun γ hγ => ⟨hγ.1, by have : ht (ι := Fin n) γ < 0 := hγ.2; omega⟩) hxn
  exact eq_one_of_mem_posPart (n := n) h2 hxp (eq_one_of_idBelow_one_of_idBelow_neg_one _ h1 h2')

theorem oddDatum_torus_iSupIndep :
    iSupIndep (fun k : Fin (oddDatum n K).rank => (torusB K k).range) := by
  show iSupIndep fun k : Fin n => (torusB K k).range
  intro k
  rw [Subgroup.disjoint_def]
  intro x hxk hx
  obtain ⟨τ, rfl⟩ := hxk
  suffices hτ : τ = 1 by rw [hτ, map_one]
  by_cases hk : k.val + 1 < n
  ·
    have key : (spinMat (quadOdd n K) (torusB K k τ)).IsDiag ∧
        ∏ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
          spinMat (quadOdd n K) (torusB K k τ) (idxB m true) (idxB m true) = 1 := by
      rw [iSup_subtype'] at hx
      refine Subgroup.iSup_induction _ hx (C := fun y : spinGroup (quadOdd n K) =>
        (spinMat (quadOdd n K) y).IsDiag ∧
          ∏ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
            spinMat (quadOdd n K) y (idxB m true) (idxB m true) = 1)
        (fun j y hy => ?_) ?_ fun y z hy hz => ?_
      · obtain ⟨σ, rfl⟩ := hy
        refine ⟨isDiag_torusB j.1 σ, ?_⟩
        rw [prod_diag_torusB, sum_corootB hk, ite_eq_right j.2, zpow_zero, Units.val_one]
      · rw [map_one]
        exact ⟨Matrix.isDiag_one, Finset.prod_eq_one fun m _ => Matrix.one_apply_eq _⟩
      · rw [map_mul]
        refine ⟨isDiag_mul hy.1 hz.1, ?_⟩
        rw [prod_diag_mul_of_isDiag _ (fun m => idxB m true) hy.1 hz.1, hy.2, hz.2, one_mul]
    have h := key.2
    rw [prod_diag_torusB, sum_corootB hk, ite_eq_left rfl, zpow_one] at h
    exact Units.val_eq_one.mp h
  ·
    have hfix : (torusB K k τ : CliffordAlgebra (quadOdd n K)) * omegaB (n := n) (K := K) =
        omegaB (n := n) (K := K) := by
      have hle : (⨆ (j : Fin n) (_ : j ≠ k), (torusB K j).range) ≤
          stabSubgroup (quadOdd n K) (omegaB (n := n) (K := K)) := by
        refine iSup₂_le fun j hj => ?_
        rintro _ ⟨σ, rfl⟩
        have hj' : j.val + 1 < n := by
          have := Fin.val_ne_of_ne hj
          omega
        exact coe_torusB_mul_spinor_of_lt hj' σ
      exact hle hx
    rw [coe_torusB_mul_spinor_self hk] at hfix
    have h0 : ((τ : K) - 1) • omegaB (n := n) (K := K) = 0 := by
      rw [sub_smul, hfix, one_smul, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact Units.ext (sub_eq_zero.mp h)
    · exact absurd h ((oddFrame n K).spinor_ne_zero _)

theorem oddDatum_torus_inf_posPart (h2 : (2 : K) ≠ 0) :
    (⨆ i : Fin (oddDatum n K).rank, (torusB K i).range) ⊓
      (⨆ γ ∈ {γ | γ ∈ (oddDatum n K).roots ∧ 0 < ht γ}, (oddDatum n K).rootGroup γ) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxt, hxp⟩
  rw [Subgroup.mem_bot]
  refine eq_one_of_mem_posPart (n := n) h2 hxp (eq_one_of_isDiag_of_idBelow
    (fun a => 1 * lvlB a) (isDiag_of_mem_iSup (n := n) hxt) ?_)
  exact idBelow_of_mem_iSup (n := n) (K := K) 1 _
    (fun γ hγ => ⟨hγ.1, by have : 0 < ht (ι := Fin n) γ := hγ.2; omega⟩) hxp

end CFSG.LieType.Universal.Spin
