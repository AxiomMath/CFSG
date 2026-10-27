module

public import CFSG.GH74.KGroups.PermCheck
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.GH74.KGroups

open CFSG.Certificates CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def centTrivCheck (L : List (Equiv.Perm (Fin n))) (a b : Equiv.Perm (Fin n)) : Bool :=
  L.all fun σ => !(decide (σ * a = a * σ) && decide (σ * b = b * σ)) || decide (σ = 1)

@[expose] def normCheck (QP : RawSchreierDatum n) (gens : List (Equiv.Perm (Fin n)))
    (a b : Equiv.Perm (Fin n)) : Bool :=
  gens.all fun σ => QP.sift (σ * a * σ⁻¹) 0 && QP.sift (σ * b * σ⁻¹) 0

@[expose] def pairCountB (QP : RawSchreierDatum n) (oa ob : ℕ) (ws : List (List Bool × ℕ)) : ℕ :=
  ((((elemsT QP).filter (fun g => orderIs g oa)) ×ˢ
      ((elemsT QP).filter (fun g => orderIs g ob))).filter
    (fun q => pairInvB ws q.1 q.2)).length

theorem closure_pair_top {M : Type*} [Group M] {K : Subgroup M} {x y : M}
    (hK : K = Subgroup.closure {x, y}) (hx : x ∈ K) (hy : y ∈ K) :
    Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set K) = ⊤ := by
  subst hK
  refine Eq.trans ?_ (Subgroup.closure_closure_coe_preimage (k := {x, y}))
  congr 1
  ext ⟨g, hg⟩
  simp [Subtype.ext_iff]

theorem pairInv_coe_iff {M : Type*} [Group M] (H : Subgroup M) (ws : List (List Bool × ℕ))
    (x y : H) : PairInv ws x y ↔ PairInv ws (x : M) (y : M) := by
  simp only [PairInv]
  refine forall_congr' fun wk => forall_congr' fun _ => ?_
  have h := map_evalW H.subtype x y wk.1
  have h' : ((evalW x y wk.1 : H) : M) = evalW (x : M) (y : M) wk.1 := h
  rw [← h', Subgroup.orderOf_coe]

theorem autModel_exists (QP QA : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (hQA : ValidSchreier QA) (gA gB : Equiv.Perm (Fin n))
    (hP : QP.originalSubgroup = Subgroup.closure {gA, gB}) (oa ob : ℕ) (hoa : 0 < oa)
    (hob : 0 < ob) (ws : List (List Bool × ℕ)) (hws : ∀ wk ∈ ws, 0 < wk.2)
    (hA : orderOf gA = oa) (hB : orderOf gB = ob) (hI : PairInv ws gA gB)
    (hcount : pairCountB QP oa ob ws = QA.orderCertificate)
    (hnorm : normCheck QP QA.original.toList gA gB = true)
    (hcent : centTrivCheck (elemsT QA) gA gB = true)
    {K : Type*} [Group K] (e : K ≃* QP.originalSubgroup) :
    ∃ M : AutModel K (Equiv.Perm (Fin n)), M.P = QP.originalSubgroup ∧
      M.A = QA.originalSubgroup := by
  classical
  set P := QP.originalSubgroup with hPdef
  set A := QA.originalSubgroup with hAdef
  have hgA : gA ∈ P := by
    rw [hP]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have hgB : gB ∈ P := by
    rw [hP]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hnormA : A ≤ Subgroup.normalizer (P : Set (Equiv.Perm (Fin n))) := by
    rw [hAdef, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
    intro σ hσ
    have hσ' : σ ∈ QA.original.toList := hσ
    have h1 := List.all_eq_true.1 hnorm σ hσ'
    simp only [Bool.and_eq_true] at h1
    have ha : σ * gA * σ⁻¹ ∈ P := (mem_iff_sift QP hQP _).2 h1.1
    have hb : σ * gB * σ⁻¹ ∈ P := (mem_iff_sift QP hQP _).2 h1.2
    apply mem_normalizer_of_conj_mem
    intro x hx
    have hle : Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) ≤
        P.comap (MulAut.conj σ).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy
      · rw [hy]; exact ha
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hb
    have hx' : x ∈ Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) := hP ▸ hx
    exact hle hx'
  have hcentA : ∀ σ ∈ A, (∀ x ∈ P, σ * x = x * σ) → σ = 1 := by
    intro σ hσ hc
    by_contra hne
    have h1 := List.all_eq_true.1 hcent σ ((mem_elemsT QA hQA σ).2 hσ)
    have hA' : σ * gA = gA * σ := hc gA hgA
    have hB' : σ * gB = gB * σ := hc gB hgB
    simp [hA', hB', hne] at h1
  have hcard : Nat.card (MulAut P) ≤ Nat.card A := by
    have hgen := closure_pair_top hP hgA hgB
    let I : P → P → Prop := fun x y => orderOf x = oa ∧ orderOf y = ob ∧ PairInv ws x y
    have hIab : I ⟨gA, hgA⟩ ⟨gB, hgB⟩ := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← Subgroup.orderOf_coe]; exact hA
      · rw [← Subgroup.orderOf_coe]; exact hB
      · exact (pairInv_coe_iff P ws _ _).2 hI
    have hIaut : ∀ φ : MulAut P, I ⟨gA, hgA⟩ ⟨gB, hgB⟩ →
        I (φ ⟨gA, hgA⟩) (φ ⟨gB, hgB⟩) := by
      rintro φ ⟨h1, h2, h3⟩
      exact ⟨by rw [MulEquiv.orderOf_eq]; exact h1, by rw [MulEquiv.orderOf_eq]; exact h2,
        pairInv_map φ ws h3⟩
    have h1 := card_mulAut_le _ _ hgen I hIaut hIab
    have h2 := card_pairs QP hQP oa ob hoa hob ws hws
    have h3 : Nat.card {p : P × P // I p.1 p.2} = pairCountB QP oa ob ws := h2
    rw [h3, hcount] at h1
    rw [hAdef, card_group QA hQA]
    exact h1
  have : Finite P := inferInstance
  have : Finite A := inferInstance
  obtain ⟨Φ', hΦ'⟩ := exists_mulEquiv_of_squeeze P A hnormA hcentA hcard
  exact ⟨AutModel.ofRealization P A e Φ' hΦ', rfl, rfl⟩

theorem bif_imp (a b : Bool) : (bif a then b else true) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

@[expose] def inner3check (LA : List (Equiv.Perm (Fin n))) (QP : RawSchreierDatum n) : Bool :=
  LA.all fun g => bif decide (g ^ 3 = 1) then QP.sift g 0 else true

theorem inner3check_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (h : inner3check (elemsT QA) QP = true) :
    ∀ g ∈ QA.originalSubgroup, g ^ 3 = 1 → g ∈ QP.originalSubgroup := by
  intro g hg hg3
  have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h g ((mem_elemsT QA hQA g).2 hg))
    (by simp [hg3])
  exact (mem_iff_sift QP hQP g).2 h1

@[expose] def e9at (C : List (Equiv.Perm (Fin n))) : Bool :=
  C.all fun X => C.all fun Y =>
    bif decide (X ≠ 1) && decide (X ^ 3 = 1) && decide (Y ^ 3 = 1) && decide (X * Y = Y * X) then
      decide (Y = 1) || decide (Y = X) || decide (Y = X ^ 2) else true

@[expose] def e9free (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.all fun τ => bif decide (τ ^ 2 = 1) && decide (τ ≠ 1) then
    e9at (L.filter (fun g => decide (g * τ = τ * g))) else true

theorem e9free_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : e9free (elemsT Q) = true) :
    ∀ τ ∈ Q.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 → ∀ X ∈ Q.originalSubgroup, X ≠ 1 →
      ∀ Y ∈ Q.originalSubgroup, X ^ 3 = 1 → Y ^ 3 = 1 → X * Y = Y * X → X * τ = τ * X →
      Y * τ = τ * Y → Y = 1 ∨ Y = X ∨ Y = X ^ 2 := by
  intro τ hτ hτ2 hτ1 X hX hX1 Y hY hX3 hY3 hXY hXτ hYτ
  have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h τ ((mem_elemsT Q hQ τ).2 hτ))
    (by simp [hτ2, hτ1])
  have h2 := List.all_eq_true.1 h1 X (by
    rw [List.mem_filter]; exact ⟨(mem_elemsT Q hQ X).2 hX, by simpa using hXτ⟩)
  have h3 := List.all_eq_true.1 h2 Y (by
    rw [List.mem_filter]; exact ⟨(mem_elemsT Q hQ Y).2 hY, by simpa using hYτ⟩)
  have h4 := (bif_imp _ _).1 h3 (by simp [hX1, hX3, hY3, hXY])
  simpa [or_assoc] using h4

@[expose] def e9all (L : List (Equiv.Perm (Fin n))) : Bool :=
  (L.filter fun g => decide (g ≠ 1 ∧ g ^ 3 = 1)).all fun X =>
    (L.filter fun g => decide (g ^ 3 = 1 ∧ g * X = X * g)).all fun Y =>
      decide (Y = 1) || decide (Y = X) || decide (Y = X ^ 2)

theorem e9all_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : e9all (elemsT Q) = true) :
    ∀ X ∈ Q.originalSubgroup, X ≠ 1 → ∀ Y ∈ Q.originalSubgroup, X ^ 3 = 1 → Y ^ 3 = 1 →
      X * Y = Y * X → Y ∈ ([1, X, X ^ 2] : List (Equiv.Perm (Fin n))) := by
  intro X hX hX1 Y hY hX3 hY3 hXY
  have h1 := List.all_eq_true.1 h X (by
    rw [List.mem_filter]; exact ⟨(mem_elemsT Q hQ X).2 hX, by simpa using ⟨hX1, hX3⟩⟩)
  have h2 := List.all_eq_true.1 h1 Y (by
    rw [List.mem_filter]; exact ⟨(mem_elemsT Q hQ Y).2 hY, by simpa using ⟨hY3, hXY.symm⟩⟩)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rcases h2 with (h2 | h2) | h2
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

@[expose] def e27at (X : Equiv.Perm (Fin n)) (C : List (Equiv.Perm (Fin n))) : Bool :=
  C.all fun Y => C.all fun Z =>
    decide (Y * Z ≠ Z * Y) || decide (Y ∈ ([1, X, X ^ 2] : List (Equiv.Perm (Fin n)))) ||
      decide (Z ∈ pow3list X Y)

@[expose] def e27free (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.all fun X => bif decide (X ^ 3 = 1) && decide (X ≠ 1) then
    e27at X (L.filter (fun g => decide (g ^ 3 = 1 ∧ g * X = X * g))) else true

theorem e27free_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : e27free (elemsT Q) = true) :
    ∀ X ∈ Q.originalSubgroup, ∀ Y ∈ Q.originalSubgroup, ∀ Z ∈ Q.originalSubgroup,
      X ^ 3 = 1 → Y ^ 3 = 1 → Z ^ 3 = 1 → X * Y = Y * X → X * Z = Z * X → Y * Z = Z * Y →
      X = 1 ∨ Y ∈ ([1, X, X ^ 2] : List (Equiv.Perm (Fin n))) ∨ Z ∈ pow3list X Y := by
  intro X hX Y hY Z hZ hX3 hY3 hZ3 hXY hXZ hYZ
  by_cases hX1 : X = 1
  · exact Or.inl hX1
  · have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h X ((mem_elemsT Q hQ X).2 hX))
      (by simp [hX3, hX1])
    have h2 := List.all_eq_true.1 h1 Y (by
      rw [List.mem_filter]
      exact ⟨(mem_elemsT Q hQ Y).2 hY, by simpa using ⟨hY3, hXY.symm⟩⟩)
    have h3 := List.all_eq_true.1 h2 Z (by
      rw [List.mem_filter]
      exact ⟨(mem_elemsT Q hQ Z).2 hZ, by simpa using ⟨hZ3, hXZ.symm⟩⟩)
    simp only [Bool.or_eq_true, decide_eq_true_eq, ne_eq] at h3
    rcases h3 with (h3 | h3) | h3
    · exact absurd hYZ h3
    · exact Or.inr (Or.inl h3)
    · exact Or.inr (Or.inr h3)

@[expose] def cent3at (x : Equiv.Perm (Fin n)) (C : List (Equiv.Perm (Fin n))) : Bool :=
  C.all fun y =>
    bif decide (y ^ 3 = 1) && !decide (y ∈ ([1, x, x ^ 2] : List (Equiv.Perm (Fin n)))) then
      C.all fun k => bif decide (k * y = y * k) then decide (k ∈ pow3list x y) else true
    else true

@[expose] def cent3check (L : List (Equiv.Perm (Fin n))) : Bool :=
  L.all fun x => bif decide (x ^ 3 = 1) && decide (x ≠ 1) then
    cent3at x (L.filter (fun g => decide (g * x = x * g))) else true

theorem cent3check_sound (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    (h : cent3check (elemsT Q) = true) :
    ∀ x ∈ Q.originalSubgroup, ∀ y ∈ Q.originalSubgroup, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x →
      x ≠ 1 → y ∉ ([1, x, x ^ 2] : List (Equiv.Perm (Fin n))) →
      ∀ k ∈ Q.originalSubgroup, k * x = x * k → k * y = y * k → k ∈ pow3list x y := by
  intro x hx y hy hx3 hy3 hxy hx1 hyn k hk hkx hky
  have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h x ((mem_elemsT Q hQ x).2 hx))
    (by simp [hx3, hx1])
  have h2 := (bif_imp _ _).1 (List.all_eq_true.1 h1 y (by
      rw [List.mem_filter]; exact ⟨(mem_elemsT Q hQ y).2 hy, by simpa using hxy.symm⟩))
    (by simp [hy3, hyn])
  have h3 := (bif_imp _ _).1 (List.all_eq_true.1 h2 k (by
      rw [List.mem_filter]; exact ⟨(mem_elemsT Q hQ k).2 hk, by simpa using hkx⟩))
    (by simpa using hky)
  simpa using h3

@[expose] def solvCheck (LA LP : List (Equiv.Perm (Fin n))) : Bool :=
  LA.all fun τ => bif decide (τ ^ 2 = 1) && decide (τ ≠ 1) then
    decide (((LP.filter (fun g => decide (g * τ = τ * g))).length).primeFactors.card ≤ 2)
    else true

theorem solvCheck_sound (QA QP : RawSchreierDatum n) (hQA : ValidSchreier QA)
    (hQP : ValidSchreier QP) (h : solvCheck (elemsT QA) (elemsT QP) = true) :
    ∀ τ ∈ QA.originalSubgroup, τ ^ 2 = 1 → τ ≠ 1 →
      Group.IsSolvable ↥(QP.originalSubgroup ⊓
        Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin n)))) := by
  intro τ hτ hτ2 hτ1
  have h1 := (bif_imp _ _).1 (List.all_eq_true.1 h τ ((mem_elemsT QA hQA τ).2 hτ))
    (by simp [hτ2, hτ1])
  have : Finite ↥(QP.originalSubgroup ⊓
        Subgroup.centralizer ({τ} : Set (Equiv.Perm (Fin n)))) := inferInstance
  apply isSolvable_of_two_primes
  rw [card_inf_centralizer QP hQP τ]
  simpa using h1

end CFSG.GH74.KGroups
