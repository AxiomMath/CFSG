module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4Eta
public import CFSG.RankThree.GF2n.Smith81.Orth28Omega

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions QuadraticMap

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private lemma funCongrLeft_single {ι : Type*} [DecidableEq ι] (π : Equiv.Perm ι) (j : ι) :
    LinearEquiv.funCongrLeft K K π (Pi.single j (1:K) : ι → K) =
      Pi.single (π.symm j) 1 := by
  ext i
  rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Pi.single_apply,
    Pi.single_apply]
  by_cases h : π i = j
  · have h' : i = π.symm j := by rw [← h, Equiv.symm_apply_apply]
    rw [if_pos h, if_pos h']
  · have h' : i ≠ π.symm j := fun hh => h (by rw [hh, Equiv.apply_symm_apply])
    rw [if_neg h, if_neg h']

omit [Finite K] [CharP K 2] in
private theorem funCongrLeft_mul (π σ : Equiv.Perm (Fin 4 ⊕ Fin 4)) :
    LinearEquiv.funCongrLeft K K π * LinearEquiv.funCongrLeft K K σ =
      LinearEquiv.funCongrLeft K K (σ * π) := by
  ext y i
  rfl

omit [Finite K] [CharP K 2] in
private theorem commSpace_funCongrLeft_of_involution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm ι) (hπ : π * π = 1) :
    commSpace (LinearEquiv.funCongrLeft K K π) =
      Submodule.span K (Set.range fun j => Pi.single (π j) (1:K) - Pi.single j 1) := by
  have hπ' : π.symm = π := inv_eq_of_mul_eq_one_right hπ
  have hsingle : ∀ j : ι, LinearEquiv.funCongrLeft K K π (Pi.single j (1:K) : ι → K) =
      Pi.single (π j) 1 := by
    intro j
    rw [funCongrLeft_single, hπ']
  rw [commSpace, LinearMap.range_eq_map, ← Module.Basis.span_eq (Pi.basisFun K ι),
    Submodule.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j
  simp [Function.comp_apply, hsingle, Pi.basisFun_apply]

private def cidx : Fin 4 ⊕ Fin 4 → Fin 4
  | Sum.inl i => i
  | Sum.inr i => i

omit [Finite K] [CharP K 2] in
private theorem quadPlus_funCongrLeft_of_pair {π : Equiv.Perm (Fin 4 ⊕ Fin 4)}
    (hπ : ∀ i : Fin 4, π (Sum.inr i) = (π (Sum.inl i)).swap)
    (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K (LinearEquiv.funCongrLeft K K π v) = quadPlus 4 K v := by
  let σ : Fin 4 → Fin 4 := fun i => cidx (π (Sum.inl i))
  have hσinj : Function.Injective σ := by
    intro i j hij
    by_contra hne
    have hπne : π (Sum.inl i) ≠ π (Sum.inl j) :=
      fun h => hne (Sum.inl.inj (π.injective h))
    rcases hi : π (Sum.inl i) with a | a <;> rcases hj : π (Sum.inl j) with b | b
    · have hab : a = b := by simpa [σ, cidx, hi, hj] using hij
      exact hπne (by rw [hi, hj, hab])
    · have hab : a = b := by simpa [σ, cidx, hi, hj] using hij
      have h1 : π (Sum.inr j) = Sum.inl a := by rw [hπ j, hj, hab]; rfl
      have h2 : π (Sum.inl i) = π (Sum.inr j) := by rw [hi, h1]
      exact Sum.inl_ne_inr (π.injective h2)
    · have hab : a = b := by simpa [σ, cidx, hi, hj] using hij
      have h1 : π (Sum.inr i) = Sum.inl b := by rw [hπ i, hi, hab]; rfl
      have h2 : π (Sum.inr i) = π (Sum.inl j) := by rw [h1, hj]
      exact Sum.inr_ne_inl (π.injective h2)
    · have hab : a = b := by simpa [σ, cidx, hi, hj] using hij
      exact hπne (by rw [hi, hj, hab])
  have hσ : Function.Bijective σ :=
    ⟨hσinj, Finite.injective_iff_surjective.mp hσinj⟩
  let eσ : Fin 4 ≃ Fin 4 := Equiv.ofBijective σ hσ
  have hterm : ∀ i : Fin 4, v (π (Sum.inl i)) * v (π (Sum.inr i)) =
      v (Sum.inl (σ i)) * v (Sum.inr (σ i)) := by
    intro i
    rcases hi : π (Sum.inl i) with a | a
    · have h2 : π (Sum.inr i) = Sum.inr a := by rw [hπ i, hi]; rfl
      have hσa : σ i = a := by simp [σ, cidx, hi]
      simp only [h2, hσa]
    · have h2 : π (Sum.inr i) = Sum.inl a := by rw [hπ i, hi]; rfl
      have hσa : σ i = a := by simp [σ, cidx, hi]
      simp only [h2, hσa]
      rw [mul_comm]
  calc quadPlus 4 K (LinearEquiv.funCongrLeft K K π v)
      = ∑ i, v (π (Sum.inl i)) * v (π (Sum.inr i)) := by
        rw [quadPlus_apply]
        simp only [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
    _ = ∑ i, v (Sum.inl (σ i)) * v (Sum.inr (σ i)) := by
        exact Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ i, v (Sum.inl i) * v (Sum.inr i) :=
        Equiv.sum_comp eσ (fun k : Fin 4 => v (Sum.inl k) * v (Sum.inr k))
    _ = quadPlus 4 K v := by rw [quadPlus_apply]

omit [Finite K] [CharP K 2] in
private theorem linearIndependent_single_sub_single {r : ℕ} {ι : Type*} [DecidableEq ι]
    (a b : Fin r → ι) (hinj : Function.Injective a) (hne : ∀ i j, a i ≠ b j) :
    LinearIndependent K (fun i => (Pi.single (a i) (1:K) - Pi.single (b i) 1 : ι → K)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hsingle : ∀ j : Fin r, j ≠ i →
      (c j • (Pi.single (a j) (1:K) - Pi.single (b j) 1 : ι → K)) (a i) = 0 := by
    intro j hji
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul]
    rw [if_neg (fun h : a i = a j => hji (hinj h).symm), if_neg (hne i j)]
    simp
  have h := congrArg (fun v : ι → K => v (a i)) hc
  simp only [Finset.sum_apply, Pi.zero_apply] at h
  rw [Finset.sum_eq_single i (fun j _ hji => hsingle j hji)
    (fun hi => absurd (Finset.mem_univ i) hi)] at h
  simpa [Pi.single_apply, hne i i] using h

omit [Finite K] in
private theorem quadPlus_eq_zero_of_mem_span_range {n : ℕ} (v : Fin n → Fin 4 ⊕ Fin 4 → K)
    (hQ : ∀ i, quadPlus 4 K (v i) = 0)
    (horth : ∀ i j, i ≠ j → polar (quadPlus 4 K) (v i) (v j) = 0) :
    ∀ x ∈ Submodule.span K (Set.range v), quadPlus 4 K x = 0 := by
  have hpolar : ∀ z : Fin 4 ⊕ Fin 4 → K, (∀ j, polar (quadPlus 4 K) z (v j) = 0) →
      ∀ y ∈ Submodule.span K (Set.range v), polar (quadPlus 4 K) z y = 0 := by
    intro z hz y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨j, rfl⟩ := hy; exact hz j
    | zero => simp
    | add a b _ _ iha ihb => rw [polar_add_right, iha, ihb, add_zero]
    | smul c a _ iha => rw [polar_smul_right, iha, smul_zero]
  have key : ∀ x ∈ Submodule.span K (Set.range v),
      quadPlus 4 K x = 0 ∧ ∀ j, polar (quadPlus 4 K) x (v j) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine ⟨hQ i, fun j => ?_⟩
        by_cases hij : i = j
        · subst hij; exact polar_self_eq_zero _ _
        · exact horth i j hij
    | zero => exact ⟨map_zero _, fun j => by simp⟩
    | add a b ha hb iha ihb =>
        refine ⟨?_, fun j => ?_⟩
        · rw [map_add_eq, iha.1, ihb.1, hpolar a iha.2 b hb, add_zero, add_zero]
        · rw [polar_add_left, iha.2 j, ihb.2 j, add_zero]
    | smul c a ha iha =>
        refine ⟨?_, fun j => ?_⟩
        · rw [QuadraticMap.map_smul (quadPlus 4 K) c a, iha.1, smul_zero]
        · rw [polar_smul_left, iha.2 j, smul_zero]
  intro x hx
  exact (key x hx).1

omit [Finite K] in
private lemma single_sub_single_comm {ι : Type*} [DecidableEq ι] (a b : ι) :
    (Pi.single a (1:K) - Pi.single b 1 : ι → K) =
      Pi.single b 1 - Pi.single a 1 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_vec_eq K, neg_vec_eq K, add_comm]

private def ps (a b : Fin 4 ⊕ Fin 4) : Fin 4 ⊕ Fin 4 → K :=
  Pi.single a 1 - Pi.single b 1

private def p0 : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | .inl 0 => .inl 0
  | .inl 1 => .inl 2
  | .inl 2 => .inl 1
  | .inl 3 => .inl 3
  | .inr 0 => .inr 0
  | .inr 1 => .inr 2
  | .inr 2 => .inr 1
  | .inr 3 => .inr 3

private def e0 : Equiv.Perm (Fin 4 ⊕ Fin 4) where
  toFun := p0
  invFun := p0
  left_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl
  right_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl

private def a0 : Fin 2 → Fin 4 ⊕ Fin 4 := ![.inl 2, .inr 2]
private def b0 : Fin 2 → Fin 4 ⊕ Fin 4 := ![.inl 1, .inr 1]

omit [Finite K] in
private theorem commSpace_invPerm_zero :
    commSpace (LinearEquiv.funCongrLeft K K (invPerm 0)) =
      Submodule.span K (Set.range fun k : Fin 2 => ps (a0 k) (b0 k)) := by
  rw [show invPerm 0 = e0 from by decide +kernel,
    commSpace_funCongrLeft_of_involution e0 (by decide +kernel +revert)]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    rcases j with j | j <;> fin_cases j <;>
      simp [e0, p0, ps, sub_self]
    all_goals
      first
      | exact Submodule.zero_mem _
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 2 => ps (a0 k) (b0 k)) 0)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 2 => ps (a0 k) (b0 k)) 1)
      | (rw [single_sub_single_comm]
         exact Submodule.subset_span
           (Set.mem_range_self (f := fun k : Fin 2 => ps (a0 k) (b0 k)) 0))
      | (rw [single_sub_single_comm]
         exact Submodule.subset_span
           (Set.mem_range_self (f := fun k : Fin 2 => ps (a0 k) (b0 k)) 1))
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨Sum.inl 1, by simp [e0, p0, ps, a0, b0]⟩
    · exact Submodule.subset_span ⟨Sum.inr 1, by simp [e0, p0, ps, a0, b0]⟩

omit [Finite K] in
private theorem finrank_commSpace_invPerm_zero :
    Module.finrank K (commSpace (LinearEquiv.funCongrLeft K K (invPerm 0))) = 2 := by
  rw [commSpace_invPerm_zero]
  rw [show (fun k : Fin 2 => ps (a0 k) (b0 k)) =
      (fun i => (Pi.single (a0 i) (1:K) - Pi.single (b0 i) 1)) from rfl]
  rw [finrank_span_eq_card (linearIndependent_single_sub_single a0 b0
      (by decide +kernel +revert) (by decide +kernel +revert))]
  norm_num

omit [Finite K] in
private theorem suzukiLetter_invPerm_zero :
    suzukiLetter (quadPlus 4 K) (LinearEquiv.funCongrLeft K K (invPerm 0)) = .a := by
  refine suzukiLetter_eq_a_iff.mpr ⟨?_, ?_⟩
  · rw [finrank_commSpace_invPerm_zero]; exact even_two
  · intro x hx
    rw [commSpace_invPerm_zero] at hx
    exact quadPlus_eq_zero_of_mem_span_range (fun k : Fin 2 => ps (a0 k) (b0 k))
      (by intro k; fin_cases k <;> simp [ps, a0, b0, quadPlus_apply,
        Pi.single_apply])
      (by intro k l hkl; fin_cases k <;> fin_cases l <;>
        simp_all [ps, a0, b0, polar_quadPlus, Pi.single_apply,
          sub_eq_add_neg, CharTwo.neg_eq, CharTwo.add_self_eq_zero]) x hx

private def p1 : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | .inl 0 => .inr 0
  | .inl 1 => .inl 1
  | .inl 2 => .inl 2
  | .inl 3 => .inr 3
  | .inr 0 => .inl 0
  | .inr 1 => .inr 1
  | .inr 2 => .inr 2
  | .inr 3 => .inl 3

private def e1 : Equiv.Perm (Fin 4 ⊕ Fin 4) where
  toFun := p1
  invFun := p1
  left_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl
  right_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl

private def a1 : Fin 2 → Fin 4 ⊕ Fin 4 := ![.inr 0, .inr 3]
private def b1 : Fin 2 → Fin 4 ⊕ Fin 4 := ![.inl 0, .inl 3]

omit [Finite K] in
private theorem commSpace_invPerm_one :
    commSpace (LinearEquiv.funCongrLeft K K (invPerm 1)) =
      Submodule.span K (Set.range fun k : Fin 2 => ps (a1 k) (b1 k)) := by
  rw [show invPerm 1 = e1 from by decide +kernel,
    commSpace_funCongrLeft_of_involution e1 (by decide +kernel +revert)]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    rcases j with j | j <;> fin_cases j <;>
      simp [e1, p1, ps, sub_self]
    all_goals
      first
      | exact Submodule.zero_mem _
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 2 => ps (a1 k) (b1 k)) 0)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 2 => ps (a1 k) (b1 k)) 1)
      | (rw [single_sub_single_comm]
         exact Submodule.subset_span
           (Set.mem_range_self (f := fun k : Fin 2 => ps (a1 k) (b1 k)) 0))
      | (rw [single_sub_single_comm]
         exact Submodule.subset_span
           (Set.mem_range_self (f := fun k : Fin 2 => ps (a1 k) (b1 k)) 1))
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨Sum.inl 0, by simp [e1, p1, ps, a1, b1]⟩
    · exact Submodule.subset_span ⟨Sum.inl 3, by simp [e1, p1, ps, a1, b1]⟩

omit [Finite K] in
private theorem finrank_commSpace_invPerm_one :
    Module.finrank K (commSpace (LinearEquiv.funCongrLeft K K (invPerm 1))) = 2 := by
  rw [commSpace_invPerm_one]
  rw [show (fun k : Fin 2 => ps (a1 k) (b1 k)) =
      (fun i => (Pi.single (a1 i) (1:K) - Pi.single (b1 i) 1)) from rfl]
  rw [finrank_span_eq_card (linearIndependent_single_sub_single a1 b1
      (by decide +kernel +revert) (by decide +kernel +revert))]
  norm_num

omit [Finite K] in
private theorem suzukiLetter_invPerm_one :
    suzukiLetter (quadPlus 4 K) (LinearEquiv.funCongrLeft K K (invPerm 1)) = .c := by
  refine suzukiLetter_eq_c_iff.mpr ⟨?_, ?_⟩
  · rw [finrank_commSpace_invPerm_one]; exact even_two
  · refine ⟨ps (a1 0) (b1 0), ?_, ?_⟩
    · rw [commSpace_invPerm_one]
      exact Submodule.subset_span
        (Set.mem_range_self (f := fun k : Fin 2 => ps (a1 k) (b1 k)) 0)
    · have hQ : quadPlus 4 K (ps (a1 0) (b1 0)) = 1 := by
        simp [a1, b1, ps, quadPlus_apply, Pi.single_apply,
          CharTwo.neg_eq]
      rw [hQ]; exact one_ne_zero

private def p2 : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | .inl 0 => .inl 3
  | .inl 1 => .inl 2
  | .inl 2 => .inl 1
  | .inl 3 => .inl 0
  | .inr 0 => .inr 3
  | .inr 1 => .inr 2
  | .inr 2 => .inr 1
  | .inr 3 => .inr 0

private def e2 : Equiv.Perm (Fin 4 ⊕ Fin 4) where
  toFun := p2
  invFun := p2
  left_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl
  right_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl

private def a2 : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inl 3, .inl 2, .inr 3, .inr 2]
private def b2 : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inl 0, .inl 1, .inr 0, .inr 1]

omit [Finite K] in
private theorem commSpace_invPerm_two :
    commSpace (LinearEquiv.funCongrLeft K K (invPerm 2)) =
      Submodule.span K (Set.range fun k : Fin 4 => ps (a2 k) (b2 k)) := by
  rw [show invPerm 2 = e2 from by decide +kernel,
    commSpace_funCongrLeft_of_involution e2 (by decide +kernel +revert)]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    rcases j with j | j <;> fin_cases j <;>
      simp [e2, p2, ps]
    all_goals
      first
      | exact Submodule.zero_mem _
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 0)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 1)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 2)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 3)
      | (rw [single_sub_single_comm]
         first
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 0)
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 1)
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 2)
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a2 k) (b2 k)) 3))
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨Sum.inl 0, by simp [e2, p2, ps, a2, b2]⟩
    · exact Submodule.subset_span ⟨Sum.inl 1, by simp [e2, p2, ps, a2, b2]⟩
    · exact Submodule.subset_span ⟨Sum.inr 0, by simp [e2, p2, ps, a2, b2]⟩
    · exact Submodule.subset_span ⟨Sum.inr 1, by simp [e2, p2, ps, a2, b2]⟩

omit [Finite K] in
private theorem finrank_commSpace_invPerm_two :
    Module.finrank K (commSpace (LinearEquiv.funCongrLeft K K (invPerm 2))) = 4 := by
  rw [commSpace_invPerm_two]
  rw [show (fun k : Fin 4 => ps (a2 k) (b2 k)) =
      (fun i => (Pi.single (a2 i) (1:K) - Pi.single (b2 i) 1)) from rfl]
  rw [finrank_span_eq_card (linearIndependent_single_sub_single a2 b2
      (by decide +kernel +revert) (by decide +kernel +revert))]
  norm_num

omit [Finite K] in
private theorem suzukiLetter_invPerm_two :
    suzukiLetter (quadPlus 4 K) (LinearEquiv.funCongrLeft K K (invPerm 2)) = .a := by
  refine suzukiLetter_eq_a_iff.mpr ⟨?_, ?_⟩
  · rw [finrank_commSpace_invPerm_two]; exact ⟨2, by norm_num⟩
  · intro x hx
    rw [commSpace_invPerm_two] at hx
    exact quadPlus_eq_zero_of_mem_span_range (fun k : Fin 4 => ps (a2 k) (b2 k))
      (by intro k; fin_cases k <;> simp [ps, a2, b2, quadPlus_apply,
        Pi.single_apply])
      (by intro k l hkl; fin_cases k <;> fin_cases l <;>
        simp_all [ps, a2, b2, polar_quadPlus, Pi.single_apply,
          sub_eq_add_neg, CharTwo.neg_eq, CharTwo.add_self_eq_zero]) x hx

private def p4 : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | .inl 0 => .inr 0
  | .inl 1 => .inr 1
  | .inl 2 => .inr 2
  | .inl 3 => .inr 3
  | .inr 0 => .inl 0
  | .inr 1 => .inl 1
  | .inr 2 => .inl 2
  | .inr 3 => .inl 3

private def e4 : Equiv.Perm (Fin 4 ⊕ Fin 4) where
  toFun := p4
  invFun := p4
  left_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl
  right_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl

private def a4 : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inr 0, .inr 1, .inr 2, .inr 3]
private def b4 : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inl 0, .inl 1, .inl 2, .inl 3]

omit [Finite K] in
private theorem commSpace_invPerm_four :
    commSpace (LinearEquiv.funCongrLeft K K (invPerm 4)) =
      Submodule.span K (Set.range fun k : Fin 4 => ps (a4 k) (b4 k)) := by
  rw [show invPerm 4 = e4 from by decide +kernel,
    commSpace_funCongrLeft_of_involution e4 (by decide +kernel +revert)]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    rcases j with j | j <;> fin_cases j <;>
      simp [e4, p4, ps]
    all_goals
      first
      | exact Submodule.zero_mem _
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 0)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 1)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 2)
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 3)
      | (rw [single_sub_single_comm]
         first
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 0)
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 1)
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 2)
         | exact Submodule.subset_span
             (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 3))
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨Sum.inl 0, by simp [e4, p4, ps, a4, b4]⟩
    · exact Submodule.subset_span ⟨Sum.inl 1, by simp [e4, p4, ps, a4, b4]⟩
    · exact Submodule.subset_span ⟨Sum.inl 2, by simp [e4, p4, ps, a4, b4]⟩
    · exact Submodule.subset_span ⟨Sum.inl 3, by simp [e4, p4, ps, a4, b4]⟩

omit [Finite K] in
private theorem finrank_commSpace_invPerm_four :
    Module.finrank K (commSpace (LinearEquiv.funCongrLeft K K (invPerm 4))) = 4 := by
  rw [commSpace_invPerm_four]
  rw [show (fun k : Fin 4 => ps (a4 k) (b4 k)) =
      (fun i => (Pi.single (a4 i) (1:K) - Pi.single (b4 i) 1)) from rfl]
  rw [finrank_span_eq_card (linearIndependent_single_sub_single a4 b4
      (by decide +kernel +revert) (by decide +kernel +revert))]
  norm_num

omit [Finite K] in
private theorem suzukiLetter_invPerm_four :
    suzukiLetter (quadPlus 4 K) (LinearEquiv.funCongrLeft K K (invPerm 4)) = .c := by
  refine suzukiLetter_eq_c_iff.mpr ⟨?_, ?_⟩
  · rw [finrank_commSpace_invPerm_four]; exact ⟨2, by norm_num⟩
  · refine ⟨ps (a4 0) (b4 0), ?_, ?_⟩
    · rw [commSpace_invPerm_four]
      exact Submodule.subset_span
        (Set.mem_range_self (f := fun k : Fin 4 => ps (a4 k) (b4 k)) 0)
    · have hQ : quadPlus 4 K (ps (a4 0) (b4 0)) = 1 := by
        simp [a4, b4, ps, quadPlus_apply, Pi.single_apply,
          CharTwo.neg_eq]
      rw [hQ]; exact one_ne_zero

private theorem orthElementaryGroup_eq_omegaGroup :
    orthElementaryGroup (quadPlus 4 K) =
      omegaGroup (quadPlus 4 K) (nondegenerate_polarBilin_quadPlus 4 K) := by
  refine le_antisymm
    (CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_omegaGroup
      (nondegenerate_polarBilin_quadPlus 4 K)) ?_
  exact CFSG.RankThree.GF2n.Smith81.omegaGroup_le_elementaryGroup_of_four_le
    (Q := quadPlus 4 K) (nondegenerate_polarBilin_quadPlus 4 K) (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      norm_num)

omit [Finite K] [CharP K 2] in
private theorem funCongrLeft_one {ι : Type*} [DecidableEq ι] :
    LinearEquiv.funCongrLeft K K (1 : Equiv.Perm ι) = 1 := by
  ext y i
  rfl

omit [Finite K] [CharP K 2] in
private theorem funCongrLeft_injective {ι : Type*} [DecidableEq ι] :
    Function.Injective (fun π : Equiv.Perm ι => LinearEquiv.funCongrLeft K K π) := by
  intro π σ h
  have h2 : ∀ j : ι, π.symm j = σ.symm j := by
    intro j
    have h1 : (Pi.single (π.symm j) (1:K) : ι → K) = Pi.single (σ.symm j) 1 := by
      have hh := congrArg (fun e : (ι → K) ≃ₗ[K] (ι → K) => e (Pi.single j 1)) h
      rwa [funCongrLeft_single, funCongrLeft_single] at hh
    have h3 := congrFun h1 (π.symm j)
    simp only [Pi.single_apply] at h3
    rw [if_true] at h3
    by_contra hne
    rw [if_neg hne] at h3
    exact one_ne_zero h3
  have hsymm : π.symm = σ.symm := Equiv.ext h2
  simpa using congrArg Equiv.symm hsymm

private theorem invPerm_pair (i : Fin 5) :
    ∀ k : Fin 4, invPerm i (Sum.inr k) = (invPerm i (Sum.inl k)).swap := by
  intro k
  fin_cases i <;> fin_cases k <;> decide +kernel

private theorem invPerm_ne_one (i : Fin 5) : invPerm i ≠ 1 := by
  fin_cases i <;> decide +kernel

omit [Finite K] [CharP K 2] in
private theorem funCongrLeft_invPerm_ne_one (i : Fin 5) :
    LinearEquiv.funCongrLeft K K (invPerm i) ≠ 1 := by
  intro h
  have h1 : LinearEquiv.funCongrLeft K K (invPerm i) = LinearEquiv.funCongrLeft K K 1 := by
    rw [h, funCongrLeft_one]
  exact invPerm_ne_one i (funCongrLeft_injective h1)

omit [Finite K] [CharP K 2] in
private theorem orderOf_funCongrLeft_invPerm (i : Fin 5) :
    orderOf (LinearEquiv.funCongrLeft K K (invPerm i)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime_iff.mpr ⟨?_, funCongrLeft_invPerm_ne_one i⟩
  rw [pow_two, funCongrLeft_mul,
    show invPerm i * invPerm i = 1 from by decide +kernel +revert, funCongrLeft_one]

omit [Finite K] [CharP K 2] in
private theorem funCongrLeft_invPerm_mem (i : Fin 5) :
    LinearEquiv.funCongrLeft K K (invPerm i) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  exact quadPlus_funCongrLeft_of_pair (π := invPerm i) (invPerm_pair i) v

private def p5 : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4
  | .inl 0 => .inl 0
  | .inl 1 => .inl 1
  | .inl 2 => .inl 2
  | .inl 3 => .inr 3
  | .inr 0 => .inr 0
  | .inr 1 => .inr 1
  | .inr 2 => .inr 2
  | .inr 3 => .inl 3

private def e5 : Equiv.Perm (Fin 4 ⊕ Fin 4) where
  toFun := p5
  invFun := p5
  left_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl
  right_inv := by intro x; rcases x with i | i <;> fin_cases i <;> rfl

private def a5 : Fin 1 → Fin 4 ⊕ Fin 4 := fun _ => .inr 3
private def b5 : Fin 1 → Fin 4 ⊕ Fin 4 := fun _ => .inl 3

omit [Finite K] in
private theorem commSpace_e5 :
    commSpace (LinearEquiv.funCongrLeft K K e5) =
      Submodule.span K (Set.range fun k : Fin 1 => ps (a5 k) (b5 k)) := by
  rw [commSpace_funCongrLeft_of_involution e5 (by decide +kernel +revert)]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    rcases j with j | j <;> fin_cases j <;>
      simp [e5, p5, ps, sub_self]
    all_goals
      first
      | exact Submodule.zero_mem _
      | exact Submodule.subset_span
          (Set.mem_range_self (f := fun k : Fin 1 => ps (a5 k) (b5 k)) 0)
      | (rw [single_sub_single_comm]
         exact Submodule.subset_span
           (Set.mem_range_self (f := fun k : Fin 1 => ps (a5 k) (b5 k)) 0))
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    fin_cases k
    · exact Submodule.subset_span ⟨Sum.inl 3, by simp [e5, p5, ps, a5, b5]⟩

omit [Finite K] in
private theorem finrank_commSpace_e5 :
    Module.finrank K (commSpace (LinearEquiv.funCongrLeft K K e5)) = 1 := by
  rw [commSpace_e5]
  rw [show (fun k : Fin 1 => ps (a5 k) (b5 k)) =
      (fun i => (Pi.single (a5 i) (1:K) - Pi.single (b5 i) 1)) from rfl]
  rw [finrank_span_eq_card (linearIndependent_single_sub_single a5 b5
      (by decide +kernel +revert) (by decide +kernel +revert))]
  norm_num

private theorem exists_conj_of_repr (t : orthElementaryGroup (quadPlus 4 K))
    (ht : t * t = 1) (ht1 : t ≠ 1) (i : Fin 5)
    (hletter : suzukiLetter (quadPlus 4 K) (LinearEquiv.funCongrLeft K K (invPerm i)) =
      suzukiLetter (quadPlus 4 K) (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)))
    (hfin : Module.finrank K (commSpace (LinearEquiv.funCongrLeft K K (invPerm i))) =
      Module.finrank K (commSpace (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))))
    (hnot : ¬ (suzukiLetter (quadPlus 4 K) (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = .a ∧
      Module.finrank K (commSpace (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))) = 4)) :
    ∃ g : orthElementaryGroup (quadPlus 4 K),
      ((g * t * g⁻¹ : orthElementaryGroup (quadPlus 4 K)) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        LinearEquiv.funCongrLeft K K (invPerm i) := by
  have hQ : (quadPlus 4 K).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 4 K
  have hV : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  let t₀ : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := t
  have htO : t₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    orthElementaryGroup_le _ t.2
  have ht2 : orderOf t₀ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have ht₀ : t₀ * t₀ = 1 := by
      change (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) *
        (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = 1
      rw [← Subgroup.coe_mul, ht, Subgroup.coe_one]
    have ht1₀ : t₀ ≠ 1 := fun h => ht1 (Subtype.ext (by simpa [t₀] using h))
    exact orderOf_eq_prime_iff.mpr ⟨by rwa [pow_two], ht1₀⟩
  have htΩ : t₀ ∈ omegaGroup (quadPlus 4 K) hQ := by
    rw [← orthElementaryGroup_eq_omegaGroup]; exact t.2
  obtain ⟨g, hgO, hconj⟩ :=
    (isConj_iff_suzukiLetter_eq (Q := quadPlus 4 K) hQ htO ht2
      (funCongrLeft_invPerm_mem i) (orderOf_funCongrLeft_invPerm i)).mpr
      ⟨hletter, hfin⟩
  have hclass := omega_conj_eq_of_not_typeA_half (Q := quadPlus 4 K) hQ (m := 4) hV htΩ ht2 hnot
  have hmem : LinearEquiv.funCongrLeft K K (invPerm i) ∈
      {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K), g * t₀ * g⁻¹ = x} :=
    ⟨g, hgO, hconj⟩
  rw [← hclass] at hmem
  obtain ⟨g', hg'Ω, hconj'⟩ := hmem
  refine ⟨⟨g', ?_⟩, ?_⟩
  · rw [orthElementaryGroup_eq_omegaGroup]; exact hg'Ω
  · change g' * t₀ * g'⁻¹ = LinearEquiv.funCongrLeft K K (invPerm i)
    exact hconj'

theorem exists_conj_eq_invPerm (t : orthElementaryGroup (quadPlus 4 K)) (ht : t * t = 1)
    (ht1 : t ≠ 1) :
    ∃ (i : Fin 5) (g : orthElementaryGroup (quadPlus 4 K)),
      ((g * t * g⁻¹ : orthElementaryGroup (quadPlus 4 K)) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
        LinearEquiv.funCongrLeft K K (invPerm i) := by
  have hQ : (quadPlus 4 K).polarBilin.Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 4 K
  let t₀ : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := t
  have htO : t₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
    orthElementaryGroup_le _ t.2
  have ht₀ : t₀ * t₀ = 1 := by
    change (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) * (t : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = 1
    rw [← Subgroup.coe_mul, ht, Subgroup.coe_one]
  have ht1₀ : t₀ ≠ 1 := fun h => ht1 (Subtype.ext (by simpa [t₀] using h))
  have ht2 : orderOf t₀ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_iff.mpr ⟨by rwa [pow_two], ht1₀⟩
  have htΩ : t₀ ∈ omegaGroup (quadPlus 4 K) hQ := by
    rw [← orthElementaryGroup_eq_omegaGroup]; exact t.2
  have hV : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 2 * 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  set l := Module.finrank K (commSpace t₀) with hl
  have hleven : Even l := htΩ.2
  have hl1 : 1 ≤ l := one_le_finrank_commSpace ht1₀
  have hl4 : 2 * l ≤ 8 := by
    have h := two_mul_finrank_commSpace_le (t := t₀) ht₀
    rw [hV] at h
    omega
  have hletter_t : suzukiLetter (quadPlus 4 K) t₀ = .a ∨ suzukiLetter (quadPlus 4 K) t₀ = .c := by
    rcases h : suzukiLetter (quadPlus 4 K) t₀ with _ | _ | _
    · exact Or.inl rfl
    · exfalso
      rw [suzukiLetter_eq_b_iff] at h
      exact (Nat.not_odd_iff_even.mpr hleven) h
    · exact Or.inr rfl
  rcases hleven with ⟨k, hk⟩
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ 2 := by omega
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · have hl2 : l = 2 := by omega
    have hnot : ¬ (suzukiLetter (quadPlus 4 K) t₀ = .a ∧
        Module.finrank K (commSpace t₀) = 4) := by
      rintro ⟨-, h4⟩
      omega
    rcases hletter_t with ha | hc
    · exact ⟨0, exists_conj_of_repr t ht ht1 0 (by rw [suzukiLetter_invPerm_zero, ha])
        (by rw [finrank_commSpace_invPerm_zero, ← hl]; omega) hnot⟩
    · exact ⟨1, exists_conj_of_repr t ht ht1 1 (by rw [suzukiLetter_invPerm_one, hc])
        (by rw [finrank_commSpace_invPerm_one, ← hl]; omega) hnot⟩
  · have hl2 : l = 4 := by omega
    rcases hletter_t with ha | hc
    ·
      obtain ⟨g, hgO, hconj⟩ :=
        (isConj_iff_suzukiLetter_eq (Q := quadPlus 4 K) hQ htO ht2
          (funCongrLeft_invPerm_mem 2) (orderOf_funCongrLeft_invPerm 2)).mpr
          ⟨by rw [suzukiLetter_invPerm_two, ha],
            by rw [finrank_commSpace_invPerm_two, ← hl]; omega⟩
      by_cases hgΩ : g ∈ omegaGroup (quadPlus 4 K) hQ
      · refine ⟨2, ⟨g, ?_⟩, ?_⟩
        · rw [orthElementaryGroup_eq_omegaGroup]; exact hgΩ
        · change g * t₀ * g⁻¹ = LinearEquiv.funCongrLeft K K (invPerm 2)
          exact hconj
      · let r : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := LinearEquiv.funCongrLeft K K e5
        have he5 : e5 * e5 = 1 := by decide +kernel +revert
        have hr2 : r * r = 1 := by
          dsimp [r]
          rw [funCongrLeft_mul, he5, funCongrLeft_one]
        have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
        have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
          rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
          intro v
          exact quadPlus_funCongrLeft_of_pair (π := e5) (by
            intro k; fin_cases k <;> rfl) v
        have hr1 : Module.finrank K (commSpace r) = 1 := by
          dsimp [r]; exact finrank_commSpace_e5
        have hrgΩ : r * g ∈ omegaGroup (quadPlus 4 K) hQ := by
          refine ⟨mul_mem hrO hgO, ?_⟩
          rw [← ZMod.natCast_eq_zero_iff_even]
          have hgodd : Odd (Module.finrank K (commSpace g)) := by
            by_contra h
            exact hgΩ ⟨hgO, Nat.not_odd_iff_even.mp h⟩
          rw [natCast_finrank_commSpace_mul hQ hrO hgO, hr1,
            (ZMod.natCast_eq_one_iff_odd).mpr hgodd, Nat.cast_one]
          decide
        have hconj3 : r * LinearEquiv.funCongrLeft K K (invPerm 2) * r⁻¹ =
            LinearEquiv.funCongrLeft K K (invPerm 3) := by
          dsimp [r]
          rw [hrinv]
          calc LinearEquiv.funCongrLeft K K e5 * LinearEquiv.funCongrLeft K K (invPerm 2) *
                LinearEquiv.funCongrLeft K K e5
              = LinearEquiv.funCongrLeft K K (e5 * (invPerm 2 * e5)) := by
                rw [funCongrLeft_mul, funCongrLeft_mul]
            _ = LinearEquiv.funCongrLeft K K (invPerm 3) := by
                rw [show e5 * (invPerm 2 * e5) = invPerm 3 from by decide +kernel]
        have hconj' : (r * g) * t₀ * (r * g)⁻¹ =
            LinearEquiv.funCongrLeft K K (invPerm 3) := by
          calc (r * g) * t₀ * (r * g)⁻¹ = r * (g * t₀ * g⁻¹) * r⁻¹ := by group
            _ = r * LinearEquiv.funCongrLeft K K (invPerm 2) * r⁻¹ := by rw [hconj]
            _ = _ := hconj3
        refine ⟨3, ⟨r * g, ?_⟩, ?_⟩
        · rw [orthElementaryGroup_eq_omegaGroup]; exact hrgΩ
        · change (r * g) * t₀ * (r * g)⁻¹ = LinearEquiv.funCongrLeft K K (invPerm 3)
          exact hconj'
    · have hnotc : ¬ (suzukiLetter (quadPlus 4 K) t₀ = .a ∧
          Module.finrank K (commSpace t₀) = 4) := by
        rintro ⟨ha, -⟩
        rw [hc] at ha
        exact absurd ha (by decide)
      exact ⟨4, exists_conj_of_repr t ht ht1 4 (by rw [suzukiLetter_invPerm_four, hc])
        (by rw [finrank_commSpace_invPerm_four, ← hl]; omega) hnotc⟩

private theorem range_mul_eq_map {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    (f g : Module.End k W) :
    LinearMap.range (f * g) = (LinearMap.range g).map f := by
  ext x
  simp only [LinearMap.mem_range, Module.End.mul_apply, Submodule.mem_map]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨g y, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, rfl⟩

private theorem range_sub_one_conj {k W G : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Group G] (ρ : Representation k G W) (g t : G) :
    LinearMap.range (ρ (g * t * g⁻¹) - 1) = (LinearMap.range (ρ t - 1)).map (ρ g) := by
  have hgg : ρ g * ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hgg' : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hsurj : Function.Surjective (ρ g) := fun x => ⟨ρ g⁻¹ x, by
    rw [← Module.End.mul_apply, hgg]; rfl⟩
  have hmul : (ρ (g * t * g⁻¹) - 1) * ρ g = ρ g * (ρ t - 1) := by
    rw [map_mul, map_mul, sub_mul, mul_sub, mul_one, one_mul]
    rw [mul_assoc, hgg', mul_one]
  have hrange : LinearMap.range ((ρ (g * t * g⁻¹) - 1) * ρ g) =
      LinearMap.range (ρ (g * t * g⁻¹) - 1) := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, rfl⟩
      exact ⟨ρ g y, rfl⟩
    · rintro x ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := hsurj y
      exact ⟨z, by rw [Module.End.mul_apply, hz]⟩
  rw [← hrange, hmul, range_mul_eq_map]

section Chev

theorem exists_conj_eq_nW_invWord
    {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
    (t : adjointGroup .D4 K) (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ (i : Fin 5) (g : adjointGroup .D4 K),
      g * t * g⁻¹ = (chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i)) := by
  have htη : eta K t * eta K t = 1 := by rw [← map_mul, ht, map_one]
  have htη1 : eta K t ≠ 1 := fun h => ht1 ((eta K).injective (by simpa using h))
  obtain ⟨i, g', hconj⟩ := exists_conj_eq_invPerm (eta K t) htη htη1
  refine ⟨i, (eta K).symm g', ?_⟩
  apply (eta K).injective
  have hleft : eta K ((eta K).symm g' * t * ((eta K).symm g')⁻¹) =
      g' * eta K t * g'⁻¹ := by
    rw [map_mul, map_mul]
    simp
  rw [hleft]
  apply Subtype.ext
  show ((g' * eta K t * g'⁻¹ : orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) =
    ((eta K ((chevDatum .D4 K 2 hw).nW ((coxeterSystem .D4).wordProd (invWord i))) :
      orthElementaryGroup (quadPlus 4 K)) :
      (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
  rw [eta_nW_invWord]
  exact hconj

theorem nine_le_finrank_range_of_sq_eq_one
    {hw : ∃ w₁ : WeylGroup Tag.D4, ∀ α : Fin Tag.D4.rank → ℤ, w₁ • α = -α}
    {k W : Type*} [Field k] [Algebra K k] [CharP k 2] [AddCommGroup W] [Module k W]
    [Module.Finite k W] {ρ : Representation k (adjointGroup .D4 K) W} {y : W}
    {χ : adjointGroup .D4 K → k} {J : Finset (Fin Tag.D4.rank)} (hρ : IsSimpleRep ρ)
    (ht : IsChevType .D4 K 2 hw ρ y χ J) (hJu : J ≠ Finset.univ)
    (hJe : ∀ e ∈ ({0, 1, 3} : Finset (Fin 4)), J ≠ Finset.univ.erase e)
    (t : adjointGroup .D4 K) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    9 ≤ Module.finrank k (LinearMap.range (ρ t - 1)) := by
  obtain ⟨i, g, hconj⟩ := exists_conj_eq_nW_invWord (hw := hw) t ht2 ht1
  have hgg' : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hinj : Function.Injective (ρ g : W →ₗ[k] W) := fun u v huv => by
    calc u = ρ g⁻¹ (ρ g u) := by rw [← Module.End.mul_apply, hgg']; rfl
      _ = ρ g⁻¹ (ρ g v) := by rw [huv]
      _ = v := by rw [← Module.End.mul_apply, hgg']; rfl
  have hrange : LinearMap.range (ρ ((chevDatum .D4 K 2 hw).nW
        ((coxeterSystem .D4).wordProd (invWord i))) - 1) =
      (LinearMap.range (ρ t - 1)).map (ρ g) := by
    rw [← hconj]
    exact range_sub_one_conj ρ g t
  have hfin : Module.finrank k (LinearMap.range (ρ t - 1)) =
      Module.finrank k (LinearMap.range (ρ ((chevDatum .D4 K 2 hw).nW
        ((coxeterSystem .D4).wordProd (invWord i))) - 1)) := by
    rw [hrange]
    exact (Submodule.equivMapOfInjective (ρ g : W →ₗ[k] W) hinj
      (LinearMap.range (ρ t - 1))).finrank_eq
  rw [hfin]
  exact nine_le_finrank_range_of_not_natural hρ ht hJu hJe i

end Chev

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
