module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjDecomp
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjE6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.TwE6Rep27

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

@[expose] def twAdjMoves (α : Fin Tag.E6.rank → ℤ) : List (Fin Tag.E6.rank → ℤ) :=
  (List.finRange 6).filterMap (fun i => if α ≠ Pi.single i 1 ∧ α ≠ -Pi.single i 1 ∧
    List.ofFn (α + Pi.single i 1) ∈ Tag.E6.artifactRoots then some (α + Pi.single i 1)
      else none) ++
  (List.finRange 4).map (fun a => (TwistTag.E6.orbitWord a).foldr (reflect .E6) α)

@[expose] def twAdjStep (S : List (Fin Tag.E6.rank → ℤ)) : List (Fin Tag.E6.rank → ℤ) :=
  (S ++ S.flatMap twAdjMoves).eraseDups

@[expose] def twAdjIter : ℕ → List (Fin Tag.E6.rank → ℤ)
  | 0 => [e6Theta0]
  | N + 1 => twAdjStep (twAdjIter N)

@[expose] def twAdjReachCheck (N : ℕ) : Bool :=
  (List.range Tag.E6.rootCount).all fun k =>
    decide ((Tag.rootCertificate .E6).root k ∈ twAdjIter N)

theorem twAdj_reach : twAdjReachCheck 20 = true := by decide +kernel

theorem mem_twAdjMoves {α β : Fin Tag.E6.rank → ℤ} (h : β ∈ twAdjMoves α) :
    (∃ i : Fin Tag.E6.rank, α ≠ Pi.single i 1 ∧ α ≠ -Pi.single i 1 ∧
      List.ofFn (α + Pi.single i 1) ∈ Tag.E6.artifactRoots ∧ β = α + Pi.single i 1) ∨
      ∃ a : Fin TwistTag.E6.foldedTag.rank,
        (TwistTag.E6.orbitWord a).foldr (reflect .E6) α = β := by
  unfold twAdjMoves at h
  rw [List.mem_append] at h
  rcases h with h | h
  · left
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 h
    by_cases hc : α ≠ Pi.single i 1 ∧ α ≠ -Pi.single i 1 ∧
        List.ofFn (α + Pi.single i 1) ∈ Tag.E6.artifactRoots
    · rw [if_pos hc] at hi
      exact ⟨i, hc.1, hc.2.1, hc.2.2, (Option.some.inj hi).symm⟩
    · rw [if_neg hc] at hi
      exact absurd hi (by simp)
  · right
    obtain ⟨a, -, ha⟩ := List.mem_map.1 h
    exact ⟨a, ha⟩

section Tw

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
  (a : Fin TwistTag.E6.foldedTag.rank)

@[expose] def twAdj :
    Representation K ↥(graphFixedRootGroup TwistTag.E6 K σ) (RootModule TwistTag.E6.tag K) :=
  (Units.coeHom (Module.End K (RootModule TwistTag.E6.tag K))).comp
    (graphFixedRootGroup TwistTag.E6 K σ).subtype

theorem twAdj_apply (g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) :
    twAdj σ g = ((g : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) :=
  rfl

@[expose] def xkOp (k : ℕ) (c : K) : Module.End K (RootModule TwistTag.E6.tag K) :=
  xOp TwistTag.E6.tag K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a)) ((σ ^ k) c)

theorem twAdj_xC (c : orbitField TwistTag.E6 K σ a) :
    twAdj σ (xC TwistTag.E6 K σ a c) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k => xkOp σ a k (c : K)).prod := by
  rw [twAdj_apply]
  change (((orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K)) :
    Module.End K (RootModule TwistTag.E6.tag K)) = _
  rw [coe_orbitX, ← Units.coeHom_apply, map_list_prod, List.map_map]
  rfl

theorem twAdj_xC_card_one (ha : (TwistTag.E6.orbit a).card = 1)
    (c : orbitField TwistTag.E6 K σ a) :
    twAdj σ (xC TwistTag.E6 K σ a c) = xkOp σ a 0 (c : K) := by
  rw [twAdj_xC, ha]
  simp

theorem twAdj_xC_card_two (ha : (TwistTag.E6.orbit a).card = 2)
    (c : orbitField TwistTag.E6 K σ a) :
    twAdj σ (xC TwistTag.E6 K σ a c) = xkOp σ a 0 (c : K) * xkOp σ a 1 (c : K) := by
  rw [twAdj_xC, ha]
  simp [List.range_succ]

include hf hK hσ in
theorem Dop_mem_of_stable_tw (hf2 : 2 ≤ f) (S : Submodule K (RootModule TwistTag.E6.tag K))
    (w : RootModule TwistTag.E6.tag K)
    (hw : ∀ c : orbitField TwistTag.E6 K σ a, twAdj σ (xC TwistTag.E6 K σ a c) w - w ∈ S)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ TwistTag.E6.orbit a) :
    Dop TwistTag.E6.tag K i w ∈ S := by
  rcases orbit_card_one_or_two a with ha | ha
  · have hi' : i = TwistTag.E6.orbitMin a := by
      have := orbit_one_data a ha
      rw [this, Finset.mem_singleton] at hi
      exact hi
    have h1 := hw 1
    rw [twAdj_xC_card_one σ a ha] at h1
    rw [hi', Dop_apply]
    simpa [xkOp] using h1
  · obtain ⟨hne, hset⟩ := orbit_two_data a ha
    obtain ⟨hfin, hcard⟩ := natCard_eq_q_sq_fintype hK
    set q := 2 ^ f with hq
    have hq4 : 4 ≤ q := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ a := fun c => by
      rw [mem_orbitField, ha]
      simp only [pow_two, RingHom.mul_def, RingHom.id_apply]
      exact sigma_sigma_eq hK σ hσ c
    set i₀ := TwistTag.E6.orbitMin a with hi₀
    set j₀ := TwistTag.E6.perm i₀ with hj₀
    let aj : RootModule TwistTag.E6.tag K := Dop TwistTag.E6.tag K j₀ w - Bop TwistTag.E6.tag K j₀ w
    let bj : RootModule TwistTag.E6.tag K := Bop TwistTag.E6.tag K j₀ w
    let Ai : RootModule TwistTag.E6.tag K → RootModule TwistTag.E6.tag K :=
      fun x => Dop TwistTag.E6.tag K i₀ x - Bop TwistTag.E6.tag K i₀ x
    let Bi : RootModule TwistTag.E6.tag K → RootModule TwistTag.E6.tag K :=
      fun x => Bop TwistTag.E6.tag K i₀ x
    let ex : Fin 8 → ℕ := ![1, 2, q, 2 * q, q + 1, q + 2, 2 * q + 1, 2 * q + 2]
    let u : Fin 8 → RootModule TwistTag.E6.tag K :=
      ![Ai w, Bi w, aj, bj, Ai aj, Bi aj, Ai bj, Bi bj]
    have hinj : Function.Injective ex := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [ex] at hxy ⊢ <;> omega
    have hbd : ∀ k, ex k < Fintype.card K := by
      intro k
      rw [hcard]
      have : q + 2 < q ^ 2 := by nlinarith
      fin_cases k <;> simp [ex] <;> nlinarith
    have key := mem_of_forall_poly_inj S ex hinj hbd u (fun c => by
      have h1 := hw ⟨c, hmem c⟩
      rw [twAdj_xC_card_two σ a ha] at h1
      simp only [Module.End.mul_apply, xkOp, pow_zero, pow_one, Equiv.Perm.coe_one, id_eq,
        RingHom.coe_one] at h1
      have h1' : xOp TwistTag.E6.tag K i₀ c (xOp TwistTag.E6.tag K j₀ (σ c) w) - w ∈ S := h1
      have e1 := xOp_eq_decomp adjHyp_E6 i₀ c (xOp TwistTag.E6.tag K j₀ (σ c) w)
      have e2 := xOp_eq_decomp adjHyp_E6 j₀ (σ c) w
      have hq' : c ^ q = σ c := (hσ c).symm
      have p1 : c ^ (2 * q) = σ c ^ 2 := by rw [mul_comm, pow_mul, hq']
      have p2 : c ^ (q + 1) = c * σ c := by rw [pow_succ, hq', mul_comm]
      have p3 : c ^ (q + 2) = c ^ 2 * σ c := by rw [pow_add, hq', mul_comm]
      have p4 : c ^ (2 * q + 1) = c * σ c ^ 2 := by rw [pow_succ, p1, mul_comm]
      have p5 : c ^ (2 * q + 2) = c ^ 2 * σ c ^ 2 := by rw [pow_add, p1, mul_comm]
      have hexp : xOp TwistTag.E6.tag K i₀ c (xOp TwistTag.E6.tag K j₀ (σ c) w) - w =
          ∑ k, c ^ ex k • u k := by
        rw [e1, e2]
        simp only [map_add, map_sub, map_smul, Fin.sum_univ_eight]
        simp only [u, ex, Ai, Bi, aj, bj]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.cons_val_four]
        simp [p1, p2, p3, p4, p5, hq']
        module
      rw [← hexp]
      exact h1')
    have hDi : Dop TwistTag.E6.tag K i₀ w ∈ S := by
      have h0 := key 0
      have h1 := key 1
      simp only [u, Matrix.cons_val_zero, Matrix.cons_val_one, Ai, Bi] at h0 h1
      have := add_mem h0 h1
      simpa using this
    have hDj : Dop TwistTag.E6.tag K j₀ w ∈ S := by
      have h2 := key 2
      have h3 := key 3
      simp only [u, Matrix.cons_val_two, Matrix.cons_val_three, aj, bj] at h2 h3
      have := add_mem h2 h3
      simpa using this
    rw [hset] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hDi
    · exact hDj

@[expose] def OrthPair (i j : Fin TwistTag.E6.tag.rank) : Prop :=
  i ≠ j ∧ ¬IsRoot TwistTag.E6.tag (Pi.single i 1 + Pi.single j 1) ∧
    ¬IsRoot TwistTag.E6.tag (-Pi.single i 1 + Pi.single j 1) ∧
    ¬IsRoot TwistTag.E6.tag (-Pi.single j 1 + Pi.single i 1) ∧
    ¬IsRoot TwistTag.E6.tag (-Pi.single i 1 - Pi.single j 1) ∧
    TwistTag.E6.tag.cartan j i = 0

theorem orbit_two_orth_aux : ∀ a : Fin TwistTag.E6.foldedTag.rank,
    (TwistTag.E6.orbit a).card = 2 →
    TwistTag.E6.perm (TwistTag.E6.orbitMin a) ≠ TwistTag.E6.orbitMin a ∧
    List.ofFn (Pi.single (TwistTag.E6.orbitMin a) 1 +
      Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 :
        Fin TwistTag.E6.tag.rank → ℤ) ∉ Tag.E6.artifactRoots ∧
    List.ofFn (-Pi.single (TwistTag.E6.orbitMin a) 1 +
      Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 :
        Fin TwistTag.E6.tag.rank → ℤ) ∉ Tag.E6.artifactRoots ∧
    List.ofFn (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 +
      Pi.single (TwistTag.E6.orbitMin a) 1 :
        Fin TwistTag.E6.tag.rank → ℤ) ∉ Tag.E6.artifactRoots ∧
    List.ofFn (-Pi.single (TwistTag.E6.orbitMin a) 1 -
      Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1 :
        Fin TwistTag.E6.tag.rank → ℤ) ∉ Tag.E6.artifactRoots ∧
    TwistTag.E6.tag.cartan (TwistTag.E6.perm (TwistTag.E6.orbitMin a))
      (TwistTag.E6.orbitMin a) = 0 := by
  decide +kernel

theorem orthPair_orbit (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 2) :
    OrthPair (TwistTag.E6.orbitMin a) (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := orbit_two_orth_aux a ha
  exact ⟨h0.symm, fun h => h1 (isRoot_iff_mem_artifactRoots.1 h),
    fun h => h2 (isRoot_iff_mem_artifactRoots.1 h), fun h => h3 (isRoot_iff_mem_artifactRoots.1 h),
    fun h => h4 (isRoot_iff_mem_artifactRoots.1 h), h5⟩

theorem orbit_raise_aux : ∀ i k : Fin TwistTag.E6.tag.rank,
    k ∈ TwistTag.E6.orbit (TwistTag.E6.orbitIndex i) → k ≠ i →
    List.ofFn (-Pi.single k 1 + Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ∉
      Tag.E6.artifactRoots := by
  decide +kernel

theorem not_isRoot_neg_add_of_orbit {i k : Fin TwistTag.E6.tag.rank}
    (hk : k ∈ TwistTag.E6.orbit (TwistTag.E6.orbitIndex i)) (hki : k ≠ i) :
    ¬IsRoot TwistTag.E6.tag (-Pi.single k 1 + Pi.single i 1) := fun h =>
  orbit_raise_aux i k hk hki (isRoot_iff_mem_artifactRoots.1 h)

section Orth

variable {K : Type} [Field K] {i j : Fin TwistTag.E6.tag.rank}

theorem neg_single_ne_single' (i j : Fin TwistTag.E6.tag.rank) :
    (-Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single j 1 := by
  intro h
  have := congrFun h i
  by_cases hij : i = j
  · subst hij; simp at this
  · simp [Pi.single_apply, hij] at this

theorem neg_single_ne_neg_single' (h : i ≠ j) :
    (-Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ -Pi.single j 1 := by
  intro h'
  have := congrFun h' i
  simp [Pi.single_apply, h] at this

theorem single_ne_single' (h : i ≠ j) :
    (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ Pi.single j 1 := by
  intro h'
  have := congrFun h' i
  simp [Pi.single_apply, h] at this

theorem single_ne_neg_single' (i j : Fin TwistTag.E6.tag.rank) :
    (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) ≠ -Pi.single j 1 := fun h =>
  neg_single_ne_single' j i h.symm

theorem Bop_Dop_of_orth (h : OrthPair i j) (w : RootModule TwistTag.E6.tag K) :
    Bop TwistTag.E6.tag K i (Dop TwistTag.E6.tag K j w) = 0 := by
  rw [Bop_apply]
  have h1 : coordR (Dop TwistTag.E6.tag K j w) (-Pi.single i 1) = 0 := by
    rw [coordR_Dop adjHyp_E6 j w (isRoot_neg_single _ i) (neg_single_ne_single' i j)]
    unfold coordR
    rw [dif_neg h.2.2.2.2.1]
  rw [h1, zero_smul]

theorem Bop_Bop_of_orth (h : OrthPair i j) (w : RootModule TwistTag.E6.tag K) :
    Bop TwistTag.E6.tag K i (Bop TwistTag.E6.tag K j w) = 0 := by
  have h1 : coordR (Bop TwistTag.E6.tag K j w) (-Pi.single i 1) = 0 := by
    rw [Bop_apply, coordR_smul, coordR_rootVec (isRoot_single _ j),
      if_neg (single_ne_neg_single' j i), mul_zero]
  rw [Bop_apply (i := i), h1, zero_smul]

theorem Dop_rootVec_single_of_ne (h : i ≠ j) :
    Dop TwistTag.E6.tag K i (rootVec TwistTag.E6.tag K (Pi.single j 1)) =
      rootVec TwistTag.E6.tag K (Pi.single j 1 + Pi.single i 1) :=
  Dop_rootVec_of_ne adjHyp_E6 i (isRoot_single _ j) (single_ne_single' h.symm)
    (single_ne_neg_single' j i)

theorem Dop_Bop_of_orth (h : OrthPair i j) (w : RootModule TwistTag.E6.tag K) :
    Dop TwistTag.E6.tag K i (Bop TwistTag.E6.tag K j w) = 0 := by
  rw [Bop_apply, map_smul, Dop_rootVec_single_of_ne h.1, add_comm,
    rootVec_eq_zero h.2.1, smul_zero]

theorem Dop_rootVec_neg_single_of_ne (h : i ≠ j) :
    Dop TwistTag.E6.tag K j (rootVec TwistTag.E6.tag K (-Pi.single i 1)) =
      rootVec TwistTag.E6.tag K (-Pi.single i 1 + Pi.single j 1) :=
  Dop_rootVec_of_ne adjHyp_E6 j (isRoot_neg_single _ i) (neg_single_ne_single' i j)
    (neg_single_ne_neg_single' h)

theorem xOp_one_eq (k : Fin TwistTag.E6.tag.rank) (v : RootModule TwistTag.E6.tag K) :
    xOp TwistTag.E6.tag K k 1 v = v + Dop TwistTag.E6.tag K k v := by
  rw [Dop_apply]; abel

theorem xx_neg_left (h : OrthPair i j) :
    xOp TwistTag.E6.tag K i 1 (xOp TwistTag.E6.tag K j 1
        (rootVec TwistTag.E6.tag K (-Pi.single i 1))) -
      rootVec TwistTag.E6.tag K (-Pi.single i 1) =
      hVec TwistTag.E6.tag K i + rootVec TwistTag.E6.tag K (Pi.single i 1) := by
  have h1 : Dop TwistTag.E6.tag K j (rootVec TwistTag.E6.tag K (-Pi.single i 1)) = 0 := by
    rw [Dop_rootVec_neg_single_of_ne h.1, rootVec_eq_zero h.2.2.1]
  rw [xOp_one_eq, xOp_one_eq, h1, map_add, map_zero, add_zero, Dop_rootVec_neg_single]
  abel

theorem xx_neg_right (h : OrthPair i j) :
    xOp TwistTag.E6.tag K i 1 (xOp TwistTag.E6.tag K j 1
        (rootVec TwistTag.E6.tag K (-Pi.single j 1))) -
      rootVec TwistTag.E6.tag K (-Pi.single j 1) =
      hVec TwistTag.E6.tag K j + rootVec TwistTag.E6.tag K (Pi.single j 1) := by
  have h1 : Dop TwistTag.E6.tag K i (rootVec TwistTag.E6.tag K (-Pi.single j 1)) = 0 := by
    rw [Dop_rootVec_neg_single_of_ne h.1.symm, rootVec_eq_zero h.2.2.2.1]
  have h2 : Dop TwistTag.E6.tag K i (hVec TwistTag.E6.tag K j) = 0 := by
    rw [Dop_hVec, h.2.2.2.2.2]; simp
  have h3 : Dop TwistTag.E6.tag K i (rootVec TwistTag.E6.tag K (Pi.single j 1)) = 0 := by
    rw [Dop_rootVec_single_of_ne h.1, add_comm, rootVec_eq_zero h.2.1]
  rw [xOp_one_eq j, xOp_one_eq i, Dop_rootVec_neg_single, map_add, map_add, h1, h2, h3]
  abel

theorem xOp_xOp_orth (h : OrthPair i j) (c d : K) (w : RootModule TwistTag.E6.tag K) :
    xOp TwistTag.E6.tag K i c (xOp TwistTag.E6.tag K j d w) - w =
      c • (Dop TwistTag.E6.tag K i w - Bop TwistTag.E6.tag K i w) +
        c ^ 2 • Bop TwistTag.E6.tag K i w +
        d • (Dop TwistTag.E6.tag K j w - Bop TwistTag.E6.tag K j w) +
        d ^ 2 • Bop TwistTag.E6.tag K j w +
        (c * d) • Dop TwistTag.E6.tag K i (Dop TwistTag.E6.tag K j w) := by
  rw [xOp_eq_decomp adjHyp_E6 j d w, xOp_eq_decomp adjHyp_E6 i c]
  simp only [map_add, map_sub, map_smul, Bop_Bop_of_orth h, Bop_Dop_of_orth h, Dop_Bop_of_orth h,
    smul_zero, sub_zero, add_zero]
  module

end Orth

include hf hK hσ in
theorem Dop_mem_of_stable_tw_B (S : Submodule K (RootModule TwistTag.E6.tag K))
    (w : RootModule TwistTag.E6.tag K)
    (hw : ∀ c : orbitField TwistTag.E6 K σ a, twAdj σ (xC TwistTag.E6 K σ a c) w - w ∈ S)
    (hB : ∀ k ∈ TwistTag.E6.orbit a, Bop TwistTag.E6.tag K k w = 0)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ TwistTag.E6.orbit a) :
    Dop TwistTag.E6.tag K i w ∈ S := by
  rcases orbit_card_one_or_two a with ha | ha
  · have hi' : i = TwistTag.E6.orbitMin a := by
      have := orbit_one_data a ha
      rw [this, Finset.mem_singleton] at hi
      exact hi
    have h1 := hw 1
    rw [twAdj_xC_card_one σ a ha] at h1
    rw [hi', Dop_apply]
    simpa [xkOp] using h1
  · obtain ⟨hne, hset⟩ := orbit_two_data a ha
    have horth := orthPair_orbit a ha
    obtain ⟨hfin, hcard⟩ := natCard_eq_q_sq_fintype hK
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ a := fun c => by
      rw [mem_orbitField, ha]
      simp only [pow_two, RingHom.mul_def, RingHom.id_apply]
      exact sigma_sigma_eq hK σ hσ c
    have hBi := hB _ (TwistTag.E6.orbitMin_mem a)
    have hBj := hB (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (by rw [hset]; simp)
    have key := mem_of_forall_poly hq hcard S σ hσ
      (Dop TwistTag.E6.tag K (TwistTag.E6.orbitMin a) w)
      (Dop TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) w)
      (Dop TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
        (Dop TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) w))
      (fun c => by
        have h1 := hw ⟨c, hmem c⟩
        rw [twAdj_xC_card_two σ a ha] at h1
        simp only [Module.End.mul_apply, xkOp, pow_zero, pow_one, Equiv.Perm.coe_one, id_eq,
          RingHom.coe_one] at h1
        have h1' : xOp TwistTag.E6.tag K (TwistTag.E6.orbitMin a) c
            (xOp TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (σ c) w) - w ∈ S :=
          h1
        rw [xOp_xOp_orth horth c (σ c) w, hBi, hBj] at h1'
        convert h1' using 1
        simp only [sub_zero, smul_zero, add_zero])
    rw [hset] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact key.1
    · exact key.2.1

theorem hVec_mem_of_stable_tw (S : Submodule K (RootModule TwistTag.E6.tag K))
    (hS : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ), ∀ w ∈ S, twAdj σ g w ∈ S)
    {j : Fin TwistTag.E6.tag.rank} (hj : j ∈ TwistTag.E6.orbit a)
    (hneg : rootVec TwistTag.E6.tag K (-Pi.single j 1) ∈ S)
    (hpos : rootVec TwistTag.E6.tag K (Pi.single j 1) ∈ S) :
    hVec TwistTag.E6.tag K j ∈ S := by
  have hw := sub_mem (hS (xC TwistTag.E6 K σ a 1) _ hneg) hneg
  rcases orbit_card_one_or_two a with ha | ha
  · have hj' : j = TwistTag.E6.orbitMin a := by
      have := orbit_one_data a ha
      rw [this, Finset.mem_singleton] at hj
      exact hj
    subst hj'
    rw [twAdj_xC_card_one σ a ha] at hw
    have h1 : Dop TwistTag.E6.tag K (TwistTag.E6.orbitMin a)
        (rootVec TwistTag.E6.tag K (-Pi.single (TwistTag.E6.orbitMin a) 1)) ∈ S := by
      rw [Dop_apply]
      simpa [xkOp] using hw
    rw [Dop_rootVec_neg_single] at h1
    simpa using sub_mem h1 hpos
  · obtain ⟨hne, hset⟩ := orbit_two_data a ha
    have horth := orthPair_orbit a ha
    rw [twAdj_xC_card_two σ a ha] at hw
    rw [hset] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · have h1 := xx_neg_left (K := K) horth
      have h2 : xOp TwistTag.E6.tag K (TwistTag.E6.orbitMin a) 1
          (xOp TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1
            (rootVec TwistTag.E6.tag K (-Pi.single (TwistTag.E6.orbitMin a) 1))) -
          rootVec TwistTag.E6.tag K (-Pi.single (TwistTag.E6.orbitMin a) 1) ∈ S := by
        simpa [xkOp] using hw
      rw [h1] at h2
      simpa using sub_mem h2 hpos
    · have h1 := xx_neg_right (K := K) horth
      have h2 : xOp TwistTag.E6.tag K (TwistTag.E6.orbitMin a) 1
          (xOp TwistTag.E6.tag K (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1
            (rootVec TwistTag.E6.tag K (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1))) -
          rootVec TwistTag.E6.tag K (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) ∈ S := by
        simpa [xkOp] using hw
      rw [h1] at h2
      simpa using sub_mem h2 hpos

include hK hσ in
theorem Dop_eq_zero_of_fixed_tw1 (hf1 : f = 1) (v : RootModule TwistTag.E6.tag K)
    (hv : ∀ c : orbitField TwistTag.E6 K σ a, twAdj σ (xC TwistTag.E6 K σ a c) v = v)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ TwistTag.E6.orbit a) :
    Dop TwistTag.E6.tag K i v = 0 := by
  rcases orbit_card_one_or_two a with ha | ha
  · have hi' : i = TwistTag.E6.orbitMin a := by
      have := orbit_one_data a ha
      rw [this, Finset.mem_singleton] at hi
      exact hi
    have h1 := hv 1
    rw [twAdj_xC_card_one σ a ha] at h1
    have h2 : xOp TwistTag.E6.tag K (TwistTag.E6.orbitMin a) 1 v = v := by simpa [xkOp] using h1
    rw [hi', Dop_apply, h2, sub_self]
  · subst hf1
    obtain ⟨hne, hset⟩ := orbit_two_data a ha
    have horth := orthPair_orbit a ha
    obtain ⟨hfin, hcard⟩ := natCard_eq_q_sq_fintype hK
    have hcard4 : Fintype.card K = 4 := by rw [hcard]; norm_num
    have hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ a := fun c => by
      rw [mem_orbitField, ha]
      simp only [pow_two, RingHom.mul_def, RingHom.id_apply]
      exact sigma_sigma_eq hK σ hσ c
    have hc4 : ∀ c : K, (c ^ 2) ^ 2 = c := fun c => by
      have := FiniteField.pow_card c
      rw [hcard4] at this
      calc (c ^ 2) ^ 2 = c ^ 4 := by ring
        _ = c := this
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by rw [hσ]; norm_num
    set i₀ := TwistTag.E6.orbitMin a with hi₀
    set j₀ := TwistTag.E6.perm i₀ with hj₀
    let ex : Fin 3 → ℕ := ![1, 2, 3]
    let u : Fin 3 → RootModule TwistTag.E6.tag K :=
      ![Dop TwistTag.E6.tag K i₀ v - Bop TwistTag.E6.tag K i₀ v + Bop TwistTag.E6.tag K j₀ v,
        Dop TwistTag.E6.tag K j₀ v - Bop TwistTag.E6.tag K j₀ v + Bop TwistTag.E6.tag K i₀ v,
        Dop TwistTag.E6.tag K i₀ (Dop TwistTag.E6.tag K j₀ v)]
    have hinj : Function.Injective ex := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [ex] at hxy ⊢
    have hbd : ∀ k, ex k < Fintype.card K := by
      intro k
      rw [hcard4]
      fin_cases k <;> simp [ex]
    have key := mem_of_forall_poly_inj ⊥ ex hinj hbd u (fun c => by
      have h1 := hv ⟨c, hmem c⟩
      rw [twAdj_xC_card_two σ a ha] at h1
      simp only [Module.End.mul_apply, xkOp, pow_zero, pow_one, Equiv.Perm.coe_one, id_eq,
        RingHom.coe_one] at h1
      have h1' : xOp TwistTag.E6.tag K i₀ c (xOp TwistTag.E6.tag K j₀ (σ c) v) - v = 0 := by
        have : xOp TwistTag.E6.tag K i₀ c (xOp TwistTag.E6.tag K j₀ (σ c) v) = v := h1
        rw [this, sub_self]
      rw [xOp_xOp_orth horth c (σ c) v, hσ2 c, hc4 c] at h1'
      rw [Submodule.mem_bot]
      refine Eq.trans ?_ h1'
      simp only [Fin.sum_univ_three, ex, u, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, pow_one]
      module)
    have s1 : Dop TwistTag.E6.tag K i₀ v - Bop TwistTag.E6.tag K i₀ v +
        Bop TwistTag.E6.tag K j₀ v = 0 := by
      simpa [u] using (Submodule.mem_bot K).1 (key 0)
    have s2 : Dop TwistTag.E6.tag K j₀ v - Bop TwistTag.E6.tag K j₀ v +
        Bop TwistTag.E6.tag K i₀ v = 0 := by
      simpa [u] using (Submodule.mem_bot K).1 (key 1)
    have hli : coordR v (-Pi.single i₀ 1) = 0 := by
      have := congrArg (fun x : RootModule TwistTag.E6.tag K => x (Sum.inl i₀)) s1
      simpa [Dop_inl adjHyp_E6, Bop_apply, rootVec_inl] using this
    have hlj : coordR v (-Pi.single j₀ 1) = 0 := by
      have := congrArg (fun x : RootModule TwistTag.E6.tag K => x (Sum.inl j₀)) s2
      simpa [Dop_inl adjHyp_E6, Bop_apply, rootVec_inl] using this
    have hBi : Bop TwistTag.E6.tag K i₀ v = 0 := by rw [Bop_apply, hli, zero_smul]
    have hBj : Bop TwistTag.E6.tag K j₀ v = 0 := by rw [Bop_apply, hlj, zero_smul]
    rw [hBi, hBj] at s1 s2
    simp only [sub_zero, add_zero] at s1 s2
    rw [hset] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact s1
    · exact s2

theorem twAdj_nC :
    twAdj σ (nC TwistTag.E6 K σ a) =
      ((TwistTag.E6.orbitWord a).map fun j =>
        (weylElt TwistTag.E6.tag K j 1 : Module.End K (RootModule TwistTag.E6.tag K))).prod := by
  rw [twAdj_apply]
  change ((canonicalRep (coxeterSystem TwistTag.E6.tag) K (TwistTag.E6.orbitReflection a) :
    ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) = _
  rw [canonicalRep_orbitReflection, ← Units.coeHom_apply, map_list_prod, List.map_map]
  rfl

theorem weylList_rootVec (l : List (Fin TwistTag.E6.tag.rank)) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.E6.tag β) :
    IsRoot TwistTag.E6.tag (l.foldr (reflect TwistTag.E6.tag) β) ∧
      ((l.map fun j => (weylElt TwistTag.E6.tag K j 1 :
        Module.End K (RootModule TwistTag.E6.tag K))).prod) (rootVec TwistTag.E6.tag K β) =
        rootVec TwistTag.E6.tag K (l.foldr (reflect TwistTag.E6.tag) β) := by
  induction l with
  | nil => exact ⟨hβ, by simp⟩
  | cons j l ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨IsRoot.reflect j h1, ?_⟩
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.foldr_cons]
    rw [h2, weylElt_one_rootVec' j h1]

include hf hK hσ in
theorem orbitSpan_twAdj :
    orbitSpan (twAdj σ) (rootVec TwistTag.E6.tag K e6Theta) = ⊤ := by
  set S := orbitSpan (twAdj σ) (rootVec TwistTag.E6.tag K e6Theta) with hSdef
  have hS : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ), ∀ w ∈ S, twAdj σ g w ∈ S :=
    fun g w hw => orbitSpan_stable (twAdj σ) _ g hw
  have hD : ∀ (i : Fin TwistTag.E6.tag.rank), ∀ w ∈ S,
      (∀ k ∈ TwistTag.E6.orbit (TwistTag.E6.orbitIndex i), Bop TwistTag.E6.tag K k w = 0) →
      Dop TwistTag.E6.tag K i w ∈ S := by
    intro i w hw hB
    exact Dop_mem_of_stable_tw_B hf hK σ hσ (TwistTag.E6.orbitIndex i) S w
      (fun c => sub_mem (hS _ _ hw) hw) hB (mem_orbit_orbitIndex' i)
  have hiter : ∀ N, ∀ α ∈ twAdjIter N, IsRoot TwistTag.E6.tag α ∧
      rootVec TwistTag.E6.tag K α ∈ S := by
    intro N
    induction N with
    | zero =>
      intro α hα
      simp only [twAdjIter, List.mem_singleton] at hα
      subst hα
      exact ⟨adjTop_E6.root, mem_orbitSpan_self (twAdj σ) _⟩
    | succ N ih =>
      intro β hβ
      simp only [twAdjIter, twAdjStep, List.mem_eraseDups, List.mem_append,
        List.mem_flatMap] at hβ
      rcases hβ with hβ | ⟨α, hα, hβ⟩
      · exact ih β hβ
      · obtain ⟨hαr, hαS⟩ := ih α hα
        rcases mem_twAdjMoves hβ with ⟨i, h1, h2, h3, rfl⟩ | ⟨a', rfl⟩
        · refine ⟨isRoot_iff_mem_artifactRoots.2 h3, ?_⟩
          have := hD i _ hαS (fun k hk => by
            rw [Bop_apply, coordR_rootVec hαr, if_neg, zero_smul]
            intro hαk
            by_cases hki : k = i
            · exact h2 (hki ▸ hαk)
            · exact not_isRoot_neg_add_of_orbit hk hki
                (hαk ▸ isRoot_iff_mem_artifactRoots.2 h3))
          rw [Dop_rootVec_of_ne adjHyp_E6 i hαr h1 h2] at this
          exact this
        · obtain ⟨hr, he⟩ := weylList_rootVec (K := K) (TwistTag.E6.orbitWord a') hαr
          refine ⟨hr, ?_⟩
          have h3 := hS (nC TwistTag.E6 K σ a') _ hαS
          rw [twAdj_nC σ a', he] at h3
          exact h3
  have hroot : ∀ α, IsRoot TwistTag.E6.tag α → rootVec TwistTag.E6.tag K α ∈ S := by
    intro α hα
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check Tag.E6) hα
    have hk' : k < Tag.E6.rootCount := by
      have := Tag.rootCertificate_length Tag.E6
      omega
    have := twAdj_reach
    simp only [twAdjReachCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
    exact (hiter 20 _ (this k hk')).2
  have hh : ∀ j, hVec TwistTag.E6.tag K j ∈ S := by
    intro j
    exact hVec_mem_of_stable_tw σ _ S hS (mem_orbit_orbitIndex' j)
      (hroot _ (isRoot_neg_single TwistTag.E6.tag j)) (hroot _ (isRoot_single TwistTag.E6.tag j))
  refine (Submodule.eq_top_iff').2 fun v => ?_
  refine adj_induction (P := fun v => v ∈ S) (zero_mem _) (fun _ _ => add_mem)
    (fun c _ h => Submodule.smul_mem _ c h) hh (fun α => ?_) v
  by_cases hα : IsRoot TwistTag.E6.tag α
  · exact hroot α hα
  · rw [rootVec_eq_zero hα]; exact zero_mem _

abbrev twA1 : Fin TwistTag.E6.foldedTag.rank := ⟨3, by decide⟩

theorem orbitIndex_node2 : TwistTag.E6.orbitIndex e6node2 = twA1 := by decide

theorem orbit_twA1_data : TwistTag.E6.orbitMin twA1 = e6node2 ∧ (TwistTag.E6.orbit twA1).card = 1 ∧
    TwistTag.E6.orbitWord twA1 = [e6node2] := by decide

theorem ne_node2_of_mem_orbit {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ twA1)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ TwistTag.E6.orbit a) : i ≠ e6node2 := by
  intro h
  have := (TwistTag.mem_orbit_iff TwistTag.E6).1 hi
  rw [h, orbitIndex_node2] at this
  exact ha this.symm

include hf hK hσ in
theorem fixU_le_line_adjTw {v : RootModule TwistTag.E6.tag K}
    (hv : v ∈ (twistedE6Datum hf hK σ hσ).fixU (twAdj σ)) :
    ∃ c : K, v = c • rootVec TwistTag.E6.tag K e6Theta := by
  refine ⟨coordR v e6Theta, fixed_E6 fun i => ?_⟩
  have hfix : ∀ c : orbitField TwistTag.E6 K σ (TwistTag.E6.orbitIndex i),
      twAdj σ (xC TwistTag.E6 K σ (TwistTag.E6.orbitIndex i) c) v = v := fun c =>
    ((twistedE6Datum hf hK σ hσ).mem_fixU _).1 hv
      (xC TwistTag.E6 K σ (TwistTag.E6.orbitIndex i) c)
      ((twistedE6Datum hf hK σ hσ).X_le _ (xC_mem_X _ c))
  by_cases hf2 : 2 ≤ f
  · have := Dop_mem_of_stable_tw hf hK σ hσ (TwistTag.E6.orbitIndex i) hf2 ⊥ v (fun c => by
      rw [hfix c, sub_self]
      exact Submodule.zero_mem _) (mem_orbit_orbitIndex' i)
    exact (Submodule.mem_bot K).1 this
  · exact Dop_eq_zero_of_fixed_tw1 hK σ hσ _ (by omega) v hfix (mem_orbit_orbitIndex' i)

include hf hK hσ in
theorem rootVec_theta_mem_fixU_tw :
    rootVec TwistTag.E6.tag K e6Theta ∈ (twistedE6Datum hf hK σ hσ).fixU (twAdj σ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (RootModule TwistTag.E6.tag K) := ⟨⟨rootVec TwistTag.E6.tag K e6Theta, 0,
    rootVec_theta_ne_zero⟩⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1
    ((twistedE6Datum hf hK σ hσ).fixU_ne_bot (p := 2) (twAdj σ))
  obtain ⟨c, rfl⟩ := fixU_le_line_adjTw hf hK σ hσ hx
  have hc : c ≠ 0 := by rintro rfl; exact hx0 (zero_smul _ _)
  have := Submodule.smul_mem _ c⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem xOp_theta_fix (i : Fin TwistTag.E6.tag.rank) (c : K) :
    xOp TwistTag.E6.tag K i c (rootVec TwistTag.E6.tag K e6Theta) =
      rootVec TwistTag.E6.tag K e6Theta :=
  xOp_rootVec_of_up_zero adjTop_E6.hyp i c adjTop_E6.root (adjTop_E6.ne_single i)
    (adjTop_E6.ne_neg i) (adjTop_E6.not_succ i)

theorem twAdj_xC_theta (c : orbitField TwistTag.E6 K σ a) :
    twAdj σ (xC TwistTag.E6 K σ a c) (rootVec TwistTag.E6.tag K e6Theta) =
      rootVec TwistTag.E6.tag K e6Theta := by
  rw [twAdj_xC]
  have : ∀ l : List (Module.End K (RootModule TwistTag.E6.tag K)),
      (∀ x ∈ l, x (rootVec TwistTag.E6.tag K e6Theta) = rootVec TwistTag.E6.tag K e6Theta) →
        l.prod (rootVec TwistTag.E6.tag K e6Theta) = rootVec TwistTag.E6.tag K e6Theta := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x l ih =>
      intro h
      rw [List.prod_cons, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
        h x List.mem_cons_self]
  refine this _ ?_
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact xOp_theta_fix _ _

theorem weylList_theta (l : List (Fin TwistTag.E6.tag.rank)) (hl : ∀ i ∈ l, i ≠ e6node2) :
    l.foldr (reflect TwistTag.E6.tag) e6Theta = e6Theta := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldr_cons, ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))]
    exact adjTop_E6.reflect_ne j (hl j List.mem_cons_self)

theorem twAdj_nC_theta (ha : a ≠ twA1) :
    twAdj σ (nC TwistTag.E6 K σ a) (rootVec TwistTag.E6.tag K e6Theta) =
      rootVec TwistTag.E6.tag K e6Theta := by
  rw [twAdj_nC]
  have h := (weylList_rootVec (K := K) (TwistTag.E6.orbitWord a) adjTop_E6.root).2
  rw [h, weylList_theta _ (fun i hi => ne_node2_of_mem_orbit ha
    ((TwistTag.mem_orbitWord (t := TwistTag.E6)).1 hi))]

@[expose] def hkOp (k : ℕ) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    Module.End K (RootModule TwistTag.E6.tag K) :=
  (torusElt TwistTag.E6.tag K ((TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a))
    (Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom u) :
      (Module.End K (RootModule TwistTag.E6.tag K))ˣ)

theorem twAdj_hC (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    twAdj σ (hC TwistTag.E6 K σ a u) =
      ((List.range (TwistTag.E6.orbit a).card).map fun k => hkOp σ a k u).prod := by
  rw [twAdj_apply]
  change (((orbitH TwistTag.E6 K σ a u : ModGL TwistTag.E6.tag K)) :
    Module.End K (RootModule TwistTag.E6.tag K)) = _
  rw [coe_orbitH, ← Units.coeHom_apply, map_list_prod, List.map_map]
  rfl

theorem hkOp_theta (k : ℕ) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    hkOp σ a k u (rootVec TwistTag.E6.tag K e6Theta) =
      ((Units.map ((σ ^ k).comp (orbitField TwistTag.E6 K σ a).subtype).toMonoidHom u ^
        (if (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin a) = e6node2 then (1 : ℤ) else 0) :
          Kˣ) : K) • rootVec TwistTag.E6.tag K e6Theta := by
  unfold hkOp
  rw [torusElt_rootVec _ _ adjTop_E6.root, adjTop_E6.weight]

theorem list_prod_fix_theta (l : List (Module.End K (RootModule TwistTag.E6.tag K)))
    (h : ∀ x ∈ l, x (rootVec TwistTag.E6.tag K e6Theta) = rootVec TwistTag.E6.tag K e6Theta) :
    l.prod (rootVec TwistTag.E6.tag K e6Theta) = rootVec TwistTag.E6.tag K e6Theta := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih (fun z hz => h z (List.mem_cons_of_mem _ hz)),
      h x List.mem_cons_self]

theorem twAdj_hC_theta (ha : a ≠ twA1) (u : (orbitField TwistTag.E6 K σ a)ˣ) :
    twAdj σ (hC TwistTag.E6 K σ a u) (rootVec TwistTag.E6.tag K e6Theta) =
      rootVec TwistTag.E6.tag K e6Theta := by
  rw [twAdj_hC]
  refine list_prod_fix_theta _ ?_
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  rw [hkOp_theta, if_neg (ne_node2_of_mem_orbit ha
    (TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem a) k))]
  simp

@[expose] def twChiAdj (g : ↥(graphFixedRootGroup TwistTag.E6 K σ)) : K :=
  coordR (twAdj σ g (rootVec TwistTag.E6.tag K e6Theta)) e6Theta

theorem twChiAdj_theta_fix {g : ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (h : twAdj σ g (rootVec TwistTag.E6.tag K e6Theta) = rootVec TwistTag.E6.tag K e6Theta) :
    twChiAdj σ g = 1 := by
  unfold twChiAdj
  rw [h, coordR_rootVec adjTop_E6.root, if_pos rfl]

theorem twChiAdj_hC_a1 (u : (orbitField TwistTag.E6 K σ twA1)ˣ) :
    twChiAdj σ (hC TwistTag.E6 K σ twA1 u) = ((u : orbitField TwistTag.E6 K σ twA1) : K) := by
  unfold twChiAdj
  rw [twAdj_hC, orbit_twA1_data.2.1]
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [hkOp_theta, orbit_twA1_data.1]
  simp [coordR_smul, coordR_rootVec adjTop_E6.root]

theorem twAdj_xnC_a1 (c : orbitField TwistTag.E6 K σ twA1) :
    twAdj σ (xC TwistTag.E6 K σ twA1 c * nC TwistTag.E6 K σ twA1)
        (rootVec TwistTag.E6.tag K e6Theta) =
      rootVec TwistTag.E6.tag K (e6Theta - Pi.single e6node2 1) +
        (c : K) • rootVec TwistTag.E6.tag K e6Theta := by
  rw [map_mul, Module.End.mul_apply, twAdj_nC, orbit_twA1_data.2.2]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [weylElt_one_rootVec' _ adjTop_E6.root, adjTop_E6.reflect_node, twAdj_xC_card_one σ twA1
    orbit_twA1_data.2.1, xkOp]
  simp only [pow_zero, Equiv.Perm.coe_one, id_eq, RingHom.coe_one]
  rw [orbit_twA1_data.1]
  have h := xOp_rootVec_of_up_one adjTop_E6.hyp e6node2 (c : K) adjTop_E6.root_sub
    adjTop_E6.sub_ne_single adjTop_E6.sub_ne_neg (by rw [sub_add_cancel]; exact adjTop_E6.root)
  rw [sub_add_cancel] at h
  exact h

include hf hK hσ in
theorem twAdj_H (h : ↥(graphFixedRootGroup TwistTag.E6 K σ))
    (hh : h ∈ (twistedE6Datum hf hK σ hσ).H) :
    twAdj σ h (rootVec TwistTag.E6.tag K e6Theta) =
      twChiAdj σ h • rootVec TwistTag.E6.tag K e6Theta := by
  obtain ⟨c, hc⟩ := fixU_le_line_adjTw hf hK σ hσ
    ((twistedE6Datum hf hK σ hσ).act_H_mem_fixU (twAdj σ) hh
      (rootVec_theta_mem_fixU_tw hf hK σ hσ))
  have : twChiAdj σ h = c := by
    unfold twChiAdj
    rw [hc, coordR_smul, coordR_rootVec adjTop_E6.root, if_pos rfl, mul_one]
  rw [this, hc]

include hf hK hσ in
theorem twAdj_heckeT_zero (ha : a ≠ twA1) :
    (twistedE6Datum hf hK σ hσ).heckeT (twAdj σ) a (rootVec TwistTag.E6.tag K e6Theta) = 0 := by
  have : Fintype (orbitField TwistTag.E6 K σ a) := Fintype.ofFinite _
  rw [twistedE6Datum, heckeT_twistedDatum]
  have hterm : ∀ c : orbitField TwistTag.E6 K σ a,
      twAdj σ (xC TwistTag.E6 K σ a c * nC TwistTag.E6 K σ a)
        (rootVec TwistTag.E6.tag K e6Theta) = rootVec TwistTag.E6.tag K e6Theta := by
    intro c
    rw [map_mul, Module.End.mul_apply, twAdj_nC_theta σ a ha, twAdj_xC_theta]
  rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K,
    (CharP.cast_eq_zero_iff K 2 _).2 (card_orbitField_even hf hK σ hσ a), zero_smul]

include hf hK hσ in
theorem twAdj_isTwType :
    IsTwType 2 e6LongestData (surjective_of_finite σ) (card_orbitField_e6 hf hK σ hσ) (twAdj σ)
      (rootVec TwistTag.E6.tag K e6Theta) (twChiAdj σ) (Finset.univ.erase twA1) := by
  refine ⟨rootVec_theta_mem_fixU_tw hf hK σ hσ, rootVec_theta_ne_zero, twAdj_H hf hK σ hσ,
    fun a => ?_⟩
  by_cases ha : a = twA1
  · subst ha
    refine ⟨fun h => absurd rfl (Finset.mem_erase.1 h).1, fun h => ?_⟩
    exfalso
    obtain ⟨h1, h2⟩ := h
    have : Fintype (orbitField TwistTag.E6 K σ twA1) := Fintype.ofFinite _
    have h1' : ∀ u : (orbitField TwistTag.E6 K σ twA1)ˣ, u = 1 := fun u => by
      have := h1 u
      rw [twChiAdj_hC_a1] at this
      exact Units.ext (Subtype.ext this)
    have h1'' : ∀ u : (orbitField TwistTag.E6 K σ twA1)ˣ, (u : orbitField TwistTag.E6 K σ twA1) = 1 :=
      fun u => by rw [h1' u]; rfl
    have hsum := sum_eq_one_of_units_eq_one h1''
    have hT : (twistedE6Datum hf hK σ hσ).heckeT (twAdj σ) twA1
        (rootVec TwistTag.E6.tag K e6Theta) =
        (((∑ c : orbitField TwistTag.E6 K σ twA1, c : orbitField TwistTag.E6 K σ twA1) : K)) •
          rootVec TwistTag.E6.tag K e6Theta := by
      rw [twistedE6Datum, heckeT_twistedDatum]
      simp only [twAdj_xnC_a1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul K,
        (CharP.cast_eq_zero_iff K 2 _).2 (card_orbitField_even hf hK σ hσ twA1), zero_smul,
        zero_add, ← Finset.sum_smul]
      simp
    have h3 := hT.symm.trans h2
    rw [hsum] at h3
    simp at h3
    exact rootVec_theta_ne_zero h3
  · refine ⟨fun _ => ⟨fun u => ?_, twAdj_heckeT_zero hf hK σ hσ a ha⟩,
      fun _ => Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩⟩
    exact twChiAdj_theta_fix σ (twAdj_hC_theta σ a ha u)

end Tw

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
