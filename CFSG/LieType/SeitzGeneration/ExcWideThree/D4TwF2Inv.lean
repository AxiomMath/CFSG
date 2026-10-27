module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Form

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Inv


open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Chain
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Form
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Span

@[expose] noncomputable def Bf (K : Type) [Field K] (u w : RootModule Tag.D4 K) : K :=
  Bzk (fun a => pcoord K u a) (fun b => pcoord K w b)

section Lemmas

variable {K : Type} [Field K]

theorem pcoord_add' (u v : RootModule Tag.D4 K) (a : ℕ) : pcoord K (u + v) a = pcoord K u a + pcoord K v a :=
  map_add (posCoord Tag.D4 K a) u v

theorem pcoord_smul' (c : K) (u : RootModule Tag.D4 K) (a : ℕ) : pcoord K (c • u) a = c * pcoord K u a :=
  by rw [pcoord, map_smul, smul_eq_mul]; rfl

theorem Bf_add_left (u v w : RootModule Tag.D4 K) : Bf K (u + v) w = Bf K u w + Bf K v w := by
  unfold Bf
  have h : (fun a => pcoord K (u + v) a) = fun a => pcoord K u a + pcoord K v a :=
    funext fun a => pcoord_add' u v a
  rw [h, Bzk_add_left]

theorem Bf_smul_left (c : K) (u w : RootModule Tag.D4 K) : Bf K (c • u) w = c * Bf K u w := by
  unfold Bf
  have h : (fun a => pcoord K (c • u) a) = fun a => c * pcoord K u a :=
    funext fun a => pcoord_smul' c u a
  rw [h, Bzk_smul_left]

theorem Bf_add_right (u v w : RootModule Tag.D4 K) : Bf K u (v + w) = Bf K u v + Bf K u w := by
  unfold Bf
  have h : (fun b => pcoord K (v + w) b) = fun b => pcoord K v b + pcoord K w b :=
    funext fun b => pcoord_add' v w b
  rw [h, Bzk_add_right]

theorem Bf_smul_right (c : K) (u w : RootModule Tag.D4 K) : Bf K u (c • w) = c * Bf K u w := by
  unfold Bf
  have h : (fun b => pcoord K (c • w) b) = fun b => c * pcoord K w b :=
    funext fun b => pcoord_smul' c w b
  rw [h, Bzk_smul_right]

theorem Bf_sum_left {ι : Type} (s : Finset ι) (f : ι → RootModule Tag.D4 K) (w : RootModule Tag.D4 K) :
    Bf K (∑ i ∈ s, f i) w = ∑ i ∈ s, Bf K (f i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; unfold Bf; simp [Bzk, pcoord, map_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Bf_add_left, ih]

theorem Bf_sum_right {ι : Type} (s : Finset ι) (f : ι → RootModule Tag.D4 K) (u : RootModule Tag.D4 K) :
    Bf K u (∑ i ∈ s, f i) = ∑ i ∈ s, Bf K u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; unfold Bf; simp [Bzk, pcoord, map_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Bf_add_right, ih]

theorem vec_eq_finset_sum (u : RootModule Tag.D4 K) :
    u = ∑ p ∈ Finset.range 28, pcoord K u p • posVec Tag.D4 K p := by
  refine eq_of_pcoord _ _ fun q hq => ?_
  have hd : dim Tag.D4 = 28 := by decide +kernel
  rw [hd] at hq
  show pcoord K u q = posCoord Tag.D4 K q (∑ p ∈ Finset.range 28, pcoord K u p • posVec Tag.D4 K p)
  rw [map_sum]
  have hterm : ∀ p ∈ Finset.range 28, posCoord Tag.D4 K q (pcoord K u p • posVec Tag.D4 K p) =
      if q = p then pcoord K u p else 0 := by
    intro p hp
    rw [Finset.mem_range] at hp
    rw [map_smul, posCoord_posVec (show p < dim Tag.D4 by rw [hd]; exact hp), smul_eq_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hq)]

theorem Bf_basis (p q : ℕ) (hp : p < 28) (hq : q < 28) :
    Bf K (posVec Tag.D4 K p) (posVec Tag.D4 K q) = (gramZ p q : K) := by
  unfold Bf
  have hdp : p < dim Tag.D4 := by
    have : dim Tag.D4 = 28 := by decide +kernel
    omega
  have hdq : q < dim Tag.D4 := by
    have : dim Tag.D4 = 28 := by decide +kernel
    omega
  rw [pcoord_posVec_fun p hdp, pcoord_posVec_fun q hdq, Bzk_delta p q hp hq]

theorem Bf_eq_of_basis (L : Module.End K (RootModule Tag.D4 K))
    (hL : ∀ p q : ℕ, p < 28 → q < 28 →
      Bf K (L (posVec Tag.D4 K p)) (L (posVec Tag.D4 K q)) = Bf K (posVec Tag.D4 K p) (posVec Tag.D4 K q))
    (u w : RootModule Tag.D4 K) : Bf K (L u) (L w) = Bf K u w := by
  have expand : ∀ (M : Module.End K (RootModule Tag.D4 K)) (α β : ℕ → K),
      Bf K (M (∑ p ∈ Finset.range 28, α p • posVec Tag.D4 K p))
        (M (∑ q ∈ Finset.range 28, β q • posVec Tag.D4 K q)) =
        ∑ p ∈ Finset.range 28, ∑ q ∈ Finset.range 28,
          α p * β q * Bf K (M (posVec Tag.D4 K p)) (M (posVec Tag.D4 K q)) := by
    intro M α β
    simp only [map_sum, map_smul]
    rw [Bf_sum_left]
    apply Finset.sum_congr rfl
    intro p _
    rw [Bf_smul_left, Bf_sum_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Bf_smul_right]
    ring
  have h1 := expand L (fun p => pcoord K u p) (fun q => pcoord K w q)
  have h2 := expand 1 (fun p => pcoord K u p) (fun q => pcoord K w q)
  rw [← vec_eq_finset_sum u, ← vec_eq_finset_sum w] at h1
  rw [← vec_eq_finset_sum u, ← vec_eq_finset_sum w] at h2
  simp only [Module.End.one_apply] at h2
  rw [h1]
  refine Eq.trans (Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_) h2.symm
  rw [hL p q (Finset.mem_range.1 hp) (Finset.mem_range.1 hq)]

theorem xOp_eq_endHom_pos (i : Fin Tag.D4.rank) (c : K) :
    endHom K (xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) c) = xOp Tag.D4 K i c := by
  rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.D4).elt_simple]

theorem xOp_eq_endHom_neg (i : Fin Tag.D4.rank) (c : K) :
    endHom K (xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) c) = yOp Tag.D4 K i c := by
  rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily Tag.D4).elt_neg_simple]

theorem Bf_inv_pos [CharP K 2] (i : ℕ) (hi : i < 4) (c : K) (u w : RootModule Tag.D4 K) :
    Bf K (endHom K (xPar (rootOperatorFamily Tag.D4) (Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) u)
      (endHom K (xPar (rootOperatorFamily Tag.D4) (Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) w) =
      Bf K u w := by
  refine Bf_eq_of_basis _ (fun p q hp hq => ?_) u w
  rw [Bf_basis p q hp hq]
  unfold Bf
  exact Bzk_basis_of_formula i hi true c p q hp hq
    (fun r => fun a => pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) (posVec Tag.D4 K r)) a)
    (fun r hr => pcoord_endHom_basis_pos i hi c r hr)
    (fun d hd => gram_inv_int i hi true p hp q hq d hd)

theorem Bf_inv_neg [CharP K 2] (i : ℕ) (hi : i < 4) (c : K) (u w : RootModule Tag.D4 K) :
    Bf K (endHom K (xPar (rootOperatorFamily Tag.D4) (-Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) u)
      (endHom K (xPar (rootOperatorFamily Tag.D4) (-Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) w) =
      Bf K u w := by
  refine Bf_eq_of_basis _ (fun p q hp hq => ?_) u w
  rw [Bf_basis p q hp hq]
  unfold Bf
  exact Bzk_basis_of_formula i hi false c p q hp hq
    (fun r => fun a => pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
      (-Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) (posVec Tag.D4 K r)) a)
    (fun r hr => pcoord_endHom_basis_neg i hi c r hr)
    (fun d hd => gram_inv_int i hi false p hp q hq d hd)

@[expose] def Bsub (K : Type) [Field K] [CharP K 2] : Subgroup (adjointGroup Tag.D4 K) where
  carrier := {g | ∀ u w : RootModule Tag.D4 K, Bf K (endHom K g u) (endHom K g w) = Bf K u w}
  one_mem' := fun u w => by
    simp only [map_one, Module.End.one_apply]
  mul_mem' := fun {g h} hg hh u w => by
    simp only [map_mul, Module.End.mul_apply]
    rw [hg, hh]
  inv_mem' := fun {g} hg u w => by
    have e : ∀ x : RootModule Tag.D4 K, endHom K g (endHom K g⁻¹ x) = x := fun x => by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h := hg (endHom K g⁻¹ u) (endHom K g⁻¹ w)
    rw [e, e] at h
    exact h.symm

theorem Bf_inv_all [CharP K 2] (g : adjointGroup Tag.D4 K) (u w : RootModule Tag.D4 K) :
    Bf K (endHom K g u) (endHom K g w) = Bf K u w := by
  have hsub : (⊤ : Subgroup (adjointGroup Tag.D4 K)) ≤ Bsub K := by
    set S : Set (ModGL Tag.D4 K) := {g | ∃ (i : Fin Tag.D4.rank) (c : K),
      (g : Module.End K (RootModule Tag.D4 K)) = xOp Tag.D4 K i c ∨
        (g : Module.End K (RootModule Tag.D4 K)) = yOp Tag.D4 K i c} with hSdef
    have hcl : Subgroup.closure (((↑) : ↥(adjointGroup Tag.D4 K) → ModGL Tag.D4 K) ⁻¹' S) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [← hcl, Subgroup.closure_le]
    rintro h ⟨i, c, hg | hg⟩
    · have hm : h ∈ Bsub K := by
        show ∀ u w : RootModule Tag.D4 K, Bf K (endHom K h u) (endHom K h w) = Bf K u w
        intro u w
        rw [show endHom K h = xOp Tag.D4 K i c from hg, ← xOp_eq_endHom_pos]
        exact Bf_inv_pos i.1 i.2 c u w
      exact hm
    · have hm : h ∈ Bsub K := by
        show ∀ u w : RootModule Tag.D4 K, Bf K (endHom K h u) (endHom K h w) = Bf K u w
        intro u w
        rw [show endHom K h = yOp Tag.D4 K i c from hg, ← xOp_eq_endHom_neg]
        exact Bf_inv_neg i.1 i.2 c u w
      exact hm
  exact hsub (Subgroup.mem_top g) u w

end Lemmas

end CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Inv

end
