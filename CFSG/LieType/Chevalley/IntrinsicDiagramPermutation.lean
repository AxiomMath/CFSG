module

public import CFSG.LieType.Chevalley.IntrinsicSimplePairs
public import CFSG.LieType.Chevalley.A2Commutator
public import CFSG.LieType.Chevalley.SimplyLacedCommutation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem card_adj_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (π : Equiv.Perm (Fin n))
    (hadj : ∀ i j, A (π i) (π j) = A i j) (i : Fin n) :
    (Finset.univ.filter fun j => A (π i) j = -1).card =
      (Finset.univ.filter fun j => A i j = -1).card := by
  refine Finset.card_equiv π.symm fun j => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hadj i (π.symm j), Equiv.apply_symm_apply]

theorem perm_eq_one_of_cartanE8 (π : Equiv.Perm (Fin 8))
    (hadj : ∀ i j, Tag.cartanE 8 (π i) (π j) = Tag.cartanE 8 i j) : π = 1 := by
  have hdeg := card_adj_perm (Tag.cartanE 8) π hadj
  have e : ∀ i j, Tag.cartanE 8 i j = -1 → Tag.cartanE 8 (π i) (π j) = -1 := fun i j h => by
    rw [hadj]; exact h
  have hne : ∀ i j, i ≠ j → π i ≠ π j := fun i j h => π.injective.ne h
  have h3 : π 3 = 3 := by
    have key : ∀ v : Fin 8, (Finset.univ.filter fun j => Tag.cartanE 8 v j = -1).card = 3 →
        v = 3 := by decide
    exact key _ ((hdeg 3).trans (by decide))
  have h1 : π 1 = 1 := by
    have key : ∀ v : Fin 8, (Finset.univ.filter fun j => Tag.cartanE 8 v j = -1).card = 1 →
        Tag.cartanE 8 v 3 = -1 → v = 1 := by decide
    exact key _ ((hdeg 1).trans (by decide)) (h3 ▸ e 1 3 (by decide))
  have h2 : π 2 = 2 := by
    have key : ∀ v : Fin 8, Tag.cartanE 8 v 3 = -1 → v ≠ 1 → v = 2 ∨ v = 4 := by decide
    rcases key _ (h3 ▸ e 2 3 (by decide)) (h1 ▸ hne 2 1 (by decide)) with h | h
    · exact h
    · exfalso
      have key0 : ∀ v : Fin 8, Tag.cartanE 8 v 4 = -1 → v ≠ 3 → v = 5 := by decide
      have h0 := key0 _ (h ▸ e 0 2 (by decide)) (h3 ▸ hne 0 3 (by decide))
      have hd := hdeg 0
      rw [h0] at hd
      exact absurd hd (by decide)
  have h0 : π 0 = 0 := by
    have key : ∀ v : Fin 8, Tag.cartanE 8 v 2 = -1 → v ≠ 3 → v = 0 := by decide
    exact key _ (h2 ▸ e 0 2 (by decide)) (h3 ▸ hne 0 3 (by decide))
  have h4 : π 4 = 4 := by
    have key : ∀ v : Fin 8, Tag.cartanE 8 v 3 = -1 → v ≠ 1 → v ≠ 2 → v = 4 := by decide
    exact key _ (h3 ▸ e 4 3 (by decide)) (h1 ▸ hne 4 1 (by decide)) (h2 ▸ hne 4 2 (by decide))
  have h5 : π 5 = 5 := by
    have key : ∀ v : Fin 8, Tag.cartanE 8 v 4 = -1 → v ≠ 3 → v = 5 := by decide
    exact key _ (h4 ▸ e 5 4 (by decide)) (h3 ▸ hne 5 3 (by decide))
  have h6 : π 6 = 6 := by
    have key : ∀ v : Fin 8, Tag.cartanE 8 v 5 = -1 → v ≠ 4 → v = 6 := by decide
    exact key _ (h5 ▸ e 6 5 (by decide)) (h4 ▸ hne 6 4 (by decide))
  have h7 : π 7 = 7 := by
    have key : ∀ v : Fin 8, Tag.cartanE 8 v 6 = -1 → v ≠ 5 → v = 7 := by decide
    exact key _ (h6 ▸ e 7 6 (by decide)) (h5 ▸ hne 7 5 (by decide))
  ext i
  fin_cases i
  exacts [congrArg Fin.val h0, congrArg Fin.val h1, congrArg Fin.val h2, congrArg Fin.val h3,
    congrArg Fin.val h4, congrArg Fin.val h5, congrArg Fin.val h6, congrArg Fin.val h7]

theorem perm_eq_one_of_cartanE7 (π : Equiv.Perm (Fin 7))
    (hadj : ∀ i j, Tag.cartanE 7 (π i) (π j) = Tag.cartanE 7 i j) : π = 1 := by
  have hdeg := card_adj_perm (Tag.cartanE 7) π hadj
  have e : ∀ i j, Tag.cartanE 7 i j = -1 → Tag.cartanE 7 (π i) (π j) = -1 := fun i j h => by
    rw [hadj]; exact h
  have hne : ∀ i j, i ≠ j → π i ≠ π j := fun i j h => π.injective.ne h
  have h3 : π 3 = 3 := by
    have key : ∀ v : Fin 7, (Finset.univ.filter fun j => Tag.cartanE 7 v j = -1).card = 3 →
        v = 3 := by decide
    exact key _ ((hdeg 3).trans (by decide))
  have h1 : π 1 = 1 := by
    have key : ∀ v : Fin 7, (Finset.univ.filter fun j => Tag.cartanE 7 v j = -1).card = 1 →
        Tag.cartanE 7 v 3 = -1 → v = 1 := by decide
    exact key _ ((hdeg 1).trans (by decide)) (h3 ▸ e 1 3 (by decide))
  have h2 : π 2 = 2 := by
    have key : ∀ v : Fin 7, Tag.cartanE 7 v 3 = -1 → v ≠ 1 → v = 2 ∨ v = 4 := by decide
    rcases key _ (h3 ▸ e 2 3 (by decide)) (h1 ▸ hne 2 1 (by decide)) with h | h
    · exact h
    · exfalso
      have key0 : ∀ v : Fin 7, Tag.cartanE 7 v 4 = -1 → v ≠ 3 → v = 5 := by decide
      have h0 := key0 _ (h ▸ e 0 2 (by decide)) (h3 ▸ hne 0 3 (by decide))
      have hd := hdeg 0
      rw [h0] at hd
      exact absurd hd (by decide)
  have h0 : π 0 = 0 := by
    have key : ∀ v : Fin 7, Tag.cartanE 7 v 2 = -1 → v ≠ 3 → v = 0 := by decide
    exact key _ (h2 ▸ e 0 2 (by decide)) (h3 ▸ hne 0 3 (by decide))
  have h4 : π 4 = 4 := by
    have key : ∀ v : Fin 7, Tag.cartanE 7 v 3 = -1 → v ≠ 1 → v ≠ 2 → v = 4 := by decide
    exact key _ (h3 ▸ e 4 3 (by decide)) (h1 ▸ hne 4 1 (by decide)) (h2 ▸ hne 4 2 (by decide))
  have h5 : π 5 = 5 := by
    have key : ∀ v : Fin 7, Tag.cartanE 7 v 4 = -1 → v ≠ 3 → v = 5 := by decide
    exact key _ (h4 ▸ e 5 4 (by decide)) (h3 ▸ hne 5 3 (by decide))
  have h6 : π 6 = 6 := by
    have key : ∀ v : Fin 7, Tag.cartanE 7 v 5 = -1 → v ≠ 4 → v = 6 := by decide
    exact key _ (h5 ▸ e 6 5 (by decide)) (h4 ▸ hne 6 4 (by decide))
  ext i
  fin_cases i
  exacts [congrArg Fin.val h0, congrArg Fin.val h1, congrArg Fin.val h2, congrArg Fin.val h3,
    congrArg Fin.val h4, congrArg Fin.val h5, congrArg Fin.val h6]

theorem perm_cases_of_cartanE6 (π : Equiv.Perm (Fin 6))
    (hadj : ∀ i j, Tag.cartanE 6 (π i) (π j) = Tag.cartanE 6 i j) :
    π = 1 ∨ π = Equiv.swap 0 5 * Equiv.swap 2 4 := by
  have hdeg := card_adj_perm (Tag.cartanE 6) π hadj
  have e : ∀ i j, Tag.cartanE 6 i j = -1 → Tag.cartanE 6 (π i) (π j) = -1 := fun i j h => by
    rw [hadj]; exact h
  have hne : ∀ i j, i ≠ j → π i ≠ π j := fun i j h => π.injective.ne h
  have h3 : π 3 = 3 := by
    have key : ∀ v : Fin 6, (Finset.univ.filter fun j => Tag.cartanE 6 v j = -1).card = 3 →
        v = 3 := by decide
    exact key _ ((hdeg 3).trans (by decide))
  have h1 : π 1 = 1 := by
    have key : ∀ v : Fin 6, (Finset.univ.filter fun j => Tag.cartanE 6 v j = -1).card = 1 →
        Tag.cartanE 6 v 3 = -1 → v = 1 := by decide
    exact key _ ((hdeg 1).trans (by decide)) (h3 ▸ e 1 3 (by decide))
  have key2 : ∀ v : Fin 6, Tag.cartanE 6 v 3 = -1 → v ≠ 1 → v = 2 ∨ v = 4 := by decide
  rcases key2 _ (h3 ▸ e 2 3 (by decide)) (h1 ▸ hne 2 1 (by decide)) with h2 | h2
  · left
    have h0 : π 0 = 0 := by
      have key : ∀ v : Fin 6, Tag.cartanE 6 v 2 = -1 → v ≠ 3 → v = 0 := by decide
      exact key _ (h2 ▸ e 0 2 (by decide)) (h3 ▸ hne 0 3 (by decide))
    have h4 : π 4 = 4 := by
      have key : ∀ v : Fin 6, Tag.cartanE 6 v 3 = -1 → v ≠ 1 → v ≠ 2 → v = 4 := by decide
      exact key _ (h3 ▸ e 4 3 (by decide)) (h1 ▸ hne 4 1 (by decide))
        (h2 ▸ hne 4 2 (by decide))
    have h5 : π 5 = 5 := by
      have key : ∀ v : Fin 6, Tag.cartanE 6 v 4 = -1 → v ≠ 3 → v = 5 := by decide
      exact key _ (h4 ▸ e 5 4 (by decide)) (h3 ▸ hne 5 3 (by decide))
    ext i
    fin_cases i
    exacts [congrArg Fin.val h0, congrArg Fin.val h1, congrArg Fin.val h2, congrArg Fin.val h3,
      congrArg Fin.val h4, congrArg Fin.val h5]
  · right
    have h0 : π 0 = 5 := by
      have key : ∀ v : Fin 6, Tag.cartanE 6 v 4 = -1 → v ≠ 3 → v = 5 := by decide
      exact key _ (h2 ▸ e 0 2 (by decide)) (h3 ▸ hne 0 3 (by decide))
    have h4 : π 4 = 2 := by
      have key : ∀ v : Fin 6, Tag.cartanE 6 v 3 = -1 → v ≠ 1 → v ≠ 4 → v = 2 := by decide
      exact key _ (h3 ▸ e 4 3 (by decide)) (h1 ▸ hne 4 1 (by decide))
        (h2 ▸ hne 4 2 (by decide))
    have h5 : π 5 = 0 := by
      have key : ∀ v : Fin 6, Tag.cartanE 6 v 2 = -1 → v ≠ 3 → v = 0 := by decide
      exact key _ (h4 ▸ e 5 4 (by decide)) (h3 ▸ hne 5 3 (by decide))
    ext i
    fin_cases i
    exacts [congrArg Fin.val h0, congrArg Fin.val h1, congrArg Fin.val h2, congrArg Fin.val h3,
      congrArg Fin.val h4, congrArg Fin.val h5]

variable {τ : Tag} {K : Type} [Field K]

theorem cartanE6_symm (i j : Fin 6) : Tag.cartanE 6 i j = Tag.cartanE 6 j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem cartanE7_symm (i j : Fin 7) : Tag.cartanE 7 i j = Tag.cartanE 7 j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem cartanE8_symm (i j : Fin 8) : Tag.cartanE 8 i j = Tag.cartanE 8 j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem cartanE6_offdiag (i j : Fin 6) (hij : i ≠ j) :
    Tag.cartanE 6 i j = 0 ∨ Tag.cartanE 6 i j = -1 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem cartanE7_offdiag (i j : Fin 7) (hij : i ≠ j) :
    Tag.cartanE 7 i j = 0 ∨ Tag.cartanE 7 i j = -1 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem cartanE8_offdiag (i j : Fin 8) (hij : i ≠ j) :
    Tag.cartanE 8 i j = 0 ∨ Tag.cartanE 8 i j = -1 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem cartan_symm_of_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i j : Fin τ.rank) :
    τ.cartan i j = τ.cartan j i := by
  rcases hτ with rfl | rfl | rfl
  exacts [cartanE6_symm i j, cartanE7_symm i j, cartanE8_symm i j]

theorem cartan_offdiag_of_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {i j : Fin τ.rank} (hij : i ≠ j) :
    τ.cartan i j = 0 ∨ τ.cartan i j = -1 := by
  rcases hτ with rfl | rfl | rfl
  exacts [cartanE6_offdiag i j hij, cartanE7_offdiag i j hij, cartanE8_offdiag i j hij]

theorem symmetrizedCartan_eq_of_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    τ.symmetrizedCartan = τ.cartan := by
  rcases hτ with rfl | rfl | rfl <;> simp [Tag.symmetrizedCartan, Tag.symmetrizer]

open Matrix in
theorem simplePos_commute_iff
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {i j : Fin τ.rank}
    (hij : i ≠ j) :
    (∀ x ∈ simplePosSubgroup τ K i, ∀ y ∈ simplePosSubgroup τ K j, Commute x y) ↔
      τ.cartan i j ≠ -1 := by
  constructor
  · intro h hc
    have hcji : τ.cartan j i = -1 := by rw [← cartan_symm_of_E hτ]; exact hc
    have h1 := congrArg Subtype.val ((h (adjX τ K i 1) ⟨1, rfl⟩ (adjX τ K j 1) ⟨1, rfl⟩).eq)
    change xUnit τ K i 1 * xUnit τ K j 1 = xUnit τ K j 1 * xUnit τ K i 1 at h1
    have h2 := (a2_simple_root_commutatorElement K hc hcji 1 1).1
    rw [commutatorElement_eq_one_iff_mul_comm.2 h1, mul_one] at h2
    have h3 : xUnit τ K j 1 = xUnit τ K j 0 := by
      rw [xUnit_zero]
      have := congrArg (fun g => (weylElt τ K i 1)⁻¹ * g * weylElt τ K i 1) h2
      simpa [mul_assoc] using this.symm
    exact one_ne_zero (adjX_injective j (Subtype.ext h3))
  · intro hc x hx y hy
    have h0 : τ.cartan i j = 0 := (cartan_offdiag_of_E hτ hij).resolve_right hc
    obtain ⟨c, hcx⟩ := hx
    obtain ⟨d, hdy⟩ := hy
    have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
    have hform : (Pi.single i 1 : Fin τ.rank → ℤ) ⬝ᵥ
        (τ.symmetrizedCartan *ᵥ Pi.single j 1) = 0 := by
      rw [single_dotProduct, one_mul, mulVec_single_one, symmetrizedCartan_eq_of_E hτ]
      exact h0
    have hxy := (simply_laced_orthogonal_root_commutation τ hτ').2 K _ _ (isRoot_single τ i)
      (isRoot_single τ j) hform (xUnit τ K i c) (mem_rootSubgroup.2 ⟨c, by rw [pinnedX_single]⟩)
      (xUnit τ K j d) (mem_rootSubgroup.2 ⟨d, by rw [pinnedX_single]⟩)
    apply Subtype.ext
    change (x : ModGL τ K) * y = y * x
    rw [hcx, hdy]
    exact hxy

theorem commute_simplePos_transport
    {α : MulAut (adjointGroup τ K)} {i j i' j' : Fin τ.rank}
    (hi : (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K i')
    (hj : (simplePosSubgroup τ K j).map α.toMonoidHom = simplePosSubgroup τ K j') :
    (∀ x ∈ simplePosSubgroup τ K i, ∀ y ∈ simplePosSubgroup τ K j, Commute x y) ↔
      (∀ x ∈ simplePosSubgroup τ K i', ∀ y ∈ simplePosSubgroup τ K j', Commute x y) := by
  constructor
  · intro h x hx y hy
    rw [← hi] at hx
    rw [← hj] at hy
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨y0, hy0, rfl⟩ := hy
    exact (h x0 hx0 y0 hy0).map α.toMonoidHom
  · intro h x hx y hy
    have h1 := h (α x) (hi ▸ ⟨x, hx, rfl⟩) (α y) (hj ▸ ⟨y, hy, rfl⟩)
    have h2 := h1.map α.symm.toMonoidHom
    simpa using h2

theorem cartan_perm_eq
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {α : MulAut (adjointGroup τ K)}
    {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i, (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K (π i))
    (i j : Fin τ.rank) : τ.cartan (π i) (π j) = τ.cartan i j := by
  by_cases hij : i = j
  · subst hij
    rw [Tag.cartan_self, Tag.cartan_self]
  have hπij : π i ≠ π j := π.injective.ne hij
  have htr := commute_simplePos_transport (hπ i) (hπ j)
  have h1 := simplePos_commute_iff (K := K) hτ hij
  have h2 := simplePos_commute_iff (K := K) hτ hπij
  rcases cartan_offdiag_of_E hτ hij with h | h <;>
    rcases cartan_offdiag_of_E hτ hπij with h' | h'
  · rw [h, h']
  · exact absurd h' (h2.1 (htr.1 (h1.2 (by rw [h]; decide))))
  · exact absurd h (h1.1 (htr.2 (h2.2 (by rw [h']; decide))))
  · rw [h, h']

theorem exceptional_E_intrinsic_diagram_permutation
    (K : Type) [Field K] :
    (∀ τ : Tag, (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ∀ α ∈ unipotentPairAut τ K,
      ∀ π : Equiv.Perm (Fin τ.rank),
        (∀ i, (simplePosSubgroup τ K i).map α.toMonoidHom = simplePosSubgroup τ K (π i) ∧
          (simpleNegSubgroup τ K i).map α.toMonoidHom = simpleNegSubgroup τ K (π i)) →
        ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) ∧
    (∀ α ∈ unipotentPairAut .E6 K, ∀ π : Equiv.Perm (Fin Tag.E6.rank),
      (∀ i, (simplePosSubgroup .E6 K i).map α.toMonoidHom = simplePosSubgroup .E6 K (π i) ∧
        (simpleNegSubgroup .E6 K i).map α.toMonoidHom = simpleNegSubgroup .E6 K (π i)) →
      π = 1 ∨ π = TwistTag.E6.perm) ∧
    (∀ α ∈ unipotentPairAut .E7 K, ∀ π : Equiv.Perm (Fin Tag.E7.rank),
      (∀ i, (simplePosSubgroup .E7 K i).map α.toMonoidHom = simplePosSubgroup .E7 K (π i) ∧
        (simpleNegSubgroup .E7 K i).map α.toMonoidHom = simpleNegSubgroup .E7 K (π i)) →
      π = 1) ∧
    (∀ α ∈ unipotentPairAut .E8 K, ∀ π : Equiv.Perm (Fin Tag.E8.rank),
      (∀ i, (simplePosSubgroup .E8 K i).map α.toMonoidHom = simplePosSubgroup .E8 K (π i) ∧
        (simpleNegSubgroup .E8 K i).map α.toMonoidHom = simpleNegSubgroup .E8 K (π i)) →
      π = 1) := by
  refine ⟨fun τ hτ α _ π hπ => cartan_perm_eq hτ fun i => (hπ i).1, fun α _ π hπ => ?_,
    fun α _ π hπ => ?_, fun α _ π hπ => ?_⟩
  · exact perm_cases_of_cartanE6 π (cartan_perm_eq (Or.inl rfl) fun i => (hπ i).1)
  · exact perm_eq_one_of_cartanE7 π (cartan_perm_eq (Or.inr (Or.inl rfl)) fun i => (hπ i).1)
  · exact perm_eq_one_of_cartanE8 π (cartan_perm_eq (Or.inr (Or.inr rfl)) fun i => (hπ i).1)

end CFSG.LieType.Chevalley
