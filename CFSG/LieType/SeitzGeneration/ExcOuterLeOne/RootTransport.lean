module

public import CFSG.LieType.Chevalley.CartanPositiveForm
public import CFSG.LieType.Steinberg.Adjoint.Datum
public import CFSG.LieType.Chevalley.RootOps.All

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section Transport

variable {τ : Tag} {K : Type} [Field K]

@[expose] def rootNorm (τ : Tag) (v : Fin τ.rank → ℤ) : ℤ :=
  dotProduct v (Matrix.mulVec τ.symmetrizedCartan v)

theorem weylElement_one_mem_of_rat (k : Subfield K) (H : Subgroup ↥(adjointGroup τ K))
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ H)
    (i : Fin τ.rank) :
    CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ H := by
  unfold CFSG.LieType.Steinberg.weylElement
  simp only [inv_one, Units.val_one]
  exact H.mul_mem (H.mul_mem (hrat _ (isRoot_single τ i) 1 k.one_mem)
    (hrat _ (isRoot_neg_single τ i) (-1) (k.neg_mem k.one_mem))) (hrat _ (isRoot_single τ i) 1 k.one_mem)

theorem xPar_mem_reflect (H : Subgroup ↥(adjointGroup τ K))
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ H)
    (i : Fin τ.rank) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (u : K) :
    xPar (rootOperatorFamily τ) β u ∈ H ↔
      xPar (rootOperatorFamily τ) (reflect τ i β) u ∈ H := by
  have key : ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β → ∀ u : K,
      xPar (rootOperatorFamily τ) β u ∈ H →
        xPar (rootOperatorFamily τ) (reflect τ i β) u ∈ H := by
    intro β hβ u hu
    obtain ⟨ε, hε, h⟩ := weylElement_xPar_conj (F := rootOperatorFamily τ) (K := K) i hβ
    have h1 := H.mul_mem (H.mul_mem (hw i) hu) (H.inv_mem (hw i))
    rw [h 1 u] at h1
    have hrefl : CFSG.LieType.RootSystem.reflection τ.cartan i β = reflect τ i β := by
      rw [CFSG.LieType.RootSystem.reflection_apply]
      rfl
    rw [hrefl] at h1
    simp only [Units.val_one, one_zpow, mul_one] at h1
    rcases hε with rfl | rfl
    · simpa using h1
    · have h2 := H.inv_mem h1
      rw [xPar_neg] at h2
      simpa using h2
  refine ⟨key hβ u, fun h => ?_⟩
  have := key (IsRoot.reflect i hβ) u h
  rwa [reflect_reflect] at this

theorem rootNorm_reflect (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    rootNorm τ (reflect τ i v) = rootNorm τ v := by
  have hsymm := symmetrizedCartan_isSymm τ
  set c : ℤ := ∑ j, τ.cartan i j * v j with hc
  have hBv : (τ.symmetrizedCartan.mulVec v) i = τ.symmetrizer i i * c := by
    simp only [Matrix.mulVec, dotProduct, symmetrizedCartan_apply, hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hBi : τ.symmetrizedCartan.mulVec (Pi.single i 1) = fun a => τ.symmetrizedCartan a i := by
    ext a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hvBi : dotProduct v (fun a => τ.symmetrizedCartan a i) = (τ.symmetrizedCartan.mulVec v) i := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm, hsymm.apply i a]
  have hBii : τ.symmetrizedCartan i i = 2 * τ.symmetrizer i i := by
    rw [symmetrizedCartan_apply, τ.cartan_self, mul_comm]
  have hsi : dotProduct (Pi.single i 1 : Fin τ.rank → ℤ) (τ.symmetrizedCartan.mulVec v) =
      (τ.symmetrizedCartan.mulVec v) i := by simp
  have hsii : dotProduct (Pi.single i 1 : Fin τ.rank → ℤ) (fun a => τ.symmetrizedCartan a i) =
      τ.symmetrizedCartan i i := by simp
  have hrefl : reflect τ i v = v - c • (Pi.single i 1 : Fin τ.rank → ℤ) := rfl
  unfold rootNorm
  rw [hrefl]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hBi, dotProduct_sub, sub_dotProduct,
    dotProduct_smul, smul_dotProduct, hvBi, hsi, hsii, hBv, hBii, smul_eq_mul]
  ring

theorem exists_simple_of_root (H : Subgroup ↥(adjointGroup τ K))
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ H)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ j : Fin τ.rank, rootNorm τ γ = rootNorm τ (Pi.single j 1) ∧
      ∀ u : K, xPar (rootOperatorFamily τ) γ u ∈ H ↔
        xPar (rootOperatorFamily τ) (Pi.single j 1) u ∈ H := by
  induction hγ with
  | basis j => exact ⟨j, rfl, fun u => Iff.rfl⟩
  | reflect i hv ih =>
    obtain ⟨j, hn, h⟩ := ih
    exact ⟨j, by rw [rootNorm_reflect, hn], fun u => (xPar_mem_reflect H hw i hv u).symm.trans (h u)⟩

theorem xPar_mem_iff_of_neighbour (H : Subgroup ↥(adjointGroup τ K))
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ H)
    {i l : Fin τ.rank} (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) (u : K) :
    xPar (rootOperatorFamily τ) (Pi.single i 1) u ∈ H ↔
      xPar (rootOperatorFamily τ) (Pi.single l 1) u ∈ H := by
  have hli' : l ≠ i := ne_of_cartan_eq_neg_one hil
  have hr1 : reflect τ i (Pi.single l 1) = Pi.single l 1 + Pi.single i 1 := by
    have hsum : ∑ j, τ.cartan i j * (Pi.single l 1 : Fin τ.rank → ℤ) j = τ.cartan i l := by
      simp [Pi.single_apply]
    simp only [reflect, hsum, hil]
    simp
  have hr2 : reflect τ l (Pi.single l 1 + Pi.single i 1) = Pi.single i 1 := by
    have hsum : ∑ j, τ.cartan l j * (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) j = 1 := by
      simp [Pi.single_apply, mul_add, Finset.sum_add_distrib, hli, τ.cartan_self]
    simp only [reflect, hsum]
    simp
  have h1 := xPar_mem_reflect H hw i (isRoot_single τ l) u
  have h2 := xPar_mem_reflect H hw l (isRoot_single_add_single hil) u
  rw [hr1] at h1
  rw [hr2] at h2
  exact (h1.trans h2).symm

theorem xPar_mem_iff_of_connected (H : Subgroup ↥(adjointGroup τ K))
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ H)
    (hconn : ∀ i j : Fin τ.rank,
      Relation.ReflTransGen (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) i j)
    (i j : Fin τ.rank) (u : K) :
    xPar (rootOperatorFamily τ) (Pi.single i 1) u ∈ H ↔
      xPar (rootOperatorFamily τ) (Pi.single j 1) u ∈ H := by
  have := hconn i j
  induction this with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact ih.trans (xPar_mem_iff_of_neighbour H hw hbc.1 hbc.2 u)

theorem xPar_mem_iff_of_roots (H : Subgroup ↥(adjointGroup τ K))
    (hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ H)
    (hconn : ∀ i j : Fin τ.rank,
      Relation.ReflTransGen (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) i j)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (u : K) :
    xPar (rootOperatorFamily τ) γ u ∈ H ↔ xPar (rootOperatorFamily τ) δ u ∈ H := by
  obtain ⟨j, -, hj⟩ := exists_simple_of_root H hw hγ
  obtain ⟨j', -, hj'⟩ := exists_simple_of_root H hw hδ
  exact (hj u).trans ((xPar_mem_iff_of_connected H hw hconn j j' u).trans (hj' u).symm)

theorem commutator_xPar_neighbour {D : AdjData τ} (hD : D.Valid) (hτ : NoG2 τ) {i l : Fin τ.rank}
    (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ a b : K,
      ⁅xPar (rootOperatorFamily τ) (Pi.single l 1) a, xPar (rootOperatorFamily τ) (Pi.single i 1) b⁆ =
        xPar (rootOperatorFamily τ) (Pi.single l 1 + Pi.single i 1) ((ε : K) * a * b) := by
  have hli' : l ≠ i := ne_of_cartan_eq_neg_one hil
  have hα : IsRoot τ (Pi.single l 1) := isRoot_single τ l
  have hβ : IsRoot τ (Pi.single i 1) := isRoot_single τ i
  have hδ : IsRoot τ (Pi.single l 1 + Pi.single i 1) := isRoot_single_add_single hil
  have hne : (Pi.single l 1 : Fin τ.rank → ℤ) ≠ Pi.single i 1 := single_ne_single_of_ne hli'
  have hne' : (Pi.single l 1 : Fin τ.rank → ℤ) ≠ -Pi.single i 1 := single_ne_neg_single_of l i
  have e1 : (2 : ℕ) • (Pi.single i 1 : Fin τ.rank → ℤ) = (2 : ℤ) • Pi.single i 1 := by
    rw [two_nsmul, two_zsmul]
  have e2 : (2 : ℕ) • (Pi.single l 1 : Fin τ.rank → ℤ) = (2 : ℤ) • Pi.single l 1 := by
    rw [two_nsmul, two_zsmul]
  have h12 : ¬IsRoot τ (Pi.single l 1 + (2 : ℕ) • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    rw [e1]
    exact not_isRoot_single_add_two hil
  have h21 : ¬IsRoot τ ((2 : ℕ) • (Pi.single l 1 : Fin τ.rank → ℤ) + Pi.single i 1) := by
    rw [e2, add_comm]
    exact not_isRoot_single_add_two hli
  have hN : (RootOperatorFamily'.coeff11 (rootOperatorFamily τ) hD ⟨_, hα⟩ ⟨_, hβ⟩).natAbs = 1 := by
    rw [RootOperatorFamily'.coeff11,
      RootOperatorFamily'.bracketCoeff_natAbs (rootOperatorFamily τ) hD (single_ne_neg_single_of i l) hδ]
    exact stringNorm_of_not_isRoot (not_isRoot_single_sub_single hli'.symm)
  refine ⟨RootOperatorFamily'.coeff11 (rootOperatorFamily τ) hD ⟨_, hα⟩ ⟨_, hβ⟩, ?_, fun a b => ?_⟩
  · rcases Int.natAbs_eq_iff.1 hN with h | h
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  · rw [commutator_xPar (F := rootOperatorFamily τ) hD hτ hα hβ hne hne' a b,
      xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one]

theorem xPar_mul_mem_of_commutator (H : Subgroup ↥(adjointGroup τ K)) {i l : Fin τ.rank} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1)
    (hcomm : ∀ a b : K,
      ⁅xPar (rootOperatorFamily τ) (Pi.single l 1) a, xPar (rootOperatorFamily τ) (Pi.single i 1) b⁆ =
        xPar (rootOperatorFamily τ) (Pi.single l 1 + Pi.single i 1) ((ε : K) * a * b))
    {a b : K} (ha : xPar (rootOperatorFamily τ) (Pi.single l 1) a ∈ H)
    (hb : xPar (rootOperatorFamily τ) (Pi.single i 1) b ∈ H) :
    xPar (rootOperatorFamily τ) (Pi.single l 1 + Pi.single i 1) (a * b) ∈ H := by
  have h2 : ⁅xPar (rootOperatorFamily τ) (Pi.single l 1) a,
      xPar (rootOperatorFamily τ) (Pi.single i 1) b⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  rw [hcomm a b] at h2
  rcases hε with rfl | rfl
  · simpa using h2
  · have h3 := H.inv_mem h2
    rw [xPar_neg] at h3
    simpa using h3

theorem eq_top_of_forall_xPar_mem (H : Subgroup ↥(adjointGroup τ K))
    (h : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c : K, xPar (rootOperatorFamily τ) γ c ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff, ← iSup_rootGroup_eq_top (rootOperatorFamily τ) K]
  refine iSup₂_le fun γ hγ => ?_
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
  exact h γ hγ c

end Transport

section FieldTheory

theorem eq_top_of_subring {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : ∀ F : Subfield K, k ≤ F → F = k ∨ F = ⊤) (S : Subring K) (hkS : ∀ c ∈ k, c ∈ S)
    {t : K} (ht : t ∉ k) (htS : t ∈ S) : S = ⊤ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have h1 : x ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
      have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
      have h2 : x * x ^ (Fintype.card K - 2) = 1 := by
        rw [← pow_succ']
        convert h1 using 2
        omega
      rw [← eq_inv_of_mul_eq_one_right h2]
      exact S.pow_mem hx _
  let F : Subfield K := { S with inv_mem' := hinv }
  have hkF : k ≤ F := fun c hc => hkS c hc
  rcases hk F hkF with h | h
  · exact absurd (h ▸ (htS : t ∈ F)) ht
  · ext x
    have : x ∈ F := by rw [h]; trivial
    exact ⟨fun _ => trivial, fun _ => this⟩

end FieldTheory

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
