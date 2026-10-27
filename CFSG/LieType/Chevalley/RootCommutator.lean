module

public import CFSG.LieType.Chevalley.RootCommutatorReduction
public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps
open scoped commutatorElement

universe u

variable {τ : Tag}

theorem pinnedX_eq_eltVec
    (R : Type) [CommRing R] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (c : R) : pinnedX τ R γ c = (rootOperatorFamily τ).eltVec R γ
      (((rootOperatorFamily τ).pinnedFamilySign γ : R) * c) := by
  rw [(rootOperatorFamily τ).pinnedX_eq_eltUnit R hγ, (rootOperatorFamily τ).eltVec_of_isRoot hγ]

theorem eltVec_eq_pinnedX
    (R : Type) [CommRing R] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (c : R) : (rootOperatorFamily τ).eltVec R γ c =
      pinnedX τ R γ (((rootOperatorFamily τ).pinnedFamilySign γ : R) * c) := by
  rw [pinnedX_eq_eltVec R hγ, ← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self,
    one_mul]

theorem abs_pinnedFamilySign
    (γ : Fin τ.rank → ℤ) :
    |(rootOperatorFamily τ).pinnedFamilySign γ| = 1 := by
  rcases (rootOperatorFamily τ).pinnedFamilySign_eq γ with h | h <;> rw [h] <;> rfl

theorem pinnedX_commFormula_of_commFormula
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) {C : ℕ × ℕ → ℤ} (hF : (rootOperatorFamily τ).CommFormula α β C)
    (R : Type) [CommRing R] (c d : R) :
    pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d) =
      ((commPairs τ α β).map fun p => pinnedX τ R (p.1 • α + p.2 • β)
        (((rootOperatorFamily τ).pinnedFamilySign (p.1 • α + p.2 • β) *
          (rootOperatorFamily τ).pinnedFamilySign α ^ p.1 *
          (rootOperatorFamily τ).pinnedFamilySign β ^ p.2 * C p : ℤ) * c ^ p.1 *
            d ^ p.2)).prod := by
  rw [pinnedX_eq_eltVec R hα, pinnedX_eq_eltVec R hβ, pinnedX_eq_eltVec R hα,
    pinnedX_eq_eltVec R hβ, mul_neg, mul_neg, hF R]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [eltVec_eq_pinnedX R (mem_commPairs.1 hp).2]
  congr 1
  push_cast
  ring

theorem exists_pinnedX_commFormula
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) :
    ∃ C : ℕ × ℕ → ℤ, (∀ p ∈ commPairs τ α β, 1 ≤ |C p| ∧ |C p| ≤ commConstBound τ) ∧
      ∀ (R : Type) [CommRing R] (c d : R),
        pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d) =
          ((commPairs τ α β).map fun p =>
            pinnedX τ R (p.1 • α + p.2 • β) ((C p : R) * c ^ p.1 * d ^ p.2)).prod := by
  obtain ⟨C, hC, hF⟩ := hasCommFormula_of_isRoot hα hβ hne hne'
  refine ⟨fun p => (rootOperatorFamily τ).pinnedFamilySign (p.1 • α + p.2 • β) *
      (rootOperatorFamily τ).pinnedFamilySign α ^ p.1 *
      (rootOperatorFamily τ).pinnedFamilySign β ^ p.2 * C p, fun p hp => ?_,
    pinnedX_commFormula_of_commFormula hα hβ hF⟩
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pinnedFamilySign, abs_pinnedFamilySign,
    abs_pinnedFamilySign, one_pow, one_pow, one_mul, one_mul, one_mul]
  exact hC p hp

theorem baseChange_list_prod_pinnedX
    {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (l : List (ℕ × ℕ)) (γ : ℕ × ℕ → Fin τ.rank → ℤ) (v : ℕ × ℕ → R) :
    BaseChange g (((l.map fun p => pinnedX τ R (γ p) (v p)).prod :
        (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      (((l.map fun p => pinnedX τ S (γ p) (g (v p))).prod :
        (Module.End S (RootModule τ S))ˣ) : Module.End S (RootModule τ S)) := by
  induction l with
  | nil => simpa using BaseChange.one (τ := τ) (f := g)
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    exact (baseChange_pinnedX g (γ p) (v p)).mul ih

open MvPolynomial in
theorem pinnedX_commFormula_univ
    {α β : Fin τ.rank → ℤ} {C : ℕ × ℕ → ℤ}
    (hF : ∀ (R : Type) [CommRing R] (c d : R),
      pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d) =
        ((commPairs τ α β).map fun p =>
          pinnedX τ R (p.1 • α + p.2 • β) ((C p : R) * c ^ p.1 * d ^ p.2)).prod)
    (R : Type u) [CommRing R] (c d : R) :
    pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d) =
      ((commPairs τ α β).map fun p =>
        pinnedX τ R (p.1 • α + p.2 • β) ((C p : R) * c ^ p.1 * d ^ p.2)).prod := by
  have h := hF (MvPolynomial (Fin 2) ℤ) (X 0) (X 1)
  set g : MvPolynomial (Fin 2) ℤ →+* R := eval₂Hom (Int.castRingHom R) ![c, d]
  have hg0 : g (X 0) = c := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = d := eval₂Hom_X' _ _ _
  have hL := (((baseChange_pinnedX (τ := τ) g α (X 0)).mul (baseChange_pinnedX g β (X 1))).mul
    (baseChange_pinnedX g α (-X 0))).mul (baseChange_pinnedX g β (-X 1))
  rw [map_neg, map_neg, hg0, hg1] at hL
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul, h] at hL
  have hR := baseChange_list_prod_pinnedX (τ := τ) g (commPairs τ α β)
    (fun p => p.1 • α + p.2 • β) fun p => (C p : MvPolynomial (Fin 2) ℤ) * X 0 ^ p.1 * X 1 ^ p.2
  simp only [map_mul, map_pow, map_intCast, hg0, hg1] at hR
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact hL.unique hR

open _root_.Classical in
@[expose] noncomputable def commConst
    (τ : Tag) (α β : Fin τ.rank → ℤ) : ℕ × ℕ → ℤ :=
  if h : IsRoot τ α ∧ IsRoot τ β ∧ α ≠ β ∧ α ≠ -β then
    Classical.choose (exists_pinnedX_commFormula h.1 h.2.1 h.2.2.1 h.2.2.2)
  else fun _ => 0

theorem commConst_spec
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β)
    (hne' : α ≠ -β) :
    (∀ p ∈ commPairs τ α β,
      1 ≤ |commConst τ α β p| ∧ |commConst τ α β p| ≤ commConstBound τ) ∧
      ∀ (R : Type u) [CommRing R] (c d : R),
        pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d) =
          ((commPairs τ α β).map fun p => pinnedX τ R (p.1 • α + p.2 • β)
            ((commConst τ α β p : R) * c ^ p.1 * d ^ p.2)).prod := by
  have h : IsRoot τ α ∧ IsRoot τ β ∧ α ≠ β ∧ α ≠ -β := ⟨hα, hβ, hne, hne'⟩
  have hspec := Classical.choose_spec (exists_pinnedX_commFormula h.1 h.2.1 h.2.2.1 h.2.2.2)
  have hC : commConst τ α β =
      Classical.choose (exists_pinnedX_commFormula h.1 h.2.1 h.2.2.1 h.2.2.2) := by
    unfold commConst
    exact dite_eq_left h
  rw [hC]
  exact ⟨hspec.1, pinnedX_commFormula_univ hspec.2⟩

theorem root_commutator_formula
    (τ : Tag) {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ IsRoot τ (p.1 • α + p.2 • β)}.Finite ∧
    (∀ p : ℕ × ℕ, p ∈ commPairs τ α β ↔ 0 < p.1 ∧ 0 < p.2 ∧ IsRoot τ (p.1 • α + p.2 • β)) ∧
    (commPairs τ α β).Pairwise (fun p q : ℕ × ℕ =>
      p.1 + p.2 < q.1 + q.2 ∨ (p.1 + p.2 = q.1 + q.2 ∧ p.1 < q.1)) ∧
    (∀ p ∈ commPairs τ α β, 1 ≤ |commConst τ α β p| ∧ |commConst τ α β p| ≤ 3) ∧
    ∀ (R : Type u) [CommRing R] (c d : R),
      pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d) =
        ((commPairs τ α β).map fun p =>
          pinnedX τ R (p.1 • α + p.2 • β) ((commConst τ α β p : R) * c ^ p.1 * d ^ p.2)).prod := by
  have hmem := mem_commPairs_iff_of_isRoot hα hβ hne hne'
  obtain ⟨hC, hF⟩ := commConst_spec.{u} hα hβ hne hne'
  have h3 : (commConstBound τ : ℤ) ≤ 3 := by cases τ <;> decide
  exact ⟨(commPairs τ α β).finite_toSet.subset fun p hp => (hmem p).2 hp, hmem,
    commPairs_pairwise α β, fun p hp => ⟨(hC p hp).1, (hC p hp).2.trans h3⟩, hF⟩

theorem list_eq_singleton_of_forall_eq {ι : Type*} {l : List ι} {a : ι} (hall : ∀ x ∈ l, x = a)
    (hnd : l.Nodup) (ha : a ∈ l) : l = [a] := by
  rcases l with _ | ⟨x, _ | ⟨y, t⟩⟩
  · exact absurd ha List.not_mem_nil
  · rw [hall x (List.mem_singleton_self x)]
  · have hx := hall x (by simp)
    have hy := hall y (by simp)
    exact absurd (by rw [hx, hy]; simp : x ∈ y :: t) (List.nodup_cons.1 hnd).1

theorem commPairs_eq_of_simplyLaced
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) :
    (IsRoot τ (α + β) → commPairs τ α β = [(1, 1)]) ∧
      (¬IsRoot τ (α + β) → commPairs τ α β = []) := by
  obtain ⟨r, hr, hrp⟩ := exists_commPairs_eq_rep hα hβ hne hne'
  have hsl := simplyLacedCheck_eq hτ
  simp only [simplyLacedCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hsl
  have hone : ∀ p ∈ commPairs τ α β, p = (1, 1) := fun p hp => by
    rw [hrp, List.mem_map] at hp
    obtain ⟨f, hf, rfl⟩ := hp
    obtain ⟨h1, h2⟩ := hsl r hr f hf
    rw [h1, h2]
  have h11 : (1, 1) ∈ commPairs τ α β ↔ IsRoot τ (α + β) := by
    rw [mem_commPairs, one_smul, one_smul]
    exact ⟨fun h => h.2, fun h => ⟨by decide, h⟩⟩
  refine ⟨fun h => list_eq_singleton_of_forall_eq hone (commPairs_nodup α β) (h11.2 h),
    fun h => List.eq_nil_iff_forall_not_mem.2 fun p hp => h (h11.1 (hone p hp ▸ hp))⟩

theorem simply_laced_root_commutator_unit
    (τ : Tag) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β) (hne : α ≠ β) (hne' : α ≠ -β) :
    (IsRoot τ (α + β) →
      (commConst τ α β (1, 1) = 1 ∨ commConst τ α β (1, 1) = -1) ∧
        ∀ (R : Type u) [CommRing R] (c d : R), ⁅pinnedX τ R α c, pinnedX τ R β d⁆ =
          pinnedX τ R (α + β) ((commConst τ α β (1, 1) : R) * c * d)) ∧
      (¬IsRoot τ (α + β) → ∀ (R : Type u) [CommRing R],
        ∀ x ∈ rootSubgroup τ R α, ∀ y ∈ rootSubgroup τ R β, Commute x y) := by
  obtain ⟨hC, hF⟩ := commConst_spec.{u} hα hβ hne hne'
  have hb : (commConstBound τ : ℤ) = 1 := by rcases hτ with rfl | rfl | rfl | rfl <;> rfl
  have hcp := commPairs_eq_of_simplyLaced hτ hα hβ hne hne'
  refine ⟨fun h => ⟨?_, fun R _ c d => ?_⟩, fun h R _ x hx y hy => ?_⟩
  · have h11 : (1, 1) ∈ commPairs τ α β := by rw [hcp.1 h]; exact List.mem_singleton_self _
    have := hC (1, 1) h11
    rw [hb] at this
    exact (abs_eq zero_le_one).1 (le_antisymm this.2 this.1)
  · rw [commutatorElement_def, pinnedX_neg, pinnedX_neg, hF R, hcp.1 h]
    simp
  · obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hy
    have h0 := hF R c d
    rw [hcp.2 h, List.map_nil, List.prod_nil] at h0
    calc pinnedX τ R α c * pinnedX τ R β d =
          (pinnedX τ R α c * pinnedX τ R β d * pinnedX τ R α (-c) * pinnedX τ R β (-d)) *
            (pinnedX τ R β d * pinnedX τ R α c) := by
          rw [← pinnedX_neg, ← pinnedX_neg]
          group
      _ = pinnedX τ R β d * pinnedX τ R α c := by rw [h0, one_mul]

end CFSG.LieType.Chevalley
