module

public import CFSG.LieType.Steinberg.Adjoint.Ops
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

universe u

variable {τ : Tag}

@[expose] def sRoot (i : Fin τ.rank) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    {v : Fin τ.rank → ℤ // IsRoot τ v} :=
  ⟨reflect τ i α.1, IsRoot.reflect i α.2⟩

theorem sRoot_sRoot (i : Fin τ.rank) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    sRoot i (sRoot i α) = α :=
  Subtype.ext (reflect_reflect τ i α.1)

theorem reflect_add (i : Fin τ.rank) (u v : Fin τ.rank → ℤ) :
    reflect τ i (u + v) = reflect τ i u + reflect τ i v := by
  rw [← reflectHom_apply, ← reflectHom_apply, ← reflectHom_apply, map_add]

theorem reflect_sub (i : Fin τ.rank) (u v : Fin τ.rank → ℤ) :
    reflect τ i (u - v) = reflect τ i u - reflect τ i v := by
  rw [← reflectHom_apply, ← reflectHom_apply, ← reflectHom_apply, map_sub]

theorem reflect_neg (i : Fin τ.rank) (u : Fin τ.rank → ℤ) :
    reflect τ i (-u) = -reflect τ i u := by
  rw [← reflectHom_apply, ← reflectHom_apply, map_neg]

theorem not_isRoot_single_add_single (j : Fin τ.rank) :
    ¬IsRoot τ (Pi.single j 1 + Pi.single j 1) := by
  rw [← two_smul ℤ, isRoot_smul_single_iff]
  omega

theorem units_conj_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (g : (Module.End R M)ˣ) (a b : Module.End R M) :
    (g : Module.End R M) * (a * b - b * a) * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M) =
      (g : Module.End R M) * a * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M) *
          ((g : Module.End R M) * b * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M)) -
        (g : Module.End R M) * b * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M) *
          ((g : Module.End R M) * a * ((g⁻¹ : (Module.End R M)ˣ) : Module.End R M)) := by
  simp only [mul_sub, sub_mul, mul_assoc, Units.inv_mul_cancel_left]

open _root_.Classical in
@[expose] def stringNorm (β γ : Fin τ.rank → ℤ) : ℕ :=
  if IsRoot τ (γ - β) then 2 else 1

theorem stringNorm_of_isRoot {β γ : Fin τ.rank → ℤ} (h : IsRoot τ (γ - β)) :
    stringNorm β γ = 2 := by
  classical
  exact ite_eq_left h

theorem stringNorm_of_not_isRoot {β γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ (γ - β)) :
    stringNorm β γ = 1 := by
  classical
  exact ite_eq_right h

theorem stringNorm_reflect (i : Fin τ.rank) (β γ : Fin τ.rank → ℤ) :
    stringNorm (reflect τ i β) (reflect τ i γ) = stringNorm β γ := by
  by_cases h : IsRoot τ (γ - β)
  · rw [stringNorm_of_isRoot h, stringNorm_of_isRoot]
    rw [← reflect_sub, isRoot_reflect_iff]
    exact h
  · rw [stringNorm_of_not_isRoot h, stringNorm_of_not_isRoot]
    rw [← reflect_sub, isRoot_reflect_iff]
    exact h

namespace AdjData

variable (D : AdjData τ)

@[expose] def checkPairNorm : Bool :=
  (List.range (nR τ)).all fun l => (List.finRange τ.rank).all fun j =>
    decide (l = D.neg j) || decide (l = j) ||
      (if D.upI l j = 0 then D.pairDig l j == 0
        else (((D.pairDig l j % 8 : ℕ) : ℤ) - 4).natAbs == if D.downI l j = 0 then 1 else 2)

structure Valid : Prop where
  tables : D.checkTables = true
  simple : D.checkSimple = true
  weyl : D.checkWeyl = true
  pairs : D.checkPairs = true
  pairNorm : D.checkPairNorm = true

variable {D}

theorem checkPairNorm_at (hN : D.checkPairNorm = true) {l : ℕ}
    (hl : l < τ.rootCertificate.roots.length) (j : Fin τ.rank) (hlj : l ≠ D.neg j)
    (hlj' : l ≠ j) :
    if D.upI l j = 0 then D.pairDig l j = 0
    else (((D.pairDig l j % 8 : ℕ) : ℤ) - 4).natAbs = if D.downI l j = 0 then 1 else 2 := by
  simp only [checkPairNorm, nR, List.all_eq_true, List.mem_range, List.mem_finRange,
    true_implies] at hN
  have h := hN l hl j
  simp only [Bool.or_eq_true, decide_eq_true_eq, hlj, hlj', false_or] at h
  split_ifs at h ⊢ <;> simpa using h

variable (D) (R : Type*) [CommRing R]

@[expose] def rootOp (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) : Module.End R (RootModule τ R) :=
  D.recOp R (pos α)

@[expose] def rootSign (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) : ℤ :=
  D.weylSign (pos α) i

variable {D R}

theorem rootSign_eq (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    D.rootSign α i = 1 ∨ D.rootSign α i = -1 :=
  D.weylSign_eq _ i

theorem rootSign_mul_self (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    D.rootSign α i * D.rootSign α i = 1 :=
  D.weylSign_mul_self _ i

theorem rootOp_congr {α β : {v : Fin τ.rank → ℤ // IsRoot τ v}} (h : α.1 = β.1) :
    D.rootOp R α = D.rootOp R β := by
  rw [Subtype.ext h]

theorem rootOp_simple (hD : D.Valid) (i : Fin τ.rank) :
    D.rootOp R ⟨Pi.single i 1, isRoot_single τ i⟩ = infE τ R i := by
  rw [rootOp, (pos_eq_simple_iff i).2 rfl, recOp_simple hD.tables hD.simple]

theorem rootOp_weyl (hD : D.Valid) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * D.rootOp R α *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R)) =
      (D.rootSign α i : R) • D.rootOp R (sRoot i α) := by
  rw [rootOp, recOp_weyl hD.tables hD.simple hD.weyl (pos_lt α), rootOp, sRoot,
    pos_reflect hD.tables α.2 i]
  rfl

theorem rootOp_reflect (hD : D.Valid) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (i : Fin τ.rank) :
    D.rootOp R (sRoot i α) = (D.rootSign α i : R) •
      ((weylElt τ R i 1 : Module.End R (RootModule τ R)) * D.rootOp R α *
        (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
          Module.End R (RootModule τ R))) := by
  rw [rootOp_weyl hD, smul_smul, ← Int.cast_mul, rootSign_mul_self, Int.cast_one, one_smul]

theorem rootOp_bracket_single (hD : D.Valid) (j : Fin τ.rank)
    (γ : {v : Fin τ.rank → ℤ // IsRoot τ v}) (hγ : γ.1 ≠ -Pi.single j 1) :
    (∀ h : IsRoot τ (Pi.single j 1 + γ.1), ∃ N : ℤ,
      N.natAbs = stringNorm (Pi.single j 1) γ.1 ∧
        ∀ (R : Type u) [CommRing R],
          D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ * D.rootOp R γ -
              D.rootOp R γ * D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ =
            (N : R) • D.rootOp R ⟨Pi.single j 1 + γ.1, h⟩) ∧
      (¬IsRoot τ (Pi.single j 1 + γ.1) → ∀ (R : Type u) [CommRing R],
          D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ * D.rootOp R γ -
              D.rootOp R γ * D.rootOp R ⟨Pi.single j 1, isRoot_single τ j⟩ = 0) := by
  have hT := hD.tables
  set l := pos γ with hl_def
  have hl : l < τ.rootCertificate.roots.length := pos_lt γ
  have hrl : τ.rootCertificate.root l = γ.1 := root_pos γ
  have hlj : l ≠ D.neg j := fun h => hγ ((pos_eq_neg_simple_iff hT j).1 h)
  have hsj : pos (⟨Pi.single j 1, isRoot_single τ j⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v}) = j :=
    (pos_eq_simple_iff j).2 rfl
  by_cases hlj' : l = j
  · have hγj : γ.1 = Pi.single j 1 := (pos_eq_simple_iff j).1 hlj'
    have hnr : ¬IsRoot τ (Pi.single j 1 + γ.1) := by
      rw [hγj]
      exact not_isRoot_single_add_single j
    refine ⟨fun h => absurd h hnr, fun _ R _ => ?_⟩
    rw [rootOp_congr (R := R) (β := ⟨Pi.single j 1, isRoot_single τ j⟩) hγj, sub_self]
  have hN := checkPairNorm_at hD.pairNorm hl j hlj hlj'
  have hP := (checkPairs_at hD.pairs hl j hlj).1
  have hbr := fun (R : Type u) [CommRing R] =>
    recOp_bracket_simple (R := R) hT hD.simple hD.weyl hD.pairs hl j hlj
  by_cases hu : D.upI l j = 0
  · rw [ite_eq_left hu] at hN
    have hnr : ¬IsRoot τ (Pi.single j 1 + γ.1) := by
      rw [add_comm, ← hrl]
      exact not_isRoot_of_upI hT hl hu
    refine ⟨fun h => absurd h hnr, fun _ R _ => ?_⟩
    rw [rootOp, rootOp, hsj, hbr R, ite_eq_left hN]
  · rw [ite_eq_right hu] at hN
    have hd : D.pairDig l j ≠ 0 := by
      intro h0
      rw [ite_eq_left h0] at hP
      exact hP.elim hlj' hu
    rw [ite_eq_right hd] at hP
    obtain ⟨hm, hmr⟩ := upI_spec hT hl hu
    have hdn : IsRoot τ (γ.1 - Pi.single j 1) ↔ D.downI l j ≠ 0 := by
      constructor
      · intro hr h0
        exact not_isRoot_of_downI hT hl h0 (hrl ▸ hr)
      · intro h0
        rw [← hrl, ← (downI_spec hT hl h0).2]
        exact isRoot_rootCertificate_root (downI_spec hT hl h0).1
    refine ⟨fun h => ⟨((D.pairDig l j % 8 : ℕ) : ℤ) - 4, ?_, fun R _ => ?_⟩, fun hnr => ?_⟩
    · rw [hN]
      by_cases hd0 : D.downI l j = 0
      · rw [ite_eq_left hd0, stringNorm_of_not_isRoot (fun hr => (hdn.1 hr) hd0)]
      · rw [ite_eq_right hd0, stringNorm_of_isRoot (hdn.2 hd0)]
    · rw [rootOp, rootOp, hsj, hbr R, ite_eq_right hd, rootOp, hP]
      congr 2
      rw [eq_comm, pos_eq_iff hm, hmr, hrl, add_comm]
    · exact absurd (by rw [add_comm, ← hrl, ← hmr]; exact isRoot_rootCertificate_root hm) hnr

theorem rootOp_bracket (hD : D.Valid) (β : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    ∀ γ : {v : Fin τ.rank → ℤ // IsRoot τ v}, γ.1 ≠ -β.1 →
      (∀ h : IsRoot τ (β.1 + γ.1), ∃ N : ℤ,
        N.natAbs = stringNorm β.1 γ.1 ∧
          ∀ (R : Type u) [CommRing R],
            D.rootOp R β * D.rootOp R γ - D.rootOp R γ * D.rootOp R β =
              (N : R) • D.rootOp R ⟨β.1 + γ.1, h⟩) ∧
        (¬IsRoot τ (β.1 + γ.1) → ∀ (R : Type u) [CommRing R],
          D.rootOp R β * D.rootOp R γ - D.rootOp R γ * D.rootOp R β = 0) := by
  obtain ⟨v, hv⟩ := β
  induction hv with
  | basis j => exact fun γ hγ => rootOp_bracket_single hD j γ hγ
  | @reflect i v hv ih =>
    intro γ hγ
    set β : {v : Fin τ.rank → ℤ // IsRoot τ v} := ⟨v, hv⟩
    set γ' := sRoot i γ with hγ'_def
    have hγγ' : γ = sRoot i γ' := (sRoot_sRoot i γ).symm
    have hne : γ'.1 ≠ -β.1 := by
      intro h
      apply hγ
      rw [hγγ']
      change reflect τ i γ'.1 = -reflect τ i v
      rw [h, reflect_neg]
    obtain ⟨ih₁, ih₂⟩ := ih γ' hne
    have hsum : reflect τ i v + γ.1 = reflect τ i (β.1 + γ'.1) := by
      rw [reflect_add, hγγ']
      rfl
    have hdiff : γ.1 - reflect τ i v = reflect τ i (γ'.1 - β.1) := by
      rw [reflect_sub, hγγ']
      rfl
    have hsβ : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v}) =
        sRoot i β := rfl
    have key : ∀ (R : Type u) [CommRing R],
        D.rootOp R ⟨reflect τ i v, IsRoot.reflect i hv⟩ * D.rootOp R γ -
            D.rootOp R γ * D.rootOp R ⟨reflect τ i v, IsRoot.reflect i hv⟩ =
          ((D.rootSign β i * D.rootSign γ' i : ℤ) : R) •
            ((weylElt τ R i 1 : Module.End R (RootModule τ R)) *
              (D.rootOp R β * D.rootOp R γ' - D.rootOp R γ' * D.rootOp R β) *
              (((weylElt τ R i 1)⁻¹ : (Module.End R (RootModule τ R))ˣ) :
                Module.End R (RootModule τ R))) := by
      intro R _
      rw [hsβ, units_conj_comm, rootOp_reflect hD, hγγ', rootOp_reflect hD, smul_mul_smul_comm,
        smul_mul_smul_comm, mul_comm (D.rootSign γ' i : R) (D.rootSign β i : R), ← smul_sub,
        Int.cast_mul]
    refine ⟨fun h => ?_, fun hnr R _ => ?_⟩
    · have h' : IsRoot τ (β.1 + γ'.1) := by
        rw [← isRoot_reflect_iff i, ← hsum]
        exact h
      obtain ⟨N, hN, hbr⟩ := ih₁ h'
      refine ⟨D.rootSign β i * D.rootSign γ' i * D.rootSign ⟨_, h'⟩ i * N, ?_, fun R _ => ?_⟩
      · rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, hN, hγγ']
        change _ = stringNorm (reflect τ i v) (reflect τ i γ'.1)
        rw [stringNorm_reflect]
        rcases rootSign_eq (D := D) β i with h1 | h1 <;>
          rcases rootSign_eq (D := D) γ' i with h2 | h2 <;>
          rcases rootSign_eq (D := D) (⟨_, h'⟩ : {v : Fin τ.rank → ℤ // IsRoot τ v}) i
            with h3 | h3 <;> simp [h1, h2, h3, β]
      · rw [key, hbr R, mul_smul_comm, smul_mul_assoc, rootOp_weyl hD, smul_smul, smul_smul,
          rootOp_congr (R := R) (β := ⟨reflect τ i v + γ.1, h⟩) hsum.symm]
        push_cast
        ring_nf
    · have h' : ¬IsRoot τ (β.1 + γ'.1) := by
        rw [← isRoot_reflect_iff i, ← hsum]
        exact hnr
      rw [key, ih₂ h' R, mul_zero, zero_mul, smul_zero]

end AdjData

end CFSG.LieType.Steinberg.Adjoint
