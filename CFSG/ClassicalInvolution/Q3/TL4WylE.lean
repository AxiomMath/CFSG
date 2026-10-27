module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.Q3.TL4SecOrbit
public import CFSG.ClassicalInvolution.Q3.TL4WylD

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj)

@[expose] def FrameAtCore {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  (∀ B ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ v : Y,
    IsUniqueInvolution B v → t * v ∈ Subgroup.center Y) ∧
    (omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)).ncard = 3

theorem exists_third_of_ncard_eq_three {α : Type*} {s : Set α} (hs : s.ncard = 3) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∃ c ∈ s, c ≠ a ∧ c ≠ b ∧ ∀ x ∈ s, x = a ∨ x = b ∨ x = c := by
  have hsub : ({a, b} : Set α) ⊆ s := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have h1 : (s \ {a, b}).ncard = 1 := by
    rw [Set.ncard_sdiff hsub, hs, Set.ncard_pair hab]
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp h1
  have hcm : c ∈ s \ {a, b} := by rw [hc]; rfl
  refine ⟨c, hcm.1, fun h => hcm.2 (Or.inl h), fun h => hcm.2 (Or.inr h), fun x hx => ?_⟩
  by_cases hxab : x ∈ ({a, b} : Set α)
  · rcases hxab with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · have : x ∈ s \ {a, b} := ⟨hx, hxab⟩
    rw [hc] at this
    exact Or.inr (Or.inr this)

section Leaves


@[expose] def SecIdE2Frame : Prop :=
  ∀ n, CIT3Below n → TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      TightInO2 t → ¬ DConnected (CoreAssembly.conjClass (tightCore R)) →
        ∀ B₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          ∀ B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) B₁,
            B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
              FrameAtCore R t

@[expose] def SecIdE4Frame : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        Blueprint.LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
        ∀ B₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          ∀ B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) B₁,
            B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
              FrameAtCore R t

@[expose] def SecIdLieFrame : Prop :=
  ∀ n, CIT3Below n → TightBelowRPlus 3 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      SecIdLie3 R t → ¬ DConnected (CoreAssembly.conjClass (tightCore R)) →
        ∀ B₁ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
          ∀ B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) B₁,
            B₂ ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) →
              FrameAtCore R t

end Leaves

section Cit3


theorem tightSecFrameR_of_plus {n : ℕ} (hA : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (h4 : Thm4RBelow 3 n) (hE2 : SecIdE2Frame) (hE4 : SecIdE4Frame) (hLie : SecIdLieFrame) :
    TightSecFrameR 3 n := by
  intro X _ _ hn Φ h hO hgen _ hc B hB hinj hadj u hu
  have htr := omegaTransitive_of_not_dConnected h4 h hO hn (hB 0) hc
  obtain ⟨S, z, hd, hcls, hfam⟩ := exists_datum_of_omegaTransitive h hO hgen (hB 0) htr
  have hcore : tightCore (B 0) = B 0 := h.closure_twoElts (hB 0)
  have hc' : ¬ DConnected (CoreAssembly.conjClass (tightCore (B 0))) := by rwa [hfam]
  have hnbr : ∀ i j, i ≠ j →
      B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore (B 0))) (B i) := fun i j hij => by
    rw [hfam]
    exact hadj i j hij
  have hK0 : omegaNbr (CoreAssembly.conjClass (tightCore (B 0))) (tightCore (B 0)) =
      omegaNbr (CoreAssembly.conjClass (tightCore (B 0))) (B 0) :=
    congrArg (omegaNbr (CoreAssembly.conjClass (tightCore (B 0)))) hcore
  have h1 : B 1 ∈ omegaNbr (CoreAssembly.conjClass (tightCore (B 0))) (tightCore (B 0)) := by
    rw [hK0]
    exact hnbr 0 1 (by decide)
  have h2 : B 2 ∈ omegaNbr (CoreAssembly.conjClass (tightCore (B 0))) (tightCore (B 0)) := by
    rw [hK0]
    exact hnbr 0 2 (by decide)
  have h12 := hnbr 1 2 (by decide)
  have hfr : FrameAtCore (B 0) z := by
    by_cases hE2' : TightInO2 z
    · exact hE2 n hA hP X hn (B 0) S z hd hcls hE2' hc' _ h1 _ h12 h2
    rcases secIdentDatum3_of hP hA X hn (B 0) S z hd hcls with
      h2o | ⟨he, -⟩ | ⟨he, -⟩ | h4o | hl
    · exact absurd h2o hE2'
    · exact absurd (Or.inl h1) (he _ (CoreAssembly.mem_conjClass_self _) _ h1.1)
    · exact absurd (Or.inl h1) (he _ (CoreAssembly.mem_conjClass_self _) _ h1.1)
    · exact hE4 X (B 0) S z hd hcls hE2' h4o.1 h4o.2 _ h1 _ h12 h2
    · exact hLie n hA hP X hn (B 0) S z hd hcls hl hc' _ h1 _ h12 h2
  obtain ⟨hcen, hcard⟩ := hfr
  rw [hfam, hcore] at hcen hcard
  have hz : IsUniqueInvolution (B 0) z := by
    have := hd.isUniqueInvolution_core
    rwa [hcore] at this
  have hu0 : u 0 = z := (hu 0).eq hz
  refine ⟨?_, ?_⟩
  · rw [hu0]
    exact hcen _ (hadj 0 1 (by decide)) _ (hu 1)
  · exact exists_third_of_ncard_eq_three hcard (hadj 0 1 (by decide)) (hadj 0 2 (by decide))
      (hinj.ne (by decide))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
