module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16OFixW

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open Matrix CFSG.Open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
  (exists_quadMinus_ne_zero_small)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem exists_ts_span (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (S : AddSubgroup (OW F))
    (hS : ∀ x ∈ S, StatedQuadMinus 3 F b c x = 0) :
    ∃ U : Submodule F (OW F), (∀ x ∈ S, x ∈ U) ∧ (∀ x ∈ U, StatedQuadMinus 3 F b c x = 0) ∧
      Module.finrank F U ≤ 2 := by
  set U : Submodule F (OW F) := Submodule.span F (S : Set (OW F)) with hU
  have hQ : ∀ x ∈ S, quadMinus 3 F b c x = 0 := fun x hx => by
    rw [quadMinus_eq_stated]
    exact hS x hx
  have hB : ∀ x ∈ S, ∀ y ∈ S, polar (quadMinus 3 F b c) x y = 0 := by
    intro x hx y hy
    show quadMinus 3 F b c (x + y) - quadMinus 3 F b c x - quadMinus 3 F b c y = 0
    rw [hQ _ (S.add_mem hx hy), hQ _ hx, hQ _ hy]
    ring
  have step1 : ∀ x ∈ U, ∀ y ∈ S, polar (quadMinus 3 F b c) x y = 0 := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx => exact hB x hx y hy
    | zero => exact polar_zero_left _ y
    | add x x' _ _ h h' => rw [polar_add_left, h, h', add_zero]
    | smul r x _ h => rw [polar_smul_left_eq, h, mul_zero]
  have step2 : ∀ x ∈ U, ∀ y ∈ U, polar (quadMinus 3 F b c) x y = 0 := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact step1 x hx y hy
    | zero => exact polar_zero_right _ x
    | add y y' _ _ h h' => rw [polar_add_right, h, h', add_zero]
    | smul r y _ h => rw [polar_smul_right_eq, h, mul_zero]
  have hQU : ∀ x ∈ U, quadMinus 3 F b c x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hQ x hx
    | zero => exact map_zero _
    | add x y hx hy h h' =>
        rw [QuadraticMap.map_add (quadMinus 3 F b c) x y, h, h', step2 x hx y hy]
        ring
    | smul r x _ h => rw [map_smul_eq_sq, h, mul_zero]
  have hdim : Module.finrank F U ≤ 2 := by
    by_contra hlt
    push_neg at hlt
    let bU : Module.Basis (Fin (Module.finrank F U)) F U := Module.finBasisOfFinrankEq F U rfl
    let v : Fin 3 → OW F := fun i => ((bU (Fin.castLE hlt i) : U) : OW F)
    have hvli : LinearIndependent F v :=
      (bU.linearIndependent.comp (Fin.castLE hlt) (Fin.castLE_injective hlt)).map' U.subtype
        (Submodule.ker_subtype U)
    have hU3 : Module.finrank F (Submodule.span F (Set.range v)) = 3 := by
      rw [finrank_span_eq_card hvli]
      simp
    obtain ⟨u, hu, hu0⟩ := exists_quadMinus_ne_zero_small hirr (by norm_num) _ hU3
    apply hu0
    apply hQU
    refine Submodule.span_le.mpr ?_ hu
    rintro _ ⟨i, rfl⟩
    exact (bU (Fin.castLE hlt i)).2
  refine ⟨U, fun x hx => Submodule.subset_span hx, fun x hx => ?_, hdim⟩
  rw [← quadMinus_eq_stated]
  exact hQU x hx

theorem ts_card_le (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (S : AddSubgroup (OW F))
    (hS : ∀ x ∈ S, StatedQuadMinus 3 F b c x = 0) : Nat.card S ≤ Nat.card F ^ 2 := by
  obtain ⟨U, hSU, -, hdim⟩ := exists_ts_span hirr S hS
  have hcardU : Nat.card U = Nat.card F ^ Module.finrank F U :=
    Module.natCard_eq_pow_finrank (K := F) (V := U)
  calc Nat.card S ≤ Nat.card U :=
        Nat.card_le_card_of_injective (fun s : S => (⟨(s : OW F), hSU _ s.2⟩ : U))
          (fun s s' h => Subtype.ext (by
            have := congrArg (fun u : U => (u : OW F)) h
            simpa using this))
    _ = Nat.card F ^ Module.finrank F U := hcardU
    _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_right Nat.card_pos hdim

theorem ts_eq_plane (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (S : AddSubgroup (OW F))
    (hS : ∀ x ∈ S, StatedQuadMinus 3 F b c x = 0) (hcard : Nat.card S = Nat.card F ^ 2) :
    ∃ Y : Submodule F (OW F), (∀ x, x ∈ S ↔ x ∈ Y) ∧ Module.finrank F Y = 2 ∧
      ∀ y ∈ Y, StatedQuadMinus 3 F b c y = 0 := by
  obtain ⟨U, hSU, hUs, hdim⟩ := exists_ts_span hirr S hS
  have hcardU : Nat.card U = Nat.card F ^ Module.finrank F U :=
    Module.natCard_eq_pow_finrank (K := F) (V := U)
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hinj : Function.Injective (fun s : S => (⟨(s : OW F), hSU _ s.2⟩ : U)) := fun s s' h =>
    Subtype.ext (by
      have := congrArg (fun u : U => (u : OW F)) h
      simpa using this)
  have hle : Nat.card S ≤ Nat.card U := Nat.card_le_card_of_injective _ hinj
  have hk : Module.finrank F U = 2 := by
    refine le_antisymm hdim ?_
    by_contra hlt
    push_neg at hlt
    have h3 : Nat.card F ^ Module.finrank F U < Nat.card F ^ 2 :=
      Nat.pow_lt_pow_right (by omega) hlt
    rw [← hcardU] at h3
    omega
  have hsurj : Function.Surjective (fun s : S => (⟨(s : OW F), hSU _ s.2⟩ : U)) :=
    (hinj.bijective_of_nat_card_le (by rw [hcard, hcardU, hk])).2
  refine ⟨U, fun x => ⟨fun hx => hSU x hx, fun hx => ?_⟩, hk, hUs⟩
  obtain ⟨s, hs⟩ := hsurj ⟨x, hx⟩
  have := congrArg (fun u : U => (u : OW F)) hs
  simp only at this
  rw [← this]
  exact s.2

end CFSG.LocalAnalysis.RankThreeUC
