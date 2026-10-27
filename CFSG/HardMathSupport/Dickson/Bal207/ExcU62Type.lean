module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.HardMathSupport.Dickson.Bal207.Corr
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open scoped commutatorElement

@[expose] def ExcU62CompIdx : TauCeti.LieTypeIndex → Prop
  | .twistedA r q => (r = 3 ∨ r = 4) ∧ IsTwoPow q 1
  | .A r q => r = 1 ∧ IsTwoPow q 3
  | _ => False

@[expose] def ExcU62Type (Q : Type) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, ExcU62CompIdx d.1 ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem excU62Type_isoInvariant : IsoInvariant ExcU62Type := by
  intro Q Q' _ _ e h
  obtain ⟨d, hd, ⟨a⟩⟩ := h
  exact ⟨d, hd, ⟨e.symm.trans a⟩⟩

theorem excU62CompIdx_cases {d : TauCeti.LieTypeIndex} (h : ExcU62CompIdx d) :
    (Bal207Index 3 d ∧ ¬ IsG2EightIndex d) ∨ IsL2EightIndex d := by
  cases d with
  | twistedA r q =>
    obtain ⟨hr, hq⟩ := h
    refine Or.inl ⟨⟨rfl, Or.inl ⟨Or.inl hq, ?_⟩⟩, fun h => h⟩
    rcases hr with rfl | rfl <;> omega
  | A r q => exact Or.inr h
  | _ => exact h.elim

theorem excU62_perfect_le_of_derived {G : Type*} [Group G] {X P Y : Subgroup G} (hPX : P ≤ X)
    (hP : ⁅P, P⁆ = P) (hY : ∃ k : ℕ, ∀ x ∈ derivedSeries ↥X k, (x : G) ∈ Y) : P ≤ Y := by
  obtain ⟨k, hk⟩ := hY
  have key : ∀ n : ℕ, P ≤ (derivedSeries ↥X n).map X.subtype := by
    intro n
    induction n with
    | zero =>
      intro x hx
      exact ⟨⟨x, hPX hx⟩, by rw [derivedSeries_zero]; exact Subgroup.mem_top _, rfl⟩
    | succ n ih =>
      rw [derivedSeries_succ, Subgroup.map_commutator]
      calc P = ⁅P, P⁆ := hP.symm
        _ ≤ _ := Subgroup.commutator_mono ih ih
  intro x hx
  obtain ⟨y, hy, rfl⟩ := key k hx
  exact hk y hy

theorem excU62_map_fixSubgroup_of_commute {S : Type} [Group S] (β ω : MulAut S)
    (hω : ω * β = β * ω) : (fixSubgroup β).map ω.toMonoidHom = fixSubgroup β := by
  have hcomm : ∀ x, ω (β x) = β (ω x) := fun x => congrArg (fun φ : MulAut S => φ x) hω
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : β x = x := hx
    show β (ω x) = ω x
    rw [← hcomm, hx']
  · intro hy
    have hy' : β y = y := hy
    refine ⟨ω.symm y, ?_, ω.apply_symm_apply y⟩
    show β (ω.symm y) = ω.symm y
    apply ω.injective
    rw [hcomm, ω.apply_symm_apply]
    exact hy'

theorem excU62_compShape_of_unique {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    (β : MulAut S) (N : Subgroup S) (hlayer : PerfectInLayer β)
    (hall : ∀ L : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup β) → L = N)
    (hT : T (↥N ⧸ Subgroup.center ↥N)) : CompShape T β where
  layer := hlayer
  type := fun L hL => by
    rw [hall L hL]
    exact hT
  norm := fun ω hω L hL => by
    have h1 : CFSG.Open.IsComponentOf (L.map ω.toMonoidHom) ((fixSubgroup β).map ω.toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (ω : S ≃* S) hL
    rw [excU62_map_fixSubgroup_of_commute β ω hω] at h1
    rw [hall _ h1, hall L hL]

theorem excU62_nontrivial_of_isQuasisimple {Q : Type*} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) :
    Nontrivial Q := by
  haveI := hq.2.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial

theorem excU62_compShape_of_core {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S] [Finite S]
    (β : MulAut S) (N : Subgroup S)
    (hN : N = ⊥ ∨ (CFSG.Open.IsComponentOf N (fixSubgroup β) ∧ T (↥N ⧸ Subgroup.center ↥N)))
    (hperf : ∀ P : Subgroup S, P ≤ fixSubgroup β → ⁅P, P⁆ = P → P ≤ N) : CompShape T β := by
  rcases hN with hNb | ⟨hcomp, hT⟩
  · have hnot : ∀ L : Subgroup S, ¬ CFSG.Open.IsComponentOf L (fixSubgroup β) := by
      intro L hL
      have hLb : L ≤ ⊥ := (hperf L hL.1 (Subgroup.isPerfect_iff.1 ⟨hL.2.2.1⟩)).trans hNb.le
      haveI := excU62_nontrivial_of_isQuasisimple hL.2.2
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
      exact hx (Subtype.ext (Subgroup.mem_bot.1 (hLb x.2)))
    exact ⟨fun P hPC hP => (hperf P hPC hP).trans (hNb.le.trans bot_le),
      fun L hL => (hnot L hL).elim, fun ω _ L hL => (hnot L hL).elim⟩
  · have hall : ∀ L : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup β) → L = N := by
      intro L hL
      obtain ⟨-, hLN⟩ := LieComp.component_mem_named_factors (ι := Unit) (fun _ => N)
        (fun _ => hcomp)
        (fun P hPC hP => by
          rw [iSup_const]
          exact hperf P hPC (Subgroup.isPerfect_iff.1 ⟨hP⟩)) hL
      exact hLN
    exact excU62_compShape_of_unique β N
      (fun P hPC hP => (hperf P hPC hP).trans (le_sSup hcomp)) hall hT

end CFSG.HardMathSupport.Dickson.Bal207

end
