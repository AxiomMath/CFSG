module

public import CFSG.ClassicalInvolution.Generic.InductionLocal
public import CFSG.ClassicalInvolution.Generic.StepMember
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {p f : ℕ} [Fact p.Prime] {Y₀ : Type} [Group Y₀]

abbrev conjFamily (L : Subgroup Y₀) : Set (Subgroup Y₀) := Set.range fun g : Y₀ => conjSub g L

abbrev conjGen (L : Subgroup Y₀) : Subgroup Y₀ := ⨆ M ∈ conjFamily L, M

theorem le_conjGen {L M : Subgroup Y₀} (hM : M ∈ conjFamily L) : M ≤ conjGen L :=
  le_iSup₂ (f := fun (M : Subgroup Y₀) (_ : M ∈ conjFamily L) => M) M hM

theorem inClass_restrict_conjugates {L : Subgroup Y₀} {z : Y₀}
    (h : IsClassicalMember p f L z) :
    InClass p f (restrictFamily (conjFamily L) (conjGen L)) where
  nonempty := ⟨L.subgroupOf (conjGen L), L, ⟨1, conjSub_one L⟩, le_conjGen ⟨1, conjSub_one L⟩, rfl⟩
  conjInvariant := by
    rintro n _ ⟨M, ⟨g, rfl⟩, -, rfl⟩
    have hmem : conjSub (n : Y₀) (conjSub g L) ∈ conjFamily L := ⟨n * g, conjSub_mul _ _ L⟩
    exact ⟨conjSub (n : Y₀) (conjSub g L), hmem, le_conjGen hmem,
      conjSub_subgroupOf (conjGen L) n (conjSub g L)⟩
  generated := by
    set S := conjFamily L with hS
    have key := iSup_subgroupOf_self (G := Y₀) (fun i : S => (i : Subgroup Y₀))
    have hsup : (⨆ i : S, (i : Subgroup Y₀)) = conjGen L := by
      rw [conjGen, iSup_subtype']
    rw [hsup] at key
    refine eq_top_iff.mpr (key.symm.le.trans ?_)
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (L' : Subgroup (conjGen L))
      (_ : L' ∈ restrictFamily S (conjGen L)) => L')
      ((i : Subgroup Y₀).subgroupOf (conjGen L)) ⟨i, i.2, le_conjGen i.2, rfl⟩
  classical := by
    rintro _ ⟨M, ⟨g, rfl⟩, hM, rfl⟩
    exact ⟨_, (h.conj g).subgroupOf p f hM⟩

theorem lieSystemMod_restrict_conjugates [Finite Y₀] {L : Subgroup Y₀} {z : Y₀}
    (h : IsClassicalMember p f L z) {n : ℕ} (hn : Nat.card Y₀ < n) (hIH : CITBelowU p f n) :
    LieSystemMod p f (restrictFamily (conjFamily L) (conjGen L)) :=
  hIH _ ((Subgroup.card_le_card_group _).trans_lt hn) _ (inClass_restrict_conjugates h)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
