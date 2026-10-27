module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.ChevLD
public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev

variable {T : TwistTag} {K : Type} [Field K] [Finite K] {p : ℕ} [CharP K p] {D : LongestData T}

theorem mem_X_chevDatumLD
    {i : Fin T.tag.rank} {x : adjointGroup T.tag K} :
    x ∈ (chevDatumLD T K p D).X i ↔ ∃ c : K, xC T.tag K i c = x := by
  change (x : ModGL T.tag K) ∈ rootSubgroup T.tag K (Pi.single i 1) ↔ _
  rw [mem_rootSubgroup_single]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc⟩, fun ⟨c, hc⟩ => ⟨c, congrArg Subtype.val hc⟩⟩

theorem xC_mem_X_LD
    (i : Fin T.tag.rank) (c : K) : xC T.tag K i c ∈ (chevDatumLD T K p D).X i :=
  mem_X_chevDatumLD.mpr ⟨c, rfl⟩

theorem heckeT_chevDatumLD
    [Fintype K] {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (adjointGroup T.tag K) V) (i : Fin T.tag.rank) (v : V) :
    (chevDatumLD T K p D).heckeT ρ i v = ∑ c : K, ρ (xC T.tag K i c * nC T.tag K i) v := by
  have := Fintype.ofFinite ((chevDatumLD T K p D).X i)
  rw [CurtisDatum.heckeT_apply]
  symm
  refine Fintype.sum_bijective (fun c => ⟨xC T.tag K i c, xC_mem_X_LD i c⟩) ⟨fun c d h =>
    xC_injective i (congrArg Subtype.val h), fun x => ?_⟩ _ _ fun c => rfl
  obtain ⟨c, hc⟩ := mem_X_chevDatumLD.mp x.2
  exact ⟨c, Subtype.ext hc⟩

variable (T K p D) in
@[expose] def IsChevTypeLD
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (adjointGroup T.tag K) V) (y : V) (χ : adjointGroup T.tag K → k)
    (J : Finset (Fin T.tag.rank)) : Prop :=
  y ∈ (chevDatumLD T K p D).fixU ρ ∧ y ≠ 0 ∧ (∀ h ∈ (chevDatumLD T K p D).H, ρ h y = χ h • y) ∧
    ∀ i, i ∈ J ↔ (∀ t : Kˣ, χ (dC T.tag K i t) = 1) ∧ (chevDatumLD T K p D).heckeT ρ i y = 0

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
