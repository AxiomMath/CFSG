module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltHeartFaithful
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasicAux
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open CFSG.AGLEmbedding (blockV)
open CFSG.RankThree.PartTwo (altHeart)
open CFSG.Quasithin (IsMaxElemAbelian)
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

variable {G : Type} [Group G]

theorem isElemAb2_of_isElemAbelian {B : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 B) :
    IsElemAb2 B := by
  intro a ha
  refine ⟨?_, fun b hb => ?_⟩
  · have := h.2 a ha
    simpa [pow_two] using this
  · have := h.1.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩
    exact congrArg Subtype.val this

theorem isElemAbelian_of_isElemAb2 {B : Subgroup G} (h : IsElemAb2 B) :
    CFSG.Open.IsElemAbelian 2 B := by
  refine ⟨⟨⟨fun a b => Subtype.ext ((h a.1 a.2).2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
  simpa [pow_two] using (h x hx).1

theorem theta_eq_one_iff {U M V : Subgroup G} {d : ℕ} (hd : 5 ≤ d)
    {π : ↥U →* Multiplicative (altHeart d)} (hπ : Function.Surjective π)
    {θ : ↥M →* Equiv.Perm (Fin d)} (hequiv : SectionEquiv U M π θ) (hUV : U ≤ V)
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ Subgroup.centralizer (V : Set G)) (m : ↥M) :
    θ m = 1 ↔ (m : G) ∈ Subgroup.centralizer (V : Set G) := by
  refine ⟨hker m, fun hm => perm_eq_one_of_altHeart_fixed hd _ fun x => ?_⟩
  obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (QuotientAddGroup.mk x : altHeart d))
  have hcomm : ((u : G)) = (m : G) * u * (m : G)⁻¹ := by
    have := Subgroup.mem_centralizer_iff.1 hm (u : G) (hUV u.2)
    rw [← this]; group
  have := hequiv m u u hcomm x (by rw [hu]; rfl)
  rw [hu] at this
  exact this.symm

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
