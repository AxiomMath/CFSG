module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.FrameCentralizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureE8

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Defs


@[expose] def FrameDetection (τ : Tag) (K : Type) [Field K] (S : Set (Fin τ.rank → ℤ)) : Prop :=
  ∀ H : Subgroup (ModGL τ K), H ≤ adjointGroup τ K → rootSpan τ K S ≤ H →
    ¬ H ≤ Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) →
      ∃ β, IsRoot τ β ∧ β ∉ S ∧ ∃ c : K, c ≠ 0 ∧ pinnedX τ K β c ∈ H

end Defs

theorem cartan_unit_pairing_E8 : ∀ α ∈ rootFinset .E8, α k4 % 5 ≠ 0 →
    ∃ k : Fin Tag.E8.rank, k ≠ k4 ∧ (∑ j, Tag.E8.cartan k j * α j) ∈ ({1, -1} : Finset ℤ) := by
  decide +kernel

section Certs


theorem pinnedX_mem_of_pairing {τ : Tag} {K : Type} [Field K] {S : Set (Fin τ.rank → ℤ)}
    {k : Fin τ.rank} (h1 : (Pi.single k 1 : Fin τ.rank → ℤ) ∈ S)
    (h2 : (-Pi.single k 1 : Fin τ.rank → ℤ) ∈ S) {H : Subgroup (ModGL τ K)}
    (hX : rootSpan τ K S ≤ H) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hp : ∑ j, τ.cartan k j * β j = ε) {c : K} (hc : c ≠ 0)
    (hm : pinnedX τ K β c ∈ H) (e : K) : pinnedX τ K β e ∈ H := by
  by_cases he : e = 0
  · subst he
    rw [pinnedX_zero]
    exact H.one_mem
  set u : Kˣ := Units.mk0 (e / c) (div_ne_zero he hc) with hu
  set t : Kˣ := u ^ ε with ht
  have hd : rootDiagUnit τ (fun j => t ^ τ.cartan k j) ∈ H := by
    rw [← torusElt_eq_rootDiagUnit]
    exact hX (torusElt_mem_rootSpan h1 h2 t)
  have hmem := H.mul_mem (H.mul_mem hd hm) (H.inv_mem hd)
  rw [rootDiagUnit_conj_pinnedX _ hβ, rootChar_cartan_zpow, hp] at hmem
  have htu : t ^ ε = u := by
    rcases hε with rfl | rfl <;> simp [ht]
  rw [htu] at hmem
  have hue : ((u : Kˣ) : K) * c = e := by
    simp [hu, div_mul_cancel₀ _ hc]
  rwa [hue] at hmem

theorem frameClosing_of_detection_E8 (K : Type) [Field K]
    (hD : FrameDetection .E8 K (cosetRoots .E8 k4 5)) :
    FrameClosing .E8 K (cosetRoots .E8 k4 5) := by
  intro H hH hX hN
  obtain ⟨β, hβ, hβS, c, hc, hm⟩ := hD H hH hX hN
  have hβ5 : β k4 % 5 ≠ 0 := by
    intro h0
    exact hβS ⟨hβ, by exact_mod_cast Int.dvd_of_emod_eq_zero h0⟩
  obtain ⟨k, hk, hpair⟩ := cartan_unit_pairing_E8 β (mem_rootFinset.2 hβ) hβ5
  have hsingle : (Pi.single k 1 : Fin Tag.E8.rank → ℤ) k4 = 0 := by
    simp [Ne.symm hk]
  have h1 : (Pi.single k 1 : Fin Tag.E8.rank → ℤ) ∈ cosetRoots .E8 k4 5 :=
    ⟨IsRoot.basis k, by rw [hsingle]; exact dvd_zero _⟩
  have h2 : (-Pi.single k 1 : Fin Tag.E8.rank → ℤ) ∈ cosetRoots .E8 k4 5 :=
    ⟨isRoot_neg_single _ k, by rw [Pi.neg_apply, hsingle, neg_zero]; exact dvd_zero _⟩
  have hU : rootSubgroup .E8 K β ≤ H := by
    intro g hg
    obtain ⟨e, rfl⟩ := mem_rootSubgroup.1 hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    exact pinnedX_mem_of_pairing h1 h2 hX hβ hpair rfl hc hm e
  exact eq_top_of_rootSubgroup_le_E8 H hH hX hβ hβS hU

end Certs

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
