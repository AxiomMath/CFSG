module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Coordinates
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.ConjSub

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem rootSpan_mono_of_subset {A B : Set (Fin τ.rank → ℤ)} (h : A ⊆ B) :
    rootSpan τ K A ≤ rootSpan τ K B :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (h hα) le_rfl

theorem rootSubgroup_le_rootSpan_of_mem {S : Set (Fin τ.rank → ℤ)} {α : Fin τ.rank → ℤ}
    (h : α ∈ S) : rootSubgroup τ K α ≤ rootSpan τ K S :=
  le_iSup₂_of_le α h le_rfl

theorem pinnedX_mem_Qθ_of_mem_Deg1 {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) (c : K) :
    pinnedX τ K β c ∈ Qθ τ K := by
  refine pinnedX_mem_rootSpan ?_ c
  have h0 : β (iθ τ) = 1 := hβ.2
  rw [mem_parabolicRadicalRoots_iff]
  refine ⟨hβ.1, ?_, iθ τ, fun h => h rfl, ?_⟩
  · rcases IsRoot.height_pos_or_neg hβ.1 with hp | hn
    · exact hp
    · exfalso
      have := (IsRoot.height_neg_iff hβ.1).1 hn (iθ τ)
      omega
  · omega

theorem rootSubgroup_le_Qθ_of_mem_Deg1 {β : Fin τ.rank → ℤ} (hβ : β ∈ Deg1 τ) :
    rootSubgroup τ K β ≤ Qθ τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨e, rfl⟩
  exact pinnedX_mem_Qθ_of_mem_Deg1 hβ e

theorem Uθ_le_Qθ : Uθ τ K ≤ Qθ τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine pinnedX_mem_rootSpan ?_ c
  rw [mem_parabolicRadicalRoots_iff]
  refine ⟨isRoot_highRoot τ, height_highRoot_pos τ, iθ τ, fun h => h rfl, ?_⟩
  rw [CoordAux.highRoot_degree]
  omega

theorem conjSub_le_Qθ {p : ModGL τ K} (hp : p ∈ Pθ τ K) {A : Subgroup (ModGL τ K)}
    (hA : A ≤ Qθ τ K) : conjSub p A ≤ Qθ τ K := by
  intro x hx
  have h1 : p⁻¹ * x * p ∈ Qθ τ K := hA (mem_conjSub_iff.1 hx)
  have hn := Pθ_le_normalizer_Qθ τ K hp
  have h2 := (Subgroup.mem_normalizer_iff.1 hn (p⁻¹ * x * p)).1 h1
  have e : p * (p⁻¹ * x * p) * p⁻¹ = x := by group
  rwa [e] at h2

theorem heisCoord_prodX {L : List (Fin τ.rank → ℤ)} (hnd : L.Nodup) (hD : ∀ β ∈ L, β ∈ Deg1 τ)
    (c : (Fin τ.rank → ℤ) → K) :
    CoordAux.prodX L c ∈ Qθ τ K ∧
      ∀ ν, heisCoord τ K (CoordAux.prodX L c) ν = if ν ∈ L then c ν else 0 := by
  classical
  have hs := heisCoord_spec τ K
  induction L with
  | nil =>
    refine ⟨by rw [CoordAux.prodX_nil]; exact one_mem _, fun ν => ?_⟩
    rw [CoordAux.prodX_nil, heisCoord_one]
    simp
  | cons a L ih =>
    have hna : a ∉ L := (List.nodup_cons.1 hnd).1
    have hL : L.Nodup := (List.nodup_cons.1 hnd).2
    obtain ⟨hQ, hc⟩ := ih hL fun β hβ => hD β (List.mem_cons_of_mem _ hβ)
    have hQa := pinnedX_mem_Qθ_of_mem_Deg1 (K := K) (hD a List.mem_cons_self) (c a)
    refine ⟨by rw [CoordAux.prodX_cons]; exact mul_mem hQa hQ, fun ν => ?_⟩
    rw [CoordAux.prodX_cons, hs.mul _ hQa _ hQ,
      hs.pinnedX_deg1 a (hD a List.mem_cons_self) (c a)]
    simp only [Pi.add_apply, hc ν]
    by_cases hν : ν = a
    · subst hν
      simp [hna]
    · simp [hν, Ne.symm hν]

theorem exists_prodX_of_support {L : List (Fin τ.rank → ℤ)} (hnd : L.Nodup)
    (hD : ∀ β ∈ L, β ∈ Deg1 τ) {q : ModGL τ K} (hq : q ∈ Qθ τ K)
    (hs : ∀ ν, ν ∉ L → heisCoord τ K q ν = 0) :
    ∃ u ∈ Uθ τ K, q = u * CoordAux.prodX L (heisCoord τ K q) := by
  classical
  have hspec := heisCoord_spec τ K
  obtain ⟨hQ, hc⟩ := heisCoord_prodX hnd hD (heisCoord τ K q)
  have hcs : heisCoord τ K (CoordAux.prodX L (heisCoord τ K q)) = heisCoord τ K q := by
    funext ν
    rw [hc ν]
    by_cases hν : ν ∈ L
    · rw [if_pos hν]
    · rw [if_neg hν, hs ν hν]
  refine ⟨q * (CoordAux.prodX L (heisCoord τ K q))⁻¹, ?_, by group⟩
  refine (hspec.eq_zero_iff _ (mul_mem hq (inv_mem hQ))).1 ?_
  rw [hspec.mul _ hq _ (inv_mem hQ), heisCoord_inv hQ, hcs]
  abel

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
