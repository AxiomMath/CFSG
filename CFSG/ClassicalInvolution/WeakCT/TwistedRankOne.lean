module

public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open scoped MatrixGroups

section RankOne

variable {K : Type} [Group K] {D : UniversalRootDatum K} {i : Fin D.rank} {F : Type} [Field F]

theorem rankOne_eq_range_of_param (r : SL(2, F) →* K)
    (hu : ∀ c, r (tv 0 1 c) ∈ D.rootGroup (Pi.single i 1))
    (hl : ∀ c, r (tv 1 0 c) ∈ D.rootGroup (-Pi.single i 1))
    (hpu : ∀ g ∈ D.rootGroup (Pi.single i 1), ∃ c, r (tv 0 1 c) = g)
    (hpl : ∀ g ∈ D.rootGroup (-Pi.single i 1), ∃ c, r (tv 1 0 c) = g) :
    CFSG.LieType.CurtisTits.rankOne D.rootGroup i = r.range := by
  refine le_antisymm (sup_le ?_ ?_) ?_
  · intro g hg
    obtain ⟨c, rfl⟩ := hpu g hg
    exact ⟨tv 0 1 c, rfl⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := hpl g hg
    exact ⟨tv 1 0 c, rfl⟩
  · exact range_le_of_tv r _ (fun c => Subgroup.mem_sup_left (hu c))
      (fun c => Subgroup.mem_sup_right (hl c))

end RankOne

section Generation

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.Blueprint CFSG.Timmesfeld

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_eq_weylAction_single_of_divisible_eq_empty (hdiv : D.divisible = ∅)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ∃ w i, γ = weylAction D.isFiniteType w (Pi.single i 1) := by
  have hγ' : γ ∈ CFSG.LieType.RootSystem.roots D.isFiniteType D.divisible := hγ
  rw [CFSG.LieType.RootSystem.roots, hdiv] at hγ'
  rcases hγ' with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · exact ⟨w, i, rfl⟩
  · exact absurd hi (Set.notMem_empty i)

theorem iSup_rankOne_eq_top_of_ct
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hdiv : D.divisible = ∅) :
    ⨆ k, CFSG.LieType.CurtisTits.rankOne D.rootGroup k = ⊤ := by
  set L := ⨆ k, CFSG.LieType.CurtisTits.rankOne D.rootGroup k with hL
  have hk : ∀ k, CFSG.LieType.CurtisTits.rankOne D.rootGroup k ≤ L := fun k =>
    le_iSup (fun k => CFSG.LieType.CurtisTits.rankOne D.rootGroup k) k
  have hw : ∀ w, Steinberg.nrep hct w ∈ L := fun w =>
    posLift_mem _ _ _ L (fun k => hk k (hct.n_mem k)) w
  rw [eq_top_iff, ← hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single_of_divisible_eq_empty hdiv hγ
  rw [← actsAs_nrep hct w _
    ((Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)]
  rintro _ ⟨x, hx, rfl⟩
  exact L.mul_mem (L.mul_mem (hw w) (hk i (Subgroup.mem_sup_left hx))) (L.inv_mem (hw w))

end Generation

section Pairs

theorem linearBlockStandardPair_of_levi {K F : Type} [Group K] [Field F] (emb : SL(3, F) →* K)
    (hinj : Function.Injective emb) {U V : Subgroup K}
    (hU : U = (emb.comp (blk F 0)).range) (hV : V = (emb.comp (blk F 1)).range) :
    ∃ W, LinearBlockStandardPair F W U V := by
  have hc : ∀ H : Subgroup SL(3, F), H.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = H :=
    fun H => by ext x; simp
  refine ⟨emb.range, emb, 1, rfl, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [(MonoidHom.ker_eq_bot_iff _).mpr hinj]
    exact bot_le
  · rw [hc, hU, MonoidHom.range_comp]
    rfl
  · rw [hc, hV, MonoidHom.range_comp]
    rfl

end Pairs

end CFSG.ClassicalInvolution.WeakCT
