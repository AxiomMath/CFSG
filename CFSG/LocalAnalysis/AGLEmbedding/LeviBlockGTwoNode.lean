module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeEscape
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock

public section

namespace CFSG.AGLEmbedding.LeviBlock

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped commutatorElement

variable {K Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem le_torus_sup_of_negIndices_eq (h : BorelQuotient D n H π M) {A : Subgroup K}
    (hBA : borel D H ≤ A) {i : Fin D.rank} (hI : negIndices D A = {i}) :
    A ≤ (⨆ k, H k) ⊔ (rankOne D.rootGroup i ⊔ posUnipotentExcept D i) := by
  rw [eq_borel_sup_rankOne h.ct h.extras hBA, hI]
  refine sup_le ?_ (iSup₂_le fun j hj => ?_)
  · rw [CFSG.LieType.Steinberg.borel, posUnipotent_eq_sup h.extras i]
    refine sup_le le_sup_left (sup_le (le_sup_of_le_right le_sup_right) ?_)
    exact le_sup_of_le_right (le_sup_of_le_left le_sup_left)
  · rw [Set.mem_singleton_iff.1 hj]
    exact le_sup_of_le_right le_sup_left

theorem posUnipotentExcept_le_of_borel_le {A : Subgroup K} (hBA : borel D H ≤ A)
    (i : Fin D.rank) : posUnipotentExcept D i ≤ A :=
  ((posUnipotentExcept_le_posUnipotent i).trans posUnipotent_le_borel).trans hBA

theorem isPGroup_posUnipotentExcept (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    IsPGroup 2 (posUnipotentExcept D i) :=
  (isPGroup_iSup_pos h.extras h.pGroup).to_le (posUnipotentExcept_le_posUnipotent i)

theorem le_normalizer_posUnipotentExcept_of_negIndices_eq [Finite K]
    (h : BorelQuotient D n H π M) {A : Subgroup K} (hBA : borel D H ≤ A) {i : Fin D.rank}
    (hI : negIndices D A = {i}) : A ≤ Subgroup.normalizer (posUnipotentExcept D i : Set K) :=
  (le_torus_sup_of_negIndices_eq h hBA hI).trans
    (sup_le (ToralCensus.iSup_torus_le_normalizer_posUnipotentExcept h.ct i)
      (sup_le (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i) Subgroup.le_normalizer))

theorem commutator_mem_of_negIndices_eq [Finite K] (h : BorelQuotient D n H π M)
    {A : Subgroup K} (hBA : borel D H ≤ A) {i : Fin D.rank} (hI : negIndices D A = {i})
    {a b : K} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅a, b⁆ ∈ rankOne D.rootGroup i ⊔ posUnipotentExcept D i :=
  commutator_mem_of_mem_torus_sup (fun _ ht => ParabAutIrr.mem_normalizer_sup
      (iSup_torus_le_normalizer_rankOne h.ct i ht)
      (ToralCensus.iSup_torus_le_normalizer_posUnipotentExcept h.ct i ht))
    (fun _ hx _ hy => h.torus_mul_comm hx hy) (le_torus_sup_of_negIndices_eq h hBA hI ha)
    (le_torus_sup_of_negIndices_eq h hBA hI hb)

theorem rankOne_inf_posUnipotentExcept_eq_bot [Finite K] (h : BorelQuotient D n H π M)
    (i : Fin D.rank) [IsSimpleGroup ↥(rankOne D.rootGroup i)]
    (hnc : ∃ a b : ↥(rankOne D.rootGroup i), a * b ≠ b * a) :
    rankOne D.rootGroup i ⊓ posUnipotentExcept D i = ⊥ :=
  inf_eq_bot_of_simple_of_isPGroup hnc (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i)
    (isPGroup_posUnipotentExcept h i)

theorem exists_leviData_of_negIndices_eq [Finite K] (h : BorelQuotient D n H π M)
    {A : Subgroup K} (hBA : borel D H ≤ A) {i : Fin D.rank} (hI : negIndices D A = {i})
    (hLU : rankOne D.rootGroup i ⊓ posUnipotentExcept D i = ⊥) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (S : Subgroup G) (β : ↥A →* (Fin 1 → G)),
      IsPGroup 2 β.ker ∧ Subgroup.pi Set.univ (fun _ => S) ≤ β.range ∧
      ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ (fun _ => S) ∧
      Nonempty (↥(rankOne D.rootGroup i) ≃* ↥S) := by
  set U := (posUnipotentExcept D i).subgroupOf A with hU
  set Λ := (rankOne D.rootGroup i).subgroupOf A with hΛ
  have hUA := posUnipotentExcept_le_of_borel_le hBA i
  have hLA : rankOne D.rootGroup i ≤ A := rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have : U.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUA).mpr
    (le_normalizer_posUnipotentExcept_of_negIndices_eq h hBA hI)
  have hU2 : IsPGroup 2 U := (isPGroup_posUnipotentExcept h i).comap_subtype
  have hc : ∀ a b : ↥A, ⁅a, b⁆ ∈ Λ ⊔ U := fun a b => by
    rw [hΛ, hU, ← Subgroup.subgroupOf_sup hLA hUA, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using commutator_mem_of_negIndices_eq h hBA hI a.2 b.2
  have hΛU : Λ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx : (x : K) ∈ rankOne D.rootGroup i ⊓ posUnipotentExcept D i := ⟨hx1, hx2⟩
    rw [hLU, Subgroup.mem_bot] at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext hx)
  obtain ⟨e⟩ := nonempty_mulEquiv_oneBlock U Λ hΛU
  exact ⟨↥A ⧸ U, inferInstance, inferInstance, Λ.map (QuotientGroup.mk' U), _,
    isPGroup_ker_oneBlock U hU2, pi_le_range_oneBlock U Λ, commutator_range_oneBlock_le U Λ hc,
    ⟨(Subgroup.subgroupOfEquivOfLe hLA).symm.trans e⟩⟩

end CFSG.AGLEmbedding.LeviBlock
