module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnCore

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal

namespace Up34Exc

section Embedding

variable {C G : Type} [Group C] [Group G]

theorem map_fixSubgroup_eq_of_conj (ι : C →* G) (hι : Function.Injective ι) (β : MulAut C) (y : G)
    (hy : ∀ s, ι (β s) = y * ι s * y⁻¹) :
    (fixSubgroup β).map ι = ι.range ⊓ Subgroup.centralizer {y} := by
  apply le_antisymm
  · rintro _ ⟨s, hs, rfl⟩
    have hβs : β s = s := mem_fixSubgroup.1 hs
    have h1 : ι s = y * ι s * y⁻¹ := by rw [← hy s, hβs]
    have hcomm : ι s * y = y * ι s := by
      calc ι s * y = (y * ι s * y⁻¹) * y := by rw [← h1]
        _ = y * ι s := inv_mul_cancel_right _ _
    exact Subgroup.mem_inf.2
      ⟨MonoidHom.mem_range.2 ⟨s, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  · intro x hx
    obtain ⟨hr, hc⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hr
    have hcomm : ι s * y = y * ι s := Subgroup.mem_centralizer_singleton_iff.1 hc
    refine Subgroup.mem_map.2 ⟨s, ?_, rfl⟩
    rw [mem_fixSubgroup]
    apply hι
    rw [hy s, ← hcomm, mul_inv_cancel_right]

theorem isComponentOf_map_inj {L K : Subgroup C} (h : IsComponentOf L K) (ι : C →* G)
    (hι : Function.Injective ι) : IsComponentOf (L.map ι) (K.map ι) := by
  obtain ⟨hLK, hsub, hq⟩ := h
  exact ⟨Subgroup.map_mono hLK, isSubnormal_map hsub ι hι,
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L ι hι) hq⟩

theorem noL34Layer_of_embedding [Finite C] (ι : C →* G) (hι : Function.Injective ι) (β : MulAut C)
    (y : G) (hy : ∀ s, ι (β s) = y * ι s * y⁻¹) (hP : PerfectInLayer β)
    (hno : ∀ K : Subgroup G, IsComponentOf K (ι.range ⊓ Subgroup.centralizer {y}) →
      IsLThreeFour (↥K ⧸ Subgroup.center ↥K) →
        ∃ z : G, z ∈ K ∧ (∀ g ∈ K, g * z = z * g) ∧ z ^ 3 = 1 ∧ z ≠ 1) :
    Up34Chev2.NoL34Layer β := by
  intro I hI hT
  obtain ⟨hcomp, hIT, hIZ⟩ := Up34Chev2.exists_component_of_isLThreeFour_two hP hI hT
  have hfix := map_fixSubgroup_eq_of_conj ι hι β y hy
  have hK : IsComponentOf (I.map ι) (ι.range ⊓ Subgroup.centralizer {y}) := by
    rw [← hfix]
    exact isComponentOf_map_inj hcomp ι hι
  let e : ↥I ≃* ↥(I.map ι) := Subgroup.equivMapOfInjective I ι hι
  have hIq : CFSG.Open.IsQuasisimple ↥I := hcomp.2.2
  have hperf : Group.IsPerfect ↥I := ⟨hIq.1⟩
  have hker : (e : ↥I →* ↥(I.map ι)).ker ≤ Subgroup.center ↥I := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  obtain ⟨eq⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf (e : ↥I →* ↥(I.map ι))
    e.surjective hker
  obtain ⟨z, hzK, hzc, hz3, hz1⟩ := hno (I.map ι) hK (IsLThreeFour.of_mulEquiv eq hIT)
  obtain ⟨c, hcI, rfl⟩ := Subgroup.mem_map.1 hzK
  have hcent : (⟨c, hcI⟩ : ↥I) ∈ Subgroup.center ↥I := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply hι
    have := hzc (ι g) (Subgroup.mem_map_of_mem ι g.2)
    simpa [map_mul] using this
  have h3 : (⟨c, hcI⟩ : ↥I) ^ 3 = 1 := by
    apply Subtype.ext
    apply hι
    simpa [map_pow] using hz3
  have h1 : (⟨c, hcI⟩ : ↥I) = 1 := hIZ _ hcent h3
  apply hz1
  have : c = 1 := congrArg Subtype.val h1
  rw [this, map_one]

end Embedding

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
