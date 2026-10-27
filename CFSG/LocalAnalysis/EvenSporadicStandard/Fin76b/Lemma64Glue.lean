module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Config

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem map_fusionOddCore_le {P Q : Type*} [Group P] [Finite P] [Group Q] (e : P ≃* Q) :
    (fusionOddCore P).map e.toMonoidHom ≤ fusionOddCore Q := by
  have hN : ((fusionOddCore P).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  refine le_fusionOddCore ?_
  rw [Subgroup.card_map_of_injective e.injective]
  exact odd_natCard_fusionOddCore P

theorem map_fusionOddCore_mulEquiv {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
    (e : P ≃* Q) : (fusionOddCore P).map e.toMonoidHom = fusionOddCore Q := by
  refine le_antisymm (map_fusionOddCore_le e) fun y hy => ?_
  have h2 : e.symm y ∈ fusionOddCore P := map_fusionOddCore_le e.symm ⟨y, hy, rfl⟩
  exact ⟨e.symm y, h2, e.apply_symm_apply y⟩

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {z t : G} {T₀ : Subgroup G}

theorem lemma64_of_innerConfig (hSol : SolomonZ2A6) (h : InnerConfig G A z t T₀) {β : G}
    {K : Subgroup G} (hK : K = centralizer ({β} : Set G)) (hKG : CFSG.SectionRank.IsKGroupCat ↥K)
    (hD : Nonempty (↥(A ⊓ K) ⧸ fusionOddCore ↥(A ⊓ K) ≃* alternatingGroup (Fin 6)))
    (hO : fusionOddCoreOf (A ⊓ K) ≤ zpowers β) {zK : ↥K} (hzK : (zK : G) = z) :
    Lemma64Conclusion ↥K (QuotientGroup.mk zK) := by
  set DK : Subgroup K := (A ⊓ K).subgroupOf K with hDK
  have hcommβ : ∀ x : K, (x : G) * β = β * x := fun x =>
    mem_centralizer_singleton_iff.1 ((congrArg (fun S : Subgroup G => (x : G) ∈ S) hK).mp x.2)
  have hzK2 : orderOf zK = 2 := by
    rw [← Subgroup.orderOf_coe, hzK]
    exact h.z_order
  have hzβ : z * β = β * z := by
    rw [← hzK]
    exact hcommβ zK
  have hcent : centralizer ({zK} : Set K) = zpowers zK ⊔ DK := by
    refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · have hx1 : (x : G) * z = z * x := by
        have := mem_centralizer_singleton_iff.1 hx
        rw [← hzK]
        exact congrArg Subtype.val this
      have hx2 : (x : G) ∈ A ⊔ zpowers z := by
        rw [← h.cent_eq]
        exact mem_centralizer_singleton_iff.2 hx1
      obtain ⟨a, ha, c, hc, hxac⟩ := exists_mul_of_mem_sup_of_le_centralizer
        (zpowers_le.2 h.z_cent) hx2
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      have hcK : z ^ k ∈ K := by
        rw [hK, mem_centralizer_singleton_iff]
        exact (Commute.zpow_left (show Commute z β from hzβ) k).eq
      have haK : a ∈ K := by
        have : a = (x : G) * (z ^ k)⁻¹ := by rw [hxac]; group
        rw [this]
        exact mul_mem x.2 (inv_mem hcK)
      have hxe : x = (⟨a, haK⟩ : K) * zK ^ k := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_zpow, hzK]
        exact hxac
      rw [hxe]
      exact mul_mem (mem_sup_right (mem_subgroupOf.2 ⟨ha, haK⟩))
        (mem_sup_left (zpow_mem (mem_zpowers zK) k))
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    · intro d hd
      rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hzK]
      exact h.z_comm_of_mem_A (mem_subgroupOf.1 hd).1
  have hdisj : Disjoint (zpowers zK) DK := by
    rw [Subgroup.disjoint_def]
    intro x hxz hxD
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxz
    have h1 : z ^ k ∈ A := by
      have := (mem_subgroupOf.1 hxD).1
      simpa [hzK] using this
    have h2 : z ^ k ∈ A ⊓ zpowers z := ⟨h1, mem_zpowers_iff.2 ⟨k, rfl⟩⟩
    rw [h.disjoint.eq_bot, mem_bot] at h2
    apply Subtype.ext
    simpa [hzK] using h2
  let e : DK ≃* ↥(A ⊓ K) := Subgroup.subgroupOfEquivOfLe (inf_le_right : A ⊓ K ≤ K)
  have hmap : (fusionOddCore DK).map e.toMonoidHom = fusionOddCore ↥(A ⊓ K) :=
    map_fusionOddCore_mulEquiv e
  have hD' : Nonempty (DK ⧸ fusionOddCore DK ≃* alternatingGroup (Fin 6)) := by
    obtain ⟨eD⟩ := hD
    exact ⟨(QuotientGroup.congr (fusionOddCore DK) (fusionOddCore ↥(A ⊓ K)) e hmap).trans eD⟩
  have hDc : fusionOddCoreOf DK ≤ center K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_center_iff]
    intro g
    have h1 : e y ∈ fusionOddCore ↥(A ⊓ K) := hmap ▸ ⟨y, hy, rfl⟩
    have h2 : ((e y : ↥(A ⊓ K)) : G) ∈ zpowers β := hO ⟨e y, h1, rfl⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hy' : ((y : K) : G) = β ^ j := by rw [hj]; rfl
    show (g : G) * ((y : K) : G) = ((y : K) : G) * g
    rw [hy']
    exact (Commute.zpow_right (show Commute (g : G) β from hcommβ g) j).eq
  exact lemma64_of_solomon hSol hKG hzK2 hcent hdisj hDc hD'

end CFSG.EvenSporadicStandard.Fin76b
