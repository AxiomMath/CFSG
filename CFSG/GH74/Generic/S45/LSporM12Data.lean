module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLiftClasses

public section

namespace CFSG.GH74.Generic.S45.LAlt

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.M12Cover

theorem exists_order_four_centralizerIn_m12Rep2 :
    ∃ g ∈ centralizerIn NativeSporadic.M12 m12Rep2, orderOf g = 4 := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  rw [centralizerIn_m12Rep2]
  have h := checkK3_eq
  simp only [checkK3, Bool.and_eq_true] at h
  obtain ⟨⟨hok, hsz⟩, hord⟩ := h
  have hgs : ∀ g ∈ k3Gens, g ∈ m12CentQ2.originalSubgroup := fun g hg => by
    rw [m12CentQ2, certificate_originalSubgroup]
    exact Subgroup.subset_closure hg
  have hmem : evalCodes k3Gens [-2, -3] ∈ k3Reps := by simp [k3Reps]
  exact ⟨evalCodes k3Gens [-2, -3], evalCodes_mem _ hgs _,
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (List.mem_map_of_mem hmem))⟩

theorem m12_involution_data
    (t : NativeSporadic.M12) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.M12)) = 192 ∨
      (Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.M12)) = 240 ∧ fixedCount t = 0 ∧
        ∃ g ∈ Subgroup.centralizer ({t} : Set NativeSporadic.M12), orderOf g = 4) := by
  obtain ⟨r, hr, c, hc, hvc⟩ := m12_involution_cover.1 (t : Equiv.Perm (Fin 12))
    (by rw [inv_one, one_mul]; exact t.2) (by rw [Subgroup.orderOf_coe, ht])
  have hrM := (m12_reps_mem r hr).1
  have ht' : t = ⟨c, hc⟩ * ⟨r, hrM⟩ * (⟨c, hc⟩ : NativeSporadic.M12)⁻¹ := Subtype.ext hvc
  have hcard : Nat.card (Subgroup.centralizer ({t} : Set NativeSporadic.M12)) =
      Nat.card (centralizerIn NativeSporadic.M12 r) := by
    rw [card_centralizer_eq_centralizerIn, hvc]
    exact (Nat.card_congr (centralizerInConjEquiv NativeSporadic.M12 hc r).toEquiv).symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Or.inl (hcard.trans card_centralizerIn_m12Rep1)
  · right
    refine ⟨hcard.trans card_centralizerIn_m12Rep2, ?_, ?_⟩
    · have h1 := fixedCount_conj elemGz elemRep2
      rw [← elemZ_eq_conj, fixedCount_elemZ] at h1
      rw [ht', fixedCount_conj]
      exact h1.symm
    · obtain ⟨g, hg, hg4⟩ := exists_order_four_centralizerIn_m12Rep2
      obtain ⟨hgM, hgc⟩ := mem_centralizerIn.1 hg
      have hg'M : c * g * c⁻¹ ∈ NativeSporadic.M12 :=
        NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem hc hgM) (NativeSporadic.M12.inv_mem hc)
      refine ⟨⟨c * g * c⁻¹, hg'M⟩, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        change c * g * c⁻¹ * (t : Equiv.Perm (Fin 12)) = (t : Equiv.Perm (Fin 12)) * (c * g * c⁻¹)
        rw [hvc]
        calc c * g * c⁻¹ * (c * m12Rep2 * c⁻¹) = c * (g * m12Rep2) * c⁻¹ := by group
          _ = c * (m12Rep2 * g) * c⁻¹ := by rw [hgc]
          _ = c * m12Rep2 * c⁻¹ * (c * g * c⁻¹) := by group
      · rw [Subgroup.orderOf_mk]
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective g
        rw [← hg4]
        exact this

theorem autModel_conj_blockGroup {c r : Equiv.Perm (Fin 24)}
    (hc : c ∈ autModel) (hr : r ∈ blockGroup) : c * r * c⁻¹ ∈ blockGroup := by
  rcases hc with hD | hσ
  · exact blockGroup.mul_mem (blockGroup.mul_mem hD hr) (blockGroup.inv_mem hD)
  · have h1 : c = m12Sigma * (m12Sigma * c) := by
      rw [← mul_assoc, sigma_mul_self, one_mul]
    set d := m12Sigma * c with hd
    have hcd : c * r * c⁻¹ = m12Sigma * (d * r * d⁻¹) * m12Sigma := by
      rw [h1]
      simp only [mul_inv_rev, sigma_inv, hd, mul_assoc]
    rw [hcd]
    exact sigma_conj_mem (blockGroup.mul_mem (blockGroup.mul_mem hσ hr) (blockGroup.inv_mem hσ))

theorem m12_outer_involution
    (α : MulAut NativeSporadic.M12) (h2 : α * α = 1) (hout : α ∉ inner NativeSporadic.M12) :
    ∃ γ : MulAut NativeSporadic.M12, α = γ * beta * γ⁻¹ := by
  obtain ⟨δ, rfl⟩ := autModelEquiv.surjective α
  have hδδ : δ * δ = 1 := autModelEquiv.injective (by rw [map_mul, h2, map_one])
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    exact hout ⟨1, by rw [map_one, map_one]⟩
  have hδ2 : orderOf (δ : Equiv.Perm (Fin 24)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hδδ) hδ1
  obtain ⟨r, hr, c, hc, hδc⟩ := autModel_involution_cover δ.2 hδ2
  have hzm : blockHom (permZ, permZ) ∈ blockGroup := by
    have := (m12EquivD elemZ).2
    rwa [m12EquivD_elemZ] at this
  have hA1 : m12A1 ∈ blockGroup := m12_gens_memD _ (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have hδ' : δ = ⟨c, hc⟩ * ⟨r, by
      rcases hr with rfl | rfl | rfl
      · exact blockGroup_le_autModel hA1
      · exact blockGroup_le_autModel hzm
      · exact sigma_mem_autModel⟩ * (⟨c, hc⟩ : autModel)⁻¹ :=
    Subtype.ext hδc
  rcases hr with rfl | rfl | rfl
  · exfalso
    have hD : (δ : Equiv.Perm (Fin 24)) ∈ blockGroup := by
      rw [hδc]
      exact autModel_conj_blockGroup hc hA1
    obtain ⟨g, hg⟩ := mem_blockGroup_iff_iota.1 hD
    exact hout ⟨g, by rw [← hg, autModelEquiv_iota]⟩
  · exfalso
    have hD : (δ : Equiv.Perm (Fin 24)) ∈ blockGroup := by
      rw [hδc]
      exact autModel_conj_blockGroup hc hzm
    obtain ⟨g, hg⟩ := mem_blockGroup_iff_iota.1 hD
    exact hout ⟨g, by rw [← hg, autModelEquiv_iota]⟩
  · refine ⟨autModelEquiv ⟨c, hc⟩, ?_⟩
    have : δ = ⟨c, hc⟩ * sigmaModel * (⟨c, hc⟩ : autModel)⁻¹ := hδ'
    rw [this, map_mul, map_mul, map_inv, beta]

end CFSG.GH74.Generic.S45.LAlt
