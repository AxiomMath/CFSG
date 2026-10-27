module

public import CFSG.GH74.GLS.Bg.Pu5.L296M
public import CFSG.GH74.GLS.Bg.Pu5.L294

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK.Lifted
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem l296_of (h295 : L295) (hL294b : L294b) (h293 : L293) (hrec : Bg.B_reciprocity)
    (h2A7 : II4_2A7) (h44 : II4_44) (hquat : II4_4_quat) : L296 := by
  intro G _ _ z t S hC
  have hG : IsKProperSimple G := hC.simple
  have hgen := hC.gen4
  have hz2 : orderOf z = 2 := hC.hz
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzS : z ∈ S := hC.z_mem_S
  have hzZ : z ∈ zStar (rigidProduct z) := hC.z_mem_zStar
  have hM : ∀ K U : Subgroup G, IsRigidRankOneComp z K → IsFour U →
      U ≤ centralizer ({z, t} : Set G) ⊓ cSec K → z ∈ U →
      (∀ y ∈ S ⊓ K, orderOf y = 2 → y ∈ U) → False :=
    fun K U hK hU hUle hzU hzi =>
      claimM h295 h293 hrec h2A7 h44 hquat ⟨hC, hK, hU, hUle, hzU, hzi⟩
  have hZ : S ⊓ zStar (rigidProduct z) = zpowers z := by
    apply le_antisymm
    · intro c hc
      by_contra hcz
      have htN : ∀ K, IsRigidRankOneComp z K → t ∈ normalizer (K : Set G) := by
        intro K hK
        by_contra htK
        exact hcz ((hL294b G z t S hC ⟨K, hK, htK⟩).2 ▸ hc)
      obtain ⟨K₀, hK₀⟩ := rigid_nonempty hz2 hC.hzK
      by_cases hsingle : ∀ K', IsRigidRankOneComp z K' → K' = K₀
      · obtain ⟨z₀, -, hZ'⟩ := zStar_single hquat hG hK₀ hC.sylow hsingle
        have hzc : z = 1 ∨ z = z₀ := hZ' z ⟨hzS, hzZ⟩
        have hzz₀ : z = z₀ := hzc.resolve_left hz1
        rcases hZ' c hc with h1 | h1
        · exact hcz (by rw [h1]; exact one_mem _)
        · exact hcz (by rw [h1, ← hzz₀]; exact mem_zpowers z)
      · push Not at hsingle
        obtain ⟨K₂, hK₂, hne⟩ := hsingle
        obtain ⟨z₁, z₂, q₁, q₂, hZ'⟩ := zStar_two hquat hG hgen hK₀ hK₂ hne.symm hC.sylow
        by_cases h12 : z₁ = z₂
        · have hz₁₁ : z₁ * z₁ = 1 := q₁.sq
          have hzc := hZ' z ⟨hzS, hzZ⟩
          have hzz₁ : z = z₁ := by
            rcases hzc with h1 | h1 | h1 | h1
            · exact absurd h1 hz1
            · exact h1
            · rw [h1, h12]
            · exfalso
              apply hz1
              rw [h1, ← h12]
              exact hz₁₁
          rcases hZ' c hc with h1 | h1 | h1 | h1
          · exact hcz (by rw [h1]; exact one_mem _)
          · exact hcz (by rw [h1, ← hzz₁]; exact mem_zpowers z)
          · exact hcz (by rw [h1, ← h12, ← hzz₁]; exact mem_zpowers z)
          · exact hcz (by rw [h1, ← h12, hz₁₁]; exact one_mem _)
        ·
          have hz₁₁ : z₁ * z₁ = 1 := q₁.sq
          have hz₂₂ : z₂ * z₂ = 1 := q₂.sq
          have hcomm₁₂ : z₁ * z₂ = z₂ * z₁ :=
            rr_sylow_comm hK₀ hK₂ hne.symm hC.sylow z₁ q₁.mem z₂ q₂.mem
          have hU := isFour_closure_pair hz₁₁ hz₂₂ hcomm₁₂ q₁.ne q₂.ne h12
          have hz₁2 : orderOf z₁ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz₁₁) q₁.ne
          have hz₂2 : orderOf z₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz₂₂) q₂.ne
          have hz₁Z : z₁ ∈ zStar (rigidProduct z) :=
            mem_zStar_rigidProduct_of_involution h44 hG hK₀ q₁.mem.2 hz₁2
          have hz₂Z : z₂ ∈ zStar (rigidProduct z) :=
            mem_zStar_rigidProduct_of_involution h44 hG hK₂ q₂.mem.2 hz₂2
          have hfix : ∀ (K : Subgroup G) (z' : G), IsRigidRankOneComp z K → QData S K z' →
              t * z' = z' * t := by
            intro K z' hK q
            have hmem : t * z' * t⁻¹ ∈ S ⊓ K :=
              ⟨S.mul_mem (S.mul_mem hC.tS q.mem.1) (S.inv_mem hC.tS),
                (mem_normalizer_iff.mp (htN K hK) z').mp q.mem.2⟩
            have hsq : t * z' * t⁻¹ * (t * z' * t⁻¹) = 1 := by
              calc t * z' * t⁻¹ * (t * z' * t⁻¹) = t * (z' * z') * t⁻¹ := by group
                _ = 1 := by rw [q.sq]; group
            rcases q.unique _ hmem hsq with h1 | h1
            · exfalso
              apply q.ne
              have : t * z' * t⁻¹ = 1 := h1
              simpa using this
            · calc t * z' = t * z' * t⁻¹ * t := by group
                _ = z' * t := by rw [h1]
          have hzC : ∀ x ∈ zStar (rigidProduct z), x ∈ centralizer ({z} : Set G) := fun x hx =>
            rigidProduct_le_cent z (Subgroup.mem_inf.1 hx).1
          have hX : ∀ z' : G, z' ∈ zStar (rigidProduct z) → orderOf z' = 2 → t * z' = z' * t →
              z' ∈ centralizer ({z, t} : Set G) ⊓ cSec K₀ := by
            intro z' hz' hz'2 htz'
            refine ⟨?_, mem_cSec_of_mem_zStar h44 hquat hG hgen hz'
              (exists_two_pow_eq_one_of_orderOf hz'2) hK₀⟩
            refine Subgroup.mem_centralizer_iff.2 ?_
            intro g hg
            rcases hg with rfl | hg
            · exact (Subgroup.mem_centralizer_singleton_iff.1 (hzC z' hz')).symm
            · rw [Set.mem_singleton_iff.mp hg]
              exact htz'
          have hz₁X := hX z₁ hz₁Z hz₁2 (hfix K₀ z₁ hK₀ q₁)
          have hz₂X := hX z₂ hz₂Z hz₂2 (hfix K₂ z₂ hK₂ q₂)
          have hUle : Subgroup.closure ({z₁, z₂} : Set G) ≤ centralizer ({z, t} : Set G) ⊓ cSec K₀ := by
            rw [Subgroup.closure_le]
            intro x hx
            rcases hx with rfl | hx
            · exact hz₁X
            · rw [Set.mem_singleton_iff.mp hx]
              exact hz₂X
          have hzU : z ∈ Subgroup.closure ({z₁, z₂} : Set G) := by
            rcases hZ' z ⟨hzS, hzZ⟩ with h1 | h1 | h1 | h1
            · exact absurd h1 hz1
            · rw [h1]; exact Subgroup.subset_closure (by simp)
            · rw [h1]; exact Subgroup.subset_closure (by simp)
            · rw [h1]
              exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
          have hzi : ∀ y ∈ S ⊓ K₀, orderOf y = 2 → y ∈ Subgroup.closure ({z₁, z₂} : Set G) := by
            intro y hy hy2
            have hyy : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hy2
            rcases q₁.unique y hy hyy with h1 | h1
            · exfalso
              rw [h1, orderOf_one] at hy2
              exact absurd hy2 (by norm_num)
            · rw [h1]
              exact Subgroup.subset_closure (by simp)
          exact hM K₀ _ hK₀ hU hUle hzU hzi
    · exact (Subgroup.zpowers_le).2 ⟨hzS, hzZ⟩
  refine ⟨hZ, fun K hK => ?_⟩
  have hzcS : z ∈ cSec K := mem_cSec_of_mem_zStar h44 hquat hG hgen hzZ
    (exists_two_pow_eq_one_of_orderOf hz2) hK
  have hzX : z ∈ centralizer ({z, t} : Set G) ⊓ cSec K := by
    refine ⟨?_, hzcS⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    intro g hg
    rcases hg with rfl | hg
    · rfl
    · rw [Set.mem_singleton_iff.mp hg]
      exact Subgroup.mem_centralizer_singleton_iff.1 hC.tC
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    obtain ⟨i, hiX, hi2, hiz⟩ := exists_involution_not_mem_zpowers (H := centralizer ({z, t} : Set G) ⊓ cSec K) hz2
      (by omega)
    have hi1 : i ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hi2
      exact absurd hi2 (by norm_num)
    have hii : i * i = 1 := mul_self_eq_one_of_orderOf_eq_two hi2
    have hzi : z * i = i * z := Subgroup.mem_centralizer_iff.1 hiX.1 z (Set.mem_insert z {t})
    have hne : z ≠ i := fun h1 => hiz (by rw [← h1]; exact mem_zpowers z)
    have hU := isFour_closure_pair hzz hii hzi hz1 hi1 hne
    have hUle : Subgroup.closure ({z, i} : Set G) ≤ centralizer ({z, t} : Set G) ⊓ cSec K := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hzX
      · rw [Set.mem_singleton_iff.mp hx]
        exact hiX
    have hzU : z ∈ Subgroup.closure ({z, i} : Set G) := Subgroup.subset_closure (by simp)
    have hzp : zpowers z ≤ Subgroup.closure ({z, i} : Set G) := (Subgroup.zpowers_le).2 hzU
    refine hM K _ hK hU hUle hzU ?_
    intro y hy hy2
    have hyZ : y ∈ zStar (rigidProduct z) :=
      mem_zStar_rigidProduct_of_involution h44 hG hK hy.2 hy2
    have hySZ : y ∈ S ⊓ zStar (rigidProduct z) := ⟨hy.1, hyZ⟩
    rw [hZ] at hySZ
    exact hzp hySZ
  · exact one_le_pRank_of_involution' hzX hz2

end CFSG.GH74.GLS.Bg.Pu5
