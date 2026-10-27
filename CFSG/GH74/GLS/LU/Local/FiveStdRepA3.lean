module

public import CFSG.GH74.GLS.LU.Local.FiveStdRepA2

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five.FiveStdRep

namespace FiveStdSetting

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

theorem rep_A (hb : baseCheck = true) {tE uE : E} (hp : pairCond tE uE = true)
    (hr : checkRep tE uE = true) :
    IsPGroup 2 ↥(centralizer ((UU st.z (st.ι uE) : Subgroup G) : Set G)) ∧
    Nat.card ↥(centralizer ((UU st.z (st.ι uE) : Subgroup G) : Set G)) = 64 ∧
    (∃ H' : Subgroup G, IsTorus st.z (st.ι uE) st.K₁ st.K₂ H') ∧
    (∀ A B : Subgroup G, IsTorus st.z (st.ι uE) st.K₁ st.K₂ A → IsTorus st.z (st.ι uE) st.K₁ st.K₂ B →
      A = B) ∧
    (∀ H' : Subgroup G, IsTorus st.z (st.ι uE) st.K₁ st.K₂ H' → st.z ∈ H' ∧ st.ι uE ∈ H' ∧
      (∀ p ∈ centralizer ((UU st.z (st.ι uE) : Subgroup G) : Set G), cjL p H' = H') ∧
      (∀ p ∈ centralizer ((UU st.z (st.ι uE) : Subgroup G) : Set G), p * p ∈ H')) ∧
    (∃ w' ∈ st.K₁, w' * w' = st.z ∧ w' * st.ι uE * w'⁻¹ = st.ι uE * st.z) ∧
    (∃ p : G, p * st.z = st.z * p ∧ p * st.ι uE = st.ι uE * p ∧ p * st.ι tE * p⁻¹ = st.z * st.ι tE) := by
  have hz := validE_zE hb
  obtain ⟨ht, hu⟩ := pairCond_valid hb hp
  obtain ⟨-, hK1, -⟩ := baseCheck_spec hb
  obtain ⟨a, b, hab, hP, -, -⟩ := checkRep_spec hr
  obtain ⟨hlen, htp, hzH, huH, hnorm, hsq, hw, hconj⟩ := checkP_spec hP
  obtain ⟨haP, hbP, -⟩ := mem_tpOf_iff.1 hab
  have hva : validE a = true := V_PlOf uE a haP
  have hvb : validE b = true := V_PlOf uE b hbP
  have hVH : V (ppE a b 4 4) := st.model.V_ppE hva hvb 4 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 6) ((card_P st hb hu).trans (hlen.trans (by norm_num)))
  · exact (card_P st hb hu).trans hlen
  · exact (isTorus_of_mem_tpOf st hb hu hab).imp fun H h => h.1
  · intro A B hA hB
    exact SetLike.coe_injective
      ((torus_set_eq st hb hu hab hP hA).trans (torus_set_eq st hb hu hab hP hB).symm)
  · intro H' hH'
    have hS := torus_set_eq st hb hu hab hP hH'
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : st.z ∈ S st.ι (ppE a b 4 4) := (st.model.inL_iff hVH hz).1 hzH
      rw [← hS] at this
      exact this
    · have : st.ι uE ∈ S st.ι (ppE a b 4 4) := (st.model.inL_iff hVH hu).1 huH
      rw [← hS] at this
      exact this
    · intro p hpP
      have hp' : p ∈ S st.ι (PlOf uE) := by rw [← P_eq st hz hu]; exact hpP
      obtain ⟨pE, hpE, rfl⟩ := mem_S.1 hp'
      have hvp : validE pE = true := V_PlOf uE pE hpE
      have hN := (st.model.normG_iff hvp (V_cons hva (V_cons hvb V_nil)) hVH).1 (hnorm pE hpE)
      have h1 : st.ι pE * st.ι a * (st.ι pE)⁻¹ ∈ H' := by
        have := hN a (by simp)
        rw [← hS] at this
        exact this
      have h2 : st.ι pE * st.ι b * (st.ι pE)⁻¹ ∈ H' := by
        have := hN b (by simp)
        rw [← hS] at this
        exact this
      apply repCj_eq_of_le
      intro x hx
      have hx' : x ∈ S st.ι (ppE a b 4 4) := by rw [← hS]; exact hx
      rw [st.model.S_ppE hva hvb] at hx'
      obtain ⟨i, -, j, -, rfl⟩ := hx'
      have : st.ι pE * (st.ι a ^ i * st.ι b ^ j) * (st.ι pE)⁻¹ =
          (st.ι pE * st.ι a * (st.ι pE)⁻¹) ^ i * (st.ι pE * st.ι b * (st.ι pE)⁻¹) ^ j := by
        rw [conj_pow, conj_pow]
        group
      rw [this]
      exact H'.mul_mem (H'.pow_mem h1 i) (H'.pow_mem h2 j)
    · intro p hpP
      have hp' : p ∈ S st.ι (PlOf uE) := by rw [← P_eq st hz hu]; exact hpP
      obtain ⟨pE, hpE, rfl⟩ := mem_S.1 hp'
      have hvp : validE pE = true := V_PlOf uE pE hpE
      have := (st.model.inL_iff hVH (st.model.valid_mul pE pE hvp hvp)).1 (hsq pE hpE)
      rw [st.model.map_mul pE pE hvp hvp, ← hS] at this
      exact this
  · obtain ⟨w, hwK, hw1, hw2⟩ := hw
    have hvw : validE w = true := hK1 w hwK
    refine ⟨st.ι w, ?_, ?_, ?_⟩
    · rw [← SetLike.mem_coe, st.hK₁]
      exact mem_S.2 ⟨w, hwK, rfl⟩
    · rw [← st.model.map_mul w w hvw hvw, hw1]
    · have := st.model.map_conjE hvw hu
      rw [hw2, st.model.map_mul uE zE hu hz] at this
      exact this.symm
  · obtain ⟨p, hpP, hpc⟩ := hconj
    obtain ⟨hvp, h1, h2⟩ := (mem_PlOf_iff st hz hu).1 hpP
    refine ⟨st.ι p, h1, h2, ?_⟩
    have := st.model.map_conjE hvp ht
    rw [hpc, st.model.map_mul zE tE hz ht] at this
    exact this.symm

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five
