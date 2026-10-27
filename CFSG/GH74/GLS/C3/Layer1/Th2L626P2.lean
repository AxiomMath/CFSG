module

public import CFSG.GH74.GLS.C3.Layer1.St1P41L42

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpL42

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm3.Sec4

variable {G : Type} [Group G] [Finite G]

theorem lemma42T
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x : G} {K Q V : Subgroup G} (hP : IsILo 2 x K)
    (hQ : IsSylowOf 2 Q (CxK x K)) (hV : IsPGroup 2 ↥V) (hVN : V ≤ NxK x K)
    (hVQ : V ≤ normalizer (Q : Set G))
    (hsyl : ∀ z ∈ Q, orderOf z = 2 → (∀ q ∈ Q, z * q = q * z) → (∀ v ∈ V, z * v = v * z) →
      ∀ K' : Subgroup G, PumpUpLT 2 x K z K' → IsSylowOf 2 Q (CxK z K'))
    (hnt : ¬ IsTwoTerminal x K) :
    ∃ u ∈ Q, orderOf u = 2 ∧ ∃ K' : Subgroup G, PumpUpLT 2 x K u K' ∧
      ¬ (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have htr : ∀ u ∈ Q, orderOf u = 2 → ∀ K' : Subgroup G, PumpUpLT 2 x K u K' →
      x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K) := by
    intro u hu hu2 K' hlt
    by_contra hnt'
    exact hne ⟨u, hu, hu2, K', hlt, hnt'⟩
  refine hnt ⟨hP, ?_, ?_⟩
  ·
    intro x' K' hlt
    by_contra hnt'
    obtain ⟨u, hu, hu2, K'', hlt'', hnt''⟩ := exists_nontrivial_in_sylow hQ hlt hnt'
    exact hnt'' (htr u hu hu2 K'' hlt'')
  ·
    intro Q' hQ' x' K' hlt hx'Q' hx'c
    obtain ⟨d, hdD, hdQ⟩ := exists_conj_sylow hQ hQ'
    have hdx_c : d * x * d⁻¹ = x := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hdD.1
      calc d * x * d⁻¹ = x * d * d⁻¹ := by rw [this]
        _ = x := by group
    have hdK : cmap d K = K := cmap_eq_of_mem_normalizer hdD.2.1
    have hlt' : PumpUpLT 2 x K (d * x' * d⁻¹) (cmap d K') := by
      have := pumpUpLT_cmap hlt d
      rwa [hdx_c, hdK] at this
    have hx'2 : orderOf x' = 2 := hlt.2.1.1
    have hx''o : orderOf (d * x' * d⁻¹) = 2 := by rw [orderOf_conj']; exact hx'2
    have hx''Q : d * x' * d⁻¹ ∈ Q := by
      rw [← hdQ]; exact ⟨x', hx'Q', by simp [MulAut.conj_apply]⟩
    have hx''c : ∀ q ∈ Q, (d * x' * d⁻¹) * q = q * (d * x' * d⁻¹) := by
      intro q hq
      rw [← hdQ] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      have := hx'c q' hq'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc d * x' * d⁻¹ * (d * q' * d⁻¹) = d * (x' * q') * d⁻¹ := by group
        _ = d * (q' * x') * d⁻¹ := by rw [this]
        _ = d * q' * d⁻¹ * (d * x' * d⁻¹) := by group
    have h5 := Iv251.iv2_5_1 hP hQ hV hVN hVQ
      (fun z _ hz2 _ _ => hR z hz2)
      (fun z hz hz2 hzc hzV K'' hlt'' =>
        ⟨htr z hz hz2 K'' hlt'', hsyl z hz hz2 hzc hzV K'' hlt''⟩)
      (d * x' * d⁻¹) hx''Q hx''o hx''c (cmap d K') hlt' (htr _ hx''Q hx''o _ hlt')
    rw [← cmap_CxK d] at h5
    have h6 := isSylowOf_cmap h5 d⁻¹
    rwa [cmap_inv_cancel, ← hdQ, cmap_inv_cancel] at h6

end CFSG.GH74.GLS.C3.Layer1.PumpL42
