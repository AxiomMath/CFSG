module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoE4A
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem E4.aut_inner_of_lieModel_PSp {M : Type} [Group M] [Finite M]
    (h : CFSG.Blueprint.LieModel M .PSp 3 2 1) : ∀ α : MulAut M, α ∈ Q3NM.innSubgroup M := by
  rcases h with ⟨-, hcl⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl hK
    have : NeZero (3 : ℕ) := ⟨by norm_num⟩
    have hFin := Finite.of_equiv M e.toEquiv
    intro α
    set α' := (e.symm.trans α).trans e with hα'
    have hαI : α' ∈ ComponentClassification.OuterAutomorphisms.inner _ := by
      have hE := (automorphism_generation (K := K) (r := 3) le_rfl).1
      obtain ⟨g, φ, hgφ⟩ := SpChain.exists_eq_spInner_mul_fieldAut
        (show α' ∈ spSemilinearAutGroup 3 K by rw [hE]; exact Subgroup.mem_top α')
      by_contra hn
      exact ((SpChain.spInner_mul_fieldAut_not_mem_inner_iff g φ).1 (hgφ ▸ hn))
        (Vtx.ringEquiv_eq_one_of_card_two hK2 φ)
    obtain ⟨y, hy⟩ := hαI
    refine ⟨e.symm y, MulEquiv.ext fun x => e.injective ?_⟩
    have h1 := DFunLike.congr_fun hy (e x)
    rw [hα'] at h1
    simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1
  all_goals exact absurd h0 (by norm_num)

theorem socleTransitive_sp62 :
    SocleTransitive IsSp62 := by
  intro G _ _ N _ _ _ hC hP Δ h _
  have hNtop : N = ⊤ := E4.eq_top_of_aut_inner (E4.aut_inner_of_lieModel_PSp hP) hC
  have hθ : ∀ z : G, orderOf z = 2 → oddCoreImg (Subgroup.centralizer ({z} : Set G)) = ⊥ :=
    fun z hz => E4.oddCoreImg_centralizer_eq_bot (Vtx.autOddFree_of_lieModel_PSp hP) hC hz
  obtain ⟨e⟩ := EvenSmallLie.Sp6.nonempty_mulEquiv_co3X36 hP
  let e₁ : G ≃* ↥Sporadic.Schreier.Co3.co3X36 :=
    ((MulEquiv.subgroupCongr hNtop).trans Subgroup.topEquiv).symm.trans e
  refine E4.conj_of_ident (E4Sp6.emb e₁) (E4Sp6.emb_injective e₁) (Kc := E4Sp6.K0)
    fun K hK => ?_
  obtain ⟨⟨z, hz⟩, -⟩ := h.hyp.omega1 K hK
  have had := E4.ambientQuatDatum_map (E4Sp6.emb e₁) (E4Sp6.emb_injective e₁)
    (E4.ambientQuatDatum_of_mem h hθ hK hz)
  rw [E4Sp6.range_emb] at had
  obtain ⟨g, hg, hgK⟩ := E4Sp6.ident_ambient had
  rw [← E4Sp6.range_emb e₁] at hg
  obtain ⟨m, rfl⟩ := hg
  exact ⟨m, hgK⟩

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
