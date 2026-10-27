module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4Block
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Walter.Cited.PSL2Small

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.GorensteinWalter Subgroup
open scoped MatrixGroups

theorem psl27_aut_conj_of_fixes_kleinFour
    (V : Subgroup PSL(2, ZMod 7)) (hV : IsKleinFour V)
    (β : MulAut PSL(2, ZMod 7)) (hβ : ∀ v ∈ V, β v = v) :
    ∃ g ∈ V, β = MulAut.conj g := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hK : Nat.card (ZMod 7) = 7 := by simp
  have hK' := Unc25K1.isOddPrimePower_of_card_prime (K := ZMod 7) (p := 7) le_rfl hK
  have hKpow : Nat.card (ZMod 7) = 7 ^ 1 := by rw [hK, pow_one]
  have hcard : 3 < Nat.card (ZMod 7) := by omega
  have hex : ∃ (g : PGL2 (ZMod 7)) (σ : ZMod 7 ≃+* ZMod 7),
      β = pgl2InnerAutPSL2 (ZMod 7) hK' hcard g * psl2FieldAut (ZMod 7) σ := by
    obtain ⟨xx, hxx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod 7) hKpow hK' hcard β
    have h := congrArg (pGammaL2ToMulAutPSL2 (ZMod 7) hK' hcard)
      (SemidirectProduct.inl_left_mul_inr_right xx)
    rw [map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr, hxx] at h
    exact ⟨xx.left, xx.right, h.symm⟩
  obtain ⟨g, σ, hβgσ⟩ := hex
  have hσ : σ = 1 :=
    (CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime (ZMod 7) hK).elim _ _
  rw [hσ, map_one, mul_one] at hβgσ
  let toPGL : PSL(2, ZMod 7) →* PGL2 (ZMod 7) := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have htoPGL : Function.Injective toPGL := fun _ _ h =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective h
  have hVP : IsKleinFour (V.map toPGL) := isKleinFour_map_of_injective V hV toPGL htoPGL
  have hgC : g ∈ Subgroup.centralizer ((V.map toPGL : Subgroup (PGL2 (ZMod 7))) :
      Set (PGL2 (ZMod 7))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 : pgl2InnerAutPSL2 (ZMod 7) hK' hcard g v = v := by
      rw [← hβgσ]
      exact hβ v hv
    have h2 := toPGL_pgl2InnerAutPSL2_apply (ZMod 7) hK' hcard g v
    rw [h1] at h2
    calc toPGL v * g = (g * toPGL v * g⁻¹) * g := by rw [← h2]
      _ = g * toPGL v := by group
  rw [pgl2_kleinFour_centralizer_eq_self (ZMod 7) hK' _ hVP] at hgC
  obtain ⟨g0, hg0V, hg0⟩ := hgC
  refine ⟨g0, hg0V, ?_⟩
  rw [hβgσ, ← hg0]
  exact pgl2InnerAutPSL2_toPGL (ZMod 7) hK' hcard g0

theorem IsA4Block.isKleinFour_subgroupOf {G : Type} [Group G] [Finite G] {L U K : Subgroup G}
    (h : IsA4Block L U) (hUK : U ≤ K) : IsKleinFour ↥(U.subgroupOf K) := by
  have hcard : Nat.card ↥(U.subgroupOf K) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv]
    exact h.card_U
  have hnt : Nontrivial ↥(U.subgroupOf K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  refine ⟨hcard, ?_⟩
  · rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    apply Subtype.ext
    apply Subtype.ext
    simpa using h.sq_U (((g : ↥K)) : G) g.2

theorem psl27_aut_eq_one
    {G : Type} [Group G] [Finite G] {K L U : Subgroup G}
    (e₁ : ↥K ≃* PSL(2, ZMod 7)) (hL : IsA4Block L U) (hLK : L ≤ K) (α : MulAut ↥K)
    (hα : ∀ (l : G) (hl : l ∈ L), α ⟨l, hLK hl⟩ = ⟨l, hLK hl⟩) : ∀ k : ↥K, α k = k := by
  have hUK : U ≤ K := hL.le.trans hLK
  obtain ⟨c, hcL, hc3, hcN, hcfp, hLc⟩ := hL.exists_c
  let V₀ : Subgroup ↥K := U.subgroupOf K
  let V : Subgroup PSL(2, ZMod 7) := V₀.map e₁.toMonoidHom
  have hV : IsKleinFour V := isKleinFour_map_of_injective V₀ (hL.isKleinFour_subgroupOf hUK)
    e₁.toMonoidHom e₁.injective
  let β : MulAut PSL(2, ZMod 7) := (e₁.symm.trans α).trans e₁
  have hβapp : ∀ k : ↥K, β (e₁ k) = e₁ (α k) := by
    intro k
    show e₁ (α (e₁.symm (e₁ k))) = e₁ (α k)
    rw [MulEquiv.symm_apply_apply]
  have hβV : ∀ v ∈ V, β v = v := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ U := hu
    have hαu : α u = u := hα (u : G) (hL.le hu')
    show β (e₁ u) = e₁ u
    rw [hβapp, hαu]
  obtain ⟨g, hgV, hg⟩ := psl27_aut_conj_of_fixes_kleinFour V hV β hβV
  obtain ⟨g₀, hg₀, rfl⟩ := hgV
  have hg₀U : (g₀ : G) ∈ U := Subgroup.mem_subgroupOf.mp hg₀
  have hcK : c ∈ K := hLK hcL
  have hfix : β (e₁ ⟨c, hcK⟩) = e₁ ⟨c, hcK⟩ := by
    rw [hβapp, show α ⟨c, hcK⟩ = ⟨c, hcK⟩ from hα c hcL]
  have hcomm : g₀ * ⟨c, hcK⟩ * g₀⁻¹ = ⟨c, hcK⟩ := by
    have h2 := hfix
    rw [hg] at h2
    simp only [MulAut.conj_apply] at h2
    apply e₁.injective
    simpa using h2
  have hcomm' : c * (g₀ : G) * c⁻¹ = (g₀ : G) := by
    have h3 : (g₀ : G) * c = c * (g₀ : G) := by
      have h4 := congrArg Subtype.val hcomm
      have h5 : (g₀ : G) * c * (g₀ : G)⁻¹ = c := h4
      calc (g₀ : G) * c = ((g₀ : G) * c * (g₀ : G)⁻¹) * (g₀ : G) := by group
        _ = c * (g₀ : G) := by rw [h5]
    calc c * (g₀ : G) * c⁻¹ = (g₀ : G) * c * c⁻¹ := by rw [h3]
      _ = (g₀ : G) := by group
  have hg₀1 : (g₀ : G) = 1 := by
    by_contra hne
    exact hcfp _ hg₀U hne hcomm'
  have hg1 : g₀ = 1 := Subtype.ext hg₀1
  intro k
  have hβ1 : β (e₁ k) = e₁ k := by
    rw [hg, hg1]
    simp
  rw [hβapp] at hβ1
  exact e₁.injective hβ1

end CFSG.QuasithinUnique.DoubleA3
