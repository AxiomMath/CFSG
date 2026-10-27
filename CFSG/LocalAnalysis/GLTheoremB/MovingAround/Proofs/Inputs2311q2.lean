module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311q
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Glue
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Shintani
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.ThreeD4
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.G2Class
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311q

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c
  CFSG.RankThree.PartOne.CTP

section Cat

set_option linter.unusedSectionVars false

theorem mulAut_congr_self_inputs2311q {G : Type*} [Group G] (ψ β : MulAut G) :
    (MulAut.congr ψ).toMonoidHom β = ψ * β * ψ⁻¹ :=
  MulEquiv.ext fun _ => rfl

theorem uniSeitzPlanes_dFour_graphSplit :
    UniSeitzPlanes fun d p E => p = 3 ∧ d.1.characteristic ≠ 2 ∧ ¬ InnerPlane d p E ∧
      ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧ q.card % 3 = 1 ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
          ∃ e : Cat d ≃* ↥(adjointGroup Tag.D4 K),
            ∀ α ∈ E.map (MulAut.congr e).toMonoidHom, α ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) →
              D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨rfl, hchar2, hin, q, hq, hq1, K, hF, hfin, hK, e, hG⟩
  obtain rfl : d = .D 4 q := hq
  have hchar : (TauCeti.LieTypeIndex.D 4 q).characteristic = q.p := by
    simp [TauCeti.LieTypeIndex.characteristic_D]
  have hK' : Nat.card K = q.p ^ q.exponent := by rw [hK, TauCeti.PrimePower.card_def]
  haveI : CharP K q.p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic q.prime_p
      q.exponent_pos hK'
  have hring : ringChar K = q.p := ringChar.eq K q.p
  have hq2 : q.p ≠ 2 := fun h => hchar2 (by rw [hchar, h])
  have hq3 : q.p ≠ 3 := fun h => hpd (by rw [hchar, h])
  have hK2 : ringChar K ≠ 2 := by rw [hring]; exact hq2
  have hK3 : ringChar K ≠ 3 := by rw [hring]; exact hq3
  obtain ⟨-, -, hK5⟩ := ringChar_facts_inputs2311q hK2 hK3
  have h5 : 5 ≤ ringChar K := by
    have h2 := q.prime_p.two_le
    have h4 : q.p ≠ 4 := fun h => by have := q.prime_p; rw [h] at this; norm_num at this
    rw [hring]
    omega
  have hqK : Nat.card K % 3 = 1 := by rw [hK]; exact hq1
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  haveI hE'ea : CFSG.IsElementaryAbelian 3 ↥E' :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card E' = 3 ^ 2 := by rw [hE', card_map_congr, hc]
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E', β ∉ CFSG.Fischer.innerAut ↥(adjointGroup Tag.D4 K) := by
    by_contra hcon
    push Not at hcon
    apply hin
    intro φ hφ
    obtain ⟨g, hg⟩ := hcon _ (Subgroup.mem_map_of_mem _ hφ)
    refine ⟨e.symm g, ?_⟩
    have h1 : (MulAut.congr e).toMonoidHom (MulAut.conj (e.symm g)) = (MulAut.congr e).toMonoidHom φ := by
      rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hg]
    exact (MulAut.congr e).injective h1
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  obtain ⟨g, a, σ, ε, hε, hσ3, ⟨hε0, hσ1⟩, hβeq⟩ := hG β hβE hβout
  subst hσ1
  have hβNF : HasNF β ε 1 := ⟨g, a, hβeq⟩
  obtain ⟨ι, hιE, hι1, ⟨x, rfl⟩⟩ := exists_inner_ne_one_of_graph hc' hG hβE (by omega) hβNF
  have hx1 : x ≠ 1 := fun h => hι1 (by rw [h, map_one])
  rcases ClassOdd.d4GraphClassOdd_of (ClassOdd.graphShintaniNF_of ClassOdd.threeD4FixedNF_holds)
      ClassOdd.g2ThreeClass_holds K h5 β hβ3 (hG β hβE hβout) with ⟨ψ, hψ⟩ | ⟨ψ, B, hB3, hB1, hψ⟩
  ·
    have hmapψ : ∀ φ ∈ E', (MulAut.congr ψ).toMonoidHom φ ∈ E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
      intro φ hφ
      obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
      exact ⟨φ₀, hφ₀, Inputs2311k.mulAut_congr_trans_excD4 e ψ φ₀⟩
    have hγ : d4Graph K 1 ∈ E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
      have hβ' := hmapψ β hβE
      rw [mulAut_congr_self_inputs2311q] at hβ'
      rcases hψ with h | h
      · rwa [h] at hβ'
      · rw [h] at hβ'
        have h4 : d4Graph K 2 * d4Graph K 2 = d4Graph K 1 := by
          rw [← d4Graph_add, show (2 : ℕ) + 2 = 1 + 3 from rfl, d4Graph_add, d4Graph_three, mul_one]
        rw [← h4]
        exact Subgroup.mul_mem _ hβ' hβ'
    have hx' : MulAut.conj (ψ x) ∈ E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
      have := hmapψ _ hιE
      rwa [mulAut_congr_conj] at this
    have hψx1 : ψ x ≠ 1 := fun h => hx1 (ψ.injective (h.trans (map_one ψ).symm))
    exact Inputs2311k.uniSeitzPlanes_dFour_graphG2Type _ 3 hp hp2 hpd hex E hE hc
      ⟨rfl, hchar2, q, rfl, K, hF, hfin, hK, e.trans ψ, hγ, ψ x, hψx1, hx'⟩
  ·
    have h3K : 3 ∣ Nat.card K - 1 := by have := Nat.card_pos (α := K); omega
    obtain ⟨P, t, hPt⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_HSL_of_three h3K B
      ⟨1, by rw [pow_one]; exact hB3⟩
    have ht3 : t ^ 3 = 1 := by
      apply CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective (K := K)
      rw [map_pow, map_one, CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_apply, ← hPt, conj_pow, hB3]
      group
    have ht1 : t ≠ 1 := by
      intro h0
      apply hB1
      have h1 : P * B * P⁻¹ = 1 := by
        rw [hPt, h0]
        exact (CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom K).map_one
      rwa [conj_eq_one_iff] at h1
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have ht : orderOf t = 3 := orderOf_eq_prime ht3 ht1
    set f := (e.trans ψ).trans (MulAut.conj (sl2At K ⟨2, by decide⟩ P)) with hf
    set E'' := E.map (MulAut.congr f).toMonoidHom with hE''
    have hmap : ∀ φ ∈ E', (MulAut.conj (sl2At K ⟨2, by decide⟩ P) * ψ) * φ *
        (MulAut.conj (sl2At K ⟨2, by decide⟩ P) * ψ)⁻¹ ∈ E'' := by
      intro φ hφ
      obtain ⟨φ₀, hφ₀, rfl⟩ := hφ
      refine ⟨φ₀, hφ₀, ?_⟩
      rw [hf, Inputs2311k.mulAut_congr_trans_excD4, Inputs2311k.mulAut_congr_trans_excD4,
        mulAut_congr_self_inputs2311q, mulAut_congr_self_inputs2311q]
      group
    haveI : CFSG.IsElementaryAbelian 3 ↥E'' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr f hE)
    have hc'' : Nat.card E'' = 3 ^ 2 := by rw [hE'', card_map_congr, hc]
    have hgB : gammaP K B ∈ E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
      have hβ' : ψ * β * ψ⁻¹ ∈ E.map (MulAut.congr (e.trans ψ)).toMonoidHom := by
        obtain ⟨φ₀, hφ₀, hβφ⟩ := hβE
        refine ⟨φ₀, hφ₀, ?_⟩
        rw [Inputs2311k.mulAut_congr_trans_excD4, mulAut_congr_self_inputs2311q, hβφ]
      rcases hψ with h | h
      · rwa [h] at hβ'
      · rw [h] at hβ'
        have := Subgroup.inv_mem _ hβ'
        rwa [inv_inv] at this
    have hαE'' : gammaP K (HSL t) ∈ E'' := by
      obtain ⟨φ₀, hφ₀, hφ₀B⟩ := hgB
      refine ⟨φ₀, hφ₀, ?_⟩
      rw [hf, Inputs2311k.mulAut_congr_trans_excD4, hφ₀B, mulAut_congr_self_inputs2311q, conj_gammaP, hPt]
    have hxE'' : MulAut.conj ((sl2At K ⟨2, by decide⟩ P) * ψ x * (sl2At K ⟨2, by decide⟩ P)⁻¹) ∈ E'' := by
      have := hmap _ hιE
      have e1 : (MulAut.conj (sl2At K ⟨2, by decide⟩ P) * ψ) * MulAut.conj x *
          (MulAut.conj (sl2At K ⟨2, by decide⟩ P) * ψ)⁻¹ =
          MulAut.conj ((sl2At K ⟨2, by decide⟩ P) * ψ x * (sl2At K ⟨2, by decide⟩ P)⁻¹) := by
        ext y
        simp [MulAut.mul_apply, MulAut.conj_apply]
      rwa [e1] at this
    have hx''1 : (sl2At K ⟨2, by decide⟩ P) * ψ x * (sl2At K ⟨2, by decide⟩ P)⁻¹ ≠ 1 := by
      intro h
      rw [conj_eq_one_iff] at h
      exact hx1 (ψ.injective (h.trans (map_one ψ).symm))
    have htop := uniPlaneClosure_eq_top_gammaP_HSL hK2 hK3 hqK ht hc'' hαE'' hx''1 hxE''
    rw [hring] at htop
    rw [hchar]
    exact (uniPlaneGen_map_congr f q.p E).1 htop

end Cat

section Residual

set_option linter.unusedSectionVars false

@[expose] def D4PlanesRest3 :
    Prop :=
  UniSeitzPlanes fun d p E => Inputs2311g.OddCpfRest4 d p E ∧ ¬ InnerPlane d p E ∧
    ¬ Inputs2311k.D4GraphG2Plane d p E ∧ ¬ Inputs2311m.D4GraphA2FramePlane d p E ∧
    ¬ Inputs2311m.TrialityBorelPairPlane d p E ∧
    ¬ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧ q.card % 3 = 1

theorem d4PlanesRest2_of_rest3 (h : D4PlanesRest3) : Inputs2311m.D4PlanesRest2 := by
  intro d p hp hp2 hpd hex E hE hc ⟨hR, hin, hg, hf, hb⟩
  by_cases hs : ∃ q : TauCeti.PrimePower, d.1 = .D 4 q ∧ q.card % 3 = 1
  · obtain ⟨q, hq, hq1⟩ := hs
    rcases hR.2 with ⟨-, hp3, -, -, ⟨q', hq', K, hF, hfin, hK, e, hG⟩, -⟩ | ⟨hin', -⟩ | ⟨-, -, htri, -⟩
    · have hqq : q' = q := by
        rw [hq] at hq'
        cases hq'
        rfl
      subst hqq
      exact uniSeitzPlanes_dFour_graphSplit d p hp hp2 hpd hex E hE hc
        ⟨hp3, hR.1.1.1, hin, q', hq', hq1, K, hF, hfin, hK, e, hG⟩
    · exact absurd hin' hin
    · obtain ⟨q', hq'⟩ := htri
      rw [hq] at hq'
      cases hq'
  · exact h d p hp hp2 hpd hex E hE hc ⟨hR, hin, hg, hf, hb, hs⟩

end Residual

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311q
