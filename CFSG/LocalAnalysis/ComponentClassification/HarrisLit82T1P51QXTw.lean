module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXTw1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXTw2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QFAt

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.Burgoyne.E2 CFSG.ComponentClassification.Burgoyne.E2.TwE6In
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem famF_twistedE6 :
    FamF .twistedE6 := by
  classical
  refine famF_of_fAt fun X _ _ _ n p f hp hp2 hX hq z hz => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hm := GH74.chevalleyExceptionalModel_of_lieModel (t := .twistedE6) (by decide) hX
  have hf : 1 ≤ f := hm.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .E6 hp hf hm.2
  have hK2 : Nat.card K = (p ^ f) ^ 2 := hK
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h3 : 3 ≤ p ^ f := le_trans hp3 (Nat.le_self_pow (by omega) p)
    obtain ⟨m, hm'⟩ := hodd
    omega
  have : CharP K p := finite_field_prime_power_characteristic hp (show 1 ≤ 2 * f by omega)
    (by rw [hK2, ← pow_mul, mul_comm])
  set L := AlgebraicClosure K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K L
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  set t : C₀ := e z with htdef
  have ht : orderOf t = 2 := (orderOf_injective e.toMonoidHom e.injective z).trans hz
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨hder, -⟩ := twE6_lift_facts (p := p) (k := L) hf hodd K hK2 σ hσ
  have hxH : baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) ∈
      ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag L)
          (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag L)
          (frobTwistGL TwistTag.E6.tag L p f (diagramMap TwistTag.E6 L))⁆ := by
    rw [hder]
    exact ⟨t, t.2, rfl⟩
  have hxR := Subgroup.commutator_le_of_le le_rfl le_rfl hxH
  have hx2 : baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) ^ 2 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, ht2, Subgroup.coe_one, map_one]
  obtain ⟨r, hr, D, h, g₁, s, hg₁G, hhT, hFg₁, -, hg₁x, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    ClassicalInvolution.Q3.exc3_e6_datum_conj p hp2 hk hf hxR hx2
  have hrmask : r.mask = 0 ∨ r.mask = 20 ∨ r.mask = 2 := by
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hmodel : CentModel (fixedSubgroup (MulAut.conj t)) := by
    rcases hrmask with h0 | h20 | h2
    · exfalso
      apply ht1
      have e1 : rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag r.mask)) = 1 := by
        have e0 : signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 0) = 1 := by
          funext j
          rw [signCharTuple, signMaskChar_single]
          simp
        rw [h0, e0]
        exact rootDiagUnit_one
      rw [e1] at hg₁x
      refine Subtype.ext (baseChangeGL_injective (algebraMap K L) ?_)
      rw [Subgroup.coe_one, map_one]
      calc baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) =
          g₁⁻¹ * (g₁ * baseChangeGL (algebraMap K L) (t : ModGL TwistTag.E6.tag K) * g₁⁻¹) *
            g₁ := by group
        _ = 1 := by rw [hg₁x]; group
    · exact centModel_twE6_t1 hp2 hf hK2 σ hσ t hg₁G hFg₁ (by rw [hg₁x, h20])
    · exact centModel_twE6_t2 hp2 hf h5 K hK2 σ hσ t D h _ hhT (by rw [hDχ, h2]) hDe hDθ hDF
        hcent
  have hfix : (centralizer ({z} : Set X)).map e.toMonoidHom = fixedSubgroup (MulAut.conj t) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
      change t * e x * t⁻¹ = e x
      rw [htdef, ← map_inv, ← map_mul, ← map_mul, ← hx', mul_inv_cancel_right]
    · intro hy
      have hy' : t * y * t⁻¹ = y := hy
      refine ⟨e.symm y, Subgroup.mem_centralizer_singleton_iff.2 (e.injective ?_),
        e.apply_symm_apply y⟩
      rw [map_mul, map_mul, e.apply_symm_apply, ← htdef]
      calc y * t = t * y * t⁻¹ * t := by rw [hy']
        _ = t * y := by group
  let Θ₀ : centralizer ({z} : Set X) ≃* fixedSubgroup (MulAut.conj t) :=
    ((centralizer ({z} : Set X)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix)
  obtain ⟨hcomm, hinv⟩ := evenCent_of_centModel hz Θ₀ hmodel
  exact fAt_of_evenCent hcomm hinv

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
