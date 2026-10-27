module

public import CFSG.LieType.Chevalley.CLSEvenE6GraphInvolutionFourGroup
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenE6AllInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem exists_four_group_le_fixedSubgroup_of_eqLocus {C : Type*} [Group C] {β : MulAut C}
    {A : Subgroup C} (hA : A ≤ β.toMonoidHom.eqLocus (MonoidHom.id C))
    (hAab : CFSG.Open.IsElemAbelian 2 A) (hAc : Nat.card A = 4) :
    ∃ V : Subgroup C, V ≤ fixedSubgroup β ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 :=
  ⟨A, hA, { toIsMulCommutative := hAab.1
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
              Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hAab.2 x x.2) },
    hAc⟩

theorem mem_inner_of_conj_mul_rootDiagAut
    {τ : Tag} {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) {β : MulAut (adjointGroup τ K)}
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (hβ : β = MulAut.conj g * rootDiagAut τ K a)
    (hβ2 : β ^ 2 = 1) : β ∈ inner (adjointGroup τ K) := by
  set q := 2 ^ f with hq
  have hq1 : Odd (q - 1) := by
    have h1 : 1 ≤ q := Nat.one_le_two_pow
    have h2 : Even q := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd h1 h2 odd_one
  have ha : a ^ (q - 1) = 1 := funext fun j => by
    rw [Pi.pow_apply, Pi.one_apply, ← hK, ← Nat.card_units]
    exact pow_card_eq_one'
  have hδ : rootDiagAut τ K a ^ (q - 1) = 1 := by
    change rootDiagAutHom τ K a ^ (q - 1) = 1
    rw [← map_pow, ha, map_one]
  set x : Outer (adjointGroup τ K) := (β : Outer (adjointGroup τ K)) with hx
  have hg : ((MulAut.conj g : MulAut (adjointGroup τ K)) : Outer (adjointGroup τ K)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have hxq : x ^ (q - 1) = 1 := by
    rw [hx, hβ, QuotientGroup.mk_mul, hg, one_mul, ← QuotientGroup.mk_pow, hδ,
      QuotientGroup.mk_one]
  have hx2 : x ^ 2 = 1 := by rw [hx, ← QuotientGroup.mk_pow, hβ2, QuotientGroup.mk_one]
  have hord : orderOf x ∣ Nat.gcd 2 (q - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2) (orderOf_dvd_of_pow_eq_one hxq)
  have hgcd : Nat.gcd 2 (q - 1) = 1 :=
    (Nat.coprime_two_left.2 hq1)
  rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
  exact (QuotientGroup.eq_one_iff β).1 hord

theorem exists_four_group_of_outer_E6
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (β : MulAut (adjointGroup TwistTag.E6.tag K)) (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ inner (adjointGroup TwistTag.E6.tag K)) :
    ∃ A : Subgroup (adjointGroup TwistTag.E6.tag K), A ≤ β.toMonoidHom.eqLocus (MonoidHom.id _) ∧
      CFSG.Open.IsElemAbelian 2 A ∧ Nat.card A = 4 := by
  obtain ⟨-, -, hexist⟩ :=
    ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hexpr⟩ := hexist β
  by_cases hσ : σ = 1
  · subst hσ
    have hid : ∀ h : ModGL TwistTag.E6.tag K,
        Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) h = h := fun h =>
      Units.ext (entrywise_id _)
    obtain ⟨ε, hε⟩ := ε
    have hε' : ε = 0 ∨ ε = 1 := by
      change ε < 2 at hε
      omega
    rcases hε' with rfl | rfl
    ·
      exfalso
      refine hβo (mem_inner_of_conj_mul_rootDiagAut hK hf g a ?_ hβ2)
      refine MulEquiv.ext fun h => Subtype.ext ?_
      have e := hexpr h
      have hQ0 : exactQ TwistTag.E6.tag K ((⟨0, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) = 1 :=
        pow_zero _
      rw [hQ0, hid, mul_one, inv_one, mul_one] at e
      rw [e, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    ·
      have hQ1 : exactQ TwistTag.E6.tag K ((⟨1, hε⟩ : Fin (exactE TwistTag.E6.tag)) : ℕ) =
          diagramMap TwistTag.E6 K := pow_one _
      refine (even_E6_graph_involution_fixed_four_group f hf).1 K hK β
        (g : ModGL TwistTag.E6.tag K) a g.2 (fun h => ?_) hβ2
      have e := hexpr h
      rw [hQ1, hid] at e
      refine e.trans ?_
      group
  · exact even_E6_field_involution_fixed_four_group_of_expr hf K hK β hβ2 g a σ ε hexpr hσ

theorem _root_.CFSG.LieType.Chevalley.even_E6_twisted_E6_all_involution_fixed_four_group
    (L : Type) [Group L] [Finite L] [IsSimpleGroup L] (hLnab : ∃ a b : L, a * b ≠ b * a)
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .twistedE6) {f : ℕ} (hf : 1 ≤ f)
    (hL : ChevalleyExceptionalModel L t 2 f) (α : MulAut L) (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  classical
  by_cases hin : α ∈ inner L
  · obtain ⟨g, rfl⟩ := hin
    exact exists_four_group_le_fixedSubgroup_conj hLnab g hα
  rcases ht with rfl | rfl
  ·
    have hm : UntwistedChevalleyModel L .E6 (2 ^ f) := hL.2
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
    set β := MulAut.congr e α with hβdef
    have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
    have hβo : β ∉ inner (adjointGroup Tag.E6 K) := by
      rw [hβdef, congr_mem_inner_iff]
      exact hin
    obtain ⟨A, hA, hAab, hAc⟩ := exists_four_group_of_outer_E6 hf K hK β hβ2 hβo
    obtain ⟨V, hV, hVab, hVc⟩ := exists_four_group_le_fixedSubgroup_of_eqLocus hA hAab hAc
    exact exists_four_group_le_fixedSubgroup_of_congr e α hV hVab hVc
  ·
    have hm : TwistedChevalleyModel L .E6 (2 ^ f) := hL.2
    obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf hm
    set β := MulAut.congr e α with hβdef
    have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
    have hβo : ∀ c, β ≠ MulAut.conj c := fun c h => hin (by
      rw [← congr_mem_inner_iff e, ← hβdef, h]
      exact ⟨c, rfl⟩)
    obtain ⟨A, hA, hAab, hAc⟩ :=
      (even_E6_graph_involution_fixed_four_group f hf).2 K hK σ.toRingHom hσ β hβo hβ2
    obtain ⟨V, hV, hVab, hVc⟩ := exists_four_group_le_fixedSubgroup_of_eqLocus hA hAab hAc
    exact exists_four_group_le_fixedSubgroup_of_congr e α hV hVab hVc

end CFSG.LieType.Chevalley.EvenE6AllInvolution
