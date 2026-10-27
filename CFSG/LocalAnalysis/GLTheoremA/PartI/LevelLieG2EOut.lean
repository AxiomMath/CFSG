module

public import CFSG.GH74.GLS.Stage2.OddAut.LangR
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyG2
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.GH74.GLS.Stage2.OddAut (normSeq normSeq_eq_one_of_pow_eq_one exists_conj_mul_eq_of_norm_eq_one_r)
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)

theorem fixSubgroup_conj_map {S : Type*} [Group S] (β Φ : MulAut S) :
    fixSubgroup (β * Φ * β⁻¹) = (fixSubgroup Φ).map β.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map, mem_fixSubgroup]
  constructor
  · intro hx
    refine ⟨β⁻¹ x, mem_fixSubgroup.2 ?_, by simp⟩
    have h1 : β (Φ (β⁻¹ x)) = x := hx
    have h2 := congrArg (⇑β⁻¹) h1
    simpa using h2
  · rintro ⟨y, hy, rfl⟩
    have hy' : Φ y = y := hy
    show β (Φ (β⁻¹ (β y))) = β y
    simp [hy']

theorem fixSubgroup_sq {S : Type*} [Group S] (α : MulAut S) (h : α ^ 3 = 1) :
    fixSubgroup (α ^ 2) = fixSubgroup α := by
  ext x
  rw [mem_fixSubgroup, mem_fixSubgroup]
  constructor
  · intro hx
    have h1 : (α ^ 2) x = x := hx
    have h2 : α = (α ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, h, one_mul, pow_one]
    rw [h2, pow_two, MulAut.mul_apply, h1, h1]
  · intro hx
    have h1 : α x = x := hx
    show (α ^ 2) x = x
    rw [pow_two, MulAut.mul_apply, h1, h1]



variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem g2e_outer_aux (hK : Nat.card K = 8) {fr : K ≃+* K} (hfr : ∀ c, fr c = c ^ 2)
    (hord : orderOf fr = 3) {α : MulAut ↥(adjointGroup .G2 K)} {g : ↥(adjointGroup .G2 K)}
    (hα3 : α ^ 3 = 1)
    (hgσ : ∀ h : ↥(adjointGroup .G2 K), (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
      Units.map (entrywiseHom fr.toRingHom) (h : ModGL .G2 K) * (g : ModGL .G2 K)⁻¹) :
    Nat.card ↥(fixSubgroup α) = 12096 := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * 1) := by rw [hK]; norm_num
  have hfr3 : fr ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one fr
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  set Φ : MulAut ↥(adjointGroup .G2 K) := entrywiseAdjointAut .G2 fr with hΦdef
  have hαeq : α = MulAut.conj g * Φ := MulEquiv.ext fun h => Subtype.ext (by
    rw [hgσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      hΦdef, coe_entrywiseAdjointAut .G2, Subgroup.coe_inv])
  have hΦ3 : Φ ^ 3 = 1 := by rw [hΦdef, ← entrywiseAdjointAut_pow, hfr3, entrywiseAdjointAut_one]
  have hN : normSeq Φ g 3 = 1 := normSeq_eq_one_of_pow_eq_one hZ hΦ3 (hαeq ▸ hα3)
  obtain ⟨β, hβ⟩ := exists_conj_mul_eq_of_norm_eq_one_r (p := 2) (m := 1) (r := 3) le_rfl
    (by norm_num) hK3 (σ := fr) (fun c => by rw [hfr, pow_one]) (Φ := Φ)
    (fun h => coe_entrywiseAdjointAut .G2 fr h) hN
  rw [hαeq, hβ, fixSubgroup_conj_map, Subgroup.card_map_of_injective β.injective]
  obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixedGroup_G2 fr
  have hfix : Nat.card ↥(fixSubgroup Φ) = Nat.card ↥(adjointGroup .G2 (fixSubfield fr)) :=
    Nat.card_congr ((Equiv.subtypeEquivRight fun _ => Iff.rfl).trans e.toEquiv)
  rw [hfix]
  obtain ⟨-, hc⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by norm_num : 1 ≤ 3) (by rw [hK]; norm_num) fr
  rw [hord] at hc
  rw [card_adjointGroup_G2, hc]
  norm_num [CFSG.Open.ordG2]


theorem g2e_outer_card (hK : Nat.card K = 8) {α : MulAut ↥(adjointGroup .G2 K)}
    (hα : α ^ 3 = 1) (hout : ∀ g : ↥(adjointGroup .G2 K), α ≠ MulAut.conj g) :
    Nat.card ↥(fixSubgroup α) = 12096 := by
  classical
  have hK3 : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨hNF, Θ, hΘ1, -, hΘk, -⟩ :=
    even_G2_exact_automorphism_normal_form (f := 3) (by norm_num) K hK3
  obtain ⟨fr, hfr, hord, htop, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two (by norm_num : 1 ≤ 3) hK3
  have hfr3 : fr ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one fr
  have hΘα1 : Θ α ≠ 1 := by
    intro h1
    have h2 : α ∈ Θ.ker := h1
    rw [hΘk] at h2
    obtain ⟨g, hg⟩ := h2
    exact hout g hg.symm
  have key : ∀ α' : MulAut ↥(adjointGroup .G2 K), α' ^ 3 = 1 → Θ α' = fr →
      Nat.card ↥(fixSubgroup α') = 12096 := by
    intro α' hα' hΘ'
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF α'
    have hσ : σ = fr := (hΘ1 α' g σ hgσ).symm.trans hΘ'
    subst hσ
    exact g2e_outer_aux hK hfr hord hα' hgσ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top (Θ α))
  have hk3 : fr ^ k = fr ^ (k % 3) := by
    conv_lhs => rw [← zpow_mod_orderOf fr k]
    rw [hord]
    norm_cast
  have hkm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hkm with h0 | h1 | h2
  · exact absurd (by rw [← hk, hk3, h0, zpow_zero]) hΘα1
  · exact key α hα (by rw [← hk, hk3, h1, zpow_one])
  · have hΘ2 : Θ α = fr ^ 2 := by rw [← hk, hk3, h2]; norm_cast
    have h4 : Θ (α ^ 2) = fr := by
      rw [map_pow, hΘ2, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hfr3, one_mul, pow_one]
    rw [← fixSubgroup_sq α hα]
    exact key (α ^ 2) (by rw [← pow_mul, mul_comm, pow_mul, hα, one_pow]) h4


end CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E
