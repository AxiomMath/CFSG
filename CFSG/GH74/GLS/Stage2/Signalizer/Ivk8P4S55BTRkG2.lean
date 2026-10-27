module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkG2Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Out
public import CFSG.RankThree.PartOne.S11c.G2Plane

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LieType.Chevalley
  CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LieType.Ree (ReeTag)



namespace RkG2

theorem not_kindFactorAll_fg2 {k : Kind} (hk : IsClassicalKind k) {Y : Type} [Group Y]
    [Finite Y] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hp2 : p ≠ 2)
    (hLie : LieModel Y .G2 0 p f) : ¬ KindFactorAll k Y := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hLie
  have hY : Nat.card Y = (p ^ f) ^ 6 * ((p ^ f) ^ 6 - 1) * ((p ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hcard]
    rfl
  have hq3 : 3 ≤ p ^ f :=
    le_trans (show 3 ≤ p by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  exact not_kindFactorAll_of_not_kindFactor hk (quad_bad_numbers hp hp2 hf hq3 hY)

variable {F : Type} [Field F] [Finite F]

theorem g2_three_outer_fixed (hK : Nat.card F = 3) {α : MulAut (adjointGroup ReeTag.G2.tag F)}
    (hα : α ^ 2 = 1) (hnot : α ∉ (MulAut.conj : adjointGroup ReeTag.G2.tag F →*
      MulAut (adjointGroup ReeTag.G2.tag F)).range) :
    ∃ K : Subgroup (adjointGroup ReeTag.G2.tag F), (∀ y ∈ K, α y = y) ∧ IsSimpleGroup ↥K ∧
      (∃ a b : ↥K, a * b ≠ b * a) ∧ Nat.card ↥K = 504 := by
  have hK1 : Nat.card F = 3 ^ 1 := by simpa using hK
  have hK0 : Nat.card F = 3 ^ (2 * 0 + 1) := by simpa using hK
  have : CharP F ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      le_rfl hK1
  rcases CFSG.LieType.AlgebraicGroups.G2_three_involution_inner_quadratic_or_exceptional
      (f := 1) le_rfl hK1 hα with
    ⟨g, a, hαg⟩ | ⟨e, he, hKe, δ, hδ, g, a, hαg⟩ | ⟨b, g, hfb, rfl⟩
  · exact absurd (ivk93res_inner_of_diag hαg) hnot
  · exfalso
    have h3 : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega) 3
    have h9 : 3 * 3 ≤ 3 ^ e * 3 ^ e := Nat.mul_le_mul h3 h3
    rw [hKe, sq] at hK
    omega
  · have hb : b = 0 := by omega
    subst hb
    have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
    obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
      CFSG.LieType.Ree.G2_exceptional_coset_involution_fixed_p_components 0 F hK0 g hα
    obtain ⟨-, ⟨e, -⟩, -, -⟩ := fixed_centralizer_of_conj_eq hψ
    have hmap : ((ReeTag.G2.finiteReeAut F 0).toMonoidHom.eqLocus (MonoidHom.id _)).map
        (adjointGroup ReeTag.G2.tag F).subtype = ReeTag.G2.reeGamma F 0 := rfl
    let Ψ := e.trans ((Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans
      (MulEquiv.subgroupCongr hmap))
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max
      (fun w : WeylGroup ReeTag.G2.tag => (coxeterSystem ReeTag.G2.tag).length w)
    obtain ⟨hs, hnab, -, -, hzero, -⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components 0 F hK0
    obtain ⟨-, h504, -⟩ := hzero rfl w₀ hw₀
    let ι : ↥(ReeTag.G2.reeGamma F 0) →* adjointGroup ReeTag.G2.tag F :=
      (Subgroup.subtype _).comp Ψ.symm.toMonoidHom
    have hι : Function.Injective ι := Subtype.val_injective.comp Ψ.symm.injective
    let D := commutator ↥(ReeTag.G2.reeGamma F 0)
    let χ : ↥D ≃* ↥(D.map ι) := D.equivMapOfInjective ι hι
    refine ⟨D.map ι, ?_, χ.symm.isSimpleGroup, ?_, ?_⟩
    · rintro _ ⟨d, -, rfl⟩
      exact (Ψ.symm d).2
    · obtain ⟨a, b, hab⟩ := hnab
      exact ⟨χ a, χ b, fun h => hab (χ.injective (by rw [map_mul, map_mul, h]))⟩
    · rw [← Nat.card_congr χ.toEquiv]
      exact h504

theorem admRank3_g2g {k : Kind} (hk : IsClassicalKind k) (hodd : Odd (Nat.card F))
    (h3 : 3 ≤ Nat.card F) : AdmRank3 k ↥(adjointGroup ReeTag.G2.tag F) := by
  have : Finite (ModGL ReeTag.G2.tag F) := finite_modGL
  refine admRank3_of_inner (conj_injective_of_center center_adjointGroup_eq_bot) ?_ ?_
  · intro W hW
    have := hW
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite (ModGL .G2 F) := finite_modGL
    let ψ : ↥(adjointGroup ReeTag.G2.tag F) →* ModGL .G2 F :=
      (adjointGroup .G2 F).subtype.comp (MulEquiv.refl ↥(adjointGroup .G2 F)).toMonoidHom
    have hψ : Function.Injective ψ := fun a b hab => Subtype.ext hab
    have hR : W.map ψ ≤ adjointGroup .G2 F := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have : IsElementaryAbelian 2 ↥(W.map ψ) := IsElementaryAbelian.map ψ
    have h8 := (CFSG.RankThree.PartOne.g2_elementary_two hodd hR).1
    rwa [Subgroup.card_map_of_injective hψ] at h8
  · intro x hxx hnot
    have hx2 : x ^ 2 = 1 := by rw [sq]; exact hxx
    by_cases h5 : 5 ≤ Nat.card F
    · obtain ⟨K, hK, hs, hnab, hbad⟩ := g2_outer_involution_bad hodd h5 hx2 hnot
      exact not_admAut_of_le (fun y hy => hK hy) (not_isSolvable_of_exists_ne hnab)
        (not_kindFactorAll_of_not_kindFactor hk hbad)
    · have hF3 : Nat.card F = 3 := by
        obtain ⟨m, hm⟩ := hodd
        omega
      obtain ⟨K, hK, hs, hnab, h504⟩ := g2_three_outer_fixed hF3 hx2 hnot
      exact not_admAut_of_le hK (not_isSolvable_of_exists_ne hnab)
        (not_kindFactorAll_of_card_eq_504 hk h504)

end RkG2

open RkG2 in
theorem rankCell_fg2 : RankCell FG2 := by
  intro k hk Y _ _ _ hY
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  refine ⟨not_kindFactorAll_fg2 hk hp hf hp2 hLie, ?_⟩
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hLie
  have hodd : Odd (Nat.card F) := hcard ▸ (hp.odd_of_ne_two hp2).pow
  have h3 : 3 ≤ Nat.card F := by
    rw [hcard]
    exact le_trans (show 3 ≤ p by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  exact admRank3_of_equiv e (admRank3_g2g hk hodd h3)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
