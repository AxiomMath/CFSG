module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PCat
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PMain
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem not_two_pow_nine_dvd_of_facts {X : Type} [Group X] [Finite X] {Y L : Subgroup X}
    (hF : Gomi1PFacts Y L) : ¬ 2 ^ 9 ∣ Nat.card L := by
  obtain ⟨-, -, -, -, -, -, ⟨U, -, hUs, hUc, -, -⟩, -⟩ := hF
  have hN0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have h := hUs.card_eq (p := 2)
  rw [hUc] at h
  have hv8 : (Nat.card L).factorization 2 = 8 := (Nat.pow_right_injective le_rfl h).symm
  intro h9
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 h9
  omega

theorem t_not_mem_of_facts {X : Type} [Group X] [Finite X] {Y L : Subgroup X} {t : X}
    (hF : Gomi1PFacts Y L) (hYcard : Nat.card Y = 979200) (ht2 : t * t = 1)
    (htn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) (htY : t ∉ Y) : t ∉ L := by
  intro htL
  have hv := not_two_pow_nine_dvd_of_facts hF
  have hYL : Y ≤ L := hF.le
  have hle : Y ⊔ zpowers t ≤ L := sup_le hYL (zpowers_le.2 htL)
  have h1 := Subgroup.card_dvd_of_le hle
  rw [card_sup_zpowers_of_normalizes ht2 htn htY, hYcard] at h1
  exact hv ((show 2 ^ 9 ∣ 2 * 979200 by norm_num).trans h1)

theorem gomiLemma1PInputK
    (X : Type) [Group X] [Finite X] (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog X)
    (t : X) (Y : Subgroup X) :
    standardComponentOddCore X = ⊥ → orderOf t = 2 → CFSG.Blueprint.LieModel Y .PSp 2 2 2 →
    t ∈ normalizer (Y : Set X) →
    (¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹) →
    centralizer ({t} : Set X) = (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t →
    CFSG.Blueprint.LieModel (genFittingLayer X) .PSp 2 2 2 ∧
      centralizer (genFittingLayer X : Set X) = standardComponentOddCore X := by
  intro hO ht hY htn hout hcent
  have hfacts := gomi1P_facts hO ht hY htn hout hcent
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htn' : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := fun y hy => (mem_normalizer_iff.mp htn y).mp hy
  have htY : t ∉ Y := fun h => hout ⟨t, h, fun z _ => rfl⟩
  have hYcard : Nat.card Y = 979200 :=
    CFSG.ComponentClassification.GSThmB.CF23I.card_of_lieModel_Sp44 hY
  have hLtop : genFittingLayer X ≠ ⊤ := fun h =>
    t_not_mem_of_facts hfacts hYcard ht2 htn' htY (h ▸ Subgroup.mem_top t)
  haveI := hfacts.simple
  have hnab : ∃ a b : ↥(genFittingLayer X), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hfacts.nonabelian
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hcat : Catalog ↥(genFittingLayer X) :=
    CFSG.EvenSmallLie.CatalogOrders.catalog_of_kProper_of_surjective hK (genFittingLayer X) hLtop
      ↥(genFittingLayer X) hnab (MonoidHom.id _) Function.surjective_id
  exact gomi1P_of_ident hO ht hY htn hout hcent (gomi1PIdent_of_catalog hY hcat)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
