module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitKernel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup

theorem isLocallyTwoBalanced_of_mulEquiv_held {K : Type} [Group K] [Finite K]
    (e : K ≃* Blueprint.NativeSporadic.He) :
    ClassicalInvolution.Balance.IsLocallyTwoBalanced K := by
  have : IsSimpleGroup K := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He e
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_held
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul, h]))⟩
  intro H hH F hF4 hF2
  obtain ⟨e'⟩ := nonempty_generalizedFitting_equiv hnab hH
  rw [deltaCore_eq_iInf_pPrimeCore]
  exact deltaCore_eq_bot_of_held (isSimpleGroup_generalizedFitting hnab hH)
    (exists_mul_ne_generalizedFitting hnab hH) ⟨e'.trans e⟩ (nonempty_mulEquiv_four hF4 hF2)

variable {G : Type} [Group G] [Finite G]

theorem commutator_deltaCore_le_of_held {a : G} {J E : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hHe : Nonempty (J ⧸ pPrimeCore 2 J ≃* Blueprint.NativeSporadic.He))
    (hE : E ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G)) (hE4 : Nat.card E = 4)
    (hE2 : ∀ e ∈ E, e * e = 1) :
    ⁅J, (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1), (pPrimeCore 2 (centralizer ({e} : Set G))).map
        (centralizer ({e} : Set G)).subtype) ⊓ centralizer ({a} : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
  obtain ⟨e⟩ := nonempty_image_center_quotient_equiv hJa hJ
  obtain ⟨eHe⟩ := hHe
  obtain ⟨e'⟩ := nonempty_fusionZStar_equiv_held eHe
  exact commutator_deltaCore_le_of_isLocallyTwoBalanced hJa hJ rfl
    (isLocallyTwoBalanced_of_mulEquiv_held (e.trans e')) hE hE4 hE2

theorem commutator_wGroup_le_of_held {a : G} {J E : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hHe : Nonempty (J ⧸ pPrimeCore 2 J ≃* Blueprint.NativeSporadic.He))
    (hE : E ≤ normalizer (J : Set G) ⊓ centralizer ({a} : Set G))
    (hE4 : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ⁅J, wGroup E ⊓ centralizer ({a} : Set G)⁆ ≤
      (pPrimeCore 2 (centralizer ({a} : Set G))).map (centralizer ({a} : Set G)).subtype := by
  obtain ⟨φ⟩ := hE4
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have h2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
    have : (⟨e, he⟩ : E) * ⟨e, he⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
    exact congrArg Subtype.val this
  rw [wGroup_eq_iInf_of_four h4 h2]
  exact commutator_deltaCore_le_of_held hJa hJ hHe
    (fun x hx => mem_inf.mpr ⟨(mem_inf.mp (hE hx)).2, (mem_inf.mp (hE hx)).1⟩) h4 h2

end CFSG.ComponentClassification.GrSLit
