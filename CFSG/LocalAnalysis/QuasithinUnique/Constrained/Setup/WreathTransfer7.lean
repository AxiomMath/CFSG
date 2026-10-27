module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

omit [Finite H] in
theorem oddOrderSubgroup_top_eq_closure :
    oddOrderSubgroup (⊤ : Subgroup H) = Subgroup.closure {g : H | Nat.Coprime (orderOf g) 2} := by
  unfold oddOrderSubgroup
  congr 1
  ext g
  simp [Nat.coprime_two_right]

namespace WreathHyp

variable {t : ∀ i, MulAut ↥(planesIn W I i)}

include h

theorem baumann_apply (ht : h.IsT0 t) :
    (CFSG.pCore 2 ↥(oddOrderSubgroup (⊤ : Subgroup H))).map
        (oddOrderSubgroup (⊤ : Subgroup H)).subtype ≤ elemBaumannIn 2 R ∧
      elemCenterIn 2 R =
        (elemCenterIn 2 R ⊓
            Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)) ⊔
          (V ⊓ Subgroup.centralizer ((thompsonJ R : Subgroup H) : Set H)) ∧
      (IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set H)) (Subgroup.centralizer (V : Set H)) →
        IsSylowTwoOf (elemBaumannIn 2 R ⊓ Subgroup.centralizer (V : Set H))
            ((oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
              Subgroup.centralizer (V : Set H)) ∧
          (IsSylowTwoOf ((elemBaumannIn 2 R).map h.rhoV)
              ((oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R).map h.rhoV) →
            IsSylowTwoOf (elemBaumannIn 2 R)
              (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVn := h.V_normal
  obtain ⟨g, hgN, hgD, hgnt⟩ := h.exists_g_odd
  have hgF : ∀ f ∈ F, g * f = f * g := fun f hf => h.odd_centralizes_F hgN hf
  obtain ⟨hHfr1, hHfr2, hHfr3, hHfr4, hHfr5, hHfr6, hHfr7⟩ := h.frattini
  have hV' : CFSG.IsElementaryAbelian 2 V :=
    BlueprintB2.isElementaryAbelian_iff.mpr (isElemAbelian_iff.mp h.V_elem)
  have hJR : thompsonJ R ≤ R := B6.thompsonJ_le R
  have hJe : elemThompsonIn 2 R = thompsonJ R := elemThompsonIn_two_eq R
  have hPQ : CFSG.inSubgroup (CFSG.pCore 2) (oddOrderSubgroup (⊤ : Subgroup H)) ≤
      R ⊓ Subgroup.centralizer (V : Set H) := by
    rw [hHfr2]
    exact (le_of_eq hHfr5).trans inf_le_right
  have hLQ : oddOrderSubgroup (⊤ : Subgroup H) ≤
      Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set H) : Subgroup H) : Set H) := by
    intro x _
    rw [hHfr2]
    have hn : (CFSG.pCore 2 H).Normal := CFSG.pCore_normal
    exact (Subgroup.normalizer_eq_top_iff.mpr hn) ▸ Subgroup.mem_top x
  have hineq : ∀ A ∈ elemThompsonFamily R 2,
      (A ⊓ Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R)).relIndex A ≤
        ((V.subgroupOf R) ⊓ Subgroup.centralizer (A : Set R)).relIndex (V.subgroupOf R) := by
    intro A hA
    have hA' : IsMaxElemAbelian R (A.map R.subtype) :=
      BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily.mpr
        ⟨BlueprintB2.map_subtype_le_self A, by rwa [BlueprintB2.subgroupOf_map_subtype_self]⟩
    have hmain := (h.maxElem_structure ht hA').1
    have hVmap : (V.subgroupOf R).map R.subtype = V := Subgroup.map_subgroupOf_eq_of_le h.V_le_R
    have e1 : (A ⊓ Subgroup.centralizer ((V.subgroupOf R : Subgroup R) : Set R)).relIndex A =
        (A.map R.subtype ⊓ Subgroup.centralizer (V : Set H)).relIndex (A.map R.subtype) := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := R.subtype) _ _ R.subtype_injective,
        ← map_inf_centralizer_map R.subtype R.subtype_injective, hVmap]
    have e2 : ((V.subgroupOf R) ⊓ Subgroup.centralizer (A : Set R)).relIndex (V.subgroupOf R) =
        (V ⊓ Subgroup.centralizer ((A.map R.subtype : Subgroup H) : Set H)).relIndex V := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := R.subtype) _ _ R.subtype_injective,
        ← map_inf_centralizer_map R.subtype R.subtype_injective, hVmap]
    rw [e1, e2]
    exact le_of_eq hmain
  have hXL : ∀ i : Fin 2, ∃ l ∈ oddOrderSubgroup (⊤ : Subgroup H),
      conjugate (![thompsonJ R, conjugate (thompsonJ R) g] i) l ≤ R := by
    intro i
    fin_cases i
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      show cj (thompsonJ R) 1 ≤ R
      rw [cj_one]
      exact hJR
    · refine ⟨g⁻¹, Subgroup.inv_mem _ hgN, ?_⟩
      show cj (cj (thompsonJ R) g) g⁻¹ ≤ R
      rw [cj_inv_cj]
      exact hJR
  have hXJ : ∀ i : Fin 2, (elemThompson (![thompsonJ R, conjugate (thompsonJ R) g] i) 2).map
      (![thompsonJ R, conjugate (thompsonJ R) g] i).subtype =
        ![thompsonJ R, conjugate (thompsonJ R) g] i := by
    intro i
    fin_cases i
    · show elemThompsonIn 2 (thompsonJ R) = thompsonJ R
      rw [← hJe]
      exact elemThompsonIn_eq_of_le 2 le_rfl (hJe ▸ hJR)
    · show elemThompsonIn 2 (cj (thompsonJ R) g) = cj (thompsonJ R) g
      rw [elemThompsonIn_cj, ← hJe]
      congr 1
      exact elemThompsonIn_eq_of_le 2 le_rfl (hJe ▸ hJR)
  have hJJ : CFSG.pRank 2 ↥(thompsonJ R) = CFSG.pRank 2 ↥R := by
    apply le_antisymm (pRank_mono hJR)
    obtain ⟨A, hA⟩ := BlueprintB2.elemThompsonFamily_nonempty R 2
    have hA' : A.map R.subtype ∈ elemFamilyIn 2 R := ⟨A, hA, rfl⟩
    obtain ⟨-, hel, hcard⟩ := mem_elemFamilyIn.mp hA'
    have hAJ : A.map R.subtype ≤ thompsonJ R := hJe ▸ le_elemThompsonIn hA'
    have h1 := card_le_pow_pRank_of_le (p := 2) hAJ hel
    rw [hcard] at h1
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp h1
  have hXe : ∀ i : Fin 2,
      CFSG.pRank 2 ↥(![thompsonJ R, conjugate (thompsonJ R) g] i) = CFSG.pRank 2 ↥R := by
    intro i
    fin_cases i
    · exact hJJ
    · show CFSG.pRank 2 ↥(cj (thompsonJ R) g) = CFSG.pRank 2 ↥R
      rw [pRank_cj, hJJ]
  have hI : thompsonJ R ⊔ conjugate (thompsonJ R) g =
      ⨆ i : Fin 2, ![thompsonJ R, conjugate (thompsonJ R) g] i := by
    apply le_antisymm
    · exact sup_le (le_iSup (fun i : Fin 2 => ![thompsonJ R, conjugate (thompsonJ R) g] i) 0)
        (le_iSup (fun i : Fin 2 => ![thompsonJ R, conjugate (thompsonJ R) g] i) 1)
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
  have hρ : (oddOrderSubgroup (⊤ : Subgroup H)).map (MulAut.conjNormal (H := V)) ≤
      (thompsonJ R ⊔ conjugate (thompsonJ R) g).map (MulAut.conjNormal (H := V)) :=
    h.rhoV_odd_le ht hgnt hgD
  have hcodim : ∏ i : Fin 2,
      (V ⊓ Subgroup.centralizer ((![thompsonJ R, conjugate (thompsonJ R) g] i : Subgroup H) :
        Set H)).relIndex V ≤
      (V ⊓ Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)).relIndex
        V := by
    rw [Fin.prod_univ_two]
    show (V ⊓ Subgroup.centralizer ((thompsonJ R : Subgroup H) : Set H)).relIndex V *
      (V ⊓ Subgroup.centralizer ((conjugate (thompsonJ R) g : Subgroup H) : Set H)).relIndex V ≤ _
    rw [h.relIndex_J ht, h.relIndex_conjugate_J ht hgF, ← h.F_eq_centralizer, h.relIndex_F,
      ← mul_pow]
    norm_num
  have hJdef : thompsonJ R = (elemThompson R 2).map R.subtype :=
    (CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ R).symm
  have key := Baumann_central_splitting_and_Sylow_transfer 2 V hV' R h.sylow.2.1 h.V_le_R
    (oddOrderSubgroup (⊤ : Subgroup H)) oddOrderSubgroup_top_eq_closure h.odd_sup_R
    (R ⊓ Subgroup.centralizer (V : Set H))
    (CFSG.inSubgroup (CFSG.pCore 2) (oddOrderSubgroup (⊤ : Subgroup H))) rfl rfl hPQ hLQ
    (hHfr7 _ hHfr4) hineq 2 (by norm_num) ![thompsonJ R, conjugate (thompsonJ R) g] hXL hXJ hXe
    (thompsonJ R ⊔ conjugate (thompsonJ R) g) hI hρ (thompsonJ R) hJdef le_sup_left hcodim
    (elemBaumannIn 2 R) (elemCenterIn 2 R) rfl rfl
  exact key

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
