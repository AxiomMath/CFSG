module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Crit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.U33Clause

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem a7_clause_dim
    {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (hC : CharTwo (⊤ : Subgroup X)) (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (eL : ↥L ≃* alternatingGroup (Fin 7)) :
    HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
      ((⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 4 ∨
       (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6) := by
  classical
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV_of_le hC hQT
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hVT : gnV T ≤ T := gnV_le_of_le hC hQT
  obtain ⟨A, hA, hAN, hLA⟩ := exists_offender_of_le hV hVT L hL hJ
  have hAb := isBestOffender_gnRep_of_le hV hVT hA
  set ρ := gnRep hV with hρ
  have hinj : Function.Injective ρ := gnRep_injective hV
  have hA2 := isElementaryAbelian_map_mk hA
  have hfaith : ∀ a ∈ A.map (QuotientGroup.mk' (gnC T)), (∀ v, ρ a v = v) → a = 1 :=
    fun a _ h => hinj (by rw [map_one]; exact LinearMap.ext h)
  have hb : IsBestOffenderOn ρ (A.map (QuotientGroup.mk' (gnC T))) ⊤ :=
    (isBestOffender_iff_on ρ _ hfaith).mp ⟨hA2, hAb⟩
  have hsimp7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hcard7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hnab : ∃ a b : alternatingGroup (Fin 7), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup (alternatingGroup (Fin 7)) :=
      { (inferInstance : Group (alternatingGroup (Fin 7))) with mul_comm := hcon }
    have := IsSimpleGroup.prime_card (α := alternatingGroup (Fin 7))
    rw [hcard7] at this
    exact absurd this (by norm_num)
  have hZ : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 7)))
      with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  obtain ⟨hirr, k, hdim, hk⟩ := commOn_quot_of_secCrit ρ hinj hZ hnab alt7_secCrit eL hA2 hAN
    hLA hb
  have hk46 : k = 4 ∨ k = 6 := by
    rcases hk with h | h
    · exact Or.inl (Nat.pow_right_injective le_rfl h)
    · exact Or.inr (Nat.pow_right_injective le_rfl h)
  have hkpos : 0 < k := by omega
  obtain ⟨hHI, hidx⟩ := clause_of_commOn_quot hV L hirr hdim hkpos
  refine ⟨hHI, ?_⟩
  rcases hk46 with rfl | rfl
  · exact Or.inl hidx
  · exact Or.inr hidx

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
