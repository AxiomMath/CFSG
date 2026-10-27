module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.U33Crit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Final
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

section Translate

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem clause_of_commOn_quot [Finite X] (L : Subgroup (X ⧸ gnC T)) {n : ℕ}
    (hirr : ∀ Z : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)),
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) L Z → fixOn (gnRep hV) L (commOn (gnRep hV) L ⊤) ≤ Z →
      Z ≤ commOn (gnRep hV) L ⊤ →
      Z = fixOn (gnRep hV) L (commOn (gnRep hV) L ⊤) ∨ Z = commOn (gnRep hV) L ⊤)
    (hdim : Module.finrank (ZMod 2) ↥(commOn (gnRep hV) L ⊤) =
      Module.finrank (ZMod 2) ↥(fixOn (gnRep hV) L (commOn (gnRep hV) L ⊤)) + n)
    (hn : 0 < n) :
    HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
      (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ n := by
  classical
  set ρ := gnRep hV with hρ
  set L' := L.comap (QuotientGroup.mk' (gnC T)) with hL'
  set U := commOn ρ L ⊤ with hU
  set C := fixOn ρ L U with hC
  have hUs : subOf hV U = ⁅gnV T, L'⁆ := subOf_commOn hV L
  have hCs : subOf hV C = ⁅gnV T, L'⁆ ⊓ Subgroup.centralizer (L' : Set X) := by
    rw [hC, subOf_fixOn, hUs]
  have hCU : C ≤ U := fun v hv => (mem_fixOn.mp hv).1
  have hcard : ∀ N : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)),
      Nat.card N = 2 ^ Module.finrank (ZMod 2) N := by
    intro N
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  refine ⟨⟨?_, fun W' hW1 hW2 hW3 => ?_⟩, ?_⟩
  · rw [← hCs, ← hUs]
    refine lt_of_le_of_ne ((subOf_le_subOf_iff hV).mpr hCU) fun h => ?_
    have h1 := congrArg (fun H : Subgroup X => Nat.card H) h
    rw [card_subOf, card_subOf, hcard, hcard, hdim] at h1
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  · rw [← hCs] at hW1
    rw [← hUs] at hW2
    rw [← hCs, ← hUs]
    have hW'V : W' ≤ gnV T := hW2.trans (subOf_le_gnV hV U)
    have hinv := isInvariant_modOf hV L hW3
    have h1 : C ≤ modOf hV W' := by
      rw [← modOf_subOf hV C]
      intro w hw
      exact hW1 hw
    have h2 : modOf hV W' ≤ U := by
      rw [← modOf_subOf hV U]
      intro w hw
      exact hW2 hw
    rcases hirr _ hinv h1 h2 with h | h
    · left
      rw [← h, subOf_modOf hV hW'V]
    · right
      rw [← h, subOf_modOf hV hW'V]
  · rw [← hCs, ← hUs]
    have hle : subOf hV C ≤ subOf hV U := (subOf_le_subOf_iff hV).mpr hCU
    have h1 := Subgroup.relIndex_mul_card (subOf hV C) (subOf hV U)
    rw [inf_eq_left.mpr hle, card_subOf, card_subOf, hcard, hcard, hdim, pow_add] at h1
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 2) _) (h1.trans (mul_comm _ _))

end Translate

section U33


theorem u33_clause {X : Type} [Group X] [Finite X] (T : Subgroup X)
    (hC : CharTwo (⊤ : Subgroup X)) (hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T)
    (L : Subgroup (X ⧸ gnC T)) (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hLs : IsSimpleGroup ↥L)
    (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1) :
    HasIrreducibleCommutatorQuotient (L.comap (QuotientGroup.mk' (gnC T))) (gnV T) ∧
      (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
          Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
        ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6 := by
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
  have hP : B42TypeU33 ↥L := G11.Harris.G2.b42TypeU33_of_simple hLs hm
  have hL6048 : Nat.card ↥L = 6048 := B42U33.card_of_b42TypeU33 hP
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup ↥L := { (inferInstance : Group ↥L) with mul_comm := hcon }
    have := IsSimpleGroup.prime_card (α := ↥L)
    rw [hL6048] at this
    exact absurd this (by norm_num)
  obtain ⟨hirr, k, hdim, hk⟩ := commOn_quot_of_secCrit ρ hinj hP.1 hnab
    (u33_secCrit hLs hm) (MulEquiv.refl _) hA2 hAN hLA hb
  have hk6 : k = 6 := Nat.pow_right_injective le_rfl hk
  subst hk6
  exact clause_of_commOn_quot hV L hirr hdim (by norm_num)

theorem agl81FiveThreeU33_proved : AGL81FiveThreeU33 := by
  intro X _ _ T _ hC _ hQT L hL hJ ⟨d, ⟨q, hq3, hqd⟩, ⟨e⟩⟩
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hqd
  subst hqd
  have hm0 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨hp3, he1⟩ : q.p = 3 ∧ q.exponent = 1 :=
    (Nat.Prime.pow_eq_iff Nat.prime_three).mp (by rw [← TauCeti.PrimePower.card_def]; exact hq3)
  rw [hp3, he1] at hm0
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1 := hm0
  obtain ⟨eU⟩ := nonempty_mulEquiv_u33G_of_statedClassicalModel hm
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  exact u33_clause T hC hQT L hL hJ eU.isSimpleGroup hm

end U33

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
