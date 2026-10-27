module

public import CFSG.Quasithin.H13.A5W1623c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1620P
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622r
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622t
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1623b
public import CFSG.Quasithin.H13.A5W1623b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.Quasithin.A5Model
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

@[expose] def End1367L4_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)) → S.InYz K →
      S.Tv ≤ Subgroup.normalizer (K : Set G) → S.Lv ≤ K →
      Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) →
      ∀ t ∈ S.Tv, ∀ Y : Subgroup G, Y ≤ K → S.Tv ⊓ K ≤ Y →
        K ⊓ Subgroup.centralizer (S.WK K : Set G) ≤ Y → t ∈ Subgroup.normalizer (Y : Set G)

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem kbar_isQuasisimple_of_sl_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hYz : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) {m : ℕ} (hm : m = 4 ∨ m = 5)
    (e : ↥(S.plus K) ≃* SpecialLinearGroup (Fin m) (ZMod 2)) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus_F4 h1222 h517 hF hYz.1 hT hLv
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hYz hT
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(modO2Image Gv K) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  let πX : ↥(modO2Image Gv K) →* ↥(S.plus K) := π.comp eX.symm.toMonoidHom
  have hπX : Function.Surjective πX := hπ.comp eX.symm.surjective

  have : IsSimpleGroup (SpecialLinearGroup (Fin m) (ZMod 2)) :=
    sl_isSimple_of_card_two Ln2P.card_zmod_two (by omega)
  have hsP : IsSimpleGroup ↥(S.plus K) := e.isSimpleGroup
  have hZP := center_eq_bot_of_isSimple_of_isQuasisimple hsP hq
  have hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 20160 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 9999360 := by
    rw [Nat.card_congr (quotCenterEquivOfEqBot hZP).toEquiv, Nat.card_congr e.toEquiv]
    exact card_sl45_two hm
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF) hK
  rcases hA with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3 | h4
  · exact (isQuasisimple_congr eX).mpr hcomp.1
  · exact (isQuasisimple_congr eX).mpr hcomp.1
  · exfalso
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, hnat⟩ := h3
    obtain ⟨-, ψ₃, hψ₃s, hψ₃k, -⟩ := hnat
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := by
      have : IsMulCommutative (Multiplicative (Fin 2 → ZMod p)) := inferInstance
      exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs hp hp5 ψ₃ hψ₃s hψ₃k
    exact sl45_card_ne_sl2 hN hp hp5 hc1 hc2 hcard
  · exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image Gv K)))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image Gv K) := by
      ext x
      simp [ψ₄]
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    exact sl45_card_ne_sl2 hN Nat.prime_five le_rfl hc1 hc2 hcard

end Setting

theorem lemma13623C_of_F4
    (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h36 : A36ForSQTK) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h132 : ASInputs.AS_C_1_32_F4) (h134 : C134L32Corr_F4)
    (hres : Lem13622Case4Z0_F4) (hGA : GriessAllModelsStatement) (h620 : Lemma13620L45_F4)
    (hEnd : End1367L4_F4) : Lemma13623C_F4 := by
  intro G _ _ T L V S hH K hK hYz hT
  have key : ∀ m : ℕ, (m = 4 ∨ m = 5) →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2))) := by
    rintro m hm ⟨e⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

    have hLvK := h620 G T L V S hH K hK hYz hT (by
      rcases hm with rfl | rfl
      · exact Or.inl ⟨e⟩
      · exact Or.inr ⟨e⟩)
    let e' : ↥(S.plus K) ≃* SpecialLinearGroup (Fin m) (ZMod 2) :=
      e.trans (specialLinearGroupEquivStatedSL m (ZMod 2)).symm
    have hq := S.kbar_isQuasisimple_of_sl_F4 h1222 h517 hH.hF h36 h37 h38 hK hYz hT hm e'
    have hLv := S.Lv_le_normalizer_of_mem_cComp_F4 h1222 h517 h37 h38 hK
    obtain ⟨α, hαs, hαk, hαC⟩ := S.exists_slHom_plus_F4 h1222 h517 hGA hH.hF hYz.1 hT hLv hq
      (by omega) (by omega) e'

    have hsylH : IsSylowTwoOf S.Tv (K ⊔ S.Tv) :=
      C1GN.isSylowTwoOf_of_le (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right
        (sup_le hYz.1 S.Tv_le_Gv)
    have hSK : IsSylowTwoOf (S.Tv ⊓ K) K :=
      A4.isSylowTwoOf_inf_normal hsylH le_sup_left (sup_le Subgroup.le_normalizer hT)
    obtain ⟨α₂, hα₂s, hα₂k, hmapU⟩ := Ln2.exists_unitriangular hSK (n := m) (by omega) hαs hαk
    have hα₂C : ∀ k : ↥K, α₂ k = 1 ↔ (k : G) ∈ Subgroup.centralizer (S.WK K : Set G) :=
      fun k => by rw [← MonoidHom.mem_ker, hα₂k, ← hαk, MonoidHom.mem_ker, hαC]
    obtain ⟨j, hj, hjm, hP⟩ := S.eq_parabolic_of_sl_F4 h1222 h517 hLvK (by omega) hα₂C hmapU
    have hinner := S.inner_of_sl hT (by omega) (by omega) hα₂s hα₂k hα₂C hmapU hj hjm hP
      (fun hm4 => by
        subst hm4
        exact hEnd G T L V S hH K hK hYz hT hLvK ⟨e⟩)
    exact S.false_of_sl_inner_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 h132 h134 hres
      hH hYz.1 hT hLvK (by omega) (by omega) hα₂s hα₂k hj hjm hP hinner
  exact ⟨key 4 (Or.inl rfl), key 5 (Or.inr rfl)⟩

end CFSG.Quasithin.H13.A5
