module

public import CFSG.Quasithin.H13.A5W1622r
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_kbar_plus_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLv : S.Lv ≤ Subgroup.normalizer (K : Set G)) :
    ∃ π : ↥K ⧸ CFSG.pCore 2 ↥K →* ↥(S.plus K), Function.Surjective π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) := hKH.trans hR.2.1
  set φ := InternalSec.autOnHom hKW with hφ
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hKW

  have hHK : S.HK K ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hLv) hT
  have hOC : pCoreOf 2 K ≤ Subgroup.centralizer (S.WK K : Set G) := by
    refine hR.2.2.2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (fun g hg => C1.mem_normalizer_blockQ (hHK hg)) fun d hd => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h1]
    exact Subgroup.one_mem _
  have hker : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro q hq
    rw [InternalSec.mem_ker_autOnHom]
    have hq' : q ∈ CFSG.Open.pCore 2 ↥K := by rw [← CFSG.pCore_eq_open]; exact hq
    exact hOC ⟨q, hq', rfl⟩
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hker, ?_⟩
  intro y
  obtain ⟨k, rfl⟩ := hφs y
  exact ⟨QuotientGroup.mk k, rfl⟩

theorem kbar_cases_F4 (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 168 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 360 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 2520 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 6048) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      (Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 168 ∧
        A36Case3 ↥(modO2Image (Subgroup.centralizer ({S.v12} : Set G)) K)) := by
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
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot_F4 h1222 h517 hF) hK
  rcases hA with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3 | h4
  · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1)
  · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1)
  · right
    have h3' := h3
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, hnat⟩ := h3
    obtain ⟨-, ψ₃, hψ₃s, hψ₃k, -⟩ := hnat
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := by
      have : IsMulCommutative (Multiplicative (Fin 2 → ZMod p)) := inferInstance
      exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs hp hp5 ψ₃ hψ₃s hψ₃k
    exact ⟨(prime_eq_seven_of_sl2 hp hp3 hc1 hc2 hN hcard).1, h3'⟩
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
    rcases hN with h | h | h | h <;> rw [h] at hcard <;> omega

end Setting

end CFSG.Quasithin.H13.A5
