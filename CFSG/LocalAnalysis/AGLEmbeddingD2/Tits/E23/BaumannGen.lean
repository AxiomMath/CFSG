module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.JPart
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.NatS3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumannGenSL
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.BaumannGenS3

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS5

variable {G : Type} [Group G] [Finite G] {H T M : Subgroup G}

theorem exists_baumannGen_of_nat
    (hV : IsElemAbelian 2 (VZ T H)) (hmin : MinParabolic H T M) (hmp : MinPar H T M)
    (hF : CharTwo H) (hred : IsTwoReducedIn H (VZ T H))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G))
    (hnat : ∀ E ∈ compSet (autI hV H) (autI hV M), SLType2 (Hyp51.offSet (autI hV H)) E ∨
      (SymType (genD (autI hV H) ⊓ autI hV M) (Hyp51.offSet (autI hV H)) E ∧ Nat.card E = 6)) :
    ∃ g ∈ twoResidual H,
      autI hV (twoResidual H) ≤ autI hV (thompsonJ T) ⊔ autI hV (cjSub g (thompsonJ T)) ∧
      2 * rkIdx (fixV (autI hV (thompsonJ T))) ≤ rkIdx (fixV (autI hV (twoResidual H))) := by
  have h51 := hyp51_of_e23 hV hmin hmp hF hred hJ
  have hF5 := fiveFive_of_e23 hV hmin hmp hF hred hJ
  have hV2 : ∀ v : IntMod (VZ T H) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hsyl := isSylowOf_of_nat h51 hV2 hnat
  have hTH : T ≤ H := hmin.isSylow.1
  have hXT : autI hV (thompsonJ T) ≤ autI hV T :=
    autI_mono hV (thompsonJ_le_self T)
  have hTX := autI_le_normalizer_autI_thompsonJ hV
  have hX₀ := exists_offSet_le_autI_thompsonJ hV hmin hmp hF hred hJ
  have hXgen := autI_thompsonJ_le_iSup hV hmin hmp hF hred hJ
  have hgood : ∀ E ∈ compSet (autI hV H) (autI hV M),
      ∃ y, GoodEl E (autI hV T ⊓ E) y := by
    intro E hE
    obtain ⟨hR, -⟩ := inf_mem_offSet_and_le h51 hV2 hF5 hsyl hXT hTX hX₀ hE
    have hRE : autI hV T ⊓ E ≤ E := inf_le_right
    rcases hnat E hE with hSL | ⟨hSym, hcard⟩
    · exact exists_goodEl_of_slType2 h51 hV2 hF5 hE hSL hR hRE
    · exact exists_goodEl_of_symType hSym hcard (hsyl E hE _ hR hRE)
  obtain ⟨z, hz3, hzgen, hgen, hrank⟩ := exists_gen_of_good h51 hV2 hF5 hsyl hXT hTX hX₀ hXgen hgood
  have hdeq := autI_thompsonJ_eq_genD hV hmin hmp hF hred hJ
  have hKD : autI hV (twoResidual H) ≤ genD (autI hV H) :=
    hdeq ▸ autI_mono hV (E2.twoResidual_le_thompsonJ hmin hred hJ)
  have hzP : z ∈ autI hV H := by
    have := hF5.sup_eq ▸ (le_sup_left : genD (autI hV H) ≤ genD (autI hV H) ⊔ autI hV T)
    exact this hzgen
  have hzodd : Odd (orderOf z) := by
    have hd : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1 <;> rw [h1] <;> decide
  have hzK : z ∈ autI hV (twoResidual H) := E2.mem_autI_twoResidual_of_odd hzP hzodd
  obtain ⟨g, hgK, hgz⟩ := (mem_autI hV).1 hzK
  refine ⟨(g : G), hgK, ?_, ?_⟩
  · have hc : autI hV (cjSub (g : G) (thompsonJ T)) = conjSub z (autI hV (thompsonJ T)) := by
      rw [← autI_cjSub hV g.2, ← hgz]
      rfl
    rw [hc]
    exact hKD.trans hgen
  · refine hrank (autI hV (twoResidual H)) hKD fun x hx hx3 =>
      E2.mem_autI_twoResidual_of_odd hx ?_
    rw [hx3]
    decide

end CFSG.AGLEmbeddingD2.Tits.E23
