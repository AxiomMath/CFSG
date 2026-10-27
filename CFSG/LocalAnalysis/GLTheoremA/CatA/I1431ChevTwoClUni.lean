module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadRk
public import CFSG.RankThree.PartOne.FOC.PSUModel
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBadCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (exists_suHom_to_cover rkY_false_su)

theorem false_of_twistedA_high (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] (hRk : CFSG.HardMathSupport.Dickson.Sec6.I1431.RkY Y)
    {n : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA n q).Valid)
    (hq : q.card = 2) (hn : 6 ≤ n)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group) : False := by
  obtain ⟨hp, hf⟩ := cl_primePower_card_two hq
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hv e
  rw [hp, hf] at hC
  obtain ⟨K, _, _, h, -, -, ⟨e0⟩⟩ := CFSG.RankThree.PartOne.FOC.exists_psu_model hC
  have hdvd : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have h2 : ¬(n + 1 = 6 ∧ 2 = 2 ∧ 1 = 1) := fun ⟨ha, _, _⟩ => by omega
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 := exists_prime_orderOf_dvd_card' 3 h3K
  obtain ⟨ρ, hρ⟩ := exists_suHom_to_cover hGA h hC e0 (by omega) h2
    (QuotientGroup.mk' (Subgroup.center Y)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le
  refine rkY_false_su hRk h (by omega) hdvd (Or.inr (by omega)) hζ ρ
    (QuotientGroup.mk' (Subgroup.center Y))
    (e0.symm.toMonoidHom.comp
      (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K (n + 1))) (n + 1)))) hρ
    (fun y hy => (QuotientGroup.eq_one_iff y).2 hy) ?_
  intro g hg
  have hg' : e0.symm (QuotientGroup.mk'
      (normOneScalars h (gramSU h (idGram K (n + 1))) (n + 1)) g) = 1 := hg
  rw [map_eq_one_iff _ e0.symm.injective] at hg'
  exact (QuotientGroup.eq_one_iff g).1 hg'

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
