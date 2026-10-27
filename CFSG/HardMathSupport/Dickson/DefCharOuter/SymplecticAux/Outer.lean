module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympField

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.SymplecticAux

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Open (StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem perfectInLayer_sp_outer {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : 2 ≤ r)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut (StatedProj (StatedSp r K))} (hβ : β ^ p = 1)
    (hout : ∀ a : StatedProj (StatedSp r K), MulAut.conj a ≠ β) : PerfectInLayer β := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have hodd : Odd (orderOf β) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ)
  have hE : β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : β ∈ spLinearAutGroup r K
  ·
    exfalso
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    obtain ⟨t, ht⟩ := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two
      hrel hp hp2 hD hβ
    exact hout t ht
  ·
    have hne1 : β ≠ 1 := fun h => hD (h ▸ one_mem _)
    have hord : orderOf β = p := orderOf_eq_prime hβ hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp β hE hD hord
    rw [hβeq]
    exact LieSemisimple.perfectInLayer_conj h _
      (LieSemisimple.perfectInLayer_fieldAut_sp hr hp hp2 σ
        (by rw [← hσ]; exact pow_orderOf_eq_one σ))

private theorem not_namesTag_psp (d : TauCeti.LieTypeIndex) (p f : ℕ) :
    ¬ CFSG.Models.NamesTag d .PSp p f := by
  cases d <;> exact id

theorem perfectInLayer_of_lieModel_psp {S : Type} [Group S] {r ℓ f : ℕ} (hr : 2 ≤ r)
    (hS : CFSG.Models.LieModel S .PSp r ℓ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  obtain ⟨hadm, hcl⟩ := hS
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl.resolve_right fun ⟨_, d, hd, _⟩ =>
    not_namesTag_psp d.1 ℓ f hd
  refine LieSemisimple.perfectInLayer_of_congr e β ?_
  refine perfectInLayer_sp_outer hadm.1 hadm.2.1 hr hK hp hp2 ?_ ?_
  · rw [← map_pow, hβ, map_one]
  · intro a ha
    apply hout (e.symm a)
    apply (MulAut.congr e).injective
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply]
    exact ha

end CFSG.HardMathSupport.Dickson.DefCharOuter.SymplecticAux
