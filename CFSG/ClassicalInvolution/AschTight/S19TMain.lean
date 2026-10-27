module

public import CFSG.ClassicalInvolution.AschTight.S19TF1
public import CFSG.ClassicalInvolution.AschTight.S19BMain

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]

theorem c19_11b_of' (hFL : FactFL) : C19_11bTmp p f := by
  intro G _ _ _ K z S W L t V hd
  by_contra hne
  have hd0 := hd.toSec19Data
  have hBS : S19B.sec19BPrime K S W L ≤ (S : Subgroup G) := fun x hx => hx.1.1.1
  have hBK : S19B.sec19BPrime K S W L ≤ centralizerModOdd ⊤ K := fun x hx =>
    ((S19B.mem_sec19BPrime_iff hd).mp hx).2.1
  have hsc : fusionStronglyClosed (S19B.sec19BPrime K S W L : Set G) (S : Subgroup G) := by
    intro x hx g hg
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, inv_mul_cancel]
      exact Subgroup.one_mem _
    obtain ⟨d, hdz, hdx⟩ := exists_mem_centralizer_conj_eq' hFL hd hx hx1 (hd0.hSz hg)
    rw [← hdx] at hg ⊢
    have hdz' : d⁻¹ * z = z * d⁻¹ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hdz)
      exact h
    have h := conj_mem_sec19BPrime hd hx hdz' (by rwa [inv_inv])
    rwa [inv_inv] at h
  exact S19B.false_of_stronglyClosed S19B.goldschmidtB1Tmp_holds hd.tight.branch.nonabelian S hBS
    hne hsc hBK
    (S19B.not_isSolvable_quotient_of_isClassicalMember hd.tight.branch.five hd.tight.branch.member)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19T
