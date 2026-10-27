module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem frattini_elementary_quotient_kernel {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] :
    (∀ (N : Subgroup G) [N.Normal], IsElementaryAbelian p (G ⧸ N) → frattini G ≤ N) ∧
      ∀ {A : Type*} [Group A], IsElementaryAbelian p A → ∀ f : G →* A, frattini G ≤ f.ker := by
  refine ⟨fun N _ hN => ?_, fun {A} _ hA f => ?_⟩
  · exact CFSG.SectionRank.Ccomm.frattini_le_of_quotient_elementary N
      (fun a b => hN.is_comm.comm a b)
      (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hN.exponent_dvd_p a)
  · exact CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary f
      (fun a b => hA.is_comm.comm a b)
      (fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p a)

end CFSG.GroupTheory.SteinbergBK
