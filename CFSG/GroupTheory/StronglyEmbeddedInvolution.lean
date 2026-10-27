module

public import CFSG.Foundations.Basic

public section

namespace CFSG

variable {G : Type*} [Group G]

theorem strong_embedding_involution_centralizers [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbedded M) {t : G} (htM : t ∈ M) (ht : orderOf t = 2) :
    Subgroup.centralizer {t} ≤ M := by
  intro c hc
  by_contra hcM
  have hodd := hM.2.2 c hcM
  have hct : t * c = c * t := (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
  have htc : t ∈ M ⊓ conjugate M c := by
    refine Subgroup.mem_inf.2 ⟨htM, t, htM, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, hct, inv_mul_cancel_left]
  have hdvd : orderOf (⟨t, htc⟩ : ↥(M ⊓ conjugate M c)) ∣ Nat.card ↥(M ⊓ conjugate M c) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, ht] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

end CFSG
