module

public import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.BenderSuzuki Matrix

theorem finite_of_isBenderGroup {K : Type*} [Group K] (hK : IsBenderGroup K) : Finite K := by
  rcases hK with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv
  · have : Finite (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
      Finite.of_surjective
        (ProjGenLinGroup.mk : GL (Fin 3) (GaloisField 2 (2 * n)) →* _)
        (QuotientGroup.mk'_surjective _)
    exact Finite.of_equiv _ e.symm.toEquiv

theorem isBenderGroup_of_mulEquiv_sz {K : Type*} [Group K] {a : ℕ} (ha : 1 ≤ a)
    (e : K ≃* CFSG.Open.Sz a) : IsBenderGroup K := by
  have hmodel : SzModel a = CFSG.Open.Sz a := CFSG.Models.benderSzModel_eq_sz a
  exact .isSuzuki a ha (e.trans (MulEquiv.subgroupCongr hmodel.symm))

theorem isBenderGroup_of_mulEquiv_psl2 {K : Type*} [Group K] {f : ℕ} (hf : 2 ≤ f)
    (e : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
    IsBenderGroup K :=
  .isPSL2 f hf e

section Sylow

variable {K : Type*} [Group K]

theorem mem_of_isStronglyEmbeddedOrder_of_commute {M : Subgroup K}
    (hM : IsStronglyEmbeddedOrder M) {s : K} (hsM : s ∈ M) (hs : s * s = 1) (hs1 : s ≠ 1)
    {g : K} (hg : g * s * g⁻¹ = s) : g ∈ M := by
  by_contra hgM
  have hodd := hM.2.2 g hgM
  have hmem : s ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom :=
    ⟨hsM, ⟨s, hsM, by simp [MulAut.conj_apply, hg]⟩⟩
  have hdvd : orderOf (⟨s, hmem⟩ : ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) ∣
      Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom) := orderOf_dvd_natCard _
  have hord : orderOf (⟨s, hmem⟩ : ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hs) hs1
  rw [hord] at hdvd
  obtain ⟨m, hm⟩ := hodd
  omega

theorem le_of_isPGroup_of_le_normalizer {P : Subgroup K} (hP : IsPGroup 2 P) (Q : Sylow 2 K)
    (hPN : P ≤ Subgroup.normalizer (Q : Set K)) : P ≤ (Q : Subgroup K) := by
  have h := hP.inf_normalizer_sylow Q
  rw [inf_eq_left.2 hPN] at h
  exact inf_eq_left.1 h.symm

variable [Finite K]

theorem centralizer_le_normalizer_of_isBenderGroup (hK : IsBenderGroup K) (Q : Sylow 2 K) {s : K}
    (hsQ : s ∈ Q) (hs : s * s = 1) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set K) ≤ Subgroup.normalizer (Q : Set K) := by
  intro g hg
  have hcomm : s * g = g * s := Subgroup.mem_centralizer_iff.1 hg s (Set.mem_singleton s)
  exact mem_of_isStronglyEmbeddedOrder_of_commute
    (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK Q)
    (Subgroup.le_normalizer (show s ∈ (Q : Subgroup K) from hsQ)) hs hs1
    (by rw [← hcomm]; group)

end Sylow

end CFSG.CGT.Timmesfeld75
