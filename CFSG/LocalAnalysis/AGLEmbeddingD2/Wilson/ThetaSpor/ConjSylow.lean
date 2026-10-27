module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AschbacherCoreTransport

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

theorem exists_conj_mem_of_orderOf_prime_sylow {G : Type*} [Group G] [Finite G] (p n : ℕ)
    [hp : Fact p.Prime] (Q : Subgroup G) (hQ : Nat.card Q = p ^ n)
    (hG : ¬ p ^ (n + 1) ∣ Nat.card G) {g : G} (hg : orderOf g = p) :
    ∃ h : G, h⁻¹ * g * h ∈ Q := by
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card G).factorization p = n := by
    have h3 : p ^ n ∣ Nat.card G := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    have a := (Nat.Prime.pow_dvd_iff_le_factorization hp.out hGne).mp h3
    have b : ¬ n + 1 ≤ (Nat.card G).factorization p := fun h =>
      hG ((Nat.Prime.pow_dvd_iff_le_factorization hp.out hGne).mpr h)
    omega
  let P₀ : Sylow p G := Sylow.ofCard Q (by rw [hQ, hfac])
  have hpg : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg]; simp)
  obtain ⟨P', hP'⟩ := hpg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P₀ P'
  refine ⟨h, ?_⟩
  have hgP' : g ∈ (P' : Subgroup G) := hP' (Subgroup.mem_zpowers g)
  have : (P' : Subgroup G) = (h • P₀ : Sylow p G) := by rw [hh]
  rw [this, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgP'
  exact hgP'

theorem aschbacherSolvableCore_three_centralizer_eq_bot_of_conj {X : Type*} [Group X] [Finite X]
    (g b b' : X) (h : g * b * g⁻¹ = b')
    (h' : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      (Subgroup.centralizer ({b'} : Set X)) = ⊥) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      (Subgroup.centralizer ({b} : Set X)) = ⊥ := by
  let e : X ≃* X := MulAut.conj g
  have heb : e b = b' := by rw [← h]; rfl
  let ψ : Subgroup.centralizer ({b} : Set X) ≃* Subgroup.centralizer ({e b} : Set X) :=
    (e.subgroupMap (Subgroup.centralizer ({b} : Set X))).trans
      (MulEquiv.subgroupCongr (CFSG.AGLEmbeddingD2.Wilson.Proving.map_centralizer_singleton_eq e b))
  have hnat := CFSG.AGLEmbeddingD2.Wilson.Proving.aschbacherSolvableCore_map_mulEquiv
    (H := Subgroup.centralizer ({b} : Set X)) (K := Subgroup.centralizer ({e b} : Set X))
    Nat.prime_three ψ
  have h'' : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
      (Subgroup.centralizer ({e b} : Set X)) = ⊥ := by rw [heb]; exact h'
  rw [h''] at hnat
  exact (Subgroup.map_eq_bot_iff_of_injective (f := ψ.toMonoidHom) _ ψ.injective).1 hnat.symm

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor
