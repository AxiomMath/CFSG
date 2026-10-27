module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36F

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem claimA_of_centralizer_le [Finite X] {M : Subgroup X} {r : ℕ}
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin r)} (hρ : IsPermAction θ ρ) (hr : 6 ≤ r)
    {H : Subgroup X} (hMH : M ≤ H) (hHN : H ≤ normalizer (M : Set X))
    (hker : ∀ g ∈ H, g ∈ UnbalancedLayer.coreActionKernel M → Odd (orderOf g)) {x₀ : X}
    (hx₀H : x₀ ∈ H) (hx₀2 : x₀ * x₀ = 1) (hx₀4 : (ρ ⟨x₀, hHN hx₀H⟩).support.card = 4)
    (hC : centralizer ({x₀} : Set X) ≤ H) :
    ∀ (x : X) (hx : x ∈ H), x * x = 1 → (ρ ⟨x, hHN hx⟩).support.card = 4 →
      centralizer ({x} : Set X) ≤ H := by
  intro x hx hx2 hx4
  obtain ⟨c, hcH, hc⟩ := hρ.exists_conj_of_four hr hMH hker (hHN hx₀H) (hHN hx) hx₀H hx hx₀2 hx2
    hx₀4 hx4
  have h := centralizer_conj_le hcH hC
  rwa [hc] at h

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem card_support_coreImage_E {x : X} (hxE : x ∈ E) (hx1 : x ≠ 1) :
    (coreImage e (S.le hxE)).support.card = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : (coreImage e (S.le hxE)).support ⊆ D := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (S.supp ⟨x, S.le hxE⟩ hxE ω hωD)
  refine le_antisymm ((Finset.card_le_card hsub).trans S.card.le) ?_
  have hx2 : x * x = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 x hxE
  refine four_le_card_support_of_mem_alternatingGroup (coreImage_mem e (S.le hxE)) ?_ ?_
  · have h1 : (⟨x, S.le hxE⟩ : ↥J) * ⟨x, S.le hxE⟩ = 1 := Subtype.ext hx2
    have h2 : e ((⟨x, S.le hxE⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        e ((⟨x, S.le hxE⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  · intro h
    have h1 : e ((⟨x, S.le hxE⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := Subtype.ext h
    rw [← map_one e] at h1
    have h2 := e.injective h1
    rw [QuotientGroup.eq_one_iff] at h2
    have hodd : Odd (orderOf x) := by
      have h3 := orderOf_dvd_natCard (⟨⟨x, S.le hxE⟩, h2⟩ : ↥(pPrimeCore 2 ↥J))
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h3
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h3 pPrimeCore_coprime_card)
    have h4 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
    · exact hx1 (orderOf_eq_one_iff.mp h5)
    · rw [h5] at hodd
      exact absurd hodd (by decide)

theorem card_support_of_mem_E {M : Subgroup X} {m : ℕ} (htM : t ∈ normalizer (M : Set X))
    (hJM : J ≤ M) (hnm : n < m) (hm6 : m ≠ 6) {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ) {x : X}
    (hxE : x ∈ E) (hx1 : x ≠ 1) :
    (ρ ⟨x, le_normalizer (hJM (S.le hxE))⟩).support.card = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hJN : J ≤ normalizer (M : Set X) := hJM.trans le_normalizer
  have hJC := S.pair.1.2.1
  have hJpc := S.pair.1.2.2.1
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  have hne : ∃ x : ↥J, ρ ⟨x, hJN x.2⟩ ≠ 1 := by
    refine ⟨⟨x, S.le hxE⟩, fun h => ?_⟩
    have h1 := hρ.apply_of_mem (by omega) ⟨x, hJM (S.le hxE)⟩
    have h2 : θ ((⟨x, hJM (S.le hxE)⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) = 1 := by
      apply Subtype.ext
      rw [← h1]
      exact h
    rw [← map_one θ] at h2
    have h3 := θ.injective h2
    rw [QuotientGroup.eq_one_iff] at h3
    have hx2 : x * x = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 x hxE
    have hodd : Odd (orderOf x) := by
      have h4 := orderOf_dvd_natCard (⟨⟨x, hJM (S.le hxE)⟩, h3⟩ : ↥(pPrimeCore 2 ↥M))
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h4
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h4 pPrimeCore_coprime_card)
    have h5 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h5 with h6 | h6
    · exact hx1 (orderOf_eq_one_iff.mp h6)
    · rw [h6] at hodd
      exact absurd hodd (by decide)
  have hpc : IsPComponent 2 (J.subgroupOf (M ⊓ centralizer ({t} : Set X))) :=
    GSThmB.B5a.isPComponent_subgroupOf_of_le (le_inf hJM hJC) inf_le_right hJpc
  obtain ⟨τ, hτk, ψ, hψ⟩ := exists_image_equiv (by omega) hnm.le hm6 θ hρ hJN
    (primeResidual_eq_top_of_isPComponent hJC hJpc)
    (UnbalancedCorr.commutator_eq_of_isPComponent hJC hJpc) (Fintype.card_fin n) e hne
    (Or.inr ⟨t, htM, ht2, hJM, hJC, hpc⟩)
  have h1 := card_support_of_le_fixAlt (by omega) hτk le_rfl (Fintype.card_fin n) (e.symm.trans ψ)
    (e ((⟨x, S.le hxE⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J))
  have h2 : (e.symm.trans ψ) (e ((⟨x, S.le hxE⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) =
      ψ ((⟨x, S.le hxE⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := by
    change ψ (e.symm (e _)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [h2, hψ ⟨x, S.le hxE⟩] at h1
  rw [h1]
  exact S.card_support_coreImage_E hxE hx1

theorem oddCore_le_of_mem_E {x : X} (hxE : x ∈ E) (hx1 : x ≠ 1) :
    (pPrimeCore 2 (centralizer ({x} : Set X))).map (centralizer ({x} : Set X)).subtype ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  have hEx : E ≤ centralizer ({x} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hcomm y hy x hxE)
  have hθ : SolAltLit.thetaFunctor E x ≤ Sol78.signalizerCompletion E E :=
    le_iSup₂_of_le (f := fun (c : X) (_ : c ∈ E) => ⨆ (_ : c ≠ 1), SolAltLit.thetaFunctor E c)
      x hxE (le_iSup_of_le hx1 le_rfl)
  exact oddCore_le_normalizer_of_theta S.isPGroup hEx hθ
    (normalizer_le_normalizer_signalizerCompletion_self E)

end Sig36

end CFSG.ComponentClassification.SolMax
