module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Simple

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.GH74.GLS

@[expose] def McLLyCenterFree : Prop :=
  ∀ (Q : Type) [Group Q], (Nonempty (Q ≃* Blueprint.NativeSporadic.McL) ∨
    Nonempty (Q ≃* Blueprint.NativeSporadic.Ly)) → center Q = ⊥

theorem eq_top_of_normal_of_involution {Q : Type} [Group Q] [Finite Q] (hQ : IsTwoGenQuasi Q)
    (hZ : center (Q ⧸ pPrimeCore 2 Q) = ⊥) {A : Subgroup Q} [A.Normal] {s : Q} (hs : s ∈ A)
    (hs2 : orderOf s = 2) : A = ⊤ := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card (pPrimeCore 2 Q)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  let π : Q →* Q ⧸ pPrimeCore 2 Q := QuotientGroup.mk' (pPrimeCore 2 Q)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hĀ : (A.map π).Normal := Subgroup.Normal.map ‹_› π hπs
  rcases LocalCores.quasisimple_normal_subgroups hQ.2 hĀ with htop | hcen
  · have h1 : A ⊔ pPrimeCore 2 Q = ⊤ := by
      have := Subgroup.comap_map_eq π A
      rw [htop, Subgroup.comap_top] at this
      have hker : π.ker = pPrimeCore 2 Q := QuotientGroup.ker_mk' _
      rw [hker] at this
      exact this.symm
    have htopres : primeResidual 2 ↥(⊤ : Subgroup Q) = ⊤ :=
      (IsTwoGenQuasi.congr (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).symm hQ).1
    exact top_le_iff.1 (le_of_le_sup_odd_of_primeResidual hOodd htopres h1.ge)
  · exfalso
    have hmem : π s ∈ A.map π := Subgroup.mem_map_of_mem π hs
    have h1 : π s = 1 := Subgroup.mem_bot.mp (hZ ▸ hcen hmem)
    have h2 : s ∈ pPrimeCore 2 Q := (QuotientGroup.eq_one_iff s).1 h1
    have h3 := Subgroup.orderOf_dvd_natCard _ h2
    rw [hs2] at h3
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h3)

section Broad

variable {X : Type} [Group X] [Finite X]

theorem IsMLIntr.exists_involution_mem {t : X} {M : Subgroup X} (h : IsMLIntr X t M) :
    ∃ s ∈ M, orderOf s = 2 ∧ ∃ J : Subgroup X, IsAhatIntr X s J := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := isTwoGenQuasi_of_isMLIntr h
  have hnt : Nontrivial ↥M := by
    by_contra hnot
    rw [not_nontrivial_iff_subsingleton] at hnot
    obtain ⟨a, b, hab⟩ := hq.2.2.2
    exact hab (Subsingleton.elim (a * b) (b * a))
  have hdvd : 2 ∣ Nat.card ↥M := by
    by_contra hnd
    have hcop : Nat.Coprime 2 (Nat.card ↥M) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hnd
    have h1 := primeResidual_eq_bot_of_coprime_card (G := ↥M) 2 hcop
    rw [hq.1] at h1
    exact top_ne_bot h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hx2 : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨J, hJ, -⟩ := h.2.2.2 (x : X) x.2 hx2
  exact ⟨x, x.2, hx2, J, hJ⟩

theorem SolMinCEx.exists_isAhatIntr_witness (hcf : McLLyCenterFree) (h : SolMinCEx X) :
    ∃ (t : X) (L : Subgroup X), orderOf t = 2 ∧ IsAhatIntr X t L ∧ ¬ L ≤ KProd X := by
  obtain ⟨t, L, ht, hL | hM, hnot⟩ := h.witness
  · exact ⟨t, L, ht, hL, hnot⟩
  · obtain ⟨s, hsM, hs2, J, hJ⟩ := hM.exists_involution_mem
    refine ⟨s, J, hs2, hJ, fun hJK => hnot ?_⟩
    have hsK : s ∈ KProd X := hJK hJ.2.1
    have hq := isTwoGenQuasi_of_isMLIntr hM
    have hZ : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥ := hcf _ hM.2.2.1
    have hA : (KProd X).subgroupOf L = ⊤ := by
      have : ((KProd X).subgroupOf L).Normal := (KProd.normal X).subgroupOf L
      refine eq_top_of_normal_of_involution hq hZ (s := ⟨s, hsM⟩) hsK ?_
      rw [Subgroup.orderOf_mk]
      exact hs2
    intro x hx
    have : (⟨x, hx⟩ : ↥L) ∈ (KProd X).subgroupOf L := by rw [hA]; exact Subgroup.mem_top _
    exact this

end Broad

theorem solLemma31_of_centerFree (hcf : McLLyCenterFree) : SolLemma31 := by
  intro X _ _ h
  obtain ⟨t, L, ht, hL, hnot⟩ := h.exists_isAhatIntr_witness hcf
  exact h.isSimpleGroup_of_isAhatIntr ht hL hnot

end CFSG.OddStandard.Solomon75
