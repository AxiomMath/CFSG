module

public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinResidual

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.I414

open CFSG CFSG.LocalCores
open CFSG.ComponentClassification.CatalogueBPrimeJoin
  (primeResidual primeResidual_le_normal_of_coprime_index)

theorem not_dvd_card_of_forall {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ g : G, ∃ m : ℕ, ¬ p ∣ m ∧ g ^ m = 1) : ¬ p ∣ Nat.card G := by
  intro hd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨m, hm, hgm⟩ := h g
  exact hm (hg ▸ orderOf_dvd_of_pow_eq_one hgm)

theorem coprime_index_of_forall_quotient {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (M : Subgroup K) [M.Normal] (h : ∀ g : K ⧸ M, ∃ m : ℕ, ¬ p ∣ m ∧ g ^ m = 1) :
    p.Coprime M.index :=
  (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (not_dvd_card_of_forall h)

theorem coprime_index_of_sup_eq_top {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (M O : Subgroup K) [M.Normal] [O.Normal] (hsup : M ⊔ O = ⊤)
    (hO : p.Coprime (Nat.card O)) : p.Coprime M.index := by
  refine coprime_index_of_forall_quotient M fun g => ?_
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  have hk : k ∈ O ⊔ M := by rw [sup_comm, hsup]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
  refine ⟨Nat.card O, (Fact.out : p.Prime).coprime_iff_not_dvd.mp hO, ?_⟩
  have h1 : ((y * z : K) : K ⧸ M) = (y : K ⧸ M) := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one]
  have h2 : y ^ Nat.card O = 1 := by
    have := pow_card_eq_one' (G := O) (x := ⟨y, hy⟩)
    exact congrArg Subtype.val this
  rw [h1, ← QuotientGroup.mk_pow, h2]
  rfl

theorem eq_top_of_coprime_index {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hgen : primeResidual p K = ⊤) (N : Subgroup K) [N.Normal] (hN : p.Coprime N.index) :
    N = ⊤ :=
  top_le_iff.mp (hgen ▸ primeResidual_le_normal_of_coprime_index p N hN)

theorem pPrimeCore_le_pPrimePCore (p : ℕ) (K : Type*) [Group K] :
    pPrimeCore p K ≤ pPrimePCore p K := by
  intro x hx
  change QuotientGroup.mk' (pPrimeCore p K) x ∈ pCore p (K ⧸ pPrimeCore p K)
  rw [show QuotientGroup.mk' (pPrimeCore p K) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

theorem normal_le_pPrimePCore {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hgen : primeResidual p K = ⊤) (hqs : IsQuasisimple (K ⧸ pPrimeCore p K))
    {M : Subgroup K} [M.Normal] (hM : M ≠ ⊤) : M ≤ pPrimePCore p K := by
  have hOn : (pPrimeCore p K).Normal := pPrimeCore_normal (p := p) (G := K)
  have hMn : (M.map (QuotientGroup.mk' (pPrimeCore p K))).Normal :=
    Subgroup.Normal.map ‹M.Normal› _ (QuotientGroup.mk'_surjective _)
  rcases quasisimple_normal_subgroups hqs hMn with h | h
  · exfalso
    apply hM
    have hsup : M ⊔ pPrimeCore p K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (pPrimeCore p K)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    exact eq_top_of_coprime_index hgen M
      (coprime_index_of_sup_eq_top M (pPrimeCore p K) hsup pPrimeCore_coprime_card)
  · intro x hx
    change QuotientGroup.mk' (pPrimeCore p K) x ∈ pCore p (K ⧸ pPrimeCore p K)
    have hbot : pPrimeCore p (K ⧸ pPrimeCore p K) = ⊥ :=
      pPrimeCore_quotient_eq_bot (Fact.out : p.Prime)
    have hfit := Fitting_eq_pcore (K ⧸ pPrimeCore p K) p hbot
    have hcen : Subgroup.center (K ⧸ pPrimeCore p K) ≤ fittingSubgroup (K ⧸ pPrimeCore p K) :=
      fitting_characteristic.2.2 _ inferInstance inferInstance
    rw [← hfit]
    exact hcen (h (Subgroup.mem_map_of_mem _ hx))

theorem pPrimePCore_ne_top {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hqs : IsQuasisimple (K ⧸ pPrimeCore p K)) : pPrimePCore p K ≠ ⊤ := by
  intro htop
  have hall : pCore p (K ⧸ pPrimeCore p K) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have : k ∈ pPrimePCore p K := by rw [htop]; trivial
    exact this
  have hp : IsPGroup p (K ⧸ pPrimeCore p K) := by
    have h2 := pCore_isPGroup (p := p) (G := K ⧸ pPrimeCore p K)
    rw [hall] at h2
    exact h2.of_equiv Subgroup.topEquiv
  have : Group.IsNilpotent (K ⧸ pPrimeCore p K) := hp.isNilpotent
  have : Group.IsPerfect (K ⧸ pPrimeCore p K) := hqs.1
  have : Nontrivial (K ⧸ pPrimeCore p K) := isQuasisimple_nontrivial hqs
  exact Group.IsPerfect.not_isSolvable (K ⧸ pPrimeCore p K) inferInstance

end CFSG.GH74.GLS.Stage2.Final.Thm6.I414
