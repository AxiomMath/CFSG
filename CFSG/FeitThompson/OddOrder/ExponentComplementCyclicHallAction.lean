module

public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Foundations.SolvableHallExistence

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise

variable {M : Type*} [Group M]

theorem mem_inf_centralizer_set_iff {H : Subgroup M} {S : Set M} {h : M} :
    h ∈ H ⊓ Subgroup.centralizer S ↔ h ∈ H ∧ ∀ x ∈ S, h * x = x * h := by
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact and_congr_right fun _ => ⟨fun hc x hx => (hc x hx).symm, fun hc x hx => (hc x hx).symm⟩

theorem centralizer_conj_smul (g : M) (K : Subgroup M) :
    Subgroup.centralizer ((MulAut.conj g • K : Subgroup M) : Set M)
      = MulAut.conj g • Subgroup.centralizer (K : Set M) := by
  ext x
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · intro h
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj]; group⟩
    intro k hk
    have hx := h (g * k * g⁻¹) ((Subgroup.mem_smul_pointwise_iff_exists _ _ _).2
      ⟨k, hk, by simp [MulAut.conj]⟩)
    calc k * (g⁻¹ * x * g) = g⁻¹ * ((g * k * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * k * g⁻¹)) * g := by rw [hx]
      _ = (g⁻¹ * x * g) * k := by group
  · rintro ⟨y, hy, rfl⟩ k hk
    obtain ⟨k', hk', rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hk
    have hy' := Subgroup.mem_centralizer_iff.1 hy k' hk'
    simp only [MulAut.smul_def, MulAut.conj_apply]
    calc (g * k' * g⁻¹) * (g * y * g⁻¹) = g * (k' * y) * g⁻¹ := by group
      _ = g * (y * k') * g⁻¹ := by rw [hy']
      _ = (g * y * g⁻¹) * (g * k' * g⁻¹) := by group

theorem isPiNumber_primeFactors (n : ℕ) : IsPiNumber ((n.primeFactors : Set ℕ)) n :=
  isPiNumber_iff.2 fun _ hp => Finset.mem_coe.2 hp

theorem isPiNumber_compl_primeFactors_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    IsPiNumber ((m.primeFactors : Set ℕ))ᶜ n :=
  isPiNumber_compl_iff.2 fun _p hp hpm =>
    (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
      (Nat.Coprime.eq_one_of_dvd
        (h.coprime_dvd_left (Nat.dvd_of_mem_primeFactors (Finset.mem_coe.1 hpm)))
        (Nat.dvd_of_mem_primeFactors hp))

theorem isHallSubgroup_primeFactors_natCard {K : Subgroup M}
    (hK : (Nat.card ↥K).Coprime K.index) :
    IsHallSubgroup ((Nat.card ↥K).primeFactors : Set ℕ) K :=
  ⟨isPiNumber_primeFactors _, isPiNumber_compl_primeFactors_of_coprime hK⟩

theorem natCard_dvd_exponent_of_sup_eq_top [Finite M] {H E K : Subgroup M} [H.Normal]
    [IsCyclic ↥K] (hsup : H ⊔ E = ⊤) (hHK : H ⊓ K = ⊥) :
    Nat.card ↥K ∣ Monoid.exponent ↥E := by
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := ↥K)
  have hkord : orderOf ((k : M)) = Nat.card ↥K := by
    rw [Subgroup.orderOf_coe]; exact orderOf_eq_card_of_forall_mem_zpowers hk
  have hmem : (k : M) ∈ (H : Set M) * (E : Set M) := by
    rw [← Subgroup.normal_mul H E, hsup]; trivial
  obtain ⟨h, hh, e, he, hke⟩ := Set.mem_mul.1 hmem
  set q : M ⧸ H := QuotientGroup.mk (k : M) with hq
  have h1 : Nat.card ↥K ∣ orderOf q := by
    rw [← hkord]
    refine orderOf_dvd_of_pow_eq_one ?_
    have hmemHK : (k : M) ^ orderOf q ∈ H ⊓ K :=
      Subgroup.mem_inf.2 ⟨by
        have h2 : (q : M ⧸ H) ^ orderOf q = 1 := pow_orderOf_eq_one _
        rwa [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2, K.pow_mem k.2 _⟩
    rw [hHK, Subgroup.mem_bot] at hmemHK
    exact hmemHK
  refine h1.trans ?_
  have hqe : q = QuotientGroup.mk e := by
    rw [hq, ← hke, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h).2 hh, one_mul]
  rw [hqe]
  refine dvd_trans ?_ (Monoid.order_dvd_exponent (⟨e, he⟩ : ↥E))
  have h3 : orderOf (QuotientGroup.mk e : M ⧸ H) ∣ orderOf e :=
    orderOf_map_dvd (QuotientGroup.mk' H) e
  rwa [← Subgroup.orderOf_mk (H := E) e he] at h3

theorem exists_conj_smul_eq_of_natCard_eq_of_exponent_eq [Finite M] [Group.IsSolvable M]
    {H E E₀ K : Subgroup M} [H.Normal] [IsCyclic ↥K]
    (hsup : H ⊔ E = ⊤) (hHK : H ⊓ K = ⊥)
    (hexp : Monoid.exponent ↥E₀ = Monoid.exponent ↥E)
    (hKindex : (Nat.card ↥K).Coprime K.index) :
    ∃ K₁ : Subgroup M, K₁ ≤ E₀ ∧ Nat.card ↥K₁ = Nat.card ↥K ∧
      ∃ g : M, MulAut.conj g • K₁ = K := by
  set π : Set ℕ := ((Nat.card ↥K).primeFactors : Set ℕ)
  have hKpi : IsPiNumber π (Nat.card ↥K) := isPiNumber_primeFactors _
  have hKidx : IsPiNumber πᶜ K.index := isPiNumber_compl_primeFactors_of_coprime hKindex
  have hdvdE₀ : Nat.card ↥K ∣ Nat.card ↥E₀ :=
    ((hexp ▸ natCard_dvd_exponent_of_sup_eq_top hsup hHK)).trans Group.exponent_dvd_nat_card
  obtain ⟨K₀, hK₀⟩ := exists_isHallSubgroup (X := ↥E₀) π
  have hcard₁ : Nat.card ↥(K₀.map E₀.subtype) = Nat.card ↥K₀ :=
    Subgroup.card_map_of_injective E₀.subtype_injective
  have hcardeq : Nat.card ↥(K₀.map E₀.subtype) = Nat.card ↥K := by
    refine hcard₁.trans (Nat.dvd_antisymm ?_ ?_)
    · refine Nat.Coprime.dvd_of_dvd_mul_right
        (hK₀.natCard.coprime_of_compl hKidx Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite) ?_
      rw [Subgroup.card_mul_index, ← hcard₁]
      exact (K₀.map E₀.subtype).card_subgroup_dvd_card
    · refine Nat.Coprime.dvd_of_dvd_mul_right
        (hKpi.coprime_of_compl hK₀.index Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite) ?_
      rw [Subgroup.card_mul_index]; exact hdvdE₀
  refine ⟨K₀.map E₀.subtype, Subgroup.map_subtype_le K₀, hcardeq, ?_⟩
  have hidx : (K₀.map E₀.subtype).index = K.index := by
    have e1 := Subgroup.card_mul_index (K₀.map E₀.subtype)
    have e2 := Subgroup.card_mul_index K
    rw [hcardeq] at e1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (e1.trans e2.symm)
  exact exists_conj_smul_eq_of_isHallSubgroup ⟨hcardeq ▸ hKpi, hidx ▸ hKidx⟩ ⟨hKpi, hKidx⟩

theorem inf_centralizer_eq_bot_of_exponent_eq [Finite M] [Group.IsSolvable M]
    {H E E₀ K : Subgroup M} [H.Normal] [IsCyclic ↥K]
    (_hHhall : (Nat.card ↥H).Coprime H.index)
    (hsup : H ⊔ E = ⊤) (_hHE : H ⊓ E = ⊥) (_hE₀ : E₀ ≤ E)
    (hexp : Monoid.exponent ↥E₀ = Monoid.exponent ↥E)
    (hfree : ∀ e ∈ E₀, e ≠ 1 → H ⊓ Subgroup.centralizer ({e} : Set M) = ⊥)
    (hKbot : K ≠ ⊥) (hKindex : (Nat.card ↥K).Coprime K.index)
    (hKH : (Nat.card ↥K).Coprime (Nat.card ↥H)) :
    H ⊓ Subgroup.centralizer (K : Set M) = ⊥ := by
  have hHK : H ⊓ K = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard hKH.symm)
  obtain ⟨K₁, hK₁E₀, hK₁card, g, hg⟩ :=
    exists_conj_smul_eq_of_natCard_eq_of_exponent_eq hsup hHK hexp hKindex
  have hK₁bot : K₁ ≠ ⊥ :=
    K₁.one_lt_card_iff_ne_bot.1 (hK₁card ▸ K.one_lt_card_iff_ne_bot.2 hKbot)
  have : Nontrivial ↥K₁ := K₁.nontrivial_iff_ne_bot.2 hK₁bot
  obtain ⟨k₀, hk₀mem, hk₀ne⟩ := K₁.exists_ne_one_of_nontrivial
  have hbot : H ⊓ Subgroup.centralizer (K₁ : Set M) = ⊥ :=
    le_bot_iff.1 <| (inf_le_inf_left H
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hk₀mem))).trans
      (hfree k₀ (hK₁E₀ hk₀mem) hk₀ne).le
  calc H ⊓ Subgroup.centralizer (K : Set M)
      = MulAut.conj g • (H ⊓ Subgroup.centralizer (K₁ : Set M)) := by
        rw [Subgroup.smul_inf, ‹H.Normal›.conj_smul_eq_self g H, ← centralizer_conj_smul, hg]
    _ = ⊥ := by rw [hbot, Subgroup.smul_bot]

theorem eq_one_of_mem_of_forall_commute_of_exponent_eq [Finite M] [Group.IsSolvable M]
    {H E E₀ K : Subgroup M} [H.Normal] [IsCyclic ↥K]
    (hHhall : (Nat.card ↥H).Coprime H.index)
    (hsup : H ⊔ E = ⊤) (hHE : H ⊓ E = ⊥) (hE₀ : E₀ ≤ E)
    (hexp : Monoid.exponent ↥E₀ = Monoid.exponent ↥E)
    (hfree : ∀ e ∈ E₀, e ≠ 1 → H ⊓ Subgroup.centralizer ({e} : Set M) = ⊥)
    (hKbot : K ≠ ⊥) (hKindex : (Nat.card ↥K).Coprime K.index)
    (hKH : (Nat.card ↥K).Coprime (Nat.card ↥H))
    {h : M} (hh : h ∈ H) (hcomm : ∀ x ∈ K, h * x = x * h) : h = 1 := by
  have hb :=
    inf_centralizer_eq_bot_of_exponent_eq hHhall hsup hHE hE₀ hexp hfree hKbot hKindex hKH
  rw [Subgroup.eq_bot_iff_forall] at hb
  exact hb h (mem_inf_centralizer_set_iff.2 ⟨hh, hcomm⟩)

end

end CFSG.FeitThompson
