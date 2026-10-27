module

public import CFSG.FeitThompson.Local.InvariantHallSubgroupsConjugate
public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Local.MaximalInvariantSubgroupTransport
import CFSG.FeitThompson.Local.OvergroupJoinsInvariantPrimeSubgroups
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup

variable {M : Type*} [Group M] {p r : ℕ}

theorem isPiNumber_compl_singleton_iff_not_dvd (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    IsPiNumber ({p}ᶜ : Set ℕ) n ↔ ¬ p ∣ n := by
  rw [isPiNumber_compl_iff]
  refine ⟨fun h hdvd => h p (Nat.mem_primeFactors.2 ⟨hp, hdvd, hn⟩) rfl, fun h q hq hq' => ?_⟩
  rw [Set.mem_singleton_iff] at hq'
  exact h (hq' ▸ Nat.dvd_of_mem_primeFactors hq)

theorem IsHallSubgroup.isHallPiSubgroup {π : Set ℕ} {K : Subgroup M} (hK : IsHallSubgroup π K) :
    IsHallPiSubgroup π K :=
  ⟨hK.isPiSubgroup, isPiNumber_compl_iff.1 hK.index⟩

theorem not_dvd_index_subgroupOf_of_natCard_eq [Finite M] (hr : r.Prime)
    {S K : Subgroup M} (hSK : S ≤ K) (hS : Nat.card S = r ^ (Nat.card K).factorization r) :
    ¬ r ∣ (S.subgroupOf K).index := by
  intro hdvd
  set n := (Nat.card K).factorization r with hn
  have hprod : Nat.card S * (S.subgroupOf K).index = Nat.card K := by
    rw [← natCard_subgroupOf_of_le hSK]; exact Subgroup.card_mul_index _
  have hpow : r ^ (n + 1) ∣ Nat.card K := by
    rw [← hprod, hS, pow_succ]
    exact Nat.mul_dvd_mul_left _ hdvd
  have := (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hpow
  omega

theorem natCard_eq_pow_factorization_of_isPGroup_of_not_dvd_index [Finite M] (hr : r.Prime)
    {S K : Subgroup M} (hSK : S ≤ K) (hS : IsPGroup r S)
    (hidx : ¬ r ∣ (S.subgroupOf K).index) :
    Nat.card S = r ^ (Nat.card K).factorization r := by
  have := Fact.mk hr
  obtain ⟨m, hm⟩ := hS.exists_card_eq
  have hprod : Nat.card S * (S.subgroupOf K).index = Nat.card K := by
    rw [← natCard_subgroupOf_of_le hSK]; exact Subgroup.card_mul_index _
  have hfac : (Nat.card K).factorization r = m := by
    rw [← hprod, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
    simp [hm, Nat.Prime.factorization_pow hr, Nat.factorization_eq_zero_of_not_dvd hidx]
  rw [hm, hfac]

theorem isHallSubgroup_subgroupOf_of_isPGroup_of_not_dvd_index [Finite M] (hr : r.Prime)
    {S K : Subgroup M} (hS : IsPGroup r S)
    (hidx : ¬ r ∣ (S.subgroupOf K).index) : IsHallSubgroup ({r} : Set ℕ) (S.subgroupOf K) where
  natCard := isPiSubgroup_iff_isPiNumber.1
    ((isPiSubgroup_singleton_iff hr _).2 (hS.comap_of_injective _ K.subtype_injective))
  index := (isPiNumber_compl_singleton_iff_not_dvd hr Subgroup.index_ne_zero_of_finite).2 hidx

theorem exists_normal_isHallSubgroup_compl_singleton_ge_commutator [Finite M] [Group.IsSolvable M]
    (hp : p.Prime) (hpM : ¬ p ∣ Nat.card (commutator M)) :
    ∃ K : Subgroup M, K.Normal ∧ IsHallSubgroup ({p}ᶜ : Set ℕ) K ∧ commutator M ≤ K := by
  obtain ⟨K, hK⟩ := exists_isHallSubgroup (X := M) ({p}ᶜ : Set ℕ)
  have hle : commutator M ≤ K :=
    hK.normal_le ((isPiNumber_compl_singleton_iff_not_dvd hp Nat.card_pos.ne').2 hpM)
  exact ⟨K, Subgroup.Normal.of_commutator_le M hle, hK, hle⟩

theorem sup_inf_eq_of_normal_of_sup_eq_top {D H K : Subgroup M} [D.Normal]
    (hDH : D ⊔ H = ⊤) (hDK : D ≤ K) : D ⊔ (K ⊓ H) = K := by
  refine le_antisymm (sup_le hDK inf_le_left) fun k hk => ?_
  have huniv : (D : Set M) * (H : Set M) = Set.univ := by
    rw [← Subgroup.normal_mul D H, hDH]; simp
  obtain ⟨d, hd, h, hh, hdh⟩ := Set.mem_mul.1 (huniv ▸ Set.mem_univ k)
  have hhK : h ∈ K := by
    have hEq : h = d⁻¹ * k := by rw [← hdh]; group
    rw [hEq]; exact K.mul_mem (K.inv_mem (hDK hd)) hk
  rw [← hdh]
  exact Subgroup.mul_mem_sup hd (Subgroup.mem_inf.2 ⟨hhK, hh⟩)

theorem factorization_natCard_eq_of_sup_eq [Finite M] {D V K : Subgroup M} [D.Normal]
    (hDV : D ⊔ V = K) (hr : ¬ r ∣ Nat.card D) :
    (Nat.card V).factorization r = (Nat.card K).factorization r := by
  have hset : Nat.card ((D : Set M) * (V : Set M)) = Nat.card K := by
    rw [← Subgroup.normal_mul D V, hDV]
    simp
  have hkey : Nat.card K * Nat.card (D ⊓ V : Subgroup M) = Nat.card D * Nat.card V := by
    rw [← hset]; exact natCard_mul_mul_natCard_inf D V
  have hDinf : ¬ r ∣ Nat.card (D ⊓ V : Subgroup M) := fun h =>
    hr (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have h2 := congrArg (fun n : ℕ => n.factorization r) hkey
  simp only [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hDinf, Nat.factorization_eq_zero_of_not_dvd hr] at h2
  omega

theorem conj_inv_smul_le_centralizer {P R : Subgroup M} {c : M}
    (hc : c ∈ centralizer (P : Set M)) (hR : R ≤ centralizer (P : Set M)) :
    MulAut.conj c⁻¹ • R ≤ centralizer (P : Set M) := by
  intro y hy
  have hy' : c * y * c⁻¹ ∈ R := by
    have h := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.1 hy
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using h
  have hz := hR hy'
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hC1 : Commute g c := Subgroup.mem_centralizer_iff.1 hc g hg
  have hC2 : Commute g (c * y * c⁻¹) := Subgroup.mem_centralizer_iff.1 hz g hg
  have hy2 : y = c⁻¹ * (c * y * c⁻¹) * c := by group
  rw [hy2]
  exact ((hC1.inv_right.mul_right hC2).mul_right hC1).eq

theorem exists_le_inf_centralizer_natCard_eq [Finite M] [Group.IsSolvable M]
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {P D H : Subgroup M} (hP : Nat.card P = p) [D.Normal] (hDM : D ≤ commutator M)
    (hPH : P ≤ normalizer (H : Set M)) (hDH : D ⊔ H = ⊤)
    (hpM : ¬ p ∣ Nat.card (commutator M)) (hrD : ¬ r ∣ Nat.card D)
    (hrC : r ∣ Nat.card (centralizer (P : Set M))) :
    ∃ R : Subgroup M, R ≤ centralizer (P : Set M) ⊓ H ∧ Nat.card R = r := by
  have := Fact.mk hr
  obtain ⟨K, hKn, hKHall, hMK⟩ :=
    exists_normal_isHallSubgroup_compl_singleton_ge_commutator hp hpM
  have : K.Normal := hKn
  have hpK : ¬ p ∣ Nat.card K :=
    (isPiNumber_compl_singleton_iff_not_dvd hp Nat.card_pos.ne').1 hKHall.natCard
  have hDK : D ≤ K := hDM.trans hMK
  set V : Subgroup M := K ⊓ H with hV
  have hDV : D ⊔ V = K := sup_inf_eq_of_normal_of_sup_eq_top hDH hDK
  have hVK : V ≤ K := inf_le_left
  have hVH : V ≤ H := inf_le_right
  have hfac : (Nat.card V).factorization r = (Nat.card K).factorization r :=
    factorization_natCard_eq_of_sup_eq hDV hrD
  have hcopK : (Nat.card K).Coprime (Nat.card P) := by
    rw [hP]; exact (hp.coprime_iff_not_dvd.2 hpK).symm
  have hcopV : (Nat.card V).Coprime (Nat.card P) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hVK) hcopK
  have hsolvK : Group.IsSolvable (K ⊔ P : Subgroup M) := inferInstance
  have hsolvV : Group.IsSolvable (V ⊔ P : Subgroup M) := inferInstance
  have hPK : P ≤ normalizer (K : Set M) := Subgroup.le_normalizer_of_normal
  have hPV : P ≤ normalizer (V : Set M) :=
    le_trans (le_inf hPK hPH) Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨S, hSV, hSr, -, hPS, hSidx⟩ :=
    exists_isPGroup_ge_le_normalizer_not_dvd_index (D := V) (P := P) (Q := ⊥)
      hsolvV hPV hcopV hr bot_le Subgroup.le_normalizer_of_normal IsPGroup.of_bot
  have hScard : Nat.card S = r ^ (Nat.card K).factorization r := by
    rw [natCard_eq_pow_factorization_of_isPGroup_of_not_dvd_index hr hSV hSr hSidx, hfac]
  have hSK : S ≤ K := hSV.trans hVK
  have hSHall : IsHallSubgroup ({r} : Set ℕ) (S.subgroupOf K) :=
    isHallSubgroup_subgroupOf_of_isPGroup_of_not_dvd_index hr hSr
      (not_dvd_index_subgroupOf_of_natCard_eq hr hSK hScard)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (centralizer (P : Set M))) r hrC
  set R₀ : Subgroup M := Subgroup.zpowers ((x : M)) with hR₀
  have hR₀card : Nat.card R₀ = r := by rw [hR₀, Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hR₀C : R₀ ≤ centralizer (P : Set M) := by rw [hR₀, Subgroup.zpowers_le]; exact x.2
  have hR₀r : IsPGroup r R₀ := IsPGroup.of_card (n := 1) (by rw [hR₀card, pow_one])
  have hR₀K : R₀ ≤ K := by
    refine hKHall.isHallPiSubgroup.le_of_isPiSubgroup (isPiSubgroup_iff.2 fun q hq => ?_)
    rw [hR₀card] at hq
    have hqr : q = r :=
      (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hq) hr).1
        (Nat.dvd_of_mem_primeFactors hq)
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, hqr]
    exact fun h => hpr h.symm
  have hPR₀ : P ≤ normalizer (R₀ : Set M) :=
    (Subgroup.le_centralizer_iff.1 hR₀C).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨T, hTK, hTr, hR₀T, hPT, hTidx⟩ :=
    exists_isPGroup_ge_le_normalizer_not_dvd_index (D := K) (P := P) (Q := R₀)
      hsolvK hPK hcopK hr hR₀K hPR₀ hR₀r
  have hTHall : IsHallSubgroup ({r} : Set ℕ) (T.subgroupOf K) :=
    isHallSubgroup_subgroupOf_of_isPGroup_of_not_dvd_index hr hTr hTidx
  obtain ⟨c, hc, hcTS⟩ := exists_mem_inf_centralizer_conj_inv_smul_eq_of_le_normalizer
    hsolvK hPK hcopK hTK hSK hTHall hSHall hPT hPS
  rw [Subgroup.mem_inf] at hc
  obtain ⟨-, hcC⟩ := hc
  refine ⟨MulAut.conj c⁻¹ • R₀, le_inf (conj_inv_smul_le_centralizer hcC hR₀C) ?_, ?_⟩
  · exact le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hR₀T)
      (hcTS.le.trans (hSV.trans hVH))
  · rw [natCard_conj_smul, hR₀card]

theorem exists_natCard_eq_and_forall_mem_and_mul_comm [Finite M] [Group.IsSolvable M]
    (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    {P D H : Subgroup M} (hP : Nat.card P = p) [D.Normal] (hDM : D ≤ commutator M)
    (hPH : P ≤ normalizer (H : Set M)) (hDH : (D : Set M) * (H : Set M) = Set.univ)
    (hpM : ¬ p ∣ Nat.card (commutator M)) (hrD : ¬ r ∣ Nat.card D)
    (hrC : r ∣ Nat.card (centralizer (P : Set M))) :
    ∃ R : Subgroup M, Nat.card R = r ∧ ∀ y ∈ R, y ∈ H ∧ ∀ g ∈ P, y * g = g * y := by
  obtain ⟨R, hRle, hRcard⟩ := exists_le_inf_centralizer_natCard_eq hp hr hpr hP hDM hPH
    (sup_eq_top_iff_coe_mul_coe_eq_univ.2 hDH) hpM hrD hrC
  refine ⟨R, hRcard, fun y hy => ?_⟩
  obtain ⟨hyC, hyH⟩ := Subgroup.mem_inf.1 (hRle hy)
  exact ⟨hyH, fun g hg => (Subgroup.mem_centralizer_iff.1 hyC g hg).symm⟩

end CFSG.FeitThompson

end
