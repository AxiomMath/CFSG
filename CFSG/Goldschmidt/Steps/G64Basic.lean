module

public import CFSG.Goldschmidt.Steps.G63Basic
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Goldschmidt.Steps.Balance
public import CFSG.Walter.Bender1970.S1.PCoreRankTwo

public section

namespace CFSG.Goldschmidt.G64

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_qCoreOf_of_mem_fstar {H : Subgroup G} {a : G}
    (ha : a ∈ generalizedFittingSubgroupOf H) (ha2 : a * a = 1) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : a ∈ Subgroup.centralizer (qCoreOf H q : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  set Q := qCoreOf H q with hQdef
  set R := pResidualOf (generalizedFittingSubgroupOf H) q with hRdef
  have hRQ : R ≤ Subgroup.centralizer (Q : Set G) :=
    pResidualOf_generalizedFitting_le_centralizer H hq
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) :=
    (qCoreOf_normal_in H q).1.trans
      (le_normalizer_of_isNormalIn (pResidualOf_generalizedFitting_isNormalIn H q))
  obtain ⟨y, hy, w, hw, rfl⟩ :=
    mem_sup_of_le_normalizer hQR (generalizedFitting_le_qCoreOf_sup_pResidualOf H hq ha)
  have hwC : w ∈ Subgroup.centralizer (Q : Set G) := hRQ hw
  have hyw : y * w = w * y := Subgroup.mem_centralizer_iff.mp hwC y hy
  have hyy : y ^ 2 = (w ^ 2)⁻¹ := by
    have h1 : y ^ 2 * w ^ 2 = 1 := by
      calc y ^ 2 * w ^ 2 = y * (y * w) * w := by simp only [pow_two, mul_assoc]
        _ = y * (w * y) * w := by rw [hyw]
        _ = (y * w) * (y * w) := by group
        _ = 1 := ha2
    exact eq_inv_of_mul_eq_one_left h1
  have hy2C : y ^ 2 ∈ Subgroup.centralizer (Q : Set G) := by
    rw [hyy]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hwC 2)
  have hyodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := (qCoreOf_isPGroup H q) ⟨y, hy⟩
    have h1 : orderOf y ∣ q ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).mp h1
    rw [hj]
    exact (hq.odd_of_ne_two hq2).pow
  obtain ⟨k, hk⟩ := exists_pow_sq_eq hyodd
  have hyC : y ∈ Subgroup.centralizer (Q : Set G) := hk ▸ Subgroup.pow_mem _ hy2C k
  exact Subgroup.mul_mem _ hyC hwC

theorem le_qCoreCompl_two {H X : Subgroup G} (hXn : IsNormalIn X H)
    (hXnil : Group.IsNilpotent X) (hXodd : Odd (Nat.card X)) : X ≤ G63.qCoreCompl H 2 := by
  have hF : CFSG.fittingSubgroupOf X = X := fittingSubgroupOf_eq_self_of_isNilpotent hXnil
  calc X = CFSG.fittingSubgroupOf X := hF.symm
    _ ≤ G63.qCoreCompl H 2 := by
      rw [(show CFSG.fittingSubgroupOf X = _ from CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf X)]
      refine iSup_le fun q => ?_
      have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hq2 : q.1.1 ≠ 2 := by
        intro h
        have hdvd : q.1.1 ∣ Nat.card X := Nat.dvd_of_mem_primeFactors q.1.2
        rw [h] at hdvd
        exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr hdvd)
      exact (qCoreOf_le_qCoreOf_of_isNormalIn X H _ hXn).trans
        (le_sSup ⟨q.1.1, hq, hq2, rfl⟩)

theorem le_centralizer_of_forall {H X : Subgroup G} {a : G}
    (hc : ∀ q : ℕ, q.Prime → q ≠ 2 → a ∈ Subgroup.centralizer (qCoreOf H q : Set G))
    (hXn : IsNormalIn X H) (hXnil : Group.IsNilpotent X) (hXodd : Odd (Nat.card X)) :
    X ≤ Subgroup.centralizer ({a} : Set G) := by
  refine (le_qCoreCompl_two hXn hXnil hXodd).trans (sSup_le ?_)
  rintro _ ⟨q, hq, hq2, rfl⟩ x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp (hc q hq hq2)) x hx)

theorem mem_fstar_of_forall_centralizer (h31 : S_G31) {H A' : Subgroup G}
    (hS : IsSStarIn H A') {a : G} (ha : a ∈ A')
    (hc : ∀ q : ℕ, q.Prime → q ≠ 2 → a ∈ Subgroup.centralizer (qCoreOf H q : Set G)) :
    a ∈ generalizedFittingSubgroupOf H := by
  set K := normalClosureIn H A' with hKdef
  set Y := oddCoreOf (CFSG.fittingSubgroupOf K) with hYdef
  have haK : a ∈ K := G73.inf_le_normalClosureIn H A' ⟨ha, hS.1 ha⟩
  have hKH : K ≤ H := G73.normalClosureIn_le H A'
  have hYK : Y ≤ K := G53.oddFitting_le K
  have hYn : IsNormalIn Y H := G63.isNormalIn_of_le_normalizer (hYK.trans hKH) fun h hh =>
    G53.mem_normalizer_oddFitting (G73.le_normalizer_normalClosureIn H A' hh)
  have hYnil : Group.IsNilpotent Y :=
    isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent K) (G73.oddCoreOf_le _)
  have hYodd : Odd (Nat.card Y) := Balance.odd_card_oddCoreOf _
  have haY : a ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_forall hc hYn hYnil hYodd hy)
  exact (h31 G H A' hS).2 ⟨haK, haY⟩

theorem commutator_qCoreOf_le_qCoreOf_fstarZero (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    ⁅qCoreOf H p, qCoreOf H p⁆ ≤ qCoreOf (fstarZero H) p := by
  have hPF := qCoreOf_le_fittingSubgroupOf H p hp
  refine (le_inf (Bender35.commutator_self_le _) ?_).trans (G63.inf_fstarZero_le_qCoreOf H p)
  exact (Subgroup.commutator_mono hPF hPF).trans le_sup_left

theorem inf_centralizer_qCoreOf_fstarZero_le (H : Subgroup G) {p : ℕ} (hp : p.Prime) :
    qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf (fstarZero H) p : Set G) ≤
      qCoreOf (fstarZero H) p :=
  G63.le_qCoreOf_fstarZero H hp inf_le_left
    ((commutator_qCoreOf_le_qCoreOf_fstarZero H hp).trans
      (Subgroup.le_centralizer_iff.mp inf_le_right))

theorem commutator_qCoreOf_fstarZero_ne_bot {H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a : G} (haH : a ∈ H) (ha2 : orderOf a = 2)
    (h : ⁅qCoreOf H p, Subgroup.zpowers a⁆ ≠ ⊥) :
    ⁅qCoreOf (fstarZero H) p, Subgroup.zpowers a⁆ ≠ ⊥ := by
  intro h0
  apply h
  have hres : pResidualOf (Subgroup.zpowers a) p = Subgroup.zpowers a :=
    Bender35.pResidualOf_zpowers_eq hp
      (by rw [ha2]; exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hPp : IsPGroup p (qCoreOf H p) := qCoreOf_isPGroup H p
  have hP₀P := G63.qCoreOf_fstarZero_le H p
  have hHP : H ≤ Subgroup.normalizer (qCoreOf H p : Set G) :=
    le_normalizer_of_isNormalIn (qCoreOf_normal_in H p)
  have hC : ⁅qCoreOf H p ⊓ Subgroup.centralizer (qCoreOf (fstarZero H) p : Set G),
      Subgroup.zpowers a⁆ = ⊥ :=
    le_bot_iff.mp (h0 ▸ Subgroup.commutator_mono (inf_centralizer_qCoreOf_fstarZero_le H hp)
      le_rfl)
  have hT := bender1970_1_1_thompson p hp _ (Subgroup.zpowers a) _ (hPp.to_le hP₀P) hPp hres
    (hP₀P.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr (hHP haH)) h0 hC
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hT)

theorem not_isCyclic_qCoreOf_fstarZero {H : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : 3 ≤ CFSG.Open.pRank p (qCoreOf H p)) : ¬ IsCyclic (qCoreOf (fstarZero H) p) := by
  intro hcyc
  have : Fact p.Prime := ⟨hp⟩
  set P := qCoreOf H p with hPdef
  set C := qCoreOf (fstarZero H) p with hCdef
  have hPp : IsPGroup p P := qCoreOf_isPGroup H p
  have hCp : IsPGroup p C := qCoreOf_isPGroup _ p
  have hPC : P ≤ Subgroup.normalizer (C : Set G) :=
    (qCoreOf_normal_in H p).1.trans
      (le_normalizer_of_isNormalIn (G63.qCoreOf_fstarZero_isNormalIn H p))
  obtain ⟨E, hEP, hE, hEcard⟩ := exists_isElemAbelian_of_le_rank hp hPp (k := 3)
    (by rw [rank_eq_pRank_of_isPGroup hp hPp]; exact h3)
  have hEN : E ≤ Subgroup.normalizer (C : Set G) := hEP.trans hPC
  have hK : Nat.card (E ⊓ Subgroup.centralizer (C : Set G) : Subgroup G) ≤ p := by
    have hle : E ⊓ Subgroup.centralizer (C : Set G) ≤ C :=
      (inf_le_inf_right _ hEP).trans (inf_centralizer_qCoreOf_fstarZero_le H hp)
    have hc : IsCyclic (E ⊓ Subgroup.centralizer (C : Set G) : Subgroup G) :=
      G63.isCyclic_of_le hcyc hle
    have hexp : Monoid.exponent (E ⊓ Subgroup.centralizer (C : Set G) : Subgroup G) ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hE.2 x x.2.1)
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  have : E.Normalizes C := ⟨hEN⟩
  have : IsCyclic C := hcyc
  set φ : E →* MulAut C := MulDistribMulAction.toMulAut E C with hφ
  have hAut : IsCyclic (MulAut C) := by
    refine (IsCyclic.mulAutMulEquiv C).isCyclic.mpr ?_
    obtain ⟨k, hk⟩ := hCp.exists_card_eq
    rw [hk]
    exact ZMod.isCyclic_units_of_prime_pow p hp hp2 k
  have hrange : Nat.card φ.range ≤ p := by
    have hc : IsCyclic φ.range := Subgroup.isCyclic _
    have hexp : Monoid.exponent φ.range ∣ p := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun f => ?_
      obtain ⟨e, he⟩ := f.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← he, ← map_pow]
      have : e ^ p = 1 := Subtype.ext (hE.2 e e.2)
      rw [this, map_one, Subgroup.coe_one]
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  have hker : Nat.card φ.ker =
      Nat.card (E ⊓ Subgroup.centralizer (C : Set G) : Subgroup G) := by
    have heq : φ.ker = (Subgroup.centralizer (C : Set G)).subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      constructor
      · intro he c hc
        have h1 := congrArg (fun f : MulAut C => ((f ⟨c, hc⟩ : C) : G)) he
        simp only [hφ, MulDistribMulAction.toMulAut_apply, MulAut.one_apply] at h1
        rw [MulDistribMulAction.toMulEquiv_apply,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] at h1
        calc c * e = (e : G) * c * (e : G)⁻¹ * e := by rw [h1]
          _ = e * c := by group
      · intro he
        ext c
        simp only [hφ, MulDistribMulAction.toMulAut_apply, MulAut.one_apply]
        rw [MulDistribMulAction.toMulEquiv_apply,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, ← he c c.2]
        group
    rw [heq, ← Subgroup.card_map_of_injective E.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hcardE : Nat.card E = Nat.card φ.ker * Nat.card φ.range := by
    rw [← φ.ker.card_mul_index, Subgroup.index_ker]
  have h1 : Nat.card E ≤ p * p := by
    rw [hcardE, hker]
    exact Nat.mul_le_mul hK hrange
  have := hp.one_lt
  have h2 : p * p < p ^ 3 := by
    rw [pow_succ, pow_two]
    exact lt_mul_of_one_lt_right (by positivity) hp.one_lt
  omega

end CFSG.Goldschmidt.G64
