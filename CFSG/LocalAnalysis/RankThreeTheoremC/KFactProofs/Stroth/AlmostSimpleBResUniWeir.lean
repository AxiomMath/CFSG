module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResUniDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerUnitaryBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.Open (IsElemAbelian)

theorem two_mul_orderOf_le_of_elemAbelian_unitary {ℓ f n : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬ (n = 3 ∧ ℓ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hpq : ¬ p ∣ ℓ ^ f + 1)
    {E : Subgroup (primeFormP hU (idCn n K))} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    2 * orderOf (-((ℓ ^ f : ℕ) : ZMod p)) ≤ n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := hU.finite
  haveI : Fintype K := Fintype.ofFinite K
  have hconj := CFSG.RankThree.PartOne.KCUnitaryRegular.conj_injective_primeFormP hU
    (isPrimeFormGram_one' (n := n)) hn hq
  set V : Subgroup (MulAut (primeFormP hU (idCn n K))) :=
    E.map (MulAut.conj : primeFormP hU (idCn n K) →* MulAut (primeFormP hU (idCn n K))) with hV
  have hVc : Nat.card V = p ^ 2 := by
    rw [hV, Subgroup.card_map_of_injective hconj]
    exact hEc
  have hcomm : ∀ a b : ↥V, a * b = b * a := by
    intro a b
    obtain ⟨y₁, hy₁, ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y₂, hy₂, hb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : MulAut (primeFormP hU (idCn n K))) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨y₁, hy₁⟩ : E) ⟨y₂, hy₂⟩)
  haveI hVe : CFSG.IsElementaryAbelian p ↥V :=
    { toIsMulCommutative := ⟨⟨fun a b => hcomm a b⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨y, hy, ha⟩ := Subgroup.mem_map.1 a.2
        apply Subtype.ext
        change (a : MulAut (primeFormP hU (idCn n K))) ^ p = 1
        rw [← ha, ← map_pow, hE.2 y hy, map_one] }
  have hVD : V ≤ primeFormD hU (idCn n K) := by
    intro v hv
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hv
    exact inner_le_primeFormD hU ⟨y, rfl⟩
  obtain ⟨W, hWe, hWc, -, -, -⟩ :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.exists_lift_group_u hU hn hpq hVD hVc
  have hpℓ' : ¬ p ∣ ℓ ^ f := fun hd =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hU.prime).1 (hp.dvd_of_dvd_pow hd))
  have hcard : Fintype.card K = (ℓ ^ f) ^ 2 := by
    rw [Fintype.card_eq_nat_card, hU.card, ← pow_mul, mul_comm, pow_mul]
  by_contra hlt
  push Not at hlt
  have hq0 : ((ℓ ^ f : ℕ) : ZMod p) ≠ 0 := fun h0 =>
    hpℓ' ((ZMod.natCast_eq_zero_iff _ _).mp h0)
  have hpos : 0 < orderOf (-((ℓ ^ f : ℕ) : ZMod p)) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, by have := hp.two_le; omega, ZMod.pow_card_sub_one_eq_one (neg_ne_zero.2 hq0)⟩)
  have hdiv : n / orderOf (-((ℓ ^ f : ℕ) : ZMod p)) ≤ 1 := by
    have := (Nat.div_lt_iff_lt_mul hpos).2
      (by omega : n < 2 * orderOf (-((ℓ ^ f : ℕ) : ZMod p)))
    omega
  let e : ↥(primeFormUnitary hU (idCn n K)) ≃* ↥(CFSG.Quasithin.StatedGU n (ℓ ^ f) K) :=
    MulEquiv.subgroupCongr
      (CFSG.GH74.GLS.Stage2.Bender.Thm1.UnC.primeFormUnitary_eq_statedGU hU)
  let W' : Subgroup ↥(CFSG.Quasithin.StatedGU n (ℓ ^ f) K) := W.map e.toMonoidHom
  let e' : ↥W ≃* ↥W' := Subgroup.equivMapOfInjective W e.toMonoidHom e.injective
  have hW'c : Nat.card ↥W' = p ^ 2 := by rw [Nat.card_congr e'.toEquiv.symm, hWc]
  have hW'p : IsPGroup p ↥W' := IsPGroup.of_card hW'c
  obtain ⟨P, hP⟩ := hW'p.exists_le_sylow
  obtain ⟨φ⟩ := CFSG.GroupTheory.WeirSylow.sylow_GU (hp.odd_of_ne_two hp2) K hcard hpℓ'
    (by omega) P
  have hcyc : IsCyclic ↥P := (MulEquiv.isCyclic φ).mpr
    (CFSG.GH74.GLS.Stage2.OddAut.isCyclic_sigmaModel_of_div_le_one hp.one_lt hdiv)
  have hW'cyc : IsCyclic ↥W' := isCyclic_of_injective (Subgroup.inclusion hP)
    (Subgroup.inclusion_injective hP)
  have hWcyc : IsCyclic ↥W := (MulEquiv.isCyclic e').mpr hW'cyc
  haveI := hWe
  exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hWc hWcyc

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
