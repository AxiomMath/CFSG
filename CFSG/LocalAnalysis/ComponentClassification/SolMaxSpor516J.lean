module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516Rows
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafSporF
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpNotLie
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.ComponentClassification.SolMax.Spor516

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.GSThmB.Pump516
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {S : Type} [Group S]

theorem center_eq_bot_of_nonabelian [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x) :
    center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · obtain ⟨x, y, hxy⟩ := hna
    exact absurd (mem_center_iff.mp (h ▸ mem_top y) x) hxy

theorem orderOf_conj_eq_two (hZ : center S = ⊥) {t : S} (ht : orderOf t = 2) :
    orderOf (MulAut.conj t) = 2 := by
  have htt : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  refine orderOf_eq_prime (by rw [← map_pow, htt, map_one]) fun h1 => ?_
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  refine ht1 (mem_bot.mp (hZ ▸ mem_center_iff.mpr fun g => ?_))
  have h2 := congrArg (fun φ : MulAut S => φ g) h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  calc g * t = t * g * t⁻¹ * t := by rw [h2]
    _ = t * g := by group

variable [Finite S]

theorem oddCore_centralizer_eq_bot [IsSimpleGroup S] {s : TauCeti.SporadicName}
    (hfree : CatalogueU.SporadicOddCoreFree s) (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier s) {t : S} (ht : orderOf t = 2) :
    CFSG.oddCore (centralizer ({t} : Set S)) = ⊥ := by
  have h := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hfree hna e)
    (orderOf_conj_eq_two (center_eq_bot_of_nonabelian hna) ht)
  rwa [fixedSubgroup_conj_eq] at h

theorem card_psl2_mul_two {X : Type} [Group X] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Blueprint.LieModel X .PSL 2 p e) : Nat.card X * 2 = p ^ e * ((p ^ e) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_mul_two_of_statedClassicalModel_psl_two_odd hp hp2 (h.statedClassicalModel (by decide))

theorem leaf_J_component_card {t : S} (hcore : CFSG.oddCore (centralizer ({t} : Set S)) = ⊥)
    {J : Subgroup S} (hJC : J ≤ centralizer ({t} : Set S))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set S)))) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hJm : LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f)) :
    IsComponent (J.subgroupOf (centralizer ({t} : Set S))) ∧
      Nat.card (↥(J.subgroupOf (centralizer ({t} : Set S))) ⧸
        center ↥(J.subgroupOf (centralizer ({t} : Set S)))) * 2 =
        p ^ (2 * f) * ((p ^ (2 * f)) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Jt := J.subgroupOf (centralizer ({t} : Set S)) with hJt
  have hO : pPrimeCore 2 (centralizer ({t} : Set S)) = ⊥ := by
    rw [← Sporadic.HeldB.oddCore_eq_pPrimeCore_two']
    exact hcore
  have hc : IsComponent Jt := B5a.isComponent_of_isPComponent hO hJ
  have hJO : pPrimeCore 2 Jt = ⊥ := by
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hc.2
    rw [hO, inf_bot_eq] at h1
    exact (map_eq_bot_iff_of_injective _ Jt.subtype_injective).mp h1
  let eO : Jt ⧸ pPrimeCore 2 Jt ≃* J ⧸ pPrimeCore 2 J :=
    CatalogueBAlternating.primeCoreQuotientEquiv 2 (subgroupOfEquivOfLe hJC)
  let eJ : Jt ≃* J ⧸ pPrimeCore 2 J :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hJO.symm)).trans eO
  have hs : IsSimpleGroup (J ⧸ pPrimeCore 2 J) :=
    CatLeafProof.X10Sp.isSimpleGroup_of_lieModel_psl (by norm_num) hJm
  have hs' : IsSimpleGroup Jt := eJ.isSimpleGroup
  have hZ : center Jt = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Jt) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hc.1.2.2
      have : Subsingleton (Jt ⧸ center Jt) := QuotientGroup.subsingleton_iff.mpr h
      exact hab (Subsingleton.elim _ _)
  refine ⟨hc, ?_⟩
  have h1 : Nat.card (Jt ⧸ center Jt) = Nat.card (J ⧸ pPrimeCore 2 J) := by
    rw [hZ]
    exact Nat.card_congr ((QuotientGroup.quotientBot (G := Jt)).trans eJ).toEquiv
  rw [h1]
  exact card_psl2_mul_two hp hp2 hJm

theorem leafAt_of_filter_empty {N : ℕ} (hN : IsSimpleGroup S → Nat.card S = N)
    (L : List (ℕ × ℕ)) (hL : ∀ x ∈ L, x.1.Prime) (hNL : (L.map fun x => x.1 ^ x.2).prod = N)
    (hF : ∀ x ∈ L, FilterOK N ∅ x) : CF516LeafAt S := by
  intro hs _ _ σ P _ p f hp hp2 hf hPm _ _ _ _ _ _ _ _ _ _ _ _ _
  exact Finset.notMem_empty _ (pow_mem_of_filter (hN hs) L hL hNL hF hp hp2 hf hPm)

theorem leafAt_of_filter {s : TauCeti.SporadicName} (e : S ≃* NativeSporadic.Carrier s)
    (hfree : CatalogueU.SporadicOddCoreFree s) {N : ℕ} (hN : IsSimpleGroup S → Nat.card S = N)
    (L : List (ℕ × ℕ)) (hL : ∀ x ∈ L, x.1.Prime) (hNL : (L.map fun x => x.1 ^ x.2).prod = N)
    {Qs : Finset ℕ} (hF : ∀ x ∈ L, FilterOK N Qs x)
    (hcomp : IsSimpleGroup S → ∀ q ∈ Qs, ∀ t : S, orderOf t = 2 →
      ∀ B : Subgroup (centralizer ({t} : Set S)), IsComponent B →
        Nat.card (B ⧸ center B) * 2 ≠ q ^ 2 * ((q ^ 2) ^ 2 - 1)) : CF516LeafAt S := by
  intro hs hna _ σ P _ p f hp hp2 hf hPm t _ ht2 J hJC hJ hJm _ _ _ _ _ _
  have hq := pow_mem_of_filter (hN hs) L hL hNL hF hp hp2 hf hPm
  have hcore := oddCore_centralizer_eq_bot hfree hna e ht2
  obtain ⟨hc, hcard⟩ := leaf_J_component_card hcore hJC hJ hp hp2 hJm
  have h1 := hcomp hs (p ^ f) hq t ht2 _ hc
  rw [← pow_mul, mul_comm f 2] at h1
  exact h1 hcard

end CFSG.ComponentClassification.SolMax.Spor516
