module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IPocketL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem mul_self_eq_one_of_orderOf_eq_two {G : Type} [Group G] {w : G} (h : orderOf w = 2) :
    w * w = 1 := by
  have h1 := pow_orderOf_eq_one w
  rw [h, pow_two] at h1
  exact h1

theorem exists_mem_omegaProj_conj_of_hasType {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} (hQ : Q.Nondegenerate)
    (h3 : 3 ≤ Module.finrank (ZMod 3) V) {x x' : ProjOrth Q} {r : ℕ} {α : ℤˣ}
    (hx : HasType x r α) (hx' : HasType x' r α) : ∃ c ∈ omegaProj hQ, c * x * c⁻¹ = x' := by
  obtain ⟨-, t, htt, hty, rfl⟩ := hx
  obtain ⟨-, t', htt', hty', rfl⟩ := hx'
  obtain ⟨c, hc, hct⟩ := exists_mem_omegaGroup_conj hQ h3 htt htt' (hty.trans hty'.symm)
  refine ⟨toProj Q c, Subgroup.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, hct]

variable {G : Type} [Group G] {L : Subgroup G}

theorem sec4I_conjClassIn_of_conj [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {w w' : G} (hw : w ∈ L) (hw' : w' ∈ L)
    (hww : w * w = 1) (hww' : w' * w' = 1) {c : ProjOrth Sec4IQ} (hc : c ∈ Sec4IOmega)
    (hconj : c * ((e (QuotientGroup.mk (⟨w, hw⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ) * c⁻¹ =
      ((e (QuotientGroup.mk (⟨w', hw'⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ)) :
    w' ∈ conjClassIn L w := by
  have hρ := sec4ICover_odd hL e
  obtain ⟨l, hl⟩ := hρ.surjective ⟨c, hc⟩
  have hww1 : (l * ⟨w, hw⟩ * l⁻¹ : ↥L) * (l * ⟨w, hw⟩ * l⁻¹) = 1 := by
    have h1 : (⟨w, hw⟩ : ↥L) * ⟨w, hw⟩ = 1 := Subtype.ext hww
    calc (l * ⟨w, hw⟩ * l⁻¹ : ↥L) * (l * ⟨w, hw⟩ * l⁻¹) =
        l * ((⟨w, hw⟩ : ↥L) * ⟨w, hw⟩) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hrho : sec4ICover e (l * ⟨w, hw⟩ * l⁻¹) = sec4ICover e ⟨w', hw'⟩ := by
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv, hl]
    exact hconj
  have heq := hρ.eq_of_mul_self_eq_one hww1 (Subtype.ext hww') hrho
  exact ⟨l, l.2, (congrArg Subtype.val heq).symm⟩

theorem sec4I_exists_inner [Finite G] (hL : IsOmega7Group L)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* Sec4IOmega) {s : G} {y : ProjOrth Sec4IQ}
    (hy : Sec4IActs e s y) (hyΩ : y ∈ Sec4IOmega) (hyy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ (u : G) (hu : u ∈ L), orderOf u = 2 ∧
      ((e (QuotientGroup.mk (⟨u, hu⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ) = y ∧
      u⁻¹ * s ∈ Subgroup.centralizer (L : Set G) := by
  have hρ := sec4ICover_odd hL e
  have hpp : (⟨y, hyΩ⟩ : Sec4IOmega) * ⟨y, hyΩ⟩ = 1 := Subtype.ext hyy
  obtain ⟨l, hll, hlp⟩ := hρ.exists_mul_self_eq_one_lift hpp
  have hl1 : l ≠ 1 := by
    intro h1
    rw [h1, map_one] at hlp
    exact hy1 (congrArg Subtype.val hlp.symm)
  have hord : orderOf (l : G) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two, ← Subgroup.coe_mul, hll]; rfl) ?_
    exact fun h => hl1 (Subtype.ext h)
  have hly : ((e (QuotientGroup.mk (⟨(l : G), l.2⟩ : ↥L)) : Sec4IOmega) : ProjOrth Sec4IQ) = y :=
    congrArg Subtype.val hlp
  have hact : Sec4IActs e (l : G) y := hly ▸ Sec4IActs.of_mem e l.2
  have hact' := (hact.inv).mul hy
  exact ⟨l, l.2, hord, hly, (Sec4IActs.eq_one_iff hL hact').mp (inv_mul_cancel y)⟩

theorem asc82Fact43Class_holds : Asc82Fact43Class := by
  intro G _ _ L hL w w' hw hw'
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨hwL, hord, hty⟩ := (sec4I_isI4PlusIn_iff hL e).mp hw
  obtain ⟨hwL', hord', hty'⟩ := (sec4I_isI4PlusIn_iff hL e).mp hw'
  obtain ⟨c, hc, hconj⟩ := exists_mem_omegaProj_conj_of_hasType sec4IQ_nondegenerate
    (by rw [sec4IQ_finrank]; norm_num) hty hty'
  exact sec4I_conjClassIn_of_conj hL e hwL hwL' (mul_self_eq_one_of_orderOf_eq_two hord)
    (mul_self_eq_one_of_orderOf_eq_two hord') hc hconj

theorem asc82Fact6Class_holds : Asc82Fact6Class := by
  intro G _ _ L hL u u' hu hu' hord hord' hty hty'
  obtain ⟨e⟩ := sec4I_exists_model hL
  have h6 : (6 : ℕ) = 2 ∨ (6 : ℕ) = 4 ∨ (6 : ℕ) = 6 := Or.inr (Or.inr rfl)
  have h1 := (sec4I_inducesTypeSome_mem_iff e hu h6).mp hty
  have h2 := (sec4I_inducesTypeSome_mem_iff e hu' h6).mp hty'
  obtain ⟨c, hc, hconj⟩ := exists_mem_omegaProj_conj_of_hasType sec4IQ_nondegenerate
    (by rw [sec4IQ_finrank]; norm_num) h1 h2
  exact sec4I_conjClassIn_of_conj hL e hu hu' (mul_self_eq_one_of_orderOf_eq_two hord)
    (mul_self_eq_one_of_orderOf_eq_two hord') hc hconj

theorem asc82FactInner6_holds : Asc82FactInner6 := by
  intro G _ _ L hL s hs2 hsN hty
  obtain ⟨e⟩ := sec4I_exists_model hL
  have h6 : (6 : ℕ) = 2 ∨ (6 : ℕ) = 4 ∨ (6 : ℕ) = 6 := Or.inr (Or.inr rfl)
  obtain ⟨y, hy, hyty⟩ := (sec4I_inducesTypeSome_iff e h6).mp hty
  have hyΩ : y ∈ Sec4IOmega :=
    (hasType_mem_omegaProj_iff_seven sec4IQ_nondegenerate sec4IQ_finrank hyty h6).mpr
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have hyy : y * y = 1 := hy.sq (mul_self_eq_one_of_orderOf_eq_two hs2)
  obtain ⟨u, hu, hord, hρu, hc⟩ := sec4I_exists_inner hL e hy hyΩ hyy hyty.1
  refine ⟨u, u⁻¹ * s, hu, hord, ?_, hc, by group⟩
  rw [sec4I_inducesTypeSome_mem_iff e hu h6, hρu]
  exact hyty

end CFSG.OddStandard.SmallF3.Omega
