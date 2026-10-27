module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OddCoresG1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Assembly.Dichotomy Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

private instance instDecEqPermFinFourE1Odd : DecidableEq (Perm (Fin 4)) := fun a b =>
  decidable_of_iff (∀ i : Fin 4, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

theorem perm4_eq_fourList : ∀ σ : Perm (Fin 4), σ * fourRep = fourRep * σ → sign σ = 1 →
    ∃ i : Fin 4, σ = fourList i := by
  decide +kernel

theorem kappaWord_mod : (∀ i : Fin 4, (E1Data.kappaWord i).val % 16 = 0) ∧
    ∀ v : Fin 64, v.val % 16 = 0 → ∃ i : Fin 4, E1Data.kappaWord i = v := by
  decide

theorem exists_pow_conj_eq_mul {X : Type*} [Group X] {t o : X} (htt : t * t = 1)
    (hto : t * o * (t * o) = 1) (hodd : Odd (orderOf o)) :
    ∃ k : ℕ, o ^ k * t * (o ^ k)⁻¹ = t * o := by
  obtain ⟨j, hj⟩ := hodd
  have ht : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h1 : t * o * t = o⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_assoc (t * o) t o]; exact hto)
  have h2 : t * o ^ j * t = (o ^ j)⁻¹ := by
    calc t * o ^ j * t = t * o ^ j * t⁻¹ := by rw [ht]
      _ = (t * o * t⁻¹) ^ j := conj_pow.symm
      _ = (o ^ j)⁻¹ := by rw [ht, h1, inv_pow]
  have h3 : o ^ j * o ^ j = o⁻¹ := by
    rw [← pow_add, eq_inv_iff_mul_eq_one, ← pow_succ, show j + j + 1 = orderOf o by omega,
      pow_orderOf_eq_one]
  refine ⟨j, ?_⟩
  calc o ^ j * t * (o ^ j)⁻¹ = o ^ j * t * (t * o ^ j * t) := by rw [h2]
    _ = o ^ j * (t * t) * o ^ j * t := by simp only [mul_assoc]
    _ = o⁻¹ * t := by rw [htt, mul_one, h3]
    _ = t * o * t * t := by rw [h1]
    _ = t * o := by rw [mul_assoc (t * o) t t, htt, mul_one]

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem rho4C_rho5C_kappaX (i : Fin 4) : d.rho4C (d.toCentralizer (d.kappaX i)) = fourList i ∧
    d.rho5C (d.toCentralizer (d.kappaX i)) = 1 := by
  rw [rho4C, rho5C, liftC_toCentralizer, liftC_toCentralizer, d.quasiMk_kappaX]
  exact ⟨d.rho4_kappa i, d.rho5_of_mem_centralizer (d.kappa_mem i)⟩

theorem coe_toCentralizer_kappaX_mem (i : Fin 4) :
    ((d.toCentralizer (d.kappaX i) : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) :
      J ⧸ Subgroup.center J) ∈ e1PBar (Subgroup.center J) u m y x := by
  rw [coe_toCentralizer, d.mk_kappaX]
  exact d.caseC3BCD.mem_e1PBar_iff.mpr ⟨_, kappaWord_mod.1 i, rfl⟩

theorem exists_inv_mul_mem_of_rho5C_eq_one
    {c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}} (hc : d.rho5C c = 1) :
    ∃ i : Fin 4, (d.toCentralizer (d.kappaX i))⁻¹ * c ∈
      CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) := by
  have hcu : c * centralizerSelf u = centralizerSelf u * c :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  have hc4 : d.rho4C c * fourRep = fourRep * d.rho4C c := by
    have := congrArg d.rho4C hcu
    rwa [map_mul, map_mul, d.rho4C_self] at this
  have hsign : sign (d.rho4C c) = 1 := by
    have h := mem_alternatingGroup.mp (d.phiU c).2
    rw [d.coe_phiU, sign_permNine, hc, Perm.sign_one, mul_one] at h
    exact h
  obtain ⟨i, hi⟩ := perm4_eq_fourList _ hc4 hsign
  obtain ⟨h4, h5⟩ := d.rho4C_rho5C_kappaX i
  refine ⟨i, ?_⟩
  rw [← d.ker_phiU, MonoidHom.mem_ker]
  apply Subtype.ext
  rw [d.coe_phiU, map_mul, map_mul, map_inv, map_inv, h4, h5, hc, ← hi, inv_mul_cancel,
    inv_one, one_mul, Prod.mk_one_one, map_one, OneMemClass.coe_one]

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem centralizer_self_le_normalizer :
    Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ Subgroup.normalizer
      (oddCoreSpan (e1WBar (Subgroup.center J) u m y x) : Set (J ⧸ Subgroup.center J)) := by
  have hb := d.caseC3BCD
  set C := Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} with hC
  set P := e1PBar (Subgroup.center J) u m y x with hP
  set W := oddCoreSpan (e1WBar (Subgroup.center J) u m y x) with hW
  have hWP : W = oddCoreSpan P := (d.oddCoreSpan_e1PBar htype).symm
  have huP : (u : J ⧸ Subgroup.center J) ∈ P :=
    hb.mem_e1PBar_iff.mpr ⟨32, by decide, CaseC3BCD.caseC3Word_thirtytwo⟩
  have hu1 : (u : J ⧸ Subgroup.center J) ≠ 1 := by
    rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x),
      Ne, hb.caseC3Word_eq_one_iff]
    decide
  have huW : involutionOddCore (u : J ⧸ Subgroup.center J) ≤ W := by
    rw [hWP]
    exact involutionOddCore_le_span P huP hu1
  have hPC : P ≤ C := fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr
    (hb.commute_of_mem_e1WBar (hb.e1PBar_le_e1WBar hp) (hb.e1PBar_le_e1WBar huP))
  intro g hg
  have hmap : W.map (MulAut.conj g).toMonoidHom ≤ W := by
    rw [hWP, oddCoreSpan_map]
    refine iSup_le fun q => iSup_le fun hq => iSup_le fun hq1 => ?_
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hq1 ⊢
    set c : C := ⟨g, hg⟩ * ⟨p, hPC hp⟩ * ⟨g, hg⟩⁻¹ with hc
    have hp5 : d.rho5C ⟨p, hPC hp⟩ = 1 := by
      obtain ⟨v, hv, hvp⟩ := hb.mem_e1PBar_iff.mp hp
      obtain ⟨i, rfl⟩ := kappaWord_mod.2 v hv
      have heq : (⟨p, hPC hp⟩ : C) = d.toCentralizer (d.kappaX i) :=
        Subtype.ext (by rw [coe_toCentralizer, d.mk_kappaX, hvp])
      rw [heq]
      exact (d.rho4C_rho5C_kappaX i).2
    have hc5 : d.rho5C c = 1 := by rw [hc, map_mul, map_mul, hp5, mul_one, map_inv, mul_inv_cancel]
    obtain ⟨i, hi⟩ := d.exists_inv_mul_mem_of_rho5C_eq_one hc5
    set t : J ⧸ Subgroup.center J := ((d.toCentralizer (d.kappaX i) : C) :
      J ⧸ Subgroup.center J) with ht
    set o : J ⧸ Subgroup.center J := (((d.toCentralizer (d.kappaX i))⁻¹ * c : C) :
      J ⧸ Subgroup.center J) with ho
    have htP : t ∈ P := d.coe_toCentralizer_kappaX_mem i
    have hoθ : o ∈ involutionOddCore (u : J ⧸ Subgroup.center J) := by
      rw [involutionOddCore_eq_map_pPrimeCore]
      exact ⟨_, hi, rfl⟩
    have hto : g * p * g⁻¹ = t * o := by
      rw [ho, Subgroup.coe_mul, Subgroup.coe_inv, ← ht, mul_inv_cancel_left]
      rfl
    have hpp : p * p = 1 := hb.mul_self_of_mem_e1WBar (hb.e1PBar_le_e1WBar hp)
    have hodd : Odd (orderOf o) := (odd_card_involutionOddCore _).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hoθ)
    obtain ⟨k, hk⟩ := exists_pow_conj_eq_mul (hb.mul_self_of_mem_e1WBar (hb.e1PBar_le_e1WBar htP))
      (by rw [← hto]; exact conj_mul_self_eq_one hpp g) hodd
    have ht1 : t ≠ 1 := fun h1 => by
      rw [h1, one_mul] at hto
      have hoo : o * o = 1 := by rw [← hto]; exact conj_mul_self_eq_one hpp g
      exact hq1 (hto.trans (eq_one_of_mul_self_of_odd hoo hodd))
    have hkW : o ^ k ∈ oddCoreSpan P := hWP ▸ huW (Subgroup.pow_mem _ hoθ k)
    rw [hto, ← hk, ← MulAut.conj_apply, ← involutionOddCore_map]
    refine (Subgroup.map_mono (involutionOddCore_le_span P htP ht1)).trans ?_
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkW hw) (Subgroup.inv_mem _ hkW)
  exact mem_normalizer_of_forall_conj_mem fun w hw => hmap ⟨w, hw, rfl⟩

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
