module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigJunk
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCaseO
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup Equiv Equiv.Perm AltStdBal CFSG.OddStandard.Solomon75
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem cycTwoBigFullPairFalse_holds : CycTwoBigFullPairFalse := by
  intro G _ _ L hS n hn hθ S hcyc h4 Q T g hQK hQp hQcard hg hTK hTp hTcard hQT
  obtain ⟨θ⟩ := hθ
  have hn8 : 8 ≤ n := by omega
  obtain ⟨z₀, d₀⟩ := cyc_of_sylow hS S hcyc
  obtain ⟨z, d⟩ := Cyc.of_card d₀ hQK hQp (by rw [hQcard, card_sylowSub])
  have hS' : StandardSetting G (CFSG.conjugate L g) := stdSetting_conjugate hS g
  obtain ⟨θ'⟩ : Nonempty (CFSG.conjugate L g ≃* alternatingGroup (Fin n)) :=
    ⟨(Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).symm.trans θ⟩
  have hTK' : T ≤ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := by
    rw [centralizer_conjugate]
    exact hTK
  obtain ⟨a, d₂⟩ := Cyc.of_card (d.conj g) hTK' hTp
    (by rw [hTcard, card_conjugate, hQcard])
  have hTC : ∀ t ∈ T, t ∈ centralizer ({z} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hQT d.mem) t ht)
  have hQa : ∀ q ∈ Q, q ∈ centralizer ({a} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hQT hq) a d₂.mem).symm
  obtain ⟨t₀, ht₀T, ht₀⟩ := exists_orderOf_eq_two_pow (k := 2) d₂.cyclic d₂.pgroup
    (by rw [hTcard]; simpa using h4)
  have ht₀sq : orderOf (t₀ ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [ht₀]; norm_num), ht₀]
    norm_num
  have ha_eq : t₀ ^ 2 = a :=
    eq_of_orderOf_eq_two_of_isCyclic d₂.cyclic (pow_mem ht₀T 2) d₂.mem ht₀sq d₂.order
  have ha2 : a ^ 2 = 1 := by rw [← d₂.order]; exact pow_orderOf_eq_one a
  have haK : a ∉ centralizer (L : Set G) := fun haK =>
    false_of_mem_cent_conj hS hg (by rw [d₂.order]; exact even_two) haK (hTK d₂.mem)
  obtain ⟨q₀, hq₀Q, hq₀⟩ := exists_orderOf_eq_two_pow (k := 2) d.cyclic d.pgroup
    (by rw [hQcard]; simpa using h4)
  have hq₀sq : orderOf (q₀ ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hq₀]; norm_num), hq₀]
    norm_num
  have hz_eq : q₀ ^ 2 = z :=
    eq_of_orderOf_eq_two_of_isCyclic d.cyclic (pow_mem hq₀Q 2) d.mem hq₀sq d.order
  have hz2 : z ^ 2 = 1 := by rw [← d.order]; exact pow_orderOf_eq_one z
  have hzK' : z ∉ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) := fun hzK' =>
    false_of_mem_cent_conj hS hg (by rw [d.order]; exact even_two) (d.le d.mem)
      (by rw [← centralizer_conjugate]; exact hzK')
  have ht₀N : t₀ ∈ normalizer (L : Set G) := cent_le_normalizer hS d (hTC t₀ ht₀T)
  rcases Int.units_eq_one_or (sign (rho θ hn8 ⟨t₀, ht₀N⟩)) with hev | hodd
  ·
    exact false_of_odd_commutators θ hn8 hn ht₀N (cent_le_normalizer hS d (hTC a d₂.mem))
      ha_eq ha2 haK _
      (oddPart_spec (cyc_le_inf_cent d₂) d₂.pgroup (cyc_odd_relIndex_inf d₂) d₂.cyclic).2.2.1
      (Or.inr ⟨hev, fun l _ hla =>
        sq_comm_mem_oddJunk hS' θ' hn8 d₂ ht₀T (mem_centralizer_singleton_iff.2 hla)⟩)
  ·
    exact false_of_odd_commutators θ' hn8 hn (cent_le_normalizer hS' d₂ (hQa q₀ hq₀Q))
      (cent_le_normalizer hS' d₂ (hQa z d.mem)) hz_eq hz2 hzK' _
      (oddPart_spec (cyc_le_inf_cent d) d.pgroup (cyc_odd_relIndex_inf d) d.cyclic).2.2.1
      (Or.inl fun b _ hbz =>
        comm_mem_oddJunk_of_outer hS θ hn8 d (hTC t₀ ht₀T) hodd hq₀Q
          (mem_centralizer_iff.1 (hQT hq₀Q) t₀ ht₀T).symm
          (mem_centralizer_singleton_iff.2 hbz))

end CFSG.OddStandard.AltStdCycTwo
