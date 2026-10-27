module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.GLTheoremB.I2810.A5BlockPure

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Fr

variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem isCharIn_of_characteristic {C : Subgroup X} (hCS : C ≤ S)
    (hC : (C.subgroupOf S).Characteristic) : IsCharIn C S := by
  refine ⟨hCS, fun ψ x hx => ?_⟩
  have hx' : x ∈ C.subgroupOf S := hx
  have h1 := Subgroup.characteristic_iff_map_eq.mp hC ψ
  have h2 : ψ x ∈ (C.subgroupOf S).map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hx'
  rw [h1] at h2
  exact Subgroup.mem_subgroupOf.mp h2

theorem a5_nochar_aux (h : Setup28 W K S) (hR : Red28 W K S) (hd : ¬ Concl28d K S) {I : Subgroup X}
    (hI : A5Frame W K S I) : CFSG.QuasithinUnique.Setup.Campbell.NoCharNormal S I := by
  intro C hCS hC0 hCchar hIN
  apply hd
  have hchar : IsCharIn C S := isCharIn_of_characteristic hCS hCchar
  refine ⟨C, hC0, hchar, ?_⟩
  have hgen := hI.gen (K ⊓ Subgroup.normalizer (C : Set X)) inf_le_left
    (fun x hx => ⟨hx.2, hIN hx.1⟩)
    (fun k hk hkN => ⟨hk, hchar.normalizer_le hkN⟩)
  have hSN : S ≤ Subgroup.normalizer (C : Set X) := fun s hs =>
    hchar.normalizer_le (Subgroup.le_normalizer hs)
  exact hgen.trans (sup_le inf_le_right fun w hw => hSN (hR.w1_S hw.2))

theorem a5_pick_aux (h : Setup28 W K S) (hR : Red28 W K S) {I : Subgroup X} (hI : A5Frame W K S I) :
    ∃ p ∈ K, p ∉ zPre W K ∧ p ∈ CFSG.Quasithin.pResidualOf 2 I := by
  obtain ⟨q⟩ := hI.quot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(alternatingGroup (Fin 5))) 3
    (by rw [A5Pure.card_alt5]; norm_num)
  let π : ↥I →* ↥(alternatingGroup (Fin 5)) := q.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπs : Function.Surjective π := q.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : ∀ g : ↥I, π g = 1 ↔ (g : X) ∈ kerAct W K S := by
    intro g
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← hI.o2, CFSG.mem_openPCoreOf_iff]
  obtain ⟨g, hg⟩ := hπs a
  obtain ⟨k, hkK, hkI, hgk⟩ := hI.dec (g : X) g.2
  set k' : ↥I := ⟨k, hkI⟩ with hk'
  have hπk : π k' = a := by
    have h1 : g = (g * k'⁻¹) * k' := by group
    have hw : π (g * k'⁻¹) = 1 := (hπker _).2 (by simpa [hk'] using hgk)
    rw [← hg, h1, map_mul, hw, one_mul]
  obtain ⟨e, b, hb, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k').ne'
  set p' : ↥I := k' ^ (2 ^ e) with hp'
  have hdvd : 2 ^ e ∣ orderOf k' := hord ▸ dvd_mul_right _ _
  have hordp : orderOf p' = b := by
    rw [hp', orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hord,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hπp : π p' ≠ 1 := by
    intro h1
    have h2 : π p' = a ^ (2 ^ e) := by rw [hp', map_pow, hπk]
    have h3 : orderOf (a ^ (2 ^ e)) = 3 := by
      rw [Nat.Coprime.orderOf_pow, ha]
      rw [ha]
      exact Nat.Coprime.pow_right _ (by norm_num)
    rw [h2] at h1
    rw [h1, orderOf_one] at h3
    omega
  have hp'K : (p' : X) ∈ K := by
    rw [hp']; exact K.pow_mem hkK _
  refine ⟨(p' : X), hp'K, fun hz => hπp ((hπker p').2 (hI.zker ⟨p'.2, hz⟩)), ?_⟩
  obtain ⟨j, hj⟩ := CFSG.Quasithin.F53Push.exists_pow_mem_pResidualOf I p'.2
  have hordX : orderOf (p' : X) = b := by rw [Subgroup.orderOf_coe, hordp]
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime (x := (p' : X)) (n := 2 ^ j)
    (by rw [hordX]; exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hb))
  rw [← ht]
  exact (CFSG.Quasithin.pResidualOf 2 I).pow_mem hj t

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Fr
