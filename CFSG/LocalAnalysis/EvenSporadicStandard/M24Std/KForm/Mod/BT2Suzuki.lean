module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Basic
public import CFSG.Sporadic.Schreier.TitsComponent
public import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Blueprint CFSG.LieType.Ree


private theorem suzuki_centralizer_odd_prime_order_false {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : suzukiGroup a K} (hu : u ∈ suzukiU a K)
    (hu1 : u ≠ 1) (hu2 : orderOf u = 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {x : suzukiGroup a K} (hx : x ∈ Subgroup.centralizer ({u} : Set (suzukiGroup a K)))
    (hxr : orderOf x = r) : False := by
  have hxB : x ∈ suzukiB a K :=
    CFSG.Sporadic.Schreier.Tits.centralizer_le_suzukiB hK hu hu1 hx
  have hdvdB : r ∣ Nat.card (suzukiB a K) := by
    rw [← hxr]
    exact (suzukiB a K).orderOf_dvd_natCard hxB
  have hdvdprod : r ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
    rwa [← (suzuki_borel_structure hK).2.2.2.2.2.2.2]
  have hnotdvd : ¬ r ∣ (2 ^ (2 * a + 1)) ^ 2 := by
    intro h
    have h' : r ∣ 2 ^ ((2 * a + 1) * 2) := by rwa [pow_mul]
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h'))
  have hrq : r ∣ 2 ^ (2 * a + 1) - 1 :=
    (hr.coprime_iff_not_dvd.2 hnotdvd).dvd_of_dvd_mul_left hdvdprod
  obtain ⟨g', hg'map⟩ :=
    ((suzuki_split_torus_odd_prime_centralizers hK).2 r hr hr2 hrq x hxr).1
  have hxcomm : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  have hu_cx : u ∈ Subgroup.centralizer ({x} : Set (suzukiGroup a K)) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxcomm.symm
  rw [hg'map] at hu_cx
  obtain ⟨τ, hτT, hτeq⟩ := Subgroup.mem_map.1 hu_cx
  have hτorder : orderOf τ = 2 := by
    have h2 : orderOf ((MulAut.conj g').toMonoidHom τ) = orderOf τ := by
      simpa only [MulEquiv.coe_toMonoidHom] using MulEquiv.orderOf_eq (MulAut.conj g') τ
    rw [hτeq, hu2] at h2
    exact h2.symm
  have h2dvdT : 2 ∣ Nat.card (suzukiT a K) := by
    rw [← hτorder]
    exact (suzukiT a K).orderOf_dvd_natCard hτT
  have hoddT : Odd (Nat.card (suzukiT a K)) := by
    rw [(suzuki_borel_structure hK).2.2.1]
    have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    have hev : Even (2 ^ (2 * a + 1)) := Nat.even_pow.2 ⟨even_two, by omega⟩
    obtain ⟨s, hs⟩ := hev
    exact ⟨s - 1, by omega⟩
  exact absurd (hoddT.of_dvd_nat h2dvdT) (by decide)

theorem suzuki_involution_centralizer_isPGroup {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : suzukiGroup a K) (ht : orderOf t = 2) :
    IsPGroup 2 ↥(centralizer ({t} : Set (suzukiGroup a K))) := by
  haveI := finite_suzukiGroup hK
  obtain ⟨hU2, hUidx⟩ := CFSG.Sporadic.Schreier.Tits.suzukiU_isSylow hK
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Schreier.Tits.exists_conj_mem_sylow (hU2.toSylow hUidx)
    (CFSG.Sporadic.Schreier.Tits.isPGroup_zpowers_of_orderOf_two ht)
  rw [IsPGroup.toSylow_coe] at hg
  have hu2 : orderOf (g * t * g⁻¹) = 2 := by
    rw [show g * t * g⁻¹ = (MulAut.conj g) t by rw [MulAut.conj_apply]]
    exact (MulEquiv.orderOf_eq (MulAut.conj g) t).trans ht
  have hu1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hCu : IsPGroup 2 ↥(centralizer ({g * t * g⁻¹} : Set (suzukiGroup a K))) := by
    rw [IsPGroup.iff_orderOf]
    intro y
    exact ⟨(orderOf y).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) (orderOf_pos y).ne'
        (fun {d} hd hdvd => by
          by_contra hd2
          have hdvdC : d ∣ Nat.card ↥(centralizer ({g * t * g⁻¹} : Set (suzukiGroup a K))) :=
            hdvd.trans (orderOf_dvd_natCard y)
          obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' d (hp := ⟨hd⟩) hdvdC
          exact suzuki_centralizer_odd_prime_order_false hK hg hu1 hu2 hd hd2 w.2
            (by rw [Subgroup.orderOf_coe, hw]))⟩
  have e : Subgroup.centralizer ({t} : Set (suzukiGroup a K)) ≃*
      Subgroup.centralizer ({g * t * g⁻¹} : Set (suzukiGroup a K)) :=
    ((Subgroup.centralizer {t}).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (CFSG.Sporadic.Schreier.Tits.map_conj_centralizer g t))
  exact hCu.of_equiv e.symm

theorem involutionCentralizersCharTwo_suzuki {S : Type} [Group S] {f : ℕ}
    (h : SuzukiModel S 2 f) : InvolutionCentralizersCharTwo S := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  refine InvolutionCentralizersCharTwo.of_mulEquiv e fun t ht => ?_
  exact isCharacteristicP_two_of_isPGroup
    (suzuki_involution_centralizer_isPGroup (a := a) (K := K) (by rw [hK, hf]) t ht)

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
