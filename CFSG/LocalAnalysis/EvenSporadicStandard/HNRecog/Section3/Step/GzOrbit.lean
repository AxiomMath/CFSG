module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.PairRep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzNE
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.ExistsB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.OrbitPart
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzIrr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.GzInvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.Card
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem orderOf_eq_of_isConj_gz {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

private theorem eq_one_or_eq_of_mem_zpowers {G : Type} [Group G] {z q : G} (hz : orderOf z = 2)
    (hq : q ∈ Subgroup.zpowers z) : q = 1 ∨ q = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  rw [← zpow_mod_orderOf, hz]
  have hn : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hn with hn | hn
  · left
    rw [hn]
    simp
  · right
    rw [hn]
    simp

private theorem eq_inv_mul_mul_of_conj_eq {G : Type} [Group G] {x t g : G} (h : g * x * g⁻¹ = t) :
    x = g⁻¹ * t * g := by
  rw [← h]
  group

private theorem exists_mem_Gx_conj_gz {G : Type} [Group G] {x x' w a z₀ g g' : G}
    (hxa : g * x * g⁻¹ = a) (hx'a : g' * x' * g'⁻¹ = a) (hwz : g * w * g⁻¹ = z₀)
    (hw'z : g' * w * g'⁻¹ = z₀) : ∃ k ∈ Gx w, k * x * k⁻¹ = x' := by
  refine ⟨g'⁻¹ * g, ?_, ?_⟩
  · have hw : (g'⁻¹ * g) * w * (g'⁻¹ * g)⁻¹ = w :=
      calc (g'⁻¹ * g) * w * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * w * g⁻¹) * g' := by group
        _ = g'⁻¹ * z₀ * g' := by rw [hwz]
        _ = w := (eq_inv_mul_mul_of_conj_eq hw'z).symm
    rw [mem_Gx]
    exact (mul_inv_eq_iff_eq_mul.mp hw).symm
  · calc (g'⁻¹ * g) * x * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * x * g⁻¹) * g' := by group
      _ = g'⁻¹ * a * g' := by rw [hxa]
      _ = x' := (eq_inv_mul_mul_of_conj_eq hx'a).symm

theorem gzOrbitInput_holds :
    ∀ (hI : TwoHSInterface) (hC : CSideFacts) (hD : AschbacherDichotomy) {G : Type} [Group G]
      [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
      (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z),
      GzOrbitFacts a z := by
  intro hI hC hD G _ _ a z h hF1 hF2 hF3
  have hF1' : Fusion1Facts a z := hF1.self
  have hF2' : Fusion2Facts a z := hF2.self
  have hNot : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have hordA : ∀ q, IsConj a q → orderOf q = 2 := fun q hq =>
    (orderOf_eq_of_isConj_gz hq).symm.trans h.orderOf_a
  have hordB : ∀ q, IsConj z q → orderOf q = 2 := fun q hq =>
    (orderOf_eq_of_isConj_gz hq).symm.trans h.orderOf_z
  have hsq : ∀ q : G, orderOf q = 2 → q ^ 2 = 1 := fun q hq => by
    rw [← hq]; exact pow_orderOf_eq_one q
  have hGz : Nat.card ↥(Gx z) = 2 ^ 9 * 7200 := card_centralizer_z_of_isF5Type h
  have hfix : ∀ k ∈ Gx z, k * z * k⁻¹ = z := by
    intro k hk
    rw [← mem_Gx.mp hk, mul_assoc, mul_inv_cancel, mul_one]
  have hQG : ∀ q ∈ Qz z, q ∈ Gx z := fun q hq =>
    (Subgroup.map_subtype_le (CFSG.pCore 2 ↥(Gx z))) hq
  have hQinv : ∀ k ∈ Gx z, ∀ c ∈ Qz z, k * c * k⁻¹ ∈ Qz z := by
    intro k hk c hc
    have := Qz_conj_mem (x := z) k hc
    rwa [hfix k hk] at this
  have hconj : ∀ (k c : G), IsConj a c → IsConj a (k * c * k⁻¹) := fun k c hc =>
    hc.trans (isConj_iff.mpr ⟨k, rfl⟩)
  have hconjB : ∀ (k c : G), IsConj z c → IsConj z (k * c * k⁻¹) := fun k c hc =>
    hc.trans (isConj_iff.mpr ⟨k, rfl⟩)
  have hmulA : ∀ q, q ∈ Qz z → IsConj a q → IsConj a (q * z) := by
    intro q hqQ hqA
    exact hqA.trans (isConj_mul_of_mem_Qz h.cent_z h.orderOf_z (hordA q hqA)
      (fun hqz => hNot (hqz ▸ hqA)) hqQ)
  have hshQA : ∀ q ∈ Qz z, IsConj a q → IsShapeTwoTwoSixS5 ↥(Gxy z q) := by
    intro q hqQ hqA
    have hmem : z ∈ orb2AB q z q := ⟨IsConj.refl z, hqA.symm.trans (hmulA q hqQ hqA)⟩
    rw [Gxy_comm]
    exact ((hF3 q z hqA (IsConj.refl z)).shape_2AB z hmem).1
  have hcase1 : ∀ q, IsConj a q → IsConj a (q * z) → q ∈ Qz z := by
    intro q hqA hqz
    have hmem : z ∈ orb2AB q z q := ⟨IsConj.refl z, hqA.symm.trans hqz⟩
    exact ((hF3 q z hqA (IsConj.refl z)).shape_2AB z hmem).2
  have hshOut : ∀ q ∈ Gx z, q ∉ Qz z → IsConj a q →
      IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy z q) := by
    intro q hqG hqQ hqA
    obtain ⟨z₀, u, hreps⟩ := exists_pair_reps hI h hF1' hF2'
    rcases hreps q z hqA (IsConj.refl z) (mem_Gx.mp hqG).symm with ⟨hA2, -⟩ | ⟨hB2, -⟩
    · exact absurd (hcase1 q hqA hA2) hqQ
    · have hmem : z ∈ orb2BB q z q := ⟨IsConj.refl z, hB2⟩
      rw [Gxy_comm]
      exact ((hF3 q z hqA (IsConj.refl z)).shape_2BB z hmem).1
  have hstabQA : ∀ c ∈ {q | q ∈ Qz z ∧ IsConj a q}, Nat.card ↥(Gx z ⊓ Gx c) = 2 ^ 11 * 15 := by
    intro c hc
    rw [← Gxy_eq_inf, card_of_isShapeTwoTwoSixS5 (hshQA c hc.1 hc.2)]
    norm_num
  have hstabOut : ∀ c ∈ {q | q ∈ Gx z ∧ q ∉ Qz z ∧ IsConj a q},
      Nat.card ↥(Gx z ⊓ Gx c) = 2 ^ 8 * 15 := by
    intro c hc
    rw [← Gxy_eq_inf, card_of_isShapeTwoTwoTimesTwoFourA5 (hshOut c hc.1 hc.2.1 hc.2.2)]
    norm_num
  obtain ⟨z₀, u, hreps⟩ := exists_pair_reps hI h hF1' hF2'
  have hOrbQA : IsConjOrbit (Gx z) {q | q ∈ Qz z ∧ IsConj a q} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro k hk c ⟨hcQ, hcA⟩
      exact ⟨hQinv k hk c hcQ, hconj k c hcA⟩
    · obtain ⟨q, hq, hqA⟩ := exists_mem_Qz_isConj hF1'
      exact ⟨q, hq, hqA⟩
    · rintro c ⟨hcQ, hcA⟩ c' ⟨hcQ', hcA'⟩
      rcases hreps c z hcA (IsConj.refl z) (mem_Gx.mp (hQG c hcQ)).symm with
        ⟨-, g, hg1, hg2⟩ | ⟨hB, -⟩
      · rcases hreps c' z hcA' (IsConj.refl z) (mem_Gx.mp (hQG c' hcQ')).symm with
          ⟨-, g', hg1', hg2'⟩ | ⟨hB', -⟩
        · exact exists_mem_Gx_conj_gz hg1 hg1' hg2 hg2'
        · exact absurd ((hmulA c' hcQ' hcA').trans hB'.symm) hNot
      · exact absurd ((hmulA c hcQ hcA).trans hB.symm) hNot
  have hOrbOut : IsConjOrbit (Gx z) {q | q ∈ Gx z ∧ q ∉ Qz z ∧ IsConj a q} := by
    refine ⟨?_, ?_, ?_⟩
    · rintro k hk c ⟨hcG, hcQ, hcA⟩
      refine ⟨(Gx z).mul_mem ((Gx z).mul_mem hk hcG) ((Gx z).inv_mem hk), ?_, hconj k c hcA⟩
      intro hmem
      have := hQinv k⁻¹ ((Gx z).inv_mem hk) _ hmem
      have e : k⁻¹ * (k * c * k⁻¹) * k⁻¹⁻¹ = c := by group
      rw [e] at this
      exact hcQ this
    · obtain ⟨q, hqG, hqQ, hqA⟩ := exists_mem_Gx_not_mem_Qz hF1' hF2'
      exact ⟨q, hqG, hqQ, hqA⟩
    · rintro c ⟨hcG, hcQ, hcA⟩ c' ⟨hcG', hcQ', hcA'⟩
      rcases hreps c z hcA (IsConj.refl z) (mem_Gx.mp hcG).symm with
        ⟨hA2, -⟩ | ⟨-, g, hg1, hg2⟩
      · exact absurd (hcase1 c hcA hA2) hcQ
      · rcases hreps c' z hcA' (IsConj.refl z) (mem_Gx.mp hcG').symm with
          ⟨hA2', -⟩ | ⟨-, g', hg1', hg2'⟩
        · exact absurd (hcase1 c' hcA' hA2') hcQ'
        · exact exists_mem_Gx_conj_gz hg1 hg1' hg2 hg2'
  obtain ⟨q₀, hq₀Q, hq₀A⟩ := exists_mem_Qz_isConj hF1'
  have hq₀1 : q₀ ≠ 1 := by
    intro h1
    have := hordA q₀ hq₀A
    rw [h1, orderOf_one] at this
    omega
  have hirr := gz_irreducible hD h ⟨q₀, hq₀Q, hq₀1, fun h1 => hNot (h1 ▸ hq₀A),
    hshQA q₀ hq₀Q hq₀A⟩
  obtain ⟨S, hS, h0, h1⟩ := inv_classes_G hC h hirr
  have hAcard : Nat.card ↥{q | q ∈ Qz z ∧ IsConj a q} = 120 := by
    have h2 := hOrbQA.card_mul_card_stab
      (show q₀ ∈ {q | q ∈ Qz z ∧ IsConj a q} from ⟨hq₀Q, hq₀A⟩)
    rw [hstabQA q₀ ⟨hq₀Q, hq₀A⟩, hGz, show (2 : ℕ) ^ 11 * 15 = 30720 by norm_num,
      show (2 : ℕ) ^ 9 * 7200 = 3686400 by norm_num] at h2
    omega
  have hAN : {q | q ∈ Qz z ∧ IsConj a q} ⊆
      {q | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} := by
    rintro q ⟨hqQ, hqA⟩
    refine ⟨hqQ, hsq q (hordA q hqA), fun hqz => ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hqz with h3 | h3
    · have := hordA q hqA
      rw [h3, orderOf_one] at this
      omega
    · exact hNot (h3 ▸ hqA)
  have hTinv : ∀ k ∈ Gx z, ∀ t ∈ {q | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z},
      k * t * k⁻¹ ∈ {q | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} := by
    rintro k hk t ⟨htQ, htB, htz⟩
    refine ⟨hQinv k hk t htQ, hconjB k t htB, fun hkt => htz ?_⟩
    calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
      _ = k⁻¹ * z * k := by rw [hkt]
      _ = z := by simpa using hfix k⁻¹ ((Gx z).inv_mem hk)
  have hTN : {q | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} ⊆
      {q | q ∈ Qz z ∧ q ^ 2 = 1 ∧ q ∉ Subgroup.zpowers z} := by
    rintro q ⟨hqQ, hqB, hqz⟩
    refine ⟨hqQ, hsq q (hordB q hqB), fun hqz' => ?_⟩
    rcases eq_one_or_eq_of_mem_zpowers h.orderOf_z hqz' with h3 | h3
    · have := hordB q hqB
      rw [h3, orderOf_one] at this
      omega
    · exact hqz h3
  have hTA : Disjoint {q | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} {q | q ∈ Qz z ∧ IsConj a q} := by
    rw [Set.disjoint_left]
    rintro q ⟨-, hqB, -⟩ ⟨-, hqA⟩
    exact hNot (hqA.trans hqB.symm)
  have hTne : ({q | q ∈ Qz z ∧ IsConj z q ∧ q ≠ z} : Set G).Nonempty := by
    obtain ⟨v, hvQ, hvB, hvz⟩ := exists_Qz_two_B hI h hF1' hF2'
    exact ⟨v, hvQ, hvB, hvz⟩
  obtain ⟨hTorb, hTcard⟩ :=
    isConjOrbit_of_partition_compl hS h0 h1 hOrbQA hAN hAcard hTinv hTN hTA hTne
  refine ⟨hirr, ⟨hTorb, fun c hc => ?_⟩, ⟨hOrbQA, hstabQA⟩, ⟨hOrbOut, hstabOut⟩, hshQA, hshOut⟩
  have h2 := hTorb.card_mul_card_stab hc
  rw [hTcard, hGz, show (2 : ℕ) ^ 9 * 7200 = 3686400 by norm_num] at h2
  rw [show (2 : ℕ) ^ 13 * 3 = 24576 by norm_num]
  omega

end CFSG.EvenSporadicStandard.HNRecog.Section3
