module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Fusion

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)

variable {G : Type} [Group G] [Finite G]

section Sylow

variable {L : Subgroup G} {Ω : Type} [Group Ω] [Finite Ω] {M : Subgroup Ω}
  {φ : normalizer (L : Set G) →* Ω}

theorem rightConjugate_eq_of_fusionModel_odd {T : Subgroup Ω} (hD : FusionModel M T)
    (hφ : IsActionHom L M φ) (hφT : φ.range ≤ T) (hZodd : Odd (Nat.card (center ↥L)))
    (hCL : Odd (Nat.card (centralizer (L : Set G)))) {z : G} (hz : orderOf z = 2)
    (hzL : centralizer ({z} : Set G) ≤ normalizer (L : Set G)) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hSz : S ≤ centralizer ({z} : Set G)) {g : G}
    (hg : z ∈ normalizer (rightConjugate L g : Set G)) : rightConjugate L g = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY := le_range_actionHom hφ
  have hzN : z ∈ normalizer (L : Set G) := hzL (mem_centralizer_singleton_iff.mpr rfl)
  have hSN : S ≤ normalizer (L : Set G) := hSz.trans hzL
  set t := g * z * g⁻¹ with ht
  have htN : t ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp hg (g⁻¹ * x * g)
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff] at h1
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group,
      show g * (z * (g⁻¹ * x * g) * z⁻¹) * g⁻¹ = t * x * t⁻¹ by rw [ht]; group] at h1
  have ht2 : orderOf t = 2 := by
    rw [ht, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hz
  have htsq : t ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  set tN : normalizer (L : Set G) := ⟨t, htN⟩ with htNdef
  set zN : normalizer (L : Set G) := ⟨z, hzN⟩ with hzNdef
  have hσ := orderOf_actionHom hφ hCL (r := zN) hz
  have hτ := orderOf_actionHom hφ hCL (r := tN) ht2
  have hσc := not_two_dvd_relIndex_of_sylow (φ := φ) hzL hS hSz
  have hτc : ¬ 2 ∣ (centralizer ({φ tN} : Set Ω)).relIndex φ.range := by
    intro h2
    obtain ⟨p, hp, -, hpσ, x, hx, hx1, hxp, hxN⟩ :=
      hD.fusion _ hMY hφT (φ zN) ⟨_, rfl⟩ (φ tN) ⟨_, rfl⟩ hσ hτ hσc h2
    have : Fact p.Prime := ⟨hp⟩
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    obtain ⟨h, hhL, hhx, hht⟩ := exists_lift_commute hφ hZodd (t := tN) htsq hx.1
      (mem_centralizer_singleton_iff.mp hx.2)
    set m := ordCompl[p] (orderOf h) with hm
    set e := (orderOf h).factorization p with he
    have hhN : h ∈ normalizer (L : Set G) := le_normalizer hhL
    have hu1 : (h ^ m) ^ p ^ e = 1 := by
      rw [← pow_mul, hm, he, mul_comm, Nat.ordProj_mul_ordCompl_eq_self, pow_orderOf_eq_one]
    have huL : h ^ m ∈ L := pow_mem hhL m
    have hφu : φ ⟨h ^ m, pow_mem hhN m⟩ = x ^ m := by
      rw [show (⟨h ^ m, pow_mem hhN m⟩ : normalizer (L : Set G)) = ⟨h, hhN⟩ ^ m from
        Subtype.ext (by simp), map_pow, hhx]
    have hcop : m.Coprime (orderOf x) := by
      rw [hxo]
      exact (Nat.coprime_ordCompl hp (orderOf_pos h).ne').symm
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
    have hct : g⁻¹⁻¹ * z * g⁻¹ = t := by rw [inv_inv]
    have hut : h ^ m ∈ centralizer ({g⁻¹⁻¹ * z * g⁻¹} : Set G) := by
      rw [hct, mem_centralizer_singleton_iff]
      exact (Commute.pow_left hht m).eq
    refine false_of_pElement hCL hzL (c := g⁻¹) hp ?_ huL hut hu1 ?_
    ·
      rw [relIndex_centralizer_eq_card_map hφ hzL]
      intro hdvd
      apply hpσ
      refine hdvd.trans (card_dvd_of_le ?_)
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨hφT ⟨n, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_subgroupOf.mp hn))
    ·
      rw [hct]
      intro N' hN'le hN'n hN'o huN'
      have hN'N : N' ≤ normalizer (L : Set G) := fun n hn => le_normalizer (hN'le hn).1
      refine hxN ((N'.subgroupOf (normalizer (L : Set G))).map φ) ?_ ?_ ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        replace hn : (n : G) ∈ N' := hn
        refine ⟨hφ.map_mem _ (hN'le hn).1, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (hN'le hn).2)
      · intro y hy
        obtain ⟨k', hk'L, hk'y, hk't⟩ := exists_lift_commute hφ hZodd (t := tN) htsq hy.1
          (mem_centralizer_singleton_iff.mp hy.2)
        have hk'N' : k' ∈ normalizer (N' : Set G) :=
          hN'n ⟨hk'L, mem_centralizer_singleton_iff.mpr hk't⟩
        rw [← hk'y]
        refine AS76b.mem_normalizer_of_map_conj_le ?_
        rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
        refine ⟨⟨k', le_normalizer hk'L⟩ * n * ⟨k', le_normalizer hk'L⟩⁻¹, ?_, ?_⟩
        · replace hn : (n : G) ∈ N' := hn
          show k' * (n : G) * k'⁻¹ ∈ N'
          exact (mem_normalizer_iff.mp hk'N' n).mp hn
        · simp [MulAut.conj_apply]
      · exact hN'o.of_dvd_nat ((card_map_dvd _ _).trans
          (dvd_of_eq (Nat.card_congr (subgroupOfEquivOfLe hN'N).toEquiv)))
      · rw [← hk]
        refine pow_mem ?_ k
        rw [← hφu]
        exact ⟨⟨h ^ m, pow_mem hhN m⟩, mem_subgroupOf.mpr huN', rfl⟩
  obtain ⟨P, hPN, hPt⟩ := exists_isSylowOf_le_centralizer (N := normalizer (L : Set G))
    (H := ((centralizer ({φ tN} : Set Ω)).comap φ).map (normalizer (L : Set G)).subtype)
    (K := centralizer (L : Set G)) (map_subtype_le _) (by
      change ¬ 2 ∣ ((((centralizer ({φ tN} : Set Ω)).comap φ).map
        (normalizer (L : Set G)).subtype).subgroupOf (normalizer (L : Set G))).index
      rw [subgroupOf, comap_map_eq_self_of_injective (normalizer (L : Set G)).subtype_injective,
        index_comap]
      exact hτc)
    ⟨tN, mem_centralizer_singleton_iff.mpr rfl, rfl⟩ htsq hCL (by
      rintro _ ⟨n, hn, rfl⟩
      have h1 : φ (n * tN * n⁻¹ * tN⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, mem_comap.mp hn |>
          mem_centralizer_singleton_iff.mp]
        group
      exact (hφ.eq_one_iff _).mp h1)
  have hNodd : ¬ 2 ∣ (normalizer (L : Set G)).relIndex ⊤ := by
    have h1 := hS
    rw [isSylowOf_iff] at h1
    intro h2
    apply h1.2.2
    rw [← relIndex_mul_relIndex S _ ⊤ hSN le_top]
    exact h2.mul_left _
  have hPG : IsSylowOf 2 P ⊤ := by
    rw [isSylowOf_iff] at hPN ⊢
    refine ⟨le_top, hPN.2.1, fun h2 => ?_⟩
    rw [← relIndex_mul_relIndex P _ ⊤ hPN.1 le_top] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · exact hPN.2.2 h
    · exact hNodd h
  have hS'G : IsSylowOf 2 (rightConjugate P g) ⊤ := by
    have h := AschbacherTheorem3.isSylowOf_rightConjugate hPG g
    rwa [rightConjugate_top] at h
  have hPt' : P ≤ centralizer ({t} : Set G) := hPt
  have hS'z : rightConjugate P g ≤ centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := mem_centralizer_singleton_iff.mp (hPt' hx)
    rw [mem_centralizer_singleton_iff]
    have e : x * z = g⁻¹ * ((g * x * g⁻¹) * t) * g := by rw [ht]; group
    have e' : z * x = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [ht]; group
    rw [e, e', h1]
  have hS'L : rightConjugate P g ≤ normalizer (rightConjugate L g : Set G) :=
    rightConjugate_le_normalizer_rightConjugate hPN.le g
  exact rightConjugate_eq_of_sylow_le hz hzL
    (fun S' hS' hS'z => card_centerIn_of_fusionModel hD hφ hφT hCL hS' (hS'z.trans hzL))
    hS'G hS'z hS'L

end Sylow

end CFSG.ComponentClassification.AS81
