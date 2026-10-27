module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611WreathC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma66

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem exists_conj_of_odd {α z' : K} (hα : α * α = 1) (hz' : z' * z' = 1)
    (hodd : Odd (orderOf (α * z'))) : ∃ g : K, g * z' * g⁻¹ = α := by
  obtain ⟨r, hr⟩ := hodd
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have hz'inv : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'
  set o := α * z' with ho
  have hinv : α * o * α⁻¹ = o⁻¹ := by
    calc α * o * α⁻¹ = (α * α) * z' * α⁻¹ := by rw [ho]; group
      _ = z' * α := by rw [hα, hαinv, one_mul]
      _ = o⁻¹ := by rw [ho, mul_inv_rev, hz'inv, hαinv]
  set g := o ^ (r + 1) with hg
  have hgg : g * g = o := by
    have h1 : o ^ (2 * r + 1) = 1 := by rw [← hr]; exact pow_orderOf_eq_one o
    calc g * g = o ^ ((r + 1) + (r + 1)) := (pow_add o (r + 1) (r + 1)).symm
      _ = o ^ ((2 * r + 1) + 1) := by congr 1; omega
      _ = o ^ (2 * r + 1) * o := pow_succ o _
      _ = o := by rw [h1, one_mul]
  have hαg : α * g * α⁻¹ = g⁻¹ := by
    calc α * g * α⁻¹ = (α * o * α⁻¹) ^ (r + 1) := by rw [hg, conj_pow]
      _ = o⁻¹ ^ (r + 1) := by rw [hinv]
      _ = g⁻¹ := by rw [hg, inv_pow]
  have hαg' : α * g = g⁻¹ * α := by
    calc α * g = (α * g * α⁻¹) * α := by group
      _ = g⁻¹ * α := by rw [hαg]
  have hz'o : z' = α * (g * g) := by
    rw [hgg, ho, ← mul_assoc, hα, one_mul]
  refine ⟨g, ?_⟩
  calc g * z' * g⁻¹ = g * (α * (g * g)) * g⁻¹ := by rw [← hz'o]
    _ = g * (α * g) := by group
    _ = g * (g⁻¹ * α) := by rw [hαg']
    _ = α := by group

theorem exists_conj_of_quotient_conj {z α : K} (hz : z * z = 1) (hα : α * α = 1)
    {n : K ⧸ fusionOddCore K}
    (hn : n * (QuotientGroup.mk z : K ⧸ fusionOddCore K) * n⁻¹ = QuotientGroup.mk α) :
    ∃ g : K, g * z * g⁻¹ = α := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective n
  have h1 : ((k * z * k⁻¹ : K) : K ⧸ fusionOddCore K) = (α : K ⧸ fusionOddCore K) := by
    rw [← hn, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have ho : α * (k * z * k⁻¹) ∈ fusionOddCore K := by
    have := QuotientGroup.eq.1 h1.symm
    rwa [hαinv] at this
  have hz' : (k * z * k⁻¹) * (k * z * k⁻¹) = 1 := by
    calc (k * z * k⁻¹) * (k * z * k⁻¹) = k * (z * z) * k⁻¹ := by group
      _ = 1 := by rw [hz]; group
  have hodd : Odd (orderOf (α * (k * z * k⁻¹))) :=
    (odd_natCard_fusionOddCore K).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
  obtain ⟨g, hg⟩ := exists_conj_of_odd hα hz' hodd
  exact ⟨g * k, by rw [← hg]; group⟩

theorem exists_noncentral_small_commutator {z α t : K} {C : Subgroup K}
    (hWreath : WreathAlt K (QuotientGroup.mk z)) (hz : z * z = 1)
    (hC2 : IsPGroup 2 C) (hC : 64 ≤ Nat.card C) (hαC : α ∈ C) (htC : t ∈ C)
    (hαcent : ∀ c ∈ C, c * α = α * c) (htcent : ∀ c ∈ C, c * t = t * c)
    (hα2 : α * α = 1) (ht2 : t * t = 1) (_hα1 : α ≠ 1) (ht1 : t ≠ 1) (_hαt : α ≠ t)
    (hzα : z * α * z⁻¹ = α * t) (hzt : z * t * z⁻¹ = t)
    (htcomm : t ∈ _root_.commutator K) (hnconj : ∀ g : K, g * z * g⁻¹ ≠ α) :
    Nat.card C = 64 ∧ ∃ p ∈ C, p ∉ (zpowers α ⊔ zpowers t : Subgroup K) ∧
      ∃ ζ ∈ (zpowers α ⊔ zpowers t : Subgroup K),
        ∀ c ∈ C, p * c * p⁻¹ * c⁻¹ = 1 ∨ p * c * p⁻¹ * c⁻¹ = ζ := by
  classical
  obtain ⟨N₁, N₂, ⟨e₁⟩, ⟨e₂⟩, hcomm, hdisj, -, hidx, hzN, hconj⟩ := hWreath
  let q : K →* K ⧸ fusionOddCore K := QuotientGroup.mk' (fusionOddCore K)
  let σ : K ⧸ fusionOddCore K := QuotientGroup.mk z
  have hσ2 : σ * σ = 1 := by
    show (QuotientGroup.mk z : K ⧸ fusionOddCore K) * QuotientGroup.mk z = 1
    rw [← QuotientGroup.mk_mul, hz, QuotientGroup.mk_one]
  have hW : WreathData N₁ N₂ σ := wreathData_of_conj hσ2 hcomm hdisj hconj
  have hqz : q z = σ := rfl
  obtain ⟨eC⟩ := exists_equiv_map_quotient hC2
  have hinj : ∀ x ∈ C, ∀ y ∈ C, q x = q y → x = y := fun x hx y hy hxy =>
    quotient_injOn_of_isPGroup hC2 hx hy hxy
  let Cb : Subgroup (K ⧸ fusionOddCore K) := C.map q
  have hCb : Nat.card Cb = Nat.card C := (Nat.card_congr eC.toEquiv).symm
  have hCb2 : IsPGroup 2 Cb := hC2.map q
  have hαb2 : q α * q α = 1 := by rw [← map_mul, hα2, map_one]
  have htb2 : q t * q t = 1 := by rw [← map_mul, ht2, map_one]
  have htb1 : q t ≠ 1 := fun h => ht1 (hinj t htC 1 C.one_mem (by rw [h, map_one]))
  have hacb : ∀ c ∈ Cb, c * q α = q α * c := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, hαcent c hc]
  have htcb : ∀ c ∈ Cb, c * q t = q t * c := by
    rintro _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul, htcent c hc]
  have hσα : σ * q α * σ⁻¹ = q α * q t := by
    calc σ * q α * σ⁻¹ = q z * q α * (q z)⁻¹ := rfl
      _ = q (z * α * z⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = q α * q t := by rw [hzα, map_mul]
  have hσt : σ * q t * σ⁻¹ = q t := by
    calc σ * q t * σ⁻¹ = q z * q t * (q z)⁻¹ := rfl
      _ = q (z * t * z⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = q t := by rw [hzt]
  have htM : q t ∈ N₁ ⊔ N₂ := by
    apply commutator_le_of_index_two hidx
    have := map_derivedSeries_le_derivedSeries q 1
    rw [derivedSeries_one, derivedSeries_one] at this
    exact this ⟨t, htcomm, rfl⟩
  have haM : q α ∈ N₁ ⊔ N₂ := by
    by_contra hnot
    obtain ⟨n, -, hn⟩ := hW.exists_conj_of_sq_eq_one hidx hzN hαb2 hnot
    obtain ⟨g, hg⟩ := exists_conj_of_quotient_conj hz hα2 hn
    exact hnconj g hg
  obtain ⟨hC64, pb, hpbC, hp1, hpa, hpt, hpat, ζb, hζb, hcommb⟩ :=
    hW.exists_small_commutator e₁ e₂ hidx hzN hCb2 (by rw [hCb]; exact hC) ⟨t, htC, rfl⟩ hacb
      htcb htb2 htb1 hσα hσt haM htM
  obtain ⟨p, hpC, rfl⟩ := hpbC
  obtain ⟨ζ, hζC, hζmem, hζq⟩ : ∃ ζ, ζ ∈ C ∧ ζ ∈ (zpowers α ⊔ zpowers t : Subgroup K) ∧
      q ζ = ζb := by
    rcases hζb with h | h
    · exact ⟨α, hαC, mem_sup_left (mem_zpowers α), h.symm⟩
    · exact ⟨α * t, C.mul_mem hαC htC,
        mul_mem (mem_sup_left (mem_zpowers α)) (mem_sup_right (mem_zpowers t)),
        by rw [map_mul, h]⟩
  have hαt' : α * t = t * α := htcent α hαC
  have hcent' : zpowers t ≤ centralizer (zpowers α : Set K) := by
    intro b hb
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hg
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow hαt' i j).eq
  refine ⟨by rw [← hCb]; exact hC64, p, hpC, ?_, ζ, hζmem, ?_⟩
  · intro hp
    obtain ⟨a', ha', b', hb', hpab⟩ := exists_mul_of_mem_sup_of_le_centralizer hcent' hp
    rcases mem_zpowers_sq_eq_one hα2 ha' with h1 | h1 <;>
      rcases mem_zpowers_sq_eq_one ht2 hb' with h2 | h2
    · exact hp1 (by rw [hpab, h1, h2, mul_one, map_one])
    · exact hpt (by rw [hpab, h1, h2, one_mul])
    · exact hpa (by rw [hpab, h1, h2, mul_one])
    · exact hpat (by rw [hpab, h1, h2, map_mul])
  · intro c hc
    have hcomm := hcommb (q c) ⟨c, hc, rfl⟩
    have hmem : p * c * p⁻¹ * c⁻¹ ∈ C :=
      C.mul_mem (C.mul_mem (C.mul_mem hpC hc) (C.inv_mem hpC)) (C.inv_mem hc)
    have hq : q (p * c * p⁻¹ * c⁻¹) = q p * q c * (q p)⁻¹ * (q c)⁻¹ := by
      simp only [map_mul, map_inv]
    rcases hcomm with h | h
    · left
      exact hinj _ hmem 1 C.one_mem (by rw [hq, h, map_one])
    · right
      exact hinj _ hmem ζ hζC (by rw [hq, h, hζq])

end CFSG.EvenSporadicStandard.Fin76b
