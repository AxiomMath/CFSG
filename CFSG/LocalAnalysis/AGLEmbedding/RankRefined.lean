module

import CFSG.LocalAnalysis.AGLEmbedding.RankRefinedAux
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section RankRefined

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem div_two_add_one_le_pRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (B Z₀ : Subgroup Γ)
    (N : ℕ) (hB : IsPGroup p B) (hZB : Z₀ ≤ B) (hZc : Z₀ ≤ Subgroup.centralizer (B : Set Γ))
    (hcyc : IsCyclic Z₀) (hpow : ∀ b ∈ B, b ^ p ∈ Z₀)
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ Z₀) (hN : 1 ≤ N)
    (hidx : p ^ N ≤ Z₀.relIndex B) : N / 2 + 1 ≤ Open.pRank p B := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hZ1 : Z₀ = ⊥
  ·
    subst hZ1
    have hBel : IsElemAbelian p B := by
      refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun b hb => by simpa using hpow b hb⟩
      have h := hcomm y y.2 x x.2
      rw [Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hB
    rw [Subgroup.relIndex_bot_left, hm] at hidx
    have hmN : N ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).mp hidx
    have : m ≤ Open.pRank p B :=
      le_csSup (pRank_bddAbove p hp B) ⟨B, le_rfl, hBel, hm⟩
    omega
  obtain ⟨⟨g, hgZ⟩, hgen⟩ := hcyc.exists_generator
  have hZ0 : Z₀ = Subgroup.zpowers g := by
    ext z
    constructor
    · intro hz
      obtain ⟨k, hk⟩ := hgen ⟨z, hz⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨k, rfl⟩
      exact Z₀.zpow_mem hgZ k
  set Zp : Subgroup Γ := Subgroup.zpowers (g ^ p) with hZpdef
  have hZpZ : Zp ≤ Z₀ := (Subgroup.zpowers_le).mpr (Z₀.pow_mem hgZ p)
  have hpowZp : ∀ z ∈ Z₀, z ^ p ∈ Zp := by
    intro z hz
    rw [hZ0] at hz
    obtain ⟨k, rfl⟩ := hz
    exact ⟨k, by simp only [← zpow_natCast, ← zpow_mul]; ring_nf⟩
  have hgp : IsPGroup p (Subgroup.zpowers g) := hZ0 ▸ hB.to_le hZB
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hgp ⟨g, Subgroup.mem_zpowers g⟩
  have ha' : orderOf g = p ^ a := by rw [← ha, Subgroup.orderOf_mk]
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hg1 : g = 1 := orderOf_eq_one_iff.mp (by simpa using ha')
    exact hZ1 (by rw [hZ0, hg1, Subgroup.zpowers_one_eq_bot])
  have hZpidx : Zp.relIndex Z₀ = p := by
    have hordp : orderOf (g ^ p) = p ^ (a - 1) := by
      rw [orderOf_pow_of_dvd hp.ne_zero (by rw [ha']; exact dvd_pow_self p ha0), ha']
      have h3 : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ]; congr 1; omega
      rw [h3, Nat.mul_div_cancel _ hp.pos]
    have h1 := Subgroup.relIndex_mul_card Zp Z₀
    rw [inf_of_le_left hZpZ, hZpdef, Nat.card_zpowers, hordp, hZ0, Nat.card_zpowers, ha'] at h1
    have h2 : p ^ a = p * p ^ (a - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2] at h1
    rw [hZpdef, hZ0]
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h1
  have hmul : ∀ a ∈ B, ∀ b ∈ B, (a * b) ^ p = a ^ p * b ^ p := fun a ha b hb =>
    mul_pow_prime_of_classTwo hp hp2 hZc hpow hcomm ha hb
  let B₀ : Subgroup Γ :=
    { carrier := {b | b ∈ B ∧ b ^ p ∈ Zp}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        exact ⟨B.mul_mem ha hb, by rw [hmul a ha b hb]; exact Zp.mul_mem hap hbp⟩
      one_mem' := ⟨B.one_mem, by rw [one_pow]; exact Zp.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        exact ⟨B.inv_mem ha, by rw [inv_pow]; exact Zp.inv_mem hap⟩ }
  have hB₀B : B₀ ≤ B := fun b hb => hb.1
  have hZB₀ : Z₀ ≤ B₀ := fun z hz => ⟨hZB hz, hpowZp z hz⟩
  let φ : B →* Z₀ :=
    { toFun := fun b => ⟨(b : Γ) ^ p, hpow b b.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; exact hmul a a.2 b b.2 }
  have hB₀idx : B₀.relIndex B ≤ Zp.relIndex Z₀ := by
    have hcomap : B₀.subgroupOf B = (Zp.subgroupOf Z₀).comap φ := by
      ext b
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
      exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap, Subgroup.relIndex]
    have h0 : (Zp.subgroupOf Z₀).relIndex ⊤ ≠ 0 := by
      rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
    have := Subgroup.relIndex_le_of_le_right (le_top : φ.range ≤ ⊤) h0
    rwa [Subgroup.relIndex_top_right] at this
  have htow := Subgroup.relIndex_mul_relIndex Z₀ B₀ B hZB₀ hB₀B
  have hB₀Z : p ^ (N - 1) ≤ Z₀.relIndex B₀ := by
    have h1 : p ^ N ≤ Z₀.relIndex B₀ * p := by
      calc p ^ N ≤ Z₀.relIndex B := hidx
        _ = Z₀.relIndex B₀ * B₀.relIndex B := htow.symm
        _ ≤ Z₀.relIndex B₀ * p := Nat.mul_le_mul_left _ (hB₀idx.trans hZpidx.le)
    have h2 : p ^ N = p ^ (N - 1) * p := by rw [← pow_succ]; congr 1; omega
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  have hcB₀ : Z₀ ≤ Subgroup.centralizer (B₀ : Set Γ) := hZc.trans (Subgroup.centralizer_le hB₀B)
  obtain ⟨A, hZA, hAB₀, hAab, hA⟩ := exists_abelian_relIndex_sq (p := p)
    (cyclicOmegaOne p Z₀ hcyc) (card_cyclicOmegaOne_le hp.pos Z₀ hcyc) _ B₀ Z₀ rfl
    (hB.to_le hB₀B) hZB₀ hcB₀ (fun z hz => hz.1) (fun b hb => hpow b hb.1)
    (fun a ha b hb => ⟨hcomm a ha.1 b hb.1, commutator_pow_eq_one_of_central hZc hpow hcomm ha.1
      hb.1⟩)
  obtain ⟨s, hs⟩ := exists_relIndex_eq_pow_of_isPGroup (H := Z₀) (hB.to_le (hAB₀.trans hB₀B))
  have hNs : N - 1 ≤ 2 * s := by
    have h1 : p ^ (N - 1) ≤ p ^ (2 * s) := by
      calc p ^ (N - 1) ≤ Z₀.relIndex B₀ := hB₀Z
        _ ≤ (Z₀.relIndex A) ^ 2 := hA
        _ = p ^ (2 * s) := by rw [hs, ← pow_mul, mul_comm]
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  have hrank : s + 1 ≤ Open.pRank p A := by
    refine le_pRank_of_pow_mem hp A Zp hAab (fun a ha => (hAB₀ ha).2) ?_
    have htow2 := Subgroup.relIndex_mul_relIndex Zp Z₀ A hZpZ hZA
    change p ^ (s + 1) ≤ Zp.relIndex A
    rw [← htow2, hZpidx, hs, pow_succ, mul_comm]
  have hmono := pRank_mono p hp (hAB₀.trans hB₀B)
  omega

end RankRefined

end CFSG.AGLEmbedding
