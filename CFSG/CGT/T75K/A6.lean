module

public import CFSG.CGT.T75K.A6Num
public import CFSG.CGT.T75K.A6Cent
public import CFSG.CGT.T75K.A6Pair

public section

namespace CFSG.CGT.T75K

open CFSG.Open CFSG.CGT.Timmesfeld75

theorem sec63A6_of_inputs (h215 : Lemma215Stmt) (h26 : Lemma26Input) : Sec63A6 := by
  intro G _ T T₁ n m x T₃ cfg hF hA6
  have hc := cfg.ctx
  have hfin := hc.finite
  obtain ⟨hm1, hTA⟩ := a6_numerics h215 h26 hc cfg hF (hA6 : _)
  subst hm1
  have hbig := cfg.big
  have hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1 := by
    rcases hc.hcase with h | h | h
    · omega
    · exact h
    · have := h.1
      omega
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun y hy => (mem_normIn.1 hy).2
  have hHN : hSub T (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) := hSub_le_normalizer hL₁N
  obtain ⟨D⟩ := NaturalSL.toLinData left_le_hSub hHN hnat
  have hx := cfg.x_mem_normIn
  have hx1 := cfg.x_ne_one
  have hwc := cfg.sec3.cfg
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 hx).2
  have hx2 : x * x = 1 := elemAbelian_mul_self hwc.wc₁.1 (normIn_le _ _ hx)
  have hAc : T ⊓ Subgroup.centralizer ({x} : Set G) = normIn T T₃ :=
    hwc.inf_centralizer_eq_normIn hx hx1
  have hcard : Nat.card T = 4 * Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [hAc]
    exact hTA
  have h8 : 8 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [hAc]
    omega
  have hFc : Nat.card (GaloisField 2 1) = 2 := by
    rw [card_F hc]
    norm_num
  obtain ⟨Lm, p, a₀, g, hp, hp1, hpLm, ha₀, ha₀Lm, hgH, hgx, hfix, hmove⟩ :=
    exists_centralizing D hFc hwc.wc.1 (fun f hf h hh => mul_mul_inv_mem_hSub hf hh) hxN hx2
      hcard h8
  rw [hAc] at hp ha₀
  have hgcent : g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hgx
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hgT₃ : g ∈ Subgroup.normalizer (T₃ : Set G) :=
    hwc.wc₁.centralizer_le_normalizer cfg.mem hx1 hgcent
  have hgT : g ∈ Subgroup.normalizer (T : Set G) := hHN hgH
  exact final_contra hwc cfg.sec3.card_normIn_swap hTA hp hp1 hpLm ha₀ ha₀Lm hgT hgT₃ hfix hmove

end CFSG.CGT.T75K
