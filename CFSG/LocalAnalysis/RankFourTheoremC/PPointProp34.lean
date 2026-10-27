module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointBorelData
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

namespace IsPPoint

variable {M : Subgroup G} {x : G}

theorem eq_zpowers_of_isConj_three {P : Sylow 3 G} (hin : PPointThreeInputs) (hS : D1Global G)
    (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x)
    {L : Subgroup G} (hLQ : L ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G))
    (hL : Nat.card L = 3) (hLc : ∃ g : G, L = (zpowers x).map (MulAut.conj g).toMonoidHom) :
    L = zpowers x := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨n, f, W, hn, hfadd, hfinj, hfx, hxf, hWQ, hW, hW3, htor, -⟩ :=
    h.exists_borelData_three hin hS hD1 hFC hloc
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.elem.2.1] at this
  have hf0 : f 0 = 1 := by
    have h1 := hfadd 0 0
    rw [add_zero] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)
  have hFcard : 9 < Nat.card (GaloisField 3 n) := by
    rw [GaloisField.card 3 n (by omega)]
    calc 9 < 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hLW : L ≤ W := fun y hy => hW3 y (hLQ hy) (by
    have := pow_card_eq_one' (G := ↥L) (x := (⟨y, hy⟩ : L))
    rw [hL] at this
    exact congrArg Subtype.val this)
  exact eq_zpowers_of_isConj_of_le hFcard hx3 hfadd hfinj hfx hxf
    (fun t => (hW _).mpr ⟨t, 0, by norm_num, by simp⟩)
    ((hW x).mpr ⟨0, 1, by norm_num, by rw [hf0]; simp⟩)
    (fun y hy => (hW y).mp hy) htor
    (fun D hDW hDel hDcard => h.not_exists_conj_lines (by norm_num) hin.h243 hin.h244 hin.hsig hS
      hD1 hFC hloc (hDW.trans hWQ) hDel hDcard) hLW hL hLc

theorem le_centralizer_three {P : Sylow 3 G} (hin : PPointThreeInputs) (hS : D1Global G)
    (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) :
    (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hxo : orderOf x = 3 := h.elem.2.1
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hxo] at this
  have hxQ : x ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hQP : (P : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ (P : Subgroup G) := inf_le_left
  have hPQ := eq_of_isPGroup_of_le_of_normalizer P.isPGroup' hQP (fun g hgP hgN => by
    refine ⟨hgP, ?_⟩
    set L : Subgroup G := (zpowers x).map (MulAut.conj g).toMonoidHom with hL
    have hLQ : L ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzQ : z ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := zpowers_le.mpr hxQ hz
      exact (mem_normalizer_iff.mp hgN z).mp hzQ
    have hLcard : Nat.card L = 3 := by
      rw [hL, Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, hxo]
    have hLx := h.eq_zpowers_of_isConj_three hin hS hD1 hFC hloc hLQ hLcard ⟨g, rfl⟩
    have hmem : g * x * g⁻¹ ∈ zpowers x := by
      rw [← hLx]
      exact ⟨x, mem_zpowers x, rfl⟩
    show g ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    rcases mem_zpowers_of_pow_three hx3 hmem with h1 | h1 | h1
    · exfalso
      have : x = 1 := by simpa using h1
      rw [this, orderOf_one] at hxo
      omega
    · calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [h1]
    ·
      have h2 : g * x⁻¹ * g⁻¹ = x := by
        calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
          _ = x⁻¹⁻¹ := by rw [h1]
          _ = x := inv_inv x
      have hg2 : g * g * x = x * (g * g) := by
        calc g * g * x = g * (g * x * g⁻¹) * g := by group
          _ = g * x⁻¹ * g := by rw [h1]
          _ = (g * x⁻¹ * g⁻¹) * (g * g) := by group
          _ = x * (g * g) := by rw [h2]
      obtain ⟨j, hj⟩ := P.isPGroup' ⟨g, hgP⟩
      have hgj : g ^ (3 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      obtain ⟨k, hk⟩ : Odd (3 ^ j) := Odd.pow (by decide)
      have hgk : (g ^ 2) ^ k = g⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_mul, ← pow_succ]
        rwa [hk] at hgj
      have hcomm : Commute (g ^ 2) x := by
        rw [pow_two]
        exact hg2
      have h3 : Commute g⁻¹ x := hgk ▸ hcomm.pow_left k
      exact (Commute.inv_left_iff.mp h3).eq)
  intro g hg
  exact (show g ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) by rw [← hPQ]; exact hg).2

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
