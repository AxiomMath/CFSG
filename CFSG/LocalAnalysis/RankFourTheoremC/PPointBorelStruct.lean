module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointBorelData
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure BorelData3 (P : Sylow 3 G) (M : Subgroup G) (x : G) {n : ℕ} (f : GaloisField 3 n → G)
    (W : Subgroup G) : Prop where
  three_le : 3 ≤ n
  f_add : ∀ s t, f (s + t) = f s * f t
  f_inj : Function.Injective f
  f_comm : ∀ t, f t * x = x * f t
  f_ne : ∀ t, f t ≠ x
  le : W ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G)
  mem_iff : ∀ g, g ∈ W ↔ ∃ (t : GaloisField 3 n) (i : ℕ), i < 3 ∧ g = f t * x ^ i
  of_pow_three : ∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ 3 = 1 → y ∈ W
  torus : ∀ a : (GaloisField 3 n)ˣ, ∃ g : G, g * x * g⁻¹ = x ∧
    ∀ t, g * f t * g⁻¹ = f ((a : GaloisField 3 n) ^ 2 * t)
  x_pow : x ^ 3 = 1
  x_ne_one : x ≠ 1
  x_mem : x ∈ (P : Subgroup G)
  reduced : ∃ (R : Sylow 3 (RedCent 3 x)) (K : Subgroup (RedCent 3 x))
      (d : TauCeti.ValidLieTypeIndex),
    PPointFacts 3 M x R K (.lie d) ∧ IsLinTwoIndex 3 n d ∧ Nonempty (K ≃* PSL2GF 3 n) ∧
    (∀ t, ∃ hc : f t ∈ centralizer ({x} : Set G),
      QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨f t, hc⟩ ∈ (R : Subgroup (RedCent 3 x)) ⊓ K ∧
      (t ≠ 0 → QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨f t, hc⟩ ≠ 1)) ∧
    (∀ k ∈ (R : Subgroup (RedCent 3 x)) ⊓ K, ∃ (t : GaloisField 3 n)
      (hc : f t ∈ centralizer ({x} : Set G)),
      QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨f t, hc⟩ = k) ∧
    (∀ σ ∈ K, σ ∈ normalizer (((R : Subgroup (RedCent 3 x)) ⊓ K : Subgroup (RedCent 3 x)) :
        Set (RedCent 3 x)) → ∃ b : (GaloisField 3 n)ˣ, ∀ (t : GaloisField 3 n)
      (hc : f t ∈ centralizer ({x} : Set G))
      (hc' : f ((b : GaloisField 3 n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
      σ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨f t, hc⟩ * σ⁻¹ = QuotientGroup.mk'
          (primeComplementCore (G := centralizer ({x} : Set G)) 3)
          ⟨f ((b : GaloisField 3 n) ^ 2 * t), hc'⟩) ∧
    (∀ a : (GaloisField 3 n)ˣ, ∃ τ ∈ K, τ ∈ normalizer (((R : Subgroup (RedCent 3 x)) ⊓ K :
        Subgroup (RedCent 3 x)) : Set (RedCent 3 x)) ∧ ∀ (t : GaloisField 3 n)
      (hc : f t ∈ centralizer ({x} : Set G))
      (hc' : f ((a : GaloisField 3 n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
      τ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
        ⟨f t, hc⟩ * τ⁻¹ = QuotientGroup.mk'
          (primeComplementCore (G := centralizer ({x} : Set G)) 3)
          ⟨f ((a : GaloisField 3 n) ^ 2 * t), hc'⟩) ∧
        (R : Subgroup (RedCent 3 x)) =
          (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
            (centralizer ({x} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3))

namespace IsPPoint

variable {M : Subgroup G} {x : G}

theorem exists_borelData3 {P : Sylow 3 G} (hin : PPointThreeInputs) (hS : D1Global G)
    (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) :
    ∃ (n : ℕ) (f : GaloisField 3 n → G) (W : Subgroup G), BorelData3 P M x f W := by
  obtain ⟨n, f, W, hn, hfadd, hfinj, hfx, hxf, hWQ, hW, hW3, htor, hred⟩ :=
    h.exists_borelData_three hin hS hD1 hFC hloc
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.elem.2.1] at this
  have hx1 : x ≠ 1 := by
    intro h1
    have := h.elem.2.1
    rw [h1, orderOf_one] at this
    omega
  exact ⟨n, f, W, ⟨hn, hfadd, hfinj, hfx, hxf, hWQ, hW, hW3, htor, hx3, hx1, h.mem, hred⟩⟩

end IsPPoint

namespace BorelData3

variable {P : Sylow 3 G} {M : Subgroup G} {x : G} {n : ℕ} {f : GaloisField 3 n → G}
  {W : Subgroup G}

theorem f_zero (hB : BorelData3 P M x f W) : f 0 = 1 := by
  have h1 := hB.f_add 0 0
  rw [add_zero] at h1
  exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)

theorem f_pow_three (hB : BorelData3 P M x f W) (t : GaloisField 3 n) : f t ^ 3 = 1 := by
  have h3F : (3 : GaloisField 3 n) = 0 := by exact_mod_cast CharP.cast_eq_zero (GaloisField 3 n) 3
  have h1 : t + t + t = 0 := by linear_combination t * h3F
  calc f t ^ 3 = f t * f t * f t := by simp only [pow_succ, pow_zero, one_mul]
    _ = f (t + t + t) := by rw [hB.f_add, hB.f_add]
    _ = 1 := by rw [h1, hB.f_zero]

theorem f_neg (hB : BorelData3 P M x f W) (t : GaloisField 3 n) : f (-t) = (f t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hB.f_add, neg_add_cancel, hB.f_zero]

theorem f_mem_W (hB : BorelData3 P M x f W) (t : GaloisField 3 n) : f t ∈ W :=
  (hB.mem_iff _).mpr ⟨t, 0, by norm_num, by simp⟩

theorem x_mem_W (hB : BorelData3 P M x f W) : x ∈ W :=
  (hB.mem_iff _).mpr ⟨0, 1, by norm_num, by simp [hB.f_zero]⟩

theorem f_not_mem_zpowers (hB : BorelData3 P M x f W) {t : GaloisField 3 n} (ht : t ≠ 0) :
    f t ∉ zpowers x := by
  intro hmem
  have hf1 : f t ≠ 1 := fun h1 => ht (hB.f_inj (h1.trans hB.f_zero.symm))
  have hfo : orderOf (f t) = 3 := orderOf_eq_prime (hB.f_pow_three t) hf1
  have hxo : orderOf x = 3 := orderOf_eq_prime hB.x_pow hB.x_ne_one
  have heq : zpowers (f t) = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmem) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hfo, hxo])
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers x : x ∈ zpowers (f t))
  have h3 : (f t) ^ (3 : ℤ) = 1 := by exact_mod_cast hB.f_pow_three t
  have hk' : (f t) ^ (k % 3) = x := by
    rw [← hk]
    conv_rhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk'
    exact hB.x_ne_one hk'.symm
  · rw [h1, zpow_one] at hk'
    exact hB.f_ne t hk'
  · rw [h2] at hk'
    refine hB.f_ne (-t) ?_
    rw [hB.f_neg, ← hk']
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← zpow_add_one]
    norm_num [h3]

@[expose] def plane (x : G) (f : GaloisField 3 n → G) (t₀ : GaloisField 3 n) : Subgroup G :=
  zpowers x ⊔ zpowers (f t₀)

omit [Finite G] in
theorem x_mem_plane (x : G) (f : GaloisField 3 n → G) (t₀ : GaloisField 3 n) :
    x ∈ plane x f t₀ := mem_sup_left (mem_zpowers x)

omit [Finite G] in
theorem f_mem_plane (x : G) (f : GaloisField 3 n → G) (t₀ : GaloisField 3 n) :
    f t₀ ∈ plane x f t₀ := mem_sup_right (mem_zpowers _)

theorem plane_le (hB : BorelData3 P M x f W) (t₀ : GaloisField 3 n) : plane x f t₀ ≤ W :=
  sup_le (zpowers_le.mpr hB.x_mem_W) (zpowers_le.mpr (hB.f_mem_W t₀))

theorem plane_le_inf (hB : BorelData3 P M x f W) (t₀ : GaloisField 3 n) :
    plane x f t₀ ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
  (hB.plane_le t₀).trans hB.le

theorem plane_isElemAbelian (hB : BorelData3 P M x f W) (t₀ : GaloisField 3 n) :
    IsElemAbelian 3 (plane x f t₀) := by
  refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3
    (isElemAbelian_zpowers hB.x_pow) (isElemAbelian_zpowers (hB.f_pow_three t₀)) ?_
  rw [zpowers_le]
  refine mem_centralizer_iff.mpr fun b hb => ?_
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  exact (Commute.zpow_left (show Commute (f t₀) x from hB.f_comm t₀) k).eq

theorem plane_card (hB : BorelData3 P M x f W) {t₀ : GaloisField 3 n} (ht₀ : t₀ ≠ 0) :
    Nat.card (plane x f t₀) = 3 ^ 2 := by
  have hxo : orderOf x = 3 := orderOf_eq_prime hB.x_pow hB.x_ne_one
  have hcomm : ∀ e ∈ zpowers x, e * f t₀ = f t₀ * e := fun e he => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute x (f t₀) from (hB.f_comm t₀).symm) k).eq
  rw [plane, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers x)
    (hB.f_pow_three t₀) (hB.f_not_mem_zpowers ht₀) hcomm, Nat.card_zpowers, hxo]
  ring

end BorelData3

end CFSG.LocalAnalysis.RankFourTheoremC
