module

public import CFSG.ClassicalInvolution.Asc77.AscT7ERNoFour
public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.Asc77.AscT7L2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

namespace C25X

section Comm

variable {G : Type} [Group G]

def commNormSub (N : Subgroup G) (c : G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (N : Set G) ∧ ⁅c, x⁆ ∈ N}
  one_mem' := ⟨Subgroup.one_mem _, by simp [commutatorElement_def]⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Subgroup.mul_mem _ hx hy, ?_⟩
    have e : ⁅c, x * y⁆ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem hx' ((Subgroup.mem_normalizer_iff.mp hx _).mp hy')
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨Subgroup.inv_mem _ hx, ?_⟩
    have e : ⁅c, x⁻¹⁆ = x⁻¹ * ⁅c, x⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have h1 : ⁅c, x⁆⁻¹ ∈ N := N.inv_mem hx'
    have h2 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) _).mp h1
    simpa using h2

theorem comm_mem_of_mem_zpowers {N : Subgroup G} {c u : G}
    (huN : u ∈ Subgroup.normalizer (N : Set G)) (h : ⁅c, u⁆ ∈ N) {r : G}
    (hr : r ∈ Subgroup.zpowers u) : ⁅c, r⁆ ∈ N :=
  ((Subgroup.zpowers_le (H := commNormSub N c)).mpr ⟨huN, h⟩) hr |>.2

end Comm

section NC4

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G}


theorem toBar_conj_odd {a x n : G} (hx : x ∈ exactLayer Ω a)
    (hn : n ∈ oddCoreOf (exactLayer Ω a)) (hxn : n * x * n⁻¹ ∈ exactLayer Ω a) :
    T7H.toBar Ω a (n * x * n⁻¹) hxn = T7H.toBar Ω a x hx := by
  obtain ⟨n', hn', hnn⟩ := Subgroup.mem_map.mp hn
  have hnn' : (n' : G) = n := hnn
  subst hnn'
  unfold T7H.toBar
  have h1 : (⟨(n' : G) * x * (n' : G)⁻¹, hxn⟩ : ↥(exactLayer Ω a)) = n' * ⟨x, hx⟩ * n'⁻¹ :=
    rfl
  have h3 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω a)) n' = 1 :=
    (QuotientGroup.eq_one_iff n').mpr hn'
  rw [h1, map_mul, map_mul, map_inv, h3]
  simp

theorem nc4_layer_excl {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) :
    ∀ {J₁ J₂ : Subgroup (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a))},
      J₁ ∈ oddQuotientFamily (exactPair Ω a) → J₂ ∈ oddQuotientFamily (exactPair Ω a) →
      ∀ {y z₂ : ↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a)},
        y ∈ J₁ → y * y * y * y = 1 → y * y ≠ 1 → z₂ ∈ J₂ → z₂ * z₂ = 1 → z₂ ≠ 1 →
        z₂ ≠ y * y → z₂ * y = y * z₂ → False := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hzK : IsUniqueInvolution K z := hs.hz
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  set Y := exactLayer Ω a with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  intro J₁ J₂ hJ₁ hJ₂ y z₂ hy hy4 hy2 hz₂ hz₂2 hz₂1 hne hcomm
  obtain ⟨M₁, hM₁tq, rfl⟩ := T7H.exists_exactImg_of_mem hJ₁
  obtain ⟨M₂, hM₂tq, rfl⟩ := T7H.exists_exactImg_of_mem hJ₂
  obtain ⟨g₁, hg₁⟩ := hst.trans M₁ hM₁tq.1
  obtain ⟨g₂, hg₂⟩ := hst.trans M₂ hM₂tq.1
  have hzM₁ : IsUniqueInvolution M₁ (g₁ * z * g₁⁻¹) := by
    rw [← hg₁]
    exact hzK.conj g₁
  have hzM₂ : IsUniqueInvolution M₂ (g₂ * z * g₂⁻¹) := by
    rw [← hg₂]
    exact hzK.conj g₂
  have hzMY₁ : g₁ * z * g₁⁻¹ ∈ Y :=
    exactCore_le_exactLayer hM₁tq
      (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hM₁tq hzM₁).mem
  have hzMY₂ : g₂ * z * g₂⁻¹ ∈ Y :=
    exactCore_le_exactLayer hM₂tq
      (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hM₂tq hzM₂).mem
  have hbar₁ := T7H.exactImg_isUnique hp hΩ hcpg hM₁tq hzM₁ hzMY₁
  have hbar₂ := T7H.exactImg_isUnique hp hΩ hcpg hM₂tq hzM₂ hzMY₂
  have hz₂eq : z₂ = T7H.toBar Ω a (g₂ * z * g₂⁻¹) hzMY₂ :=
    (hbar₂.unique z₂ hz₂ hz₂2).resolve_left hz₂1
  have hyy : y * y = T7H.toBar Ω a (g₁ * z * g₁⁻¹) hzMY₁ := by
    refine (hbar₁.unique (y * y) ((T7H.exactImg Ω a M₁).mul_mem hy hy) ?_).resolve_left hy2
    calc y * y * (y * y) = y * y * y * y := by simp only [mul_assoc]
      _ = 1 := hy4
  obtain ⟨c, hcmem, hcy⟩ := Subgroup.mem_map.mp hy
  have hcM : (c : G) ∈ exactCore a M₁ := Subgroup.mem_subgroupOf.mp hcmem
  have hy_ord : orderOf y = 4 := by
    have h4 : y ^ 2 ^ (1 + 1) = 1 := by
      have : y ^ 2 ^ (1 + 1) = y * y * y * y := by simp [pow_succ, mul_assoc]
      rw [this]
      exact hy4
    have h2 : ¬ y ^ 2 ^ 1 = 1 := by simpa [pow_two] using hy2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
    simpa using this
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  set c' : ↥Y := c ^ m with hc'
  have hc'k : c' ^ (2 ^ k) = 1 := by
    rw [hc', ← pow_mul, mul_comm, ← hkm]
    exact pow_orderOf_eq_one c
  have hπc' : QuotientGroup.mk' N₀ c' = y ^ m := by
    rw [hc', map_pow, hcy]
  have hcop : Nat.Coprime (orderOf y) m := by
    rw [hy_ord]
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have hym_ord : orderOf (y ^ m) = 4 := by
    rw [Nat.Coprime.orderOf_pow hcop, hy_ord]
  have hy44 : y ^ 4 = 1 := by
    rw [← hy_ord]
    exact pow_orderOf_eq_one y
  have hc'4 : c' ^ 4 = 1 := by
    have h1 : c' ^ 4 ∈ N₀ := by
      have h0 : QuotientGroup.mk' N₀ (c' ^ 4) = 1 := by
        rw [map_pow, hπc', ← pow_mul, mul_comm, pow_mul, hy44, one_pow]
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ Nat.card N₀ := orderOf_dvd_natCard _
    have h3 : orderOf (⟨c' ^ 4, h1⟩ : N₀) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      refine orderOf_dvd_of_pow_eq_one ?_
      show (c' ^ 4) ^ (2 ^ k) = 1
      rw [← pow_mul, mul_comm, pow_mul, hc'k, one_pow]
    have h4 : Nat.Coprime (2 ^ k) (Nat.card N₀) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN₀odd)
    have h5 : orderOf (⟨c' ^ 4, h1⟩ : N₀) = 1 := Nat.eq_one_of_dvd_coprimes h4 h3 h2
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
  have hc'2 : ¬ c' ^ 2 ^ 1 = 1 := by
    intro h'
    have h'' : c' ^ 2 = 1 := by simpa using h'
    have h3 : (y ^ m) ^ 2 = 1 := by
      rw [← hπc', ← map_pow, h'', map_one]
    have h4 : orderOf (y ^ m) ∣ 2 := orderOf_dvd_of_pow_eq_one h3
    rw [hym_ord] at h4
    omega
  have hc'_ord : orderOf c' = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hc'2 (by simpa using hc'4)
    simpa using this
  set y₁ : G := (c' : G) with hy₁
  have hy₁M : y₁ ∈ M₁ :=
    exactCore_le_left a M₁ ((exactCore a M₁).pow_mem hcM m)
  have hy₁Y : y₁ ∈ Y := c'.2
  have hy₁4 : orderOf y₁ = 4 := by rw [hy₁, Subgroup.orderOf_coe]; exact hc'_ord
  have hcom : ⁅g₂ * z * g₂⁻¹, y₁⁆ ∈ oddCoreOf Y := by
    have h1 : (⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) * c' * (c' * ⟨g₂ * z * g₂⁻¹, hzMY₂⟩)⁻¹ ∈ N₀ := by
      have h2 : QuotientGroup.mk' N₀ ((⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) * c' *
          (c' * ⟨g₂ * z * g₂⁻¹, hzMY₂⟩)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_mul, map_mul, hπc']
        have h3 : QuotientGroup.mk' N₀ (⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) = z₂ := hz₂eq.symm
        rw [h3]
        exact mul_inv_eq_one.mpr ((Commute.pow_right (show Commute z₂ y from hcomm) m).eq)
      exact (QuotientGroup.eq_one_iff _).mp h2
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [commutatorElement_def, mul_assoc, hy₁]⟩
  have hR2 : IsPGroup 2 (Subgroup.zpowers y₁) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hy₁4]; norm_num)
  have hcN : g₂ * z * g₂⁻¹ ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hzMY₂)
  have huN : y₁ ∈ Subgroup.normalizer (oddCoreOf Y : Set G) :=
    T7L.mem_normalizer_oddCoreOf (Subgroup.le_normalizer hy₁Y)
  obtain ⟨n, hn, hncent⟩ := T7L.exists_conj_centralizes hzM₂.sq (oddCoreOf_odd_natCard Y) hR2
    (Subgroup.zpowers_le.mpr huN) hcN (fun r hr => comm_mem_of_mem_zpowers huN hcom hr)
  have hyc : (n * y₁ * n⁻¹) * (g₂ * z * g₂⁻¹) = (g₂ * z * g₂⁻¹) * (n * y₁ * n⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (hncent (conj_mem_conjSub (Subgroup.mem_zpowers y₁)))
  have hJ₀Ω : conjSub n M₁ ∈ Ω := hΩ.conjInvariant n M₁ hM₁tq.1
  have hJ₀z : IsUniqueInvolution (conjSub n M₁) (n * (g₁ * z * g₁⁻¹) * n⁻¹) := hzM₁.conj n
  have hyJ : n * y₁ * n⁻¹ ∈ conjSub n M₁ := conj_mem_conjSub hy₁M
  have hy4' : orderOf (n * y₁ * n⁻¹) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n) y₁
    simpa [MulAut.conj_apply, hy₁4] using this
  have hya : g₂ * z * g₂⁻¹ ≠ n * (g₁ * z * g₁⁻¹) * n⁻¹ := by
    intro heq
    have hxn : n * (g₁ * z * g₁⁻¹) * n⁻¹ ∈ Y := heq ▸ hzMY₂
    have h1 : (⟨g₂ * z * g₂⁻¹, hzMY₂⟩ : ↥Y) = ⟨n * (g₁ * z * g₁⁻¹) * n⁻¹, hxn⟩ :=
      Subtype.ext heq
    have h2 : T7H.toBar Ω a (g₂ * z * g₂⁻¹) hzMY₂ =
        T7H.toBar Ω a (n * (g₁ * z * g₁⁻¹) * n⁻¹) hxn := by
      unfold T7H.toBar
      rw [h1]
    rw [toBar_conj_odd hzMY₁ hn hxn, ← hyy, ← hz₂eq] at h2
    exact hne h2
  exact T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ₀Ω hJ₀z hya hyJ hy4' hyc.symm

end NC4

end C25X

end CFSG.ClassicalInvolution.Asc77
