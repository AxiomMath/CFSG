module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25E5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25V3
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMB01

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Q3.AE (AEQ mkQ memBar Wr)
open CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL (layerX_le_centralizer conjSub_layerX_of_mem le_layerX
  mem_coreHull_of_mem_layerX layerBarHullEquiv_mk layer_twinData)
open scoped commutatorElement MatrixGroups


section Finite

@[expose] def b₀ : SL(2, ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩

theorem b₀_pow3 : b₀ ^ 3 = 1 := by decide +kernel

theorem b₀_nontriv : ∀ k : ℕ, k % 3 ≠ 0 → ∃ q : SL(2, ZMod 3), q ^ 4 = 1 ∧ b₀ ^ k * q ≠ q * b₀ ^ k := by
  intro k hk
  have e : b₀ ^ k = b₀ ^ (k % 3) := by
    conv_lhs => rw [← Nat.mod_add_div k 3]
    rw [pow_add, pow_mul, b₀_pow3, one_pow, mul_one]
  have h1 : ∃ q : SL(2, ZMod 3), q ^ 4 = 1 ∧ b₀ ^ 1 * q ≠ q * b₀ ^ 1 := by decide +kernel
  have h2 : ∃ q : SL(2, ZMod 3), q ^ 4 = 1 ∧ b₀ ^ 2 * q ≠ q * b₀ ^ 2 := by decide +kernel
  have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [e]
  rcases hk' with h | h
  · rw [h]; exact h1
  · rw [h]; exact h2

variable {F : Type} [Field F]

theorem exists_b (r : ZMod 3 ≃+* F) :
    ∃ b : SL(2, F), b ^ 3 = 1 ∧ ∀ k : ℕ, k % 3 ≠ 0 →
      ∃ q ∈ EndL.Q8.Qsub r, b ^ k * q ≠ q * b ^ k := by
  refine ⟨Q3T7P25.slMapEquivF r b₀, ?_, ?_⟩
  · rw [← map_pow, b₀_pow3, map_one]
  · intro k hk
    obtain ⟨q, hq4, hne⟩ := b₀_nontriv k hk
    refine ⟨Q3T7P25.slMapEquivF r q, (EndL.Q8.mem_Qsub r _).2 (by rw [← map_pow, hq4, map_one]), ?_⟩
    intro he
    apply hne
    apply (Q3T7P25.slMapEquivF r).injective
    rw [map_mul, map_mul, map_pow]
    exact he

end Finite

section Odd

theorem wr_mul_self_of_perm_one {w : Wr 5} (h : w.perm = 1) : w * w = 1 := by
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [Wr.mul_vec, h]
    show w.vec i + w.vec i = 0
    exact Wr.zmod_two_add_self _
  · rw [Wr.mul_perm, h, mul_one]
    rfl

theorem pow_240 (x : AEQ 5) : x ^ 240 = 1 := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨w, hw⟩ : ∃ w : Wr 5, w = c ^ 120 := ⟨_, rfl⟩
  have h1 : w.perm = 1 := by
    have : w.perm = c.perm ^ 120 := by rw [hw]; exact (map_pow permHom c 120)
    rw [this]
    have hcard : Fintype.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Fintype.card_perm, Fintype.card_fin]
      norm_num [Nat.factorial]
    rw [← hcard]
    exact pow_card_eq_one
  have h2 : c ^ 240 = 1 := by
    have : c ^ 240 = w * w := by rw [hw, ← pow_add]
    rw [this]
    exact wr_mul_self_of_perm_one h1
  show (mkQ 5 c) ^ 240 = 1
  rw [← map_pow, h2, map_one]

theorem pow_fifteen_of_odd {x : AEQ 5} {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) : x ^ 15 = 1 := by
  have h1 : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm
  have h2 : orderOf x ∣ 240 := orderOf_dvd_of_pow_eq_one (pow_240 x)
  have hcop : Nat.Coprime (orderOf x) 16 := by
    have : Nat.Coprime m 2 := Nat.coprime_two_right.mpr hm
    have h16 : Nat.Coprime m (2 ^ 4) := this.pow_right 4
    exact Nat.Coprime.coprime_dvd_left h1 h16
  have h3 : orderOf x ∣ 15 * 16 := by simpa using h2
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right h3)

end Odd

section Frame

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ c : G}

theorem exists_frame_at (Λ : Lay Ω K K' W S R R' z t u₁ u₂ c) (hno : SecNoExitAt Ω c)
    (hL : LayerLie Ω c 5) :
    ∃ (A A' : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)))
      (z' : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
      Nonempty (M.Frame (GaloisField 3 1) (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
        (liftFam (TwinDisc.secFam Ω c)) A A' z') ∧
      secImg Ω c K ≤ A ∧ secImg Ω c K' ≤ A' := by
  obtain ⟨htC, htY, hu₁C, hu₁Y, hu₂C, hu₂Y, A, A', htw, hA, hA'⟩ :=
    layer_twinData Λ.hyp Λ.hc2 Λ.hc1 Λ.hcA hno
  have hS := layer_q8Section Λ.hyp Λ.hc2
  have hD : Q3T8.Asc77.C5O.Om5Data (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))
      (liftFam (TwinDisc.secFam Ω c)) A A'
      (QuotientGroup.mk (⟨⟨z, htC⟩, htY⟩ : ↥(coreHull Ω c)))
      (QuotientGroup.mk (⟨⟨u₁, hu₁C⟩, hu₁Y⟩ : ↥(coreHull Ω c)))
      (QuotientGroup.mk (⟨⟨u₂, hu₂C⟩, hu₂Y⟩ : ↥(coreHull Ω c))) :=
    ⟨hL, htw, fun J hJ y => conjInvariant_liftFam hS.hyp.conjInvariant y J hJ⟩
  exact ⟨A, A', _, Q3T8.Asc77.C5O.M.exists_frame hD, hA, hA'⟩

end Frame

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.AE5X
