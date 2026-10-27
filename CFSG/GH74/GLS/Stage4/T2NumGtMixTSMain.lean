module

public import CFSG.GH74.GLS.Stage4.T2NumGtSingular
public import CFSG.GH74.GLS.Stage4.T2NumGtMixTSDefs
public import CFSG.GH74.GLS.Stage4.T2NumGtMixTSArith
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSteps

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem ch6Mix_ts_of_steps (hS : Ch6MixSing) (hJ : Ch6MixLayer) :
    Ch6MixTS := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt hlt hmod z K₁ K₂ F₁ F₂ _ _ t hSet hRem p n hp hp2 hq₂p N u hz
    hK₁ hK₂ hq₁ hq₂ hCoord hSec
  have hloc := hSec.loc
  have hlt' : N.q₂ < N.q₁ := by rw [hq₁, hq₂]; exact hlt
  have h2part : ∀ k : ℕ, 2 ^ k ∣ N.q₁ + 1 ↔ 2 ^ k ∣ N.q₂ - 1 := by
    rw [hq₁, hq₂]; exact t5_two_part_mix_of_setup hSet hmod
  obtain ⟨y, hyH, hyz, hyp, hyodd, hyq, hya⟩ := hS G N u hSec hlt' h2part
  obtain ⟨J, hJy, hKJ, hJ'⟩ := hJ G hStd hr Gs q₁ q₂ hAt hlt hmod z K₁ K₂ F₁ F₂ t hSet hRem p n hp
    hp2 hq₂p N u hz hK₁ hK₂ hq₁ hq₂ hCoord hSec y hyH hyz hyp hyodd hyq hya
  have hz2 : orderOf z = 2 := hSet.central.1
  have hzc : ∀ x ∈ K₂, z * x = x * z := by
    intro x hx
    have : x ∈ centralizer ({z} : Set G) := hSet.le_centralizer (Subgroup.mem_sup_right hx)
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  have hX₂K₂ : N.X₂ ≤ N.K₂ := by rw [hloc.K₂_eq]; exact le_sup_left
  have hX₂p : IsPGroup p ↥N.X₂ :=
    IsPGroup.of_card (n := n) (by rw [hloc.card_X₂, hq₂, hq₂p])
  have hX₂c : Nat.card ↥N.X₂ = p ^ n := by rw [hloc.card_X₂, hq₂, hq₂p]
  have hJ'' : IsSLnEps 3 ↥J 1 (p ^ n) ∨ IsLnEps 3 ↥J 1 (p ^ n) := by rw [← hq₂p]; exact hJ'
  have hKJ' : N.K₂ ≤ J := by rw [hK₂]; exact hKJ
  have hz2' : orderOf N.z = 2 := by rw [hz]; exact hz2
  have hzK' : N.z ∈ N.K₂ := hloc.z_mem_K₂
  have hzc' : ∀ x ∈ N.K₂, N.z * x = x * N.z := by rw [hz, hK₂]; exact hzc
  obtain ⟨R, hRp, hXR, hRc, hRcard, hRZ, hRcom1, hRcom2, hRinv, hRy, hRexp⟩ :=
    t5_transport_exp hp hp2 hJy hKJ' hJ'' hz2' hzK' hzc' hX₂K₂ hX₂p hX₂c
  refine ⟨y, R, ?_⟩
  exact
    { yK := hyH.2
      y_ne := hyz
      y_prime := hyp
      y_odd := hyodd
      y_dvd := hyq
      R_p := hRp
      X_le := hXR
      R_cent := hRc
      R_card := by rw [hRcard, hq₂, hq₂p]
      R_center := hRZ
      X_comm := hRcom1
      R_comm := hRcom2
      R_inv := hRinv
      R_exp := hRexp
      y_cent := hRy }

end CFSG.GH74.GLS.Stage4.Rest
