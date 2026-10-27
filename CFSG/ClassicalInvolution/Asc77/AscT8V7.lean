module

public import CFSG.ClassicalInvolution.Asc77.AscT8V6
import CFSG.ClassicalInvolution.Asc77.AscT8V7Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8V1
public import CFSG.ClassicalInvolution.Asc77.AscT8V4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8V

section Roots

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem pow_two_pow_two_eq {H : Type*} [Group H] (y : H) : y ^ 2 ^ 2 = (y * y) * (y * y) := by
  rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, pow_two, pow_two]

omit [Finite G] in
theorem layerMk_congr {x g h : G} (hg : g ∈ T8.layerJoin Ω x) (hh : h ∈ T8.layerJoin Ω x)
    (e : g = h) : layerMk x g hg = layerMk x h hh := by
  subst e
  rfl

theorem comm_mem_oddCoreOf_of_pow (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {M : Subgroup G} (hM : M ∈ Ω) {R₀ : Subgroup G}
    (hR : IsSylow2In R₀ M) {y : G} (hyN : y ∈ Subgroup.normalizer (M : Set G)) {m : ℕ}
    (hym : y ^ 2 ^ m = 1) (hyR : ∀ r ∈ R₀, y * r = r * y) : ∀ k ∈ M, ⁅y, k⁆ ∈ oddCoreOf M := by
  obtain ⟨w, hw⟩ := hΩ.classical M hM
  exact commutator_mem_oddCoreIn_of_pow hp hq hw hR hyN hym hyR


theorem z_mem_W (hs : Std8 p f Ω K J S R T W z t) : z ∈ W := by
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact (uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW (T8.stdRepK hs).hK (T8.stdRepK hs).hR
    (T8.stdRepK hs).hRK hs.hz).2

theorem t_mem_W (hs : Std8 p f Ω K J S R T W z t) : t ∈ W := by
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact (uniqueInvolution_mem_W c.hp c.hq c.hΩ c.hW (T8.stdRepJ hs).hK (T8.stdRepJ hs).hR
    (T8.stdRepJ hs).hRK hs.ht).2

theorem y_data (hs : Std8 p f Ω K J S R T W z t) {y : G} (hyW : y ∈ W) (hy4 : y ^ 2 ^ 2 = 1)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) :
    y ∈ T8.cenZ (z * t) ∧ y ∈ Subgroup.normalizer (K : Set G) ∧
      y ∈ Subgroup.normalizer (J : Set G) ∧ (∀ k ∈ K, ⁅y, k⁆ ∈ oddCoreOf K) ∧
      (∀ k ∈ J, ⁅y, k⁆ ∈ oddCoreOf J) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have c := T8.ctxOf (T8.partIHyp_of_std8 hs) hs.hW.1
  exact y_dataE hΩ.conjInvariant c.comm_W hs.stand.mem hs.hJ.1 hs.hz hs.ht hs.noTwins hnt (z_mem_W hs)
    (t_mem_W hs) (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.stand.mem hs.hR.1 hs.hR.2.1)
    (T3.isSylow2In_of_mem_RSet_of_le hp hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1)
    (fun hM hR hy hym hyR' => comm_mem_oddCoreOf_of_pow hp hq hΩ hM hR hy hym hyR') hyW hy4 hyR hyT

theorem no_root_sq [IsSimpleGroup G] (hE : E4SecNoRoot p f) (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (T8.layerFamQ Ω (z * t))) {y u : G}
    (hu : u ∈ T8.layerJoin Ω (z * t)) (hyW : y ∈ W) (hyy : y * y = u) (hy4 : y ^ 2 ^ 2 = 1)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x)
    (hconj : MulAut.conj (layerMk (z * t) u hu) =
      MulAut.conj (layerMk (z * t) z (z_mem_layerJoin hs))) : False := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hycen, hyK, hyJ, hcK, hcJ⟩ := y_data hs hyW hy4 hyR hyT
  have hyN : y ∈ Subgroup.normalizer ((T8.layerJoin Ω (z * t) : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr (T8.layerJoin_conjSub_eq hΩ hycen)
  refine (e4_layer hE hs hdisc).1 (s26Act (T8.layerJoin Ω (z * t)) ⟨y, hyN⟩)
    (s26Act_mul_inv_mem hΩ (T8.xMem_zt hs) hycen hyK hcK)
    (s26Act_mul_inv_mem hΩ (xMem_J hs) hycen hyJ hcJ) ?_
  rw [← map_mul]
  have e : (⟨y, hyN⟩ * ⟨y, hyN⟩ :
      ↥(Subgroup.normalizer ((T8.layerJoin Ω (z * t) : Subgroup G) : Set G))) =
      ⟨u, Subgroup.le_normalizer hu⟩ := Subtype.ext hyy
  rw [e, s26Act_eq_conj (T8.layerJoin Ω (z * t)) ⟨u, hu⟩]
  exact hconj

theorem no_root_z [IsSimpleGroup G] (hE : E4SecNoRoot p f) (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (T8.layerFamQ Ω (z * t))) {y : G} (hyW : y ∈ W)
    (hyy : y * y = z) (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) : False :=
  no_root_sq hE hs hdisc (z_mem_layerJoin hs) hyW hyy
    (by rw [pow_two_pow_two_eq, hyy, hs.hz.sq]) hyR hyT rfl

theorem no_root_t [IsSimpleGroup G] (hE : E4SecNoRoot p f) (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (T8.layerFamQ Ω (z * t))) {y : G} (hyW : y ∈ W)
    (hyy : y * y = t) (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) : False :=
  no_root_sq hE hs hdisc (t_mem_layerJoin hs) hyW hyy
    (by rw [pow_two_pow_two_eq, hyy, hs.ht.sq]) hyR hyT
    (conj_eq_of_central_mul (layerMk_z_sq hs) (layerMk_central hs))

theorem no_root_zt [IsSimpleGroup G] (hE : E4SecNoRoot p f) (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ T3.DStarConnected (T8.layerFamQ Ω (z * t))) {y : G} (hyW : y ∈ W)
    (hyY : y ∈ T8.layerJoin Ω (z * t)) (hyy : y * y = z * t)
    (hyR : ∀ x ∈ R, x * y = y * x) (hyT : ∀ x ∈ T, x * y = y * x) : False := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := T8.mul_self_zt hp hΩ hs.hz hs.hJ hs.ht
  obtain ⟨hycen, hyK, hyJ, hcK, hcJ⟩ :=
    y_data hs hyW (by rw [pow_two_pow_two_eq, hyy, hx]) hyR hyT
  refine (e4_layer hE hs hdisc).2 (layerMk (z * t) y hyY)
    (comm_mk_mem (T8.xMem_zt hs) ⟨y, hyY⟩ hycen hyK hcK)
    (comm_mk_mem (xMem_J hs) ⟨y, hyY⟩ hycen hyJ hcJ) ?_
  rw [layerMk_mul, layerMk_mul]
  exact layerMk_congr _ _ hyy

end Roots

end T8V

end CFSG.ClassicalInvolution.Asc77
