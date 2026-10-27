module

public import CFSG.ClassicalInvolution.Asc77.AscT3SOut
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC3b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Cmo

variable {G : Type} [Group G]

theorem cmo_conj_mem {M : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (M : Set G))
    (hy : y ∈ centralizerModOdd (⊤ : Subgroup G) M) :
    x * y * x⁻¹ ∈ centralizerModOdd (⊤ : Subgroup G) M := by
  obtain ⟨-, hyN, -, hyc⟩ := hy
  have hN : x * y * x⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hyN) (Subgroup.inv_mem _ hx)
  refine ⟨Subgroup.mem_top _, hN, mem_normalizer_oddCore_of_mem_normalizer hN, fun m hm => ?_⟩
  have hm' : x⁻¹ * m * x ∈ M := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) m).mp hm
    simpa using this
  have e : ⁅x * y * x⁻¹, m⁆ = x * ⁅y, x⁻¹ * m * x⁆ * x⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer hx) _).mp
    (hyc _ hm')

end Cmo

section C3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem s_centE_le (c7 : Concl20_7 S K K' z) :
    sec20X (CoreAssembly.conjClass K) z K K' ⊓
        centralizerModOdd (⊤ : Subgroup G) (K ⊔ K') ≤
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers z := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  set E := X ⊓ centralizerModOdd (⊤ : Subgroup G) (K ⊔ K') with hE
  have hXC := d.sec20X_le_C
  have hXN := d.sec20X_le_normalizers
  have hMN : ∀ x ∈ X, x ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := fun x hx =>
    late_mem_normalizer_sup (hXN hx).1 (hXN hx).2
  have hXE : X ≤ Subgroup.normalizer (E : Set G) := by
    intro x hx
    refine mem_normalizer_of_conjSub_le ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨X.mul_mem (X.mul_mem hx hy.1) (X.inv_mem hx), cmo_conj_mem (hMN x hx) hy.2⟩
  have hzE : z ∈ E := by
    refine ⟨le_sec20X_left d.viol.hzK.mem, Subgroup.mem_top _,
      Subgroup.le_normalizer (Subgroup.mem_sup_left d.viol.hzK.mem),
      mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer
        (Subgroup.mem_sup_left d.viol.hzK.mem)), fun l hl => ?_⟩
    have := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (d.sup_le_centralizer_z hl)).symm
    rw [this]
    exact (oddCoreOf _).one_mem
  have h2 : ∀ x ∈ E, IsPGroup 2 (Subgroup.zpowers x) → x ∈ Subgroup.zpowers z := by
    intro x hx hx2
    obtain ⟨c, hc, hcU⟩ := d.exists_conj_le_S hx2 (Subgroup.zpowers_le.mpr (hXC hx.1))
    have hcx : c * x * c⁻¹ ∈ conjSub c (Subgroup.zpowers x) := ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hcS : c * x * c⁻¹ ∈ (S : Subgroup G) := hcU hcx
    have hMc : c ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
      d.late_cent_le_normalizer_sup hc
    have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
      d.hSz.trans d.late_cent_le_normalizer_sup
    have hcxC := cmo_conj_mem hMc hx.2
    have hA : c * x * c⁻¹ ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') :=
      ⟨hcS, hSN hcS, mem_normalizer_oddCore_of_mem_normalizer (hSN hcS), hcxC.2.2.2⟩
    rw [c7] at hA
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hA
    have hcz : Commute c z := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hxz : x = z ^ n := by
      have h5 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
      rw [h5, ← hn]
      calc c⁻¹ * z ^ n * c = z ^ n * c⁻¹ * c := by rw [((hcz.zpow_right n).inv_left).eq]
        _ = z ^ n := by group
    rw [hxz]
    exact Subgroup.zpow_mem_zpowers z n
  have h3 := le_oddCoreOf_sup_zpowers hzE d.viol.hzK.sq d.viol.hzK.ne_one h2
  have h4 : oddCoreOf E ≤ oddCoreOf X := Hall196.oddCoreOf_le_of_le_normalizer inf_le_left hXE
  exact h3.trans (sup_le_sup_right h4 _)


theorem concl20_3_of_mod (hH : Hex20 (CoreAssembly.conjClass K) K J W)
    (c7 : Concl20_7 S K K' z) : Concl20_3 K K' V z := by
  have hp := d.branch.odd
  have hq := d.branch.five
  obtain ⟨eK⟩ := d.hyp.nonempty_equiv_sl2 d.late_mem_K
  obtain ⟨eK'⟩ := d.hyp.nonempty_equiv_sl2 d.late_mem_K'
  have hout := T3S.outCommMod_of_chart hp hq eK
  have hout' := T3S.outCommMod_of_chart hp hq eK'
  have hcomm : ∀ k ∈ K, ∀ k' ∈ K', ⁅k, k'⁆ ∈ oddCoreOf K ∧ ⁅k, k'⁆ ∈ oddCoreOf K' :=
    fun k hk k' hk' => by
    have := d.hyp.comm_le_oddCore_of_twin d.late_mem_K d.late_mem_K' d.ne.symm d.viol.hzK
      d.late_hzK' (Subgroup.commutator_mem_commutator hk hk')
    exact ⟨this.1, this.2⟩
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  set N := oddCoreOf X ⊔ (V ⊔ (K ⊔ K')) with hN
  have hMN : K ⊔ K' ≤ N := le_trans le_sup_right le_sup_right
  have hVN : V ≤ N := le_trans le_sup_left le_sup_right
  have step : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c ∈ Subgroup.normalizer (K : Set G) →
      conjSub c V ≤ N := by
    intro c hc hcK
    have hcK' : c ∈ Subgroup.normalizer (K' : Set G) :=
      mem_normalizer_iff_conjSub_eq.mpr
        ((d.late_conj_iff hc).mp (mem_normalizer_iff_conjSub_eq.mp hcK))
    rintro _ ⟨v, hv, rfl⟩
    change c * v * c⁻¹ ∈ N
    have hvX : v ∈ X := tw.hVX hv
    obtain ⟨hvK, hvK'⟩ := d.sec20X_le_normalizers hvX
    obtain ⟨k, hk, k', hk', hdec⟩ := T3S.commutator_decomp_mod d.late_K_le d.late_K'_le hcomm hout
      hout' hcK hcK' hvK hvK'
    have hcX : c ∈ Subgroup.normalizer (X : Set G) :=
      le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins hc
    have hXcv : ⁅c, v⁆ ∈ X := by
      have e : ⁅c, v⁆ = (c * v * c⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hcX v).mp hvX) (X.inv_mem hvX)
    have hkkX : k * k' ∈ X := X.mul_mem (le_sec20X_left hk) (le_sec20X_right hk')
    have he₀E : (k * k')⁻¹ * ⁅c, v⁆ ∈ X ⊓ centralizerModOdd (⊤ : Subgroup G) (K ⊔ K') :=
      ⟨X.mul_mem (X.inv_mem hkkX) hXcv, hdec⟩
    have he₀m := d.s_centE_le c7 he₀E
    have hcv : c * v * c⁻¹ = (k * k') * ((k * k')⁻¹ * ⁅c, v⁆) * v := by
      simp only [commutatorElement_def]
      group
    have hzM : Subgroup.zpowers z ≤ N :=
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left d.viol.hzK.mem)).trans hMN
    have h1 : (k * k')⁻¹ * ⁅c, v⁆ ∈ N := (sup_le le_sup_left hzM) he₀m
    have h2 : k * k' ∈ N :=
      N.mul_mem (hMN (Subgroup.mem_sup_left hk)) (hMN (Subgroup.mem_sup_right hk'))
    rw [hcv]
    exact N.mul_mem (N.mul_mem h2 h1) (hVN hv)
  refine d.concl20_3_of_res_pt hH fun c hc => ?_
  by_cases hcK : c ∈ Subgroup.normalizer (K : Set G)
  · exact step c hc hcK
  · obtain ⟨u, huS, huK⟩ := d.late_exists_swap
    obtain ⟨huK', -, huW, -⟩ := d.late_swap_data huS huK
    have huz : u ∈ Subgroup.centralizer ({z} : Set G) := d.hSz huS
    have hc₁ : c * u⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      (Subgroup.centralizer _).mul_mem hc ((Subgroup.centralizer _).inv_mem huz)
    have hcK₁ : conjSub c K = K' := by
      rcases d.late_conj_K hc with h | h
      · exact absurd (mem_normalizer_iff_conjSub_eq.mpr h) hcK
      · exact h
    have hcK'₁ : conjSub c K' = K := by
      rcases d.late_conj_K' hc with h | h
      · exact h
      · exact absurd (conjSub_injective c (hcK₁.trans h.symm)) d.ne.symm
    have huinv : conjSub u⁻¹ K = K' := by
      rw [← huK', conjSub_inv_conjSub]
    have hc₁N : c * u⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, huinv, hcK'₁]
    have hcu : conjSub c V = conjSub (c * u⁻¹) (conjSub u V) := by
      rw [← conjSub_mul, inv_mul_cancel_right]
    have h1 : conjSub u V ≤ V ⊔ K :=
      (conjSub_mono d.hVW).trans (huW.le.trans ((d.W_le_V_sup_K hH).trans
        (sup_le_sup_left inf_le_right V)))
    have h2 := conjSub_mono (n := c * u⁻¹) h1
    rw [hcu]
    refine h2.trans ?_
    rw [conjSub_sup', mem_normalizer_iff_conjSub_eq.mp hc₁N]
    exact sup_le (step _ hc₁ hc₁N) (le_trans le_sup_left hMN)

end Std20

end C3

end CFSG.ClassicalInvolution.Asc77.T3CII
