module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOut
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC3
public import CFSG.ClassicalInvolution.Asc77.AscT3CLateSwap
public import CFSG.ClassicalInvolution.AschTight.Hall196XG
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC5Eng
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIExact

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type} [Group G]

theorem conj_centralizer_of_mem_normalizer {M : Subgroup G} {x e : G}
    (hx : x ∈ Subgroup.normalizer (M : Set G)) (he : ∀ m ∈ M, m * e = e * m) :
    ∀ m ∈ M, m * (x * e * x⁻¹) = (x * e * x⁻¹) * m := by
  intro m hm
  have hm' : x⁻¹ * m * x ∈ M := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (M : Set G)).inv_mem hx) m).mp hm
    simpa using this
  have h := he _ hm'
  calc m * (x * e * x⁻¹) = x * ((x⁻¹ * m * x) * e) * x⁻¹ := by group
    _ = x * (e * (x⁻¹ * m * x)) * x⁻¹ := by rw [h]
    _ = (x * e * x⁻¹) * m := by group

end Generic

section Exact3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem sec20X_le_normalizers :
    sec20X (CoreAssembly.conjClass K) z K K' ≤
      Subgroup.normalizer (K : Set G) ⊓ Subgroup.normalizer (K' : Set G) := by
  have hp := d.branch.odd
  have hq := d.branch.five
  unfold sec20X
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨hUU, hUC⟩ := hU
    obtain ⟨L₀, hL₀, hUL₀⟩ := d.hyp.exists_member_of_mem_USet hp hUU
    have hU2 : IsPGroup 2 U := d.hyp.isPGroup_of_mem_USet hp hUU
    obtain ⟨-, -, -, -, -, -, -, -, hU4⟩ := d.hyp.exists_data_of_mem_USet hp hUU
    refine le_inf ?_ ?_
    · by_cases h : L₀ = K
      · subst h
        exact hUL₀.trans Subgroup.le_normalizer
      · exact d.hyp.le_normalizer_of_le_centralizer hp hq d.late_mem_K hL₀ (Ne.symm h)
          d.viol.hzK hUL₀ hU2 (by omega) hUC
    · by_cases h : L₀ = K'
      · subst h
        exact hUL₀.trans Subgroup.le_normalizer
      · exact d.hyp.le_normalizer_of_le_centralizer hp hq d.late_mem_K' hL₀ (Ne.symm h)
          d.late_hzK' hUL₀ hU2 (by omega) hUC
  · exact le_inf Subgroup.le_normalizer d.late_K_le
  · exact le_inf d.late_K'_le Subgroup.le_normalizer

theorem sec20X_le_C :
    sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
  sec20X_le_centralizer (le_sup_left.trans d.sup_le_centralizer_z)
    (le_sup_right.trans d.sup_le_centralizer_z)

theorem centE_le (c7 : Concl20_7 S K K' z) :
    sec20X (CoreAssembly.conjClass K) z K K' ⊓
        Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G) ≤
      oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers z := by
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hX
  set E := X ⊓ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G) with hE
  have hXC := d.sec20X_le_C
  have hXN := d.sec20X_le_normalizers
  have hMN : ∀ x ∈ X, x ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) := fun x hx =>
    late_mem_normalizer_sup (hXN hx).1 (hXN hx).2
  have hXE : X ≤ Subgroup.normalizer (E : Set G) := by
    intro x hx
    refine mem_normalizer_of_conjSub_le ?_
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨X.mul_mem (X.mul_mem hx hy.1) (X.inv_mem hx), ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr
      (conj_centralizer_of_mem_normalizer (hMN x hx) (Subgroup.mem_centralizer_iff.mp hy.2))
  have hzE : z ∈ E := by
    refine ⟨le_sec20X_left d.viol.hzK.mem, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (d.sup_le_centralizer_z hm)
  have h2 : ∀ x ∈ E, IsPGroup 2 (Subgroup.zpowers x) → x ∈ Subgroup.zpowers z := by
    intro x hx hx2
    have hxC : ∀ m ∈ K ⊔ K', m * x = x * m := Subgroup.mem_centralizer_iff.mp hx.2
    obtain ⟨c, hc, hcU⟩ := d.exists_conj_le_S hx2 (Subgroup.zpowers_le.mpr (hXC hx.1))
    have hcx : c * x * c⁻¹ ∈ conjSub c (Subgroup.zpowers x) := ⟨x, Subgroup.mem_zpowers x, rfl⟩
    have hcS : c * x * c⁻¹ ∈ (S : Subgroup G) := hcU hcx
    have hMc : c ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
      d.late_cent_le_normalizer_sup hc
    have hcomm := conj_centralizer_of_mem_normalizer hMc hxC
    have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
      d.hSz.trans d.late_cent_le_normalizer_sup
    have hA : c * x * c⁻¹ ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := by
      refine ⟨hcS, hSN hcS, mem_normalizer_oddCore_of_mem_normalizer (hSN hcS), fun m hm => ?_⟩
      have : ⁅c * x * c⁻¹, m⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hcomm m hm).symm
      rw [this]
      exact (oddCoreOf _).one_mem
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

theorem concl20_3_of_res_pt (hH : Hex20 (CoreAssembly.conjClass K) K J W)
    (hres : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      conjSub c V ≤ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K'))) :
    Concl20_3 K K' V z := by
  have hp := d.branch.odd
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  show sec20X (CoreAssembly.conjClass K) z K K' =
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K'))
  have hNX : oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) ≤
      sec20X (CoreAssembly.conjClass K) z K K' :=
    sup_le (oddCoreOf_le_self _) (sup_le (tw.hVX) le_sec20X_pair)
  refine le_antisymm ?_ hNX
  set N := oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K')) with hN
  have hMN : K ⊔ K' ≤ N := le_trans le_sup_right le_sup_right
  have hKconj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inl rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  have hK'conj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K' ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inr rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  unfold sec20X
  refine sup_le (sup_le ?_ (le_trans le_sup_left hMN)) (le_trans le_sup_right hMN)
  refine iSup₂_le fun U hU => ?_
  obtain ⟨hUU, hUC⟩ := hU
  have hU2 : IsPGroup 2 U := d.hyp.isPGroup_of_mem_USet hp hUU
  obtain ⟨c, hc, hcU⟩ := d.exists_conj_le_S hU2 hUC
  have hU1 : conjSub c U ∈ USet (CoreAssembly.conjClass K) := USet.conj d.hyp.conjInvariant hUU c
  have hc' : c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := (Subgroup.centralizer _).inv_mem hc
  have hback : U = conjSub c⁻¹ (conjSub c U) := (conjSub_inv_conjSub c U).symm
  rcases d.U_cases hU1 hcU with h | h | h
  · have h1 : conjSub c U ≤ V ⊔ K :=
      h.trans ((d.W_le_V_sup_K hH).trans (sup_le_sup_left inf_le_right V))
    have h2 := conjSub_mono (n := c⁻¹) h1
    rw [conjSub_inv_conjSub, conjSub_sup'] at h2
    exact h2.trans (sup_le (hres c⁻¹ hc') ((hKconj c⁻¹ hc').trans hMN))
  · have h2 := conjSub_mono (n := c⁻¹) h
    rw [conjSub_inv_conjSub] at h2
    exact h2.trans ((hKconj c⁻¹ hc').trans hMN)
  · have h2 := conjSub_mono (n := c⁻¹) h
    rw [conjSub_inv_conjSub] at h2
    exact h2.trans ((hK'conj c⁻¹ hc').trans hMN)

theorem concl20_3_of_exact (hH : Hex20 (CoreAssembly.conjClass K) K J W)
    (hex : ExactMembers (CoreAssembly.conjClass K)) (c7 : Concl20_7 S K K' z) :
    Concl20_3 K K' V z := by
  have hp := d.branch.odd
  have hq := d.branch.five
  obtain ⟨eK⟩ := exists_equiv_sl2_of_exact d.hyp hex d.late_mem_K
  obtain ⟨eK'⟩ := exists_equiv_sl2_of_exact d.hyp hex d.late_mem_K'
  have hout := outComm_of_equiv_galoisField hp hq eK
  have hout' := outComm_of_equiv_galoisField hp hq eK'
  have hcomm := commute_of_twin_exact hp hq d.hyp hex d.late_mem_K d.late_mem_K' d.ne
    d.viol.hzK d.late_hzK'
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
    obtain ⟨k, hk, k', hk', hcommv⟩ := commutator_decomp hcomm hout hout' hcK hcK' hvK hvK'
    have hcX : c ∈ Subgroup.normalizer (X : Set G) :=
      le_normalizer_sec20X d.hyp.conjInvariant d.viol.hzK d.twins hc
    have hXcv : ⁅c, v⁆ ∈ X := by
      have e : ⁅c, v⁆ = (c * v * c⁻¹) * v⁻¹ := by simp only [commutatorElement_def]
      rw [e]
      exact X.mul_mem ((Subgroup.mem_normalizer_iff.mp hcX v).mp hvX) (X.inv_mem hvX)
    have hkkX : k * k' ∈ X := X.mul_mem (le_sec20X_left hk) (le_sec20X_right hk')
    have he₀E : (k * k')⁻¹ * ⁅c, v⁆ ∈ X ⊓ Subgroup.centralizer ((K ⊔ K' : Subgroup G) : Set G) :=
      ⟨X.mul_mem (X.inv_mem hkkX) hXcv,
        Subgroup.mem_centralizer_iff.mpr fun m hm => (hcommv m hm).symm⟩
    have he₀m := d.centE_le c7 he₀E
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

end Exact3

end CFSG.ClassicalInvolution.Asc77.T3CII
