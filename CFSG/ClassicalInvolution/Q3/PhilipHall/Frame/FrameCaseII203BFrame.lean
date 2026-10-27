module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203Defs
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII207Cent
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII203BGroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

open Out


variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem cent203b_oddCore_le_trivialOnQuot {X J : Subgroup G} (hJX : J ≤ X)
    (hXN : X ≤ Subgroup.normalizer (J : Set G)) : oddCoreOf X ≤ trivialOnQuot J := by
  intro x hx
  have hxX : x ∈ X := oddCoreOf_le_self X hx
  refine ⟨hXN hxX, fun y hy => ?_⟩
  have hyX : y ∈ X := hJX hy
  have h1 : ⁅x, y⁆ ∈ oddCoreOf X := by
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    refine (oddCoreOf X).mul_mem hx ?_
    have := conj_mem_oddCoreIn_of_mem_normalizer (Subgroup.le_normalizer hyX)
      ((oddCoreOf X).inv_mem hx)
    simpa [oddCoreIn_eq_oddCoreOf] using this
  have h2 : ⁅x, y⁆ ∈ J := by
    have e : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by
      simp [commutatorElement_def]
    rw [e]
    exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXN hxX) y).mp hy) (J.inv_mem hy)
  rw [oddCoreIn_eq_oddCoreOf]
  exact Out.oddCoreOf_inf_le hJX ⟨h1, h2⟩

theorem cent203b_oddCore_le_oddCore {X J : Subgroup G} (hJX : J ≤ X)
    (hXN : X ≤ Subgroup.normalizer (J : Set G)) : oddCoreOf J ≤ oddCoreOf X := by
  refine le_oddCoreOf_of_normalizes ((oddCoreOf_le_self J).trans hJX) ?_
    (oddCoreOf_odd_natCard J)
  intro x hx
  exact mem_normalizer_oddCore_of_mem_normalizer (hXN hx)

theorem cent203b_z_comm (d : Std20Frame K K' J S R R' W V z t) :
    ∀ y ∈ sec20X (CoreAssembly.conjClass K) z K K', z * y = y * z := by
  intro y hy
  have hC : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.centralizer ({z} : Set G) :=
    sec20X_le_centralizer (le_sup_left.trans d.sup_le_centralizer_z)
      (le_sup_right.trans d.sup_le_centralizer_z)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hy)).symm

theorem cent203b_V_le_X (d : Std20Frame K K' J S R R' W V z t) :
    V ≤ sec20X (CoreAssembly.conjClass K) z K K' := by
  rw [Std20Frame.sec20X_eq d]
  refine le_sup_of_le_left ?_
  refine le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) ?_
  rw [conjSub_one]

theorem cent203b_mem_trivialOnQuot_of_comm (J : Subgroup G) {g : G}
    (hg : ∀ y ∈ J, g * y = y * g) : g ∈ trivialOnQuot J := by
  have hconj : ∀ y ∈ J, g * y * g⁻¹ = y := fun y hy => by
    rw [hg y hy]
    group
  have hN : g ∈ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj h hh]
      exact hh
    · intro hh
      have hc := hg _ hh
      have e : g⁻¹ * (g * h * g⁻¹) * g = g * h * g⁻¹ := by
        calc g⁻¹ * (g * h * g⁻¹) * g = g⁻¹ * ((g * h * g⁻¹) * g) * 1 := by group
          _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [← hc]; group
          _ = g * h * g⁻¹ := by group
      have e2 : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
          _ = g * h * g⁻¹ := e
      rw [e2]
      exact hh
  refine ⟨hN, fun y hy => ?_⟩
  have e : ⁅g, y⁆ = 1 := by
    rw [commutatorElement_def, hg y hy]
    group
  rw [e]
  exact one_mem _

theorem cent203b_le_normalizer_zpowers {X : Subgroup G} (hX : ∀ x ∈ X, z * x = x * z) :
    X ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
  have hc : ∀ x ∈ X, ∀ k : ℤ, x * z ^ k * x⁻¹ = z ^ k := fun x hx k => by
    rw [← (Commute.zpow_left (hX x hx : Commute z x) k).eq, mul_inv_cancel_right]
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [hc x hx k]
    exact hh
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hx' : x⁻¹ ∈ X := X.inv_mem hx
    have e : h = x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ := by group
    rw [e, ← hk, hc x⁻¹ hx' k]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k

theorem cent203b_D_normal (d : Std20Frame K K' J S R R' W V z t) {x a : G}
    (hx : x ∈ sec20X (CoreAssembly.conjClass K) z K K')
    (ha : a ∈ (trivialOnQuot K ⊓ trivialOnQuot K') ⊓ sec20X (CoreAssembly.conjClass K) z K K') :
    x * a * x⁻¹ ∈
      (trivialOnQuot K ⊓ trivialOnQuot K') ⊓ sec20X (CoreAssembly.conjClass K) z K K' := by
  obtain ⟨⟨haK, haK'⟩, haX⟩ := ha
  refine ⟨⟨conj_mem_trivialOnQuot (frameX_le_N d hx) haK,
    conj_mem_trivialOnQuot ((sec20X_le_normalizers_frame d) hx).2 haK'⟩,
    (sec20X (CoreAssembly.conjClass K) z K K').mul_mem
      ((sec20X (CoreAssembly.conjClass K) z K K').mul_mem hx haX)
      ((sec20X (CoreAssembly.conjClass K) z K K').inv_mem hx)⟩

theorem cent203b_factor (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (ha : a ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')) :
    ∃ o ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K'), ∃ k ∈ K, ∃ k' ∈ K',
      a = o * k * k' := by
  rw [← sup_assoc] at ha
  exact cent203b_mem_sup_three _ _ _ _ (oddCoreOf_le_self _) le_sec20X_left le_sec20X_right
    (fun y hy => mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hy))
    (frameX_le_N d) (fun y hy => ((sec20X_le_normalizers_frame d) hy).2) ha

theorem cent203b_N_normal (d : Std20Frame K K' J S R R' W V z t) {x a : G}
    (hx : x ∈ sec20X (CoreAssembly.conjClass K) z K K')
    (ha : a ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')) :
    x * a * x⁻¹ ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') := by
  obtain ⟨o, ho, k, hk, k', hk', rfl⟩ := cent203b_factor d ha
  have e : x * (o * k * k') * x⁻¹ = (x * o * x⁻¹) * (x * k * x⁻¹) * (x * k' * x⁻¹) := by
    group
  rw [e]
  have hxo : x * o * x⁻¹ ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') :=
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer hx) ho
  have hxk : x * k * x⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (frameX_le_N d hx) k).mp hk
  have hxk' : x * k' * x⁻¹ ∈ K' :=
    (Subgroup.mem_normalizer_iff.mp ((sec20X_le_normalizers_frame d) hx).2 k').mp hk'
  refine (oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')).mul_mem
    ((oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')).mul_mem
      (Subgroup.mem_sup_left hxo) (Subgroup.mem_sup_right (Subgroup.mem_sup_left hxk)))
    (Subgroup.mem_sup_right (Subgroup.mem_sup_right hxk'))

theorem cent203b_trivialOnQuot_le_kerG : trivialOnQuot K ≤ kerG K := by
  intro a ha
  exact mem_kerG.mpr ⟨ha.1, psiK_eq_one_of_mem_trivialOnQuot K ha⟩

theorem cent203b_N_le_kerG (d : Std20Frame K K' J S R R' W V z t) :
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') ≤ kerG K :=
  sup_le (fun _ hy => oddCoreX_le_kerG d hy)
    (sup_le (fun _ hy => K_le_kerG d hy) (fun _ hy => K'_le_kerG d hy))

theorem cent203b_exists_v (d : Std20Frame K K' J S R R' W V z t) :
    ∃ v ∈ sec20X (CoreAssembly.conjClass K) z K K', v ∉ kerG K ∧
      v * v ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K') := by
  obtain ⟨v, hvV, -, hv2, hvt⟩ := exists_gen_V d
  refine ⟨v, cent203b_V_le_X d hvV, ?_, ?_⟩
  · intro hvk
    obtain ⟨h, h1⟩ := mem_kerG.mp hvk
    obtain ⟨e⟩ := kbar_equiv_q8 d
    have hinner : InnerOn K v := (psiK_eq_one_iff K e ⟨v, h⟩).mp h1
    exact (frame203Outer G K K' J S R R' W V z t d v hvV hv2).1 hinner
  · rw [hvt]
    exact Subgroup.mem_sup_right d.htKK

theorem cent203b_aux_comm {M : Type} [Group M] (x y w c c' : M) (hy : c * y = y * c)
    (hw : c' * w = w * c') (hcw : c * w = w * c) :
    x * (c * y) * (c' * w) = x * y * w * (c * c') := by
  calc x * (c * y) * (c' * w) = x * (y * c) * (c' * w) := by rw [hy]
    _ = x * y * (c * (c' * w)) := by simp only [mul_assoc]
    _ = x * y * (c * (w * c')) := by rw [hw]
    _ = x * y * ((c * w) * c') := by simp only [mul_assoc]
    _ = x * y * ((w * c) * c') := by rw [hcw]
    _ = x * y * w * (c * c') := by simp only [mul_assoc]

theorem cent203b_inter (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (haK : a ∈ trivialOnQuot K) (haK' : a ∈ trivialOnQuot K')
    (haN : a ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (K ⊔ K')) :
    ∃ u ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K'), ∃ e : G,
      (e = 1 ∨ e = z) ∧ a = u * e := by
  obtain ⟨o, ho, k, hk, k', hk', hfac⟩ := cent203b_factor d haN
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hKX : K ≤ sec20X (CoreAssembly.conjClass K) z K K' := le_sec20X_left
  have hK'X : K' ≤ sec20X (CoreAssembly.conjClass K) z K K' := le_sec20X_right
  have hXN : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (K : Set G) :=
    frameX_le_N d
  have hXN' : sec20X (CoreAssembly.conjClass K) z K K' ≤ Subgroup.normalizer (K' : Set G) :=
    fun x hx => ((sec20X_le_normalizers_frame d) hx).2
  have hOK : oddCoreOf K ≤ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') :=
    cent203b_oddCore_le_oddCore hKX hXN
  have hOK' : oddCoreOf K' ≤ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') :=
    cent203b_oddCore_le_oddCore hK'X hXN'
  have hoK : o ∈ trivialOnQuot K := cent203b_oddCore_le_trivialOnQuot hKX hXN ho
  have hoK' : o ∈ trivialOnQuot K' := cent203b_oddCore_le_trivialOnQuot hK'X hXN' ho
  have hk'K : k' ∈ trivialOnQuot K := le_trivialOnQuot_K d hk'
  have hkK' : k ∈ trivialOnQuot K' := le_trivialOnQuot_K' d hk
  have hkK : k ∈ trivialOnQuot K := by
    have e : k = o⁻¹ * a * k'⁻¹ := by
      rw [hfac]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hoK) haK) (inv_mem hk'K)
  have hk'K' : k' ∈ trivialOnQuot K' := by
    have e : k' = k⁻¹ * o⁻¹ * a := by
      rw [hfac]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hkK') (inv_mem hoK')) haK'
  obtain ⟨c, hc, n₁, hn₁, hkc⟩ := exists_central_mul_oddCore d hk hkK
  obtain ⟨c', hc', n₂, hn₂, hk'c⟩ := exists_central_mul_oddCore' d hk' hk'K'
  have hcX : ∀ e : G, (e = 1 ∨ e = z) → ∀ y ∈ sec20X (CoreAssembly.conjClass K) z K K',
      e * y = y * e := by
    intro e he y hy
    rcases he with he | he
    · rw [he, one_mul, mul_one]
    · rw [he]
      exact cent203b_z_comm d y hy
  have hn₁X : n₁ ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    oddCoreOf_le_self _ (hOK hn₁)
  have hn₂X : n₂ ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    oddCoreOf_le_self _ (hOK' hn₂)
  have hfac2 : a = (o * n₁ * n₂) * (c * c') := by
    rw [hfac, hkc, hk'c]
    exact cent203b_aux_comm o n₁ n₂ c c' (hcX c hc n₁ hn₁X) (hcX c' hc' n₂ hn₂X)
      (hcX c hc n₂ hn₂X)
  have he : c * c' = 1 ∨ c * c' = z := by
    rcases hc with h | h <;> rcases hc' with h' | h' <;> rw [h, h'] <;> simp [hz2]
  exact ⟨o * n₁ * n₂, Subgroup.mul_mem _ (Subgroup.mul_mem _ ho (hOK hn₁)) (hOK' hn₂),
    c * c', he, hfac2⟩

theorem cent203b_le_normalizer_of_closed {X N : Subgroup G}
    (hXN : ∀ x ∈ X, ∀ a ∈ N, x * a * x⁻¹ ∈ N) : X ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hXN x hx h hh
  · intro hh
    have h' := hXN x⁻¹ (X.inv_mem hx) _ hh
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rw [e] at h'
    exact h'

theorem cent203b_card_subgroupOf {H X : Subgroup G} (h : H ≤ X) :
    Nat.card ↥(H.subgroupOf X) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem cent203b_main (d : Std20Frame K K' J S R R' W V z t)
    (hpad : padicValNat 2 ((oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔
      (K ⊔ K')).subgroupOf (sec20X (CoreAssembly.conjClass K) z K K')).index ≤ 1)
    {x : G} (hxX : x ∈ sec20X (CoreAssembly.conjClass K) z K K')
    (hxK : x ∈ trivialOnQuot K) (hxK' : x ∈ trivialOnQuot K') :
    x ∈ oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ Subgroup.zpowers z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : z ≠ 1 := d.viol.hzK.ne_one
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hzK : z ∈ K := d.viol.hzK.mem
  have hzK' : z ∈ K' := d.late_hzK'.mem
  have hzcomm := cent203b_z_comm d
  set X := sec20X (CoreAssembly.conjClass K) z K K' with hXdef
  set N := oddCoreOf X ⊔ (K ⊔ K') with hNdef
  set D := (trivialOnQuot K ⊓ trivialOnQuot K') ⊓ X with hDdef
  have hzX : z ∈ X := le_sec20X_left hzK
  have hNX : N ≤ X := sup_le (oddCoreOf_le_self X) (sup_le le_sec20X_left le_sec20X_right)
  have hDX : D ≤ X := inf_le_right
  have hzN : z ∈ N := Subgroup.mem_sup_right (Subgroup.mem_sup_left hzK)
  have hzD : z ∈ D := Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
    ⟨cent203b_mem_trivialOnQuot_of_comm K (fun y hy => hzcomm y (le_sec20X_left hy)),
      cent203b_mem_trivialOnQuot_of_comm K' (fun y hy => hzcomm y (le_sec20X_right hy))⟩, hzX⟩
  have hXnD : X ≤ Subgroup.normalizer (D : Set G) :=
    cent203b_le_normalizer_of_closed fun x hx a ha => cent203b_D_normal d hx ha
  have hXnN : X ≤ Subgroup.normalizer (N : Set G) :=
    cent203b_le_normalizer_of_closed fun x hx a ha => cent203b_N_normal d hx ha
  haveI hNn : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr hXnN
  haveI hDn : (D.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDX).mpr hXnD
  haveI hZn : ((Subgroup.zpowers z).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.zpowers_le.mpr hzX)).mpr
      (cent203b_le_normalizer_zpowers hzcomm)
  set Dx : Subgroup X := D.subgroupOf X with hDxdef
  set Nx : Subgroup X := N.subgroupOf X with hNxdef
  set Zx : Subgroup X := (Subgroup.zpowers z).subgroupOf X with hZxdef
  set Qx : Subgroup X := (oddCoreOf X ⊓ D).subgroupOf X with hQxdef
  haveI : Dx.Normal := hDn
  haveI : Nx.Normal := hNn
  haveI : Zx.Normal := hZn
  have hDN_kerG : D ⊔ N ≤ kerG K :=
    sup_le ((inf_le_left.trans inf_le_left).trans cent203b_trivialOnQuot_le_kerG)
      (cent203b_N_le_kerG d)
  obtain ⟨v, hvX, hvkerG, hv2N⟩ := cent203b_exists_v d
  have hvD : v ∉ D ⊔ N := fun h => hvkerG (hDN_kerG h)
  set vx : X := ⟨v, hvX⟩ with hvxdef
  have hv_out : vx ∉ Dx ⊔ Nx := by
    intro h
    have hle : Dx ⊔ Nx ≤ (D ⊔ N).comap X.subtype :=
      sup_le (fun a ha => Subgroup.mem_comap.mpr
          (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp ha)))
        (fun a ha => Subgroup.mem_comap.mpr
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp ha)))
    exact hvD (Subgroup.mem_comap.mp (hle h))
  have hv_sq : vx * vx ∈ Dx ⊔ Nx :=
    Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hv2N)
  have h2D : 2 ∣ (Dx ⊔ Nx).index := cent203b_two_dvd_index (Dx ⊔ Nx) hv_out hv_sq
  have hm : Nx.index = Nx.relIndex Dx * (Dx ⊔ Nx).index := by
    have e := Subgroup.relIndex_mul_index (le_sup_left : Nx ≤ Nx ⊔ Dx)
    rw [Subgroup.relIndex_sup_left, sup_comm] at e
    exact e.symm
  have hNx0 : Nx.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hNx_odd : ¬ 2 ∣ Nx.relIndex Dx := cent203b_not_two_dvd hm hNx0 hpad h2D
  have hZD : (Subgroup.zpowers z).relIndex D = Zx.relIndex Dx :=
    (Subgroup.relIndex_subgroupOf hDX).symm
  have hZle : Zx ≤ Dx ⊓ Nx := by
    intro w hw
    have hw' := Subgroup.mem_subgroupOf.mp hw
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr (Subgroup.zpowers_le.mpr hzD hw'),
      Subgroup.mem_subgroupOf.mpr (Subgroup.zpowers_le.mpr hzN hw')⟩
  have hQle : Qx ≤ Dx ⊓ Nx := by
    intro w hw
    have hw' := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨hwO, hwD⟩ := Subgroup.mem_inf.mp hw'
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hwD,
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hwO)⟩
  have hkey : Dx ⊓ Nx ≤ Qx ⊔ Zx := by
    intro w hw
    obtain ⟨hwD, hwN⟩ := Subgroup.mem_inf.mp hw
    have hwD' : (w : G) ∈ D := Subgroup.mem_subgroupOf.mp hwD
    have hwN' : (w : G) ∈ N := Subgroup.mem_subgroupOf.mp hwN
    obtain ⟨u, hu, e, he, hwe⟩ := cent203b_inter d hwD'.1.1 hwD'.1.2 hwN'
    rcases he with he | he
    · rw [he, mul_one] at hwe
      have hwQ : w ∈ Qx := Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mpr ⟨by rw [hwe]; exact hu, hwD'⟩)
      exact Subgroup.mem_sup_left hwQ
    · have huD : u ∈ D := by
        have hu' : u = (w : G) * z⁻¹ := by
          rw [hwe, he]
          group
        rw [hu']
        exact D.mul_mem hwD' (D.inv_mem hzD)
      have huX : u ∈ X := oddCoreOf_le_self X hu
      have huQ : (⟨u, huX⟩ : X) ∈ Qx :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hu, huD⟩)
      have hzZ : (⟨z, hzX⟩ : X) ∈ Zx := Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z)
      have hwe' : w = (⟨u, huX⟩ : X) * ⟨z, hzX⟩ := Subtype.ext (by
            rw [Subgroup.coe_mul]
            rw [hwe, he])
      rw [hwe']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huQ) (Subgroup.mem_sup_right hzZ)
  have hZQodd : Odd (Nat.card ↥Qx) := by
    rw [hQxdef, cent203b_card_subgroupOf (inf_le_right.trans hDX)]
    exact Odd.of_dvd_nat (oddCoreOf_odd_natCard X) (Subgroup.card_dvd_of_le inf_le_left)
  have hZcard : Nat.card ↥Zx = 2 := by
    have hordz : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    rw [hZxdef, cent203b_card_subgroupOf (Subgroup.zpowers_le.mpr hzX), Nat.card_zpowers, hordz]
  have hZQbot : Zx ⊓ Qx = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(Zx ⊓ Qx) ∣ Nat.card ↥Zx := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(Zx ⊓ Qx) ∣ Nat.card ↥Qx := Subgroup.card_dvd_of_le inf_le_right
    rw [hZcard] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      obtain ⟨m, hm'⟩ := hZQodd
      obtain ⟨k, hk⟩ := h2
      omega
  have hZQrel : Zx.relIndex Qx = Nat.card ↥Qx := by
    have h := Subgroup.relIndex_mul_card (H := Zx) (K := Qx)
    rw [hZQbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hZDodd : ¬ 2 ∣ Zx.relIndex Dx := by
    have e1 : Zx.relIndex (Dx ⊓ Nx) * (Dx ⊓ Nx).relIndex Dx = Zx.relIndex Dx :=
      Subgroup.relIndex_mul_relIndex Zx (Dx ⊓ Nx) Dx hZle inf_le_left
    have e2 : (Dx ⊓ Nx).relIndex Dx = Nx.relIndex Dx := Subgroup.inf_relIndex_left Dx Nx
    have e3 : Zx.relIndex (Dx ⊓ Nx) = Nat.card ↥Qx := by
      have hsup : Dx ⊓ Nx = Qx ⊔ Zx := le_antisymm hkey (sup_le hQle hZle)
      rw [hsup, Subgroup.relIndex_sup_right, hZQrel]
    rw [← e1, e2, e3]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h1
    · obtain ⟨m, hm'⟩ := hZQodd
      obtain ⟨k, hk⟩ := h1
      omega
    · exact hNx_odd h1
  have hidx : ¬ 2 ∣ (Subgroup.zpowers z).relIndex D := by
    rw [hZD]
    exact hZDodd
  have hzc : ∀ d' ∈ D, z * d' = d' * z := fun d' hd' => hzcomm d' (hDX hd')
  obtain ⟨Y, hYD, hYodd, hYnorm, hYcov⟩ :=
    cent203b_exists_normal_complement D hzD hz1 hz2 hzc hidx
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) :=
    cent203b_le_normalizer_of_closed fun x hx a ha => hYnorm x (hXnD hx) a ha
  have hYO : Y ≤ oddCoreOf X := le_oddCoreOf_of_normalizes (hYD.trans hDX) hXY hYodd
  have hxD : x ∈ D := Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxK, hxK'⟩, hxX⟩
  exact sup_le_sup_right hYO _ (hYcov x hxD)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
