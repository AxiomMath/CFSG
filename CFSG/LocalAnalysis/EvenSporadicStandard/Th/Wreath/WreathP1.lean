module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathN1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.WreathGoursat
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.UnitriangularCoord
public import CFSG.LinearAlgebra.GL4OddGeneration

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd CFSG.GroupTheory Matrix

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D : Subgroup G} {z b : G}

theorem wFix_add_one (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) :
    wFix hD (w + 1) = wKer hD w := by
  ext v
  constructor
  · rintro ⟨x, rfl, hx⟩
    refine ⟨x, rfl, ?_⟩
    change w x + x = x at hx
    have h : w x + x = 0 + x := by simpa using hx
    exact add_right_cancel h
  · rintro ⟨x, rfl, hx⟩
    refine ⟨x, rfl, ?_⟩
    change w x + x = x
    rw [hx, zero_add]

theorem wKer_add_one (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) :
    wKer hD (w + 1) = wFix hD w := by
  ext v
  constructor
  · rintro ⟨x, rfl, hx⟩
    refine ⟨x, rfl, ?_⟩
    change w x + x = 0 at hx
    have h : w x + x = x + x := by rw [hx, VSub.add_self_apply hD x]
    exact add_right_cancel h
  · rintro ⟨x, rfl, hx⟩
    refine ⟨x, rfl, ?_⟩
    change w x + x = 0
    rw [hx]
    exact VSub.add_self_apply hD x

theorem wComm_add_one (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) :
    wComm hD (w + 1) = wComm hD w := by
  ext n
  constructor
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    have h : vConj hD n * w + vConj hD n = w * vConj hD n + vConj hD n := by
      simpa only [mul_add, mul_one, add_mul, one_mul] using hc
    exact add_right_cancel h
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    rw [mul_add, mul_one, add_mul, one_mul, hc]

theorem add_one_add_one (hD : DHyp A Aa t D) (w : AddMonoid.End (VSub hD)) :
    w + 1 + 1 = w := by
  rw [add_assoc, VSub.add_self hD 1, add_zero]

theorem add_one_mul_add_one (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) : (w + 1) * (w + 1) = w + 1 := by
  calc (w + 1) * (w + 1) = w * (w + 1) + 1 * (w + 1) := add_mul w 1 (w + 1)
    _ = (w * w + w * 1) + (1 * w + 1 * 1) := by rw [mul_add, mul_add, one_mul, one_mul]
    _ = (w * w + w) + (w + 1) := by rw [mul_one, one_mul, mul_one]
    _ = (w + w) + (w + 1) := by rw [hww]
    _ = w + 1 := by rw [VSub.add_self hD w, zero_add]

theorem vConj_t_mul_add_one_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) :
    vConj hD t * (w + 1) * vConj hD t = w + 1 + 1 := by
  have hτ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  calc vConj hD t * (w + 1) * vConj hD t
      = (vConj hD t * w + vConj hD t) * vConj hD t := by rw [mul_add, mul_one]
    _ = vConj hD t * w * vConj hD t + vConj hD t * vConj hD t := by rw [add_mul]
    _ = (w + 1) + 1 := by rw [hτw, hτ]

theorem commute_add_one_of_commute (hD : DHyp A Aa t D) {f w : AddMonoid.End (VSub hD)}
    (h : f * w = w * f) : f * (w + 1) = (w + 1) * f := by
  rw [mul_add, mul_one, add_mul, one_mul, h]

theorem conj_mem_wreathN₁ (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)} {n x : G}
    (hn : n ∈ normalizer (Q : Set G) ⊓ wComm hD w) (hx : x ∈ wreathN₁ hD Q w) :
    n * x * n⁻¹ ∈ wreathN₁ hD Q w := by
  have hx' := (mem_wreathN₁_iff hD).1 hx
  refine (mem_wreathN₁_iff hD).2 ⟨?_, ?_, ?_⟩
  · exact (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).mul_mem hn.1 hx'.1)
      ((normalizer (Q : Set G)).inv_mem hn.1)
  · exact (wComm hD w).mul_mem ((wComm hD w).mul_mem hn.2 hx'.2.1)
      ((wComm hD w).inv_mem hn.2)
  · intro v hv
    have hv' : n⁻¹ * v * n ∈ wKer hD w := by
      simpa only [inv_inv] using
        conj_mem_wKer_of_mem_wComm hD ((wComm hD w).inv_mem hn.2) hv
    calc (n * x * n⁻¹) * v * (n * x * n⁻¹)⁻¹
        = n * (x * (n⁻¹ * v * n) * x⁻¹) * n⁻¹ := by group
      _ = n * (n⁻¹ * v * n) * n⁻¹ := by rw [hx'.2.2 _ hv']
      _ = v := by group

theorem conj_mem_wreathP₁ (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)} {n x : G}
    (hn : n ∈ normalizer (Q : Set G) ⊓ wComm hD w) (hx : x ∈ wreathP₁ hD Q w) :
    n * x * n⁻¹ ∈ wreathP₁ hD Q w := by
  refine Subgroup.closure_induction
    (p := fun y _ => n * y * n⁻¹ ∈ wreathP₁ hD Q w) ?_ ?_ ?_ ?_ hx
  · intro y hy
    refine subset_closure ⟨conj_mem_wreathN₁ hD hn hy.1, ?_⟩
    have hord : orderOf (n * y * n⁻¹) = orderOf y := by
      rw [← MulAut.conj_apply n y]
      exact MulEquiv.orderOf_eq (MulAut.conj n) y
    rw [hord]
    exact hy.2
  · simpa using (wreathP₁ hD Q w).one_mem
  · intro x y _ _ hx' hy'
    have h : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    rw [h]
    exact (wreathP₁ hD Q w).mul_mem hx' hy'
  · intro x _ hx'
    have h : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    rw [h]
    exact (wreathP₁ hD Q w).inv_mem hx'

theorem wreathP₁_le (hD : DHyp A Aa t D) (Q : Subgroup G) (w : AddMonoid.End (VSub hD)) :
    wreathP₁ hD Q w ≤ normalizer (Q : Set G) ⊓ wComm hD w :=
  (wreathP₁_le_wreathN₁ hD Q w).trans inf_le_left

theorem conj_mem_wreathE₂ (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)} {n e : G}
    (hn : n ∈ normalizer (Q : Set G) ⊓ wComm hD w) (he : e ∈ wreathE₂ hD Q w) :
    n * e * n⁻¹ ∈ wreathE₂ hD Q w := by
  have he' := (mem_wreathE₂_iff hD).1 he
  refine (mem_wreathE₂_iff hD).2 ⟨?_, ?_⟩
  · exact (mem_normalizer_iff.1 hn.1 e).1 he'.1
  · intro x hx
    have hx' : n⁻¹ * x * n ∈ wreathP₁ hD Q w := by
      have h := conj_mem_wreathP₁ hD ((normalizer (Q : Set G) ⊓ wComm hD w).inv_mem hn) hx
      rwa [inv_inv] at h
    calc x * (n * e * n⁻¹) = n * ((n⁻¹ * x * n) * e) * n⁻¹ := by group
      _ = n * (e * (n⁻¹ * x * n)) * n⁻¹ := by rw [he'.2 _ hx']
      _ = (n * e * n⁻¹) * x := by group

theorem commutator_mem_wreathP₁_inf (hD : DHyp A Aa t D) {Q : Subgroup G}
    {w : AddMonoid.End (VSub hD)} {x y : G} (hx : x ∈ wreathP₁ hD Q w)
    (hy : y ∈ wreathP₁ hD Q (w + 1)) :
    x * y * x⁻¹ * y⁻¹ ∈ wreathP₁ hD Q w ⊓ wreathP₁ hD Q (w + 1) := by
  have hxN : x ∈ normalizer (Q : Set G) ⊓ wComm hD w := wreathP₁_le hD Q w hx
  have hyN : y ∈ normalizer (Q : Set G) ⊓ wComm hD w := by
    have h := wreathP₁_le hD Q (w + 1) hy
    simpa only [wComm_add_one hD w] using h
  have hxN' : x ∈ normalizer (Q : Set G) ⊓ wComm hD (w + 1) := by
    simpa only [wComm_add_one hD w] using hxN
  refine ⟨?_, ?_⟩
  · have h1 : y * x⁻¹ * y⁻¹ ∈ wreathP₁ hD Q w := by
      have h := conj_mem_wreathP₁ hD hyN ((wreathP₁ hD Q w).inv_mem hx)
      simpa only [inv_inv] using h
    have h : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [h]
    exact (wreathP₁ hD Q w).mul_mem hx h1
  · have h1 : x * y * x⁻¹ ∈ wreathP₁ hD Q (w + 1) := conj_mem_wreathP₁ hD hxN' hy
    exact (wreathP₁ hD Q (w + 1)).mul_mem h1 ((wreathP₁ hD Q (w + 1)).inv_mem hy)

theorem QHyp.t_mem_normalizer (H : ThCyc G L R t) {Q : Subgroup G} (hQ : QHyp L A D t Q) :
    t ∈ normalizer (Q : Set G) := by
  have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  refine mem_normalizer_iff.2 fun q => ⟨hQ.conj_t_mem q, fun hq => ?_⟩
  have h := hQ.conj_t_mem (t * q * t⁻¹) hq
  have e : t * (t * q * t⁻¹) * t⁻¹ = q := by
    rw [htinv]
    calc t * (t * q * t) * t = (t * t) * q * (t * t) := by group
      _ = q := by rw [ht2, one_mul, mul_one]
  rwa [e] at h

private theorem vConj_conj_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G)) :
    vConj hD (t * n * t⁻¹) = vConj hD t * vConj hD n * vConj hD t := by
  have ht := H.t_mem_normalizer_omega1 W W2 hD
  have htinv : t⁻¹ = t := by
    have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
    exact inv_eq_of_mul_eq_one_right ht2
  have htn : t * n ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).mul_mem ht hn
  calc vConj hD (t * n * t⁻¹)
      = vConj hD (t * n) * vConj hD t⁻¹ :=
        vConj_mul hD htn ((normalizer (omega1 D hD.comm : Set G)).inv_mem ht)
    _ = (vConj hD t * vConj hD n) * vConj hD t⁻¹ := by rw [vConj_mul hD ht hn]
    _ = vConj hD t * vConj hD n * vConj hD t := by rw [htinv]

private theorem conj_t_commute_add_one (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    {n : G} (hτw : vConj hD t * w * vConj hD t = w + 1)
    (hn : vConj hD n * w = w * vConj hD n) :
    (vConj hD t * vConj hD n * vConj hD t) * (w + 1) =
      (w + 1) * (vConj hD t * vConj hD n * vConj hD t) := by
  set τ := vConj hD t with hτdef
  set ρ := vConj hD n with hρdef
  have hτ : τ * τ = 1 := by
    rw [hτdef]
    exact H.vConj_t_mul_self W W2 hD
  have hτw' : τ * w * τ = w + 1 := by
    rw [hτdef]
    exact hτw
  have hn' : ρ * w = w * ρ := by
    rw [hρdef]
    exact hn
  calc (τ * ρ * τ) * (w + 1)
      = (τ * ρ * τ) * (τ * w * τ) := by rw [← hτw']
    _ = τ * ρ * w * τ := by
          rw [show (τ * ρ * τ) * (τ * w * τ) = τ * ρ * (τ * τ) * w * τ from by
            noncomm_ring, hτ, mul_one]
    _ = τ * w * ρ * τ := by
          calc τ * ρ * w * τ = τ * (ρ * w) * τ := by noncomm_ring
            _ = τ * (w * ρ) * τ := by rw [hn']
            _ = τ * w * ρ * τ := by noncomm_ring
    _ = (τ * w * τ) * (τ * ρ * τ) := by
          rw [show (τ * w * τ) * (τ * ρ * τ) = τ * w * (τ * τ) * ρ * τ from by
            noncomm_ring, hτ, mul_one]
    _ = (w + 1) * (τ * ρ * τ) := by rw [hτw']

private theorem conj_t_mem_wreathN₁_forward (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) {Q : Subgroup G} (hQ : QHyp L A D t Q)
    {x : G} (hx : x ∈ wreathN₁ hD Q w) :
    t * x * t⁻¹ ∈ wreathN₁ hD Q (w + 1) := by
  have hx' := (mem_wreathN₁_iff hD).1 hx
  have htQ : t ∈ normalizer (Q : Set G) := QHyp.t_mem_normalizer H hQ
  have htV : t ∈ normalizer (omega1 D hD.comm : Set G) := H.t_mem_normalizer_omega1 W W2 hD
  have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  refine (mem_wreathN₁_iff hD).2 ⟨?_, ?_, ?_⟩
  · exact (normalizer (Q : Set G)).mul_mem
      ((normalizer (Q : Set G)).mul_mem htQ hx'.1)
      ((normalizer (Q : Set G)).inv_mem htQ)
  · refine ⟨?_, ?_⟩
    · exact (normalizer (omega1 D hD.comm : Set G)).mul_mem
        ((normalizer (omega1 D hD.comm : Set G)).mul_mem htV hx'.2.1.1)
        ((normalizer (omega1 D hD.comm : Set G)).inv_mem htV)
    · rw [vConj_conj_t H W W2 hD hx'.2.1.1]
      exact conj_t_commute_add_one H W W2 hD hτw hx'.2.1.2
  · intro v hv
    rw [wKer_add_one hD w] at hv
    have hv' : t⁻¹ * v * t ∈ wKer hD w := by
      have h := conj_t_mem_wKer_of_mem_wFix H W W2 hD hτw hv
      simpa only [htinv] using h
    have h' : (t * x * t⁻¹) * v * (t * x * t⁻¹)⁻¹ =
        t * (x * (t⁻¹ * v * t) * x⁻¹) * t⁻¹ := by group
    rw [h', hx'.2.2 _ hv']
    group

private theorem conj_t_mem_wreathP₁_forward (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) {Q : Subgroup G} (hQ : QHyp L A D t Q)
    {x : G} (hx : x ∈ wreathP₁ hD Q w) :
    t * x * t⁻¹ ∈ wreathP₁ hD Q (w + 1) := by
  refine Subgroup.closure_induction
    (p := fun y _ => t * y * t⁻¹ ∈ wreathP₁ hD Q (w + 1)) ?_ ?_ ?_ ?_ hx
  · intro y hy
    refine subset_closure ⟨conj_t_mem_wreathN₁_forward H W W2 hD hτw hQ hy.1, ?_⟩
    have hord : orderOf (t * y * t⁻¹) = orderOf y := by
      rw [← MulAut.conj_apply t y]
      exact MulEquiv.orderOf_eq (MulAut.conj t) y
    rw [hord]
    exact hy.2
  · simpa using (wreathP₁ hD Q (w + 1)).one_mem
  · intro x y _ _ hx' hy'
    have h : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [h]
    exact (wreathP₁ hD Q (w + 1)).mul_mem hx' hy'
  · intro x _ hx'
    have h : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [h]
    exact (wreathP₁ hD Q (w + 1)).inv_mem hx'

theorem map_conj_t_wreathP₁ (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w * vConj hD t = w + 1) {Q : Subgroup G} (hQ : QHyp L A D t Q) :
    (wreathP₁ hD Q w).map (MulAut.conj t).toMonoidHom = wreathP₁ hD Q (w + 1) := by
  have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change t * x * t⁻¹ ∈ wreathP₁ hD Q (w + 1)
    exact conj_t_mem_wreathP₁_forward H W W2 hD hτw hQ hx
  · intro y hy
    have hτw' : vConj hD t * (w + 1) * vConj hD t = (w + 1) + 1 :=
      vConj_t_mul_add_one_mul H W W2 hD hτw
    have hy' : t * y * t⁻¹ ∈ wreathP₁ hD Q ((w + 1) + 1) :=
      conj_t_mem_wreathP₁_forward H W W2 hD hτw' hQ hy
    rw [add_one_add_one hD w] at hy'
    refine ⟨t * y * t⁻¹, hy', ?_⟩
    show (MulAut.conj t) (t * y * t⁻¹) = y
    rw [MulAut.conj_apply]
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
      _ = y := by rw [htinv]; simp only [ht2, one_mul, mul_one]

private theorem thV_iota1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1) (a : A) :
    thV t (iota1 hD w hww (H.A_le_omega1 W W2 hD) a : G) = a := by
  let v : VSub hD := AbelianSub.mk (iota1 hD w hww (H.A_le_omega1 W W2 hD) a : G)
    (wFix_le_omega1 hD w (iota1 hD w hww (H.A_le_omega1 W W2 hD) a).2)
  have hv : v.val ∈ wFix hD w := by
    dsimp only [v]
    rw [AbelianSub.val_mk]
    exact (iota1 hD w hww (H.A_le_omega1 W W2 hD) a).2
  have h := congrArg (fun x : wFix hD w => (x : G))
    (iota1_thV H W W2 hD hww hτw (y := v) hv)
  have hfix : (iota1 hD w hww (H.A_le_omega1 W W2 hD)
      ⟨thV t v.val, H.thV_mem_A W W2 hD (AbelianSub.val_mem v)⟩ : wFix hD w) =
      iota1 hD w hww (H.A_le_omega1 W W2 hD) a := by
    apply Subtype.ext
    simpa only [v, AbelianSub.val_mk] using h
  exact congrArg Subtype.val (iota1_injective H W W2 hD hww hτw hfix)

private theorem isCoord_wFix (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {w : AddMonoid.End (VSub hD)}
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c) :
    IsCoord (wFix hD w) (fun v => c (thV t v)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    have haV : a ∈ omega1 D hD.comm := wFix_le_omega1 hD w ha
    have hbV : b ∈ omega1 D hD.comm := wFix_le_omega1 hD w hb
    show c (thV t (a * b)) = c (thV t a) + c (thV t b)
    rw [H.thV_mul W W2 hD haV hbV]
    exact hc.mul _ (H.thV_mem_A W W2 hD haV) _ (H.thV_mem_A W W2 hD hbV)
  · intro a ha b hb hab
    have haV : a ∈ omega1 D hD.comm := wFix_le_omega1 hD w ha
    have hbV : b ∈ omega1 D hD.comm := wFix_le_omega1 hD w hb
    have hA : thV t a = thV t b :=
      hc.inj _ (H.thV_mem_A W W2 hD haV) _ (H.thV_mem_A W W2 hD hbV) hab
    have hA' : (⟨thV t a, H.thV_mem_A W W2 hD haV⟩ : A) =
        ⟨thV t b, H.thV_mem_A W W2 hD hbV⟩ := Subtype.ext hA
    have hia : (iota1 hD w hww (H.A_le_omega1 W W2 hD)
        ⟨thV t a, H.thV_mem_A W W2 hD haV⟩ : wFix hD w) = ⟨a, ha⟩ := by
      simpa using iota1_thV H W W2 hD hww hτw
        (y := AbelianSub.mk a haV) (by simpa using ha)
    have hib : (iota1 hD w hww (H.A_le_omega1 W W2 hD)
        ⟨thV t b, H.thV_mem_A W W2 hD hbV⟩ : wFix hD w) = ⟨b, hb⟩ := by
      simpa using iota1_thV H W W2 hD hww hτw
        (y := AbelianSub.mk b hbV) (by simpa using hb)
    have hfix : (⟨a, ha⟩ : wFix hD w) = ⟨b, hb⟩ := by
      rw [← hia, ← hib, hA']
    exact congrArg Subtype.val hfix
  · intro u
    obtain ⟨a, haA, hca⟩ := hc.onto u
    refine ⟨(iota1 hD w hww (H.A_le_omega1 W W2 hD) ⟨a, haA⟩ : G),
      (iota1 hD w hww (H.A_le_omega1 W W2 hD) ⟨a, haA⟩).2, ?_⟩
    show c (thV t (iota1 hD w hww (H.A_le_omega1 W W2 hD) ⟨a, haA⟩ : G)) = u
    rw [thV_iota1 H W W2 hD hww hτw ⟨a, haA⟩, hca]

theorem ThCyc.exists_wreathN₁_matHom (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) :
    ∃ c₁ : G → (Fin 4 → ZMod 2), IsCoord (wFix hD w) c₁ ∧
      ∃ ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2),
        (∀ σ : ↥(wreathN₁ hD Q w),
          IsRep (wFix hD w) c₁ σ (ρ₁ σ : Matrix (Fin 4) (Fin 4) (ZMod 2))) ∧
          Function.Surjective ρ₁ := by
  classical
  obtain ⟨c, hc, -⟩ := W.exists_coord_unitriangular
  let c₁ : G → (Fin 4 → ZMod 2) := fun v => c (thV t v)
  have hc₁ : IsCoord (wFix hD w) c₁ :=
    isCoord_wFix H W W2 hD hww hτw hc
  have hN : ∀ q ∈ wreathN₁ hD Q w, ∀ a ∈ wFix hD w, q * a * q⁻¹ ∈ wFix hD w := by
    intro q hq a ha
    exact conj_mem_wFix_of_mem_wComm hD ((mem_wreathN₁_iff hD).1 hq).2.1 ha
  obtain ⟨m, hm⟩ := hc₁.exists_matHom (wreathN₁ hD Q w) hN
  let ρ₁ : ↥(wreathN₁ hD Q w) →* GL (Fin 4) (ZMod 2) := m.toHomUnits
  refine ⟨c₁, hc₁, ρ₁, ?_, ?_⟩
  · intro σ
    simpa only [ρ₁, MonoidHom.coe_toHomUnits] using hm σ
  · intro M
    have hMinj : Function.Injective
        (M : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec := by
      intro u v huv
      have h := congrArg (fun x =>
        ((M⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) huv
      simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec] using h
    obtain ⟨n, hnL, hnA, hnrep⟩ := hc.exists_lift W.surj hMinj
    have hnN : n ∈ normalizer (A : Set G) := by
      have hmaple : A.map (MulAut.conj n).toMonoidHom ≤ A := by
        rintro _ ⟨a, ha, rfl⟩
        simpa [MulAut.conj_apply] using hnA a ha
      have hcard : Nat.card (A.map (MulAut.conj n).toMonoidHom) = Nat.card A :=
        Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom)
          (MulAut.conj n).injective
      exact Subgroup.mem_normalizer_iff_map_conj_eq.2
        (Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq hcard.symm))
    obtain ⟨m₀, hm₀, hm₀Ker, hm₀Fix⟩ :=
      H.exists_trivial_wKer_of_wreath W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
        ⟨hnL, hnN⟩
    have hm₀N₁ : m₀ ∈ wreathN₁ hD Q w := by
      refine (mem_wreathN₁_iff hD).2 ⟨hm₀.1, hm₀.2, ?_⟩
      intro v hv
      exact hm₀Ker v hv
    have hrepρ : IsRep (wFix hD w) c₁ m₀ (ρ₁ ⟨m₀, hm₀N₁⟩) := by
      simpa only [ρ₁, MonoidHom.coe_toHomUnits] using hm ⟨m₀, hm₀N₁⟩
    have hrepM : IsRep (wFix hD w) c₁ m₀ M := by
      intro v hv
      have hvV : v ∈ omega1 D hD.comm := wFix_le_omega1 hD w hv
      calc c₁ (m₀ * v * m₀⁻¹) = c (thV t (m₀ * v * m₀⁻¹)) := rfl
        _ = c (thV t (n * v * n⁻¹)) := by rw [hm₀Fix v hv]
        _ = c (n * thV t v * n⁻¹) := by rw [H.thV_conj W W2 hD hnL]
        _ = M *ᵥ c (thV t v) := hnrep _ (H.thV_mem_A W W2 hD hvV)
        _ = M *ᵥ c₁ v := rfl
    refine ⟨⟨m₀, hm₀N₁⟩, ?_⟩
    exact Units.ext (hc₁.rep_unique hrepρ hrepM)

theorem ThCyc.exists_wreathP₁_conj_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hww : w * w = w) (hτw : vConj hD t * w * vConj hD t = w + 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q) {g : G}
    (hgQ : g ∈ normalizer (Q : Set G)) (hgw : g ∈ wComm hD w)
    (hgM : g ∉ normalizer (D : Set G)) {m : G} (hm : m ∈ wreathN₁ hD Q w) :
    ∃ p ∈ wreathP₁ hD Q w, ∀ v ∈ wFix hD w, p * v * p⁻¹ = m * v * m⁻¹ := by
  classical
  obtain ⟨c₁, hc₁, ρ₁, hrep, hsurj⟩ :=
    H.exists_wreathN₁_matHom W W2 hD h4 hb hwH hww hτw hQ hgQ hgw hgM
  obtain ⟨γ, hγ, hγρ⟩ :=
    CFSG.LinearAlgebra.exists_mem_closure_odd_map_eq ρ₁ hsurj (ρ₁ ⟨m, hm⟩)
  have hgen : (wreathN₁ hD Q w).subtype '' {x : ↥(wreathN₁ hD Q w) | Odd (orderOf x)} =
      {x : G | x ∈ wreathN₁ hD Q w ∧ Odd (orderOf x)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      change Odd (orderOf (y : G))
      rwa [Subgroup.orderOf_coe]
    · rintro ⟨hxN, hxodd⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      show Odd (orderOf (⟨x, hxN⟩ : ↥(wreathN₁ hD Q w)))
      rwa [Subgroup.orderOf_mk]
  have hmap : (Subgroup.closure {x : ↥(wreathN₁ hD Q w) | Odd (orderOf x)}).map
      (wreathN₁ hD Q w).subtype = wreathP₁ hD Q w := by
    rw [MonoidHom.map_closure, hgen, wreathP₁]
  have hγP : (γ : G) ∈ wreathP₁ hD Q w := by
    rw [← hmap]
    exact ⟨γ, hγ, rfl⟩
  have hmrep : IsRep (wFix hD w) c₁ m (ρ₁ ⟨m, hm⟩) := hrep ⟨m, hm⟩
  refine ⟨(γ : G), hγP, ?_⟩
  intro v hv
  have hγw : (γ : G) ∈ wComm hD w := ((mem_wreathN₁_iff hD).1 γ.2).2.1
  have hmw : m ∈ wComm hD w := ((mem_wreathN₁_iff hD).1 hm).2.1
  have hγFix : ∀ a ∈ wFix hD w, (γ : G) * a * (γ : G)⁻¹ ∈ wFix hD w :=
    fun a ha => conj_mem_wFix_of_mem_wComm hD hγw ha
  have hmFix : ∀ a ∈ wFix hD w, m * a * m⁻¹ ∈ wFix hD w :=
    fun a ha => conj_mem_wFix_of_mem_wComm hD hmw ha
  have hmrep' : IsRep (wFix hD w) c₁ m (ρ₁ γ) := by
    rw [hγρ]
    exact hmrep
  exact (hrep γ).conj_mem hc₁ hγFix hmFix hmrep' hv

end CFSG.EvenSporadicStandard.ThStd
