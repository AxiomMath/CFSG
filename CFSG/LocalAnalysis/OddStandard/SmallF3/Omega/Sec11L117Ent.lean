module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Out
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Nrm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sec11_mem_normalizer_oddCoreIn [Finite G] {X : Subgroup G} {x : G}
    (hx : x ∈ normalizer (X : Set G)) : x ∈ normalizer (oddCoreIn X : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  refine ⟨fun hy => sec11_conj_mem_oddCoreIn (Subgroup.mem_normalizer_iff.mpr hx) hy, fun hy => ?_⟩
  have hxinv : x⁻¹ ∈ normalizer (X : Set G) :=
    Subgroup.inv_mem _ (Subgroup.mem_normalizer_iff.mpr hx)
  have h := sec11_conj_mem_oddCoreIn hxinv hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y by group] at h

theorem sec11_x_nt1 [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) {x : G} (hxT : x ∈ T)
    (hx : IsOuterOn x (K1 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))) :
    ∃ y ∈ twoCoreIn K1, x * y * x⁻¹ * y⁻¹ ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  have hctx10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx10.toSec10Z).1
  have hxK0 : x ∈ normalizer (secK0 t z : Set G) :=
    (r.l111N G t L S z K1 K2 T R hctx).2.2.1 hxT
  have hxN : x ∈ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    sec11_mem_normalizer_oddCoreIn hxK0
  have hQ : Sec11Q8 G z (twoCoreIn K1) := sec11_Q8_K1 hp hctx10
  have hQK : twoCoreIn K1 ≤ K1 := twoCoreIn_le_self K1
  have hK : Nat.card K1 = 24 :=
    (sec10KS_main hp.facts.pockets5 hp.facts.centZ5 hpsp hctx10).1
  have hKQ : ∀ k ∈ K1, ∀ q ∈ twoCoreIn K1, k * q * k⁻¹ ∈ twoCoreIn K1 :=
    fun k hk q hq => sec11_twoCoreIn_conj_mem K1 hk hq
  have hKN : K1 ≤ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    (le_sup_left.trans (sec11_K_le_K0 hp.r10.lK0 hctx10)).trans
      (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
  have hNQ : ∀ n ∈ oddCoreIn (secK0 t z), ∀ q ∈ twoCoreIn K1, n * q = q * n := by
    intro n hn q hq
    exact sec11_N_centQ hp hctx10 hn (by
      rw [sec11_Q_eq_sup hp hctx10]
      exact Subgroup.mem_sup_left hq)
  have hKN1 : ∀ g ∈ K1, g ∈ oddCoreIn (secK0 t z) → g = 1 :=
    fun g hg hgN => sec11_K1_inf_N hp hctx10 hg hgN
  have hCK : ∀ k ∈ K1, (∀ q ∈ twoCoreIn K1, k * q = q * k) → k ∈ zpowers z :=
    sec10KS_cent_Qi hp.facts.pockets5 hp.facts.centZ5 hpsp hctx10
  exact hx.2 (sec11_out_abs hQ hQK hK hKQ hKN hNQ hKN1 hCK hx.1 hxN
    (sec11_x_normQ1 hp hctx hxT hx) hcon)

theorem sec11_x_nt2 [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) {x : G} (hxT : x ∈ T)
    (hx : IsOuterOn x (K2 ⊔ oddCoreIn (secK0 t z)) (oddCoreIn (secK0 t z))) :
    ∃ y ∈ twoCoreIn K2, x * y * x⁻¹ * y⁻¹ ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  have hctx10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx10.toSec10Z).1
  have hxK0 : x ∈ normalizer (secK0 t z : Set G) :=
    (r.l111N G t L S z K1 K2 T R hctx).2.2.1 hxT
  have hxN : x ∈ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    sec11_mem_normalizer_oddCoreIn hxK0
  have hQ : Sec11Q8 G z (twoCoreIn K2) := sec11_Q8_K2 hp hctx10
  have hQK : twoCoreIn K2 ≤ K2 := twoCoreIn_le_self K2
  have hK : Nat.card K2 = 24 :=
    (sec10KS_main hp.facts.pockets5 hp.facts.centZ5 hpsp hctx10).2.1
  have hKQ : ∀ k ∈ K2, ∀ q ∈ twoCoreIn K2, k * q * k⁻¹ ∈ twoCoreIn K2 :=
    fun k hk q hq => sec11_twoCoreIn_conj_mem K2 hk hq
  have hKN : K2 ≤ normalizer (oddCoreIn (secK0 t z) : Set G) :=
    (le_sup_right.trans (sec11_K_le_K0 hp.r10.lK0 hctx10)).trans
      (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
  have hNQ : ∀ n ∈ oddCoreIn (secK0 t z), ∀ q ∈ twoCoreIn K2, n * q = q * n := by
    intro n hn q hq
    exact sec11_N_centQ hp hctx10 hn (by
      rw [sec11_Q_eq_sup hp hctx10]
      exact Subgroup.mem_sup_right hq)
  have hKN1 : ∀ g ∈ K2, g ∈ oddCoreIn (secK0 t z) → g = 1 :=
    fun g hg hgN => sec11_K2_inf_N hp hctx10 hg hgN
  have hCK : ∀ k ∈ K2, (∀ q ∈ twoCoreIn K2, k * q = q * k) → k ∈ zpowers z :=
    sec10KS_cent_Qi hp.facts.pockets5 hp.facts.centZ5 hpsp hctx10.swap
  exact hx.2 (sec11_out_abs hQ hQK hK hKQ hKN hNQ hKN1 hCK hx.1 hxN
    (sec11_x_normQ2 hp hctx hxT hx) hcon)

end CFSG.OddStandard.SmallF3.Omega
