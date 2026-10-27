module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma mem_centerIn_iff' {K : Subgroup G} (a : G) :
    a ∈ centerIn K ↔ a ∈ K ∧ ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm⟩
  · rintro ⟨haK, hcent⟩
    exact ⟨⟨a, haK⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (hcent (y : G) y.2).symm, rfl⟩

theorem sec10_not_conj_z [Finite G] (h37 : Asc82Lemma37) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) (g : G) : g⁻¹ * z * g ≠ t := by
  intro hconj
  have hmem : g⁻¹ * z * g ∈ centralizer ({t} : Set G) := by
    rw [hconj]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have h37' :=
    h37 G t L hctx.toSec10Z.toSec10Setting.toSec3SettingLB z g hctx.toSec10Z.pocket hmem
  rw [hconj] at h37'
  rw [inf_eq_left.mpr hctx.component.le] at h37'
  have hlayer : CFSG.layer ↥L = ⊤ := by
    rw [CFSG.layer.eq_sSup]
    exact eq_top_iff.mpr (le_sSup
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
        hctx.component.isQuasisimple, Subgroup.IsSubnormal.top⟩)
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hzbot : z ∈ (⊥ : Subgroup G) := by
    rw [← h37']
    change z ∈ (CFSG.layer ↥L).map L.subtype
    rw [hlayer]
    exact ⟨⟨z, hzL⟩, Subgroup.mem_top _, rfl⟩
  have hz1 : z = 1 := by simpa using hzbot
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  rw [hz1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem sec10_conj_mem_omega1 {S : Subgroup G} {n : G} (hn : n ∈ normalizer (S : Set G)) {y : G}
    (hy : y ∈ omega1 (centerIn S)) : n⁻¹ * y * n ∈ omega1 (centerIn S) := by
  rw [omega1] at hy ⊢
  have hgen : ∀ x ∈ ({x | x ∈ centerIn S ∧ x ^ 2 = 1} : Set G),
      (MulAut.conj n⁻¹) x ∈ ({x | x ∈ centerIn S ∧ x ^ 2 = 1} : Set G) := by
    rintro x ⟨hxZ, hx2⟩
    obtain ⟨hxS, hxcomm⟩ := (mem_centerIn_iff' x).mp hxZ
    have hninv : n⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hn
    have hxSn : (MulAut.conj n⁻¹) x ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp hninv x).mp hxS
      simpa [MulAut.conj_apply] using this
    have hcommn : ∀ s ∈ S, ((MulAut.conj n⁻¹) x) * s = s * ((MulAut.conj n⁻¹) x) := by
      intro s hs
      have hns : n * s * n⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hn s).mp hs
      calc ((MulAut.conj n⁻¹) x) * s
          = n⁻¹ * (x * (n * s * n⁻¹)) * n := by rw [MulAut.conj_apply]; group
        _ = n⁻¹ * ((n * s * n⁻¹) * x) * n := by rw [hxcomm (n * s * n⁻¹) hns]
        _ = s * ((MulAut.conj n⁻¹) x) := by rw [MulAut.conj_apply]; group
    have hpow : ((MulAut.conj n⁻¹) x) ^ 2 = 1 := by
      have hm := map_pow (MulAut.conj n⁻¹) x 2
      rw [hx2, map_one] at hm
      exact hm.symm
    exact ⟨(mem_centerIn_iff' ((MulAut.conj n⁻¹) x)).mpr ⟨hxSn, hcommn⟩, hpow⟩
  have hle : (Subgroup.closure {x | x ∈ centerIn S ∧ x ^ 2 = 1}).map
      (MulAut.conj n⁻¹).toMonoidHom ≤ Subgroup.closure {x | x ∈ centerIn S ∧ x ^ 2 = 1} := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro x ⟨a, ha, rfl⟩
    exact hgen a ha
  have hy' := hle (Subgroup.mem_map_of_mem (MulAut.conj n⁻¹).toMonoidHom hy)
  simpa [MulAut.conj_apply] using hy'

theorem sec10_two_elem_cases {z t x : G} (hzt : z * t = t * z) (hz : orderOf z = 2)
    (ht : orderOf t = 2) (hx : x ∈ zpowers z ⊔ zpowers t) (hx2 : orderOf x = 2) :
    x = z ∨ x = t ∨ x = t * z := by
  have hc : ∀ b ∈ zpowers z, b * t = t * b := by
    intro b hb
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hj]
    exact ((Commute.zpow_left (show Commute z t from hzt) j)).eq
  obtain ⟨b, hb, i, hxi⟩ := (mem_sup_zpowers_iff_of_commute (B := zpowers z) hc).mp hx
  obtain ⟨j, hzj⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hx' : x = z ^ j * t ^ i := by rw [hxi, ← hzj]
  have hzi : z ^ j = z ^ (j % 2) := by
    refine (zpow_eq_zpow_iff_modEq).mpr ?_
    rw [hz]
    exact (Int.mod_modEq j 2).symm
  have hti : t ^ i = t ^ (i % 2) := by
    refine (zpow_eq_zpow_iff_modEq).mpr ?_
    rw [ht]
    exact (Int.mod_modEq i 2).symm
  rw [hx', hzi, hti]
  rcases Int.emod_two_eq_zero_or_one j with hj | hj <;>
    rcases Int.emod_two_eq_zero_or_one i with hi | hi
  · exfalso
    have h1 : x = 1 := by simp [hx', hzi, hti, hj, hi]
    rw [h1, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  · simp [hj, hi]
  · simp [hj, hi]
  · right; right
    simpa [hj, hi] using hzt

theorem sec10_normalizer_grows [Finite G] {S T : Subgroup G} (hT : IsPGroup 2 T) (hlt : S < T) :
    ∃ n ∈ T, n ∈ normalizer (S : Set G) ∧ n ∉ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  let H : Subgroup ↥T := S.subgroupOf T
  have hHlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hlt.ne (le_antisymm hlt.le (Subgroup.subgroupOf_eq_top.mp htop))
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥T)
  obtain ⟨x, hxnorm, hxH⟩ := SetLike.exists_of_lt (hnc H hHlt)
  have hxT : (x : G) ∈ T := x.2
  have hxnormS : (x : G) ∈ normalizer (S : Set G) := by
    have hmap := Subgroup.le_normalizer_map (f := T.subtype) (H := H)
    have hxmem : (x : G) ∈ (Subgroup.normalizer H).map T.subtype := ⟨x, hxnorm, rfl⟩
    have hthis := hmap hxmem
    rwa [Subgroup.map_subgroupOf_eq_of_le hlt.le] at hthis
  exact ⟨(x : G), hxT, hxnormS, fun hxS => hxH ((Subgroup.mem_subgroupOf).mpr hxS)⟩

theorem asc82Step105S_of (h37 : Asc82Lemma37) (h103 : Asc82Lemma103) (hb : Asc82Basic10) :
    Asc82Step105S := by
  intro G _ _ t L S z K1 K2 hctx hnot
  obtain ⟨hpsp, htC, htnotL, htS, hSN, hsylL⟩ := hb G t L S z hctx.toSec10Z
  have hsyl : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  obtain ⟨T, hT, hST⟩ := exists_isSylow2Of_ge hsyl.2.1 (le_top : S ≤ ⊤)
  have hTS : T = S := by
    by_contra hne
    have hlt : S < T := lt_of_le_of_ne hST (Ne.symm hne)
    obtain ⟨n, hnT, hnN, hnS⟩ := sec10_normalizer_grows hT.2.1 hlt
    have ht_omega : t ∈ omega1 (centerIn S) := by
      rw [h103 G t L S z hctx.toSec10Z]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have hconj_omega : n⁻¹ * t * n ∈ omega1 (centerIn S) :=
      sec10_conj_mem_omega1 hnN ht_omega
    rw [h103 G t L S z hctx.toSec10Z] at hconj_omega
    have horder : orderOf (n⁻¹ * t * n) = 2 := by
      have h1 : orderOf ((MulAut.conj n⁻¹) t) = orderOf t := MulEquiv.orderOf_eq _ _
      have h2 : (MulAut.conj n⁻¹) t = n⁻¹ * t * n := by
        rw [MulAut.conj_apply]; group
      rw [h2] at h1
      exact h1.trans hctx.involution
    have hzt : z * t = t * z := (hctx.central t htS).symm
    have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
    rcases sec10_two_elem_cases hzt hz2 hctx.involution hconj_omega horder with h | h | h
    · exfalso
      apply sec10_not_conj_z h37 hctx n⁻¹
      rw [inv_inv, ← h]
      group
    · have hnC : n ∈ centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h' : t * n = n * t := by
          calc t * n = n * (n⁻¹ * t * n) := by group
            _ = n * t := by rw [h]
        exact h'.symm
      let Q : Subgroup G := T ⊓ centralizer ({t} : Set G)
      have hQ2 : IsPGroup 2 Q := hT.2.1.to_le inf_le_left
      have hSQ : S ≤ Q := le_inf hST hsyl.1
      have hQS : Q = S := hsyl.eq_of_le inf_le_right hQ2 hSQ
      have hnQ : n ∈ Q := ⟨hnT, hnC⟩
      exact hnS (hQS ▸ hnQ)
    · exact absurd ⟨n, h⟩ hnot
  simpa [hTS] using hT

end CFSG.OddStandard.SmallF3.Omega
