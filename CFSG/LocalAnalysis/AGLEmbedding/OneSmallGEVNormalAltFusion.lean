module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVZCore
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroArith
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroCount

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem two_mul_lt_of_dvd {p c : ℕ} (hp5 : 5 ≤ p)
    (h : c = 0 ∨ c = p ^ 2 - 1 ∨ 2 * c = p ^ 2 - 1 ∨ c = 2 * (p - 1) ∨ c = (p - 1) ^ 2)
    (hdvd : p ∣ c + (p - 1)) : 2 * (p - 1) < c := by
  have hp1 : 1 ≤ p := by omega
  have hX : ((c + (p - 1) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [Nat.cast_add, zmod_cast_pred hp1] at hX
  rcases h with h | h | h | h | h
  · subst h
    exact (false_of_zmod_eq_zero (p := p) (k := 1) (by norm_num) (by omega)
      (by push_cast at hX ⊢; linear_combination -hX)).elim
  · rw [h, zmod_cast_sq_pred hp1] at hX
    exact (false_of_zmod_eq_zero (p := p) (k := 2) (by norm_num) (by omega)
      (by push_cast; linear_combination -hX)).elim
  · have h2 : ((2 * c : ℕ) : ZMod p) = -1 := by rw [h, zmod_cast_sq_pred hp1]
    push_cast at h2
    exact (false_of_zmod_eq_zero (p := p) (k := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination h2 - 2 * hX)).elim
  · have h2 : ((2 * (p - 1) : ℕ) : ZMod p) = -2 := by
      push_cast [Nat.cast_sub hp1]
      rw [ZMod.natCast_self]
      ring
    rw [h, h2] at hX
    exact (false_of_zmod_eq_zero (p := p) (k := 3) (by norm_num) (by omega)
      (by push_cast; linear_combination -hX)).elim
  · rw [h]
    have h4 : 4 ≤ p - 1 := by omega
    nlinarith

variable {G : Type} [Group G] [Finite G]

section ZCore

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem D1SmallZCore.eq_one_of_mul_mem_fusionSet (hc : D1SmallZCore p P M H R Rbar K z)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hzbC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hTC : d1LiftX p H R K ≤
      rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))))
    {t : G} (ht : t ∈ d1LiftX p H R K) (hzt : z * t ∈ fusionSet R z) : t = 1 := by
  have hRM := hc.phase.le_M
  have htR : t ∈ R := d1LiftX_le p H R K ht
  have hztR : z * t ∈ R := R.mul_mem hc.elt.1 htR
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨-, n, hn, hztn⟩ := hzt
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hztn
  have hnM : n ∈ M := hc.phase.normalizer_le hn
  set Lb := barM M L
  set L' := Lb.map (MulAut.conj (mkM ⟨n, hnM⟩)).toMonoidHom
  have hL' : IsComponentOf L' ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (mkM ⟨n, hnM⟩)) Lb).mpr
      hL.component
  have hmem : mkM ⟨z * t, hRM hztR⟩ ∈ L' := by
    refine ⟨mkM ⟨z, hc.mem_M⟩ ^ k, Lb.zpow_mem hzbL k, ?_⟩
    have he : (⟨z * t, hRM hztR⟩ : ↥M) = ⟨n, hnM⟩ * ⟨z, hc.mem_M⟩ ^ k * ⟨n, hnM⟩⁻¹ :=
      Subtype.ext (by simp [← hk, conj_zpow])
    rw [he]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, map_zpow,
      conj_zpow]
  by_cases hne : L' = Lb
  · have h1 : z * t ∈ rPart M R Lb := (mem_rPart hRM hztR).mpr (hne ▸ hmem)
    have h2 : t ∈ Subgroup.zpowers z := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers z)) (hBL h1)
      simpa using this
    by_contra ht1
    exact hc.card_d1LiftX.2 ((Subgroup.zpowers_le.mpr ht)
      (mem_zpowers_of_mem_zpowers_of_prime hc.prime hc.elt.2.1 h2 ht1))
  · exfalso
    have h1 := le_centralizer_of_component_ne hL' hL.component hne hmem
    have h2 := (mem_rPart hRM htR).mp (hTC ht)
    apply hzbC
    have he : mkM ⟨z, hc.mem_M⟩ = mkM ⟨z * t, hRM hztR⟩ * (mkM ⟨t, hRM htR⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rw [he]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

theorem D1SmallZCore.false_of_d1LiftX_le_C (hc : D1SmallZCore p P M H R Rbar K z)
    (hOrb : KFactSmallOrbits) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hzbC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hTC : d1LiftX p H R K ≤
      rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) : False := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTcard, hzT⟩ := hc.card_d1LiftX
  set T := d1LiftX p H R K
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer hr)
  have hz1 : z ≠ 1 := fun h => by
    have h' := hc.elt.2.1
    rw [h, orderOf_one] at h'
    exact hp.one_lt.ne h'
  have hO : ∀ t ∈ T, z * t ∈ fusionSet R z → t = 1 := fun t ht h =>
    hc.eq_one_of_mul_mem_fusionSet hL hBL hzbL hzbC hTC ht h
  obtain ⟨x, hxP, hxN, hxR, hxz⟩ := hc.data.exists_moving_elt hc.elt hc.b0
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hpdvd : p ∣ (fusionSet R z).ncard := p_dvd_ncard_fusionSet hc.elt.2.1 hxN hxk hxR
    (fun y hy hyz hyk => hc.data.mem_of_mem_normalizer_of_commute hc.b0 hy hyz hyk)
  have hcount := ncard_fusionSet_eq hp hTR hc.elt.1 hzT hc.elt.2.1 hRz hc.exp hc.dec
  have hO' : {t | t ∈ T ∧ z * t ∈ fusionSet R z} = {1} := by
    ext t
    constructor
    · rintro ⟨ht, hzt⟩
      exact hO t ht hzt
    · rintro rfl
      exact ⟨T.one_mem, by rw [mul_one]; exact self_mem_fusionSet hz1⟩
  rw [hO', Set.ncard_singleton, mul_one] at hcount
  have hinv : D1InvSubset p H R K z (fusionSet R z ∩ (T : Set G)) :=
    ⟨fun w hw => ⟨hw.2, hw.1.1⟩, fun n hn _ hnT w hw => ⟨conj_mem_fusionSet hn hw.1, hnT w hw.2⟩⟩
  have hY := two_mul_lt_of_dvd hc.five_le (hc.sizes_of_invSubset hOrb hinv) (hcount ▸ hpdvd)
  exact false_of_plane_lemma hp hTR hc.elt.1 hzT hc.elt.2.1 hTcard hRz hc.exp hc.dec hxN hxz hO hY

end ZCore

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem false_of_d1LiftX_le (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hB : D1AltBlockInputs) (hOrb : KFactSmallOrbits) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hTC : d1LiftX p H R K ≤
      rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) : False :=
  hc.toZCore.false_of_d1LiftX_le_C hOrb hL hBL (hc.zbar_mem_block hB hL)
    (hc.zbar_not_mem_centralizer hL) hTC

end D1SmallAltConfig

end CFSG.AGLEmbedding
