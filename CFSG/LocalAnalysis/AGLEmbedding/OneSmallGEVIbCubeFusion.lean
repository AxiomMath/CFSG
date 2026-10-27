module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeToral
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbCubeConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem central_decomp (hc : D1IbCubeConfig p P M H R Rbar K z) {w : G} (hw : w ∈ R)
    (hwc : ∀ r ∈ R, w * r = r * w) :
    ∃ c ∈ centerOf (d1LiftX p H R K), ∃ i : ℕ, w = c * z ^ i := by
  obtain ⟨t, ht, i, rfl⟩ := hc.dec w hw
  refine ⟨t, hc.mem_centerOf_of_comm ht fun r hr => ?_, i, rfl⟩
  have h1 := hwc r hr
  have hzr : z ^ i * r = r * z ^ i := (Commute.pow_left (hc.commute_z hr).symm i).eq
  calc t * r = t * z ^ i * r * (z ^ i)⁻¹ := by rw [mul_assoc t, hzr]; group
    _ = r * (t * z ^ i) * (z ^ i)⁻¹ := by rw [h1]
    _ = r * t := by group

theorem conj_central (hc : D1IbCubeConfig p P M H R Rbar K z) {x : G}
    (hx : x ∈ Subgroup.normalizer (R : Set G)) :
    ∀ r ∈ R, x * z * x⁻¹ * r = r * (x * z * x⁻¹) := by
  intro r hr
  have hr' : x⁻¹ * r * x ∈ R := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) r).mp hr
    simpa using this
  have h1 := hc.commute_z hr'
  calc x * z * x⁻¹ * r = x * (z * (x⁻¹ * r * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * r * x) * z) * x⁻¹ := by rw [h1]
    _ = r * (x * z * x⁻¹) := by group

theorem eq_one_of_mul_mem_fusionSet (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L) {t : G}
    (ht : t ∈ rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))))
    (hzt : z * t ∈ fusionSet R z) : t = 1 := by
  have hRM := hc.phase.le_M
  have htR : t ∈ R := ht.1
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
    exact hc.not_mem_cent hL ((Subgroup.zpowers_le.mpr ht)
      (mem_zpowers_of_mem_zpowers_of_prime hc.prime hc.elt.2.1 h2 ht1))
  · exfalso
    have h1 := le_centralizer_of_component_ne hL' hL.component hne hmem
    have h2 := (mem_rPart hRM htR).mp ht
    apply hc.zbar_not_mem_centralizer hL
    have he : mkM ⟨z, hc.mem_M⟩ = mkM ⟨z * t, hRM hztR⟩ * (mkM ⟨t, hRM htR⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rw [he]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

theorem false_of_fusion (hc : D1IbCubeConfig p P M H R Rbar K z) (hShape : KFactSmallSylowShape)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hZC : centerOf (d1LiftX p H R K) ≤
      rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) : False := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, -, hxN, -, hxz⟩ := hc.data.exists_moving_elt hc.elt hc.b0
  set w := x * z * x⁻¹ with hw
  have hwR : w ∈ R := (Subgroup.mem_normalizer_iff.mp hxN z).mp hc.elt.1
  obtain ⟨c, hcZ, i, hwc⟩ := hc.central_decomp hwR (hc.conj_central hxN)
  have hzi1 : z ^ i ≠ 1 := by
    intro h
    apply hc.conj_not_mem hShape hxN
    rw [← hw, hwc, h, mul_one]
    exact hcZ.1
  have hzzi : z ∈ Subgroup.zpowers (z ^ i) :=
    mem_zpowers_of_mem_zpowers_of_prime hp hc.elt.2.1 (Subgroup.npow_mem_zpowers z i) hzi1
  obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr hzzi)
  have hcz : Commute c (z ^ i) :=
    Commute.pow_right (hc.commute_z (d1LiftX_le p H R K hcZ.1)) i
  have hn' : (z ^ i) ^ n = z := hn
  have hwn : w ^ n = c ^ n * z := by rw [hwc, hcz.mul_pow, hn']
  have hcn : c ^ n ∈ centerOf (d1LiftX p H R K) := Subgroup.pow_mem _ hcZ n
  have hwn1 : w ^ n ≠ 1 := by
    intro h
    rw [hwn] at h
    have hz : z = (c ^ n)⁻¹ := eq_inv_of_mul_eq_one_right h
    exact hc.card_d1LiftX.2 (hz ▸ (d1LiftX p H R K).inv_mem hcn.1)
  have hwZ : w ∈ fusionSet R z := by
    refine ⟨fun h => ?_, x, hxN, Subgroup.mem_zpowers _⟩
    exact hxz (by rw [h]; exact Subgroup.one_mem _)
  have hfus : z * c ^ n ∈ fusionSet R z := by
    have h1 := pow_mem_fusionSet hwZ hwn1
    have hcz' : Commute (c ^ n) z :=
      Commute.pow_left (hc.commute_z (d1LiftX_le p H R K hcZ.1)) n
    rwa [hwn, hcz'.eq] at h1
  have hcn1 := hc.eq_one_of_mul_mem_fusionSet hL hBL hzbL (hZC hcn) hfus
  rw [hcn1, one_mul] at hwn
  apply hxz
  have hzw : z ∈ Subgroup.zpowers w := ⟨n, by simp [hwn]⟩
  have hwo : orderOf w = p := by
    have := orderOf_injective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective z
    rw [hw, ← hc.elt.2.1, ← this]
    rfl
  have hz1 : z ≠ 1 := fun h => by
    have h' := hc.elt.2.1
    rw [h, orderOf_one] at h'
    exact hp.one_lt.ne h'
  exact (Subgroup.zpowers_le.mpr (mem_zpowers_of_mem_zpowers_of_prime hp hwo hzw
    hz1)) (Subgroup.mem_zpowers w)

theorem exists_not_mem_centerOf (hc : D1IbCubeConfig p P M H R Rbar K z)
    (hShape : KFactSmallSylowShape) :
    ∃ t ∈ d1LiftX p H R K, t ∉ centerOf (d1LiftX p H R K) := by
  by_contra h
  push Not at h
  have h1 := Subgroup.card_le_of_le (show d1LiftX p H R K ≤ centerOf (d1LiftX p H R K) from h)
  rw [hc.card_d1LiftX.1, hc.card_Z hShape] at h1
  have hp := hc.prime
  have : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  rw [pow_one] at this
  omega

theorem false_of_cyc_bot (hc : D1IbCubeConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    (hShape : KFactSmallSylowShape) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hBC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥) :
    False := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set T := d1LiftX p H R K
  have hRM := hc.phase.le_M
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hnorm : ∀ r (hr : r ∈ R), mkM ⟨r, hRM hr⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro r hr
    refine hc.mem_normalizer_of_commute hL ?_
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext (hc.commute_z hr))
  have hpow : ∀ r (hr : r ∈ R), mkM ⟨r, hRM hr⟩ ^ p = 1 := by
    intro r hr
    have : (⟨r, hRM hr⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hc.exp r hr)
    rw [← map_pow, this, map_one]
  obtain ⟨t₀, ht₀T, ht₀Z⟩ := hc.exists_not_mem_centerOf hShape
  have ht₀1 : t₀ ≠ 1 := fun h => ht₀Z (h ▸ (centerOf T).one_mem)
  rcases blockType_ib hc.phase hB.h85 hB.h93 hB.hD2 hL with htype | ⟨hcl, hpar, hne, hnB⟩
  · exact ht₀1 (hc.eq_one_of_mem_sup hL hBL hzbL hBC ht₀T (hRM (hTR ht₀T))
      (hB.hOP _ (barM M L) hL.component p hp hc.five_le htype _ (hnorm t₀ (hTR ht₀T))
        (hpow t₀ (hTR ht₀T))))
  obtain ⟨hXT, hXel, hXcard⟩ := hc.elem_sup_zpowers hShape ht₀T ht₀Z
  set X := centerOf T ⊔ Subgroup.zpowers t₀
  obtain ⟨hEel, hEcard⟩ := hc.barM_elem (hXT.trans hTR) hXel
  set E := barM M X
  have hEN : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hnorm _ (hTR (hXT (Subgroup.mem_subgroupOf.mp ht)))
  have hE1 : E ⊓ (barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) =
      ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨⟨t, ht, rfl⟩, hxL⟩ := hx
    have h1 := hc.eq_one_of_mem_sup hL hBL hzbL hBC (hXT (Subgroup.mem_subgroupOf.mp ht)) t.2 hxL
    have : t = 1 := Subtype.ext h1
    rw [this, map_one]
  exact hB.hOR _ (barM M L) _ hL.component hcl hpar hne hnB p hp hc.five_le (hc.perf_block hL)
    E hEN hEel (hEcard.trans hXcard) hE1

end D1IbCubeConfig

end CFSG.AGLEmbedding
