module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbSplit
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem exists_block_part (hc : D1IbConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ∃ l ∈ barM M L, l ≠ 1 ∧ (∃ k : ℕ, l ^ p ^ k = 1) ∧
      l * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * l ∧
      l⁻¹ * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set zb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ with hzb
  set Lb := barM M L
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have hzL := hc.zbar_mem_sup hB hL
  have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLC] at hzL
  obtain ⟨l, hl, c, hcC, hlc⟩ := hzL
  have hlx : l⁻¹ * zb ∈ C := by
    have : zb = l * c := hlc.symm
    rw [this]
    simpa using hcC
  obtain ⟨l', hl'L, -, hl'p, hl'c⟩ := exists_pow_mem_of_inv_mul_mem_centralizer hc.prime
    hc.zbar_pow hl hlx
  have hcomm : l' * zb = zb * l' := by
    have h1 := Subgroup.mem_centralizer_iff.mp hl'c l' hl'L
    calc l' * zb = l' * (l' * (l'⁻¹ * zb)) := by group
      _ = l' * ((l'⁻¹ * zb) * l') := by rw [h1]
      _ = zb * l' := by group
  refine ⟨l', hl'L, fun h1 => ?_, hl'p, hcomm, hl'c⟩
  apply hc.zbar_not_mem_centralizer hL
  rw [h1, inv_one, one_mul] at hl'c
  exact hl'c

theorem false_of_rPart_block_eq_bot (hc : D1IbConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) = ⊥) : False := by
  obtain ⟨l, hlL, hl1, ⟨k, hk⟩, hlz, -⟩ := hc.exists_block_part hB hL
  obtain ⟨g, rfl, a, haM, -, hga⟩ := hc.exists_conj_rPart hL hlL hlz hk
  rw [hBL, Subgroup.mem_bot] at hga
  have hg : (g : G) = 1 := by
    calc (g : G) = a * (a⁻¹ * g * a) * a⁻¹ := by group
      _ = 1 := by rw [hga]; group
  apply hl1
  rw [show g = 1 from Subtype.ext hg, map_one]

theorem false_of_d1LiftX_le_of_not_mem (hc : D1IbConfig p P M H R Rbar K z)
    (hB : D1IbBlockInputs) (hOrb : KFactSmallOrbits) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hTL : d1LiftX p H R K ≤ rPart M R (barM M L))
    (hzL : z ∉ rPart M R (barM M L)) : False := by
  have hp := hc.prime
  have hRM := hc.phase.le_M
  set T := d1LiftX p H R K
  have hTR : T ≤ R := d1LiftX_le p H R K
  obtain ⟨-, hzT⟩ := hc.card_d1LiftX
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set zb := mkM ⟨z, hc.mem_M⟩ with hzb
  set Lb := barM M L
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have hRL : ∀ b ∈ rPart M R Lb, b ∈ T := by
    intro b hb
    obtain ⟨t, ht, i, rfl⟩ := hc.dec b hb.1
    have hzi : z ^ i ∈ rPart M R Lb := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTL ht)) hb
      simpa using this
    by_cases hzi1 : z ^ i = 1
    · rw [hzi1, mul_one]
      exact ht
    · exact absurd ((Subgroup.zpowers_le.mpr hzi) (mem_zpowers_of_mem_zpowers_of_prime hp
        hc.elt.2.1 (Subgroup.npow_mem_zpowers z i) hzi1)) hzL
  obtain ⟨l, hlL, hl1, ⟨k, hk⟩, hlz, hlc⟩ := hc.exists_block_part hB hL
  obtain ⟨g, rfl, a, haM, haz, hga⟩ := hc.exists_conj_rPart hL hlL hlz hk
  set t := a⁻¹ * (g : G) * a with ht
  have htT : t ∈ T := hRL t hga
  have htR : t ∈ R := hTR htT
  have haN : mkM ⟨a, haM⟩ ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine hc.mem_normalizer_of_commute hL ?_
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext haz)
  have haC : mkM ⟨a, haM⟩ ∈ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    normalizer_le_normalizer_centralizer _ haN
  have htz : t⁻¹ * z ∈ rPart M R C := by
    refine (mem_rPart hRM (R.mul_mem (R.inv_mem htR) hc.elt.1)).mpr ?_
    have he : (⟨t⁻¹ * z, hRM (R.mul_mem (R.inv_mem htR) hc.elt.1)⟩ : ↥M) =
        (⟨a, haM⟩ : ↥M)⁻¹ * (g⁻¹ * ⟨z, hc.mem_M⟩) * ⟨a, haM⟩ := by
      apply Subtype.ext
      simp only [ht, Subgroup.coe_mul, Subgroup.coe_inv]
      have hza : a⁻¹ * z * a = z := by
        calc a⁻¹ * z * a = a⁻¹ * (z * a) := by group
          _ = a⁻¹ * (a * z) := by rw [haz]
          _ = z := by group
      calc (a⁻¹ * ↑g * a)⁻¹ * z = a⁻¹ * (↑g)⁻¹ * a * (a⁻¹ * z * a) := by
            rw [hza]; group
        _ = a⁻¹ * ((↑g)⁻¹ * z) * a := by group
    rw [he, map_mul, map_mul, map_inv, map_mul, map_inv]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haC) ((mkM g)⁻¹ * zb)).mp hlc
    rw [inv_inv] at this
    exact this
  have hBC := (hc.inv_subgroup hOrb inf_le_left
    (hc.rPart_inv hL (normalizer_le_normalizer_centralizer _))).1
  rcases hBC with hTC | hTC
  · apply hc.zbar_not_mem_centralizer hL
    have hz : z ∈ rPart M R C := by
      have h := Subgroup.mul_mem _ (hTC htT) htz
      rwa [mul_inv_cancel_left] at h
    exact (mem_rPart hRM hc.elt.1).mp hz
  · have hz := ((hc.inv_subgroup hOrb inf_le_left
      (hc.rPart_inv hL (normalizer_le_normalizer_centralizer _))).2 hTC).1 htz
    have htz' : t ∈ Subgroup.zpowers z := by
      have := Subgroup.mul_mem _ (Subgroup.mem_zpowers z) (Subgroup.inv_mem _ hz)
      simpa using this
    have ht1 : t = 1 := by
      by_contra h1
      exact hzT ((Subgroup.zpowers_le.mpr htT)
        (mem_zpowers_of_mem_zpowers_of_prime hp hc.elt.2.1 htz' h1))
    have hg1 : (g : G) = 1 := by
      calc (g : G) = a * t * a⁻¹ := by rw [ht]; group
        _ = 1 := by rw [ht1]; group
    apply hl1
    rw [show g = 1 from Subtype.ext hg1, map_one]

end D1IbConfig

end CFSG.AGLEmbedding
