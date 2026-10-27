module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeLattice
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbCubeConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem le_d1LiftX_of_not_mem (hc : D1IbCubeConfig p P M H R Rbar K z)
    (hShape : KFactSmallSylowShape) (hOrb3 : KFactSmallOrbitsCube) {B : Subgroup G}
    (hBR : B ≤ R) (hB : IsInvR p H R K z B) (hzB : z ∉ B) : B ≤ d1LiftX p H R K := by
  have hp := hc.prime
  intro b hb
  obtain ⟨t, ht, i, hbt⟩ := hc.dec b (hBR hb)
  have hzi : z ^ i = 1 := by
    by_contra hzi
    apply hzB
    have hziB : z ^ i ∈ B := by
      rcases hc.lattice hShape hOrb3 hBR hB with hTB | ⟨hall, h0, h1⟩
      · have := B.mul_mem (B.inv_mem (hTB ht)) hb
        rwa [hbt, inv_mul_cancel_left] at this
      · obtain ⟨c, hcZ, i', hbc⟩ := hall b hb
        by_cases hD : B ⊓ d1LiftX p H R K = ⊥
        · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h0 hD hb)
          have ht' : t = z ^ k * (z ^ i)⁻¹ := by rw [hk, hbt]; group
          have htz : t ∈ Subgroup.zpowers z := by
            rw [ht']
            exact Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers z k)
              (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers z i))
          have ht1 : t = 1 := by
            by_contra ht1
            exact hc.card_d1LiftX.2 ((Subgroup.zpowers_le.mpr ht)
              (mem_zpowers_of_mem_zpowers_of_prime hp hc.elt.2.1 htz ht1))
          rw [hbt, ht1, one_mul] at hb
          exact hb
        · have hcB : c ∈ B := h1 hD hcZ
          have : z ^ i' ∈ B := by
            have := B.mul_mem (B.inv_mem hcB) hb
            rwa [hbc, inv_mul_cancel_left] at this
          have hzz : z ^ i * (z ^ i')⁻¹ ∈ d1LiftX p H R K := by
            have h2 : z ^ i * (z ^ i')⁻¹ = t⁻¹ * c := by
              have h3 : t * z ^ i = c * z ^ i' := hbt.symm.trans hbc
              calc z ^ i * (z ^ i')⁻¹ = t⁻¹ * (t * z ^ i) * (z ^ i')⁻¹ := by group
                _ = t⁻¹ * (c * z ^ i') * (z ^ i')⁻¹ := by rw [h3]
                _ = t⁻¹ * c := by group
            rw [h2]
            exact (d1LiftX p H R K).mul_mem ((d1LiftX p H R K).inv_mem ht) hcZ.1
          have hzz1 : z ^ i * (z ^ i')⁻¹ = 1 := by
            by_contra h1'
            exact hc.card_d1LiftX.2 ((Subgroup.zpowers_le.mpr hzz)
              (mem_zpowers_of_mem_zpowers_of_prime hp hc.elt.2.1
                (Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers z i)
                  (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers z i'))) h1'))
          rw [mul_inv_eq_one] at hzz1
          rwa [hzz1]
    exact (Subgroup.zpowers_le.mpr hziB)
      (mem_zpowers_of_mem_zpowers_of_prime hp hc.elt.2.1 (Subgroup.npow_mem_zpowers z i) hzi)
  rw [hbt, hzi, mul_one]
  exact ht

theorem isInvR_block (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IsInvR p H R K z (rPart M R (barM M L)) :=
  hc.rPart_inv hL le_rfl

theorem isInvR_cent (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    IsInvR p H R K z
      (rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) :=
  hc.rPart_inv hL (normalizer_le_normalizer_centralizer _)

theorem not_mem_cent (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    z ∉ rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
  fun h => hc.zbar_not_mem_centralizer hL ((mem_rPart hc.phase.le_M hc.elt.1).mp h)

theorem mem_rPart_block (hc : D1IbCubeConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
    (hShape : KFactSmallSylowShape) (hOrb3 : KFactSmallOrbitsCube) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : z ∈ rPart M R (barM M L) := by
  have hRM := hc.phase.le_M
  set T := d1LiftX p H R K
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set zb := mkM ⟨z, hc.mem_M⟩ with hzb
  set Lb := barM M L
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  obtain ⟨l, hlL, -, ⟨k, hk⟩, hlz, hlc⟩ := hc.exists_block_part hB hL
  obtain ⟨g, rfl, a, haM, haz, hga⟩ := hc.exists_conj_rPart hL hlL hlz hk
  set t := a⁻¹ * (g : G) * a with ht
  have htR : t ∈ R := hga.1
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
  by_contra hzL
  have hLT := hc.le_d1LiftX_of_not_mem hShape hOrb3 inf_le_left (hc.isInvR_block hL) hzL
  have hCT := hc.le_d1LiftX_of_not_mem hShape hOrb3 inf_le_left (hc.isInvR_cent hL)
    (hc.not_mem_cent hL)
  have h1 : t * (t⁻¹ * z) ∈ T := T.mul_mem (hLT hga) (hCT htz)
  rw [mul_inv_cancel_left] at h1
  exact hc.card_d1LiftX.2 h1

theorem barM_elem (hc : D1IbCubeConfig p P M H R Rbar K z) {E : Subgroup G} (hER : E ≤ R)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (barM M E) ∧ Nat.card (barM M E) = Nat.card E := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hEM : E ≤ M := hER.trans hc.phase.le_M
  have hEp : IsPGroup p (E.subgroupOf M) :=
    (hc.phase.isPGroup.to_le hER).comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp (CFSG.pCore 2 ↥M)
    (by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact fun h => hc.data.cfg.red.ne_two
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
    _ hEp
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨s, hs, rfl⟩⟩ := a
    obtain ⟨_, ⟨t, ht, rfl⟩⟩ := b
    change mkM s * mkM t = mkM t * mkM s
    rw [← map_mul, ← map_mul]
    have := hE.1.is_comm.comm ⟨s, Subgroup.mem_subgroupOf.mp hs⟩ ⟨t, Subgroup.mem_subgroupOf.mp ht⟩
    have h' : (s : G) * t = t * s := congrArg (fun x : ↥E => (x : G)) this
    exact congrArg mkM (Subtype.ext h')
  · rintro _ ⟨r, hr, rfl⟩
    have : r ^ p = 1 := Subtype.ext (by simpa using hE.2 r (Subgroup.mem_subgroupOf.mp hr))
    rw [← map_pow, this, map_one]
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,
      MonoidHom.subgroupMap_surjective _ _⟩)).symm

end D1IbCubeConfig

end CFSG.AGLEmbedding
