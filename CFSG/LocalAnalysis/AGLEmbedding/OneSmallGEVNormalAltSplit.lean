module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltInv
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltComp
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltLambda

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def rPart (M R : Subgroup G) (X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup G :=
  R ⊓ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

omit [Finite G] in
theorem mem_rPart {M R : Subgroup G} (hRM : R ≤ M) {X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    {r : G} (hr : r ∈ R) :
    r ∈ rPart M R X ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hRM hr⟩ ∈ X := by
  constructor
  · rintro ⟨-, m, hm, rfl⟩
    exact hm
  · exact fun h => ⟨hr, ⟨r, hRM hr⟩, h, rfl⟩

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem mem_normalizer_of_commute (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hB : D1AltBlockInputs) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hy : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) :
    y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  refine mem_normalizer_of_conj_not_mem_centralizer hL.component (hc.zbar_mem_block hB hL) ?_
  rw [hy, mul_inv_cancel_right]
  exact hc.zbar_not_mem_centralizer hL

theorem rPart_inv (hc : D1SmallAltConfig p P M H R Rbar K z) (hB : D1AltBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hX : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (X : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) →
        ∀ b ∈ rPart M R X, n * b * n⁻¹ ∈ rPart M R X := by
  intro n hn hnz _ b hb
  have hRM := hc.phase.le_M
  have hnM : n ∈ M := hc.phase.normalizer_le hn
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hnz' : mkM ⟨n, hnM⟩ * mkM ⟨z, hc.mem_M⟩ = mkM ⟨z, hc.mem_M⟩ * mkM ⟨n, hnM⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using (mul_inv_eq_iff_eq_mul.mp hnz))
  have hnN := hX (hc.mem_normalizer_of_commute hB hL hnz')
  have hbR : b ∈ R := hb.1
  have hnbR : n * b * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn b).mp hbR
  rw [mem_rPart hRM hbR] at hb
  rw [mem_rPart hRM hnbR]
  have h1 : (⟨n * b * n⁻¹, hRM hnbR⟩ : ↥M) = ⟨n, hnM⟩ * ⟨b, hRM hbR⟩ * ⟨n, hnM⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp hnN _).mp hb

theorem split (hc : D1SmallAltConfig p P M H R Rbar K z) (hB : D1AltBlockInputs)
    (hOrb : KFactSmallOrbits) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    R ≤ rPart M R (barM M L) ∨ (rPart M R (barM M L) ≤ Subgroup.zpowers z ∧
      (d1LiftX p H R K ≤
          rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∨
        rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥)) := by
  have hRM := hc.phase.le_M
  have hzL : z ∈ rPart M R (barM M L) := (mem_rPart hRM hc.elt.1).mpr (hc.zbar_mem_block hB hL)
  have hzC : z ∉ rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
    fun h => hc.zbar_not_mem_centralizer hL ((mem_rPart hRM hc.elt.1).mp h)
  obtain ⟨h1, h2⟩ := hc.inv_subgroup hOrb inf_le_left (hc.rPart_inv hB hL le_rfl)
  obtain ⟨h3, h4⟩ := hc.inv_subgroup hOrb inf_le_left
    (hc.rPart_inv hB hL (normalizer_le_normalizer_centralizer _))
  rcases h1 with h1 | h1
  · left
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hc.dec r hr
    exact Subgroup.mul_mem _ (h1 ht) (Subgroup.pow_mem _ hzL i)
  · right
    refine ⟨(h2 h1).1, ?_⟩
    rcases h3 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr ((h4 h3).2 hzC)

end D1SmallAltConfig

end CFSG.AGLEmbedding
