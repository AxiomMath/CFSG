module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVOuterSup

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1IbCubeConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem rPart_inv (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hX : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (X : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) →
        ∀ b ∈ rPart M R X, n * b * n⁻¹ ∈ rPart M R X :=
  rPart_inv_of hc.phase.le_M hc.phase.normalizer_le hc.mem_M
    (hc.mem_normalizer_of_commute hL) hX
theorem exists_conj_rPart (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hyL : y ∈ barM M L)
    (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    ∃ g : ↥M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) g = y ∧ ∃ a : G, a ∈ M ∧
      a * z = z * a ∧ a⁻¹ * (g : G) * a ∈ rPart M R (barM M L) :=
  exists_conj_rPart_of hc.prime hc.phase.le_M hc.mem_M hc.elt.2.1 hc.coprime_twoCore
    hc.le_centralizer hc.b0 hc.phase.isPGroup (hc.mem_normalizer_of_commute hL) hyL hyz hy
theorem exists_block_part (hc : D1IbCubeConfig p P M H R Rbar K z) (hB : D1IbBlockInputs)
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

theorem mem_zpowers_of_mem_block (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hyL : y ∈ barM M L)
    (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    y ∈ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩) :=
  mem_zpowers_of_mem_block_of hc.prime hc.phase.le_M hc.mem_M hc.elt.2.1 hc.coprime_twoCore
    hc.le_centralizer hc.b0 hc.phase.isPGroup (hc.mem_normalizer_of_commute hL) hBL hyL hyz hy
theorem eq_one_of_mem_sup (hc : D1IbCubeConfig p P M H R Rbar K z) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ ∈ barM M L)
    (hBC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥)
    {t : G} (ht : t ∈ d1LiftX p H R K) (hRt : t ∈ M)
    (htL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, hRt⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : t = 1 :=
  eq_one_of_mem_sup_of_block hc.prime hc.phase.le_M hc.elt.1 hc.elt.2.1 hc.mem_M hc.le_centralizer
    hc.exp hc.card_d1LiftX.2 (fun hyL hyz _ hy => hc.mem_zpowers_of_mem_block hL hBL hyL hyz hy)
    hzbL hBC ht hRt htL
end D1IbCubeConfig

end CFSG.AGLEmbedding
