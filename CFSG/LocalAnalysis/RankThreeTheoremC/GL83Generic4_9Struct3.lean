module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen49_rank3 (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {R : Subgroup G} (hRP : R ≤ (P : Subgroup G)) (hRe : IsElemAbelian p R)
    (hRc : Nat.card R = p ^ 2) (hxR : x ∈ R) :
    ∀ H : Subgroup G, IsTwoLocal H → R ≤ H → 3 ≤ CFSG.Open.pRank p H → H ≤ M := by
  intro H hH hRH hrk
  have _ := hxR
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core
  obtain ⟨E, hEH, hEe, hEc⟩ := pRank_attained p H (by omega)
  obtain ⟨P'', hEP''⟩ := (elementary_isPGroup p E hEe).exists_le_sylow
  obtain ⟨M'', hM'', hP''M'', -, -, -⟩ := exists_isCoreMaxLocal hG.setting hl.sigma P''
  have hHM'' : H ≤ M'' := le_of_three_le_pRank_inf hG.d1 hl.sigma hM'' hH
    (hrk.trans (le_pRank_of_elemAbelian_card (le_inf hEH (hEP''.trans hP''M'')) hEe hEc))
  have hNR : normalizer (R : Set G) ≤ M'' :=
    normalizer_le_of_le_of_two_le_pRank hG.setting hG.u0 hl.sigma hM''
      (elementary_isPGroup p R hRe) (hRH.trans hHM'')
      (le_pRank_of_elemAbelian_card le_rfl hRe hRc)
  obtain ⟨-, hPab⟩ := gen5_P_abelian hG hl
  have hPR : (P : Subgroup G) ≤ normalizer (R : Set G) := fun g hg =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      congrArg Subtype.val (hPab.is_comm.comm ⟨r, hRP hr⟩ ⟨g, hg⟩))
  obtain ⟨E₃, hE₃P, hE₃e, hE₃c⟩ := pRank_attained p (P : Subgroup G) (by omega)
  rw [hP3] at hE₃c
  have hM''M : M'' ≤ M := le_of_three_le_pRank_inf hG.d1 hl.sigma hl.core hM''.1.1
    (le_pRank_of_elemAbelian_card (le_inf (hE₃P.trans (hPR.trans hNR)) (hE₃P.trans hPM))
      hE₃e hE₃c)
  exact hHM''.trans hM''M

theorem gen49_proper (hG : Gen5Global G) :
    ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → normalizer (Y : Set G) ≠ ⊤ := by
  intro Y hY1 hY2 hN
  have hsimple : IsSimpleGroup G := hG.setting.simple
  have hnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hYtop : Y = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal Y).resolve_left hY1
  have hG2 : IsPGroup 2 G := by
    rw [hYtop] at hY2
    exact hY2.of_equiv Subgroup.topEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
  have hcen : Subgroup.center G = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center G)
      exact absurd (Subtype.ext (by simpa [h] using hz)) hz1
    · exact h
  obtain ⟨a, b, hab⟩ := hG.setting.nonab
  have ha : a ∈ Subgroup.center G := hcen ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ha b).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
