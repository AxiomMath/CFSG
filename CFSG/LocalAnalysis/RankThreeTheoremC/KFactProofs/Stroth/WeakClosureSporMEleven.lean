module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporResidue
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ElevenRotCheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ElevenFusion

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.AGLEmbedding.Norton.MON11_13

private theorem gw_powL_rot (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (by simpa using wordLin_powL k w)

theorem eleven_rot_fact
    (h : elevenRotCheck () = true) :
    gw gen11W3 * gw gen11W1 = gw gen11W0 ^ 8 * gw gen11W3 := by
  have h' : agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) (gen11W1 ++ gen11W3)
      (gen11W3 ++ powL 8 gen11W0) = true := h
  have := agree_sound (by rwa [agreeC_eq] at h')
  simp only [gw_append, gw_powL_rot] at this
  exact this

theorem rotationDatum_Gmat_eleven
    (h : elevenRotCheck () = true) : RotationDatum 11 Gmat := by
  obtain ⟨hx, -, hxy, hx1, -, hB, -, -⟩ := eleven_gw_facts
  have hN := eleven_rot_fact h
  have h1 : gw gen11W3 * gw gen11W1 * (gw gen11W3)⁻¹ = gw gen11W0 ^ 8 := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hN
  refine ⟨gw gen11W0, gw gen11W1 ^ 4, gw gen11W3, hx1, hx,
    (Commute.pow_right (show Commute (gw gen11W0) (gw gen11W1) from hxy) 4).eq, ?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]
    exact hB
  · rw [← conj_pow, h1, ← pow_mul]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show 8 * 4 + 1 = 11 * 3 by norm_num, pow_mul, hx, one_pow]

theorem rotationDatum_of_mulEquiv {p : ℕ} {K L : Type} [Group K] [Group L] (e : K ≃* L)
    (h : RotationDatum p L) : RotationDatum p K := by
  obtain ⟨a, b, g, ha1, ha, hab, hga, hgb⟩ := h
  refine ⟨e.symm a, e.symm b, e.symm g, fun h1 => ha1 ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg e h1
  · rw [← map_pow, ha, map_one]
  · rw [← map_mul, ← map_mul, hab]
  · rw [← map_inv, ← map_mul, ← map_mul, hga]
  · rw [← map_inv, ← map_mul, ← map_mul, hgb, map_inv]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
