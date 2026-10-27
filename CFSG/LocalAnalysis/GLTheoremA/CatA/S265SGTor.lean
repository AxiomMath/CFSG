module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF0
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SG

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10

theorem false_of_torusLift {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 3 S B T x D K) {e : ℕ} (hB : Nat.card B = 3 ^ e)
    {lab : GLALabel} (hlab : LabelOf S lab) {r : ℕ} (hr : e ≤ r)
    (hT : CFSG.StandardType.LargeEvenLabelAll lab fun R _ _ _ =>
      CFSG.StandardType.GGTorusLift 3 r R) : False := by
  have hc := h.cfg
  haveI : Fact (Nat.Prime 3) := ⟨hc.prime⟩
  obtain ⟨hcomm, lab', -, hraw⟩ := hlab
  obtain ⟨-, -, -, -, -, -, -, hl⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  subst hl
  obtain ⟨R, _, _, _, ⟨-, -, θ, -⟩, hlift⟩ := CFSG.StandardType.largeEvenRawDatum_exists
    (hT _ ((CFSG.StandardType.largeEvenRawDatum_legacy _ _).2
      (Y10GInnLin.largeEvenRawDatumLegacy_of_canonical_carrier hraw)))
  have hxc : x ∈ Subgroup.center Ω := Subgroup.mem_center_iff.2 hc.xcen
  have h1 := SF.pow_mul_card_le_of_torusLift hc.prime hcomm θ hlift
    (hc.elem.mono (Subgroup.zpowers_le.2 hc.xB))
    ((Subgroup.zpowers_le.2 hxc).trans (Subgroup.center_le_centralizer _))
  rw [Nat.card_zpowers, orderOf_eq_prime (hc.elem.2 x hc.xB) hc.x1] at h1
  have h2 := hc.rank
  rw [hB] at h2
  have h3 : 3 ^ e ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  have h4 : 0 < 3 ^ r := by positivity
  omega

end CFSG.LocalAnalysis.GLTheoremA.S265.SG

end
