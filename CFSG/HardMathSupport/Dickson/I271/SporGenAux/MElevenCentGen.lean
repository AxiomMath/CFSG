module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ElevenGenerate
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.CentGenPair
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
public import Certificates.Certificate17420

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.AxisCount CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

private theorem gw_eq_of_agreeC_x5
    {w₁ w₂ : List Native.Gen}
    (h : agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂ = true) : gw w₁ = gw w₂ :=
  agree_sound (by rwa [agreeC_eq] at h)

theorem x5_y_fact :
    gw gen11W4 * gw gen11W1 = gw gen11W1 ^ 3 * gw gen11W4 := by
  have h : elevenX5yCheck () = true := Certificates.certificate17420
  unfold elevenX5yCheck at h
  have := gw_eq_of_agreeC_x5 h
  simp only [gw_append, gw_powL'] at this
  exact this

theorem centGen_Gmat_eleven
    (hG : (Nat.card Gmat).factorization 11 = 2)
    (hGen : Subgroup.closure (Set.range fun i : Fin gen11Gens.size => gw gen11Gens[i]) = ⊤) :
    CentGen 11 Gmat := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hfin : Finite Gmat := Nat.finite_of_card_ne_zero (by
    intro h; rw [h] at hG; simp at hG)
  obtain ⟨hx, hy, hxy, hx1, hA, hB, hC, hT⟩ := eleven_gw_facts
  have hy3 := eleven_data_facts.1
  have hrot := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.eleven_rot_fact
    Certificates.certificate41508
  have hy5 := x5_y_fact
  have hc : Commute (gw gen11W0) (gw gen11W1) := hxy
  have h3x : gw gen11W2 * gw gen11W0 * (gw gen11W2)⁻¹ = gw gen11W0 ^ 6 * gw gen11W1 ^ 3 := by
    rw [hA, mul_inv_cancel_right, ((hc.pow_pow 6 3).symm).eq]
  have h3y : gw gen11W2 * gw gen11W1 * (gw gen11W2)⁻¹ = gw gen11W0 ^ 4 * gw gen11W1 ^ 4 := by
    rw [hy3, mul_inv_cancel_right]
  have h4x : gw gen11W3 * gw gen11W0 * (gw gen11W3)⁻¹ = gw gen11W1 ^ 4 := by
    rw [hB, mul_inv_cancel_right]
  have h4y : gw gen11W3 * gw gen11W1 * (gw gen11W3)⁻¹ = gw gen11W0 ^ 8 := by
    rw [hrot, mul_inv_cancel_right]
  have h5x : gw gen11W4 * gw gen11W0 * (gw gen11W4)⁻¹ = gw gen11W0 ^ 3 := by
    rw [hC, mul_inv_cancel_right]
  have h5y : gw gen11W4 * gw gen11W1 * (gw gen11W4)⁻¹ = gw gen11W1 ^ 3 := by
    rw [hy5, mul_inv_cancel_right]
  have htx : gw thirteenT0 * gw gen11W0 = gw gen11W0 * gw thirteenT0 := hT
  have hsz : gen11Gens.size = 6 := rfl
  have hset : Set.range (fun i : Fin gen11Gens.size => gw gen11Gens[i]) =
      ({gw gen11W0, gw gen11W1, gw gen11W2, gw gen11W3, gw gen11W4, gw thirteenT0} :
        Set Gmat) := by
    ext z
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      rw [hsz] at hi
      interval_cases i <;> simp [gen11Gens]
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨⟨0, by rw [hsz]; norm_num⟩, rfl⟩
      · exact ⟨⟨1, by rw [hsz]; norm_num⟩, rfl⟩
      · exact ⟨⟨2, by rw [hsz]; norm_num⟩, rfl⟩
      · exact ⟨⟨3, by rw [hsz]; norm_num⟩, rfl⟩
      · exact ⟨⟨4, by rw [hsz]; norm_num⟩, rfl⟩
      · exact ⟨⟨5, by rw [hsz]; norm_num⟩, rfl⟩
  rw [hset] at hGen
  have hcent := closure_centralizers_eq_top hx hy hxy h3x h3y h4x h4y h5x h5y hx1 htx hGen
  have hyx := y_ne_pow_x hx h4x h4y hx1
  have hPcard := card_epsSubgroup hx hy hxy hx1 hyx hG
  exact centGen_of_sylow (by norm_num) hG hPcard hcent

end CFSG.HardMathSupport.Dickson.I271
