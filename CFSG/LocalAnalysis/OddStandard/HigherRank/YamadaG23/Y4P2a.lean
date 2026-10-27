module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4JStr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Ctx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_card_centV_le (c : Ctx4 s e) {x : G}
    (hnot : ∃ v ∈ cen s.fr.B, x * v * x⁻¹ ≠ v) :
    Nat.card ↥(centEl (cen s.fr.B) x) ≤ 2 := by
  have hcardV : Nat.card ↥(cen s.fr.B) = 4 := y4_card_V c.toF33
  have hdvd4 : Nat.card ↥(centEl (cen s.fr.B) x) ∣ 4 := by
    rw [← hcardV]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hdvd : Nat.card ↥(centEl (cen s.fr.B) x) ∣ 2 ^ 2 := by
    rwa [show (2 : ℕ) ^ 2 = 4 by norm_num]
  obtain ⟨k, hk, hkval⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hne4 : Nat.card ↥(centEl (cen s.fr.B) x) ≠ 4 := by
    intro h4
    have heq : centEl (cen s.fr.B) x = cen s.fr.B :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardV, h4])
    obtain ⟨v, hv, hne⟩ := hnot
    have hvC : v ∈ centEl (cen s.fr.B) x := heq.symm ▸ hv
    have hvcent : v ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hvC).2
    have hcomm : x * v = v * x :=
      Subgroup.mem_centralizer_iff.mp hvcent x (Set.mem_singleton x)
    exact hne (by rw [hcomm]; group)
  have hklt : k < 2 := by
    by_contra h
    have hk2 : k = 2 := by omega
    rw [hkval, hk2] at hne4
    norm_num at hne4
  have hk01 : k = 0 ∨ k = 1 := by omega
  rw [hkval]
  rcases hk01 with rfl | rfl <;> norm_num

private theorem y4_card_centEl_thompson_le_four (c : Ctx4 s e) {x : G}
    (hnot : ∃ v ∈ cen s.fr.B, x * v * x⁻¹ ≠ v) :
    Nat.card ↥(centEl (thompsonSubgroup s.fr.B) x) ≤ 4 := by
  have hH := c.toF33
  let CJ : Subgroup G := centEl (thompsonSubgroup s.fr.B) x
  let CV : Subgroup G := centEl (cen s.fr.B) x
  have hCVmem : ∀ j : ↥CJ, (j : G) * (j : G) ∈ CV := by
    intro j
    have hjJ : (j : G) ∈ thompsonSubgroup s.fr.B := (Subgroup.mem_inf.mp j.2).1
    have hjC : (j : G) ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp j.2).2
    exact Subgroup.mem_inf.mpr ⟨y4_J_sq_mem_V hH (j : G) hjJ, mul_mem hjC hjC⟩
  let sq : ↥CJ →* ↥CV :=
    { toFun := fun j => ⟨(j : G) * (j : G), hCVmem j⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        show ((a : G) * (b : G)) * ((a : G) * (b : G)) =
          ((a : G) * (a : G)) * ((b : G) * (b : G))
        have ha : (a : G) ∈ thompsonSubgroup s.fr.B := (Subgroup.mem_inf.mp a.2).1
        have hb : (b : G) ∈ thompsonSubgroup s.fr.B := (Subgroup.mem_inf.mp b.2).1
        have hba : (b : G) * (a : G) = (a : G) * (b : G) := y4_J_comm hH (b : G) hb (a : G) ha
        calc ((a : G) * (b : G)) * ((a : G) * (b : G))
            = (a : G) * ((b : G) * (a : G)) * (b : G) := by group
          _ = (a : G) * ((a : G) * (b : G)) * (b : G) := by rw [hba]
          _ = ((a : G) * (a : G)) * ((b : G) * (b : G)) := by group }
  have hmem : ∀ j : ↥sq.ker, ((j : ↥CJ) : G) ∈ CV := by
    intro j
    have hj : ((j : ↥CJ) : G) * ((j : ↥CJ) : G) = 1 := by
      have h1 := j.2
      rw [MonoidHom.mem_ker] at h1
      dsimp only [sq] at h1
      simpa using congrArg (Subtype.val : ↥CV → G) h1
    have hjJ : ((j : ↥CJ) : G) ∈ thompsonSubgroup s.fr.B :=
      (Subgroup.mem_inf.mp (j : ↥CJ).2).1
    have hjC : ((j : ↥CJ) : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.mem_inf.mp (j : ↥CJ).2).2
    exact Subgroup.mem_inf.mpr ⟨y4_J_sq_one_mem_V hH ((j : ↥CJ) : G) hjJ hj, hjC⟩
  have hkermap : (sq.ker).map CJ.subtype = CV := by
    refine le_antisymm ?_ ?_
    · rintro g ⟨j, hj, rfl⟩
      simpa using hmem ⟨j, hj⟩
    · intro v hv
      refine Subgroup.mem_map.mpr ⟨⟨v, ?_⟩, ?_, rfl⟩
      · exact Subgroup.mem_inf.mpr ⟨y5_V_le_J hH hv.1, hv.2⟩
      · rw [MonoidHom.mem_ker]
        apply Subtype.ext
        dsimp only [sq]
        exact y4_V_mul_self hH v hv.1
  have hker_le : Nat.card ↥sq.ker ≤ Nat.card ↥CV := by
    rw [← Subgroup.card_subtype CJ sq.ker, hkermap]
  have hrange_le : Nat.card ↥sq.range ≤ Nat.card ↥CV :=
    Subgroup.card_le_card_group (H := sq.range)
  have hCVle : Nat.card ↥CV ≤ 2 := y4_card_centV_le c hnot
  calc Nat.card ↥CJ = Nat.card ↥sq.ker * Nat.card ↥sq.range :=
        (Subgroup.card_ker_mul_card_range sq).symm
    _ ≤ Nat.card ↥CV * Nat.card ↥CV := Nat.mul_le_mul hker_le hrange_le
    _ ≤ 2 * 2 := Nat.mul_le_mul hCVle hCVle
    _ = 4 := by norm_num

theorem y4_card_centB_le (c : Ctx4 s e) {x : G}
    (hnot : ∃ v ∈ cen s.fr.B, x * v * x⁻¹ ≠ v) : Nat.card ↥(centEl s.fr.B x) ≤ 8 := by
  have hH := c.toF33
  have hCJleC : centEl (thompsonSubgroup s.fr.B) x ≤ centEl s.fr.B x := by
    intro g hg
    exact Subgroup.mem_inf.mpr
      ⟨y5_J_le_B s (Subgroup.mem_inf.mp hg).1, (Subgroup.mem_inf.mp hg).2⟩
  have hCJeq : centEl (thompsonSubgroup s.fr.B) x =
      thompsonSubgroup s.fr.B ⊓ centEl s.fr.B x := by
    refine le_antisymm ?_ ?_
    · intro g hg
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1, hCJleC hg⟩
    · intro g hg
      obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.mp hg
      exact Subgroup.mem_inf.mpr ⟨hgJ, (Subgroup.mem_inf.mp hgC).2⟩
  have hrelJB : (thompsonSubgroup s.fr.B).relIndex s.fr.B = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
    refine ⟨s.fr.a₁ * s.fr.a₂, ⟨y5_a12_mem_B hH, y5_a12_not_mem_J hH, ?_⟩⟩
    intro b hb
    rcases y4_B_cases hH b hb with hbJ | ⟨j, hj, rfl⟩
    · exact Or.inr hbJ
    · left
      have hαinv : (s.fr.a₁ * s.fr.a₂)⁻¹ = s.fr.a₁ * s.fr.a₂ := by
        rw [inv_eq_iff_mul_eq_one]
        exact y4_alpha_sq hH
      have hmem : (s.fr.a₁ * s.fr.a₂) * (j * (s.fr.a₁ * s.fr.a₂)) = j⁻¹ := by
        calc (s.fr.a₁ * s.fr.a₂) * (j * (s.fr.a₁ * s.fr.a₂))
            = (s.fr.a₁ * s.fr.a₂) * j * (s.fr.a₁ * s.fr.a₂) := by group
          _ = (s.fr.a₁ * s.fr.a₂) * j * (s.fr.a₁ * s.fr.a₂)⁻¹ := by rw [hαinv]
          _ = j⁻¹ := y4_alpha_inv_J hH j hj
      rw [hmem]
      exact Subgroup.inv_mem _ hj
  have hrelJC : (thompsonSubgroup s.fr.B).relIndex (centEl s.fr.B x) ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := thompsonSubgroup s.fr.B)
      (K := centEl s.fr.B x) (L := s.fr.B) inf_le_left (by rw [hrelJB]; norm_num)
    exact le_trans h (le_of_eq hrelJB)
  have hrelCJ : (centEl (thompsonSubgroup s.fr.B) x).relIndex (centEl s.fr.B x) ≤ 2 := by
    rw [hCJeq, Subgroup.inf_relIndex_right]
    exact hrelJC
  have hcard : Nat.card ↥(centEl s.fr.B x) =
      (centEl (thompsonSubgroup s.fr.B) x).relIndex (centEl s.fr.B x) *
        Nat.card ↥(centEl (thompsonSubgroup s.fr.B) x) := by
    rw [← Subgroup.relIndex_mul_card (H := centEl (thompsonSubgroup s.fr.B) x)
      (K := centEl s.fr.B x), inf_eq_left.mpr hCJleC]
  calc Nat.card ↥(centEl s.fr.B x)
      = (centEl (thompsonSubgroup s.fr.B) x).relIndex (centEl s.fr.B x) *
          Nat.card ↥(centEl (thompsonSubgroup s.fr.B) x) := hcard
    _ ≤ 2 * 4 := Nat.mul_le_mul hrelCJ (y4_card_centEl_thompson_le_four c hnot)
    _ = 8 := by norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
