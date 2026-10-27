module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.Gen11.Gen
public import CFSG.RankThree.PartOne.CTP.FusionSound
public import Certificates.Certificate125502

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.RankThree.PartOne.CTP.Fus CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.Gen11

section Algebra

variable {G : Type*} [Group G]

theorem fusionGenerationOf_of_commuting_pair {p : ℕ} (hp : p.Prime) {n : ℕ} {gens : Fin n → G}
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hel : ∀ i, ∃ u ∈ Subgroup.closure ({x, y} : Set G), gens i * x = u * gens i) :
    FusionGenerationOf G p := by
  have hxE : x ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
  refine ⟨Subgroup.closure ({x, y} : Set G), Set.range gens, isPGroup_closure_pair hp hx hy hxy, ?_,
    hgen, ?_⟩
  · intro h
    exact hx1 (by simpa using (Subgroup.mem_bot.1 (h ▸ hxE)))
  · rintro _ ⟨i, rfl⟩
    obtain ⟨u, hu, h⟩ := hel i
    refine ⟨x, hxE, hx1, ?_⟩
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact hu

end Algebra

private theorem gw_powL (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (by simpa using wordLin_powL k w)

private theorem gw_eq_of_agreeC
    {w₁ w₂ : List Native.Gen}
    (h : agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂ = true) : gw w₁ = gw w₂ :=
  agree_sound (by rwa [agreeC_eq] at h)

theorem eleven_eligible_check : elevenEligibleCheck () = true :=
  Certificates.certificate125502

theorem eleven_gw_facts :
    gw gen11W0 ^ 11 = 1 ∧ gw gen11W1 ^ 11 = 1 ∧ gw gen11W0 * gw gen11W1 = gw gen11W1 * gw gen11W0 ∧
    gw gen11W0 ≠ 1 ∧
    gw gen11W2 * gw gen11W0 = gw gen11W1 ^ 3 * gw gen11W0 ^ 6 * gw gen11W2 ∧
    gw gen11W3 * gw gen11W0 = gw gen11W1 ^ 4 * gw gen11W3 ∧
    gw gen11W4 * gw gen11W0 = gw gen11W0 ^ 3 * gw gen11W4 ∧
    gw thirteenT0 * gw gen11W0 = gw gen11W0 * gw thirteenT0 := by
  have h := eleven_eligible_check
  simp only [elevenEligibleCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hx : gw gen11W0 ^ 11 = 1 := by
    have := gw_eq_of_agreeC h1
    rwa [gw_powL, gw_nil] at this
  have hy : gw gen11W1 ^ 11 = 1 := by
    have := gw_eq_of_agreeC h2
    rwa [gw_powL, gw_nil] at this
  have hxy : gw gen11W0 * gw gen11W1 = gw gen11W1 * gw gen11W0 := by
    have := gw_eq_of_agreeC h3
    simp only [gw_append] at this
    exact this.symm
  have hx1 : gw gen11W0 ≠ 1 := by
    rcases Bool.or_eq_true_iff.1 h8 with h8 | h8
    · rcases Bool.or_eq_true_iff.1 h8 with h8 | h8
      · exact gw_ne_one_of_moveCheck h8
      · exact gw_ne_one_of_moveCheck h8
    · exact gw_ne_one_of_moveCheck h8
  refine ⟨hx, hy, hxy, hx1, ?_, ?_, ?_, ?_⟩
  · have := gw_eq_of_agreeC h4
    simp only [gw_append, gw_powL] at this
    rw [mul_assoc]
    exact this
  · have := gw_eq_of_agreeC h5
    simp only [gw_append, gw_powL] at this
    exact this
  · have := gw_eq_of_agreeC h6
    simp only [gw_append, gw_powL] at this
    exact this
  · have := gw_eq_of_agreeC h7
    simp only [gw_append] at this
    exact this

theorem fusionGenerationOf_gmat_eleven :
    FusionGenerationOf Gmat 11 := by
  obtain ⟨hx, hy, hxy, hx1, hA, hB, hC, hT⟩ := eleven_gw_facts
  have hgen : Subgroup.closure (Set.range fun i : Fin gen11Gens.size => gw gen11Gens[i]) = ⊤ :=
    closure_gen11_eq_top
  have hsz : gen11Gens.size = 6 := rfl
  have hxE : gw gen11W0 ∈ Subgroup.closure ({gw gen11W0, gw gen11W1} : Set Gmat) :=
    Subgroup.subset_closure (by simp)
  have hyE : gw gen11W1 ∈ Subgroup.closure ({gw gen11W0, gw gen11W1} : Set Gmat) :=
    Subgroup.subset_closure (by simp)
  refine fusionGenerationOf_of_commuting_pair (by norm_num : Nat.Prime 11) hx hy hxy hx1 hgen ?_
  rintro ⟨i, hi⟩
  rw [hsz] at hi
  interval_cases i
  · exact ⟨gw gen11W0, hxE, rfl⟩
  · exact ⟨gw gen11W0, hxE, hxy.symm⟩
  · exact ⟨gw gen11W1 ^ 3 * gw gen11W0 ^ 6, mul_mem (pow_mem hyE _) (pow_mem hxE _), hA⟩
  · exact ⟨gw gen11W1 ^ 4, pow_mem hyE _, hB⟩
  · exact ⟨gw gen11W0 ^ 3, pow_mem hxE _, hC⟩
  · exact ⟨gw gen11W0, hxE, hT⟩

end CFSG.AGLEmbedding.Norton.MON11_13
