module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.GenD13.Gen
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13Abstract
public import Certificates.Certificate125552
public import Certificates.Certificate125553
public import Certificates.Certificate125554
public import Certificates.Certificate125555
public import Certificates.Certificate125556
public import Certificates.Certificate125557
public import Certificates.Certificate125558
public import Certificates.Certificate125559
public import Certificates.Certificate125561

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON11_13

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13

private theorem gw_powL (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (by simpa using wordLin_powL k w)

private theorem gw_eq_of_agreeC
    {w₁ w₂ : List Native.Gen}
    (h : agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂ = true) : gw w₁ = gw w₂ :=
  agree_sound (by rwa [agreeC_eq] at h)

theorem d13_order_check : d13OrderCheck () = true :=
  Certificates.certificate125552

theorem d13_comm_check : d13CommCheck () = true :=
  Certificates.certificate125553

theorem d13_x1x_check : d13X1xCheck () = true :=
  Certificates.certificate125554

theorem d13_x1y_check : d13X1yCheck () = true :=
  Certificates.certificate125555

theorem d13_x2x_check : d13X2xCheck () = true :=
  Certificates.certificate125556

theorem d13_x2y_check : d13X2yCheck () = true :=
  Certificates.certificate125557

theorem d13_anorm1_check : d13ANorm1Check () = true :=
  Certificates.certificate125558

theorem d13_anorm2_check : d13ANorm2Check () = true :=
  Certificates.certificate125559

theorem d13_anorm4_check : d13ANorm4Check () = true :=
  Certificates.certificate125561

theorem d13_gw_facts :
    gw genD13W0 ^ 13 = 1 ∧ gw genD13W2 ^ 13 = 1 ∧ gw genD13W1 ^ 13 = 1 ∧
    gw genD13W1 * gw genD13W0 = gw genD13W0 * gw genD13W1 ∧
    gw genD13W1 * gw genD13W2 = gw genD13W2 * gw genD13W1 ∧
    gw genD13W2 * gw genD13W0 = gw genD13W0 * (gw genD13W2 * gw genD13W1 ^ 4) ∧
    gw genD13W1 ≠ 1 ∧ gw genD13W8 = gw genD13W4 ^ 3 ∧
    gw genD13W3 * gw genD13W0 =
      gw genD13W1 ^ 11 * (gw genD13W2 ^ 10 * (gw genD13W0 ^ 6 * gw genD13W3)) ∧
    gw genD13W3 * gw genD13W2 =
      gw genD13W1 ^ 3 * (gw genD13W2 ^ 7 * (gw genD13W0 ^ 1 * gw genD13W3)) ∧
    gw genD13W4 * gw genD13W0 =
      gw genD13W1 ^ 8 * (gw genD13W2 ^ 7 * (gw genD13W0 ^ 7 * gw genD13W4)) ∧
    gw genD13W4 * gw genD13W2 =
      gw genD13W1 ^ 6 * (gw genD13W2 ^ 7 * (gw genD13W0 ^ 5 * gw genD13W4)) ∧
    gw genD13W5 * gw genD13W1 = gw genD13W1 ^ 12 * gw genD13W5 ∧
    gw genD13W5 * gw genD13W2 = gw genD13W2 ^ 12 * (gw genD13W1 ^ 12 * gw genD13W5) ∧
    gw genD13W6 * gw genD13W1 = gw genD13W2 ^ 12 * gw genD13W6 ∧
    gw genD13W6 * gw genD13W2 = gw genD13W1 ^ 1 * gw genD13W6 ∧
    gw genD13W7 * gw genD13W1 = gw genD13W1 ^ 12 * gw genD13W7 ∧
    gw genD13W7 * gw genD13W2 = gw genD13W2 ^ 8 * (gw genD13W1 ^ 10 * gw genD13W7) := by
  have hO := d13_order_check
  have hC := d13_comm_check
  have hX1x := d13_x1x_check
  have hX1y := d13_x1y_check
  have hX2x := d13_x2x_check
  have hX2y := d13_x2y_check
  have hN1 := d13_anorm1_check
  have hN2 := d13_anorm2_check
  have hN4 := d13_anorm4_check
  simp only [d13OrderCheck, Bool.and_eq_true, and_assoc] at hO
  simp only [d13CommCheck, Bool.and_eq_true, and_assoc] at hC
  simp only [d13ANorm1Check, Bool.and_eq_true] at hN1
  simp only [d13ANorm2Check, Bool.and_eq_true] at hN2
  simp only [d13ANorm4Check, Bool.and_eq_true] at hN4
  obtain ⟨h1, h2, h3⟩ := hO
  obtain ⟨h4, h5, h6, h7, h8⟩ := hC
  unfold d13X1xCheck d13Ag at hX1x
  unfold d13X1yCheck d13Ag at hX1y
  unfold d13X2xCheck d13Ag at hX2x
  unfold d13X2yCheck d13Ag at hX2y
  have h9 := hX1x
  have h10 := hX1y
  have h11 := hX2x
  have h12 := hX2y
  obtain ⟨h13, h14⟩ := hN1
  obtain ⟨h15, h16⟩ := hN2
  obtain ⟨h17, h18⟩ := hN4
  have e : ∀ {w₁ w₂ : List Native.Gen},
      agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂ = true → gw w₁ = gw w₂ :=
    fun h => gw_eq_of_agreeC h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := e h1; rwa [gw_powL, gw_nil] at this
  · have := e h2; rwa [gw_powL, gw_nil] at this
  · have := e h3; rwa [gw_powL, gw_nil] at this
  · have := e h4; simp only [gw_append] at this; exact this
  · have := e h5; simp only [gw_append] at this; exact this
  · have := e h6; simp only [gw_append, gw_powL] at this; exact this
  · exact gw_ne_one_of_moveCheck h7
  · have := e h8; rwa [gw_powL] at this
  · have := e h9; simp only [gw_append, gw_powL] at this; exact this
  · have := e h10; simp only [gw_append, gw_powL] at this; exact this
  · have := e h11; simp only [gw_append, gw_powL] at this; exact this
  · have := e h12; simp only [gw_append, gw_powL] at this; exact this
  · have := e h13; simp only [gw_append, gw_powL] at this; exact this
  · have := e h14; simp only [gw_append, gw_powL] at this; exact this
  · have := e h15; simp only [gw_append, gw_powL] at this; exact this
  · have := e h16; simp only [gw_append, gw_powL] at this; exact this
  · have := e h17; simp only [gw_append, gw_powL] at this; exact this
  · have := e h18; simp only [gw_append, gw_powL] at this; exact this

set_option maxHeartbeats 1600000 in
theorem glbCore_two_thirteen_gmat :
    ∀ S : Sylow 13 Gmat,
      @CFSG.Open.GLBCore Gmat _ generated_rational_group_finite_simple.2.2 13 2
        (S : Subgroup Gmat) = ⊤ := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨hx, hy, hz13, hzx, hzy, hcomm, hz1, ht, hx1x, hx1y, hx2x, hx2y, hy1z, hy1y, hy2z, hy2y,
    hy4z, hy4y⟩ := d13_gw_facts
  have hgen : Subgroup.closure (Set.range fun i : Fin genD13Gens.size => gw genD13Gens[i]) = ⊤ :=
    closure_genD13_eq_top
  have hsz : genD13Gens.size = 9 := rfl
  have hzS : gw genD13W1 ∈ Subgroup.closure ({gw genD13W0, gw genD13W2} : Set Gmat) :=
    mem_closure_of_comm_relation hz13 hcomm
  have hxS : gw genD13W0 ∈ Subgroup.closure ({gw genD13W0, gw genD13W2} : Set Gmat) :=
    Subgroup.subset_closure (by simp)
  have hyS : gw genD13W2 ∈ Subgroup.closure ({gw genD13W0, gw genD13W2} : Set Gmat) :=
    Subgroup.subset_closure (by simp)
  have hzA : gw genD13W1 ∈ Subgroup.closure ({gw genD13W1, gw genD13W2} : Set Gmat) :=
    Subgroup.subset_closure (by simp)
  have hyA : gw genD13W2 ∈ Subgroup.closure ({gw genD13W1, gw genD13W2} : Set Gmat) :=
    Subgroup.subset_closure (by simp)
  have hN1 : gw genD13W3 ∈ Subgroup.normalizer
      (Subgroup.closure ({gw genD13W0, gw genD13W2} : Set Gmat) : Set Gmat) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · refine conj_mem_of_mul_eq (n := gw genD13W1 ^ 11 * (gw genD13W2 ^ 10 * gw genD13W0 ^ 6))
        (mul_mem (pow_mem hzS _) (mul_mem (pow_mem hyS _) (pow_mem hxS _))) ?_
      rw [hx1x]; simp only [mul_assoc]
    · refine conj_mem_of_mul_eq (n := gw genD13W1 ^ 3 * (gw genD13W2 ^ 7 * gw genD13W0 ^ 1))
        (mul_mem (pow_mem hzS _) (mul_mem (pow_mem hyS _) (pow_mem hxS _))) ?_
      rw [hx1y]; simp only [mul_assoc]
  have hN2 : gw genD13W4 ∈ Subgroup.normalizer
      (Subgroup.closure ({gw genD13W0, gw genD13W2} : Set Gmat) : Set Gmat) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · refine conj_mem_of_mul_eq (n := gw genD13W1 ^ 8 * (gw genD13W2 ^ 7 * gw genD13W0 ^ 7))
        (mul_mem (pow_mem hzS _) (mul_mem (pow_mem hyS _) (pow_mem hxS _))) ?_
      rw [hx2x]; simp only [mul_assoc]
    · refine conj_mem_of_mul_eq (n := gw genD13W1 ^ 6 * (gw genD13W2 ^ 7 * gw genD13W0 ^ 5))
        (mul_mem (pow_mem hzS _) (mul_mem (pow_mem hyS _) (pow_mem hxS _))) ?_
      rw [hx2y]; simp only [mul_assoc]
  have hN5 : gw genD13W5 ∈ Subgroup.normalizer
      (Subgroup.closure ({gw genD13W1, gw genD13W2} : Set Gmat) : Set Gmat) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · exact conj_mem_of_mul_eq (n := gw genD13W1 ^ 12) (pow_mem hzA _) hy1z
    · exact conj_mem_of_mul_eq (n := gw genD13W2 ^ 12 * gw genD13W1 ^ 12)
        (mul_mem (pow_mem hyA _) (pow_mem hzA _)) (by rw [hy1y]; simp only [mul_assoc])
  have hN6 : gw genD13W6 ∈ Subgroup.normalizer
      (Subgroup.closure ({gw genD13W1, gw genD13W2} : Set Gmat) : Set Gmat) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · exact conj_mem_of_mul_eq (n := gw genD13W2 ^ 12) (pow_mem hyA _) hy2z
    · exact conj_mem_of_mul_eq (n := gw genD13W1 ^ 1) (pow_mem hzA _) hy2y
  have hN7 : gw genD13W7 ∈ Subgroup.normalizer
      (Subgroup.closure ({gw genD13W1, gw genD13W2} : Set Gmat) : Set Gmat) := by
    refine mem_normalizer_closure_pair ?_ ?_
    · exact conj_mem_of_mul_eq (n := gw genD13W1 ^ 12) (pow_mem hzA _) hy4z
    · exact conj_mem_of_mul_eq (n := gw genD13W2 ^ 8 * gw genD13W1 ^ 10)
        (mul_mem (pow_mem hyA _) (pow_mem hzA _)) (by rw [hy4y]; simp only [mul_assoc])
  refine glbCore_two_thirteen_of_heisenberg (x := gw genD13W0) (y := gw genD13W2)
    (z := gw genD13W1) hx hy hz13 hzx hzy hcomm hz1 hgen ?_
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  rw [hsz] at hi
  interval_cases i
  · exact Or.inl (Subgroup.le_normalizer hxS)
  · exact Or.inr (Subgroup.le_normalizer hzA)
  · exact Or.inr (Subgroup.le_normalizer hyA)
  · exact Or.inl hN1
  · exact Or.inl hN2
  · exact Or.inr hN5
  · exact Or.inr hN6
  · exact Or.inr hN7
  · exact Or.inl (by
      show gw genD13W8 ∈ _
      rw [ht]
      exact pow_mem hN2 3)

end CFSG.AGLEmbedding.Norton.MON11_13
