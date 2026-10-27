module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Hyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRelG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSetBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y5_B_eq_closure {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.B = Subgroup.closure {s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} := by
  rw [SFrame.B]
  rw [show centIn s.fr.S (closure {s.fr.b₁ * s.fr.b₂}) =
      centEl s.fr.S (s.fr.b₁ * s.fr.b₂) by
    rw [centIn, centEl, Subgroup.centralizer_closure]]
  exact hH.hLF.fact12.2.2.2.1

private theorem commutator_swap_mem {H : Type*} [Group H] {D : Subgroup H} {x y : H}
    (h : ⁅x, y⁆ ∈ D) : ⁅y, x⁆ ∈ D := by
  rw [show ⁅y, x⁆ = (⁅x, y⁆)⁻¹ from (commutatorElement_inv x y).symm]
  exact D.inv_mem h

private theorem closure_sq_comm_le {H : Type*} [Group H] {D : Subgroup H} {T : Set H}
    (hN : ∀ x ∈ Subgroup.closure T, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hsq : ∀ t ∈ T, t ^ 2 ∈ D)
    (hcomm : ∀ t ∈ T, ∀ t' ∈ T, ⁅t, t'⁆ ∈ D) :
    (∀ x ∈ Subgroup.closure T, x ^ 2 ∈ D) ∧
      ⁅Subgroup.closure T, Subgroup.closure T⁆ ≤ D := by
  have hstep2 : ∀ x ∈ Subgroup.closure T, ∀ y ∈ Subgroup.closure T, ⁅x, y⁆ ∈ D := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => ⁅x, y⁆ ∈ D)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
    · intro a b ha hb
      exact hcomm a ha b hb
    · intro b hb
      simp
    · intro a ha
      simp
    · intro a b c ha hb hc iha ihb
      have e : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact D.mul_mem (hN a ha _ ihb) iha
    · intro b c a hb hc ha ihb ihc
      have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      exact D.mul_mem ihb (hN b hb _ ihc)
    · intro a b ha hb iha
      have e : ⁅a⁻¹, b⁆ = a⁻¹ * (⁅a, b⁆)⁻¹ * a := by
        rw [commutatorElement_def]; group
      rw [e]
      simpa using hN a⁻¹ (Subgroup.inv_mem _ ha) _ (D.inv_mem iha)
    · intro a b ha hb iha
      have e : ⁅a, b⁻¹⁆ = b⁻¹ * (⁅a, b⁆)⁻¹ * b := by
        rw [commutatorElement_def]; group
      rw [e]
      simpa using hN b⁻¹ (Subgroup.inv_mem _ hb) _ (D.inv_mem iha)
  have hcomm_le : ⁅Subgroup.closure T, Subgroup.closure T⁆ ≤ D :=
    Subgroup.commutator_le.mpr hstep2
  refine ⟨?_, hcomm_le⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem t ht => exact hsq t ht
  | one => simpa using D.one_mem
  | mul x y hx hy ihx ihy =>
      have hc : ⁅x, y⁆ ∈ D := hstep2 x hx y hy
      have e : (x * y) ^ 2 = ⁅x, y⁆ * (y * x ^ 2 * y⁻¹) * y ^ 2 := by
        simp only [commutatorElement_def, pow_two]
        group
      rw [e]
      exact D.mul_mem (D.mul_mem hc (hN y hy _ ihx)) ihy
  | inv x hx ih =>
      have e : (x⁻¹) ^ 2 = (x ^ 2)⁻¹ := by group
      rw [e]
      exact D.inv_mem ih

private theorem y5_z_central {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.fr.S, x * s.fr.z = s.fr.z * x := by
  have hcenS : cen s.fr.S = s.fr.Z := hH.hLF.fact14.1.1
  have hzC : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) := by
    have hzZ : s.fr.z ∈ s.fr.Z := Subgroup.mem_zpowers s.fr.z
    exact (Subgroup.mem_inf.mp (hcenS.symm ▸ hzZ)).2
  intro x hx
  exact Subgroup.mem_centralizer_iff.mp hzC x hx

private theorem y5_comm_a12_b1 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ⁅s.fr.a₁ * s.fr.a₂, s.fr.b₁⁆ = s.fr.z := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have h21 : ⁅s.fr.a₂, s.fr.b₁⁆ = 1 := by
    rw [show ⁅s.fr.a₂, s.fr.b₁⁆ = (⁅s.fr.b₁, s.fr.a₂⁆)⁻¹ from
      (commutatorElement_inv s.fr.b₁ s.fr.a₂).symm, hsrel.b1a2, inv_one]
  rw [commutatorElement_mul_left_eq_conj_mul, h21, hsrel.comm1]
  group

private theorem y5_comm_a12_b2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ⁅s.fr.a₁ * s.fr.a₂, s.fr.b₂⁆ = s.fr.z := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hz := y5_z_central hH
  rw [commutatorElement_mul_left_eq_conj_mul, hsrel.comm2, hsrel.a1b2, mul_one]
  rw [hz s.fr.a₁ (Subgroup.subset_closure (by simp))]
  group

private theorem y5_comm_a12_h0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ⁅s.fr.a₁ * s.fr.a₂, s.fr.h₀⁆ = s.fr.b₁ * s.fr.b₂ := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hz := y5_z_central hH
  have ha1b2 : s.fr.a₁ * s.fr.b₂ = s.fr.b₂ * s.fr.a₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp hsrel.a1b2
  have hb1b2 : s.fr.b₁ * s.fr.b₂ = s.fr.b₂ * s.fr.b₁ :=
    commutatorElement_eq_one_iff_mul_comm.mp hsrel.b1b2
  have hA : s.fr.a₁ * (s.fr.b₂ * s.fr.z) * s.fr.a₁⁻¹ = s.fr.b₂ * s.fr.z := by
    have h1 : s.fr.a₁ * s.fr.b₂ * s.fr.a₁⁻¹ = s.fr.b₂ := by rw [ha1b2]; group
    have h2 : s.fr.a₁ * s.fr.z * s.fr.a₁⁻¹ = s.fr.z := by
      rw [hz s.fr.a₁ (Subgroup.subset_closure (by simp))]; group
    calc s.fr.a₁ * (s.fr.b₂ * s.fr.z) * s.fr.a₁⁻¹
        = (s.fr.a₁ * s.fr.b₂ * s.fr.a₁⁻¹) * (s.fr.a₁ * s.fr.z * s.fr.a₁⁻¹) := by group
      _ = s.fr.b₂ * s.fr.z := by rw [h1, h2]
  have hB : (s.fr.b₂ * s.fr.z) * (s.fr.b₁ * s.fr.z) = s.fr.b₁ * s.fr.b₂ := by
    have hb1z : s.fr.b₁ * s.fr.z = s.fr.z * s.fr.b₁ :=
      hz s.fr.b₁ (Subgroup.subset_closure (by simp))
    calc (s.fr.b₂ * s.fr.z) * (s.fr.b₁ * s.fr.z)
        = s.fr.b₂ * (s.fr.z * s.fr.b₁) * s.fr.z := by group
      _ = s.fr.b₂ * (s.fr.b₁ * s.fr.z) * s.fr.z := by rw [← hb1z]
      _ = s.fr.b₂ * s.fr.b₁ * (s.fr.z * s.fr.z) := by group
      _ = s.fr.b₂ * s.fr.b₁ := by rw [← pow_two, hsrel.z_sq, mul_one]
      _ = s.fr.b₁ * s.fr.b₂ := hb1b2.symm
  rw [commutatorElement_mul_left_eq_conj_mul, hsrel.a2h, hsrel.a1h, hA, hB]

private theorem y5_gen_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ t ∈ ({s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} : Set G),
      t ^ 2 ∈ cen s.fr.B := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hcen : cen s.fr.B = Subgroup.closure {s.fr.b₁ * s.fr.b₂, s.fr.z} :=
    hH.hLF.fact14.2.2.1.1
  have hzV : s.fr.z ∈ cen s.fr.B := by
    rw [hcen]; exact Subgroup.subset_closure (by simp)
  have h1V : (1 : G) ∈ cen s.fr.B := (cen s.fr.B).one_mem
  intro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · have hsq : (s.fr.a₁ * s.fr.a₂) ^ 2 = 1 := by
      have hc : Commute s.fr.a₁ s.fr.a₂ :=
        commutatorElement_eq_one_iff_commute.mp hsrel.a1a2
      rw [hc.mul_pow 2, hsrel.a1_sq, hsrel.a2_sq, ← pow_two, hsrel.z_sq]
    rw [hsq]; exact h1V
  · show s.fr.z ∈ cen s.fr.B; exact hzV
  · rw [hsrel.b2_sq]; exact hzV
  · rw [hsrel.h0_sq]; exact h1V

private theorem y5_gen_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ t ∈ ({s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} : Set G),
      ∀ t' ∈ ({s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} : Set G),
        ⁅t, t'⁆ ∈ cen s.fr.B := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hcen : cen s.fr.B = Subgroup.closure {s.fr.b₁ * s.fr.b₂, s.fr.z} :=
    hH.hLF.fact14.2.2.1.1
  have hzV : s.fr.z ∈ cen s.fr.B := by rw [hcen]; exact Subgroup.subset_closure (by simp)
  have hwV : s.fr.b₁ * s.fr.b₂ ∈ cen s.fr.B := by
    rw [hcen]; exact Subgroup.subset_closure (by simp)
  have h1V : (1 : G) ∈ cen s.fr.B := (cen s.fr.B).one_mem
  have hAb1 : ⁅s.fr.a₁ * s.fr.a₂, s.fr.b₁⁆ ∈ cen s.fr.B := by
    rw [y5_comm_a12_b1 hH]; exact hzV
  have hAb2 : ⁅s.fr.a₁ * s.fr.a₂, s.fr.b₂⁆ ∈ cen s.fr.B := by
    rw [y5_comm_a12_b2 hH]; exact hzV
  have hAh0 : ⁅s.fr.a₁ * s.fr.a₂, s.fr.h₀⁆ ∈ cen s.fr.B := by
    rw [y5_comm_a12_h0 hH]; exact hwV
  have hb1h0 : ⁅s.fr.b₁, s.fr.h₀⁆ ∈ cen s.fr.B := by rw [hsrel.b1h]; exact hzV
  have hb2h0 : ⁅s.fr.b₂, s.fr.h₀⁆ ∈ cen s.fr.B := by rw [hsrel.b2h]; exact hzV
  have hb1b2 : ⁅s.fr.b₁, s.fr.b₂⁆ ∈ cen s.fr.B := by rw [hsrel.b1b2]; exact h1V
  have hb2b1 : ⁅s.fr.b₂, s.fr.b₁⁆ ∈ cen s.fr.B := commutator_swap_mem hb1b2
  have hb1A : ⁅s.fr.b₁, s.fr.a₁ * s.fr.a₂⁆ ∈ cen s.fr.B := commutator_swap_mem hAb1
  have hb2A : ⁅s.fr.b₂, s.fr.a₁ * s.fr.a₂⁆ ∈ cen s.fr.B := commutator_swap_mem hAb2
  have hh0A : ⁅s.fr.h₀, s.fr.a₁ * s.fr.a₂⁆ ∈ cen s.fr.B := commutator_swap_mem hAh0
  have hh0b1 : ⁅s.fr.h₀, s.fr.b₁⁆ ∈ cen s.fr.B := commutator_swap_mem hb1h0
  have hh0b2 : ⁅s.fr.h₀, s.fr.b₂⁆ ∈ cen s.fr.B := commutator_swap_mem hb2h0
  intro t ht t' ht'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht ht'
  rcases ht with rfl | rfl | rfl | rfl <;> rcases ht' with rfl | rfl | rfl | rfl
  all_goals
    first
    | exact hAb1
    | exact hAb2
    | exact hAh0
    | exact hb1A
    | exact hb2A
    | exact hh0A
    | exact hb1h0
    | exact hb2h0
    | exact hh0b1
    | exact hh0b2
    | exact hb1b2
    | exact hb2b1
    | (rw [commutatorElement_self]; exact h1V)

private theorem y5_B_sq_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (∀ x ∈ s.fr.B, x ^ 2 ∈ cen s.fr.B) ∧
      ∀ x ∈ s.fr.B, ∀ y ∈ s.fr.B, ⁅x, y⁆ ∈ cen s.fr.B := by
  have hB : s.fr.B =
      Subgroup.closure ({s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} : Set G) :=
    y5_B_eq_closure hH
  have hN : ∀ x ∈ Subgroup.closure ({s.fr.a₁ * s.fr.a₂, s.fr.b₁, s.fr.b₂, s.fr.h₀} : Set G),
      ∀ d ∈ cen s.fr.B, x * d * x⁻¹ ∈ cen s.fr.B := by
    intro x hx d hd
    have hxB : x ∈ s.fr.B := hB.symm ▸ hx
    have hcomm : x * d = d * x :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2 x hxB
    have hfix : x * d * x⁻¹ = d := by rw [hcomm]; group
    rw [hfix]; exact hd
  have hkey := closure_sq_comm_le hN (y5_gen_sq hH) (y5_gen_comm hH)
  refine ⟨fun x hx => hkey.1 x (hB ▸ hx), ?_⟩
  intro x hx y hy
  exact Subgroup.commutator_le.mp hkey.2 x (hB ▸ hx) y (hB ▸ hy)

theorem y5_V_le_F {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    cen s.fr.B ≤ s.fr.F := by
  have hcen : cen s.fr.B = Subgroup.closure {s.fr.b₁ * s.fr.b₂, s.fr.z} :=
    hH.hLF.fact14.2.2.1.1
  rw [hcen, SFrame.F]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> exact Subgroup.subset_closure (by simp)

theorem y5_V_le_A {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    cen s.fr.B ≤ s.fr.A := by
  have hcen : cen s.fr.B = Subgroup.closure {s.fr.b₁ * s.fr.b₂, s.fr.z} :=
    hH.hLF.fact14.2.2.1.1
  rw [hcen, SFrame.A]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · rw [SFrame.z]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2

theorem y5_B_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.fr.B, x ^ 2 ∈ cen s.fr.B :=
  (y5_B_sq_comm hH).1

theorem y5_B_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.fr.B, ∀ y ∈ s.fr.B, ⁅x, y⁆ ∈ cen s.fr.B :=
  (y5_B_sq_comm hH).2

theorem y5_V_le_J {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    cen s.fr.B ≤ thompsonSubgroup s.fr.B := by
  obtain ⟨-, -, -, -, -, -, -, -, homega, -⟩ := hH.hLF.fact14.2.2.1
  have homega' : cen s.fr.B = omega1 (thompsonSubgroup s.fr.B) := homega
  rw [homega', omega1]
  exact (Subgroup.closure_le _).mpr fun y hy => hy.1

theorem y5_J_le_B (s : Setting3 G L) : thompsonSubgroup s.fr.B ≤ s.fr.B :=
  CFSG.ambientMaxCardThompson_le s.fr.B

theorem y5_J_conj (s : Setting3 G L) :
    ∀ x ∈ normalizer (s.fr.B : Set G), ∀ j ∈ thompsonSubgroup s.fr.B,
      x * j * x⁻¹ ∈ thompsonSubgroup s.fr.B := by
  intro x hx j hj
  have hmap : s.fr.B.map (MulAut.conj x) = s.fr.B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hmem : x * j * x⁻¹ ∈ (thompsonSubgroup s.fr.B).map (MulAut.conj x : G →* G) :=
    Subgroup.mem_map.mpr ⟨j, hj, by
      show (MulAut.conj x) j = x * j * x⁻¹
      rw [MulAut.conj_apply]⟩
  have h := thompsonSubgroup_map (f := (MulAut.conj x : G →* G))
    (MulAut.conj x).injective s.fr.B
  rw [hmap] at h
  have h' : thompsonSubgroup s.fr.B =
      (thompsonSubgroup s.fr.B).map (MulAut.conj x : G →* G) := h
  exact h'.symm ▸ hmem

theorem y5_a12_mem_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.a₁ * s.fr.a₂ ∈ s.fr.B := by
  rw [y5_B_eq_closure hH]
  exact Subgroup.subset_closure (by simp)

theorem y5_a12_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (s.fr.a₁ * s.fr.a₂) ^ 2 = 1 := by
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hc : Commute s.fr.a₁ s.fr.a₂ :=
    commutatorElement_eq_one_iff_commute.mp hsrel.a1a2
  rw [hc.mul_pow 2, hsrel.a1_sq, hsrel.a2_sq, ← pow_two, hsrel.z_sq]

theorem y5_a12_not_mem_J {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.a₁ * s.fr.a₂ ∉ thompsonSubgroup s.fr.B := by
  intro hJ
  obtain ⟨-, -, -, -, -, -, -, -, homega, -⟩ := hH.hLF.fact14.2.2.1
  have homega' : cen s.fr.B = omega1 (thompsonSubgroup s.fr.B) := homega
  have hom : s.fr.a₁ * s.fr.a₂ ∈ omega1 (thompsonSubgroup s.fr.B) :=
    Subgroup.subset_closure ⟨hJ, y5_a12_sq hH⟩
  rw [← homega'] at hom
  have hcomm : s.fr.a₁ * s.fr.a₂ ∈ Subgroup.centralizer (s.fr.B : Set G) :=
    (Subgroup.mem_inf.mp hom).2
  have hb1B : s.fr.b₁ ∈ s.fr.B := by
    rw [y5_B_eq_closure hH]; exact Subgroup.subset_closure (by simp)
  have hc : (s.fr.a₁ * s.fr.a₂) * s.fr.b₁ = s.fr.b₁ * (s.fr.a₁ * s.fr.a₂) :=
    (Subgroup.mem_centralizer_iff.mp hcomm s.fr.b₁ hb1B).symm
  have hz1 : s.fr.z = 1 := by
    have h := commutatorElement_eq_one_iff_mul_comm.mpr hc
    rw [y5_comm_a12_b1 hH] at h
    exact h
  have hzne1 : s.fr.z ≠ 1 := by
    intro h
    have := s3_z_order s (lfactsA_of_setting hH.hS hH.hZ s)
    rw [h, orderOf_one] at this
    norm_num at this
  exact hzne1 hz1

theorem y5_B_eq_J_sup {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.B = thompsonSubgroup s.fr.B ⊔ zpowers (s.fr.a₁ * s.fr.a₂) := by
  obtain ⟨hcen, -, -, -, -, -, hJ0, -, -, -⟩ := hH.hLF.fact14.2.2.1
  have hcen' : cen s.fr.B = Subgroup.closure {s.fr.b₁ * s.fr.b₂, s.fr.z} := hcen
  have hJ0' : thompsonSubgroup s.fr.B =
      Subgroup.closure {s.fr.b₁, s.fr.a₁ * s.fr.a₂ * s.fr.h₀} := hJ0
  refine le_antisymm ?_ ?_
  · refine le_trans (le_of_eq (y5_B_eq_closure hH)) ?_
    apply (Subgroup.closure_le _).mpr
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_left (by rw [hJ0']; exact Subgroup.subset_closure (by simp))
    · refine Subgroup.mem_sup_left ?_
      have hb1 : s.fr.b₁ ∈ thompsonSubgroup s.fr.B := by
        rw [hJ0']; exact Subgroup.subset_closure (by simp)
      have hw : s.fr.b₁ * s.fr.b₂ ∈ thompsonSubgroup s.fr.B :=
        y5_V_le_J hH (by rw [hcen']; exact Subgroup.subset_closure (by simp))
      have hb2 : s.fr.b₂ = s.fr.b₁⁻¹ * (s.fr.b₁ * s.fr.b₂) := by group
      rw [hb2]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hb1) hw
    · have hmem : s.fr.a₁ * s.fr.a₂ * s.fr.h₀ ∈ thompsonSubgroup s.fr.B := by
        rw [hJ0']; exact Subgroup.subset_closure (by simp)
      have hinv : (s.fr.a₁ * s.fr.a₂)⁻¹ ∈ zpowers (s.fr.a₁ * s.fr.a₂) :=
        Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      have heq : s.fr.h₀ =
          (s.fr.a₁ * s.fr.a₂)⁻¹ * (s.fr.a₁ * s.fr.a₂ * s.fr.h₀) := by group
      rw [heq, sup_comm]
      exact Subgroup.mul_mem_sup hinv hmem
  · exact sup_le (y5_J_le_B s) (Subgroup.zpowers_le.mpr (y5_a12_mem_B hH))

end CFSG.OddStandard.HigherRank.YamadaG23
