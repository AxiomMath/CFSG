module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.CentralizerK
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Centralizer
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Steinberg.TwistedD4.Datum
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Weyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair
  CFSG.Timmesfeld.RankTwo CFSG.LieType.Universal CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.CurtisTits CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups commutatorElement

open CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.RootSystem CFSG.LieType.Universal

section BruhatPoint


variable {K : Type} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)

@[expose] def IsLongPos (k : ℤ) : Prop := k = 2 ∨ k = 4 ∨ k = 6 ∨ k = -2 ∨ k = -4 ∨ k = -6

omit hσ in
theorem weylAction_hexPos_four
    (w : (coxeterMatrix (twistedDatum σ.toRingHom).isFiniteType).Group) :
    ∃ k : ℤ, IsLongPos k ∧
      weylAction (twistedDatum σ.toRingHom).isFiniteType w (hexPos 4) = hexPos k := by
  refine (coxeterMatrix (twistedDatum σ.toRingHom).isFiniteType).toCoxeterSystem.simple_induction_left
    (p := fun w => ∃ k : ℤ, IsLongPos k ∧
      weylAction (twistedDatum σ.toRingHom).isFiniteType w (hexPos 4) = hexPos k)
    w ⟨4, Or.inr (Or.inl rfl), by rw [map_one]; rfl⟩ ?_
  intro w i ⟨k, hk, hw⟩
  have e : weylAction (twistedDatum σ.toRingHom).isFiniteType
      ((coxeterMatrix (twistedDatum σ.toRingHom).isFiniteType).toCoxeterSystem.simple i * w)
        (hexPos 4) = reflection cartanG2 i (hexPos k) := by
    rw [map_mul]
    erw [Module.End.mul_apply]
    erw [hw]
    erw [weylAction_simple]
    rfl
  rw [e]
  have h0 : ∀ j : ℤ, 1 ≤ j → j ≤ 5 → reflection cartanG2 0 (hexPos j) = hexPos (6 - j) ∧
      reflection cartanG2 0 (hexPos (-j)) = hexPos (-(6 - j)) := fun j h1 h5 =>
    reflection_zero_hexPos h1 h5
  have h1 : ∀ j : ℤ, 2 ≤ j → j ≤ 6 → reflection cartanG2 1 (hexPos j) = hexPos (8 - j) ∧
      reflection cartanG2 1 (hexPos (-j)) = hexPos (-(8 - j)) := fun j h2 h6 =>
    reflection_one_hexPos h2 h6
  fin_cases i
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨4, Or.inr (Or.inl rfl), (h0 2 (by norm_num) (by norm_num)).1⟩
    · exact ⟨2, Or.inl rfl, (h0 4 (by norm_num) (by norm_num)).1⟩
    · exact ⟨-6, by simp [IsLongPos], reflection_zero_hexPos_six.1⟩
    · exact ⟨-4, by simp [IsLongPos], (h0 2 (by norm_num) (by norm_num)).2⟩
    · exact ⟨-2, by simp [IsLongPos], (h0 4 (by norm_num) (by norm_num)).2⟩
    · exact ⟨6, by simp [IsLongPos], reflection_zero_hexPos_six.2⟩
  · rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨6, by simp [IsLongPos], (h1 2 (by norm_num) (by norm_num)).1⟩
    · exact ⟨4, by simp [IsLongPos], (h1 4 (by norm_num) (by norm_num)).1⟩
    · exact ⟨2, by simp [IsLongPos], (h1 6 (by norm_num) (by norm_num)).1⟩
    · exact ⟨-6, by simp [IsLongPos], (h1 2 (by norm_num) (by norm_num)).2⟩
    · exact ⟨-4, by simp [IsLongPos], (h1 4 (by norm_num) (by norm_num)).2⟩
    · exact ⟨-2, by simp [IsLongPos], (h1 6 (by norm_num) (by norm_num)).2⟩

include hσ in
theorem commute_posUnipotent_hexGroup_four
    {y x : twistedGroup σ.toRingHom}
    (hy : y ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)))
    (hx : x ∈ hexGroup (twistedX σ.toRingHom) 4) : y * x = x * y := by
  have R := d4Rel_model hσ
  obtain ⟨c, rfl⟩ := (mem_posUnipotent_d4_iff hσ y).1 hy
  obtain ⟨a, rfl⟩ := (mem_hexGroup_d4_iff hσ 3 x).1 (by simpa using hx)
  have h33 : ∀ b : fixedField σ.toRingHom, d4X hσ 3 b * d4X hσ 3 a = d4X hσ 3 a * d4X hσ 3 b := by
    intro b
    rw [← d4X_add hσ 3 b a, ← d4X_add hσ 3 a b]
    exact congrArg (fun c : fixedField σ.toRingHom => d4X hσ 3 c) (add_comm b a)
  have hc : ∀ i : Fin 6, Commute (d4X hσ i (c i)) (d4X hσ 3 a) := by
    intro i
    fin_cases i
    · exact R.c03 _ _
    · exact R.c13 _ _
    · exact (R.c23 _ _)
    · exact (h33 _ : Commute _ _)
    · exact (R.c34 _ _).symm
    · exact (R.c35 _ _).symm
  exact (Commute.mul_left (hc 0) (Commute.mul_left (hc 1) (Commute.mul_left (hc 2)
    (Commute.mul_left (hc 3) (Commute.mul_left (hc 4) (hc 5)))))).eq

omit hσ in
theorem isRoot_six_of_isLongPos {k : ℤ} (hk : IsLongPos k) : CFSG.GH74.BNPair.IsRoot 6 k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩

include hσ in
theorem bruhat_point
    (g : twistedGroup σ.toRingHom) :
    ∃ k : ℤ, IsLongPos k ∧ ∃ v ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)),
      (∀ x ∈ hexGroup (twistedX σ.toRingHom) 4, ∃ x' ∈ hexGroup (twistedX σ.toRingHom) k,
        g * x * g⁻¹ = v * x' * v⁻¹) ∧
      (∀ x' ∈ hexGroup (twistedX σ.toRingHom) k, ∃ x ∈ hexGroup (twistedX σ.toRingHom) 4,
        g * x * g⁻¹ = v * x' * v⁻¹) := by
  have hct := twistedDatum_isCTGroupDatum σ.toRingHom hσ
  have hext := twistedDatum_steinbergExtras σ.toRingHom hσ
  have R := d4RGD2 σ.toRingHom hσ
  obtain ⟨w, hw⟩ : ∃ w, g ∈ bruhatCell hct w := by
    have := iUnion_bruhatCell hct hext
    have hg : g ∈ ⋃ w, bruhatCell hct w := by rw [this]; trivial
    exact Set.mem_iUnion.1 hg
  obtain ⟨b, hb, u, hu, rfl⟩ := exists_eq_mul_nrep_mul hct hext hw
  rw [← SetLike.mem_coe, coe_borel hct, Set.mem_mul] at hb
  obtain ⟨t, ht, u₁, hu₁, rfl⟩ := hb
  obtain ⟨k, hk, hwk⟩ := weylAction_hexPos_four (σ := σ) w
  have hroot : hexPos 4 ∈ (twistedDatum σ.toRingHom).roots := by
    rw [twistedDatum_roots]
    exact isRoot_hexPos (by norm_num) (by norm_num)
  have hact := actsAs_nrep hct w (hexPos 4) hroot
  rw [hwk] at hact
  have hu' : u ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)) :=
    inversionUnipotent_le_posUnipotent w hu
  have hu₁' : u₁ ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)) := hu₁
  have hv : t * u₁ * t⁻¹ ∈ posUnipotent (g2Shape (twistedX σ.toRingHom)) :=
    R.conj_mem_U ht hu₁'
  have hk6 := isRoot_six_of_isLongPos hk
  refine ⟨k, hk, t * u₁ * t⁻¹, hv, ?_, ?_⟩
  · intro x hx
    have hx3 : nrep hct w * x * (nrep hct w)⁻¹ ∈ hexGroup (twistedX σ.toRingHom) k := by
      have : nrep hct w * x * (nrep hct w)⁻¹ ∈
          ((twistedDatum σ.toRingHom).rootGroup (hexPos 4)).map
            (MulAut.conj (nrep hct w)).toMonoidHom :=
        ⟨x, hx, rfl⟩
      rw [hact] at this
      exact this
    refine ⟨t * (nrep hct w * x * (nrep hct w)⁻¹) * t⁻¹,
      R.invariant k hk6 t ht _ hx3, ?_⟩
    have hc := commute_posUnipotent_hexGroup_four hσ hu' hx
    have e : u * x * u⁻¹ = x := by rw [hc]; group
    calc t * u₁ * (nrep hct w * u) * x * (t * u₁ * (nrep hct w * u))⁻¹
        = t * u₁ * nrep hct w * (u * x * u⁻¹) * (nrep hct w)⁻¹ * u₁⁻¹ * t⁻¹ := by group
      _ = t * u₁ * nrep hct w * x * (nrep hct w)⁻¹ * u₁⁻¹ * t⁻¹ := by rw [e]
      _ = _ := by group
  · intro x' hx'
    have hx'' : t⁻¹ * x' * t ∈ hexGroup (twistedX σ.toRingHom) k :=
      R.invariant k hk6 t⁻¹ (inv_mem ht) x' hx'
    have hx3 : t⁻¹ * x' * t ∈ (twistedDatum σ.toRingHom).rootGroup (hexPos k) := hx''
    rw [← hact] at hx3
    obtain ⟨x, hx, hxe⟩ := hx3
    refine ⟨x, hx, ?_⟩
    have hc := commute_posUnipotent_hexGroup_four hσ hu' hx
    have e : u * x * u⁻¹ = x := by rw [hc]; group
    have hxe' : nrep hct w * x * (nrep hct w)⁻¹ = t⁻¹ * x' * t := hxe
    calc t * u₁ * (nrep hct w * u) * x * (t * u₁ * (nrep hct w * u))⁻¹
        = t * u₁ * nrep hct w * (u * x * u⁻¹) * (nrep hct w)⁻¹ * u₁⁻¹ * t⁻¹ := by group
      _ = t * u₁ * (nrep hct w * x * (nrep hct w)⁻¹) * u₁⁻¹ * t⁻¹ := by rw [e]; group
      _ = t * u₁ * (t⁻¹ * x' * t) * u₁⁻¹ * t⁻¹ := by rw [hxe']
      _ = _ := by group

end BruhatPoint

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
