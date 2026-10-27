module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SevenWeyl
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameDatum
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SplitTorus
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TorusFrame
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankLang
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh
open CFSG.RankThree.E6 (charVal charVal_single)

section Irrational

theorem int_eq_zero_of_add_sqrt_two_sqrt_three {a b c : ℤ}
    (h : (a : ℝ) + Real.sqrt 2 * (b : ℝ) + Real.sqrt 3 * (c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have h3 : Irrational (Real.sqrt 3) := by
    have := Nat.Prime.irrational_sqrt Nat.prime_three
    simpa using this
  have h6 : Irrational (Real.sqrt 6) := by
    have hns : ¬ IsSquare 6 := by
      rintro ⟨r, hr⟩
      have hr3 : r ≤ 3 := by nlinarith
      interval_cases r <;> omega
    have h := (irrational_sqrt_natCast_iff (n := 6)).2 hns
    simpa using h
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hab : (a : ℝ) * b = 0 := by
    by_contra hne
    have key : 2 * Real.sqrt 2 * ((a : ℝ) * b) = 3 * (c : ℝ) ^ 2 - (a : ℝ) ^ 2 - 2 * (b : ℝ) ^ 2 := by
      have e : (a : ℝ) + Real.sqrt 2 * b = -(Real.sqrt 3 * c) := by linarith
      have e2 := congrArg (fun t : ℝ => t ^ 2) e
      nlinarith [hs2, hs3]
    apply h2
    refine ⟨((3 * c ^ 2 - a ^ 2 - 2 * b ^ 2 : ℤ) : ℚ) / (2 * ((a * b : ℤ) : ℚ)), ?_⟩
    have hden : (2 : ℝ) * ((a : ℝ) * b) ≠ 0 := mul_ne_zero two_ne_zero hne
    push_cast
    rw [div_eq_iff hden]
    linear_combination (-1 : ℝ) * key
  rcases mul_eq_zero.1 hab with ha | hb
  ·
    have ha' : a = 0 := by exact_mod_cast ha
    subst ha'
    have e : Real.sqrt 2 * b + Real.sqrt 3 * c = 0 := by simpa using h
    have e2 : 2 * (b : ℝ) + Real.sqrt 6 * c = 0 := by
      calc 2 * (b : ℝ) + Real.sqrt 6 * c
          = (Real.sqrt 2 * Real.sqrt 2) * b + (Real.sqrt 2 * Real.sqrt 3) * c := by
            rw [hs2, hs6]
        _ = Real.sqrt 2 * (Real.sqrt 2 * b + Real.sqrt 3 * c) := by ring
        _ = 0 := by rw [e, mul_zero]
    by_cases hc : c = 0
    · subst hc
      simp only [Int.cast_zero, mul_zero, add_zero] at e2
      have : (b : ℝ) = 0 := by linarith
      exact ⟨rfl, by exact_mod_cast this, rfl⟩
    · exfalso
      apply h6
      refine ⟨(-(2 * b : ℤ) : ℚ) / (c : ℚ), ?_⟩
      have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.2 hc
      push_cast
      rw [div_eq_iff hc']
      linear_combination (-1 : ℝ) * e2
  ·
    have hb' : b = 0 := by exact_mod_cast hb
    subst hb'
    have e : (a : ℝ) + Real.sqrt 3 * c = 0 := by simpa using h
    by_cases hc : c = 0
    · subst hc
      simp only [Int.cast_zero, mul_zero, add_zero] at e
      exact ⟨by exact_mod_cast e, rfl, rfl⟩
    · exfalso
      apply h3
      refine ⟨(-(a : ℚ)) / (c : ℚ), ?_⟩
      have hc' : (c : ℝ) ≠ 0 := Int.cast_ne_zero.2 hc
      push_cast
      rw [div_eq_iff hc']
      linear_combination (-1 : ℝ) * e

end Irrational

section Averaging

variable {τ : Tag}

theorem inf3_dualWeylStabilizer_le_closure_of_card
    {p : ℕ} [Fact p.Prime] (z₀ z₁ z₂ : Fin τ.rank → ZMod p)
    (hU : ¬ p ∣ Nat.card ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓
      dualWeylStabilizer z₂)) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓ dualWeylStabilizer z₂ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁ ∩ rootKernel z₂,
        s = rootReflection α} := by
  classical
  set U := dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓ dualWeylStabilizer z₂ with hUdef
  have : Fintype U := Fintype.ofFinite _
  have hcard : (Fintype.card U : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff, ← Nat.card_eq_fintype_card] at h
    exact hU h
  have hz : ∀ z : Fin τ.rank → ZMod p, U ≤ dualWeylStabilizer z →
      ∀ α, charVal (avgColumn U (intLift z)) α = 0 → charVal z α = 0 := by
    intro z hUz α h
    have h' := charVal_avgColumn_cast hUz α
    rw [h, Int.cast_zero, eq_comm] at h'
    exact (mul_eq_zero.1 h').resolve_left hcard
  have hU0 : U ≤ dualWeylStabilizer z₀ := inf_le_left.trans inf_le_left
  have hU1 : U ≤ dualWeylStabilizer z₁ := inf_le_left.trans inf_le_right
  have hU2 : U ≤ dualWeylStabilizer z₂ := inf_le_right
  intro w hw
  have hwinv : w⁻¹ ∈ U := U.inv_mem hw
  have hfix : w ∈ weylStabilizer τ (dualVector (avgColumn U (intLift z₀)) +
      Real.sqrt 2 • dualVector (avgColumn U (intLift z₁)) +
      Real.sqrt 3 • dualVector (avgColumn U (intLift z₂))) := by
    rw [mem_weylStabilizer, map_add, map_add, map_smul, map_smul,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v,
      weylAct_dualVector_eq fun v => charVal_avgColumn_smul _ hwinv v]
  rw [(exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2] at hfix
  refine Subgroup.closure_mono ?_ hfix
  rintro _ ⟨α, hα, h0, rfl⟩
  rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    inner_ofLattice_dualVector, inner_ofLattice_dualVector, inner_ofLattice_dualVector] at h0
  obtain ⟨h0', h1', h2'⟩ := int_eq_zero_of_add_sqrt_two_sqrt_three h0
  exact ⟨α, ⟨⟨⟨hα, hz z₀ hU0 α h0'⟩, ⟨hα, hz z₁ hU1 α h1'⟩⟩, ⟨hα, hz z₂ hU2 α h2'⟩⟩, rfl⟩

end Averaging

section Sylow

set_option linter.unusedSectionVars false


theorem e7_inf3_le_closure_of_fix {z₀ z₁ z₂ : Fin Tag.E7.rank → ZMod 7}
    (h₀ : e7G0 ∈ dualWeylStabilizer z₀) (h₁ : e7G0 ∈ dualWeylStabilizer z₁)
    (h₂ : e7G0 ∈ dualWeylStabilizer z₂) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓ dualWeylStabilizer z₂ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁ ∩ rootKernel z₂,
        s = rootReflection α} := by
  have e₀ := e7_fixed_col_eq (e7G0_fix h₀)
  have e₁ := e7_fixed_col_eq (e7G0_fix h₁)
  have e₂ := e7_fixed_col_eq (e7G0_fix h₂)
  generalize z₀ 1 = c₀ at e₀
  generalize z₁ 1 = c₁ at e₁
  generalize z₂ 1 = c₂ at e₂
  subst e₀ e₁ e₂
  by_cases hz : c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0
  ·
    obtain ⟨rfl, rfl, rfl⟩ := hz
    refine le_trans le_top ?_
    rw [← closure_rootReflection_eq_top (τ := Tag.E7)]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨α, ⟨⟨⟨hα, by rw [charVal_pi_single]; simp⟩, ⟨hα, by rw [charVal_pi_single]; simp⟩⟩,
      ⟨hα, by rw [charVal_pi_single]; simp⟩⟩, rfl⟩
  ·
    have hsub : {s | ∃ α, IsRoot Tag.E7 α ∧ α 1 = 0 ∧ s = rootReflection α} ⊆
        {s | ∃ α ∈ rootKernel (Pi.single (1 : Fin Tag.E7.rank) c₀) ∩
          rootKernel (Pi.single (1 : Fin Tag.E7.rank) c₁) ∩
          rootKernel (Pi.single (1 : Fin Tag.E7.rank) c₂), s = rootReflection α} := by
      rintro _ ⟨α, hα, h1, rfl⟩
      exact ⟨α, ⟨⟨⟨hα, by rw [charVal_pi_single, h1]; simp⟩,
        ⟨hα, by rw [charVal_pi_single, h1]; simp⟩⟩, ⟨hα, by rw [charVal_pi_single, h1]; simp⟩⟩,
        rfl⟩
    intro w hw
    refine Subgroup.closure_mono hsub ?_
    have hn : ¬ (c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0) := hz
    by_cases h0 : c₀ = 0
    · by_cases h1 : c₁ = 0
      · have h2 : c₂ ≠ 0 := fun h2 => hn ⟨h0, h1, h2⟩
        exact e7_stab_e1_le h2 hw.2
      · exact e7_stab_e1_le h1 hw.1.2
    · exact e7_stab_e1_le h0 hw.1.1

theorem exists_conj_fix_e7_triple {z₀ z₁ z₂ : Fin Tag.E7.rank → ZMod 7}
    (h7 : 7 ∣ Nat.card ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓ dualWeylStabilizer z₂)) :
    ∃ (a : WeylGroup Tag.E7) (z₀' z₁' z₂' : Fin Tag.E7.rank → ZMod 7),
      (∀ y, charVal z₀' (a • y) = charVal z₀ y) ∧ (∀ y, charVal z₁' (a • y) = charVal z₁ y) ∧
      (∀ y, charVal z₂' (a • y) = charVal z₂ y) ∧
      e7G0 ∈ dualWeylStabilizer z₀' ∧ e7G0 ∈ dualWeylStabilizer z₁' ∧
      e7G0 ∈ dualWeylStabilizer z₂' := by
  obtain ⟨x, hx⟩ := exists_conj_e7G0_mem h7
  obtain ⟨z₀', h₀, g₀⟩ := exists_conj_col_e7 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1
  obtain ⟨z₁', h₁, g₁⟩ := exists_conj_col_e7 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2
  obtain ⟨z₂', h₂, g₂⟩ := exists_conj_col_e7 (Subgroup.mem_inf.1 hx).2
  exact ⟨x⁻¹, z₀', z₁', z₂', h₀, h₁, h₂, g₀, g₁, g₂⟩

theorem e7_inf3_le_closure_of_conj
    {a : WeylGroup Tag.E7} {z₀ z₁ z₂ z₀' z₁' z₂' : Fin Tag.E7.rank → ZMod 7}
    (h₀ : ∀ y, charVal z₀' (a • y) = charVal z₀ y) (h₁ : ∀ y, charVal z₁' (a • y) = charVal z₁ y)
    (h₂ : ∀ y, charVal z₂' (a • y) = charVal z₂ y)
    (h : dualWeylStabilizer z₀' ⊓ dualWeylStabilizer z₁' ⊓ dualWeylStabilizer z₂' ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀' ∩ rootKernel z₁' ∩ rootKernel z₂',
        s = rootReflection α}) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓ dualWeylStabilizer z₂ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁ ∩ rootKernel z₂,
        s = rootReflection α} := by
  intro y hy
  have hy' : a * y * a⁻¹ ∈
      dualWeylStabilizer z₀' ⊓ dualWeylStabilizer z₁' ⊓ dualWeylStabilizer z₂' :=
    ⟨⟨(e7_mem_dualStab_conj h₀ y).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).1).1,
      (e7_mem_dualStab_conj h₁ y).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).1).2⟩,
      (e7_mem_dualStab_conj h₂ y).1 (Subgroup.mem_inf.1 hy).2⟩
  have hle : Subgroup.closure
      {s | ∃ β ∈ rootKernel z₀' ∩ rootKernel z₁' ∩ rootKernel z₂', s = rootReflection β} ≤
      (Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁ ∩ rootKernel z₂,
        s = rootReflection α}).comap (MulAut.conj a⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨β, ⟨⟨hβ₀, hβ₁⟩, hβ₂⟩, rfl⟩
    have hα : IsRoot Tag.E7 (a⁻¹ • β) := IsRoot.smul hβ₀.1 a⁻¹
    have hk₀ : charVal z₀ (a⁻¹ • β) = 0 := by rw [← h₀, smul_inv_smul]; exact hβ₀.2
    have hk₁ : charVal z₁ (a⁻¹ • β) = 0 := by rw [← h₁, smul_inv_smul]; exact hβ₁.2
    have hk₂ : charVal z₂ (a⁻¹ • β) = 0 := by rw [← h₂, smul_inv_smul]; exact hβ₂.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hconj : a⁻¹ * rootReflection β * a = rootReflection (a⁻¹ • β) := by
      rw [rootReflection_smul_root a⁻¹ hβ₀.1, inv_inv]
    rw [hconj]
    exact Subgroup.subset_closure ⟨a⁻¹ • β, ⟨⟨⟨hα, hk₀⟩, ⟨hα, hk₁⟩⟩, ⟨hα, hk₂⟩⟩, rfl⟩
  have h3 := hle (h hy')
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h3
  simpa [mul_assoc] using h3

theorem e7_inf3_dualWeylStabilizer_le_closure (z₀ z₁ z₂ : Fin Tag.E7.rank → ZMod 7) :
    dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓ dualWeylStabilizer z₂ ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z₀ ∩ rootKernel z₁ ∩ rootKernel z₂,
        s = rootReflection α} := by
  by_cases h7 : 7 ∣ Nat.card ↥(dualWeylStabilizer z₀ ⊓ dualWeylStabilizer z₁ ⊓
      dualWeylStabilizer z₂)
  · obtain ⟨a, z₀', z₁', z₂', h₀, h₁, h₂, g₀, g₁, g₂⟩ := exists_conj_fix_e7_triple h7
    exact e7_inf3_le_closure_of_conj h₀ h₁ h₂ (e7_inf3_le_closure_of_fix g₀ g₁ g₂)
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact inf3_dualWeylStabilizer_le_closure_of_card z₀ z₁ z₂ h7

open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley in
theorem e7SevenCubeWeyl_holds (L : Type) [Field L] (a : Fin 3 → Fin Tag.E7.rank → Lˣ)
    (ha : ∀ (s : Fin 3) (i : Fin Tag.E7.rank), a s i ^ 7 = 1) (y : WeylGroup Tag.E7)
    (hy : ∀ (s : Fin 3) (v : Fin Tag.E7.rank → ℤ), rootChar (a s) (y • v) = rootChar (a s) v) :
    y ∈ Subgroup.closure ((fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a) := by
  by_cases hall : ∀ (s : Fin 3) (i : Fin Tag.E7.rank), a s i = 1
  · have hone : ∀ (s : Fin 3) (α : Fin Tag.E7.rank → ℤ), rootChar (a s) α = 1 := fun s α => by
      simp [rootChar, hall s]
    have htop : (⊤ : Subgroup (WeylGroup Tag.E7)) ≤
        Subgroup.closure ((fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a) := by
      rw [← closure_rootReflection_eq_top (τ := Tag.E7)]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨α, ⟨hα, fun s => hone s α⟩, rfl⟩
    exact htop (Subgroup.mem_top y)
  · push Not at hall
    obtain ⟨s₀, i₀, hne⟩ := hall
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hζ : orderOf (a s₀ i₀) = 7 := orderOf_eq_prime (ha s₀ i₀) hne
    have hexp : ∀ (s : Fin 3) (i : Fin Tag.E7.rank), ∃ n : ℕ, a s i = (a s₀ i₀) ^ n :=
      fun s i => exists_pow_eq_of_pow_seven hζ (ha s i)
    choose e he using hexp
    set z : Fin 3 → Fin Tag.E7.rank → ZMod 7 := fun s i => (e s i : ZMod 7) with hz
    have hchar : ∀ (s : Fin 3) (l l' : Fin Tag.E7.rank → ℤ),
        rootChar (a s) l = rootChar (a s) l' ↔ charVal (z s) l = charVal (z s) l' :=
      fun s l l' => rootChar_eq_rootChar_iff hζ (e s) (a s) (he s) l l'
    have hyU : y ∈ dualWeylStabilizer (z 0) ⊓ dualWeylStabilizer (z 1) ⊓
        dualWeylStabilizer (z 2) :=
      ⟨⟨fun x => (hchar 0 _ _).1 (hy 0 x), fun x => (hchar 1 _ _).1 (hy 1 x)⟩,
        fun x => (hchar 2 _ _).1 (hy 2 x)⟩
    have hmain := e7_inf3_dualWeylStabilizer_le_closure (z 0) (z 1) (z 2) hyU
    have h0 : ∀ s (α : Fin Tag.E7.rank → ℤ), rootChar (a s) α = 1 ↔ charVal (z s) α = 0 :=
      fun s α => by
        have h := hchar s α 0
        rw [rootChar_zero] at h
        have h00 : charVal (z s) (0 : Fin Tag.E7.rank → ℤ) = 0 := by simp [charVal]
        rw [h00] at h
        exact h
    have hker : familyKernel (τ := Tag.E7) a =
        rootKernel (z 0) ∩ rootKernel (z 1) ∩ rootKernel (z 2) := by
      ext α
      constructor
      · rintro ⟨hα, hs⟩
        exact ⟨⟨⟨hα, (h0 0 α).1 (hs 0)⟩, ⟨hα, (h0 1 α).1 (hs 1)⟩⟩, ⟨hα, (h0 2 α).1 (hs 2)⟩⟩
      · rintro ⟨⟨⟨hα, h0'⟩, ⟨-, h1'⟩⟩, ⟨-, h2'⟩⟩
        refine ⟨hα, fun s => ?_⟩
        fin_cases s
        · exact (h0 0 α).2 h0'
        · exact (h0 1 α).2 h1'
        · exact (h0 2 α).2 h2'
    rw [hker]
    refine Subgroup.closure_mono ?_ hmain
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨α, hα, rfl⟩

end Sylow

section Generators

theorem exists_two_gen_of_card_sq' {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (F : Subgroup G) (hF : Nat.card F = p ^ 2) (hexp : ∀ x ∈ F, x ^ p = 1) :
    ∃ x1 ∈ F, ∃ x2 ∈ F, F = Subgroup.closure {x1, x2} := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero 2 hp.ne_zero)
  have hp12 : p < p ^ 2 := by nlinarith [hp.one_lt]
  obtain ⟨x1, hx1F, hx1⟩ : ∃ x ∈ F, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
    rw [hbot, Subgroup.card_bot] at hF
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hord : orderOf x1 = p := orderOf_eq_prime (hexp x1 hx1F) hx1
  haveI : Finite (Subgroup.zpowers x1) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hp.ne_zero)
  obtain ⟨x2, hx2F, hx2⟩ : ∃ x2 ∈ F, x2 ∉ Subgroup.zpowers x1 := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show F ≤ Subgroup.zpowers x1 from fun x hx => hcon x hx)
    rw [hF, Nat.card_zpowers, hord] at hle
    omega
  refine ⟨x1, hx1F, x2, hx2F, ?_⟩
  set C := Subgroup.closure ({x1, x2} : Set G) with hCdef
  have hCF : C ≤ F := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact hx1F
    · exact hx2F
  have hZC : Subgroup.zpowers x1 ≤ C :=
    (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inl rfl))
  have hx2C : x2 ∈ C := Subgroup.subset_closure (Or.inr rfl)
  have hlt : Subgroup.zpowers x1 < C := lt_of_le_of_ne hZC fun h => hx2 (h ▸ hx2C)
  haveI : Finite C := Finite.of_injective (Subgroup.inclusion hCF) (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, hord] at h1
  have h2 : Nat.card C ∣ p ^ 2 := hF ▸ Subgroup.card_dvd_of_le hCF
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow hp).1 h2
  rw [hkC] at h1
  have hk2 : k = 2 := by
    have hk1 : 1 < k := by
      have h1' : p ^ 1 < p ^ k := by rwa [pow_one]
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1'
    omega
  exact (Subgroup.eq_of_le_of_card_ge hCF (by rw [hF, hkC, hk2])).symm

theorem exists_three_gen_of_card_cube {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (E : Subgroup G) (hE : Nat.card E = p ^ 3) (hexp : ∀ x ∈ E, x ^ p = 1) :
    ∃ x1 ∈ E, ∃ x2 ∈ E, ∃ x3 ∈ E, E = Subgroup.closure {x1, x2, x3} := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hE]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := 2)
    (by rw [hE]; exact pow_dvd_pow p (by norm_num))
  set F : Subgroup G := F'.map E.subtype with hFdef
  have hFE : F ≤ E := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hFc : Nat.card F = p ^ 2 := by
    rw [hFdef, Subgroup.card_map_of_injective E.subtype_injective]
    exact hF'
  obtain ⟨x1, hx1, x2, hx2, hF⟩ :=
    exists_two_gen_of_card_sq' hp F hFc (fun x hx => hexp x (hFE hx))
  have hp23 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hFc]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨x3, hx3E, hx3F⟩ : ∃ x3 ∈ E, x3 ∉ F := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show E ≤ F from fun x hx => h x hx)
    rw [hE, hFc] at hle
    omega
  refine ⟨x1, hFE hx1, x2, hFE hx2, x3, hx3E, ?_⟩
  set C := Subgroup.closure ({x1, x2, x3} : Set G) with hCdef
  have hCE : C ≤ E := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl | rfl)
    · exact hFE hx1
    · exact hFE hx2
    · exact hx3E
  have hFC : F ≤ C := by
    rw [hF]
    refine Subgroup.closure_mono ?_
    rintro _ (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hx3C : x3 ∈ C := Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have hlt : F < C := lt_of_le_of_ne hFC fun h => hx3F (h ▸ hx3C)
  haveI : Finite C := Finite.of_injective (Subgroup.inclusion hCE) (Subgroup.inclusion_injective _)
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card C ∣ p ^ 3 := hE ▸ Subgroup.card_dvd_of_le hCE
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow hp).1 h2
  rw [hFc, hkC] at h1
  have hk3 : k = 3 := by
    have hk2 : 2 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
    omega
  exact (Subgroup.eq_of_le_of_card_ge hCE (by rw [hE, hkC, hk3])).symm

end Generators

section CubeBar

open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint

set_option linter.unusedSectionVars false

variable {τ : Tag}


theorem exists_conj_le_monomial_familyCentralizer_bar {L : Type} [Field L] [IsAlgClosed L]
    {ℓ p : ℕ} [Fact ℓ.Prime] [hp : Fact p.Prime] (hℓ : ℓ ≠ p) [CharP L ℓ]
    (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) {ι : Type} [Fintype ι]
    (a : ι → Fin τ.rank → Lˣ)
    {B : Subgroup (ModGL τ L)} (hB : B ≤ adjointGroup τ L) (hBfin : (B : Set (ModGL τ L)).Finite)
    (hBa : ∀ x ∈ B, ∀ i, rootDiagUnit τ (a i) * x = x * rootDiagUnit τ (a i))
    (hexp : ∀ x ∈ B, x ^ p = 1) :
    ∃ z ∈ adjointGroup τ L, (∀ i, rootDiagUnit τ (a i) * z = z * rootDiagUnit τ (a i)) ∧
      ∀ x ∈ B, z * x * z⁻¹ ∈ monomialSubgroup τ L := by
  classical
  set M := (Nat.card (WeylGroup τ)).factorization p + 1 with hM
  have hWM : ¬ p ^ M ∣ Nat.card (WeylGroup τ) :=
    Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp.out
  set E₀ : Finset L := Finset.univ.biUnion fun i : ι =>
    Finset.univ.image (fun j => (a i j : L)) ∪
      Finset.univ.image (fun j => ((a i j)⁻¹ : Lˣ) : Fin τ.rank → L) with hE₀
  obtain ⟨K₁, hK₁, hE₀K, hq, hdesc⟩ := exists_descent_subgroup hℓ halg hB hBfin E₀
    (by omega : 1 ≤ M)
  have hq3 : ¬ p ∣ Nat.card K₁ := not_dvd_of_modEq_pow hp.out (by omega) hq
  set ι' := K₁.subtype with hι'
  have ha1 : ∀ i j, (a i j : L) ∈ K₁ := fun i j =>
    hE₀K (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i,
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩))
  have ha2 : ∀ i j, (((a i j)⁻¹ : Lˣ) : L) ∈ K₁ := fun i j =>
    hE₀K (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i,
      Finset.mem_union_right _ (Finset.mem_image_of_mem
        (fun j => ((a i j)⁻¹ : Lˣ) : Fin τ.rank → L) (Finset.mem_univ j))⟩))
  let a' : ι → Fin τ.rank → K₁ˣ := fun i j =>
    ⟨⟨a i j, ha1 i j⟩, ⟨((a i j)⁻¹ : Lˣ), ha2 i j⟩, Subtype.ext (Units.mul_inv (a i j)),
      Subtype.ext (Units.inv_mul (a i j))⟩
  have ha' : ∀ i, (fun j => Units.map ι'.toMonoidHom (a' i j)) = a i := by
    intro i
    funext j
    exact Units.ext rfl
  have hda : ∀ i, baseChangeGL ι' (rootDiagUnit τ (a' i)) = rootDiagUnit τ (a i) := fun i => by
    rw [baseChangeGL_rootDiagUnit, ha' i]
  set B' := B.comap (baseChangeGL ι') with hB'
  have hB'C : B' ≤ familyCentralizer τ K₁ a' := by
    intro y hy
    refine mem_familyCentralizer.2 ⟨comap_le_adjointGroup ι' hdesc hy, fun i => ?_⟩
    apply baseChangeGL_injective ι'
    have h := hBa _ hy i
    rw [map_mul, map_mul, map_inv, hda, h, mul_inv_cancel_right]
  obtain ⟨u, hu, hun⟩ := exists_conj_le_monomial_of_isPGroup_family a' hq3 hq hWM hB'C
    (isPGroup_comap ι' hexp)
  obtain ⟨huC, hud⟩ := mem_familyCentralizer.1 hu
  refine ⟨baseChangeGL ι' u, CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι' huC,
    fun i => ?_, fun x hx => ?_⟩
  · have h := congrArg (baseChangeGL ι') (hud i)
    rw [map_mul, map_mul, map_inv, hda] at h
    calc rootDiagUnit τ (a i) * baseChangeGL ι' u =
          (rootDiagUnit τ (a i) * baseChangeGL ι' u * (rootDiagUnit τ (a i))⁻¹) *
            rootDiagUnit τ (a i) := by group
      _ = baseChangeGL ι' u * rootDiagUnit τ (a i) := by rw [h]
  · obtain ⟨y, -, rfl⟩ := hdesc x hx
    have h := baseChangeGL_mem_monomialSubgroup ι' (Subgroup.mem_inf.1 (hun y (by
      change baseChangeGL ι' y ∈ B
      exact hx))).2
    rwa [map_mul, map_mul, map_inv] at h

theorem exists_conj_mem_torusGroup_of_mem_monomial_familyCentralizer {p : ℕ}
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ p)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hstab : ∀ w : WeylGroup τ, (∀ i, w ∈ rootCharStabilizer (a i)) →
      w ∈ kernelWeylGroup (familyChar a))
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hna : ∀ i, rootDiagUnit τ (a i) * n = n * rootDiagUnit τ (a i)) (hp : n ^ p = 1) :
    ∃ g ∈ adjointGroup τ L, (∀ i, rootDiagUnit τ (a i) * g = g * rootDiagUnit τ (a i)) ∧
      g * n * g⁻¹ ∈ torusGroup τ L := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom τ L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul hk w hn
  have hw : ∀ i, w ∈ rootCharStabilizer (a i) := by
    intro i
    rw [← conj_canonicalRep_eq_iff]
    have hdk : rootDiagUnit τ (a i) * k = k * rootDiagUnit τ (a i) :=
      rootDiagUnit_mul_comm_of_mem_torusGroup (a i) hk
    have h1 : rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) L w =
        canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ (a i) := by
      have e1 : rootDiagUnit τ (a i) * canonicalRep (coxeterSystem τ) L w =
          k⁻¹ * (rootDiagUnit τ (a i) * (k * canonicalRep (coxeterSystem τ) L w)) := by
        rw [← mul_assoc (rootDiagUnit τ (a i)) k, hdk]
        group
      rw [e1, hna i]
      group
    rw [h1, mul_inv_cancel_right]
  have hwS : weylQuotientHom τ L ⟨_, hn⟩ ∈ kernelWeylGroup (familyChar a) := by
    rw [hπ]
    exact hstab w hw
  obtain ⟨g, hg, hgn⟩ := hmon L hL (ι → Lˣ) (familyChar a) _ hn hwS
    (weylQuotientHom_pow_eq_one hn hp)
  refine ⟨g, rootSpan_le_adjointGroup L _ hg, fun i => ?_, hgn⟩
  have hgc : g ∈ Subgroup.centralizer {rootDiagUnit τ (a i)} := by
    refine rootSpan_le_centralizer (a i) (S := kernelRoots (familyChar a)) (fun α hα => ?_) hg
    rw [kernelRoots_familyChar] at hα
    exact ⟨hα.1, hα.2 i⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm

theorem exists_conj_le_torusGroup_of_cube {p : ℕ} [hp : Fact p.Prime]
    (hmon : MonomialToralAt τ p) {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : ℓ ≠ p) [CharP L ℓ] (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    (hstab : ∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a)
    (hstab2 : ∀ a : Fin 2 → Fin τ.rank → Lˣ, (∀ s i, a s i ^ p = 1) →
      ∀ w : WeylGroup τ, (∀ s, w ∈ rootCharStabilizer (a s)) → w ∈ kernelWeylGroup (familyChar a))
    {A : Subgroup (ModGL τ L)} (hA : A ≤ adjointGroup τ L)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hexp : ∀ x ∈ A, x ^ p = 1)
    (hcard : Nat.card A = p ^ 3) :
    ∃ C ∈ adjointGroup τ L, ∀ x ∈ A, C * x * C⁻¹ ∈ torusGroup τ L := by
  classical
  have hLp : ringChar L ≠ p := by rw [ringChar.eq L ℓ]; exact hℓ
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.out.ne_zero)
  have hAfin : (A : Set (ModGL τ L)).Finite := Set.toFinite _
  obtain ⟨x₀, hx₀A, y₀, hy₀A, w₀, hw₀A, hgen⟩ := exists_three_gen_of_card_cube hp.out A hcard hexp
  have hexpDiag : ∀ (c : ModGL τ L) (x : ModGL τ L), x ∈ A → ∀ a : Fin τ.rank → Lˣ,
      c * x * c⁻¹ = rootDiagUnit τ a → ∀ i, a i ^ p = 1 := by
    intro c x hx a hca
    have h : rootDiagUnit τ (a ^ p) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, ← hca, conj_pow_eq_one' c (hexp x hx)]
    intro i
    have := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h) i
    simpa using this
  obtain ⟨c₁, hc₁, hc₁N⟩ := exists_conj_le_monomial_bar hℓ halg hA hAfin hexp
  obtain ⟨g, hg, hgn⟩ := exists_conj_mem_torusGroup_of_mem_monomial hmon hLp (hc₁N x₀ hx₀A)
    (conj_pow_eq_one' c₁ (hexp x₀ hx₀A))
  set c := g * c₁ with hcdef
  have hcC : c ∈ adjointGroup τ L := mul_mem hg hc₁
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgn
  have hda : c * x₀ * c⁻¹ = rootDiagUnit τ a := by
    rw [← ha, hcdef]
    group
  have hap : ∀ i, a i ^ p = 1 := hexpDiag c x₀ hx₀A a hda
  have hcommConj : ∀ (C : ModGL τ L) (x₁ : ModGL τ L), x₁ ∈ A → ∀ x ∈ A,
      (C * x₁ * C⁻¹) * (C * x * C⁻¹) = (C * x * C⁻¹) * (C * x₁ * C⁻¹) := by
    intro C x₁ hx₁ x hx
    calc (C * x₁ * C⁻¹) * (C * x * C⁻¹) = C * (x₁ * x) * C⁻¹ := by group
      _ = C * (x * x₁) * C⁻¹ := by rw [hcomm x₁ hx₁ x hx]
      _ = (C * x * C⁻¹) * (C * x₁ * C⁻¹) := by group
  set A' := A.map (MulAut.conj c).toMonoidHom with hA'
  have hA'C : A' ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hcC (hA hx)) (inv_mem hcC)
  have hA'fin : (A' : Set (ModGL τ L)).Finite := Set.Finite.image _ hAfin
  have hA'a : ∀ y ∈ A', rootDiagUnit τ a * y = y * rootDiagUnit τ a := by
    rintro _ ⟨x, hx, rfl⟩
    change rootDiagUnit τ a * (c * x * c⁻¹) = c * x * c⁻¹ * rootDiagUnit τ a
    rw [← hda]
    exact hcommConj c x₀ hx₀A x hx
  have hA'exp : ∀ y ∈ A', y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c (hexp x hx)
  obtain ⟨z, hz, hzd, hzN⟩ := exists_conj_le_monomial_centralizer_bar hℓ halg a hA'C hA'fin
    hA'a hA'exp
  set n' := z * (c * y₀ * c⁻¹) * z⁻¹ with hn'
  have hn'N : n' ∈ monomialSubgroup τ L := hzN _ ⟨y₀, hy₀A, rfl⟩
  have hzd' : rootDiagUnit τ a * z⁻¹ = z⁻¹ * rootDiagUnit τ a := by
    calc rootDiagUnit τ a * z⁻¹ = z⁻¹ * (z * rootDiagUnit τ a) * z⁻¹ := by group
      _ = z⁻¹ * (rootDiagUnit τ a * z) * z⁻¹ := by rw [hzd]
      _ = z⁻¹ * rootDiagUnit τ a := by group
  have hn'a : rootDiagUnit τ a * n' = n' * rootDiagUnit τ a := by
    have h1 : rootDiagUnit τ a * (c * y₀ * c⁻¹) = c * y₀ * c⁻¹ * rootDiagUnit τ a :=
      hA'a _ ⟨y₀, hy₀A, rfl⟩
    calc rootDiagUnit τ a * n' = (rootDiagUnit τ a * z) * (c * y₀ * c⁻¹) * z⁻¹ := by
          rw [hn']; group
      _ = z * (rootDiagUnit τ a * (c * y₀ * c⁻¹)) * z⁻¹ := by rw [hzd]; group
      _ = z * (c * y₀ * c⁻¹) * (rootDiagUnit τ a * z⁻¹) := by rw [h1]; group
      _ = n' * rootDiagUnit τ a := by rw [hzd', hn']; group
  have hn'p : n' ^ p = 1 := conj_pow_eq_one' z (hA'exp _ ⟨y₀, hy₀A, rfl⟩)
  obtain ⟨g', hg', hg'd, hg'n⟩ := exists_conj_mem_torusGroup_of_mem_monomial_centralizer hmon
    hLp (hstab a hap) hn'N hn'a hn'p
  set c₂ := g' * z * c with hc₂def
  have hc₂C : c₂ ∈ adjointGroup τ L := mul_mem (mul_mem hg' hz) hcC
  have hzdc : z * rootDiagUnit τ a * z⁻¹ = rootDiagUnit τ a := by
    rw [← hzd, mul_inv_cancel_right]
  have hg'dc : g' * rootDiagUnit τ a * g'⁻¹ = rootDiagUnit τ a := by
    rw [← hg'd, mul_inv_cancel_right]
  have hx₀c₂ : c₂ * x₀ * c₂⁻¹ = rootDiagUnit τ a := by
    have e : c₂ * x₀ * c₂⁻¹ = g' * (z * (c * x₀ * c⁻¹) * z⁻¹) * g'⁻¹ := by
      rw [hc₂def]
      group
    rw [e, hda, hzdc, hg'dc]
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg'n
  have hy₀c₂ : c₂ * y₀ * c₂⁻¹ = rootDiagUnit τ b := by
    rw [← hb, hc₂def, hn']
    group
  have hbp : ∀ i, b i ^ p = 1 := hexpDiag c₂ y₀ hy₀A b hy₀c₂
  let a2 : Fin 2 → Fin τ.rank → Lˣ := ![a, b]
  let gens : Fin 2 → ModGL τ L := ![x₀, y₀]
  have ha2 : ∀ s, c₂ * gens s * c₂⁻¹ = rootDiagUnit τ (a2 s) := by
    intro s
    fin_cases s
    · exact hx₀c₂
    · exact hy₀c₂
  have ha2mem : ∀ s, gens s ∈ A := by
    intro s
    fin_cases s
    · exact hx₀A
    · exact hy₀A
  set A'' := A.map (MulAut.conj c₂).toMonoidHom with hA''
  have hA''C : A'' ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hc₂C (hA hx)) (inv_mem hc₂C)
  have hA''fin : (A'' : Set (ModGL τ L)).Finite := Set.Finite.image _ hAfin
  have hA''a : ∀ y ∈ A'', ∀ s, rootDiagUnit τ (a2 s) * y = y * rootDiagUnit τ (a2 s) := by
    rintro _ ⟨x, hx, rfl⟩ s
    change rootDiagUnit τ (a2 s) * (c₂ * x * c₂⁻¹) = c₂ * x * c₂⁻¹ * rootDiagUnit τ (a2 s)
    rw [← ha2 s]
    exact hcommConj c₂ _ (ha2mem s) x hx
  have hA''exp : ∀ y ∈ A'', y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_pow_eq_one' c₂ (hexp x hx)
  obtain ⟨z₂, hz₂, hz₂d, hz₂N⟩ := exists_conj_le_monomial_familyCentralizer_bar hℓ halg a2
    hA''C hA''fin hA''a hA''exp
  set n'' := z₂ * (c₂ * w₀ * c₂⁻¹) * z₂⁻¹ with hn''
  have hn''N : n'' ∈ monomialSubgroup τ L := hz₂N _ ⟨w₀, hw₀A, rfl⟩
  have hz₂d' : ∀ s, rootDiagUnit τ (a2 s) * z₂⁻¹ = z₂⁻¹ * rootDiagUnit τ (a2 s) := by
    intro s
    calc rootDiagUnit τ (a2 s) * z₂⁻¹ = z₂⁻¹ * (z₂ * rootDiagUnit τ (a2 s)) * z₂⁻¹ := by group
      _ = z₂⁻¹ * (rootDiagUnit τ (a2 s) * z₂) * z₂⁻¹ := by rw [hz₂d s]
      _ = z₂⁻¹ * rootDiagUnit τ (a2 s) := by group
  have hn''a : ∀ s, rootDiagUnit τ (a2 s) * n'' = n'' * rootDiagUnit τ (a2 s) := by
    intro s
    have h1 : rootDiagUnit τ (a2 s) * (c₂ * w₀ * c₂⁻¹) = c₂ * w₀ * c₂⁻¹ * rootDiagUnit τ (a2 s) :=
      hA''a _ ⟨w₀, hw₀A, rfl⟩ s
    calc rootDiagUnit τ (a2 s) * n'' =
          (rootDiagUnit τ (a2 s) * z₂) * (c₂ * w₀ * c₂⁻¹) * z₂⁻¹ := by rw [hn'']; group
      _ = z₂ * (rootDiagUnit τ (a2 s) * (c₂ * w₀ * c₂⁻¹)) * z₂⁻¹ := by rw [hz₂d s]; group
      _ = z₂ * (c₂ * w₀ * c₂⁻¹) * (rootDiagUnit τ (a2 s) * z₂⁻¹) := by rw [h1]; group
      _ = n'' * rootDiagUnit τ (a2 s) := by rw [hz₂d' s, hn'']; group
  have hn''p : n'' ^ p = 1 := conj_pow_eq_one' z₂ (hA''exp _ ⟨w₀, hw₀A, rfl⟩)
  have ha2p : ∀ s i, a2 s i ^ p = 1 := by
    intro s
    fin_cases s
    · exact hap
    · exact hbp
  obtain ⟨g'', hg'', hg''d, hg''n⟩ := exists_conj_mem_torusGroup_of_mem_monomial_familyCentralizer
    hmon hLp (hstab2 a2 ha2p) hn''N hn''a hn''p
  set C := g'' * z₂ * c₂ with hCdef
  have hCC : C ∈ adjointGroup τ L := mul_mem (mul_mem hg'' hz₂) hc₂C
  refine ⟨C, hCC, ?_⟩
  have hfix2 : ∀ s, C * gens s * C⁻¹ = rootDiagUnit τ (a2 s) := by
    intro s
    have e : C * gens s * C⁻¹ = g'' * (z₂ * (c₂ * gens s * c₂⁻¹) * z₂⁻¹) * g''⁻¹ := by
      rw [hCdef]
      group
    have hz₂c : z₂ * rootDiagUnit τ (a2 s) * z₂⁻¹ = rootDiagUnit τ (a2 s) := by
      rw [← hz₂d s, mul_inv_cancel_right]
    have hg''c : g'' * rootDiagUnit τ (a2 s) * g''⁻¹ = rootDiagUnit τ (a2 s) := by
      rw [← hg''d s, mul_inv_cancel_right]
    rw [e, ha2 s, hz₂c, hg''c]
  set S := A ⊓ (torusGroup τ L).comap (MulAut.conj C).toMonoidHom with hS
  have hx₀S : x₀ ∈ S := by
    refine ⟨hx₀A, ?_⟩
    change C * x₀ * C⁻¹ ∈ torusGroup τ L
    have h0 : C * x₀ * C⁻¹ = rootDiagUnit τ (a2 0) := hfix2 0
    rw [h0]
    exact rootDiagUnit_mem_torusGroup _
  have hy₀S : y₀ ∈ S := by
    refine ⟨hy₀A, ?_⟩
    change C * y₀ * C⁻¹ ∈ torusGroup τ L
    have h1 : C * y₀ * C⁻¹ = rootDiagUnit τ (a2 1) := hfix2 1
    rw [h1]
    exact rootDiagUnit_mem_torusGroup _
  have hw₀S : w₀ ∈ S := by
    refine ⟨hw₀A, ?_⟩
    change C * w₀ * C⁻¹ ∈ torusGroup τ L
    have e : C * w₀ * C⁻¹ = g'' * n'' * g''⁻¹ := by
      rw [hCdef, hn'']
      group
    rw [e]
    exact hg''n
  have hAS : A ≤ S := by
    rw [hgen]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl | rfl)
    · exact hx₀S
    · exact hy₀S
    · exact hw₀S
  intro x hx
  exact (hAS hx).2

end CubeBar

section E7CubeBar

open CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false

variable {τ : Tag}


variable (τ) in
@[expose] def CubesToralBar (p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ p ∣ Nat.card K →
    ∀ A : Subgroup (ModGL τ (AlgebraicClosure K)), A ≤ adjointGroup τ (AlgebraicClosure K) →
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ p = 1) → Nat.card A = p ^ 3 →
      ∃ g ∈ adjointGroup τ (AlgebraicClosure K), ∀ x ∈ A,
        g⁻¹ * x * g ∈ torusGroup τ (AlgebraicClosure K)

theorem closure_rootReflection_familyKernel_le {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) :
    Subgroup.closure ((fun α => rootReflection α) '' familyKernel (τ := τ) a) ≤
      kernelWeylGroup (familyChar a) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨u, j, huj⟩ := isRoot_iff_exists_smul_single.1 hα.1
  change rootReflection α ∈ kernelWeylGroup (familyChar a)
  rw [rootReflection_eq_conj huj]
  refine Subgroup.subset_closure ⟨u, j, ?_, rfl⟩
  rw [huj, kernelRoots_familyChar]
  exact hα

theorem cubesToralBar_E7_seven : CubesToralBar Tag.E7 7 := by
  intro K _ _ hpK A hA hcomm hexp hcard
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ : ℓ ≠ 7 := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 7
    apply hpK
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 7 n.ne_zero
  have hmon : MonomialToralAt Tag.E7 7 :=
    monomialToralAt_seven_of_chainBlock (fun _ hγ => iform_self_E7 hγ)
      (chainBlockToral_E7_six_of_transitive a6ChainTransitive_E7)
  obtain ⟨C, hC, hCA⟩ := exists_conj_le_torusGroup_of_cube hmon hℓ
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ)
    (fun a ha => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven a ha).le)
    (fun a ha w hw => closure_rootReflection_familyKernel_le a
      (e7SevenPlaneWeyl_holds (AlgebraicClosure K) a ha w hw))
    hA hcomm hexp hcard
  refine ⟨C⁻¹, inv_mem hC, fun x hx => ?_⟩
  rw [inv_inv]
  exact hCA x hx

variable (τ) in
@[expose] def LangToralCube (p : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ¬ p ∣ Nat.card K →
    ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (∀ x ∈ A, x ^ p = 1) → Nat.card A = p ^ 3 →
      ∃ w : WeylGroup τ, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ Nat.card K) ∧
        ∃ g0 ∈ adjointGroup τ (AlgebraicClosure K),
          Units.map (entrywiseHom Fr) g0 =
            g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
          ∃ c : adjointGroup τ K, ∀ x ∈ A,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom

theorem langToralCube_of_bar {p : ℕ} (hp : p.Prime) (hbar : CubesToralBar τ p) :
    LangToralCube τ p := by
  intro K _ _ hpK A hAcomm hAp hAcard
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have he : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hpq : Nat.Coprime p (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (hq ▸ hpK)
  set ι : K →+* L := algebraMap K L with hι
  set φ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype with hφ
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective ι).comp Subtype.val_injective
  set AL : Subgroup (ModGL τ L) := A.map φ with hAL
  have hAL_le : AL ≤ adjointGroup τ L := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι x.2
  have hALp : ∀ y ∈ AL, y ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hAp x hx, map_one]
  have hALcard : Nat.card AL = p ^ 3 := by
    rw [hAL, ← Nat.card_congr (Subgroup.equivMapOfInjective A φ hφinj).toEquiv]
    exact hAcard
  have hALcomm : ∀ x ∈ AL, ∀ y ∈ AL, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hAcomm x hx y hy]
  obtain ⟨g, hgG, hg⟩ := hbar K hpK AL hAL_le hALcomm hALp hALcard
  have hT : ∀ x : A, g⁻¹ * φ x * g ∈ torusGroup τ L := fun x => hg _ ⟨x, x.2, rfl⟩
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hT x)
  have hexp : ∀ (x : A) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ 1 := by
      have : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ (a x) ^ p :=
        ((rootDiagUnitHom τ L).map_pow (a x) p)
      rw [this, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * φ x * g) ^ p = g⁻¹ * (φ x) ^ p * g := by
            have := conj_pow (a := g⁻¹) (b := φ x) (i := p)
            rwa [inv_inv] at this
        _ = 1 := by
            rw [← map_pow, hAp x x.2, map_one]
            group
    have h2 : a x ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι y) = baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hFix' : ∀ x : A, entrywiseFrobGL τ L ℓ (f : ℕ) (φ x) = φ x := fun x => hFix (x : ModGL τ K)
  have hn : ∀ x : A, (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g) *
      entrywiseFrobGL τ L ℓ (f : ℕ) (rootDiagUnit τ (a x)) *
      (g⁻¹ * entrywiseFrobGL τ L ℓ (f : ℕ) g)⁻¹ = rootDiagUnit τ (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix' x]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane ℓ (f : ℕ) he hpq a hexp hgG hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL τ L ℓ (f : ℕ) (g * z) =
      (g * z) * canonicalRep (coxeterSystem τ) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨w', iterateFrobenius L ℓ (f : ℕ), fun c => ?_, g * z, mul_mem hgG hzG, hu, 1, ?_⟩
  · rw [iterateFrobenius_def, hq]
  · intro x hx
    set xA : A := ⟨x, hx⟩ with hxA
    set d := rootDiagUnit τ (a xA) with hd
    have hzd : z⁻¹ * d * z = d := by
      have := hzcomm xA
      rw [← hd, mul_inv_eq_iff_eq_mul] at this
      calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
        _ = z⁻¹ * (z * d) := by rw [this]
        _ = d := by group
    have ht : (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z) = d := by
      have h0 : φ xA = baseChangeGL ι (x : ModGL τ K) := rfl
      calc (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z)
          = z⁻¹ * (g⁻¹ * φ xA * g) * z := by rw [h0]; group
        _ = d := by rw [ha xA, hzd]
    refine ⟨(g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_twistedTorusOf, ht]
      refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      have hfx : entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι (x : ModGL τ K)) =
          baseChangeGL ι (x : ModGL τ K) := hFix _
      have hFd : entrywiseFrobGL τ L ℓ (f : ℕ) d =
          (canonicalRep (coxeterSystem τ) L w')⁻¹ * d * canonicalRep (coxeterSystem τ) L w' := by
        rw [← ht, map_mul, map_mul, map_inv, hfx, hu]
        group
      change canonicalRep (coxeterSystem τ) L w' * entrywiseFrobGL τ L ℓ (f : ℕ) d *
        (canonicalRep (coxeterSystem τ) L w')⁻¹ = d
      rw [hFd]
      group
    · change (g * z) * ((g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z)) * (g * z)⁻¹ =
        baseChangeGL ι ((1 * x * 1⁻¹ : ↥(adjointGroup τ K)) : ModGL τ K)
      simp only [one_mul, inv_one, mul_one]
      group

end E7CubeBar

section E7SevenDescent

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Open
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem image_neg_familyKernel' {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin Tag.E7.rank → L ˣ) {w0 : WeylGroup Tag.E7}
    (hw0 : ∀ u : Fin Tag.E7.rank → ℤ, w0 • u = -u) :
    (fun α => w0 • α) '' familyKernel (τ := Tag.E7) a = familyKernel (τ := Tag.E7) a := by
  have hneg : ∀ β ∈ familyKernel (τ := Tag.E7) a, -β ∈ familyKernel (τ := Tag.E7) a :=
    fun β hβ => ⟨IsRoot.neg hβ.1, fun i => by rw [rootChar_neg_eq_inv, hβ.2 i, inv_one]⟩
  ext β
  constructor
  · rintro ⟨α, hα, rfl⟩
    dsimp only
    rw [hw0 α]
    exact hneg α hα
  · intro hβ
    refine ⟨-β, hneg β hβ, ?_⟩
    dsimp only
    rw [hw0 (-β), neg_neg]

theorem e7_conj_into_frame_seven_cube {K : Type} [Field K] [Finite K] (hpq : 7 ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup Tag.E7 K)) (hE₀ : IsElemAbelian 7 E₀)
    (hE₀c : Nat.card E₀ = 7 ^ 3) :
    ∃ g : adjointGroup Tag.E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K := by
  obtain ⟨w0, hw0, hframe⟩ := e7SevenFrameDatum_holds
  have hE₀p := hE₀.2
  have hE₀comm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpK : ¬ 7 ∣ Nat.card K := fun h => by
    have h1 : 7 ∣ 1 := (Nat.dvd_add_right h).1 hpq
    norm_num at h1
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ :=
    (langToralCube_of_bar Nat.prime_seven cubesToralBar_E7_seven) K hpK E₀ hE₀comm hE₀p hE₀c
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  subst hfr
  have hq7 : 7 ∣ ringChar K ^ (f : ℕ) + 1 := hq ▸ hpq
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  obtain ⟨x1, hx1, x2, hx2, x3, hx3, hgenE⟩ :=
    exists_three_gen_of_card_cube Nat.prime_seven E₀ hE₀c hE₀p
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  let Φ : ModGL Tag.E7 (AlgebraicClosure K) →* ModGL Tag.E7 (AlgebraicClosure K) :=
    entrywiseFrobGL Tag.E7 (AlgebraicClosure K) (ringChar K) (f : ℕ)
  let bb : adjointGroup Tag.E7 K → ModGL Tag.E7 (AlgebraicClosure K) := fun x =>
    baseChangeGL ι ((c * x * c⁻¹ : adjointGroup Tag.E7 K) : ModGL Tag.E7 K)
  let ψ : adjointGroup Tag.E7 K →* ModGL Tag.E7 (AlgebraicClosure K) :=
    (MulAut.conj g0⁻¹).toMonoidHom.comp ((baseChangeGL ι).comp
      ((adjointGroup Tag.E7 K).subtype.comp (MulAut.conj c).toMonoidHom))
  have hψ : ∀ x, ψ x = g0⁻¹ * bb x * g0 := fun x => by
    show g0⁻¹ * bb x * g0⁻¹⁻¹ = g0⁻¹ * bb x * g0
    rw [inv_inv]
  let Tw : Subgroup (ModGL Tag.E7 (AlgebraicClosure K)) :=
    twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w) Φ
  have hψT : ∀ x ∈ E₀, ψ x ∈ Tw := by
    intro x hx
    obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (hc x hx)
    have htb' : g0 * t * g0⁻¹ = bb x := htb
    have : ψ x = t := by
      rw [hψ, ← htb']
      group
    rw [this]
    exact ht
  have h7 : ∀ x ∈ E₀, ψ x ^ 7 = 1 := fun x hx => by
    rw [← map_pow, hE₀p x hx, map_one]
  have hSS : E₀.map ψ = Subgroup.closure {ψ x1, ψ x2, ψ x3} := by
    conv_lhs => rw [hgenE]
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_pair]
  have htor1 : ψ x1 ∈ torusGroup Tag.E7 (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 (hψT x1 hx1)).1
  have htor2 : ψ x2 ∈ torusGroup Tag.E7 (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 (hψT x2 hx2)).1
  have htor3 : ψ x3 ∈ torusGroup Tag.E7 (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 (hψT x3 hx3)).1
  obtain ⟨a1, ha1⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htor1
  obtain ⟨a2, ha2⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htor2
  obtain ⟨a3, ha3⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup htor3
  have hfix1 := (mem_twistedTorusOf.1 (hψT x1 hx1)).2
  have hfix2 := (mem_twistedTorusOf.1 (hψT x2 hx2)).2
  have hfix3 := (mem_twistedTorusOf.1 (hψT x3 hx3)).2
  rw [ha1] at hfix1
  rw [ha2] at hfix2
  rw [ha3] at hfix3
  let a : Fin 3 → Fin Tag.E7.rank → (AlgebraicClosure K)ˣ := ![a1, a2, a3]
  have ha_exp : ∀ (s : Fin 3) (i : Fin Tag.E7.rank), a s i ^ 7 = 1 := by
    intro s
    fin_cases s
    · exact exp_seven_of_rootDiagUnit a1 (by rw [← ha1]; exact h7 x1 hx1)
    · exact exp_seven_of_rootDiagUnit a2 (by rw [← ha2]; exact h7 x2 hx2)
    · exact exp_seven_of_rootDiagUnit a3 (by rw [← ha3]; exact h7 x3 hx3)
  have hyfix : ∀ (s : Fin 3) (v : Fin Tag.E7.rank → ℤ),
      rootChar (a s) ((w0⁻¹ * w) • v) = rootChar (a s) v := by
    intro s v
    fin_cases s
    · exact rootChar_y_fix (ringChar K) (f : ℕ) hw0 (fun i => ha_exp 0 i) hq7 hfix1 v
    · exact rootChar_y_fix (ringChar K) (f : ℕ) hw0 (fun i => ha_exp 1 i) hq7 hfix2 v
    · exact rootChar_y_fix (ringChar K) (f : ℕ) hw0 (fun i => ha_exp 2 i) hq7 hfix3 v
  have hy_mem : canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) (w0⁻¹ * w) ∈
      familyGroup (τ := Tag.E7) (K := AlgebraicClosure K) a :=
    CFSG.LocalAnalysis.RankFourTheoremC.ExcRank.canonicalRep_mem_familyGroup_of_closure a
      (e7SevenCubeWeyl_holds (AlgebraicClosure K) a ha_exp (w0⁻¹ * w) hyfix)
  have hw0img := image_neg_familyKernel' (L := AlgebraicClosure K) a hw0
  have hfix0 : entrywiseFrobGL Tag.E7 (AlgebraicClosure K) (ringChar K) (f : ℕ) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w := hg0
  obtain ⟨z, hz, hzF⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.ExcRank.exists_datum_change (ringChar K) (f : ℕ) hf1 a w
      w0 g0 hfix0 hw0img hy_mem
  have hzC := mem_familyCentralizer.1
    (familyGroup_le_familyCentralizer (K := AlgebraicClosure K) a hz)
  have hzG : z ∈ adjointGroup Tag.E7 (AlgebraicClosure K) := hzC.1
  have hz1 : z * ψ x1 = ψ x1 * z := comm_of_conj_eq (by
    rw [ha1]
    exact hzC.2 0)
  have hz2 : z * ψ x2 = ψ x2 * z := comm_of_conj_eq (by
    rw [ha2]
    exact hzC.2 1)
  have hz3 : z * ψ x3 = ψ x3 * z := comm_of_conj_eq (by
    rw [ha3]
    exact hzC.2 2)
  have hzS : ∀ t ∈ E₀.map ψ, z * t = t * z := by
    intro t ht
    have hle : Subgroup.closure ({ψ x1, ψ x2, ψ x3} : Set (ModGL Tag.E7 (AlgebraicClosure K))) ≤
        Subgroup.centralizer ({z} : Set (ModGL Tag.E7 (AlgebraicClosure K))) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro t' (rfl | rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hz1
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hz2
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hz3
    rw [hSS] at ht
    have := hle ht
    rw [Subgroup.mem_centralizer_iff] at this
    exact this z (Set.mem_singleton z)
  let Tw0 : Subgroup (ModGL Tag.E7 (AlgebraicClosure K)) :=
    twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0) Φ
  have hnewT : ∀ x ∈ E₀, (g0 * z)⁻¹ * bb x * (g0 * z) ∈ Tw0 := by
    intro x hx
    have hcomm := hzS (ψ x) (Subgroup.mem_map_of_mem ψ hx)
    have hb : bb x = g0 * ψ x * g0⁻¹ := by
      rw [hψ]
      group
    have key : (g0 * z)⁻¹ * bb x * (g0 * z) = ψ x := by
      rw [hb]
      calc (g0 * z)⁻¹ * (g0 * ψ x * g0⁻¹) * (g0 * z) = z⁻¹ * ψ x * z := by group
        _ = z⁻¹ * (ψ x * z) := by group
        _ = z⁻¹ * (z * ψ x) := by rw [hcomm]
        _ = ψ x := by group
    rw [key]
    have hT := mem_twistedTorusOf.1 (hψT x hx)
    obtain ⟨b, hb'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT.1
    have hb7 : ∀ i, b i ^ 7 = 1 :=
      exp_seven_of_rootDiagUnit b (by rw [← hb']; exact h7 x hx)
    rw [mem_twistedTorusOf]
    refine ⟨hT.1, ?_⟩
    rw [hb']
    exact twisted_w0_fix (ringChar K) (f : ℕ) hw0 hq7 hb7
  have hg'mem : g0 * z ∈ adjointGroup Tag.E7 (AlgebraicClosure K) := mul_mem hg0C hzG
  have hg'eq : Units.map
      (entrywiseHom (iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ))) (g0 * z) =
      g0 * z * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) w0 := hzF
  obtain ⟨gf, hgfmem, hgfeq, hgfframe⟩ := hframe K hpq _ hFr
  let A : Subgroup (adjointGroup Tag.E7 K) := E₀.map (MulAut.conj c).toMonoidHom
  have hA7 : ∀ x ∈ A, x ^ 7 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    show (c * y * c⁻¹) ^ 7 = 1
    rw [conj_pow, hE₀p y hy, mul_one, mul_inv_cancel]
  have hAT : ∀ x ∈ A, baseChangeGL ι (x : ModGL Tag.E7 K) ∈
      Tw0.map (MulAut.conj (g0 * z)).toMonoidHom := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(g0 * z)⁻¹ * bb y * (g0 * z), hnewT y hy, ?_⟩
    show (g0 * z) * ((g0 * z)⁻¹ * bb y * (g0 * z)) * (g0 * z)⁻¹ = bb y
    group
  obtain ⟨e, he⟩ := frame_descent (ringChar K) (f : ℕ) hf1 hq hpq e7SplitTorusNonSimple_holds
    e7TorusNormalizesFrame_holds w0 hw0 gf hgfmem hgfeq hgfframe (g0 * z) hg'mem hg'eq A hA7 hAT
  refine ⟨e * c, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  have hmemA : c * v * c⁻¹ ∈ A := Subgroup.mem_map.2 ⟨v, hv, rfl⟩
  have hconj : (MulAut.conj (e * c)).toMonoidHom v = e * (c * v * c⁻¹) * e⁻¹ := by
    show (e * c) * v * (e * c)⁻¹ = e * (c * v * c⁻¹) * e⁻¹
    group
  rw [hconj]
  exact he _ hmemA

end E7SevenDescent

section Classes

set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge CFSG.AGLEmbeddingD2
  CFSG.Open CFSG.LieType.SeitzGeneration TauCeti CFSG.LieType.Seitz
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2


theorem hyperGen_adjoint_E7_two_seven (K : Type) [Field K] [Finite K] (hpq : 7 ∣ Nat.card K + 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
      IsElemAbelian 7 E → Nat.card E = 7 ^ 3 → HyperGen 7 ⊤ E)
    {E₀ : Subgroup (adjointGroup .E7 K)} (hE₀ : IsElemAbelian 7 E₀) (hc : Nat.card E₀ = 7 ^ 3) :
    HyperGen 7 ⊤ E₀ := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact hyperGen_of_two_conj (e7A1D6 K) (e7FrameGroup K) (weylWordElt .E7 K e7Word)
    e7FrameGroup_le_e7A1D6 e7FrameGroup_le_conj_e7A1D6
    (fun M hX hn => eq_top_of_e7A1D6_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => e7A1D6_le_hyperClosure (by norm_num) (by norm_num) hpq hcube E hE hEa hEc)
    hE₀ hc (e7_conj_into_frame_seven_cube hpq E₀ hE₀ hc)

theorem hyperGen_E7_two_seven {q : PrimePower} (hv : (LieTypeIndex.E7 q).Valid)
    (h2 : orderOf ((q.card : ℕ) : ZMod 7) = 2)
    {E₀ : Subgroup (Cat ⟨.E7 q, hv⟩)} (hE₀ : IsElemAbelian 7 E₀) (hc : Nat.card E₀ = 7 ^ 3) :
    HyperGen 7 ⊤ E₀ := by
  have hp7 : (7 : ℕ).Prime := by norm_num
  obtain ⟨K, _, _, hKq, -, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpq : 7 ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp7 h2
  have hpK : ¬ 7 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp7 hpq
  refine hyperGen_of_mulEquiv e ?_
  exact hyperGen_adjoint_E7_two_seven K hpq (fun E hE hEc =>
    SeitzExcOpenRest.plusModel_cubes_of_orthTwo seitzGoodInnerOrthTwo_holds (by norm_num)
      hp7 (by norm_num) hpK E hE hEc)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 7 hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

section E8Five

variable {K : Type} [Field K] [Finite K]

theorem e8_conj_into_frame_five_of_d8 (hpq : 5 ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀ : IsElemAbelian 5 E₀)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀)
    (hD8 : ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, e8D8Chain K k) :
    ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8FrameGroup K := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp5p : (5 : ℕ).Prime := Nat.prime_five
  have hord := orderOf_eq_two_of_dvd_add_one hp5p (by norm_num) hpq
  have hpK : ¬ 5 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp5p hpq
  have hpq1 := not_dvd_pred_of_dvd_add_one hp5p (by norm_num) hpq
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hpl : 5 ≠ ringChar K := by
    intro h
    apply hpK
    rw [hK, ← h]
    exact dvd_pow_self 5 m.ne_zero
  have hn3 : 3 ≤ 8 := by norm_num
  obtain ⟨Ψ, hker, hrange, hrank, hweyl⟩ := exists_psi_D8_param K hn3
  obtain ⟨g, hg⟩ := hD8
  set E := E₀.map (MulAut.conj g).toMonoidHom with hE
  have hEa : IsElemAbelian 5 E := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE₀ _
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : Nonempty (Fin 8 ⊕ Fin 8) := ⟨Sum.inl 0⟩
  haveI : Finite (spinGroup (Spin.quadPlus 8 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcen5 := not_dvd_card_center_spinPlus (K := K) hn3 (p := 5) (by norm_num) hpq1
  have hΨcop : ¬ 5 ∣ Nat.card Ψ.ker := fun hd => hcen5 (hd.trans (Subgroup.card_dvd_of_le hker))
  have hE_le : E ≤ Ψ.range := by rw [hrange]; exact hg
  set Ψ' : spinGroup (Spin.quadPlus 8 K) →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hE1 : IsElemAbelian 5 E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEa.2 x hx)⟩
  obtain ⟨E', hmapE', -, hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE'ea.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hlift : ∀ ε ∈ E, ∃ e ∈ E', Ψ e = ε := by
    intro ε hε
    have : (⟨ε, hE_le hε⟩ : Ψ.range) ∈ E1 := hε
    rw [← hmapE'] at this
    obtain ⟨e, he, hee⟩ := this
    exact ⟨e, he, congrArg Subtype.val hee⟩
  have hNS : ∀ T : Submodule K (Fin 8 ⊕ Fin 8 → K),
      (∀ e ∈ E', ∀ v ∈ T, spinAction (Spin.quadPlus 8 K) e v ∈ T) →
      (∀ v ∈ T, Spin.quadPlus 8 K v = 0) → T = ⊥ := by
    intro T hTi hTs
    by_contra hT0
    haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
    obtain ⟨U, hU0, hUp, hUn⟩ : ∃ U : Subgroup (spinGroup (Spin.quadPlus 8 K)), U ≠ ⊥ ∧
        IsPGroup (ringChar K) U ∧ ∀ e ∈ E', U.map (MulAut.conj e).toMonoidHom = U := by
      rcases Nat.even_or_odd (Nat.card K) with hev | hodd
      · have hchar2 : ringChar K = 2 := by
          have heven : Even (Fintype.card K) := by
            rw [← Nat.card_eq_fintype_card]
            exact hev
          exact FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
        haveI : CharP K 2 := ringChar.of_eq hchar2
        exact exists_rGroup_normalized_of_invariant_singular_charTwo hn3 E' T hT0 hTs hTi
      · exact exists_rGroup_normalized_of_invariant_singular hodd hn3 E' T hT0 hTs hTi
    have hcenr : ¬ ringChar K ∣ Nat.card (Subgroup.center (spinGroup (Spin.quadPlus 8 K))) := by
      rcases Nat.even_or_odd (Nat.card K) with hev | hodd
      · have hchar2 : ringChar K = 2 := by
          have heven : Even (Fintype.card K) := by
            rw [← Nat.card_eq_fintype_card]
            exact hev
          exact FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
        haveI : CharP K 2 := ringChar.of_eq hchar2
        rw [hchar2]
        exact not_dvd_card_center_spinPlus_charTwo hn3
      · have hr2 : ringChar K ≠ 2 := by
          intro h2
          have : Even (Nat.card K) := by
            rw [hK, h2]
            exact (Nat.even_pow.mpr ⟨even_two, m.ne_zero⟩)
          exact (Nat.not_even_iff_odd.mpr hodd) this
        have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
          intro hd
          have hq1 : 1 ≤ Nat.card K := Nat.card_pos
          have h1 : ringChar K ∣ Nat.card K := by
            rw [hK]
            exact dvd_pow_self _ m.ne_zero
          have h2 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
          have e : Nat.card K - (Nat.card K - 1) = 1 := by omega
          rw [e] at h2
          exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
        exact not_dvd_card_center_spinPlus (K := K) hn3 hr2 hrq1
    have hV0 := map_ne_bot_of_central_kernel Ψ hker hcenr hU0 hUp
    apply hN
    refine normalizesRGroup_of_map_conj g ⟨U.map Ψ, hV0, hUp.map Ψ, ?_⟩
    rintro ε hε
    obtain ⟨e, he, rfl⟩ := hlift ε hε
    rw [← map_conj_map Ψ e U, hUn e he]
  have hfr : ∃ x : spinGroup (Spin.quadPlus 8 K), ∀ e ∈ E',
      x * e * x⁻¹ ∈ spinFrameGroup 8 K hn3 ιstd := by
    rcases Nat.even_or_odd (Nat.card K) with hev | hodd
    · have hchar2 : ringChar K = 2 := by
        have heven : Even (Fintype.card K) := by
          rw [← Nat.card_eq_fintype_card]
          exact hev
        exact FiniteField.even_card_iff_char_two.mpr (Nat.even_iff.mp heven)
      haveI : CharP K 2 := ringChar.of_eq hchar2
      exact SeitzExcOpenRest2.exists_spin_conj_frameGroup_elem_charTwo hn3 (k := 4) (by norm_num)
        ιstd hp5p le_rfl hpl hord E' hE'comm hE'ea.2 hNS
    · exact SeitzExcOpenRest2.exists_spin_conj_frameGroup_elem hodd hn3 (k := 4) (by norm_num)
        ιstd hp5p le_rfl hpl hord E' hE'comm hE'ea.2 hNS
  obtain ⟨x, hx⟩ := hfr
  refine ⟨Ψ x * g, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨e, he, hee⟩ := hlift (g * z * g⁻¹) ⟨z, hz, rfl⟩
  have h1 : Ψ (x * e * x⁻¹) ∈ e8FrameGroup K :=
    map_spinFrameGroup_le hn3 hrank hweyl ⟨_, hx e he, rfl⟩
  have h2 : Ψ (x * e * x⁻¹) = Ψ x * (g * z * g⁻¹) * (Ψ x)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hee]
  rw [h2] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  simpa [mul_assoc] using h1

theorem hyperGen_adjoint_E8_two_five (K : Type) [Field K] [Finite K] (hpq : 5 ∣ Nat.card K + 1)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 8 K))),
      IsElemAbelian 5 E → Nat.card E = 5 ^ 3 → HyperGen 5 ⊤ E)
    {E₀ : Subgroup (adjointGroup .E8 K)} (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 3)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀)
    (hD8 : ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, e8D8Chain K k) :
    HyperGen 5 ⊤ E₀ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hpq1 : ¬ 5 ∣ Nat.card K - 1 :=
    not_dvd_pred_of_dvd_add_one Nat.prime_five (by norm_num) hpq
  exact hyperGen_of_two_conj (⨆ k, e8D8Chain K k) (e8FrameGroup K) (weylWordElt .E8 K e8Word)
    e8FrameGroup_le_d8 e8FrameGroup_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_d8Chain_le_hyperClosure Nat.prime_five le_rfl hpq1 hcube Ψ
      hker hrange E hE hEa hEc)
    hE₀ hc (e8_conj_into_frame_five_of_d8 hpq E₀ hE₀ hN hD8)

theorem hyperGen_adjoint_E8_four_five (K : Type) [Field K] [Finite K]
    (he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4)
    {E₀ : Subgroup (adjointGroup .E8 K)} (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 3)
    (hD4 : ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8D4Group K) :
    HyperGen 5 ⊤ E₀ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D8_E8_of_family (exists_e8D8_family K)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hpK := not_dvd_of_orderOf_eq_four Nat.prime_five he
  have hpq1 := not_dvd_pred_of_orderOf_eq_four Nat.prime_five hq1 he
  exact hyperGen_of_two_conj (⨆ k, e8D8Chain K k) (e8D4Group K) (weylWordElt .E8 K e8Word)
    e8D4Group_le_d8 e8D4Group_le_conj_d8
    (fun M hX hn => eq_top_of_e8D8Chain_le_of_conj_le M hX hn)
    (fun E hE hEa hEc => iSup_d8Chain_le_hyperClosure Nat.prime_five le_rfl hpq1
      (fun E' hE' hE'c => hyperGen_statedProj_quadPlus Nat.prime_five (by norm_num) hpK
        (by rw [he]) (by norm_num) E' hE' hE'c)
      Ψ hker hrange E hE hEa hEc)
    hE₀ hc hD4

end E8Five

end Classes

section Residual

open CFSG.Open CFSG.LieType.SeitzGeneration TauCeti CFSG.LieType.Seitz CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.AGLEmbedding

@[expose] def SeitzGoodInnerExcThree : Prop :=
  SeitzHyperLie fun d p E₀ => IsTopIndex d.1 ∧ ¬ NormalizesRSub d E₀ ∧ SeitzGoodIndex p d.1 ∧
    p = 3

@[expose] def E8OneFiveCubeRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ → HyperGen 5 ⊤ E₀

theorem seitzGoodInnerExcThree_of_rest2 (h : SeitzExcOpenRest2.SeitzGoodInnerExcOpenRest2) :
    SeitzGoodInnerExcThree := by
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, h3⟩
  exact h d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, Or.inl h3⟩

theorem not_p1ThreeLieList_E8 (p : ℕ) {q : PrimePower} (hv : (LieTypeIndex.E8 q).Valid) :
    ¬ P1ThreeLieList p ⟨.E8 q, hv⟩ := by
  unfold P1ThreeLieList
  rintro (⟨n, q', hq', -⟩ | ⟨q', -, hq'⟩ | ⟨-, m, hm⟩ | ⟨q', ⟨-, -, hq'⟩ | ⟨-, -, -, hq'⟩⟩ | hch)
  · simp at hq'
  · simp at hq'
  · simp at hm
  · simp at hq'
  · simp at hq'
  · unfold IsP1ChevTwoIndex at hch
    rcases hch with ⟨-, q', -, -, h⟩ | ⟨-, q', -, -, h⟩ | ⟨-, h⟩
    · simp at h
    · simp at h
    · simp at h

theorem seitzGoodIndex_five_E8 (q : PrimePower) : SeitzGoodIndex 5 (LieTypeIndex.E8 q) :=
  Or.inl (by simp [ExcIndex, Bal207Index])

end Residual

section ResidualSubgroups

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.ComponentClassification.CatLeafProof


@[expose] def E8TwoFiveCubeRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
      (¬ ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ ⨆ k, e8D8Chain K k) →
      HyperGen 5 ⊤ E₀

@[expose] def E8FourFiveCubeRest : Prop :=
  ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 4 →
    ∀ E₀ : Subgroup (adjointGroup .E8 K), IsElemAbelian 5 E₀ → Nat.card E₀ = 5 ^ 3 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
      (¬ ∃ g : adjointGroup .E8 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e8D4Group K) →
      HyperGen 5 ⊤ E₀

@[expose] def SeitzExcOpenResidual3 : Prop :=
  SeitzGoodInnerExcThree ∧ E8OneFiveCubeRest ∧ E8TwoFiveCubeRest ∧ E8FourFiveCubeRest

end ResidualSubgroups

section Assembly

set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge CFSG.AGLEmbeddingD2
  CFSG.Open CFSG.LieType.SeitzGeneration TauCeti CFSG.LieType.Seitz
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest2 CFSG.AGLEmbedding


theorem seitzGoodInnerExcOpenRest2_of_residual3 (hres : SeitzExcOpenResidual3) :
    SeitzExcOpenRest2.SeitzGoodInnerExcOpenRest2 := by
  obtain ⟨h3, h81, h82, h84⟩ := hres
  intro d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, hopen⟩
  rcases hopen with hp3 | ⟨q, hcls⟩
  ·
    exact h3 d p hp hp2 hpd hlist E₀ hE₀ hcard ⟨htop, hN, hgood, hp3⟩
  obtain ⟨d, hv⟩ := d
  rcases hcls with ⟨hd, h2, h7⟩ | ⟨hd, h5, hcase⟩
  ·
    simp only at hd
    subst hd h7
    exact hyperGen_E7_two_seven hv h2 hE₀ hcard
  · simp only at hd
    subst hd h5
    obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
    have hE₁ : IsElemAbelian 5 (E₀.map e.toMonoidHom) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE₀ _
    have hc₁ : Nat.card (E₀.map e.toMonoidHom) = 5 ^ 3 := by
      rw [Subgroup.card_map_of_injective e.injective, hcard]
    have hN₁ : ¬ NormalizesRGroup (ringChar K) (E₀.map e.toMonoidHom) := by
      intro hN'
      apply hN
      have h1 := normalizesRGroup_of_map_mulEquiv e hN'
      have hrc : ringChar K = (LieTypeIndex.E8 q).characteristic := by
        rw [ringChar.eq K q.p, LieTypeIndex.characteristic_E8]
      rw [hrc] at h1
      exact h1
    refine hyperGen_of_mulEquiv e ?_
    rcases hcase with h2 | h4 | h1
    ·
      have hpq : 5 ∣ Nat.card K + 1 := by
        rw [hKq]
        exact dvd_add_one_of_orderOf_eq_two Nat.prime_five h2
      have hpK : ¬ 5 ∣ Nat.card K := not_dvd_card_of_dvd_add_one Nat.prime_five hpq
      by_cases hD8 : ∃ g : adjointGroup .E8 K,
          (E₀.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ ⨆ k, e8D8Chain K k
      · exact hyperGen_adjoint_E8_two_five K hpq (fun E hE hEc =>
          SeitzExcOpenRest.plusModel_cubes_of_orthTwo seitzGoodInnerOrthTwo_holds (by norm_num)
            Nat.prime_five le_rfl hpK E hE hEc) hE₁ hc₁ hN₁ hD8
      · exact h82 K hpq _ hE₁ hc₁ hN₁ hD8
    ·
      have he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4 := by
        rw [hKq]
        exact h4
      by_cases hD4 : ∃ g : adjointGroup .E8 K,
          (E₀.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ e8D4Group K
      · exact hyperGen_adjoint_E8_four_five K he hE₁ hc₁ hD4
      · exact h84 K he _ hE₁ hc₁ hN₁ hD4
    ·
      have he : orderOf ((Nat.card K : ℕ) : ZMod 5) = 1 := by
        rw [hKq]
        exact h1
      exact h81 K he _ hE₁ hc₁ hN₁

theorem exists_cat_E8_equiv (K : Type) [Field K] [Finite K] :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid), Nat.card K = q.card ∧
      q.p = ringChar K ∧ Nonempty (Cat ⟨.E8 q, hv⟩ ≃* adjointGroup .E8 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  let q : PrimePower := ⟨ringChar K, n, hℓ, n.pos⟩
  have hKq : Nat.card K = q.card := by rw [Nat.card_eq_fintype_card, hn, PrimePower.card_def]
  have hv : (LieTypeIndex.E8 q).Valid := by simp
  obtain ⟨K', _, _, hK'q, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have : Fintype K' := Fintype.ofFinite K'
  have hcard : Fintype.card K' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK'q, hKq]
  let φ : K' ≃+* K := FiniteField.ringEquivOfCardEq hcard
  exact ⟨q, hv, hKq, rfl, ⟨e.trans (CFSG.TauCetiBridge.adjointGroupCongr (τ := .E8) φ)⟩⟩

theorem hyperGen_E8_five_of_rest2 (h : SeitzExcOpenRest2.SeitzGoodInnerExcOpenRest2)
    (K : Type) [Field K] [Finite K] (hpK : ¬ 5 ∣ Nat.card K)
    (hcls : ∀ q : PrimePower, Nat.card K = q.card →
      SeitzExcOpenRest2.ExcCubeOpenRest2 (LieTypeIndex.E8 q) 5)
    (E₀ : Subgroup (adjointGroup .E8 K)) (hE₀ : IsElemAbelian 5 E₀) (hc : Nat.card E₀ = 5 ^ 3)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) : HyperGen 5 ⊤ E₀ := by
  obtain ⟨q, hv, hKq, hqp, ⟨e⟩⟩ := exists_cat_E8_equiv K
  refine hyperGen_of_mulEquiv e.symm ?_
  have hpd : 5 ≠ (⟨LieTypeIndex.E8 q, hv⟩ : ValidLieTypeIndex).1.characteristic := by
    change 5 ≠ (LieTypeIndex.E8 q).characteristic
    rw [LieTypeIndex.characteristic_E8, hqp]
    intro h5
    apply hpK
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hn, ← h5]
    exact dvd_pow_self 5 n.ne_zero
  refine h ⟨.E8 q, hv⟩ 5 Nat.prime_five (by norm_num) hpd (not_p1ThreeLieList_E8 5 hv) _
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE₀ _)
    (by rw [Subgroup.card_map_of_injective e.symm.injective, hc])
    ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))), ?_, seitzGoodIndex_five_E8 q, hcls q hKq⟩
  intro hR
  apply hN
  have h1 : NormalizesRGroup (LieTypeIndex.E8 q).characteristic
      (E₀.map e.symm.toMonoidHom) := hR
  have h2 := normalizesRGroup_of_map_mulEquiv e.symm h1
  rwa [LieTypeIndex.characteristic_E8, hqp] at h2

theorem e8OneFiveCubeRest_of_rest2 (h : SeitzExcOpenRest2.SeitzGoodInnerExcOpenRest2) :
    E8OneFiveCubeRest := by
  intro K _ _ he E₀ hE₀ hc hN
  have hpK : ¬ 5 ∣ Nat.card K :=
    CFSG.LieType.SeitzGeneration.not_dvd_of_orderOf_pos Nat.prime_five he one_ne_zero
  refine hyperGen_E8_five_of_rest2 h K hpK (fun q hKq => ?_) E₀ hE₀ hc hN
  have hord : orderOf ((q.card : ℕ) : ZMod 5) = 1 := by
    rw [← hKq]
    exact he
  exact Or.inr ⟨q, Or.inr ⟨rfl, rfl, Or.inr (Or.inr hord)⟩⟩

theorem e8TwoFiveCubeRest_of_rest2 (h : SeitzExcOpenRest2.SeitzGoodInnerExcOpenRest2) :
    E8TwoFiveCubeRest := by
  intro K _ _ hpq E₀ hE₀ hc hN _
  have hpK : ¬ 5 ∣ Nat.card K := not_dvd_card_of_dvd_add_one Nat.prime_five hpq
  refine hyperGen_E8_five_of_rest2 h K hpK (fun q hKq => ?_) E₀ hE₀ hc hN
  have hord : orderOf ((q.card : ℕ) : ZMod 5) = 2 := by
    rw [← hKq]
    exact orderOf_eq_two_of_dvd_add_one Nat.prime_five (by norm_num) hpq
  exact Or.inr ⟨q, Or.inr ⟨rfl, rfl, Or.inl hord⟩⟩

theorem e8FourFiveCubeRest_of_rest2 (h : SeitzExcOpenRest2.SeitzGoodInnerExcOpenRest2) :
    E8FourFiveCubeRest := by
  intro K _ _ he E₀ hE₀ hc hN _
  have hpK : ¬ 5 ∣ Nat.card K := not_dvd_of_orderOf_eq_four Nat.prime_five he
  refine hyperGen_E8_five_of_rest2 h K hpK (fun q hKq => ?_) E₀ hE₀ hc hN
  have hord : orderOf ((q.card : ℕ) : ZMod 5) = 4 := by
    rw [← hKq]
    exact he
  exact Or.inr ⟨q, Or.inr ⟨rfl, rfl, Or.inr (Or.inl hord)⟩⟩

theorem seitzExcOpenResidual3_of_rest2 (h : SeitzExcOpenRest2.SeitzGoodInnerExcOpenRest2) :
    SeitzExcOpenResidual3 :=
  ⟨seitzGoodInnerExcThree_of_rest2 h, e8OneFiveCubeRest_of_rest2 h, e8TwoFiveCubeRest_of_rest2 h,
    e8FourFiveCubeRest_of_rest2 h⟩

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
