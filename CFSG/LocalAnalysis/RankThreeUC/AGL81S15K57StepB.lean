module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K57StepB
section Chain

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_eq_zero (w : W) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 by decide, zero_smul]

@[expose] def IsInv (ρ : G →* Module.End (ZMod 2) W) (L : Subgroup G)
    (P : Submodule (ZMod 2) W) : Prop :=
  ∀ l ∈ L, ∀ w ∈ P, ρ l w ∈ P

@[expose] def NoChainThree (ρ : G →* Module.End (ZMod 2) W) (L : Subgroup G)
    (U : Submodule (ZMod 2) W) : Prop :=
  ∀ P₀ P₁ P₂ P₃ : Submodule (ZMod 2) W, P₀ < P₁ → P₁ < P₂ → P₂ < P₃ → P₃ ≤ U →
    IsInv ρ L P₀ → IsInv ρ L P₁ → IsInv ρ L P₂ → IsInv ρ L P₃ → False

def eps (ρ : G →* Module.End (ZMod 2) W) (g : G) : W →ₗ[ZMod 2] W := ρ g + 1

theorem eps_apply (ρ : G →* Module.End (ZMod 2) W) (g : G) (w : W) :
    eps ρ g w = ρ g w + w := by simp [eps]

theorem apply_sq (ρ : G →* Module.End (ZMod 2) W) {g : G} (hg : g * g = 1) (w : W) :
    ρ g (ρ g w) = w := by
  simpa [map_mul] using congrArg (fun x => ρ x w) hg

theorem apply_comm (ρ : G →* Module.End (ZMod 2) W) {g h : G} (hgh : g * h = h * g) (w : W) :
    ρ g (ρ h w) = ρ h (ρ g w) := by
  simpa [map_mul] using congrArg (fun x => ρ x w) hgh

theorem eps_eps (ρ : G →* Module.End (ZMod 2) W) {g : G} (hg : g * g = 1) (w : W) :
    eps ρ g (eps ρ g w) = 0 := by
  rw [eps_apply, eps_apply, map_add, apply_sq ρ hg]
  calc w + ρ g w + (ρ g w + w) = (w + w) + (ρ g w + ρ g w) := by abel
    _ = 0 := by rw [add_self_eq_zero, add_self_eq_zero, add_zero]

theorem eps_comm_apply (ρ : G →* Module.End (ZMod 2) W) {g l : G} (h : g * l = l * g) (w : W) :
    eps ρ g (ρ l w) = ρ l (eps ρ g w) := by
  rw [eps_apply, eps_apply, apply_comm ρ h, map_add]

theorem eps_comm_eps (ρ : G →* Module.End (ZMod 2) W) {g h : G} (hgh : g * h = h * g) (w : W) :
    eps ρ g (eps ρ h w) = eps ρ h (eps ρ g w) := by
  simp only [eps_apply, map_add, apply_comm ρ hgh]
  abel

theorem eq_zero_of_simple (ρ : G →* Module.End (ZMod 2) W) (L : Subgroup G)
    {D : Submodule (ZMod 2) W} (hD : IsInv ρ L D)
    (hsimple : ∀ Q : Submodule (ZMod 2) W, IsInv ρ L Q → ⊥ < Q → Q < D → False)
    (f : W →ₗ[ZMod 2] W) (hf : ∀ l ∈ L, ∀ w, f (ρ l w) = ρ l (f w))
    (hfD : ∀ w ∈ D, f w ∈ D) (hff : ∀ w ∈ D, f (f w) = 0) : ∀ w ∈ D, f w = 0 := by
  intro w hw
  obtain ⟨Q, hQ⟩ : ∃ Q : Submodule (ZMod 2) W, Q = D ⊓ LinearMap.ker f := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ Q ↔ x ∈ D ∧ f x = 0 := fun x => by
    rw [hQ, Submodule.mem_inf, LinearMap.mem_ker]
  have hQD : Q ≤ D := fun x hx => ((hmem x).mp hx).1
  have hQinv : IsInv ρ L Q := fun l hl v hv => by
    obtain ⟨hv1, hv2⟩ := (hmem v).mp hv
    exact (hmem _).mpr ⟨hD l hl v hv1, by rw [hf l hl, hv2, map_zero]⟩
  have hfw : f w ∈ Q := (hmem _).mpr ⟨hfD w hw, hff w hw⟩
  rcases hQD.lt_or_eq with hlt | heq
  · by_cases hbot : Q = ⊥
    · rw [hbot, Submodule.mem_bot] at hfw
      exact hfw
    · exact (hsimple Q hQinv (bot_lt_iff_ne_bot.mpr hbot) hlt).elim
  · exact ((hmem w).mp (heq ▸ hw)).2

theorem apply_mem_of_maximal (ρ : G →* Module.End (ZMod 2) W) (L : Subgroup G)
    {D U : Submodule (ZMod 2) W} (hDU : D ≤ U) (hU : IsInv ρ L U) (hD : IsInv ρ L D)
    (hmax : ∀ Q : Submodule (ZMod 2) W, IsInv ρ L Q → D < Q → Q < U → False)
    (f : W →ₗ[ZMod 2] W) (hf : ∀ l ∈ L, ∀ w, f (ρ l w) = ρ l (f w))
    (hfU : ∀ w ∈ U, f w ∈ U) (hfD : ∀ w ∈ D, f w = 0) (hff : ∀ w ∈ U, f (f w) = 0) :
    ∀ w ∈ U, f w ∈ D := by
  intro u hu
  obtain ⟨Q, hQ⟩ : ∃ Q : Submodule (ZMod 2) W, Q = U ⊓ D.comap f := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ Q ↔ x ∈ U ∧ f x ∈ D := fun x => by
    rw [hQ, Submodule.mem_inf, Submodule.mem_comap]
  have hQU : Q ≤ U := fun x hx => ((hmem x).mp hx).1
  have hQinv : IsInv ρ L Q := fun l hl v hv => by
    obtain ⟨hv1, hv2⟩ := (hmem v).mp hv
    exact (hmem _).mpr ⟨hU l hl v hv1, by rw [hf l hl]; exact hD l hl _ hv2⟩
  have hDQ : D ≤ Q := fun w hw => (hmem w).mpr ⟨hDU hw, by rw [hfD w hw]; exact D.zero_mem⟩
  have hfuQ : f u ∈ Q := (hmem _).mpr ⟨hfU u hu, by rw [hff u hu]; exact D.zero_mem⟩
  rcases hDQ.lt_or_eq with hlt | heq
  · rcases hQU.lt_or_eq with hlt2 | heq2
    · exact (hmax Q hQinv hlt hlt2).elim
    · exact ((hmem u).mp (heq2 ▸ hu)).2
  · exact heq ▸ hfuQ

theorem action_trivial_of_noChainThree (ρ : G →* Module.End (ZMod 2) W) (L : Subgroup G)
    (U : Submodule (ZMod 2) W) (hlen : NoChainThree ρ L U) (hUL : IsInv ρ L U)
    {a b c : G} (haa : a * a = 1) (hbb : b * b = 1) (hcc : c * c = 1)
    (hac : a * c = c * a) (hbc : b * c = c * b) (hab : a * b = b * a * c)
    (haL : ∀ l ∈ L, a * l = l * a) (hbL : ∀ l ∈ L, b * l = l * b) (hcL : ∀ l ∈ L, c * l = l * c)
    (hUa : ∀ w ∈ U, ρ a w ∈ U) (hUb : ∀ w ∈ U, ρ b w ∈ U) (hUc : ∀ w ∈ U, ρ c w ∈ U) :
    ∀ u ∈ U, ρ c u = u := by
  by_contra hne
  push Not at hne
  obtain ⟨u₀, hu₀, hu₀ne⟩ := hne
  have hbotinv : IsInv ρ L ⊥ := fun l _ w hw => by
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]
  have hεU : ∀ g : G, (∀ w ∈ U, ρ g w ∈ U) → ∀ w ∈ U, eps ρ g w ∈ U := fun g hg w hw => by
    rw [eps_apply]
    exact U.add_mem (hg w hw) hw
  obtain ⟨D, hD⟩ : ∃ D : Submodule (ZMod 2) W, D = U ⊓ LinearMap.ker (eps ρ c) := ⟨_, rfl⟩
  have hDmem : ∀ x, x ∈ D ↔ x ∈ U ∧ eps ρ c x = 0 := fun x => by
    rw [hD, Submodule.mem_inf, LinearMap.mem_ker]
  obtain ⟨R, hR⟩ : ∃ R : Submodule (ZMod 2) W, R = U.map (eps ρ c) := ⟨_, rfl⟩
  have hRmem : ∀ x, x ∈ R ↔ ∃ v ∈ U, eps ρ c v = x := fun x => by
    rw [hR, Submodule.mem_map]
  have hDU' : D ≤ U := fun x hx => ((hDmem x).mp hx).1
  have hDinv : IsInv ρ L D := fun l hl w hw => by
    obtain ⟨hw1, hw2⟩ := (hDmem w).mp hw
    exact (hDmem _).mpr ⟨hUL l hl w hw1, by rw [eps_comm_apply ρ (hcL l hl), hw2, map_zero]⟩
  have hRinv : IsInv ρ L R := fun l hl w hw => by
    obtain ⟨v, hv, rfl⟩ := (hRmem w).mp hw
    exact (hRmem _).mpr ⟨ρ l v, hUL l hl v hv, eps_comm_apply ρ (hcL l hl) v⟩
  have hRD : R ≤ D := fun x hx => by
    obtain ⟨v, hv, rfl⟩ := (hRmem x).mp hx
    exact (hDmem _).mpr ⟨hεU c hUc v hv, eps_eps ρ hcc v⟩
  have hεne : eps ρ c u₀ ≠ 0 := fun h0 => by
    apply hu₀ne
    rw [eps_apply] at h0
    calc ρ c u₀ = (ρ c u₀ + u₀) + u₀ := by rw [add_assoc, add_self_eq_zero, add_zero]
      _ = u₀ := by rw [h0, zero_add]
  have hRne : R ≠ ⊥ := fun h => by
    have hmem : eps ρ c u₀ ∈ R := (hRmem _).mpr ⟨u₀, hu₀, rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hεne hmem
  have hDU : D < U := lt_of_le_of_ne hDU' fun h => by
    have : u₀ ∈ D := by rw [h]; exact hu₀
    exact hεne ((hDmem u₀).mp this).2
  have hRDeq : R = D := by
    by_contra hne'
    exact hlen ⊥ R D U (bot_lt_iff_ne_bot.mpr hRne) (lt_of_le_of_ne hRD hne') hDU le_rfl hbotinv
      hRinv hDinv hUL
  have hDne : D ≠ ⊥ := by rw [← hRDeq]; exact hRne
  have hsimple : ∀ Q : Submodule (ZMod 2) W, IsInv ρ L Q → ⊥ < Q → Q < D → False :=
    fun Q hQ h1 h2 => hlen ⊥ Q D U h1 h2 hDU le_rfl hbotinv hQ hDinv hUL
  have hmax : ∀ Q : Submodule (ZMod 2) W, IsInv ρ L Q → D < Q → Q < U → False :=
    fun Q hQ h1 h2 =>
      hlen ⊥ D Q U (bot_lt_iff_ne_bot.mpr hDne) h1 h2 le_rfl hbotinv hDinv hQ hUL
  have key : ∀ g : G, g * g = 1 → g * c = c * g → (∀ l ∈ L, g * l = l * g) →
      (∀ w ∈ U, ρ g w ∈ U) → (∀ w ∈ D, eps ρ g w = 0) ∧ (∀ u ∈ U, eps ρ g u ∈ D) := by
    intro g hgg hgc hgL hUg
    have hεD : ∀ w ∈ D, eps ρ g w ∈ D := fun w hw => by
      obtain ⟨hw1, hw2⟩ := (hDmem w).mp hw
      exact (hDmem _).mpr ⟨hεU g hUg w hw1, by rw [eps_comm_eps ρ hgc.symm, hw2, map_zero]⟩
    have hfL : ∀ l ∈ L, ∀ w, eps ρ g (ρ l w) = ρ l (eps ρ g w) :=
      fun l hl w => eps_comm_apply ρ (hgL l hl) w
    have h1 : ∀ w ∈ D, eps ρ g w = 0 :=
      eq_zero_of_simple ρ L hDinv hsimple (eps ρ g) hfL hεD fun w _ => eps_eps ρ hgg w
    exact ⟨h1, apply_mem_of_maximal ρ L hDU' hUL hDinv hmax (eps ρ g) hfL (hεU g hUg) h1
      fun w _ => eps_eps ρ hgg w⟩
  obtain ⟨hAD, hAU⟩ := key a haa hac haL hUa
  obtain ⟨hBD, hBU⟩ := key b hbb hbc hbL hUb
  have hcomm : ρ a (ρ b u₀) = ρ b (ρ a u₀) := by
    have e1 : eps ρ a (eps ρ b u₀) = 0 := hAD _ (hBU u₀ hu₀)
    have e2 : eps ρ b (eps ρ a u₀) = 0 := hBD _ (hAU u₀ hu₀)
    simp only [eps_apply, map_add] at e1 e2
    have e3 : ρ a (ρ b u₀) + (ρ a u₀ + ρ b u₀ + u₀) = 0 := by
      refine Eq.trans ?_ e1
      abel
    have e4 : ρ b (ρ a u₀) + (ρ a u₀ + ρ b u₀ + u₀) = 0 := by
      refine Eq.trans ?_ e2
      abel
    exact add_right_cancel (e3.trans e4.symm)
  have h1 : ρ a (ρ b u₀) = ρ b (ρ a (ρ c u₀)) := by
    simpa [map_mul] using congrArg (fun x => ρ x u₀) hab
  have h2 : ρ a u₀ = ρ a (ρ c u₀) := by
    have := congrArg (ρ b) (hcomm.symm.trans h1)
    rwa [apply_sq ρ hbb, apply_sq ρ hbb] at this
  have h3 : u₀ = ρ c u₀ := by
    have := congrArg (ρ a) h2
    rwa [apply_sq ρ haa, apply_sq ρ haa] at this
  exact hu₀ne h3.symm

end Chain

section SL3

variable {F : Type*} [CommRing F]

@[expose] def d8A : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def d8B : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def d8C : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_d8A : ((d8A : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem coe_d8B : ((d8B : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl

theorem coe_d8C : ((d8C : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 1; 0, 1, 0; 0, 0, 1] := rfl

theorem d8A_mul_self [CharP F 2] : d8A * d8A = (1 : Matrix.SpecialLinearGroup (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_d8A,
    Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem d8B_mul_self [CharP F 2] : d8B * d8B = (1 : Matrix.SpecialLinearGroup (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_d8B,
    Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem d8C_mul_self [CharP F 2] : d8C * d8C = (1 : Matrix.SpecialLinearGroup (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_d8C,
    Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

theorem d8A_mul_d8C : d8A * d8C = (d8C * d8A : Matrix.SpecialLinearGroup (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_d8A, coe_d8C,
    Matrix.mul_apply, Fin.sum_univ_three]

theorem d8B_mul_d8C : d8B * d8C = (d8C * d8B : Matrix.SpecialLinearGroup (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_d8B, coe_d8C,
    Matrix.mul_apply, Fin.sum_univ_three]

theorem d8A_mul_d8B : d8A * d8B = (d8B * d8A * d8C : Matrix.SpecialLinearGroup (Fin 3) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_mul, coe_d8A, coe_d8B,
    coe_d8C, Matrix.mul_apply, Fin.sum_univ_three]

theorem d8C_not_mem_center [Nontrivial F] :
    (d8C : Matrix.SpecialLinearGroup (Fin 3) F) ∉
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have h02 := congrFun (congrFun hr 0) 2
  change Matrix.scalar (Fin 3) r 0 2 = (1 : F) at h02
  simp [Matrix.scalar_apply, Matrix.diagonal_apply] at h02

end SL3

section Composite

variable {G W F : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W] [CommRing F] [CharP F 2]
  [Nontrivial F]

theorem exists_noncentral_acting_trivially (ρ : G →* Module.End (ZMod 2) W) (L M : Subgroup G)
    (hLM : ∀ l ∈ L, ∀ m ∈ M, l * m = m * l) (e : M ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (U : Submodule (ZMod 2) W) (hlen : NoChainThree ρ L U) (hUL : IsInv ρ L U)
    (hUM : IsInv ρ M U) : ∃ c : M, c ∉ Subgroup.center M ∧ ∀ u ∈ U, ρ c u = u := by
  have hmul : ∀ x y z : Matrix.SpecialLinearGroup (Fin 3) F, x * y = z →
      ((e.symm x : M) : G) * (e.symm y : M) = (e.symm z : M) := fun x y z h => by
    rw [← h, map_mul, Subgroup.coe_mul]
  have hone : ∀ x : Matrix.SpecialLinearGroup (Fin 3) F, x * x = 1 →
      ((e.symm x : M) : G) * (e.symm x : M) = 1 := fun x h => by
    rw [hmul x x 1 h, map_one, Subgroup.coe_one]
  have hcomm : ∀ x : Matrix.SpecialLinearGroup (Fin 3) F, ∀ l ∈ L,
      ((e.symm x : M) : G) * l = l * (e.symm x : M) := fun x l hl =>
    (hLM l hl _ (e.symm x).2).symm
  have hcomm' : ∀ x y : Matrix.SpecialLinearGroup (Fin 3) F, x * y = y * x →
      ((e.symm x : M) : G) * (e.symm y : M) = (e.symm y : M) * (e.symm x : M) :=
    fun x y h => (hmul x y (y * x) h).trans (hmul y x (y * x) rfl).symm
  have hab : ((e.symm d8A : M) : G) * (e.symm d8B : M) =
      (e.symm d8B : M) * (e.symm d8A : M) * (e.symm d8C : M) := by
    rw [hmul d8A d8B (d8B * d8A * d8C) d8A_mul_d8B, hmul d8B d8A (d8B * d8A) rfl,
      hmul (d8B * d8A) d8C (d8B * d8A * d8C) rfl]
  refine ⟨e.symm d8C, ?_, ?_⟩
  · intro h
    apply d8C_not_mem_center (F := F)
    rw [Subgroup.mem_center_iff]
    intro s
    simpa using congrArg e (Subgroup.mem_center_iff.mp h (e.symm s))
  · exact action_trivial_of_noChainThree ρ L U hlen hUL (hone _ d8A_mul_self)
      (hone _ d8B_mul_self) (hone _ d8C_mul_self) (hcomm' _ _ d8A_mul_d8C)
      (hcomm' _ _ d8B_mul_d8C) hab (hcomm _) (hcomm _) (hcomm _)
      (hUM _ (e.symm d8A).2) (hUM _ (e.symm d8B).2) (hUM _ (e.symm d8C).2)

end Composite

end K57StepB

end CFSG.LocalAnalysis.RankThreeUC.S15
