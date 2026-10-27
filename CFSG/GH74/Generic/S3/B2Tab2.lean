module

public import CFSG.Open.StatedDefs
import CFSG.GH74.Generic.S45.LDiagCore

public section

namespace CFSG.GH74.Generic.S3.B2Tab

open Matrix Subgroup CFSG.Open
open scoped commutatorElement

section Perfect

theorem perfect_hom_trivial {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q) {M : Type*}
    [Monoid M] (φ : Q →* M) (hφ : ∀ a b : Q, φ a * φ b = φ b * φ a) (g : Q) : φ g = 1 := by
  let K : Subgroup Q :=
    { carrier := {g | φ g = 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at *
        rw [ha, hb, one_mul]
      one_mem' := map_one φ
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at *
        have h : φ a⁻¹ * φ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
        rwa [ha, mul_one] at h }
  have hcomm : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    show φ ⁅a, b⁆ = 1
    rw [commutatorElement_def]
    have h1 : φ b * φ a⁻¹ = φ a⁻¹ * φ b := hφ b a⁻¹
    calc φ (a * b * a⁻¹ * b⁻¹) = φ a * φ b * φ a⁻¹ * φ b⁻¹ := by simp only [map_mul]
      _ = φ a * (φ b * φ a⁻¹) * φ b⁻¹ := by simp only [mul_assoc]
      _ = φ a * (φ a⁻¹ * φ b) * φ b⁻¹ := by rw [h1]
      _ = (φ a * φ a⁻¹) * (φ b * φ b⁻¹) := by simp only [mul_assoc]
      _ = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel, mul_inv_cancel, map_one, mul_one]
  have htop : K = ⊤ := by
    have h1 : (⊤ : Subgroup Q) ≤ K := by
      have h2 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = (⊤ : Subgroup Q) := by
        have := hQ.commutator_eq_top
        rwa [_root_.commutator_def] at this
      rwa [h2] at hcomm
    exact top_unique h1
  have : g ∈ K := htop ▸ Subgroup.mem_top g
  exact this

end Perfect


section Rank1

variable {F : Type} [Field F]

theorem rank_one_of_sq_zero (N : Matrix (Fin 3) (Fin 3) F) (hN2 : N * N = 0) (hN0 : N ≠ 0) :
    ∃ x₀ : Fin 3 → F, N.mulVec x₀ ≠ 0 ∧ (∀ y : Fin 3 → F, ∃ a : F, N.mulVec y = a • N.mulVec x₀) ∧
      ∃ w₀ : Fin 3 → F, N.mulVec w₀ = 0 ∧ ∀ a : F, w₀ ≠ a • N.mulVec x₀ := by
  classical
  let f : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := Matrix.mulVecLin N
  have hf2 : ∀ x, f (f x) = 0 := by
    intro x
    simp only [f, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    exact hf2 x
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, N.mulVec x₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hN0
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  set u := N.mulVec x₀ with hu
  have huR : u ∈ LinearMap.range f := ⟨x₀, rfl⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrk
  have hmono := Submodule.finrank_mono hle
  have hrange1 : Module.finrank F (LinearMap.range f) = 1 := by
    have hpos : 0 < Module.finrank F (LinearMap.range f) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨⟨u, huR⟩, fun h => hx₀ (congrArg Subtype.val h)⟩
    omega
  have hker2 : Module.finrank F (LinearMap.ker f) = 2 := by omega
  refine ⟨x₀, hx₀, ?_, ?_⟩
  · intro y
    have h1 := (finrank_eq_one_iff_of_nonzero' (⟨u, huR⟩ : LinearMap.range f)
      (fun h => hx₀ (congrArg Subtype.val h))).1 hrange1 ⟨N.mulVec y, ⟨y, rfl⟩⟩
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  · by_contra hcon
    push Not at hcon
    have hkle : LinearMap.ker f ≤ Submodule.span F {u} := by
      intro z hz
      obtain ⟨a, ha⟩ := hcon z (by simpa [f] using hz)
      rw [ha]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
    have := Submodule.finrank_mono hkle
    rw [finrank_span_singleton hx₀] at this
    omega


end Rank1

section U

variable {F : Type} [Field F]

theorem flag_indep (N : Matrix (Fin 3) (Fin 3) F) (hN2 : N * N = 0) {x₀ w₀ : Fin 3 → F}
    (hx₀ : N.mulVec x₀ ≠ 0) (hw₀ : N.mulVec w₀ = 0) (hw₀' : ∀ a : F, w₀ ≠ a • N.mulVec x₀)
    (a b c : F) (h : a • N.mulVec x₀ + b • w₀ + c • x₀ = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hNu : N.mulVec (N.mulVec x₀) = 0 := by
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have h1 := congrArg N.mulVec h
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hNu, hw₀, Matrix.mulVec_zero] at h1
  simp only [smul_zero, zero_add] at h1
  have hc : c = 0 := by
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 hx₀
  subst hc
  simp only [zero_smul, add_zero] at h
  have hb : b = 0 := by
    by_contra hb
    apply hw₀' (-(a / b))
    have h3 : b • w₀ = -(a • N.mulVec x₀) := eq_neg_of_add_eq_zero_right h
    calc w₀ = b⁻¹ • (b • w₀) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • (-(a • N.mulVec x₀)) := by rw [h3]
      _ = -(a / b) • N.mulVec x₀ := by
        rw [smul_neg, smul_smul, neg_smul]
        congr 2
        field_simp
  subst hb
  simp only [zero_smul, add_zero] at h
  have ha : a = 0 := by
    rcases smul_eq_zero.1 h with h2 | h2
    · exact h2
    · exact absurd h2 hx₀
  exact ⟨ha, rfl, rfl⟩

end U


section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem false_of_perfect_central_involution_gl3 (Q : Subgroup (GL (Fin 3) F)) (hQ : ⁅Q, Q⁆ = Q)
    {c : GL (Fin 3) F} (hcQ : c ∈ Q) (hcc : c * c = 1) (hc1 : c ≠ 1)
    (hcen : ∀ g ∈ Q, g * c = c * g) : False := by
  classical
  have hperf : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQ
  set C : Matrix (Fin 3) (Fin 3) F := (c : Matrix (Fin 3) (Fin 3) F) with hC
  have hC2 : C * C = 1 := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hcc
    simpa [hC] using this
  set N : Matrix (Fin 3) (Fin 3) F := C - 1 with hNdef
  have hN2 : N * N = 0 := by
    have h2 : (1 : Matrix (Fin 3) (Fin 3) F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    have h3 : C + C = 0 := CharTwo.add_self_eq_zero C
    calc N * N = C * C - (C + C) + 1 := by rw [hNdef]; noncomm_ring
      _ = 0 := by rw [hC2, h3, sub_zero, h2]
  have hN0 : N ≠ 0 := by
    intro h
    apply hc1
    apply Units.ext
    have : C = 1 := sub_eq_zero.1 h
    simpa [hC] using this
  set G : ↥Q → Matrix (Fin 3) (Fin 3) F := fun g => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    with hG
  have hcomm : ∀ g : ↥Q, G g * N = N * G g := by
    intro g
    have h := hcen g g.2
    have h' : G g * C = C * G g := by
      have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) h
      simpa [hG, hC] using this
    rw [hNdef, mul_sub, sub_mul, h', mul_one, one_mul]
  have hGmul : ∀ g h : ↥Q, G (g * h) = G g * G h := by intro g h; simp [hG]
  have hGone : G 1 = 1 := by simp [hG]
  obtain ⟨x₀, hx₀, hrk, w₀, hw₀, hw₀'⟩ := rank_one_of_sq_zero N hN2 hN0
  set u := N.mulVec x₀ with hu
  have hind := flag_indep N hN2 hx₀ hw₀ hw₀'
  have hNu : N.mulVec u = 0 := by rw [hu, Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have hli : LinearIndependent F ![u, w₀, x₀] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hc
    obtain ⟨h0, h1, h2⟩ := hind (c 0) (c 1) (c 2) hc
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  have hspan : Submodule.span F (Set.range ![u, w₀, x₀]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hcoord : ∀ y : Fin 3 → F, ∃ a b c : F, y = a • u + b • w₀ + c • x₀ := by
    intro y
    have hy : y ∈ Submodule.span F (Set.range ![u, w₀, x₀]) := by rw [hspan]; exact Submodule.mem_top
    obtain ⟨cc, hcc'⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
    refine ⟨cc 0, cc 1, cc 2, ?_⟩
    rw [← hcc']
    simp [Fin.sum_univ_three]
  have hA : ∀ g : ↥Q, ∃ a : F, (G g).mulVec u = a • u := by
    intro g
    have h1 : (G g).mulVec u = N.mulVec ((G g).mulVec x₀) := by
      rw [hu, Matrix.mulVec_mulVec, hcomm g, ← Matrix.mulVec_mulVec]
    obtain ⟨a, ha⟩ := hrk ((G g).mulVec x₀)
    exact ⟨a, by rw [h1, ha]⟩
  have hB : ∀ g : ↥Q, ∃ α β : F, (G g).mulVec w₀ = α • u + β • w₀ := by
    intro g
    obtain ⟨a, b, c, habc⟩ := hcoord ((G g).mulVec w₀)
    have h1 : N.mulVec ((G g).mulVec w₀) = 0 := by
      rw [Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hw₀, Matrix.mulVec_zero]
    rw [habc] at h1
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hNu, hw₀, smul_zero, zero_add] at h1
    have hc : c = 0 := by
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 hx₀
    exact ⟨a, b, by rw [habc, hc, zero_smul, add_zero]⟩
  have hC' : ∀ g : ↥Q, ∃ ε δ γ : F, (G g).mulVec x₀ = ε • u + δ • w₀ + γ • x₀ :=
    fun g => hcoord _
  choose lam hlam using hA
  choose α β hαβ using hB
  choose ε δ γ hεδγ using hC'
  have hind2 : ∀ a b : F, a • u + b • w₀ = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    obtain ⟨h0, h1, -⟩ := hind a b 0 (by simpa using h)
    exact ⟨h0, h1⟩
  have hlam_mul : ∀ g h, lam (g * h) = lam g * lam h := by
    intro g h
    have h1 : (G (g * h)).mulVec u = lam (g * h) • u := hlam _
    have h2 : (G (g * h)).mulVec u = (lam g * lam h) • u := by
      rw [hGmul, ← Matrix.mulVec_mulVec, hlam h, Matrix.mulVec_smul, hlam g, smul_smul, mul_comm]
    exact smul_left_injective F hx₀ (h1.symm.trans h2)
  have hlam_one : lam 1 = 1 := by
    have h1 : (G 1).mulVec u = lam 1 • u := hlam _
    rw [hGone, Matrix.one_mulVec] at h1
    exact smul_left_injective F hx₀ (by simpa using h1.symm)
  have hβ_mul : ∀ g h, β (g * h) = β g * β h := by
    intro g h
    have e1 : (G (g * h)).mulVec w₀ = α (g * h) • u + β (g * h) • w₀ := hαβ _
    have e2 : (G (g * h)).mulVec w₀ =
        (α h * lam g + β h * α g) • u + (β g * β h) • w₀ := by
      rw [hGmul, ← Matrix.mulVec_mulVec, hαβ h, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, hlam g, hαβ g]
      module
    have e3 : (α (g * h) - (α h * lam g + β h * α g)) • u +
        (β (g * h) - β g * β h) • w₀ = 0 := by
      have := e1.symm.trans e2
      rw [sub_smul, sub_smul]
      linear_combination (exp := 1) this
    exact sub_eq_zero.1 (hind2 _ _ e3).2
  have hβ_one : β 1 = 1 := by
    have e1 : (G 1).mulVec w₀ = α 1 • u + β 1 • w₀ := hαβ _
    rw [hGone, Matrix.one_mulVec] at e1
    have e3 : α 1 • u + (β 1 - 1) • w₀ = 0 := by
      rw [sub_smul, one_smul]
      linear_combination (exp := 1) -e1
    exact sub_eq_zero.1 (hind2 _ _ e3).2
  have hγ_mul : ∀ g h, γ (g * h) = γ g * γ h := by
    intro g h
    have e1 : (G (g * h)).mulVec x₀ = ε (g * h) • u + δ (g * h) • w₀ + γ (g * h) • x₀ := hεδγ _
    have e2 : (G (g * h)).mulVec x₀ =
        (ε h * lam g + δ h * α g + γ h * ε g) • u + (δ h * β g + γ h * δ g) • w₀ +
          (γ g * γ h) • x₀ := by
      rw [hGmul, ← Matrix.mulVec_mulVec, hεδγ h, Matrix.mulVec_add, Matrix.mulVec_add,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam g, hαβ g, hεδγ g]
      module
    have e3 : (ε (g * h) - (ε h * lam g + δ h * α g + γ h * ε g)) • u +
        (δ (g * h) - (δ h * β g + γ h * δ g)) • w₀ + (γ (g * h) - γ g * γ h) • x₀ = 0 := by
      have := e1.symm.trans e2
      rw [sub_smul, sub_smul, sub_smul]
      linear_combination (exp := 1) this
    exact sub_eq_zero.1 (hind _ _ _ (by simpa [hu] using e3)).2.2
  have hγ_one : γ 1 = 1 := by
    have e1 : (G 1).mulVec x₀ = ε 1 • u + δ 1 • w₀ + γ 1 • x₀ := hεδγ _
    rw [hGone, Matrix.one_mulVec] at e1
    have e3 : ε 1 • u + δ 1 • w₀ + (γ 1 - 1) • x₀ = 0 := by
      rw [sub_smul, one_smul]
      linear_combination (exp := 1) -e1
    exact sub_eq_zero.1 (hind _ _ _ (by simpa [hu] using e3)).2.2
  let lamH : ↥Q →* F := { toFun := lam, map_one' := hlam_one, map_mul' := hlam_mul }
  let βH : ↥Q →* F := { toFun := β, map_one' := hβ_one, map_mul' := hβ_mul }
  let γH : ↥Q →* F := { toFun := γ, map_one' := hγ_one, map_mul' := hγ_mul }
  have hlam1 : ∀ g, lam g = 1 := fun g => perfect_hom_trivial hperf lamH (fun a b => mul_comm _ _) g
  have hβ1 : ∀ g, β g = 1 := fun g => perfect_hom_trivial hperf βH (fun a b => mul_comm _ _) g
  have hγ1 : ∀ g, γ g = 1 := fun g => perfect_hom_trivial hperf γH (fun a b => mul_comm _ _) g
  have hM3 : ∀ g : ↥Q, (G g - 1) * (G g - 1) * (G g - 1) = 0 := by
    intro g
    set M := G g - 1 with hM
    have hMu : M.mulVec u = 0 := by
      rw [hM, Matrix.sub_mulVec, hlam, hlam1, one_smul, Matrix.one_mulVec, sub_self]
    have hMw : M.mulVec w₀ = α g • u := by
      rw [hM, Matrix.sub_mulVec, hαβ, hβ1, one_smul, Matrix.one_mulVec]
      module
    have hMx : M.mulVec x₀ = ε g • u + δ g • w₀ := by
      rw [hM, Matrix.sub_mulVec, hεδγ, hγ1, one_smul, Matrix.one_mulVec]
      module
    have hy : ∀ y, (M * M * M).mulVec y = 0 := by
      intro y
      obtain ⟨a, b, c, rfl⟩ := hcoord y
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hMu, hMw, hMx, smul_zero,
        zero_add]
    ext i j
    have := congrFun (hy (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one] using this
  have hG4 : ∀ g : ↥Q, g ^ 4 = 1 := by
    intro g
    have hM3g := hM3 g
    set M := G g - 1 with hM
    have h2 : M + M = 0 := CharTwo.add_self_eq_zero M
    have hGg : G g = 1 + M := by rw [hM]; abel
    have h4 : G g * G g * (G g * G g) = 1 := by
      rw [hGg]
      have e1 : (1 + M) * (1 + M) = 1 + M * M := by
        calc (1 + M) * (1 + M) = 1 + (M + M) + M * M := by noncomm_ring
          _ = 1 + M * M := by rw [h2, add_zero]
      rw [e1]
      calc (1 + M * M) * (1 + M * M) = 1 + (M * M + M * M) + M * M * (M * M) := by noncomm_ring
        _ = 1 := by
          rw [CharTwo.add_self_eq_zero, add_zero]
          have : M * M * (M * M) = (M * M * M) * M := by noncomm_ring
          rw [this, hM3g, zero_mul, add_zero]
    apply Subtype.ext
    apply Units.ext
    have h5 : (G g) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      exact h4
    simpa [hG] using h5
  have hp : IsPGroup 2 ↥Q := fun g => ⟨2, by simpa using hG4 g⟩
  have hnil : Group.IsNilpotent ↥Q := IsPGroup.isNilpotent hp
  have : Nontrivial ↥Q := ⟨⟨⟨c, hcQ⟩, 1, fun h => hc1 (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isNilpotent ↥Q hnil

end Main


section PSL34

variable {F : Type} [Field F] [Finite F]

theorem false_of_perfect_central_involution_psl34 (hF : Nat.card F = 4) {Λ : Type} [Group Λ]
    [hperf : Group.IsPerfect Λ] (θ : Λ →* StatedProj (StatedSL 3 F)) (hθ : Function.Injective θ)
    {a : Λ} (ha2 : a * a = 1) (ha1 : a ≠ 1) (hac : ∀ g, g * a = a * g) : False := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  let N₀ : Subgroup ↥(StatedSL 3 F) := (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)
  let f : ↥(StatedSL 3 F) →* StatedProj (StatedSL 3 F) := QuotientGroup.mk' N₀
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective N₀
  have hPperf : ⁅θ.range, θ.range⁆ = θ.range :=
    Subgroup.isPerfect_iff.1 (Group.IsPerfect.range θ)
  obtain ⟨Q, hQ, hQP⟩ := CFSG.GH74.Generic.S45.exists_perfect_lift_hom f hPperf (by
    intro x _
    obtain ⟨y, rfl⟩ := hfsurj x
    exact ⟨y, rfl⟩)
  have hFu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hN₀cube : ∀ n ∈ N₀, n ^ 3 = 1 := by
    intro n hn
    obtain ⟨s, hs⟩ : (n : GL (Fin 3) F) ∈ StatedScalars (Fin 3) F := hn
    apply Subtype.ext
    show ((n : GL (Fin 3) F)) ^ 3 = 1
    rw [← hs, ← map_pow]
    have : s ^ 3 = 1 := by rw [← hFu]; exact pow_card_eq_one'
    rw [this, map_one]
  have hN₀cen : ∀ n ∈ N₀, ∀ u : ↥(StatedSL 3 F), n * u = u * n := by
    intro n hn u
    have hc : (n : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hn
    apply Subtype.ext
    exact ((Subgroup.mem_center_iff.1 hc) (u : GL (Fin 3) F)).symm
  obtain ⟨b, hbQ, hb⟩ : θ a ∈ Q.map f := by rw [hQP]; exact ⟨a, rfl⟩
  set c : ↥(StatedSL 3 F) := b ^ 3 with hcdef
  have hcQ : c ∈ Q := Q.pow_mem hbQ 3
  have hfc : f c = θ a := by
    rw [hcdef, map_pow, hb, ← map_pow]
    congr 1
    calc a ^ 3 = a * (a * a) := by rw [pow_succ, sq, mul_assoc]
      _ = a := by rw [ha2, mul_one]
  have hc1 : c ≠ 1 := fun h => ha1 (hθ (by rw [← hfc, h, map_one, map_one]))
  have hcc : c * c = 1 := by
    have hb2 : b ^ 2 ∈ N₀ := by
      rw [← QuotientGroup.eq_one_iff (N := N₀), ← QuotientGroup.mk'_apply]
      show f (b ^ 2) = 1
      rw [map_pow, hb, sq, ← map_mul, ha2, map_one]
    have h3 := hN₀cube _ hb2
    calc c * c = (b ^ 2) ^ 3 := by rw [hcdef, ← pow_add, ← pow_mul]
      _ = 1 := h3
  have hcomm : ∀ g ∈ Q, ⁅c, g⁆ ∈ N₀ := by
    intro g hg
    obtain ⟨h, hh⟩ : f g ∈ θ.range := hQP ▸ ⟨g, hg, rfl⟩
    rw [← QuotientGroup.eq_one_iff (N := N₀)]
    show f ⁅c, g⁆ = 1
    rw [map_commutatorElement, hfc, ← hh, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.2 (hac h).symm, map_one]
  let φ : ↥Q →* ↥(StatedSL 3 F) :=
    { toFun := fun g => ⁅c, (g : ↥(StatedSL 3 F))⁆
      map_one' := by simp
      map_mul' := fun g h => by
        have key : ⁅c, (g : ↥(StatedSL 3 F)) * h⁆ = ⁅c, (g : ↥(StatedSL 3 F))⁆ * ((g : ↥(StatedSL 3 F)) * ⁅c, (h : ↥(StatedSL 3 F))⁆ * (g : ↥(StatedSL 3 F))⁻¹) := by
          simp only [commutatorElement_def, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
        have h2 : (g : ↥(StatedSL 3 F)) * ⁅c, (h : ↥(StatedSL 3 F))⁆ * (g : ↥(StatedSL 3 F))⁻¹ = ⁅c, (h : ↥(StatedSL 3 F))⁆ := by
          rw [← hN₀cen _ (hcomm h h.2) g, mul_assoc, mul_inv_cancel, mul_one]
        simp only [Subgroup.coe_mul]
        rw [key, h2] }
  have hφcomm : ∀ g h : ↥Q, φ g * φ h = φ h * φ g := fun g h => hN₀cen _ (hcomm g g.2) (φ h)
  have hφ1 : ∀ g : ↥Q, φ g = 1 := fun g =>
    perfect_hom_trivial (Subgroup.isPerfect_iff.2 hQ) φ hφcomm g
  have hcen : ∀ g ∈ Q, g * c = c * g := by
    intro g hg
    exact (commutatorElement_eq_one_iff_mul_comm.1 (hφ1 ⟨g, hg⟩)).symm
  let Q' : Subgroup (GL (Fin 3) F) := Q.map (StatedSL 3 F).subtype
  have hQ' : ⁅Q', Q'⁆ = Q' := by
    show ⁅Q.map (StatedSL 3 F).subtype, Q.map (StatedSL 3 F).subtype⁆ = Q.map (StatedSL 3 F).subtype
    rw [← Subgroup.map_commutator, hQ]
  exact false_of_perfect_central_involution_gl3 Q' hQ' (c := (c : GL (Fin 3) F)) ⟨c, hcQ, rfl⟩
    (by have := congrArg Subtype.val hcc; simpa using this)
    (fun h => hc1 (Subtype.ext h))
    (by rintro _ ⟨g, hg, rfl⟩; exact congrArg Subtype.val (hcen g hg))

end PSL34

end CFSG.GH74.Generic.S3.B2Tab
