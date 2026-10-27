module

public import CFSG.ClassicalInvolution.Q3.TL4OrthQ8Frame
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
import CFSG.ClassicalInvolution.Q3.TL4Mdl264Eng

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.O264

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

theorem isPGroup_closure_of_comm {G : Type*} [Group G] {s : Set G}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (h4 : ∀ x ∈ s, x ^ 4 = 1) :
    IsPGroup 2 ↥(Subgroup.closure s) :=
  CFSG.ClassicalInvolution.Q3.TL4.O264.isPGroup_closure_of_comm_gen hcomm h4

theorem two_lt_card_of_three {G : Type*} [Group G] {H : Subgroup G} [Finite ↥H] {a b c : G}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 < Nat.card ↥H :=
  CFSG.ClassicalInvolution.Q3.TL4.O264.two_lt_card_of_three_gen ha hb hc hab hac hbc

theorem three_ne_of_sq {G : Type*} [Group G] {x : G} (hx : x * x ≠ 1) :
    (1 : G) ≠ x * x ∧ (1 : G) ≠ x ∧ x * x ≠ x := by
  refine ⟨fun h => hx h.symm, fun h => hx (by rw [← h, one_mul]), fun h => hx ?_⟩
  have h1 : x = 1 := mul_left_cancel (a := x) (by rw [h, mul_one])
  rw [h1, one_mul]

theorem two_lt_card_inf {G : Type*} [Group G] [Finite G] {C P : Subgroup G} {x : G}
    (hC : x ∈ C) (hP : x ∈ P) (hx : x * x ≠ 1) : 2 < Nat.card ↥(C ⊓ P) := by
  obtain ⟨h1, h2, h3⟩ := three_ne_of_sq hx
  exact two_lt_card_of_three (C ⊓ P).one_mem ((C ⊓ P).mul_mem ⟨hC, hP⟩ ⟨hC, hP⟩) ⟨hC, hP⟩
    h1 h2 h3

section Comm

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem comm_of_orthoQuad {w₀ w₁ w₂ w₃ : V} (h : OrthoQuad Q w₀ w₁ w₂ w₃) (h3 : (3 : K) = 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg₀ : g w₀ = w₁)
    (hg₁ : g w₁ = -w₀) (hg₂ : g w₂ = w₂) (hg₃ : g w₃ = w₃) :
    g * (h.frame h3).La sl2I = (h.frame h3).La sl2I * g := by
  have hfix : ∀ x : V, polar Q x w₀ = 0 → polar Q x w₁ = 0 → polar Q x w₂ = 0 →
      polar Q x w₃ = 0 → g ((h.frame h3).La sl2I x) = (h.frame h3).La sl2I (g x) := by
    intro x h₀ h₁ h₂ h₃
    have e₀ : polar Q (g x) w₀ = 0 := by
      rw [show w₀ = g (-w₁) by rw [map_neg, hg₁, neg_neg], polar_map_of_mem hg,
        polar_neg_right, h₁, neg_zero]
    have e₁ : polar Q (g x) w₁ = 0 := by rw [← hg₀, polar_map_of_mem hg, h₀]
    have e₂ : polar Q (g x) w₂ = 0 := by rw [← hg₂, polar_map_of_mem hg, h₂]
    have e₃ : polar Q (g x) w₃ = 0 := by rw [← hg₃, polar_map_of_mem hg, h₃]
    rw [h.La_fix h3 sl2I h₀ h₁ h₂ h₃, h.La_fix h3 sl2I e₀ e₁ e₂ e₃]
  have s₀ : polar Q w₀ w₀ = 2 := by rw [polar_self, h.Q₀]; simp
  have s₁ : polar Q w₁ w₁ = 2 := by rw [polar_self, h.Q₁]; simp
  have s₂ : polar Q w₂ w₂ = 2 := by rw [polar_self, h.Q₂]; simp
  have s₃ : polar Q w₃ w₃ = 2 := by rw [polar_self, h.Q₃]; simp
  have r₁₀ : polar Q w₁ w₀ = 0 := by rw [polar_comm]; exact h.p₀₁
  have r₂₀ : polar Q w₂ w₀ = 0 := by rw [polar_comm]; exact h.p₀₂
  have r₃₀ : polar Q w₃ w₀ = 0 := by rw [polar_comm]; exact h.p₀₃
  have r₂₁ : polar Q w₂ w₁ = 0 := by rw [polar_comm]; exact h.p₁₂
  have r₃₁ : polar Q w₃ w₁ = 0 := by rw [polar_comm]; exact h.p₁₃
  have r₃₂ : polar Q w₃ w₂ = 0 := by rw [polar_comm]; exact h.p₂₃
  refine LinearEquiv.ext fun v => ?_
  set c₀ := polar Q v w₀ with hc₀
  set c₁ := polar Q v w₁ with hc₁
  set c₂ := polar Q v w₂ with hc₂
  set c₃ := polar Q v w₃ with hc₃
  set y := comb4 w₀ w₁ w₂ w₃ c₀ c₁ c₂ c₃ with hy
  have hpy : ∀ u : V, polar Q y u =
      c₀ * polar Q w₀ u + c₁ * polar Q w₁ u + c₂ * polar Q w₂ u + c₃ * polar Q w₃ u := by
    intro u
    simp only [hy, comb4, polar_add_left, polar_smul_left, smul_eq_mul]
  have x₀ : polar Q (v + y) w₀ = 0 := by
    rw [polar_add_left, hpy, s₀, r₁₀, r₂₀, r₃₀]
    linear_combination c₀ * h3
  have x₁ : polar Q (v + y) w₁ = 0 := by
    rw [polar_add_left, hpy, s₁, h.p₀₁, r₂₁, r₃₁]
    linear_combination c₁ * h3
  have x₂ : polar Q (v + y) w₂ = 0 := by
    rw [polar_add_left, hpy, s₂, h.p₀₂, h.p₁₂, r₃₂]
    linear_combination c₂ * h3
  have x₃ : polar Q (v + y) w₃ = 0 := by
    rw [polar_add_left, hpy, s₃, h.p₀₃, h.p₁₃, h.p₂₃]
    linear_combination c₃ * h3
  have hv : v = (v + y) - y := by abel
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hv, map_sub, map_sub, map_sub, map_sub,
    hfix _ x₀ x₁ x₂ x₃]
  congr 1
  simp only [hy, comb4, map_add, map_smul, map_neg, h.La_sl2I_w₀ h3, h.La_sl2I_w₁ h3,
    h.La_sl2I_w₂ h3, h.La_sl2I_w₃ h3, hg₀, hg₁, hg₂, hg₃]

end Comm

section Frame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (F : Frame Q)

theorem coe_sl2I_mul_self :
    ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * ((sl2I : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_sl2I, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaLin_one : sigmaLin (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

theorem sigmaLin_sl2I :
    sigmaLin ((sl2I : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = (sl2I : SL(2, K)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply, coe_sl2I]

theorem La_sl2I_incl_one : F.La sl2I (F.incl 1) = F.incl (sl2I : SL(2, K)) := by
  rw [Frame.La_apply_incl, Matrix.mul_one]

theorem La_sl2I_incl_sl2I : F.La sl2I (F.incl (sl2I : SL(2, K))) = -F.incl 1 := by
  rw [Frame.La_apply_incl, coe_sl2I_mul_self, map_neg]

theorem swap_La_sl2I_incl_one : F.swap.La sl2I (F.incl 1) = F.incl (sl2I : SL(2, K)) := by
  have h1 : F.incl 1 = F.swap.incl 1 := by rw [Frame.incl_swap, sigmaLin_one]
  have h2 : F.incl (sl2I : SL(2, K)) = F.swap.incl (sl2I : SL(2, K)) := by
    rw [Frame.incl_swap, sigmaLin_sl2I]
  rw [h1, Frame.La_apply_incl, Matrix.mul_one, ← h2]

theorem swap_La_sl2I_incl_sl2I : F.swap.La sl2I (F.incl (sl2I : SL(2, K))) = -F.incl 1 := by
  have h1 : F.incl 1 = F.swap.incl 1 := by rw [Frame.incl_swap, sigmaLin_one]
  have h2 : F.incl (sl2I : SL(2, K)) = F.swap.incl (sl2I : SL(2, K)) := by
    rw [Frame.incl_swap, sigmaLin_sl2I]
  rw [h2, Frame.La_apply_incl, coe_sl2I_mul_self, map_neg, h1]

theorem swap_La_of_mem_perp (A : SL(2, K)) {v : V} (hv : v ∈ F.perp) : F.swap.La A v = v := by
  rw [← F.perp_swap] at hv
  exact F.swap.La_apply_of_coords_eq_zero A (F.swap.mem_perp_iff.mp hv)

theorem exists_orthoQuad_perp [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V) :
    ∃ u v z : V, u ∈ F.perp ∧ v ∈ F.perp ∧ z ∈ F.perp ∧
      OrthoQuad Q (F.incl 1) (F.incl (sl2I : SL(2, K))) u v ∧ z ≠ 0 ∧ polar Q z u = 0 ∧
        polar Q z v = 0 := by
  have hd := ModelFacts.finrank_perp_add_four F
  have hP := nondegenerate_polarBilin_restrict (ModelFacts.polarNondegOn_perp hQ F)
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h0 : 0 < Module.finrank K F.perp := by omega
  have h1 : 1 < Module.finrank K F.perp := by omega
  have h2 : 2 < Module.finrank K F.perp := by omega
  obtain ⟨b, hb, hb1, -⟩ := CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hodd rfl
    (by omega) (Q.restrict F.perp) hP (one_ne_zero (α := K))
  have hQ0 : Q (b ⟨0, h0⟩ : V) = 1 := hb1 ⟨0, h0⟩ (by dsimp only; omega)
  have hQ1 : Q (b ⟨1, h1⟩ : V) = 1 := hb1 ⟨1, h1⟩ (by dsimp only; omega)
  have hpb : ∀ i j, i ≠ j → polar Q (b i : V) (b j : V) = 0 := fun i j hij => by
    have := hb i j hij
    rwa [polar_restrict] at this
  have hpi : ∀ x : V, x ∈ F.perp → ∀ Y, polar Q (F.incl Y) x = 0 := fun x hx Y => by
    rw [polar_comm]
    exact (Frame.mem_perp_iff_forall_incl F).mp hx Y
  have hu := (b ⟨0, h0⟩).2
  have hv := (b ⟨1, h1⟩).2
  refine ⟨_, _, _, hu, hv, (b ⟨2, h2⟩).2, ⟨?_, ?_, hQ0, hQ1, ?_, hpi _ hu 1, hpi _ hv 1,
    hpi _ hu _, hpi _ hv _, hpb _ _ (by simp [Fin.ext_iff])⟩, fun h => b.ne_zero ⟨2, h2⟩
    (Submodule.coe_eq_zero.mp h), hpb _ _ (by simp [Fin.ext_iff]),
    hpb _ _ (by simp [Fin.ext_iff])⟩
  · rw [Frame.Q_incl, Matrix.det_one]
  · rw [Frame.Q_incl, coe_sl2I, Matrix.det_fin_two_of]
    ring
  · rw [Frame.polar_incl_right, Frame.coords_incl, coe_sl2I]
    simp

theorem comm_La_sl2I {u v : V} (hq : OrthoQuad Q (F.incl 1) (F.incl (sl2I : SL(2, K))) u v)
    (h3 : (3 : K) = 0) (hu : u ∈ F.perp) (hv : v ∈ F.perp) :
    F.La sl2I * (hq.frame h3).La sl2I = (hq.frame h3).La sl2I * F.La sl2I :=
  comm_of_orthoQuad hq h3 (F.La_mem_orthogonalGroup sl2I) (La_sl2I_incl_one F)
    (La_sl2I_incl_sl2I F) (F.La_apply_of_coords_eq_zero _ (F.mem_perp_iff.mp hu))
    (F.La_apply_of_coords_eq_zero _ (F.mem_perp_iff.mp hv))

theorem comm_swap_La_sl2I {u v : V}
    (hq : OrthoQuad Q (F.incl 1) (F.incl (sl2I : SL(2, K))) u v) (h3 : (3 : K) = 0)
    (hu : u ∈ F.perp) (hv : v ∈ F.perp) :
    F.swap.La sl2I * (hq.frame h3).La sl2I = (hq.frame h3).La sl2I * F.swap.La sl2I :=
  comm_of_orthoQuad hq h3 (F.swap.La_mem_orthogonalGroup sl2I) (swap_La_sl2I_incl_one F)
    (swap_La_sl2I_incl_sl2I F) (swap_La_of_mem_perp F _ hu) (swap_La_of_mem_perp F _ hv)

end Frame

section Three

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Type} [Group S]

theorem theta_ne_of_apply (θ : ↥(orthDerived Q) →* S)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) (h2 : (2 : K) ≠ 0)
    {x y : ↥(orthDerived Q)} {u u' : V} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hxy : (x : V ≃ₗ[K] V) u = (y : V ≃ₗ[K] V) u) (hx : (x : V ≃ₗ[K] V) u' = -u')
    (hy : (y : V ≃ₗ[K] V) u' = u') : θ x ≠ θ y := by
  intro hθ
  have hmem : x⁻¹ * y ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθ, inv_mul_cancel]
  rw [hker, Subgroup.mem_subgroupOf, mem_scalars] at hmem
  obtain ⟨c, hc⟩ := hmem
  have key : ∀ w, (y : V ≃ₗ[K] V) w = c • (x : V ≃ₗ[K] V) w := by
    intro w
    have h1 := congrArg (x : V ≃ₗ[K] V) (hc w)
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.apply_inv_apply', map_smul] at h1
  have hc1 : c = 1 := by
    have h1 := key u
    rw [← hxy] at h1
    by_contra hne
    have h0 : (1 - c) • (x : V ≃ₗ[K] V) u = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    exact ((x : V ≃ₗ[K] V).map_ne_zero_iff.mpr hu)
      ((smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hne)))
  have h1 := key u'
  rw [hx, hy, hc1, one_smul] at h1
  have h0 : (2 : K) • u' = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    exact neg_add_cancel u'
  exact hu' ((smul_eq_zero.mp h0).resolve_left h2)

theorem La_sl2I_mul_self (θ : ↥(orthDerived Q) →* S) (G : Frame Q)
    (h : G.La sl2I ∈ orthDerived Q) : θ ⟨G.La sl2I, h⟩ * θ ⟨G.La sl2I, h⟩ = frameInv θ G := by
  rw [← map_mul, frameInv]
  congr 1
  exact Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, ← pow_two, sl2I_sq])

theorem La_sl2I_pow_four (θ : ↥(orthDerived Q) →* S) (G : Frame Q)
    (h : G.La sl2I ∈ orthDerived Q) : θ ⟨G.La sl2I, h⟩ ^ 4 = 1 := by
  rw [← map_pow]
  convert map_one θ
  exact Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, sl2I_pow_four, map_one]; rfl)

theorem frameInv_swap (θ : ↥(orthDerived Q) →* S) (F : Frame Q) :
    frameInv θ F.swap = frameInv θ F := by
  rw [frameInv, frameInv]
  congr 1
  exact Subtype.ext F.La_swap_neg_one

theorem exists_three_frames [Finite K] [FiniteDimensional K V] [Finite S] (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    (θ : ↥(orthDerived Q) →* S) (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    (F : Frame Q) :
    ∃ F₃ : Frame Q, frameInv θ F₃ ≠ frameInv θ F ∧ ∃ P : Subgroup S, IsPGroup 2 ↥P ∧
      2 < Nat.card ↥(frameMember θ F ⊓ P) ∧ 2 < Nat.card ↥(frameMember θ F.swap ⊓ P) ∧
        2 < Nat.card ↥(frameMember θ F₃ ⊓ P) := by
  have h3 := three_eq_zero hK
  have h2 := two_ne_zero' hK
  obtain ⟨u, v, z, hu, hv, hz, hq, hz0, hzu, hzv⟩ := exists_orthoQuad_perp F hK hQ hn
  have hne : ∀ w : V, Q w = 1 → w ≠ 0 := fun w hw h0 => by
    rw [h0, QuadraticMap.map_zero] at hw
    exact zero_ne_one hw
  have hu0 := hne u hq.Q₂
  have hw0 := hne _ hq.Q₀
  have hi : (sl2I : SL(2, K)) ∈ commutator SL(2, K) :=
    (mem_commutator_sl2_iff hK).mpr sl2I_pow_four
  have hFm : ∀ w : V, F.La (-1) (F.incl 1) = -F.incl 1 ∧ (w ∈ F.perp → F.La (-1) w = w) :=
    fun w => ⟨by rw [Frame.La_apply_incl, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.neg_mul, Matrix.one_mul, map_neg],
      fun hw => F.La_apply_of_coords_eq_zero _ (F.mem_perp_iff.mp hw)⟩
  have hF₃m : (hq.frame h3).La (-1) (F.incl 1) = -F.incl 1 ∧ (hq.frame h3).La (-1) u = -u := by
    have e : (hq.frame h3).La (-1) = (hq.frame h3).La sl2I * (hq.frame h3).La sl2I := by
      rw [← map_mul, ← pow_two, sl2I_sq]
    rw [e, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hq.La_sl2I_w₀ h3, hq.La_sl2I_w₁ h3,
      hq.La_sl2I_w₂ h3, hq.La_sl2I_w₃ h3]
    exact ⟨rfl, rfl⟩
  have hzfix : (hq.frame h3).La (-1) z = z := by
    have hpi := (Frame.mem_perp_iff_forall_incl F).mp hz
    exact hq.La_fix h3 (-1) (hpi 1) (hpi _) hzu hzv
  have hinvF : frameInv θ F ≠ 1 := by
    have := theta_ne_of_apply θ hker h2 (x := ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩)
      (y := 1) hu0 hw0 ((hFm u).2 hu) (hFm u).1 rfl
    rwa [θ.map_one] at this
  have hinv₃ : frameInv θ (hq.frame h3) ≠ 1 := by
    have := theta_ne_of_apply θ hker h2
      (x := ⟨(hq.frame h3).La (-1), La_neg_one_mem_orthDerived (hq.frame h3)⟩)
      (y := 1) hz0 hw0 hzfix hF₃m.1 rfl
    rwa [θ.map_one] at this
  have hinv : frameInv θ (hq.frame h3) ≠ frameInv θ F :=
    theta_ne_of_apply θ hker h2
      (x := ⟨(hq.frame h3).La (-1), La_neg_one_mem_orthDerived (hq.frame h3)⟩)
      (y := ⟨F.La (-1), La_neg_one_mem_orthDerived F⟩) hw0 hu0
      (hF₃m.1.trans (hFm u).1.symm) hF₃m.2 ((hFm u).2 hu)
  set xa : ↥(orthDerived Q) := ⟨F.La sl2I, frameQ8_le F (La_mem_frameQ8 F hi)⟩ with hxa
  set xb : ↥(orthDerived Q) := ⟨F.swap.La sl2I, frameQ8_le F.swap (La_mem_frameQ8 F.swap hi)⟩
    with hxb
  set xc : ↥(orthDerived Q) :=
    ⟨(hq.frame h3).La sl2I, frameQ8_le (hq.frame h3) (La_mem_frameQ8 (hq.frame h3) hi)⟩ with hxc
  have hab : θ xa * θ xb = θ xb * θ xa := by
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (F.La_comm_La_swap sl2I sl2I))
  have hac : θ xa * θ xc = θ xc * θ xa := by
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (comm_La_sl2I F hq h3 hu hv))
  have hbc : θ xb * θ xc = θ xc * θ xb := by
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (comm_swap_La_sl2I F hq h3 hu hv))
  have hcomm : ∀ x ∈ ({θ xa, θ xb, θ xc} : Set S), ∀ y ∈ ({θ xa, θ xb, θ xc} : Set S),
      x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · exact hab
    · exact hac
    · exact hab.symm
    · rfl
    · exact hbc
    · exact hac.symm
    · exact hbc.symm
    · rfl
  have h4 : ∀ x ∈ ({θ xa, θ xb, θ xc} : Set S), x ^ 4 = 1 := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact La_sl2I_pow_four θ F _
    · exact La_sl2I_pow_four θ F.swap _
    · exact La_sl2I_pow_four θ (hq.frame h3) _
  refine ⟨hq.frame h3, hinv, Subgroup.closure {θ xa, θ xb, θ xc},
    isPGroup_closure_of_comm hcomm h4,
    two_lt_card_inf (La_mem_frameMember θ F hi) (Subgroup.subset_closure (Set.mem_insert _ _)) ?_,
    two_lt_card_inf (La_mem_frameMember θ F.swap hi)
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) ?_,
    two_lt_card_inf (La_mem_frameMember θ (hq.frame h3) hi)
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))) ?_⟩
  · rw [La_sl2I_mul_self θ F]
    exact hinvF
  · rw [La_sl2I_mul_self θ F.swap, frameInv_swap]
    exact hinvF
  · rw [La_sl2I_mul_self θ (hq.frame h3)]
    exact hinv₃

end Three

end CFSG.ClassicalInvolution.Q3.TL4.O264
