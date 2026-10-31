
module

public import CFSG.GF2Type.Smith1979.IdxFourModelTrvBase
public import Certificates.Certificate17605

@[expose] public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour.Orb

theorem fixed_of_normal_pGroup {Gp X : Type*} [Group Gp] [MulAction Gp X] [Finite X]
    [MulAction.IsPretransitive Gp X] (hX : Odd (Nat.card X)) (Nn : Subgroup Gp) [Nn.Normal]
    (h2 : IsPGroup 2 Nn) : ∀ n ∈ Nn, ∀ x : X, n • x = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := h2.card_modEq_card_fixedPoints X
  have hodd : Odd (Nat.card (MulAction.fixedPoints Nn X)) := by
    have := (Nat.odd_iff.2 (hmod ▸ Nat.odd_iff.1 hX))
    exact this
  have hne : (MulAction.fixedPoints Nn X).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hodd
    simp at hodd
  obtain ⟨x₀, hx₀⟩ := hne
  intro n hn x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Gp x₀ x
  have h1 : (g⁻¹ * n * g : Gp) ∈ Nn := by
    have := Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
    simpa [mul_assoc] using this
  have h2' : (⟨g⁻¹ * n * g, h1⟩ : Nn) • x₀ = x₀ := hx₀ ⟨_, h1⟩
  calc n • g • x₀ = g • ((g⁻¹ * n * g) • x₀) := by
        rw [← mul_smul, ← mul_smul]
        congr 1
        group
    _ = g • x₀ := by rw [show ((g⁻¹ * n * g) • x₀) = x₀ from h2']

theorem theta0_theta0_add (x : V12) : theta0 (theta0 x) = x + theta0 x := by
  refine ext_lo_hi (fun i => ?_) (fun i => ?_) <;> simp only [theta0_lo, theta0_hi, Pi.add_apply]

theorem add_self_V12 (x : V12) : x + x = 0 := by
  funext j
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x j = c
  revert c
  decide

theorem f0_add_right' (x y z : V12) : f0 x (y + z) = f0 x y + f0 x z := by
  unfold f0
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

def InOmega (v : V12) : Prop :=
  inO378 v ∧ f0 v w0 = 0 ∧ f0 v (theta0 w0) = 0 ∧ v ≠ w0 ∧ v ≠ theta0 w0 ∧
    v ≠ theta0 (theta0 w0)

theorem theta0_theta0_w0 : theta0 (theta0 w0) = vecOf 195 := by
  rw [theta0_w0]
  have := vecOf_theta0N (n := 192) (by norm_num)
  rw [show theta0N 192 = 195 by decide] at this
  exact this.symm

theorem f0_codes_eq_zero (v : V12) (m : ℕ) (hm : m < 4096) :
    f0 v (vecOf m) = 0 ↔ f0b (codeOf v) m = false := by
  have h : f0 v (vecOf m) = if f0b (codeOf v) m then 1 else 0 := by
    conv_lhs => rw [← vecOf_codeOf v]
    exact f0_vecOf _ _
  rw [h]
  cases f0b (codeOf v) m <;> simp

theorem inOmega_iff (v : V12) : InOmega v ↔ inOmegab (codeOf v) = true := by
  have e3 : w0 = vecOf 3 := rfl
  have h0 : f0 v w0 = 0 ↔ f0b (codeOf v) 3 = false := by
    rw [e3]; exact f0_codes_eq_zero v 3 (by norm_num)
  have h1 : f0 v (theta0 w0) = 0 ↔ f0b (codeOf v) 192 = false := by
    rw [theta0_w0]; exact f0_codes_eq_zero v 192 (by norm_num)
  have hne : ∀ m : ℕ, m < 4096 → (v ≠ vecOf m ↔ codeOf v ≠ m) := fun m hm => by
    constructor
    · intro h h'
      exact h (by rw [← vecOf_codeOf v, h'])
    · intro h h'
      exact h (by rw [h', codeOf_vecOf hm])
  unfold InOmega inO378 inOmegab
  rw [h0, h1, theta0_theta0_w0, theta0_w0, e3, hne 3 (by norm_num), hne 192 (by norm_num),
    hne 195 (by norm_num)]
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
  tauto

theorem card_InOmega : Nat.card {v : V12 // InOmega v} = 135 := by
  have e : {v : V12 // InOmega v} ≃ {n : Fin 4096 // inOmegab n = true} :=
    codeEquiv.subtypeEquiv (fun v => inOmega_iff v)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

section Invariance

variable {g : V12 ≃ₗ[ZMod 2] V12}

theorem g_theta_w0 (hg : g ∈ stabIn M0 w0) :
    g (theta0 w0) = theta0 w0 ∨ g (theta0 w0) = theta0 (theta0 w0) := by
  obtain ⟨hgM, hgw⟩ := mem_stabIn.1 hg
  rcases (mem_gammaU.1 (M0_le_gammaU hgM)).2 with h | h
  · left
    rw [h, hgw]
  · right
    rw [h, hgw]

theorem triple_stab (hg : g ∈ stabIn M0 w0) {v : V12}
    (hv : v = w0 ∨ v = theta0 w0 ∨ v = theta0 (theta0 w0)) :
    g v = w0 ∨ g v = theta0 w0 ∨ g v = theta0 (theta0 w0) := by
  obtain ⟨-, hgw⟩ := mem_stabIn.1 hg
  rcases hv with rfl | rfl | rfl
  · exact Or.inl hgw
  · rcases g_theta_w0 hg with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rw [theta0_theta0_add, map_add, hgw]
    rcases g_theta_w0 hg with h | h
    · rw [h, ← theta0_theta0_add]
      exact Or.inr (Or.inr rfl)
    · rw [h, theta0_theta0_add, ← add_assoc, add_self_V12, zero_add]
      exact Or.inr (Or.inl rfl)

theorem inOmega_stab (hg : g ∈ stabIn M0 w0) {v : V12}
    (hv : InOmega v) : InOmega (g v) := by
  obtain ⟨hgM, hgw⟩ := mem_stabIn.1 hg
  obtain ⟨h378, hf0, hf1, hn0, hn1, hn2⟩ := hv
  have hiso := f0_gammaU (M0_le_gammaU hgM)
  have h0 : f0 (g v) w0 = 0 :=
    calc f0 (g v) w0 = f0 (g v) (g w0) := by rw [hgw]
      _ = f0 v w0 := hiso _ _
      _ = 0 := hf0
  refine ⟨inO378_invariant hgM h378, h0, ?_, ?_⟩
  · rcases g_theta_w0 hg with h | h
    · calc f0 (g v) (theta0 w0) = f0 (g v) (g (theta0 w0)) := by rw [h]
        _ = f0 v (theta0 w0) := hiso _ _
        _ = 0 := hf1
    · have h2 : f0 (g v) (theta0 (theta0 w0)) = 0 :=
        calc f0 (g v) (theta0 (theta0 w0)) = f0 (g v) (g (theta0 w0)) := by rw [h]
          _ = f0 v (theta0 w0) := hiso _ _
          _ = 0 := hf1
      rw [theta0_theta0_add, f0_add_right', h0, zero_add] at h2
      exact h2
  · have hinv : g⁻¹ ∈ stabIn M0 w0 := inv_mem hg
    have key : ∀ t, ¬ (t = w0 ∨ t = theta0 w0 ∨ t = theta0 (theta0 w0)) →
        ¬ (g t = w0 ∨ g t = theta0 w0 ∨ g t = theta0 (theta0 w0)) := by
      intro t ht h
      refine ht ?_
      have := triple_stab hinv h
      simpa [inv_apply_apply] using this
    have := key v (by tauto)
    refine ⟨fun h => this (Or.inl h), fun h => this (Or.inr (Or.inl h)),
      fun h => this (Or.inr (Or.inr h))⟩

end Invariance

abbrev OmegaTy : Type := {v : V12 // InOmega v}

@[instance_reducible] def omegaAction (K : Subgroup (V12 ≃ₗ[ZMod 2] V12))
    (hK : K ≤ stabIn M0 w0) : MulAction ↥K OmegaTy where
  smul g x := ⟨g.1 x.1, inOmega_stab (hK g.2) x.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

theorem gensOK_pGens : GensOK pGens :=
  gensOK_of_pairs
    [(#[2241, 2242, 1052, 227, 1540, 1288, 2211, 2147, 784, 2051, 1816, 1812],
      #[706, 705, 2100, 1076, 3376, 203, 587, 651, 1312, 2320, 308, 515]),
     (#[2, 1, 8, 16, 32, 4, 128, 64, 512, 1024, 2048, 256],
      #[2, 1, 32, 4, 8, 16, 128, 64, 2048, 256, 512, 1024])]
    (by decide +kernel) (by decide +kernel)

theorem pGens_fix : ∀ p ∈ pGens, appN p 3 = 3 := by decide +kernel

theorem genGrp_pGens_le :
    genGrp pGens ≤ stabIn E0 w0 := by
  refine genGrp_le_of_rep fun p hp => ?_
  obtain ⟨hok, U, hU, hUx⟩ := rep_gen gensOK_pGens hp
  refine ⟨hok, U, mem_stabIn.2 ⟨Certificates.certificate17605.1 hU, ?_⟩, hUx⟩
  have : U w0 = linOfRows p w0 := hUx w0
  rw [this]
  change linOfRows p (vecOf 3) = vecOf 3
  rw [← vecOf_appN, pGens_fix p hp]

theorem e0Base_inOmega : ∀ b ∈ Chain.e0Base, inOmegab b.val = true := by
  intro b hb
  simp only [Chain.e0Base, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

end CFSG.GF2Type.Smith1979.IdxFour
