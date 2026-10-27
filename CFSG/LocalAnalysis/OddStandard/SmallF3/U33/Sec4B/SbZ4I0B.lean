module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4I0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAmbient

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

private theorem z4i_conjAut_congr {G : Type*} [Group G] (H : Subgroup G) {g g' : G}
    (hg : g ∈ normalizer (H : Set G)) (hg' : g' ∈ normalizer (H : Set G)) (h : g = g') :
    Outside.conjAut H g hg = Outside.conjAut H g' hg' := by
  subst h
  ext x
  rfl

private theorem z4i_card_mod_three_of_fpf {S : Type*} [Group S] [Finite S] (ρ : MulAut S)
    (hρ : ρ ^ 3 = 1) (hfpf : ∀ g : S, ρ g = g → g = 1) (H : Subgroup S)
    (hH : ∀ h ∈ H, ρ h ∈ H) : Nat.card H % 3 = 1 := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let f : Function.End H := fun h => ⟨ρ h, hH h h.2⟩
  have hf : ∀ k : ℕ, ∀ h : H, ((f ^ k) h : S) = (ρ ^ k) h := by
    intro k
    induction k with
    | zero => intro h; rfl
    | succ k ih =>
      intro h
      rw [pow_succ, pow_succ]
      show ((f ^ k) (f h) : S) = (ρ ^ k) (ρ h)
      rw [ih]
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext h
    apply Subtype.ext
    rw [pow_one, hf 3 h, hρ]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  have hfix : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, Subtype.ext (map_one ρ)⟩, ?_⟩
    rintro ⟨y, hy⟩
    exact Subtype.ext (Subtype.ext (hfpf y (congrArg Subtype.val hy)))
  rw [Nat.card_eq_fintype_card]
  have h2 : Fintype.card f.fixedPoints % 3 = 1 := by simp [hfix]
  have h3 : Fintype.card H % 3 = Fintype.card f.fixedPoints % 3 := hmod
  omega

theorem z4i_card_mod_three {A : Type*} [Group A] (K : Subgroup A) [Finite K] (σ : A)
    (hσ3 : σ ^ 3 = 1) (hnorm : ∀ k ∈ K, σ * k * σ⁻¹ ∈ K)
    (hfpf : ∀ k ∈ K, σ * k * σ⁻¹ = k → k = 1) : Nat.card K % 3 = 1 := by
  classical
  have hmem : σ ∈ normalizer (K : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hnorm h hh
    · intro hh
      have h1 : σ * (σ * h * σ⁻¹) * σ⁻¹ ∈ K := hnorm _ hh
      have h2 : σ * (σ * (σ * h * σ⁻¹) * σ⁻¹) * σ⁻¹ ∈ K := hnorm _ h1
      have hσ3' : σ * σ * σ = 1 := by rw [← pow_three', hσ3]
      have heq : σ * (σ * (σ * h * σ⁻¹) * σ⁻¹) * σ⁻¹ = h := by
        calc σ * (σ * (σ * h * σ⁻¹) * σ⁻¹) * σ⁻¹
            = (σ * σ * σ) * h * (σ * σ * σ)⁻¹ := by group
          _ = h := by rw [hσ3']; group
      rwa [heq] at h2
  have hp := Outside.conjAut_pow K hmem 3 (pow_mem hmem 3)
  have h1 : Outside.conjAut K (σ ^ 3) (pow_mem hmem 3) = 1 := by
    rw [z4i_conjAut_congr K (pow_mem hmem 3) (one_mem _) hσ3]
    exact Outside.conjAut_one K (one_mem _)
  have hρ3 : Outside.conjAut K σ hmem ^ 3 = 1 := by
    rw [← hp]
    exact h1
  have hfpf' : ∀ x : K, Outside.conjAut K σ hmem x = x → x = 1 := by
    intro x hx
    apply Subtype.ext
    apply hfpf (x : A) x.2
    have h := congrArg (fun y : K => (y : A)) hx
    simpa [Outside.conjAut_coe] using h
  have hmod := z4i_card_mod_three_of_fpf (Outside.conjAut K σ hmem) hρ3 hfpf'
    (⊤ : Subgroup K) (fun _ _ => trivial)
  rwa [Subgroup.card_top] at hmod

theorem z4i_card_pow_two {A : Type*} [Group A] (K : Subgroup A) [Finite K]
    (hsq : ∀ k ∈ K, k * k = 1) : ∃ n : ℕ, Nat.card K = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 K := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hsq (g : A) g.2
  exact hp.exists_card_eq

private def z4iMap {Q : Type*} [Group Q] (V : Subgroup Q) (x₁ x₂ : Q)
    (K : Subgroup (MulAut Q)) (hKV : ∀ σ ∈ K, ∀ q : Q, σ q * q⁻¹ ∈ V) : K → V × V :=
  fun σ => (⟨σ.1 x₁ * x₁⁻¹, hKV σ.1 σ.2 x₁⟩, ⟨σ.1 x₂ * x₂⁻¹, hKV σ.1 σ.2 x₂⟩)

private theorem z4iMap_injective {Q : Type*} [Group Q] (V : Subgroup Q) (x₁ x₂ : Q)
    (hdet : ∀ σ ∈ z4iFixY Q, ∀ τ ∈ z4iFixY Q, σ x₁ = τ x₁ → σ x₂ = τ x₂ → σ = τ)
    (K : Subgroup (MulAut Q)) (hKF : K ≤ z4iFixY Q)
    (hKV : ∀ σ ∈ K, ∀ q : Q, σ q * q⁻¹ ∈ V) :
    Function.Injective (z4iMap V x₁ x₂ K hKV) := by
  intro σ σ' h
  have h1 : σ.1 x₁ * x₁⁻¹ = σ'.1 x₁ * x₁⁻¹ := by
    have := congrArg (fun y : V => (y : Q)) (congrArg Prod.fst h)
    simpa [z4iMap] using this
  have h2 : σ.1 x₂ * x₂⁻¹ = σ'.1 x₂ * x₂⁻¹ := by
    have := congrArg (fun y : V => (y : Q)) (congrArg Prod.snd h)
    simpa [z4iMap] using this
  have hx1 : σ.1 x₁ = σ'.1 x₁ := mul_right_cancel h1
  have hx2 : σ.1 x₂ = σ'.1 x₂ := mul_right_cancel h2
  exact Subtype.ext (hdet σ.1 (hKF σ.2) σ'.1 (hKF σ'.2) hx1 hx2)

theorem z4i_card_le {Q : Type*} [Group Q] [Finite Q] (V : Subgroup Q) (x₁ x₂ : Q)
    (hdet : ∀ σ ∈ z4iFixY Q, ∀ τ ∈ z4iFixY Q, σ x₁ = τ x₁ → σ x₂ = τ x₂ → σ = τ)
    (K : Subgroup (MulAut Q)) (hKF : K ≤ z4iFixY Q) (hKV : ∀ σ ∈ K, ∀ q : Q, σ q * q⁻¹ ∈ V) :
    Nat.card K ≤ Nat.card V ^ 2 := by
  classical
  haveI : Finite V := Finite.of_injective (Subtype.val : V → Q) Subtype.val_injective
  have hf : Function.Injective (z4iMap V x₁ x₂ K hKV) := z4iMap_injective V x₁ x₂ hdet K hKF hKV
  calc Nat.card K ≤ Nat.card (V × V) := Nat.card_le_card_of_injective _ hf
    _ = Nat.card V ^ 2 := by rw [Nat.card_prod, ← pow_two]

theorem z4i_mem_of_card_eq {Q : Type*} [Group Q] [Finite Q] (V : Subgroup Q) (x₁ x₂ : Q)
    (hdet : ∀ σ ∈ z4iFixY Q, ∀ τ ∈ z4iFixY Q, σ x₁ = τ x₁ → σ x₂ = τ x₂ → σ = τ)
    (K : Subgroup (MulAut Q)) (hKF : K ≤ z4iFixY Q) (hKV : ∀ σ ∈ K, ∀ q : Q, σ q * q⁻¹ ∈ V)
    (hcard : Nat.card K = Nat.card V ^ 2) {τ : MulAut Q} (hτF : τ ∈ z4iFixY Q)
    (hτV : ∀ q : Q, τ q * q⁻¹ ∈ V) : τ ∈ K := by
  classical
  haveI : Finite V := Finite.of_injective (Subtype.val : V → Q) Subtype.val_injective
  have hf : Function.Injective (z4iMap V x₁ x₂ K hKV) := z4iMap_injective V x₁ x₂ hdet K hKF hKV
  have hcard' : Nat.card (V × V) ≤ Nat.card K := by
    rw [Nat.card_prod, ← pow_two, ← hcard]
  have hbij : Function.Bijective (z4iMap V x₁ x₂ K hKV) := hf.bijective_of_nat_card_le hcard'
  let target : V × V := (⟨τ x₁ * x₁⁻¹, hτV x₁⟩, ⟨τ x₂ * x₂⁻¹, hτV x₂⟩)
  obtain ⟨σ, hσ⟩ := hbij.2 target
  have hx1 : σ.1 x₁ = τ x₁ := by
    have h := congrArg (fun y : V => (y : Q)) (congrArg Prod.fst hσ)
    have h' : σ.1 x₁ * x₁⁻¹ = τ x₁ * x₁⁻¹ := by simpa [z4iMap, target] using h
    exact mul_right_cancel h'
  have hx2 : σ.1 x₂ = τ x₂ := by
    have h := congrArg (fun y : V => (y : Q)) (congrArg Prod.snd hσ)
    have h' : σ.1 x₂ * x₂⁻¹ = τ x₂ * x₂⁻¹ := by simpa [z4iMap, target] using h
    exact mul_right_cancel h'
  have hστ : σ.1 = τ := hdet σ.1 (hKF σ.2) τ hτF hx1 hx2
  rw [← hστ]
  exact σ.2

theorem z4i_count {Q : Type*} [Group Q] [Finite Q] (hcomm : ∀ a b : Q, a * b = b * a)
    (h4 : ∀ q : Q, q ^ 4 = 1) (V : Subgroup Q) (hV : Nat.card V = 4) (x₁ x₂ : Q)
    (hdet : ∀ σ ∈ z4iFixY Q, ∀ τ ∈ z4iFixY Q, σ x₁ = τ x₁ → σ x₂ = τ x₂ → σ = τ)
    (ρ τ : MulAut Q) (hρ3 : ρ ^ 3 = 1) (hτF : τ ∈ z4iFixY Q)
    (hτV : ∀ q : Q, τ q * q⁻¹ ∈ V) (hρτ : ρ * τ = τ * ρ) (hτ1 : τ ≠ 1)
    (K : Subgroup (MulAut Q)) [Finite K] (hKF : K ≤ ⁅z4iFixY Q, zpowers ρ⁆)
    (hKV : ∀ σ ∈ K, ∀ q : Q, σ q * q⁻¹ ∈ V) (hKρ : ∀ σ ∈ K, ρ * σ * ρ⁻¹ ∈ K) :
    Nat.card K = 1 ∨ Nat.card K = 4 := by
  classical
  have hnormE : ∀ e ∈ z4iFixY Q, ρ * e * ρ⁻¹ ∈ z4iFixY Q :=
    fun e he => z4iFixY_conj_mem he ρ
  have hcommE : ∀ e ∈ z4iFixY Q, ∀ e' ∈ z4iFixY Q, e * e' = e' * e :=
    fun e he e' he' => z4iFixY_mul_comm hcomm h4 he he'
  have hsqE : ∀ e ∈ z4iFixY Q, e * e = 1 :=
    fun e he => z4iFixY_mul_self hcomm h4 he
  have hcomm_le : ⁅z4iFixY Q, zpowers ρ⁆ ≤ z4iFixY Q := by
    rw [Subgroup.commutator_le]
    intro e he g _
    have hmem : g * e⁻¹ * g⁻¹ ∈ z4iFixY Q := z4iFixY_conj_mem ((z4iFixY Q).inv_mem he) g
    have heq : ⁅e, g⁆ = e * (g * e⁻¹ * g⁻¹) := by rw [commutatorElement_def]; group
    rw [heq]
    exact (z4iFixY Q).mul_mem he hmem
  have hKE : K ≤ z4iFixY Q := hKF.trans hcomm_le
  have hsqK : ∀ σ ∈ K, σ * σ = 1 := fun σ hσ => hsqE σ (hKE hσ)
  obtain ⟨n, hn⟩ := z4i_card_pow_two K hsqK
  have hle16 : Nat.card K ≤ 16 := by
    have hle : Nat.card K ≤ Nat.card V ^ 2 := z4i_card_le V x₁ x₂ hdet K hKE hKV
    simpa [hV] using hle
  have hfpfK : ∀ k ∈ K, ρ * k * ρ⁻¹ = k → k = 1 := by
    intro k hk hfix
    exact z4i_fix_trivial (z4iFixY Q) ρ hρ3 hnormE hcommE hsqE (hKF hk) hfix
  have hmod : Nat.card K % 3 = 1 := z4i_card_mod_three K ρ hρ3 hKρ hfpfK
  have hne16 : Nat.card K ≠ 16 := by
    intro h16
    have hcard : Nat.card K = Nat.card V ^ 2 := by rw [h16, hV]; norm_num
    have hτK : τ ∈ K := z4i_mem_of_card_eq V x₁ x₂ hdet K hKE hKV hcard hτF hτV
    have hfixτ : ρ * τ * ρ⁻¹ = τ := by rw [hρτ]; group
    exact hτ1 (z4i_fix_trivial (z4iFixY Q) ρ hρ3 hnormE hcommE hsqE (hKF hτK) hfixτ)
  have hn4 : n ≤ 4 := by
    have hpow : 2 ^ n ≤ 2 ^ 4 := by
      rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hn]
      exact hle16
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp hpow
  interval_cases n
  · left; simpa using hn
  · exfalso; rw [hn] at hmod; norm_num at hmod
  · right; simpa using hn
  · exfalso; rw [hn] at hmod; norm_num at hmod
  · exfalso; exact hne16 (by simpa using hn)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
