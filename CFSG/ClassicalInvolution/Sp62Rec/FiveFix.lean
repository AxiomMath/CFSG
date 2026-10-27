module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

variable {G : Type*} [Group G] [Finite G]

private theorem eq_eight_of_dvd_of_modEq {c : ℕ} (h1 : c ∣ 8) (h2 : 8 % 5 = c % 5) :
    c = 8 := by
  have : c ≤ 8 := Nat.le_of_dvd (by norm_num) h1
  interval_cases c <;> omega

private theorem eq_sixtyFour_of_dvd_of_modEq {c : ℕ} (h1 : c ∣ 64) (h2 : 8 ∣ c)
    (h3 : 64 % 5 = c % 5) : c = 64 := by
  have : c ≤ 64 := Nat.le_of_dvd (by norm_num) h1
  interval_cases c <;> omega

theorem card_modEq_card_inf_centralizer {p : ℕ} [Fact p.Prime] {B : Subgroup G} {g : G}
    (hgB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) (hgp : g ^ p = 1) :
    Nat.card B ≡ Nat.card ↥(B ⊓ Subgroup.centralizer ({g} : Set G)) [MOD p] := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  have hginv : g ^ (p - 1) = g⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hp1, hgp]
  have hit : ∀ k : ℕ, ∀ b ∈ B, g ^ k * b * (g ^ k)⁻¹ ∈ B := by
    intro k
    induction k with
    | zero => intro b hb; simpa using hb
    | succ k ih =>
      intro b hb
      have h := hgB _ (ih b hb)
      have e : g * (g ^ k * b * (g ^ k)⁻¹) * g⁻¹ = g ^ (k + 1) * b * (g ^ (k + 1))⁻¹ := by
        group
      rwa [e] at h
  have hinv : ∀ b ∈ B, g⁻¹ * b * g ∈ B := by
    intro b hb
    have h := hit (p - 1) b hb
    rwa [hginv, inv_inv] at h
  let σ : Equiv.Perm B :=
    { toFun := fun b => ⟨g * (b : G) * g⁻¹, hgB (b : G) b.2⟩
      invFun := fun b => ⟨g⁻¹ * (b : G) * g, hinv (b : G) b.2⟩
      left_inv := fun b => Subtype.ext (by
        show g⁻¹ * (g * (b : G) * g⁻¹) * g = (b : G)
        group)
      right_inv := fun b => Subtype.ext (by
        show g * (g⁻¹ * (b : G) * g) * g⁻¹ = (b : G)
        group) }
  have hσpow : ∀ k : ℕ, ∀ b : B, ((σ ^ k) b : G) = g ^ k * (b : G) * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [show σ ^ (k + 1) = σ ^ k * σ from pow_succ σ k, Equiv.Perm.mul_apply, ih]
      show g ^ k * (g * (b : G) * g⁻¹) * (g ^ k)⁻¹ = g ^ (k + 1) * (b : G) * (g ^ (k + 1))⁻¹
      group
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [Nat.pow_one]
    refine Equiv.ext fun b => Subtype.ext ?_
    rw [hσpow p b, hgp]
    simp
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have hfix_of_cent : ∀ (z : G) (hzB : z ∈ B), z ∈ Subgroup.centralizer ({g} : Set G) →
      σ ⟨z, hzB⟩ = ⟨z, hzB⟩ := by
    intro z hzB hzC
    apply Subtype.ext
    show g * z * g⁻¹ = z
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hzC, mul_inv_cancel_right]
  have hcent_of_fix : ∀ x : B, σ x = x → (x : G) ∈ Subgroup.centralizer ({g} : Set G) := by
    intro x hx
    have h1 : g * (x : G) * g⁻¹ = (x : G) := congrArg Subtype.val hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hmemc : ∀ x : B, σ x = x → x ∈ σ.supportᶜ := fun x hx =>
    Finset.mem_compl.mpr fun h => Equiv.Perm.mem_support.mp h hx
  have hmemc' : ∀ x : B, x ∈ σ.supportᶜ → σ x = x := fun x hx => by
    by_contra hne
    exact (Finset.mem_compl.mp hx) (Equiv.Perm.mem_support.mpr hne)
  have hcard : Nat.card ↥(B ⊓ Subgroup.centralizer ({g} : Set G)) = σ.supportᶜ.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr
      { toFun := fun z => ⟨⟨(z : G), (Subgroup.mem_inf.mp z.2).1⟩,
          hmemc ⟨(z : G), (Subgroup.mem_inf.mp z.2).1⟩
            (hfix_of_cent _ (Subgroup.mem_inf.mp z.2).1 (Subgroup.mem_inf.mp z.2).2)⟩
        invFun := fun x =>
          ⟨(x.1 : G), Subgroup.mem_inf.mpr ⟨x.1.2, hcent_of_fix x.1 (hmemc' x.1 x.2)⟩⟩
        left_inv := fun z => rfl
        right_inv := fun x => rfl }
  rw [hcard, Nat.card_eq_fintype_card]
  exact hmod.symm

theorem forall_commute_of_pow_five {A D : Subgroup G} {g : G} (hcardA : Nat.card A = 64)
    (hDA : D ≤ A) (hcardD : Nat.card D = 8) (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hg5 : g ^ 5 = 1) :
    ∀ a ∈ A, g * a = a * g := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvdD : Nat.card ↥(D ⊓ Subgroup.centralizer ({g} : Set G)) ∣ Nat.card D :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hcardD] at hdvdD
  have hmodD := card_modEq_card_inf_centralizer (p := 5) hgD hg5
  rw [hcardD] at hmodD
  have hcD : Nat.card ↥(D ⊓ Subgroup.centralizer ({g} : Set G)) = 8 :=
    eq_eight_of_dvd_of_modEq hdvdD hmodD
  have hDC : D ≤ Subgroup.centralizer ({g} : Set G) := by
    have heq : D ⊓ Subgroup.centralizer ({g} : Set G) = D :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact inf_eq_left.mp heq
  have hDAC : D ≤ A ⊓ Subgroup.centralizer ({g} : Set G) := le_inf hDA hDC
  have hdvdA : Nat.card ↥(A ⊓ Subgroup.centralizer ({g} : Set G)) ∣ Nat.card A :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hcardA] at hdvdA
  have h8A : 8 ∣ Nat.card ↥(A ⊓ Subgroup.centralizer ({g} : Set G)) := by
    have hdvd8 := Subgroup.card_dvd_of_le hDAC
    rwa [hcardD] at hdvd8
  have hmodA := card_modEq_card_inf_centralizer (p := 5) hgA hg5
  rw [hcardA] at hmodA
  have hcA : Nat.card ↥(A ⊓ Subgroup.centralizer ({g} : Set G)) = 64 :=
    eq_sixtyFour_of_dvd_of_modEq hdvdA h8A hmodA
  have hAC : A ≤ Subgroup.centralizer ({g} : Set G) := by
    have heq : A ⊓ Subgroup.centralizer ({g} : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact inf_eq_left.mp heq
  intro a ha
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hAC ha)).symm

end CFSG.ClassicalInvolution.Sp62Rec
