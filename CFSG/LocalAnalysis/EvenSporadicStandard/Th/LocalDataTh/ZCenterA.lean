module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ZData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Aa

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped Matrix commutatorElement

section Generic

variable {F : Type*} [Group F]

theorem conj_mem_A_of_iff {S A : Subgroup F}
    (hA : ∀ x, x ∈ A ↔ x ∈ S ∧ ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, ∀ s₄ ∈ S,
      ⁅⁅⁅⁅x, s₁⁆, s₂⁆, s₃⁆, s₄⁆ = 1)
    {g : F} (hg : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S) {x : F} (hx : x ∈ A) : g * x * g⁻¹ ∈ A := by
  rw [hA] at hx ⊢
  obtain ⟨hxS, hx4⟩ := hx
  refine ⟨(hg x).1 hxS, fun s₁ hs₁ s₂ hs₂ s₃ hs₃ s₄ hs₄ => ?_⟩
  have key : ∀ (u v : F), ⁅g * u * g⁻¹, g * v * g⁻¹⁆ = g * ⁅u, v⁆ * g⁻¹ := fun u v => by
    simp only [commutatorElement_def]
    group
  have hS' : ∀ s ∈ S, g⁻¹ * s * g ∈ S := fun s hs => by
    refine (hg _).2 ?_
    simpa [mul_assoc] using hs
  have h := hx4 (g⁻¹ * s₁ * g) (hS' _ hs₁) (g⁻¹ * s₂ * g) (hS' _ hs₂) (g⁻¹ * s₃ * g) (hS' _ hs₃)
    (g⁻¹ * s₄ * g) (hS' _ hs₄)
  have e : ∀ s : F, s = g * (g⁻¹ * s * g) * g⁻¹ := fun s => by group
  rw [e s₁, e s₂, e s₃, e s₄, key, key, key, key, h]
  group

theorem comm_mul_left_eq (x y a : F) : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
  simp only [commutatorElement_def]
  group

theorem comm_mul_right_eq (s a b : F) : ⁅s, a * b⁆ = ⁅s, a⁆ * (a * ⁅s, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

end Generic

section Z


theorem A_le_M : A ≤ M := by
  rintro _ ⟨s, u, -, rfl⟩
  exact Q_le_M (nf_mem_Q s u)

theorem conj_mem_A_of_mem_S {τ x : J} (hτ : τ ∈ S) (hx : x ∈ A) : τ * x * τ⁻¹ ∈ A :=
  conj_mem_A_of_iff mem_A_iff (mem_iff_conj_of_mem hτ) hx

theorem comm_nf_nf (s t : ZMod 2) (v w : Vec) :
    ⁅nf s v, nf t w⁆ = z ^ (CFSG.Certificates.ExtraspecialNF.bil c v w).val :=
  CFSG.Certificates.ExtraspecialNF.commutator_eq_zpow symplectic_rel (fun i j => c_symm j i)
    (by decide) s t v w

theorem zpow_val_add (a b : ZMod 2) : z ^ (a + b).val = z ^ a.val * z ^ b.val := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases a with rfl | rfl <;>
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · have h11 : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h11]
    simp [CFSG.Certificates.ExtraspecialNF.val_one_two, z_mul_self]

theorem zpow_val_pow (l e : ZMod 2) : (z ^ l.val) ^ e.val = z ^ (e * l).val := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases e with rfl | rfl
  · simp
  · simp [CFSG.Certificates.ExtraspecialNF.val_one_two]

theorem zpow_val_inj {a b : ZMod 2} (h : z ^ a.val = z ^ b.val) : a = b := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases a with rfl | rfl <;>
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases b with rfl | rfl
  · rfl
  · exfalso
    simp [CFSG.Certificates.ExtraspecialNF.val_one_two] at h
    exact z_ne_one h.symm
  · exfalso
    simp [CFSG.Certificates.ExtraspecialNF.val_one_two] at h
    exact z_ne_one h
  · rfl

theorem rho_fix_of_comm_B (hZ : HZFacts) {s : J} (hs : s ∈ S) (h : ∀ x ∈ S, ⁅s, x⁆ ∈ B) :
    ∀ j : Fin 3, rho s *ᵥ uVec j = uVec j := by
  obtain ⟨a, ha, hrho⟩ := mem_Pt_iff.1 hs.2
  have key : ∀ (i : Fin 8) (j : Fin 3), CFSG.Certificates.ExtraspecialNF.bil c
      ((rho s + 1) *ᵥ (Pi.single i 1 : Vec)) (uVec j) = 0 := by
    intro i j
    have hB := h (q i) (Q_le_S (q_mem_Q i))
    obtain ⟨t, ht⟩ := comm_nf hs.1 0 (Pi.single i 1)
    rw [← nf_single i, ht] at hB
    have hc := (mem_B_iff _).1 hB (nf 0 (uVec j)) (nf_zero_uVec_mem j)
    have h1 := comm_eq_one_iff.2 hc
    rw [comm_nf_nf] at h1
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases
      (CFSG.Certificates.ExtraspecialNF.bil c ((rho s + 1) *ᵥ (Pi.single i 1 : Vec)) (uVec j))
      with h0 | h0
    · exact h0
    · exfalso
      rw [h0, CFSG.Certificates.ExtraspecialNF.val_one_two, pow_one] at h1
      exact z_ne_one h1
  rw [← hrho] at key ⊢
  exact hZ.1 a ha key

theorem ksem3_span {u : Vec} (hu : u ∈ Ksem 3) :
    ∃ e : Fin 3 → ZMod 2, u = e 0 • uVec 0 + e 1 • uVec 1 + e 2 • uVec 2 := by
  obtain ⟨c, hc, rfl⟩ := Ksem3_iff.1 hu
  have : ∀ c ∈ UCodes, ∃ e : Fin 3 → ZMod 2,
      codeVec 8 c = e 0 • uVec 0 + e 1 • uVec 1 + e 2 • uVec 2 := by decide
  exact this c hc

theorem comm_mem_zpowers_of_mem_A {s : J} (hs : s ∈ Kt) {a : J} (ha : a ∈ A) :
    ⁅s, a⁆ ∈ Subgroup.zpowers z := by
  obtain ⟨r, u, hu, rfl⟩ := mem_A_iff'.1 ha
  obtain ⟨e, he⟩ := ksem3_span hu
  have hfix : rho s *ᵥ u = u := by
    rw [he, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hs.2 0, hs.2 1, hs.2 2]
  obtain ⟨t, ht⟩ := comm_nf hs.1 r u
  rw [ht, Matrix.add_mulVec, Matrix.one_mulVec, hfix, vec_add_self, nf_zero_vec]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _

theorem comm_mul_of_mem_A {s : J} (hs : s ∈ Kt) {a b : J} (ha : a ∈ A) (hb : b ∈ A) :
    ⁅s, a * b⁆ = ⁅s, a⁆ * ⁅s, b⁆ := by
  rw [comm_mul_right_eq, conj_eq_of_mem_zpowers_z (A_le_M ha) (comm_mem_zpowers_of_mem_A hs hb)]

theorem comm_cA {s : J} (hs : s ∈ Kt) (lam : Fin 3 → ZMod 2)
    (hlam : ∀ j, ⁅s, nf 0 (uVec j)⁆ = z ^ (lam j).val) (e : Vec4) :
    ⁅s, cA e⁆ = z ^ (e 1 * lam 0 + e 2 * lam 1 + e 3 * lam 2).val := by
  have hmul : ∀ a ∈ A, ∀ b ∈ A, (fun g => ⁅s, g⁆) (a * b) =
      (fun g => ⁅s, g⁆) a * (fun g => ⁅s, g⁆) b := fun a ha b hb => comm_mul_of_mem_A hs ha hb
  have key := map_cA (fun g => ⁅s, g⁆) hmul e
  rw [key]
  have h0 : ⁅s, aGen 0⁆ = 1 := by
    have : aGen 0 = z := by simp [aGen]
    rw [this]
    exact comm_eq_one_iff.2 (commute_z_of_mem_M hs.1).symm.eq
  have h1 : ⁅s, aGen 1⁆ = z ^ (lam 0).val := hlam 0
  have h2 : ⁅s, aGen 2⁆ = z ^ (lam 1).val := hlam 1
  have h3 : ⁅s, aGen 3⁆ = z ^ (lam 2).val := hlam 2
  rw [h0, h1, h2, h3, one_pow, one_mul, zpow_val_pow, zpow_val_pow, zpow_val_pow, zpow_val_add,
    zpow_val_add]

theorem comm_conj_A {s : J} (hs : s ∈ Kt) (hSB : ∀ x ∈ S, ⁅s, x⁆ ∈ B) {τ a : J} (hτ : τ ∈ S)
    (ha : a ∈ A) : ⁅s, τ⁻¹ * a * τ⁆ = ⁅s, a⁆ := by
  have hτM : τ ∈ M := hτ.1
  have ha' : τ⁻¹ * a * τ ∈ A := by
    have := conj_mem_A_of_mem_S (S.inv_mem hτ) ha
    simpa using this
  have hw : ⁅τ, s⁆ ∈ B := by
    rw [← commutatorElement_inv]
    exact B.inv_mem (hSB τ hτ)
  have hz : ∀ u ∈ Subgroup.zpowers z, ⁅τ, s⁆ * u * ⁅τ, s⁆⁻¹ = u := fun u hu => by
    have hu' : u ∈ A := (Subgroup.zpowers_le.2 z_mem_A) hu
    rw [(mem_B_iff _).1 hw u hu', mul_inv_cancel_right]
  have e1 : ⁅τ * s * τ⁻¹, a⁆ = ⁅s, τ⁻¹ * a * τ⁆ := by
    have : ⁅τ * s * τ⁻¹, τ * (τ⁻¹ * a * τ) * τ⁻¹⁆ = τ * ⁅s, τ⁻¹ * a * τ⁆ * τ⁻¹ := by
      simp only [commutatorElement_def]
      group
    have e : τ * (τ⁻¹ * a * τ) * τ⁻¹ = a := by group
    rw [e] at this
    rw [this, conj_eq_of_mem_zpowers_z hτM (comm_mem_zpowers_of_mem_A hs ha')]
  have e2 : ⁅τ * s * τ⁻¹, a⁆ = ⁅s, a⁆ := by
    have : τ * s * τ⁻¹ = ⁅τ, s⁆ * s := by
      simp only [commutatorElement_def]
      group
    rw [this, comm_mul_left_eq, hz _ (comm_mem_zpowers_of_mem_A hs ha),
      comm_eq_one_iff.2 ((mem_B_iff _).1 hw a ha), mul_one]
  rw [← e1, e2]

end Z

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
