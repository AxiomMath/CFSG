module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NFUni
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOddHigherLinear

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.LocalAnalysis.ComponentInitial Matrix

namespace GenLocL3NF

open GenLocL3NFAux

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem not_typeIII_conj {D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))} (H : GL (Fin 3) K)
    (φ : K ≃+* K) (h3 : ¬ ∃ x ∈ D, ∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ) :
    ¬ ∃ x ∈ D.map (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom,
      ∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ := by
  rintro ⟨_, ⟨x, hx, rfl⟩, A, hA⟩
  apply h3
  refine ⟨x, hx, H * A * GeneralLinearGroup.map (φ : K →+* K) H⁻¹, ?_⟩
  rw [← conj_typeIII, ← hA]
  show x = LinearFlag.conjAut 3 K H * ((LinearFlag.conjAut 3 K H)⁻¹ * x * LinearFlag.conjAut 3 K H) *
    (LinearFlag.conjAut 3 K H)⁻¹
  group

theorem exists_conj_le_frameStab' {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ C : GL (Fin 3) K, ∀ x ∈ D, OkC C x := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have hK2 : ringChar K ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · exfalso
      have : Nat.card K = 1 := by rw [hK]; simp
      have h2 := Finite.one_lt_card (α := K)
      omega
    · exact h
  obtain ⟨-, hsq⟩ := WeakSigGen.forall_of_isElementaryAbelian hD
  have hδδ : LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have hnofield : (∀ x ∈ D, (∃ A, x = LinearFlag.conjAut 3 K A) ∨
      (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.dualAut 3 K)) →
      ∃ C : GL (Fin 3) K, ∀ x ∈ D, OkC C x := fun hno =>
    good_of_field_data (φ := 1) (by simp) hK2 hD (by rw [map_one]; exact D.one_mem)
      (fun x hx => (hno x hx).elim Or.inl fun h => Or.inr (Or.inl h))
  by_cases hex : ∃ σ : K ≃+* K, σ ≠ 1 ∧ σ * σ = 1
  · obtain ⟨φ, hφ1, hφφ⟩ := hex
    obtain ⟨hfe, hφpow⟩ := LinearFlag.even_and_eq_pow_of_involution_prime hp hf hK hφ1 hφφ
    have huniq : ∀ σ : K ≃+* K, σ * σ = 1 → σ = 1 ∨ σ = φ := by
      intro σ hσ
      by_cases hσ1 : σ = 1
      · exact Or.inl hσ1
      · right
        obtain ⟨-, hσpow⟩ := LinearFlag.even_and_eq_pow_of_involution_prime hp hf hK hσ1 hσ
        exact RingEquiv.ext fun x => (hσpow x).trans (hφpow x).symm
    by_cases h3 : ∃ x ∈ D, ∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ
    · obtain ⟨y, hyD, A, rfl⟩ := h3
      have hy2 : (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ) ^ 2 = 1 := by
        rw [sq]; exact hsq _ hyD
      obtain ⟨H, hH⟩ := OddHigherLinear.field_involution_conjugacy hp hp2 hf hK (by norm_num) A φ
        hφ1 hy2
      have : CFSG.IsElementaryAbelian 2 ↥D := hD
      have hD'' : CFSG.IsElementaryAbelian 2
          ↥(D.map (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom) :=
        CFSG.IsElementaryAbelian.map _
      have hfD'' : LinearFlag.fieldAut 3 K φ ∈
          D.map (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom := by
        refine ⟨_, hyD, ?_⟩
        show (LinearFlag.conjAut 3 K H)⁻¹ * (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ) *
          ((LinearFlag.conjAut 3 K H)⁻¹)⁻¹ = LinearFlag.fieldAut 3 K φ
        rw [hH]
        group
      exact good_of_conj H (good_of_field_data hφφ hK2 hD'' hfD''
        (fun x hx => shape4 huniq hD'' hx))
    · by_cases h4 : ∃ x ∈ D, ∃ A,
          x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K
      · obtain ⟨y, hyD, A, rfl⟩ := h4
        have hy2 : (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ *
            LinearFlag.dualAut 3 K) ^ 2 = 1 := by
          rw [sq]; exact hsq _ hyD
        obtain ⟨-, -, H, hH⟩ := LinearFlag.odd_linear_graph_field_involution_conjugacy hp hf hK
          (by norm_num) A φ hφ1 hy2
        have : CFSG.IsElementaryAbelian 2 ↥D := hD
        have hD'' : CFSG.IsElementaryAbelian 2
            ↥(D.map (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom) :=
          CFSG.IsElementaryAbelian.map _
        have hτD'' : LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K ∈
            D.map (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom := by
          refine ⟨_, hyD, ?_⟩
          show (LinearFlag.conjAut 3 K H)⁻¹ * (LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ *
            LinearFlag.dualAut 3 K) * ((LinearFlag.conjAut 3 K H)⁻¹)⁻¹ =
            LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K
          rw [hH]
          group
        have hn3 := not_typeIII_conj H φ h3
        have hshapeU : ∀ x ∈ D.map (MulAut.conj (LinearFlag.conjAut 3 K H)⁻¹).toMonoidHom,
            (∃ A, x = LinearFlag.conjAut 3 K A) ∨
              (∃ A, x = LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K φ *
                LinearFlag.dualAut 3 K) := by
          intro x hx
          rcases shape4 huniq hD'' hx with h | ⟨A', rfl⟩ | h | h
          · exact Or.inl h
          · exfalso
            apply hn3
            refine ⟨_, mul_mem hx hτD'', A', ?_⟩
            calc LinearFlag.conjAut 3 K A' * LinearFlag.dualAut 3 K *
                (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K)
                = LinearFlag.conjAut 3 K A' * (LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K φ) *
                  LinearFlag.dualAut 3 K := by simp only [mul_assoc]
              _ = LinearFlag.conjAut 3 K A' * (LinearFlag.fieldAut 3 K φ * LinearFlag.dualAut 3 K) *
                  LinearFlag.dualAut 3 K := by rw [LinearFlag.dualAut_mul_fieldAut]
              _ = LinearFlag.conjAut 3 K A' * LinearFlag.fieldAut 3 K φ *
                  (LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K) := by simp only [mul_assoc]
              _ = LinearFlag.conjAut 3 K A' * LinearFlag.fieldAut 3 K φ := by rw [hδδ, mul_one]
          · exact absurd ⟨x, hx, h⟩ hn3
          · exact Or.inr h
        exact good_of_conj H (GenLocL3NFUni.good_of_graph_field_data hp hp2 hf hK hfe hK2 hφφ hφpow
          hD'' hτD'' hshapeU)
      · apply hnofield
        intro x hx
        rcases shape4 huniq hD hx with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd ⟨x, hx, h⟩ h3
        · exact absurd ⟨x, hx, h⟩ h4
  · apply hnofield
    intro x hx
    have huniq : ∀ σ : K ≃+* K, σ * σ = 1 → σ = 1 ∨ σ = 1 := fun σ hσ =>
      Or.inl (by_contra fun h => hex ⟨σ, h, hσ⟩)
    rcases shape4 (φ := 1) huniq hD hx with h | h | ⟨A, rfl⟩ | ⟨A, rfl⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl ⟨A, by rw [map_one, mul_one]⟩
    · exact Or.inr ⟨A, by rw [map_one, mul_one]⟩

end GenLocL3NF

theorem exists_conj_le_frameStab {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K)))
    (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ β : MulAut (LinearFlag.projectiveSL 3 K), D.map (MulAut.conj β).toMonoidHom ≤ frameStab 3 K := by
  obtain ⟨C, hC⟩ := GenLocL3NF.exists_conj_le_frameStab' hp hp2 hK D hD
  refine ⟨(LinearFlag.conjAut 3 K C)⁻¹, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hC x hx
  unfold GenLocL3NFAux.OkC at h1
  show (LinearFlag.conjAut 3 K C)⁻¹ * x * ((LinearFlag.conjAut 3 K C)⁻¹)⁻¹ ∈ frameStab 3 K
  rwa [inv_inv]

end CFSG.GH74.Generic.BProg.B2
