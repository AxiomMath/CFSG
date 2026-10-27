module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem s8d_matrix_pow_five (e : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h : e ^ 5 = 1) :
    e = 1 := by
  revert h e
  decide +kernel

theorem s8d_cent_five {f : S8A}
    (hf : ∀ a : ↥(alternatingGroup (Fin 5)), f * s8dDiag a = s8dDiag a * f) (h5 : f ^ 5 = 1) :
    f = 1 := by
  let s : ↥(alternatingGroup (Fin 5)) → EvW →+ EvW :=
    fun a => permW (a : Equiv.Perm (Fin 5))
  have hs : OntoAct s := fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩
  let F : (EvW × EvW) →+ (EvW × EvW) :=
    { toFun := s8dAp f
      map_zero' := s8dAp_zero f
      map_add' := s8dAp_add f }
  have hF : ∀ i p, F (s i p.1, s i p.2) = (s i (F p).1, s i (F p).2) := by
    intro i p
    have h := congrArg (fun g : S8A => s8dAp g p) (hf i)
    simpa [F, s, s8dAp_mul, s8dAp_diag] using h
  obtain ⟨e, he⟩ := sec128_exists_theta hs F hF
  have hFe : ∀ p, s8dAp f p = thetaW e p :=
    fun p => congrArg (fun g : (EvW × EvW) →+ (EvW × EvW) => g p) he
  have hpow : ∀ k : ℕ, ∀ p, s8dAp (f ^ k) p = thetaW (e ^ k) p := by
    intro k
    induction k with
    | zero => intro p; rw [pow_zero, s8dAp_one, pow_zero, sec128_thetaW_one]; rfl
    | succ k ih =>
        intro p
        calc s8dAp (f ^ (k + 1)) p
            = s8dAp (f ^ k * f) p := by rw [pow_succ]
          _ = s8dAp (f ^ k) (s8dAp f p) := s8dAp_mul _ _ _
          _ = thetaW (e ^ k) (thetaW e p) := by rw [ih, hFe]
          _ = thetaW (e ^ k * e) p := by rw [sec128_thetaW_mul (e ^ k) e]; rfl
          _ = thetaW (e ^ (k + 1)) p := by rw [pow_succ]
  have h5e : e ^ 5 = 1 := by
    apply sec128_thetaW_injective
    refine AddMonoidHom.ext fun p => ?_
    have h := hpow 5 p
    rw [h5, s8dAp_one] at h
    rw [sec128_thetaW_one]
    exact h.symm
  have he1 : e = 1 := s8d_matrix_pow_five e h5e
  have hFid : F = AddMonoidHom.id (EvW × EvW) := by
    rw [he, he1]
    exact sec128_thetaW_one
  refine s8d_ext fun p => ?_
  have hp := congrArg (fun g : (EvW × EvW) →+ (EvW × EvW) => g p) hFid
  change s8dAp f p = p
  simpa [F] using hp

theorem s8d_endA5_dich (β : ↥(alternatingGroup (Fin 5)) →* ↥(alternatingGroup (Fin 5))) :
    (∀ a, β a = 1) ∨ Function.Bijective β := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal β.ker with h | h
  · right
    exact ((MonoidHom.ker_eq_bot_iff β).mp h).bijective_of_finite
  · left
    intro a
    have ha : a ∈ β.ker := by rw [h]; exact Subgroup.mem_top a
    simpa [MonoidHom.mem_ker] using ha

theorem s8d_diag_param {Z : Subgroup S8A}
    (hD : ∀ a : ↥(alternatingGroup (Fin 5)), s8dDiag a ∈ Z)
    (θ : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z) :
    ∃ θ' : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) ≃* ↥Z,
      ∀ a : ↥(alternatingGroup (Fin 5)), (θ' (a, a) : S8A) = s8dDiag a := by
  let A := ↥(alternatingGroup (Fin 5))
  let D : A →* S8A := s8dDiag.comp (alternatingGroup (Fin 5)).subtype
  let D' : A →* ↥Z := D.codRestrict Z fun a => hD a
  let δ : A →* A × A := θ.symm.toMonoidHom.comp D'
  let β₁ : A →* A := (MonoidHom.fst A A).comp δ
  let β₂ : A →* A := (MonoidHom.snd A A).comp δ
  have hθδZ : ∀ a, θ (δ a) = D' a := by
    intro a
    have hδ : δ a = θ.symm (D' a) := rfl
    rw [hδ]
    exact θ.apply_symm_apply (D' a)
  have hθδ : ∀ a, (θ (δ a) : S8A) = s8dDiag a := by
    intro a
    rw [hθδZ a]
    rfl
  have hgpow : s8dG ^ 5 = 1 := by
    refine Subtype.ext ?_
    simpa [s8dG] using (show (finRotate 5 : Equiv.Perm (Fin 5)) ^ 5 = 1 by decide)
  have hgne : s8dG ≠ 1 := by
    intro h
    have h' : (finRotate 5 : Equiv.Perm (Fin 5)) = 1 := by
      simpa [s8dG] using congrArg Subtype.val h
    revert h'
    decide
  have hprod : ((s8dG, 1) : A × A) ^ 5 = 1 := by
    refine Prod.ext ?_ ?_
    · show s8dG ^ 5 = 1
      exact hgpow
    · show (1 : A) ^ 5 = 1
      simp
  have hprod' : ((1, s8dG) : A × A) ^ 5 = 1 := by
    refine Prod.ext ?_ ?_
    · show (1 : A) ^ 5 = 1
      simp
    · show s8dG ^ 5 = 1
      exact hgpow
  by_cases h1t : ∀ a, β₁ a = 1
  · exfalso
    have hδa : ∀ a, δ a = (1, β₂ a) := by
      intro a
      refine Prod.ext ?_ ?_
      · change β₁ a = 1
        exact h1t a
      · rfl
    have hcomm : ∀ a : A,
        (θ (s8dG, 1) : S8A) * s8dDiag a = s8dDiag a * (θ (s8dG, 1) : S8A) := by
      intro a
      have hD'θa : D' a = θ (1, β₂ a) := by rw [← hθδZ a, hδa a]
      have hZ : θ (s8dG, 1) * D' a = D' a * θ (s8dG, 1) := by
        rw [hD'θa]
        calc θ (s8dG, 1) * θ (1, β₂ a)
            = θ ((s8dG, 1) * (1, β₂ a)) := (map_mul θ _ _).symm
          _ = θ ((1, β₂ a) * (s8dG, 1)) := by simp
          _ = θ (1, β₂ a) * θ (s8dG, 1) := map_mul θ _ _
      have h := congrArg (fun z : ↥Z => (z : S8A)) hZ
      have hDa : (D' a : S8A) = s8dDiag a := rfl
      simpa [hDa] using h
    have hu5Z : (θ (s8dG, 1) : ↥Z) ^ 5 = 1 := by
      rw [← map_pow, hprod, map_one]
    have hu5 : (θ (s8dG, 1) : S8A) ^ 5 = 1 := by
      change (Subgroup.subtype Z (θ (s8dG, 1) : ↥Z)) ^ 5 = 1
      rw [← map_pow (Subgroup.subtype Z), hu5Z, map_one]
    have hu1 : (θ (s8dG, 1) : S8A) = 1 := s8d_cent_five hcomm hu5
    have huZ1 : (θ (s8dG, 1) : ↥Z) = 1 := by
      apply Subtype.ext
      simpa using hu1
    have hpair : ((s8dG, 1) : A × A) = 1 := by
      apply θ.injective
      rw [huZ1]
      exact (map_one θ).symm
    exact hgne (by simpa using congrArg Prod.fst hpair)
  · by_cases h2t : ∀ a, β₂ a = 1
    · exfalso
      have hδa : ∀ a, δ a = (β₁ a, 1) := by
        intro a
        refine Prod.ext ?_ ?_
        · rfl
        · change β₂ a = 1
          exact h2t a
      have hcomm : ∀ a : A,
          (θ (1, s8dG) : S8A) * s8dDiag a = s8dDiag a * (θ (1, s8dG) : S8A) := by
        intro a
        have hD'θa : D' a = θ (β₁ a, 1) := by rw [← hθδZ a, hδa a]
        have hZ : θ (1, s8dG) * D' a = D' a * θ (1, s8dG) := by
          rw [hD'θa]
          calc θ (1, s8dG) * θ (β₁ a, 1)
              = θ ((1, s8dG) * (β₁ a, 1)) := (map_mul θ _ _).symm
            _ = θ ((β₁ a, 1) * (1, s8dG)) := by simp
            _ = θ (β₁ a, 1) * θ (1, s8dG) := map_mul θ _ _
        have h := congrArg (fun z : ↥Z => (z : S8A)) hZ
        have hDa : (D' a : S8A) = s8dDiag a := rfl
        simpa [hDa] using h
      have hu5Z : (θ (1, s8dG) : ↥Z) ^ 5 = 1 := by
        rw [← map_pow, hprod', map_one]
      have hu5 : (θ (1, s8dG) : S8A) ^ 5 = 1 := by
        change (Subgroup.subtype Z (θ (1, s8dG) : ↥Z)) ^ 5 = 1
        rw [← map_pow (Subgroup.subtype Z), hu5Z, map_one]
      have hu1 : (θ (1, s8dG) : S8A) = 1 := s8d_cent_five hcomm hu5
      have huZ1 : (θ (1, s8dG) : ↥Z) = 1 := by
        apply Subtype.ext
        simpa using hu1
      have hpair : ((1, s8dG) : A × A) = 1 := by
        apply θ.injective
        rw [huZ1]
        exact (map_one θ).symm
      exact hgne (by simpa using congrArg Prod.snd hpair)
    · have h1bij : Function.Bijective β₁ := by
        rcases s8d_endA5_dich β₁ with h | h
        · exact absurd h h1t
        · exact h
      have h2bij : Function.Bijective β₂ := by
        rcases s8d_endA5_dich β₂ with h | h
        · exact absurd h h2t
        · exact h
      refine ⟨(MulEquiv.prodCongr (MulEquiv.ofBijective β₁ h1bij)
        (MulEquiv.ofBijective β₂ h2bij)).trans θ, fun a => ?_⟩
      change (θ (MulEquiv.ofBijective β₁ h1bij a, MulEquiv.ofBijective β₂ h2bij a)
        : S8A) = s8dDiag a
      rw [show MulEquiv.ofBijective β₁ h1bij a = β₁ a from rfl,
        show MulEquiv.ofBijective β₂ h2bij a = β₂ a from rfl]
      rw [show (β₁ a, β₂ a) = δ a from Prod.ext rfl rfl]
      exact hθδ a

end CFSG.OddStandard.SmallF3.Omega
