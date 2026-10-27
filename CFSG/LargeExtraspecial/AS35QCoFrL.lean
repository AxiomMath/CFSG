module

public import CFSG.LargeExtraspecial.AS35QCoNat
public import CFSG.LargeExtraspecial.AS35QCoFrF0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Co2Smith

section Hom

variable {A B : Type*} [Group A] [Group B] (f : A →* B)

theorem map_comm_of {a b c d : A} (h : a * b = c * d) : f a * f b = f c * f d := by
  rw [← map_mul, ← map_mul, h]

theorem map_conj_of {a b c : A} (h : a * b * a = c * c) : f a * f b * f a = f c * f c := by
  rw [← map_mul, ← map_mul, ← map_mul, h]

theorem map_pow_of {a : A} {n : ℕ} (h : a ^ n = 1) : f a ^ n = 1 := by
  rw [← map_pow, h, map_one]

theorem map_sq_of {a : A} (h : a * a = 1) : f a * f a = 1 := by
  rw [← map_mul, h, map_one]

end Hom

variable {G : Type} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def psiS0 (θ : S.LbarAsc ≃* Sp62) : S0 ≃* S.LbarAsc :=
  (MulEquiv.ofBijective resS0 resS0_bijective).trans θ.symm

@[expose] noncomputable def kappa (θ : S.LbarAsc ≃* Sp62) : S0 →* (S.Qt ≃ₗ[ZMod 2] S.Qt) where
  toFun k := (((psiS0 S θ k : S.LbarAsc) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  map_one' := by simp only [map_one, Subgroup.coe_one]
  map_mul' a b := by simp only [map_mul, Subgroup.coe_mul]

theorem kappa_apply (θ : S.LbarAsc ≃* Sp62) (k : S0) :
    kappa S θ k = (((psiS0 S θ k : S.LbarAsc) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := rfl

theorem kappa_injective (θ : S.LbarAsc ≃* Sp62) : Function.Injective (kappa S θ) := fun _ _ h =>
  (psiS0 S θ).injective (Subtype.ext (Subtype.ext h))

theorem isIsom_kappa (θ : S.LbarAsc ≃* Sp62) (k : S0) : IsIsom S.q (kappa S θ k) :=
  isom S _

@[expose] noncomputable def frameL (θ : S.LbarAsc ≃* Sp62) : Frame S.q where
  Y₁ := kappa S θ (frS 0)
  Y₂ := kappa S θ (frS 2)
  Y₃ := kappa S θ (frS 4)
  S₁ := kappa S θ (frS 1)
  S₂ := kappa S θ (frS 3)
  S₃ := kappa S θ (frS 5)
  P₁₂ := kappa S θ (frS 6)
  P₂₃ := kappa S θ (frS 7)
  X := kappa S θ (frS 8)
  iY₁ := isIsom_kappa S θ _
  iY₂ := isIsom_kappa S θ _
  iY₃ := isIsom_kappa S θ _
  iS₁ := isIsom_kappa S θ _
  iX := isIsom_kappa S θ _
  y₁ := map_pow_of _ (frS_y_pow (i := 0) (by norm_num))
  y₂ := map_pow_of _ (frS_y_pow (i := 1) (by norm_num))
  y₃ := map_pow_of _ (frS_y_pow (i := 2) (by norm_num))
  s₁ := map_sq_of _ (frS_s_sq (i := 0) (by norm_num))
  s₂ := map_sq_of _ (frS_s_sq (i := 1) (by norm_num))
  s₃ := map_sq_of _ (frS_s_sq (i := 2) (by norm_num))
  sy₁ := map_conj_of _ (frS_s_y (i := 0) (by norm_num))
  sy₂ := map_conj_of _ (frS_s_y (i := 1) (by norm_num))
  sy₃ := map_conj_of _ (frS_s_y (i := 2) (by norm_num))
  y₁₂ := map_comm_of _ (frS_comm (i := 0) (j := 1) (e := 0) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  y₁₃ := map_comm_of _ (frS_comm (i := 0) (j := 2) (e := 0) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  y₂₃ := map_comm_of _ (frS_comm (i := 1) (j := 2) (e := 0) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₁y₂ := map_comm_of _ (frS_comm (i := 0) (j := 1) (e := 1) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₁y₃ := map_comm_of _ (frS_comm (i := 0) (j := 2) (e := 1) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₂y₁ := map_comm_of _ (frS_comm (i := 1) (j := 0) (e := 1) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₂y₃ := map_comm_of _ (frS_comm (i := 1) (j := 2) (e := 1) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₃y₁ := map_comm_of _ (frS_comm (i := 2) (j := 0) (e := 1) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₃y₂ := map_comm_of _ (frS_comm (i := 2) (j := 1) (e := 1) (e' := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₁₂ := map_comm_of _ (frS_comm (i := 0) (j := 1) (e := 1) (e' := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  s₁₃ := map_comm_of _ (frS_comm (i := 0) (j := 2) (e := 1) (e' := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num))
  p₁₂y₁ := map_comm_of _ (frS_p12 (k := 0) (by norm_num))
  p₁₂y₂ := map_comm_of _ (frS_p12 (k := 2) (by norm_num))
  p₁₂y₃ := map_comm_of _ (frS_p12 (k := 4) (by norm_num))
  p₁₂s₁ := map_comm_of _ (frS_p12 (k := 1) (by norm_num))
  p₂₃y₁ := map_comm_of _ (frS_p23 (k := 0) (by norm_num))
  p₂₃y₂ := map_comm_of _ (frS_p23 (k := 2) (by norm_num))
  p₂₃y₃ := map_comm_of _ (frS_p23 (k := 4) (by norm_num))
  p₂₃s₁ := map_comm_of _ (frS_p23 (k := 1) (by norm_num))
  x₅ := map_pow_of _ frS_x_pow
  xy₁ := map_comm_of _ frS_x_y1
  xs₁ := map_comm_of _ frS_x_s1

theorem mem_fixL_of_fixedByFrame (θ : S.LbarAsc ≃* Sp62) {f₀ : S.Qt}
    (h : (frameL S θ).FixedByFrame f₀) : f₀ ∈ fixL S := by
  let K : Subgroup S0 :=
    { carrier := {k | kappa S θ k f₀ = f₀}
      mul_mem' := fun {a b} ha hb => by
        change kappa S θ (a * b) f₀ = f₀
        rw [map_mul, LinearEquiv.mul_apply, show kappa S θ b f₀ = f₀ from hb]
        exact ha
      one_mem' := by
        change kappa S θ 1 f₀ = f₀
        rw [map_one]
        rfl
      inv_mem' := fun {a} ha => by
        change kappa S θ a⁻¹ f₀ = f₀
        rw [map_inv]
        nth_rewrite 1 [← show kappa S θ a f₀ = f₀ from ha]
        exact inv_mul_apply _ f₀ }
  have hK : K = ⊤ := by
    obtain ⟨h0, h2, h4, h1, h3, h5, h6, h7, h8⟩ := h
    refine eq_top_of_frS_mem K fun k hk => ?_
    interval_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
  intro g hg
  obtain ⟨k, hk⟩ := (psiS0 S θ).surjective ⟨g, hg⟩
  have hkK : k ∈ K := hK ▸ mem_top k
  have e : kappa S θ k = (g : S.Qt ≃ₗ[ZMod 2] S.Qt) := by rw [kappa_apply, hk]
  rw [← e]
  exact hkK

theorem fixSpace_frameL_X
    (hS : S.SixHyp) (hst : S.Asc512Standing)
    (hsp : S.Asc512SpSix) (hSym : S14.Asc512SymStmt) (hP : S14.Asc512PbarStmt)
    (θ : S.LbarAsc ≃* Sp62) : fixSpace (frameL S θ).X = ⊥ := by
  have := finite_Qt S
  have hY : (frameL S θ).Y₁ ≠ 1 := fun h => frS_zero_ne_one (kappa_injective S θ
    (h.trans (map_one (kappa S θ)).symm))
  have hX : (frameL S θ).X ≠ 1 := fun h => frS_eight_ne_one (kappa_injective S θ
    (h.trans (map_one (kappa S θ)).symm))
  have hev : Even (finrank (ZMod 2) (commSpace (frameL S θ).S₁)) :=
    even_of_mem_lbar S hS (psiS0 S θ (frS 1)).2
  rcases (frameL S θ).fpf_or_fixed S.q_nondegenerate (finrank_eq_eight S hsp.1) hY hX hev with
    h | ⟨f₀, -, hq, hfix⟩
  · exact h
  · exact (false_of_fixL S hS hst hsp hSym hP hq (mem_fixL_of_fixedByFrame S θ hfix)).elim

theorem frameL_X_mem (θ : S.LbarAsc ≃* Sp62) :
    ∃ x ∈ S.LbarAsc, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) = (frameL S θ).X :=
  ⟨_, (psiS0 S θ (frS 8)).2, rfl⟩

end CFSG.LargeExtraspecial.AS35QCo
