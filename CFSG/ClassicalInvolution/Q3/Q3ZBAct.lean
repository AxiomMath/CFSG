module

public import CFSG.ClassicalInvolution.Q3.Q3ZBHeisAut
public import CFSG.ClassicalInvolution.Q3.Q3ZBRigid
public import CFSG.ClassicalInvolution.Q3.Q3ZACross

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3ZA
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.Q3.Q3Z (negOne negOne_mem_center longInv_mul_self)
open scoped MatrixGroups
open Matrix

theorem heis_comm_vec (x : Heis) (w : V4) :
    x * Heis.vec w * x⁻¹ * (Heis.vec w)⁻¹ = ⟨form x.v w, 0⟩ := by
  obtain ⟨c, v⟩ := x
  have h1 : form w v = -form v w := form_antisymm v w
  have h2 : form v v = 0 := form_self v
  have h3 : form w w = 0 := form_self w
  refine Heis.ext ?_ ?_
  · simp only [Heis.mul_def, Heis.inv_def, Heis.vec, form_add_left, Heis.form_neg_left',
      Heis.form_neg_right', h1, h2, h3]
    linear_combination (form v w) * f3_three_eq_zero
  · simp only [Heis.mul_def, Heis.inv_def, Heis.vec]
    abel

theorem heis_injective_of_center_ne_one {G : Type*} [Group G] (φ : Heis →* G)
    (hz : φ Heis.center ≠ 1) : Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  have hc : ∀ c : F3, φ ⟨c, 0⟩ = 1 → c = 0 := by
    intro c hc
    rcases f3_eq_zero_or_one_or_neg_one c with h | h | h
    · exact h
    · subst h
      exact absurd hc hz
    · subst h
      have e : (⟨-1, 0⟩ : Heis) = Heis.center⁻¹ := by
        refine Heis.ext rfl ?_
        simp [Heis.inv_def, Heis.center]
      rw [e, map_inv, inv_eq_one] at hc
      exact absurd hc hz
  have hnd : ∀ v : V4, v ≠ 0 → ∃ w : V4, form v w ≠ 0 := by
    intro v hv
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
    refine ⟨Pi.single (par i) 1, ?_⟩
    rw [form_single_right, par_par]
    exact mul_ne_zero hi (sgn_ne_zero _)
  intro x hx
  have hv : x.v = 0 := by
    by_contra hv
    obtain ⟨w, hw⟩ := hnd x.v hv
    have h : φ ⟨form x.v w, 0⟩ = 1 := by
      rw [← heis_comm_vec x w]
      simp [hx]
    exact hw (hc _ h)
  have hx' : x = ⟨x.c, 0⟩ := Heis.ext rfl hv
  have hcx : x.c = 0 := hc x.c (by rw [← hx']; exact hx)
  exact Heis.ext hcx hv

theorem hom_ext_heis {G : Type*} [Group G] {ψ₁ ψ₂ : Heis →* G}
    (hz : ψ₁ Heis.center = ψ₂ Heis.center) (h0 : ψ₁ (Heis.vec bE0) = ψ₂ (Heis.vec bE0))
    (h1 : ψ₁ (Heis.vec bE1) = ψ₂ (Heis.vec bE1)) (h2 : ψ₁ (Heis.vec bF0) = ψ₂ (Heis.vec bF0))
    (h3 : ψ₁ (Heis.vec bF1) = ψ₂ (Heis.vec bF1)) : ψ₁ = ψ₂ := by
  refine MonoidHom.eq_of_eqOn_dense heis_closure_eq_top fun x hx => ?_
  simp only [heisGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [hz, h0, h1, h2, h3]

theorem range_eq_closure {G : Type*} [Group G] (φ : Heis →* G) {a e0 f0 e1 f1 : G}
    (hz : φ Heis.center = a⁻¹) (h0 : φ (Heis.vec bE0) = e0) (h1 : φ (Heis.vec bE1) = e1)
    (h2 : φ (Heis.vec bF0) = f0⁻¹) (h3 : φ (Heis.vec bF1) = f1⁻¹) :
    φ.range = Subgroup.closure {a, e0, f0, e1, f1} := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    have hm : m ∈ Subgroup.closure heisGens := by
      rw [heis_closure_eq_top]
      exact Subgroup.mem_top m
    have hle : Subgroup.closure heisGens ≤
        (Subgroup.closure {a, e0, f0, e1, f1}).comap φ := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [heisGens, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · rw [hz]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      · rw [h0]
        exact Subgroup.subset_closure (by simp)
      · rw [h1]
        exact Subgroup.subset_closure (by simp)
      · rw [h2]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      · rw [h3]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    exact hle hm
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact ⟨Heis.center⁻¹, by rw [map_inv, hz, inv_inv]⟩
    · exact ⟨_, h0⟩
    · exact ⟨(Heis.vec bF0)⁻¹, by rw [map_inv, h2, inv_inv]⟩
    · exact ⟨_, h1⟩
    · exact ⟨(Heis.vec bF1)⁻¹, by rw [map_inv, h3, inv_inv]⟩

section GenAct

variable {G : Type} [Group G]

theorem phi_vec_add_EF (φ : Heis →* G) (k : Fin 2) :
    φ (Heis.vec ((Pi.single (Sum.inl k) (1 : F3) : V4) + Pi.single (Sum.inr k) 1)) =
      φ Heis.center * (φ (Heis.vec (Pi.single (Sum.inl k) (1 : F3))) *
        φ (Heis.vec (Pi.single (Sum.inr k) (1 : F3)))) := by
  have h := congrArg φ
    (vec_add_eq (Pi.single (Sum.inl k) (1 : F3) : V4) (Pi.single (Sum.inr k) 1))
  have e : (-(2 * 1) : F3) = 1 := by linear_combination (-1 : F3) * three_eq_zero_f3
  rw [map_mul, map_mul, form_single_inl_inr k, e] at h
  exact h

theorem act_of_vec_gens {θ : StatedSp 2 F3 →* G} {φ : Heis →* G} {s : StatedSp 2 F3}
    (hz : θ s * φ Heis.center = φ Heis.center * θ s)
    (h0 : θ s * φ (Heis.vec bE0) * (θ s)⁻¹ = φ (Heis.vec (mat 2 F3 s *ᵥ bE0)))
    (h1 : θ s * φ (Heis.vec bE1) * (θ s)⁻¹ = φ (Heis.vec (mat 2 F3 s *ᵥ bE1)))
    (h2 : θ s * φ (Heis.vec bF0) * (θ s)⁻¹ = φ (Heis.vec (mat 2 F3 s *ᵥ bF0)))
    (h3 : θ s * φ (Heis.vec bF1) * (θ s)⁻¹ = φ (Heis.vec (mat 2 F3 s *ᵥ bF1))) :
    ∀ x, θ s * φ x * (θ s)⁻¹ = φ (heisAct s x) := by
  have hfg : (MulAut.conj (θ s)).toMonoidHom.comp φ = φ.comp (heisAct s).toMonoidHom := by
    refine hom_ext_heis ?_ h0 h1 h2 h3
    show θ s * φ Heis.center * (θ s)⁻¹ = φ (heisAct s Heis.center)
    rw [heisAct_center]
    exact mul_inv_eq_iff_eq_mul.2 hz
  intro x
  exact DFunLike.congr_fun hfg x

theorem heisAct_negOne_vec (v : V4) : heisAct (negOne 2 F3) (Heis.vec v) = Heis.vec (-v) :=
  heisAct_negOne (Heis.vec v)

theorem phi_heisAct_negOne {φ : Heis →* G} {w : G}
    (hz : w * φ Heis.center = φ Heis.center * w)
    (h0 : w * φ (Heis.vec bE0) * w⁻¹ = (φ (Heis.vec bE0))⁻¹)
    (h1 : w * φ (Heis.vec bE1) * w⁻¹ = (φ (Heis.vec bE1))⁻¹)
    (h2 : w * φ (Heis.vec bF0) * w⁻¹ = (φ (Heis.vec bF0))⁻¹)
    (h3 : w * φ (Heis.vec bF1) * w⁻¹ = (φ (Heis.vec bF1))⁻¹) (x : Heis) :
    φ (heisAct (negOne 2 F3) x) = w * φ x * w⁻¹ := by
  have hfg : φ.comp (heisAct (negOne 2 F3)).toMonoidHom = (MulAut.conj w).toMonoidHom.comp φ := by
    refine hom_ext_heis ?_ ?_ ?_ ?_ ?_
    · show φ (heisAct (negOne 2 F3) Heis.center) = w * φ Heis.center * w⁻¹
      rw [heisAct_center]
      exact (mul_inv_eq_iff_eq_mul.2 hz).symm
    · show φ (heisAct (negOne 2 F3) (Heis.vec bE0)) = w * φ (Heis.vec bE0) * w⁻¹
      rw [heisAct_negOne_vec]
      exact (ph_neg φ bE0).trans h0.symm
    · show φ (heisAct (negOne 2 F3) (Heis.vec bE1)) = w * φ (Heis.vec bE1) * w⁻¹
      rw [heisAct_negOne_vec]
      exact (ph_neg φ bE1).trans h1.symm
    · show φ (heisAct (negOne 2 F3) (Heis.vec bF0)) = w * φ (Heis.vec bF0) * w⁻¹
      rw [heisAct_negOne_vec]
      exact (ph_neg φ bF0).trans h2.symm
    · show φ (heisAct (negOne 2 F3) (Heis.vec bF1)) = w * φ (Heis.vec bF1) * w⁻¹
      rw [heisAct_negOne_vec]
      exact (ph_neg φ bF1).trans h3.symm
  exact DFunLike.congr_fun hfg x

end GenAct

section Endo

variable {G : Type} [Group G]

theorem exists_mulEquiv_of_conj {H : Type} [Group H] {φ : H →* G} (hφ : Function.Injective φ)
    {x : G} (h : ∀ m, ∃ m', φ m' = x * φ m * x⁻¹) (h' : ∀ m, ∃ m', φ m' = x⁻¹ * φ m * x) :
    ∃ α : H ≃* H, ∀ m, φ (α m) = x * φ m * x⁻¹ := by
  choose f hf using h
  choose g hg using h'
  refine ⟨{ toFun := f
            invFun := g
            left_inv := fun m => hφ ?_
            right_inv := fun m => hφ ?_
            map_mul' := fun m m' => hφ ?_ }, hf⟩
  · rw [hg, hf]
    group
  · rw [hf, hg]
    group
  · rw [hf, map_mul, map_mul, hf, hf]
    group

theorem exists_heisAct_conj {φ : Heis →* G} (hφ : Function.Injective φ)
    {θ : StatedSp 2 F3 →* G} (hN : ∀ s m, ∃ m', φ m' = θ s * φ m * (θ s)⁻¹)
    (hc : ∀ s, θ s * φ Heis.center = φ Heis.center * θ s)
    (hτ : ∀ x, φ (heisAct (negOne 2 F3) x) = θ (negOne 2 F3) * φ x * (θ (negOne 2 F3))⁻¹)
    (s : StatedSp 2 F3) : ∃ t : StatedSp 2 F3, ∀ x, θ s * φ x * (θ s)⁻¹ = φ (heisAct t x) := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_of_conj hφ (hN s)
    (fun m => by simpa [map_inv] using hN s⁻¹ m)
  have hz : α Heis.center = Heis.center := by
    apply hφ
    rw [hα]
    exact mul_inv_eq_iff_eq_mul.2 (hc s)
  have hcomm : θ s * θ (negOne 2 F3) = θ (negOne 2 F3) * θ s := by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 (negOne_mem_center (n := 2) (F := F3)) s]
  have hτ' : ∀ x, α (heisAct (negOne 2 F3) x) = heisAct (negOne 2 F3) (α x) := by
    intro x
    apply hφ
    rw [hα, hτ, hτ, hα]
    calc θ s * (θ (negOne 2 F3) * φ x * (θ (negOne 2 F3))⁻¹) * (θ s)⁻¹
        = (θ s * θ (negOne 2 F3)) * φ x * (θ s * θ (negOne 2 F3))⁻¹ := by group
      _ = (θ (negOne 2 F3) * θ s) * φ x * (θ (negOne 2 F3) * θ s)⁻¹ := by rw [hcomm]
      _ = θ (negOne 2 F3) * (θ s * φ x * (θ s)⁻¹) * (θ (negOne 2 F3))⁻¹ := by group
  obtain ⟨t, ht⟩ := exists_heisAct_of_aut α hz hτ'
  exact ⟨t, fun x => by rw [← hα, ht]⟩

theorem eq_of_conj_act {φ : Heis →* G} (hφ : Function.Injective φ) {θ : StatedSp 2 F3 →* G}
    {s t t' : StatedSp 2 F3} (h : ∀ x, θ s * φ x * (θ s)⁻¹ = φ (heisAct t x))
    (h' : ∀ x, θ s * φ x * (θ s)⁻¹ = φ (heisAct t' x)) : t = t' := by
  apply heisAct_injective
  exact MulEquiv.ext fun x => hφ ((h x).symm.trans (h' x))

theorem exists_endo_of_normalizes {φ : Heis →* G} (hφ : Function.Injective φ)
    {θ : StatedSp 2 F3 →* G} (hN : ∀ s m, ∃ m', φ m' = θ s * φ m * (θ s)⁻¹)
    (hc : ∀ s, θ s * φ Heis.center = φ Heis.center * θ s)
    (hτ : ∀ x, φ (heisAct (negOne 2 F3) x) = θ (negOne 2 F3) * φ x * (θ (negOne 2 F3))⁻¹) :
    ∃ ρ : StatedSp 2 F3 →* StatedSp 2 F3,
      ∀ s x, θ s * φ x * (θ s)⁻¹ = φ (heisAct (ρ s) x) := by
  choose ρ hρ using exists_heisAct_conj hφ hN hc hτ
  refine ⟨MonoidHom.mk' ρ fun s s' => ?_, hρ⟩
  refine eq_of_conj_act hφ (θ := θ) (s := s * s') (hρ (s * s')) fun x => ?_
  calc θ (s * s') * φ x * (θ (s * s'))⁻¹ = θ s * (θ s' * φ x * (θ s')⁻¹) * (θ s)⁻¹ := by
        rw [map_mul]
        group
    _ = θ s * φ (heisAct (ρ s') x) * (θ s)⁻¹ := by rw [hρ s' x]
    _ = φ (heisAct (ρ s) (heisAct (ρ s') x)) := hρ s _
    _ = φ (heisAct (ρ s * ρ s') x) := by rw [map_mul]; rfl

end Endo

theorem lb1_uSL_ne_one : longBlock F3 2 1 uSL ≠ 1 := by
  intro h
  have h1 := congrArg (fun g => mat 2 F3 g *ᵥ bF1) h
  simp only [lb1U_f1, map_one, Matrix.one_mulVec] at h1
  have h2 := congrFun h1 (Sum.inl 1)
  simp at h2

theorem eq_id_or_iota (ρ : StatedSp 2 F3 →* StatedSp 2 F3)
    (h0 : ∀ x, ρ (longBlock F3 2 0 x) = longBlock F3 2 0 x)
    (h1 : ∀ x, ρ (longBlock F3 2 1 x) = longBlock F3 2 1 x) :
    ρ = MonoidHom.id _ ∨ ρ = iotaHom := by
  have hz : ρ (longInv F3 2 0) = longInv F3 2 0 := h0 (-1)
  have hS3 : ρ sbU * ρ sbU * ρ sbU = 1 := by
    rw [← map_mul, ← map_mul, (pow_three' sbU).symm.trans sbU_pow_three, map_one]
  have hSz : longInv F3 2 0 * ρ sbU * longInv F3 2 0 = (ρ sbU)⁻¹ := by
    have h := congrArg ρ longInv0_sbU
    rw [map_mul, map_mul, hz, map_inv] at h
    exact h
  have hS1 : ρ sbU * longBlock F3 2 0 uSL = longBlock F3 2 0 uSL * ρ sbU := by
    have h := congrArg ρ M4
    rw [map_mul, map_mul, h0] at h
    exact h.symm
  have hS2 : ρ sbU * longBlock F3 2 1 lSL = longBlock F3 2 1 lSL * ρ sbU := by
    have h := congrArg ρ M10
    rw [map_mul, map_mul, h1] at h
    exact h.symm
  rcases rigid (ρ sbU) hS3 hSz hS1 hS2 with hS | hS | hS
  · exfalso
    have hq : ρ qSp = 1 := by
      rw [qSp, map_mul, map_mul, hS, mul_one, map_inv, mul_inv_cancel]
    have h6 := congrArg ρ M6'
    simp only [map_mul, map_inv, hq, h1, one_mul, mul_one] at h6
    have h7 : (longBlock F3 2 1 uSL)⁻¹ * (ρ sbL)⁻¹ = 1 * (ρ sbL)⁻¹ := by
      rw [one_mul]
      exact h6.symm
    exact lb1_uSL_ne_one (inv_eq_one.1 (mul_right_cancel h7))
  · left
    exact hom_ext_H_sbU (fun x => h0 x) (fun x => h1 x) hS
  · right
    refine hom_ext_H_sbU (fun x => ?_) (fun x => ?_) ?_
    · rw [h0, iota_lb0]
    · rw [h1, iota_lb1]
    · rw [hS]
      exact ((iota_sb_usl 1).trans (sb_usl_inv 1).symm).symm

theorem iota_iota (s : StatedSp 2 F3) : iotaHom (iotaHom s) = s := by
  rw [iota_apply, iota_apply, longInv_inv]
  calc longInv F3 2 0 * (longInv F3 2 0 * s * longInv F3 2 0) * longInv F3 2 0
      = (longInv F3 2 0 * longInv F3 2 0) * s * (longInv F3 2 0 * longInv F3 2 0) := by group
    _ = s := by rw [longInv_mul_self, one_mul, mul_one]

theorem lb0l_e0 (c : F3) : mat 2 F3 (longBlock F3 2 0 (lsl c)) *ᵥ bE0 = bE0 + c • bF0 :=
  lb_lsl_inl 0 c

theorem lb0l_f0 (c : F3) : mat 2 F3 (longBlock F3 2 0 (lsl c)) *ᵥ bF0 = bF0 := lb_lsl_inr 0 c

theorem lb0l_e1 (c : F3) : mat 2 F3 (longBlock F3 2 0 (lsl c)) *ᵥ bE1 = bE1 :=
  lb_mulVec_other 0 _ (by simp [coords])

theorem lb0l_f1 (c : F3) : mat 2 F3 (longBlock F3 2 0 (lsl c)) *ᵥ bF1 = bF1 :=
  lb_mulVec_other 0 _ (by simp [coords])

theorem lb0U_e0 : mat 2 F3 (longBlock F3 2 0 uSL) *ᵥ bE0 = bE0 := lb0u_e0 1

theorem lb0U_e1 : mat 2 F3 (longBlock F3 2 0 uSL) *ᵥ bE1 = bE1 := lb0u_e1 1

theorem lb0U_f0 : mat 2 F3 (longBlock F3 2 0 uSL) *ᵥ bF0 = bE0 + bF0 := by
  have h := lb0u_f0 1
  rwa [one_smul] at h

theorem lb0U_f1 : mat 2 F3 (longBlock F3 2 0 uSL) *ᵥ bF1 = bF1 := lb0u_f1 1

theorem lb0L_e0 : mat 2 F3 (longBlock F3 2 0 lSL) *ᵥ bE0 = bE0 + bF0 := by
  have h := lb0l_e0 1
  rwa [one_smul] at h

theorem lb0L_e1 : mat 2 F3 (longBlock F3 2 0 lSL) *ᵥ bE1 = bE1 := lb0l_e1 1

theorem lb0L_f0 : mat 2 F3 (longBlock F3 2 0 lSL) *ᵥ bF0 = bF0 := lb0l_f0 1

theorem lb0L_f1 : mat 2 F3 (longBlock F3 2 0 lSL) *ᵥ bF1 = bF1 := lb0l_f1 1

local macro "act_simp" : tactic =>
  `(tactic| simp only [map_mul, ← Matrix.mulVec_mulVec, uSL_eq, lSL_eq, sbU_eq, sbL_eq, qSp,
    sb_usl_inv, sb_lsl_inv, lb_usl_inv, sb_usl_e0, sb_usl_e1, sb_usl_f0, sb_usl_f1, sb_lsl_e0,
    sb_lsl_e1, sb_lsl_f0, sb_lsl_f1, w1_e0, w1_e1, w1_f0, w1_f1, w1i_e0, w1i_e1, w1i_f0, w1i_f1,
    lb0u_e0, lb0u_f0, lb0u_e1, lb0u_f1, lb0l_e0, lb0l_f0, lb0l_e1, lb0l_f1, lb1u_e0, lb1u_f0,
    lb1u_e1, lb1u_f1, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul,
    Matrix.mulVec_sub, map_one, Matrix.one_mulVec])

local macro "act_close" : tactic =>
  `(tactic| first
    | module
    | (match_scalars <;>
        first
        | ring1
        | linear_combination three_eq_zero_f3
        | linear_combination (-1 : F3) * three_eq_zero_f3
        | linear_combination (2 : F3) * three_eq_zero_f3
        | linear_combination (-2 : F3) * three_eq_zero_f3))

theorem lb0U_sbL_inv : longBlock F3 2 0 uSL * sbL⁻¹ =
    (longBlock F3 2 1 uSL)⁻¹ * qSp * sbL⁻¹ * longBlock F3 2 0 uSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp; try act_close)

theorem lb0L_qSp : longBlock F3 2 0 lSL * qSp =
    (longBlock F3 2 1 uSL)⁻¹ * qSp * sbL⁻¹ * longBlock F3 2 0 lSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp; try act_close)

theorem lb0L_sbL : longBlock F3 2 0 lSL * sbL = sbL * longBlock F3 2 0 lSL := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp; try act_close)

theorem iota_qSp : iotaHom qSp = qSp⁻¹ := by
  have h1 : iotaHom weyl₁ = weyl₁ := iota_lb1 wSL
  have h2 : iotaHom sbU = sbU⁻¹ := (iota_sb_usl 1).trans (sb_usl_inv 1).symm
  show iotaHom (weyl₁ * sbU * weyl₁⁻¹) = (weyl₁ * sbU * weyl₁⁻¹)⁻¹
  rw [map_mul, map_mul, map_inv, h1, h2]
  group

theorem conj_longInv0_qSp : longInv F3 2 0 * qSp * (longInv F3 2 0)⁻¹ = qSp⁻¹ := iota_qSp

theorem conj_longInv0_sbU : longInv F3 2 0 * sbU * (longInv F3 2 0)⁻¹ = sbU⁻¹ :=
  (iota_sb_usl 1).trans (sb_usl_inv 1).symm

theorem conj_longInv0_sbL : longInv F3 2 0 * sbL * (longInv F3 2 0)⁻¹ = sbL⁻¹ :=
  (iota_sb_lsl 1).trans (sb_lsl_inv 1).symm

section Hub

variable {G : Type} [Group G]

theorem heisRels_of_hub {A B : StatedSp 2 F3 →* G}
    (hub : ∀ x, A (longBlock F3 2 1 x) = B (longBlock F3 2 0 x))
    (e0e1 : Commute (A qSp) (B qSp)) (f0f1 : Commute (A sbL) (B sbU))
    (e0f1 : Commute (A qSp) (B sbU)) (e1f0 : Commute (B qSp) (A sbL)) :
    HeisRels (A (longBlock F3 2 1 uSL))⁻¹ (A qSp) (B qSp) (A sbL)⁻¹ (B sbU)⁻¹ := by
  have hM6 := congrArg A (comm_of_mul_eq M6')
  have hM7 := congrArg B (comm_of_mul_eq M7')
  simp only [map_inv, map_commutatorElement] at hM6 hM7
  exact
    { z_e0 := (hom_commute A M1).inv_left
      z_e1 := by
        rw [hub]
        exact (hom_commute B M2).inv_left
      z_f0 := (hom_commute A M3).inv_inv
      z_f1 := by
        rw [hub]
        exact (hom_commute B M4).inv_inv
      pow_z := by rw [inv_pow, ← map_pow, lb_uSL_pow_three, map_one, inv_one]
      pow_e0 := by rw [← map_pow, qSp_pow_three, map_one]
      pow_e1 := by rw [← map_pow, qSp_pow_three, map_one]
      pow_f0 := by rw [inv_pow, ← map_pow, sbL_pow_three, map_one, inv_one]
      pow_f1 := by rw [inv_pow, ← map_pow, sbU_pow_three, map_one, inv_one]
      comm_0 := hM6
      comm_1 := by
        rw [hub]
        exact hM7
      e0_e1 := e0e1
      f0_f1 := f0f1.inv_inv
      e0_f1 := e0f1.inv_right
      e1_f0 := e1f0.inv_right }

structure HubData (A B X : StatedSp 2 F3 →* G) (φ : Heis →* G) : Prop where
  hub : ∀ x, A (longBlock F3 2 1 x) = B (longBlock F3 2 0 x)
  end_p : ∀ x, X (longBlock F3 2 0 x) = A (longBlock F3 2 0 x)
  end_r : ∀ x, X (longBlock F3 2 1 x) = B (longBlock F3 2 1 x)
  cA : ∀ s y, Commute (A s) (B (longBlock F3 2 1 y))
  cB : ∀ s y, Commute (B s) (A (longBlock F3 2 0 y))
  cX : ∀ s y, Commute (X s) (A (longBlock F3 2 1 y))
  hz : φ Heis.center = (A (longBlock F3 2 1 uSL))⁻¹
  h0 : φ (Heis.vec bE0) = A qSp
  h1 : φ (Heis.vec bE1) = B qSp
  h2 : φ (Heis.vec bF0) = (A sbL)⁻¹
  h3 : φ (Heis.vec bF1) = (B sbU)⁻¹

namespace HubData

variable {A B X : StatedSp 2 F3 →* G} {φ : Heis →* G}

theorem center_comm_X (D : HubData A B X φ) (s : StatedSp 2 F3) :
    X s * φ Heis.center = φ Heis.center * X s := by
  rw [D.hz]
  exact (D.cX s uSL).inv_right.eq

theorem act_lb1_uSL (D : HubData A B X φ) :
    ∀ x, X (longBlock F3 2 1 uSL) * φ x * (X (longBlock F3 2 1 uSL))⁻¹ =
      φ (heisAct (longBlock F3 2 1 uSL) x) := by
  refine act_of_vec_gens (D.center_comm_X _) ?_ ?_ ?_ ?_
  · rw [lb1U_e0, D.h0, D.end_r]
    exact mul_inv_eq_iff_eq_mul.2 (D.cA qSp uSL).symm.eq
  · rw [lb1U_e1, D.h1, D.end_r]
    exact mul_inv_eq_iff_eq_mul.2 (hom_commute B M1).eq
  · rw [lb1U_f0, D.h2, D.end_r]
    exact mul_inv_eq_iff_eq_mul.2 (D.cA sbL uSL).symm.inv_right.eq
  · rw [lb1U_f1, phi_vec_add_EF φ 1, D.hz, D.h1, D.h3, D.end_r]
    have h := congrArg B M8'
    simp only [map_mul, map_inv] at h
    rw [← D.hub] at h
    rw [mul_inv_eq_iff_eq_mul, h]
    simp only [mul_assoc]

theorem act_lb1_lSL (D : HubData A B X φ) :
    ∀ x, X (longBlock F3 2 1 lSL) * φ x * (X (longBlock F3 2 1 lSL))⁻¹ =
      φ (heisAct (longBlock F3 2 1 lSL) x) := by
  refine act_of_vec_gens (D.center_comm_X _) ?_ ?_ ?_ ?_
  · rw [lb1L_e0, D.h0, D.end_r]
    exact mul_inv_eq_iff_eq_mul.2 (D.cA qSp lSL).symm.eq
  · rw [lb1L_e1, phi_vec_add_EF φ 1, D.hz, D.h1, D.h3, D.end_r]
    have h := congrArg B M9'
    simp only [map_mul, map_inv] at h
    rw [← D.hub] at h
    rw [mul_inv_eq_iff_eq_mul, h]
    simp only [mul_assoc]
  · rw [lb1L_f0, D.h2, D.end_r]
    exact mul_inv_eq_iff_eq_mul.2 (D.cA sbL lSL).symm.inv_right.eq
  · rw [lb1L_f1, D.h3, D.end_r]
    exact mul_inv_eq_iff_eq_mul.2 (hom_commute B M10).inv_right.eq

theorem act_lb0_uSL (D : HubData A B X φ) :
    ∀ x, X (longBlock F3 2 0 uSL) * φ x * (X (longBlock F3 2 0 uSL))⁻¹ =
      φ (heisAct (longBlock F3 2 0 uSL) x) := by
  refine act_of_vec_gens (D.center_comm_X _) ?_ ?_ ?_ ?_
  · rw [lb0U_e0, D.h0, D.end_p]
    exact mul_inv_eq_iff_eq_mul.2 (hom_commute A M2).eq
  · rw [lb0U_e1, D.h1, D.end_p]
    exact mul_inv_eq_iff_eq_mul.2 (D.cB qSp uSL).symm.eq
  · rw [lb0U_f0, phi_vec_add_EF φ 0, D.hz, D.h0, D.h2, D.end_p]
    have h := congrArg A lb0U_sbL_inv
    simp only [map_mul, map_inv] at h
    rw [mul_inv_eq_iff_eq_mul, h]
    simp only [mul_assoc]
  · rw [lb0U_f1, D.h3, D.end_p]
    exact mul_inv_eq_iff_eq_mul.2 (D.cB sbU uSL).symm.inv_right.eq

theorem act_lb0_lSL (D : HubData A B X φ) :
    ∀ x, X (longBlock F3 2 0 lSL) * φ x * (X (longBlock F3 2 0 lSL))⁻¹ =
      φ (heisAct (longBlock F3 2 0 lSL) x) := by
  refine act_of_vec_gens (D.center_comm_X _) ?_ ?_ ?_ ?_
  · rw [lb0L_e0, phi_vec_add_EF φ 0, D.hz, D.h0, D.h2, D.end_p]
    have h := congrArg A lb0L_qSp
    simp only [map_mul, map_inv] at h
    rw [mul_inv_eq_iff_eq_mul, h]
    simp only [mul_assoc]
  · rw [lb0L_e1, D.h1, D.end_p]
    exact mul_inv_eq_iff_eq_mul.2 (D.cB qSp lSL).symm.eq
  · rw [lb0L_f0, D.h2, D.end_p]
    exact mul_inv_eq_iff_eq_mul.2 (hom_commute A lb0L_sbL).inv_right.eq
  · rw [lb0L_f1, D.h3, D.end_p]
    exact mul_inv_eq_iff_eq_mul.2 (D.cB sbU lSL).symm.inv_right.eq

theorem negOne_conj (D : HubData A B X φ) (x : Heis) :
    φ (heisAct (negOne 2 F3) x) = A (longInv F3 2 1) * φ x * (A (longInv F3 2 1))⁻¹ := by
  have hw : A (longInv F3 2 1) = B (longInv F3 2 0) := D.hub (-1)
  refine phi_heisAct_negOne ?_ ?_ ?_ ?_ ?_ x
  · rw [D.hz]
    exact (hom_commute A (longInv_comm_lb 1 uSL)).inv_right.eq
  · rw [D.h0]
    have h := congrArg A ((conj_longInv1 qSp).trans conj_longInv0_qSp)
    simpa only [map_mul, map_inv] using h
  · rw [D.h1, hw]
    have h := congrArg B conj_longInv0_qSp
    simpa only [map_mul, map_inv] using h
  · rw [D.h2]
    have h := congrArg A ((conj_longInv1 sbL).trans conj_longInv0_sbL)
    simp only [map_mul, map_inv] at h
    calc A (longInv F3 2 1) * (A sbL)⁻¹ * (A (longInv F3 2 1))⁻¹
        = (A (longInv F3 2 1) * A sbL * (A (longInv F3 2 1))⁻¹)⁻¹ := by group
      _ = ((A sbL)⁻¹)⁻¹ := by rw [h]
  · rw [D.h3, hw]
    have h := congrArg B conj_longInv0_sbU
    simp only [map_mul, map_inv] at h
    calc B (longInv F3 2 0) * (B sbU)⁻¹ * (B (longInv F3 2 0))⁻¹
        = (B (longInv F3 2 0) * B sbU * (B (longInv F3 2 0))⁻¹)⁻¹ := by group
      _ = ((B sbU)⁻¹)⁻¹ := by rw [h]

end HubData

end Hub

theorem heisAt_or_of_normalizes {G : Type} [Group G] {A B X : StatedSp 2 F3 →* G}
    (injA : Function.Injective A)
    (hub : ∀ x, A (longBlock F3 2 1 x) = B (longBlock F3 2 0 x))
    (end_p : ∀ x, X (longBlock F3 2 0 x) = A (longBlock F3 2 0 x))
    (end_r : ∀ x, X (longBlock F3 2 1 x) = B (longBlock F3 2 1 x))
    (cA : ∀ s y, A s * B (longBlock F3 2 1 y) = B (longBlock F3 2 1 y) * A s)
    (cB : ∀ s y, B s * A (longBlock F3 2 0 y) = A (longBlock F3 2 0 y) * B s)
    (cX : ∀ s y, X s * A (longBlock F3 2 1 y) = A (longBlock F3 2 1 y) * X s)
    (negOne_X : X (negOne 2 F3) = A (longInv F3 2 1))
    (e0e1 : Commute (A qSp) (B qSp)) (f0f1 : Commute (A sbL) (B sbU))
    (e0f1 : Commute (A qSp) (B sbU)) (e1f0 : Commute (B qSp) (A sbL))
    (hnorm : ∀ s, ∀ r ∈ Subgroup.closure
        {A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU},
        X s * r * (X s)⁻¹ ∈ Subgroup.closure
        {A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU}) :
    HeisAt A B X ∨ HeisAt A B (X.comp iotaHom) := by
  obtain ⟨φ, hz, h0, h1, h2, h3⟩ :=
    exists_hom_of_rels (heisRels_of_hub hub e0e1 f0f1 e0f1 e1f0)
  have D : HubData A B X φ :=
    { hub := hub, end_p := end_p, end_r := end_r, cA := cA, cB := cB, cX := cX,
      hz := hz, h0 := h0, h1 := h1, h2 := h2, h3 := h3 }
  have ha : A (longBlock F3 2 1 uSL) ≠ 1 := fun h =>
    lb1_uSL_ne_one (injA (h.trans (map_one A).symm))
  have hφ : Function.Injective φ :=
    heis_injective_of_center_ne_one φ (by rw [hz]; exact inv_ne_one.2 ha)
  have hrange := range_eq_closure φ hz h0 h1 h2 h3
  have hN : ∀ s m, ∃ m', φ m' = X s * φ m * (X s)⁻¹ := by
    intro s m
    have hm : φ m ∈ Subgroup.closure
        {A (longBlock F3 2 1 uSL), A qSp, A sbL, B qSp, B sbU} := by
      rw [← hrange]
      exact MonoidHom.mem_range.2 ⟨m, rfl⟩
    have h := hnorm s _ hm
    rw [← hrange] at h
    exact MonoidHom.mem_range.1 h
  have hτ : ∀ x, φ (heisAct (negOne 2 F3) x) =
      X (negOne 2 F3) * φ x * (X (negOne 2 F3))⁻¹ := by
    intro x
    rw [negOne_X]
    exact D.negOne_conj x
  obtain ⟨ρ, hρ⟩ := exists_endo_of_normalizes hφ hN D.center_comm_X hτ
  have hfix : ∀ s t, (∀ x, X s * φ x * (X s)⁻¹ = φ (heisAct t x)) → ρ s = t :=
    fun s t ht => eq_of_conj_act hφ (hρ s) ht
  have hfix0 : ∀ y, ρ (longBlock F3 2 0 y) = longBlock F3 2 0 y := by
    have hU : ρ (longBlock F3 2 0 uSL) = longBlock F3 2 0 uSL := hfix _ _ D.act_lb0_uSL
    have hL : ρ (longBlock F3 2 0 lSL) = longBlock F3 2 0 lSL := hfix _ _ D.act_lb0_lSL
    intro y
    exact map_SL2_mem_of (longBlock F3 2 0) (MonoidHom.eqLocus ρ (MonoidHom.id _)) hU hL y
  have hfix1 : ∀ y, ρ (longBlock F3 2 1 y) = longBlock F3 2 1 y := by
    have hU : ρ (longBlock F3 2 1 uSL) = longBlock F3 2 1 uSL := hfix _ _ D.act_lb1_uSL
    have hL : ρ (longBlock F3 2 1 lSL) = longBlock F3 2 1 lSL := hfix _ _ D.act_lb1_lSL
    intro y
    exact map_SL2_mem_of (longBlock F3 2 1) (MonoidHom.eqLocus ρ (MonoidHom.id _)) hU hL y
  rcases eq_id_or_iota ρ hfix0 hfix1 with hρ1 | hρ1
  · left
    show HeisDatum X (A (longBlock F3 2 1 uSL))⁻¹ (A qSp) (B qSp) (A sbL)⁻¹ (B sbU)⁻¹
    refine ⟨φ, hz, h0, h1, h2, h3, fun s x => ?_⟩
    have h := hρ s x
    rw [hρ1] at h
    exact h
  · right
    show HeisDatum (X.comp iotaHom) (A (longBlock F3 2 1 uSL))⁻¹ (A qSp) (B qSp) (A sbL)⁻¹
      (B sbU)⁻¹
    refine ⟨φ, hz, h0, h1, h2, h3, fun s x => ?_⟩
    have h := hρ (iotaHom s) x
    rw [hρ1, iota_iota] at h
    exact h

end CFSG.ClassicalInvolution.Q3.Q3ZB
