module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AR2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAD
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2e

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

variable (H : AD S T₁)

@[expose] noncomputable def R : Subgroup X := MA.T1.map H.ι

theorem ι_mem_R {a : MA} (ha : MA.inT1 a = true) : H.ι a ∈ H.R := ⟨a, ha, rfl⟩

theorem mem_R_iff {g : X} : g ∈ H.R ↔ ∃ a : MA, MA.inT1 a = true ∧ H.ι a = g := Iff.rfl

theorem E₁_le_R : S.E S.y ≤ H.R := by
  refine (closure_le _).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h | h <;> rw [h]
  · rw [← H.ι_z]; exact H.ι_mem_R (by decide +kernel)
  · rw [← H.ι_y]; exact H.ι_mem_R (by decide +kernel)
  · have h1 := H.ι_mem_R (a := MA.t) (by decide +kernel)
    rwa [H.ι_t] at h1
  · rw [← H.ι_k]; exact H.ι_mem_R (by decide +kernel)

theorem conj_mem_R_of_mem_S₁ {s τ : X} (hs : s ∈ H.G.D₁.S₁) (hτ : τ ∈ H.R) :
    s * τ * s⁻¹ ∈ H.R := by
  obtain ⟨a, rfl⟩ := H.mem_range_of_mem_S₁ hs
  obtain ⟨b, hb, rfl⟩ := hτ
  rw [← map_inv, ← map_mul, ← map_mul]
  exact H.ι_mem_R (MA.T1_normal a b hb)

omit [Finite X] in
theorem conj_mem_centralizer {R' : Subgroup X} {g c : X} (hgR : ∀ τ ∈ R', g⁻¹ * τ * g ∈ R')
    (hc : c ∈ centralizer (R' : Set X)) : g * c * g⁻¹ ∈ centralizer (R' : Set X) := by
  rw [mem_centralizer_iff]
  intro τ hτ
  have h1 := mem_centralizer_iff.mp hc _ (hgR τ hτ)
  calc τ * (g * c * g⁻¹) = g * ((g⁻¹ * τ * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * τ * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * τ := by group

theorem S₁_le_normalizer_C : H.G.D₁.S₁ ≤ normalizer (centralizer (H.R : Set X) : Set X) := by
  intro s hs
  refine mem_normalizer_of_conj_le fun c hc => ?_
  refine conj_mem_centralizer (fun τ hτ => ?_) hc
  have := H.conj_mem_R_of_mem_S₁ (inv_mem hs) hτ
  rwa [inv_inv] at this

theorem centralizer_R_le : centralizer (H.R : Set X) ≤ normalizer (S.E S.y : Set X) := by
  intro c hc
  refine mem_normalizer_of_conj_le fun e he => ?_
  rw [(mem_centralizer_iff.mp hc e (H.E₁_le_R he)).symm, mul_inv_cancel_right]
  exact he

@[expose] noncomputable def K₁ : Subgroup X := centralizer (H.R : Set X) ⊔ H.G.D₁.S₁

theorem K₁_le : H.K₁ ≤ normalizer (S.E S.y : Set X) := sup_le H.centralizer_R_le H.G.D₁.S₁_le

theorem S₁_max_K₁ : ∀ Q : Subgroup X, IsPGroup 2 Q → H.G.D₁.S₁ ≤ Q → Q ≤ H.K₁ →
    Q = H.G.D₁.S₁ :=
  fun Q hQ hle hQK => H.G.D₁.S₁_maximal Q hQ hle (hQK.trans H.K₁_le)

theorem w₂_mul_w₂ : H.ι MA.w₂ * H.ι MA.w₂ = 1 := by
  rw [← map_mul, show MA.w₂ * MA.w₂ = 1 by decide +kernel, map_one]

namespace DC

variable {H} (D : H.DC)

theorem ι_tE_inv : (H.ι (tE D.e))⁻¹ = H.ι (tE D.e) := by rw [← map_inv, tE_inv]

theorem conj_inv {a : MA} (ha : MA.inT1 a = true) :
    H.ι (dci D.e D.c₂ a) = D.d₀⁻¹ * H.ι a * D.d₀ := by
  have h1 := D.conj a ha
  have e1 : H.ι (tE D.e) = (D.d₀ * D.d₀)⁻¹ := by rw [D.sq, D.ι_tE_inv]
  have e2 : H.ι (tE D.e) = D.d₀ * D.d₀ := D.sq.symm
  rw [dci, map_mul, map_mul, h1]
  nth_rewrite 1 [e1]
  rw [e2]
  group

@[expose] noncomputable def g₁ : X := D.d₀ * H.ι MA.w₂ * D.d₀⁻¹

theorem g₁_mul_g₁ : D.g₁ * D.g₁ = 1 := by
  rw [g₁, show D.d₀ * H.ι MA.w₂ * D.d₀⁻¹ * (D.d₀ * H.ι MA.w₂ * D.d₀⁻¹) =
    D.d₀ * (H.ι MA.w₂ * H.ι MA.w₂) * D.d₀⁻¹ by group, H.w₂_mul_w₂]; group

theorem g₁_inv : D.g₁⁻¹ = D.g₁ := inv_eq_of_mul_eq_one_right D.g₁_mul_g₁

theorem g₁_conj {a : MA} (ha : MA.inT1 a = true) :
    D.g₁ * H.ι a * D.g₁⁻¹ = H.ι (pAct D.e D.c₂ a) := by
  have h1 := D.conj_inv ha
  have h2 : MA.inT1 (MA.w₂ * dci D.e D.c₂ a * MA.w₂⁻¹) = true :=
    MA.T1_normal _ _ (dci_T1 D.e D.c₂ D.hc₂ a)
  rw [pAct, D.conj _ h2, map_mul, map_mul, map_inv, h1, g₁]
  group

theorem g₁_conj_mem_R {τ : X} (hτ : τ ∈ H.R) : D.g₁ * τ * D.g₁⁻¹ ∈ H.R := by
  obtain ⟨a, ha, rfl⟩ := hτ
  rw [D.g₁_conj ha]
  exact H.ι_mem_R (pAct_T1 D.e D.c₂ D.hc₂ a)

theorem g₁w₂_conj {a : MA} (ha : MA.inT1 a = true) :
    (D.g₁ * H.ι MA.w₂ * D.g₁⁻¹) * H.ι a * (D.g₁ * H.ι MA.w₂ * D.g₁⁻¹)⁻¹ =
      H.ι (MA.condWit (cOne D.e)) * H.ι a * (H.ι (MA.condWit (cOne D.e)))⁻¹ := by
  have h1 : D.g₁⁻¹ * H.ι a * D.g₁ = H.ι (pAct D.e D.c₂ a) := by
    have h := D.g₁_conj ha
    rw [D.g₁_inv] at h ⊢
    exact h
  have h2 : MA.inT1 (MA.w₂ * pAct D.e D.c₂ a * MA.w₂⁻¹) = true :=
    MA.T1_normal _ _ (pAct_T1 D.e D.c₂ D.hc₂ a)
  rw [show (D.g₁ * H.ι MA.w₂ * D.g₁⁻¹) * H.ι a * (D.g₁ * H.ι MA.w₂ * D.g₁⁻¹)⁻¹ =
    D.g₁ * (H.ι MA.w₂ * (D.g₁⁻¹ * H.ι a * D.g₁) * (H.ι MA.w₂)⁻¹) * D.g₁⁻¹ by group, h1,
    ← map_inv, ← map_mul, ← map_mul, D.g₁_conj h2, pAct_w₂ D.e D.c₂ D.hc₂ a ha, map_mul,
    map_mul, map_inv]

theorem conj_S₁_le_K₁ : H.G.D₁.S₁.map (MulAut.conj D.g₁).toMonoidHom ≤ H.K₁ := by
  rw [← H.range_ι, MonoidHom.range_eq_map, map_map, ← MonoidHom.range_eq_map]
  refine MA.range_le _ fun g hg => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  have hT : ∀ a : MA, MA.inT1 a = true → D.g₁ * H.ι a * D.g₁⁻¹ ∈ H.K₁ := fun a ha => by
    rw [D.g₁_conj ha]; exact mem_sup_right (H.ι_mem_S₁ _)
  simp only [MA.gens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hC : (H.ι (MA.condWit (cOne D.e)))⁻¹ * (D.g₁ * H.ι MA.w₂ * D.g₁⁻¹) ∈
        centralizer (H.R : Set X) := by
      refine inv_mul_mem_centralizer fun τ hτ => ?_
      obtain ⟨a, ha, rfl⟩ := hτ
      exact D.g₁w₂_conj ha
    rw [show D.g₁ * H.ι MA.w₂ * D.g₁⁻¹ = H.ι (MA.condWit (cOne D.e)) *
      ((H.ι (MA.condWit (cOne D.e)))⁻¹ * (D.g₁ * H.ι MA.w₂ * D.g₁⁻¹)) by group]
    exact mul_mem (mem_sup_right (H.ι_mem_S₁ _)) (mem_sup_left hC)
  all_goals exact hT _ (by decide +kernel)

structure PD (D : H.DC) where
  p : X
  hN : p ∈ normalizer (H.G.D₁.S₁ : Set X)
  hact : ∀ τ ∈ H.R, p * τ * p⁻¹ = D.g₁ * τ * D.g₁⁻¹
  a : ℕ
  hpow : p ^ 2 ^ a = 1

theorem nonempty_PD : Nonempty D.PD := by
  obtain ⟨c, hc, hN⟩ := exists_centralizer_mul_mem_normalizer H.S₁_le_normalizer_C
    H.G.D₁.isPGroup_S₁ H.S₁_max_K₁ D.conj_S₁_le_K₁
  obtain ⟨m, hm, a, hpow⟩ := exists_odd_pow_two_elt (c * D.g₁)
  have hgR : ∀ τ ∈ H.R, D.g₁ * τ * D.g₁⁻¹ ∈ H.R := fun τ hτ => D.g₁_conj_mem_R hτ
  have hT : ∀ τ ∈ H.R, (c * D.g₁) * τ * (c * D.g₁)⁻¹ = D.g₁ * τ * D.g₁⁻¹ :=
    fun τ hτ => conj_centralizer_mul hc hgR hτ
  have hcR : ∀ τ ∈ H.R, (c * D.g₁) * τ * (c * D.g₁)⁻¹ ∈ H.R := fun τ hτ => by
    rw [hT τ hτ]; exact hgR τ hτ
  refine ⟨⟨(c * D.g₁) ^ m, pow_mem hN m, fun τ hτ => ?_, a, hpow⟩⟩
  rw [(conj_pow_eq_of_conj_eq hT hcR m τ hτ).1, pow_odd_of_sq D.g₁_mul_g₁ hm]

end DC

end AD

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
