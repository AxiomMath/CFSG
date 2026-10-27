module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbA17e
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17Y

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma l17_tauom_le_K (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({tau, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
  rw [Subgroup.closure_le]
  rintro a (ha : a ∈ ({tau, om} : Set G))
  rcases ha with rfl | rfl
  · exact (l17_mem_K hc).2.1
  · exact (l17_mem_K hc).2.2.1

private lemma l17_tauom_normalizes_P (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ k ∈ closure ({tau, om} : Set G), ∀ h ∈ ctxP t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxP t tau x₁ x₂ rho := fun k hk h hh =>
  (l17_P_normal hc).2 k (l17_tauom_le_K hc hk) h hh

private lemma l17_conj_tauom_by_t (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ closure ({tau, om} : Set G), t * a * t⁻¹ ∈ closure ({tau, om} : Set G) := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc
  have ht2' : t * t = 1 := by rwa [pow_two] at ht2
  have hom2' : om * om = 1 := by rwa [pow_two] at hom2
  have htau_gen : t * tau * t⁻¹ ∈ closure ({tau, om} : Set G) := by
    have h : t * tau * t⁻¹ = tau := by rw [ht_tau]; group
    rw [h]; exact Subgroup.subset_closure (by simp)
  have hom_gen : t * om * t⁻¹ ∈ closure ({tau, om} : Set G) := by
    have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_left hom2'
    have h : om * t * om = t * tau := by simpa [hom_inv] using hom_t
    have key : (t * om * t) * om = tau := by
      calc (t * om * t) * om = t * (om * t * om) := by group
        _ = t * (t * tau) := by rw [h]
        _ = tau := by rw [← mul_assoc, ht2', one_mul]
    have htomt : t * om * t = tau * om := by
      calc t * om * t = (t * om * t) * (om * om) := by rw [hom2', mul_one]
        _ = ((t * om * t) * om) * om := by group
        _ = tau * om := by rw [key]
    have hfin : t * om * t⁻¹ = tau * om := by
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left ht2']; exact htomt
    rw [hfin]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact htau_gen
      · exact hom_gen
  | one => simpa using Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
      have heq : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ihx =>
      have heq : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      rw [heq]
      exact Subgroup.inv_mem _ ihx

private lemma l17_lam_fix_tauom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ closure ({tau, om} : Set G), lam * a * lam⁻¹ = a := by
  obtain ⟨hlamt, hlamtau, hlamom⟩ := l17_lam_comm hc
  have hle : closure ({tau, om} : Set G) ≤ centralizer ({lam} : Set G) := by
    rw [Subgroup.closure_le]
    rintro a (ha : a ∈ ({tau, om} : Set G))
    rcases ha with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hlamtau.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hlamom.symm
  intro a ha
  have hcomm : lam * a = a * lam := Subgroup.mem_centralizer_iff.mp (hle ha) lam rfl
  rw [hcomm]; group

theorem l17_E0_le_cent (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxE0 t tau x₁ x₂ rho om ≤
      centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  rw [ctxE0]
  refine sup_le ?_ ?_
  · intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (l17_P_cent_Y hc p hp a ha).symm
  · rw [Subgroup.closure_le]
    rintro a (ha : a ∈ ({tau, om} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hc.tau_cent_Y y hy).symm)
    · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hc.om_cent_Y y hy).symm)

theorem l17_mem_E0 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {x : G} :
    x ∈ ctxE0 t tau x₁ x₂ rho om ↔
      ∃ p ∈ ctxP t tau x₁ x₂ rho, ∃ a ∈ closure ({tau, om} : Set G), x = p * a := by
  rw [ctxE0]
  exact mem_sup_iff_of_normalizes (l17_tauom_normalizes_P hc)

theorem l17_E0_le_sylow (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxE0 t tau x₁ x₂ rho om ≤ 𝒮 := by
  rw [ctxE0]
  refine sup_le (l17_P_le_sylow hc) ?_
  rw [Subgroup.closure_le]
  rintro a (ha : a ∈ ({tau, om} : Set G))
  rcases ha with rfl | rfl
  · exact (l17_T_le_sylow hc).2.1
  · exact (l17_T_le_sylow hc).2.2.1

theorem l17_card_tauom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(closure ({tau, om} : Set G)) = 4 := by
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc
  have htau_ne : tau ≠ 1 := fun h => htau_not (by rw [h]; exact Subgroup.one_mem _)
  have htau_om : tau * om = om * tau := (om_tau_comm ht2 hom2 htau2 ht_tau hom_t).symm
  exact card_closure_pair htau2 htau_ne hom2 htau_om (fun hmem =>
    hc.om_not_mem (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)) hmem))

theorem l17_card_E0 (hc : Ctx17 t L S x₁ x₂ lam rho tau om 𝒮) :
    Nat.card ↥(ctxE0 t tau x₁ x₂ rho om) = 2 ^ 10 := by
  have hbot : ctxP t tau x₁ x₂ rho ⊓ closure ({tau, om} : Set G) = ⊥ := by
    rw [inf_comm]
    exact l17_A_inf_P hc.toCtx13
  rw [ctxE0]
  rw [card_sup_eq_mul (l17_tauom_normalizes_P hc.toCtx13) hbot,
    (l17_card_P hc).1, l17_card_tauom hc.toCtx13]
  norm_num

theorem l17_not_cent_Y (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∉ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) ∧
      lam ∉ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) ∧
      t * lam ∉ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
  have hyY : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho :=
    l17_V_le_Y hc (Subgroup.subset_closure (by simp))
  have hz_ne : (x₁ * x₂) ^ 2 ≠ 1 := (l17_yz_ne hc).2.1
  have hcancel : ∀ b : G, x₁ ^ 2 * b = x₁ ^ 2 → b = 1 := fun b h =>
    mul_left_cancel (show x₁ ^ 2 * b = x₁ ^ 2 * 1 by rw [h, mul_one])
  have ht_not : t ∉ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro ht
    have hYle : ctxYq t tau x₁ x₂ rho ≤ centralizer ({t} : Set G) := by
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp ht y hy)
    have hYeq : ctxYq t tau x₁ x₂ rho = fourGrp x₁ x₂ :=
      (inf_eq_left.mpr hYle).symm.trans hc.Y_cent.1
    have hcardY := l17_card_Y hc
    have hcardV := l17_card_V hc
    rw [hYeq] at hcardY
    omega
  have hlam_not : lam ∉ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro hlam
    have hcomm : x₁ ^ 2 * lam = lam * x₁ ^ 2 :=
      Subgroup.mem_centralizer_iff.mp hlam (x₁ ^ 2) hyY
    have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by rw [← hcomm]; group
    refine hz_ne (hcancel ((x₁ * x₂) ^ 2) ?_)
    rw [← l17_lam_y hc, hconj]
  have hg_not : t * lam ∉ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    intro hg
    have hcomm : x₁ ^ 2 * (t * lam) = (t * lam) * x₁ ^ 2 :=
      Subgroup.mem_centralizer_iff.mp hg (x₁ ^ 2) hyY
    have hconj : (t * lam) * x₁ ^ 2 * (t * lam)⁻¹ = x₁ ^ 2 := by rw [← hcomm]; group
    refine hz_ne (hcancel ((x₁ * x₂) ^ 2) ?_)
    rw [← (l17_g_facts hc).2.2.1, hconj]
  exact ⟨ht_not, hlam_not, hg_not⟩

theorem l17_not_mem_E0 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∉ ctxE0 t tau x₁ x₂ rho om ∧ lam ∉ ctxE0 t tau x₁ x₂ rho om ∧
      t * lam ∉ ctxE0 t tau x₁ x₂ rho om := by
  obtain ⟨ht, hlam, hg⟩ := l17_not_cent_Y hc
  exact ⟨fun h => ht (l17_E0_le_cent hc h),
    fun h => hlam (l17_E0_le_cent hc h),
    fun h => hg (l17_E0_le_cent hc h)⟩

theorem l17_E0_normalized (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ e ∈ ctxE0 t tau x₁ x₂ rho om,
      t * e * t⁻¹ ∈ ctxE0 t tau x₁ x₂ rho om ∧ lam * e * lam⁻¹ ∈ ctxE0 t tau x₁ x₂ rho om := by
  intro e he
  obtain ⟨p, hp, a, ha, rfl⟩ := (l17_mem_E0 hc).mp he
  refine ⟨?_, ?_⟩
  · have htp : t * p * t⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
      (l17_P_normal hc).2 t (l17_mem_K hc).1 p hp
    have hta : t * a * t⁻¹ ∈ closure ({tau, om} : Set G) := l17_conj_tauom_by_t hc a ha
    have heq : t * (p * a) * t⁻¹ = (t * p * t⁻¹) * (t * a * t⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htp) (Subgroup.mem_sup_right hta)
  · have hlp : lam * p * lam⁻¹ ∈ ctxP t tau x₁ x₂ rho :=
      (l17_P_normal hc).2 lam (l17_mem_K hc).2.2.2.1 p hp
    have hla : lam * a * lam⁻¹ = a := l17_lam_fix_tauom hc a ha
    have heq : lam * (p * a) * lam⁻¹ = (lam * p * lam⁻¹) * a := by
      calc lam * (p * a) * lam⁻¹
          = (lam * p * lam⁻¹) * (lam * a * lam⁻¹) := by group
        _ = (lam * p * lam⁻¹) * a := by rw [hla]
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlp) (Subgroup.mem_sup_right ha)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
