module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Cj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF17a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem k18g_lam2 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : lam * lam = 1 := by
  have h := (ctx13_lam_facts hc).1
  simpa [pow_two] using h

private theorem k18g_t2 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : t * t = 1 := by
  have h := (ctx13_relations hc).1
  simpa [pow_two] using h

private theorem k18g_exists_mul_of_abelian_sup {Q A B : Subgroup G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hAQ : A ≤ Q) (hBQ : B ≤ Q)
    {q : G} (hq : q ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, q = a * b := by
  have hBnorm : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := by
    intro b hb a ha
    have hcomm : b * a = a * b := (hQab a (hAQ ha) b (hBQ hb)).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact ha
  exact (mem_sup_iff_of_normalizes (H := A) (K := B) hBnorm).mp hq

private theorem k18g_inf_eq_bot_of_card_le {A B Q : Subgroup G}
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hAQ : A ≤ Q) (hBQ : B ≤ Q)
    (hQle : Q ≤ A ⊔ B) (hcardA : Nat.card A ≤ 8) (hcardB : Nat.card B ≤ 8)
    (hcardQ : Nat.card Q = 64) : A ⊓ B = ⊥ := by
  have hsurj : ∀ q ∈ Q, ∃ a ∈ A, ∃ b ∈ B, q = a * b :=
    fun q hq => k18g_exists_mul_of_abelian_sup hQab hAQ hBQ (hQle hq)
  let f : ↥A × ↥B → ↥Q :=
    fun p => ⟨(p.1 : G) * (p.2 : G), Q.mul_mem (hAQ p.1.2) (hBQ p.2.2)⟩
  have hsurjf : Function.Surjective f := by
    intro q
    obtain ⟨a, ha, b, hb, hq⟩ := hsurj q q.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hq.symm⟩
  have hcard_prod : Nat.card (↥A × ↥B) ≤ Nat.card ↥Q := by
    rw [Nat.card_prod, hcardQ]
    calc Nat.card A * Nat.card B ≤ 8 * 8 := Nat.mul_le_mul hcardA hcardB
      _ = 64 := by norm_num
  have hinj : Function.Injective f := (hsurjf.bijective_of_nat_card_le hcard_prod).1
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  obtain ⟨hcA, hcB⟩ := Subgroup.mem_inf.mp hc
  have h1 : f (⟨c, hcA⟩, ⟨1, B.one_mem⟩) = f (⟨1, A.one_mem⟩, ⟨c, hcB⟩) := by
    apply Subtype.ext
    simp only [f, Subtype.coe_mk, mul_one, one_mul]
  have h2 := congrArg (fun p : ↥A × ↥B => (p.1 : G)) (hinj h1)
  exact Subgroup.mem_bot.mpr (by simpa using h2)

theorem k18_u_x₁ (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    (lam * t) * x₁ * (lam * t)⁻¹ = x₂ := by
  have hx₁t : x₁ * t = t * x₁ :=
    S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp (S4A.generators_mem_L hc.toCtx0).1)
  calc (lam * t) * x₁ * (lam * t)⁻¹ = lam * (t * x₁ * t⁻¹) * lam⁻¹ := by group
    _ = lam * x₁ * lam⁻¹ := by
          have h : t * x₁ * t⁻¹ = x₁ := by rw [← hx₁t]; group
          rw [h]
    _ = x₂ := hc.wreath.conj_x₁

theorem k18_u_x₂ (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    (lam * t) * x₂ * (lam * t)⁻¹ = x₁ := by
  have hx₂t : x₂ * t = t * x₂ :=
    S4A.mem_invCent_iff.mp (S4A.L_le_invCent hc.hyp (S4A.generators_mem_L hc.toCtx0).2.1)
  have hlam2 := k18g_lam2 hc
  have hlamx₂ : lam * x₂ * lam⁻¹ = x₁ := by
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [hc.wreath.conj_x₁]
      _ = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by simp only [mul_assoc]
      _ = x₁ := by
            have hli : lam⁻¹ * lam⁻¹ = 1 := by rw [← mul_inv_rev, hlam2, inv_one]
            rw [hlam2, hli, one_mul, mul_one]
  calc (lam * t) * x₂ * (lam * t)⁻¹ = lam * (t * x₂ * t⁻¹) * lam⁻¹ := by group
    _ = lam * x₂ * lam⁻¹ := by
          have h : t * x₂ * t⁻¹ = x₂ := by rw [← hx₂t]; group
          rw [h]
    _ = x₁ := hlamx₂

theorem k18_u_mem_K (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    lam * t ∈ ctxK t tau x₁ x₂ rho :=
  Subgroup.mul_mem _ (l17_mem_K hc).2.2.2.1 (l17_mem_K hc).1

theorem k18_u_sq (hc : Ctx13 t L S x₁ x₂ lam rho tau om) : (lam * t) * (lam * t) = 1 := by
  have hlt : lam * t = t * lam := (l17_lam_comm hc).1
  have hlam2 := k18g_lam2 hc
  have ht2 := k18g_t2 hc
  calc (lam * t) * (lam * t) = lam * (t * lam) * t := by group
    _ = lam * (lam * t) * t := by rw [← hlt]
    _ = (lam * lam) * (t * t) := by group
    _ = 1 := by rw [hlam2, ht2, mul_one]

theorem k18_u_x₁x₂ (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    (lam * t) * (x₁ * x₂) * (lam * t)⁻¹ = x₁ * x₂ := by
  calc (lam * t) * (x₁ * x₂) * (lam * t)⁻¹
      = ((lam * t) * x₁ * (lam * t)⁻¹) * ((lam * t) * x₂ * (lam * t)⁻¹) := by group
    _ = x₂ * x₁ := by rw [k18_u_x₁ hc, k18_u_x₂ hc]
    _ = x₁ * x₂ := hc.wreath.comm.symm

theorem k18_u_normalizes_Q (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ q ∈ ctxQ t tau x₁ x₂ rho, (lam * t) * q * (lam * t)⁻¹ ∈ ctxQ t tau x₁ x₂ rho := by
  intro q hq
  exact hc.normal_Q_K.2 (lam * t) (k18_u_mem_K hc) q hq

theorem k18_A0_le_Q (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    closure ({x₁, v₂} : Set G) ≤ ctxQ t tau x₁ x₂ rho := by
  obtain ⟨hV1, hV2, hVQ, hVbase, hVrho, hVu, hVY, hVfix, hv₁V, hv₁ne, hv₁t,
    hv₂V, hv₂nv₁, hVgen, hv₂t, hv₂u, hVcent, hω₁, hω₂⟩ := hV
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]
    exact hc.base_le_Q (Subgroup.subset_closure (by simp))
  · rw [hg, hVQ]
    exact Subgroup.mem_sup_right hv₂V

theorem k18_Q_le_sup (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    ctxQ t tau x₁ x₂ rho ≤
      closure ({x₁, v₂} : Set G) ⊔ cj (lam * t) (closure ({x₁, v₂} : Set G)) := by
  obtain ⟨hV1, hV2, hVQ, hVbase, hVrho, hVu, hVY, hVfix, hv₁V, hv₁ne, hv₁t,
    hv₂V, hv₂nv₁, hVgen, hv₂t, hv₂u, hVcent, hω₁, hω₂⟩ := hV
  have hbase : baseGrp x₁ x₂ ≤
      closure ({x₁, v₂} : Set G) ⊔ cj (lam * t) (closure ({x₁, v₂} : Set G)) := by
    rw [baseGrp, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hg, ← k18_u_x₁ hc]
      exact Subgroup.mem_sup_right (conj_mem_cj (Subgroup.subset_closure (by simp)))
  have hV' : V' ≤
      closure ({x₁, v₂} : Set G) ⊔ cj (lam * t) (closure ({x₁, v₂} : Set G)) := by
    rw [hVgen, Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      have hv₁eq : v₁ = v₂⁻¹ * ((lam * t) * v₂ * (lam * t)⁻¹) := by rw [hv₂u]; group
      rw [hv₁eq]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))))
        (Subgroup.mem_sup_right (conj_mem_cj (Subgroup.subset_closure (by simp))))
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  rw [hVQ]
  exact sup_le hbase hV'

theorem k18_card_A0_le (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    Nat.card ↥(closure ({x₁, v₂} : Set G)) ≤ 8 := by
  obtain ⟨hV1, hV2, hVQ, hVbase, hVrho, hVu, hVY, hVfix, hv₁V, hv₁ne, hv₁t,
    hv₂V, hv₂nv₁, hVgen, hv₂t, hv₂u, hVcent, hω₁, hω₂⟩ := hV
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hv₂Q : v₂ ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hVQ]; exact Subgroup.mem_sup_right hv₂V
  have hle : closure ({x₁, v₂} : Set G) ≤ zpowers x₁ ⊔ zpowers v₂ := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
    · rw [hg]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v₂)
  have hcomm : ∀ k ∈ zpowers v₂, ∀ h ∈ zpowers x₁, k * h * k⁻¹ ∈ zpowers x₁ := by
    intro k hk h hh
    have hkQ : k ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.zpowers_le.mpr hv₂Q) hk
    have hhQ : h ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.zpowers_le.mpr hx₁Q) hh
    have hck := IsZ4Z4E4.comm hc.q_iso hhQ hkQ
    rw [← hck, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hinf : zpowers x₁ ⊓ zpowers v₂ = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have hgbase : g ∈ baseGrp x₁ x₂ :=
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) hg.1
    have hgV : g ∈ V' := (Subgroup.zpowers_le.mpr hv₂V) hg.2
    have hmem : g ∈ baseGrp x₁ x₂ ⊓ V' := ⟨hgbase, hgV⟩
    rwa [hVbase] at hmem
  have hcard_sup := card_sup_eq_mul (H := zpowers x₁) (K := zpowers v₂) hcomm hinf
  have hcard_le : Nat.card ↥(closure ({x₁, v₂} : Set G)) ≤ orderOf x₁ * orderOf v₂ := by
    have h := Subgroup.card_le_of_le hle
    rwa [hcard_sup, Nat.card_zpowers, Nat.card_zpowers] at h
  have hv₂sq : v₂ ^ 2 = 1 := hV1.2 v₂ hv₂V
  have hdvd : orderOf v₂ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hv₂sq
  have hle2 : orderOf v₂ ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  calc Nat.card ↥(closure ({x₁, v₂} : Set G)) ≤ 4 * orderOf v₂ := by
        simpa [hc.wreath.ord_x₁] using hcard_le
    _ ≤ 4 * 2 := Nat.mul_le_mul_left 4 hle2
    _ = 8 := by norm_num

theorem k18_A0_inf (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    closure ({x₁, v₂} : Set G) ⊓ cj (lam * t) (closure ({x₁, v₂} : Set G)) = ⊥ := by
  have hAQ : closure ({x₁, v₂} : Set G) ≤ ctxQ t tau x₁ x₂ rho := k18_A0_le_Q hc hV
  have hBQ : cj (lam * t) (closure ({x₁, v₂} : Set G)) ≤ ctxQ t tau x₁ x₂ rho := by
    intro b hb
    have hb' : (lam * t)⁻¹ * b * (lam * t) ∈ closure ({x₁, v₂} : Set G) := mem_cj.mp hb
    have hmem := k18_u_normalizes_Q hc _ (hAQ hb')
    have heq : (lam * t) * ((lam * t)⁻¹ * b * (lam * t)) * (lam * t)⁻¹ = b := by group
    rwa [heq] at hmem
  have hcardA := k18_card_A0_le hc hV
  have hcardB : Nat.card ↥(cj (lam * t) (closure ({x₁, v₂} : Set G))) ≤ 8 := by
    rw [card_cj]; exact hcardA
  exact k18g_inf_eq_bot_of_card_le
    (fun a ha b hb => IsZ4Z4E4.comm hc.q_iso ha hb) hAQ hBQ (k18_Q_le_sup hc hV)
    hcardA hcardB (IsZ4Z4E4.card hc.q_iso)

theorem k18_free_A0 (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {V' : Subgroup G} {v₁ v₂ : G}
    (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    (∀ q ∈ ctxQ t tau x₁ x₂ rho, ∃ a ∈ closure ({x₁, v₂} : Set G),
        ∃ b ∈ closure ({x₁, v₂} : Set G), q = a * ((lam * t) * b * (lam * t)⁻¹)) ∧
      ∀ a ∈ closure ({x₁, v₂} : Set G), ∀ b ∈ closure ({x₁, v₂} : Set G),
        a * ((lam * t) * b * (lam * t)⁻¹) = 1 → a = 1 := by
  have hAQ : closure ({x₁, v₂} : Set G) ≤ ctxQ t tau x₁ x₂ rho := k18_A0_le_Q hc hV
  have hBQ : cj (lam * t) (closure ({x₁, v₂} : Set G)) ≤ ctxQ t tau x₁ x₂ rho := by
    intro b hb
    have hb' : (lam * t)⁻¹ * b * (lam * t) ∈ closure ({x₁, v₂} : Set G) := mem_cj.mp hb
    have hmem := k18_u_normalizes_Q hc _ (hAQ hb')
    have heq : (lam * t) * ((lam * t)⁻¹ * b * (lam * t)) * (lam * t)⁻¹ = b := by group
    rwa [heq] at hmem
  constructor
  · intro q hq
    obtain ⟨a, ha, b, hb, hqeq⟩ := k18g_exists_mul_of_abelian_sup
      (fun a ha b hb => IsZ4Z4E4.comm hc.q_iso ha hb) hAQ hBQ (k18_Q_le_sup hc hV hq)
    have hb' : (lam * t)⁻¹ * b * (lam * t) ∈ closure ({x₁, v₂} : Set G) := mem_cj.mp hb
    refine ⟨a, ha, (lam * t)⁻¹ * b * (lam * t), hb', ?_⟩
    rw [hqeq]
    group
  · intro a ha b hb hab
    have hbinB : (lam * t) * b * (lam * t)⁻¹ ∈
        cj (lam * t) (closure ({x₁, v₂} : Set G)) := conj_mem_cj hb
    have hainB : a ∈ cj (lam * t) (closure ({x₁, v₂} : Set G)) := by
      rw [mul_eq_one_iff_eq_inv.mp hab]
      exact Subgroup.inv_mem _ hbinB
    have hmem : a ∈ closure ({x₁, v₂} : Set G) ⊓
        cj (lam * t) (closure ({x₁, v₂} : Set G)) := ⟨ha, hainB⟩
    rw [k18_A0_inf hc hV] at hmem
    exact Subgroup.mem_bot.mp hmem

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
