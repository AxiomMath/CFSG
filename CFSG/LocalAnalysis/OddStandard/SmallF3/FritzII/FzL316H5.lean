module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35d
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fzl_prod_sup_equiv_aux {H₁ H₂ : Subgroup G}
    (hcomm : ∀ x ∈ H₁, ∀ y ∈ H₂, Commute x y) (hdisj : H₁ ⊓ H₂ = ⊥) :
    Nonempty ((H₁ × H₂) ≃* (H₁ ⊔ H₂ : Subgroup G)) := by
  have hc : ∀ (x : H₁) (y : H₂), Commute (H₁.subtype x) (H₂.subtype y) :=
    fun x y => hcomm x x.2 y y.2
  have hf : Function.Injective (MonoidHom.noncommCoprod H₁.subtype H₂.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨H₁.subtype_injective, H₂.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hdisj
  have hrange : (MonoidHom.noncommCoprod H₁.subtype H₂.subtype hc).range = H₁ ⊔ H₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)⟩

theorem fzl_twoCore_cases (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ k ∈ twoCore t, k = 1 ∨ k = t := by
  have htP : twoCore t = zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge (H := zpowers t) (K := twoCore t)
      (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore) ?_).symm
    rw [hK, Nat.card_zpowers, h.hyp.ord_t]
  intro k hk
  rw [htP] at hk
  exact S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hk

theorem fzl_t_notin_E (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    t ∉ baseGrp x₁ x₂ := by
  intro ht
  have hmem : t ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨h.hyp.mem_twoCore, ht⟩
  rw [S4A.pt_inf_base h.toCtx0, Subgroup.mem_bot] at hmem
  have h1 : orderOf t = 1 := orderOf_eq_one_iff.mpr hmem
  rw [h.hyp.ord_t] at h1
  norm_num at h1

theorem fzl_W_split (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ w ∈ ctxW t x₁ x₂, w ∈ baseGrp x₁ x₂ ∨ t * w ∈ baseGrp x₁ x₂ := by
  have htt : t * t = 1 := S4A.t_mul_self h.hyp
  intro w hw
  obtain ⟨p, hp, b, hb, rfl⟩ :=
    (mem_sup_iff_of_commute (S4A.pt_comm_base h.toCtx0)).mp hw
  rcases fzl_twoCore_cases h hK p hp with h1 | h1
  · left
    rw [h1, one_mul]
    exact hb
  · right
    have : t * (t * b) = b := by rw [← mul_assoc, htt, one_mul]
    rw [h1, this]
    exact hb

theorem fzl_E_sq (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ e ∈ baseGrp x₁ x₂, e ^ 2 ∈ fourGrp x₁ x₂ := by
  intro e he
  exact fzl_sq_mem_Z h hK (Subgroup.mem_sup_right he)

theorem fzl_E_exp (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ e ∈ baseGrp x₁ x₂, e ^ 4 = 1 := by
  intro e he
  have h2 : (e ^ 2) ^ 2 = 1 := fzl_Z_sq_eq_one h (fzl_E_sq h hK e he)
  rw [show (4 : Nat) = 2 * 2 by norm_num, pow_mul]
  exact h2

theorem fzl_Z_sqrt (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ z ∈ fourGrp x₁ x₂, ∃ e ∈ baseGrp x₁ x₂, e ^ 2 = z := by
  have hEcomm : IsMulCommutative (baseGrp x₁ x₂) := (h.wreath.baseGrp_eq).1
  have hmemE : ∀ a ∈ baseGrp x₁ x₂, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (isMulCommutative_iff.mp hEcomm ⟨a, ha⟩ ⟨b, hb⟩)
  intro z hz
  rw [fourGrp] at hz
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ e ∈ baseGrp x₁ x₂, e ^ 2 = x) ?_ ?_ ?_ ?_ hz
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨x₁, Subgroup.subset_closure (by simp), rfl⟩
    · exact ⟨x₁ * x₂, Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)), rfl⟩
  · exact ⟨1, Subgroup.one_mem _, by simp⟩
  · intro a b _ _ iha ihb
    obtain ⟨ea, hea, rfl⟩ := iha
    obtain ⟨eb, heb, rfl⟩ := ihb
    exact ⟨ea * eb, Subgroup.mul_mem _ hea heb,
      (show Commute ea eb from hmemE ea hea eb heb).mul_pow 2⟩
  · intro a _ iha
    obtain ⟨ea, hea, rfl⟩ := iha
    exact ⟨ea⁻¹, Subgroup.inv_mem _ hea, by rw [inv_pow]⟩

theorem fzl_E_invol (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    ∀ e ∈ baseGrp x₁ x₂, e ^ 2 = 1 → e ∈ fourGrp x₁ x₂ := by
  intro e he he2
  rcases fzl_invol_mem_W h hK (Subgroup.mem_sup_right he) he2 with hZ | ⟨z, hz, heq⟩
  · exact hZ
  · exfalso
    have hzE : z ∈ baseGrp x₁ x₂ := S4A.pt_four_le_base x₁ x₂ hz
    have ht : t ∈ baseGrp x₁ x₂ := by
      have h1 : t = e * z⁻¹ := by rw [heq]; group
      rw [h1]
      exact Subgroup.mul_mem _ he (Subgroup.inv_mem _ hzE)
    exact fzl_t_notin_E h hK ht

theorem fzl_E_equiv (h : Ctx t L S x₁ x₂ lam rho tau) :
    Nonempty (↥(baseGrp x₁ x₂) ≃* Z4Z4) := by
  have hE : baseGrp x₁ x₂ = zpowers x₁ ⊔ zpowers x₂ := (h.wreath.baseGrp_eq).2.1
  have hc12 : Commute x₁ x₂ := h.wreath.comm
  have hcommE : ∀ u ∈ zpowers x₁, ∀ v ∈ zpowers x₂, Commute u v := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact hc12.zpow_zpow i j
  let ζ1 : Multiplicative (ZMod 4) ≃* ↥(zpowers x₁) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, h.wreath.ord_x₁, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card])
  let ζ2 : Multiplicative (ZMod 4) ≃* ↥(zpowers x₂) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, h.wreath.ord_x₂, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card])
  let eE : ↥(zpowers x₁) × ↥(zpowers x₂) ≃* ↥(baseGrp x₁ x₂) :=
    (fzl_prod_sup_equiv_aux hcommE h.wreath.inf_eq_bot).some.trans (MulEquiv.subgroupCongr hE.symm)
  let pM2 : Multiplicative (ZMod 4 × ZMod 4) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4)
  exact ⟨((pM2.trans (MulEquiv.prodCongr ζ1 ζ2)).trans eE).symm⟩

theorem fzl_lam_E (h : Ctx t L S x₁ x₂ lam rho tau) :
    (∀ e ∈ baseGrp x₁ x₂, lam * e * lam⁻¹ ∈ baseGrp x₁ x₂) ∧
      ∃ e ∈ baseGrp x₁ x₂, lam * e * lam⁻¹ ≠ e ∧ lam * e * lam⁻¹ ≠ e⁻¹ := by
  have hlam2 : lam ^ 2 = 1 := (fzl_lam_Z h).2.2.1
  have hll : lam * lam = 1 := by rw [← pow_two]; exact hlam2
  have hx2 : lam * x₂ * lam⁻¹ = x₁ := by
    have h1 : lam * (lam * x₁ * lam⁻¹) * lam⁻¹ = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by
      group
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by rw [h.wreath.conj_x₁]
      _ = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := h1
      _ = x₁ := by
        have hllinv : lam⁻¹ * lam⁻¹ = 1 := by rw [← mul_inv_rev, hll, inv_one]
        rw [hll, hllinv, one_mul, mul_one]
  constructor
  · intro e he
    refine Subgroup.closure_induction
      (p := fun x _ => lam * x * lam⁻¹ ∈ baseGrp x₁ x₂) ?_ ?_ ?_ ?_ he
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [h.wreath.conj_x₁]
        exact Subgroup.subset_closure (by simp)
      · rw [hx2]
        exact Subgroup.subset_closure (by simp)
    · simp
    · intro a b _ _ iha ihb
      have h1 : lam * (a * b) * lam⁻¹ = (lam * a * lam⁻¹) * (lam * b * lam⁻¹) := by group
      rw [h1]
      exact Subgroup.mul_mem _ iha ihb
    · intro a _ iha
      have h1 : lam * a⁻¹ * lam⁻¹ = (lam * a * lam⁻¹)⁻¹ := by group
      rw [h1]
      exact Subgroup.inv_mem _ iha
  · refine ⟨x₁, Subgroup.subset_closure (by simp), ?_, ?_⟩
    · rw [h.wreath.conj_x₁]
      intro hx
      exact (fzl_z1_ne_z2 h).1 (by rw [hx])
    · rw [h.wreath.conj_x₁]
      intro hx
      apply (fzl_z1_ne_z2 h).1
      have hx4 : x₁ ^ 4 = 1 := by
        rw [← h.wreath.ord_x₁]
        exact pow_orderOf_eq_one x₁
      have h22 : x₁ ^ 2 * x₁ ^ 2 = 1 := by
        have h4 := hx4
        rw [show (4 : Nat) = 2 + 2 by norm_num, pow_add] at h4
        exact h4
      have hinv : (x₁ ^ 2)⁻¹ = x₁ ^ 2 := inv_eq_of_mul_eq_one_right h22
      rw [hx, inv_pow, hinv]

theorem fzl_rho_nrm_E (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ e ∈ baseGrp x₁ x₂, rho * e * rho⁻¹ ∈ baseGrp x₁ x₂ := by
  have hWmap_le : (ctxW t x₁ x₂).map (MulAut.conj rho) ≤ ctxW t x₁ x₂ := by
    rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp h.rho_normalizes w).mp hw
  have hWmap_eq : (ctxW t x₁ x₂).map (MulAut.conj rho) = ctxW t x₁ x₂ := by
    refine le_antisymm hWmap_le ?_
    intro w hw
    refine Subgroup.mem_map.mpr ⟨rho⁻¹ * w * rho, ?_, ?_⟩
    · simpa [MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G)).inv_mem
            h.rho_normalizes) w).mp hw
    · change rho * (rho⁻¹ * w * rho) * rho⁻¹ = w
      group
  have hzpmap : (zpowers rho).map (MulAut.conj rho) = zpowers rho := by
    rw [MonoidHom.map_zpowers]
    congr 1
    change rho * rho * rho⁻¹ = rho
    group
  have hmap : (baseGrp x₁ x₂).map (MulAut.conj rho) = baseGrp x₁ x₂ := by
    have h1 := congrArg
      (fun K : Subgroup G => K.map (MulAut.conj rho : G →* G)) h.comm_rho.symm
    rw [h1, Subgroup.map_commutator, hWmap_eq, hzpmap, h.comm_rho]
  intro e he
  have hmem : (MulAut.conj rho) e ∈ baseGrp x₁ x₂ := by
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨e, he, rfl⟩
  simpa [MulAut.conj_apply] using hmem

end CFSG.OddStandard.SmallF3.FritzII
