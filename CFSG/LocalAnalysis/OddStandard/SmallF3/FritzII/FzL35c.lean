module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma twoCore_eq_zpowers (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 2) : twoCore t = zpowers t := by
  refine (Subgroup.eq_of_le_of_card_ge (H := zpowers t) (K := twoCore t)
    (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore) ?_).symm
  rw [hK, Nat.card_zpowers, h.hyp.ord_t]

private theorem fzl_prod_sup_equiv {H₁ H₂ : Subgroup G}
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

private lemma fourGrp_le_sq (h : Ctx t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ Subgroup.closure {z : G | ∃ w ∈ ctxW t x₁ x₂, w ^ 2 = z} := by
  rw [fourGrp, Subgroup.closure_le]
  rintro g (hg : g ∈ ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure
      ⟨x₁, Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)), rfl⟩
  · exact Subgroup.subset_closure
      ⟨x₁ * x₂, Subgroup.mem_sup_right (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))), rfl⟩

theorem fzl_card_W (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    Nat.card (ctxW t x₁ x₂) = 32 := by
  rw [S4A.pt_card_W h.toCtx0, hK]
  norm_num

theorem fzl_W_equiv (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) :
    Nonempty (↥(ctxW t x₁ x₂) ≃* FzZ244) := by
  have htP : twoCore t = zpowers t := twoCore_eq_zpowers h hK
  have hE : baseGrp x₁ x₂ = zpowers x₁ ⊔ zpowers x₂ := (h.wreath.baseGrp_eq).2.1
  have hc12 : Commute x₁ x₂ := h.wreath.comm
  have hcommE : ∀ u ∈ zpowers x₁, ∀ v ∈ zpowers x₂, Commute u v := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact hc12.zpow_zpow i j
  have hcommW : ∀ u ∈ zpowers t, ∀ v ∈ baseGrp x₁ x₂, Commute u v := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hct : Commute t v := S4A.pt_comm_base h.toCtx0 t h.hyp.mem_twoCore v hv
    exact hct.zpow_left i
  have hinfW : zpowers t ⊓ baseGrp x₁ x₂ = ⊥ := by
    rw [← htP]
    exact S4A.pt_inf_base h.toCtx0
  let ζP : Multiplicative (ZMod 2) ≃* ↥(zpowers t) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, h.hyp.ord_t, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card])
  let ζ1 : Multiplicative (ZMod 4) ≃* ↥(zpowers x₁) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, h.wreath.ord_x₁, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card])
  let ζ2 : Multiplicative (ZMod 4) ≃* ↥(zpowers x₂) :=
    mulEquivOfCyclicCardEq (by
      rw [Nat.card_zpowers, h.wreath.ord_x₂, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card])
  let eE : ↥(zpowers x₁) × ↥(zpowers x₂) ≃* ↥(baseGrp x₁ x₂) :=
    (fzl_prod_sup_equiv hcommE h.wreath.inf_eq_bot).some.trans (MulEquiv.subgroupCongr hE.symm)
  let eW : ↥(zpowers t) × ↥(baseGrp x₁ x₂) ≃* ↥(ctxW t x₁ x₂) :=
    (fzl_prod_sup_equiv hcommW hinfW).some.trans
      (MulEquiv.subgroupCongr (by rw [ctxW, htP]))
  let e3 : ↥(zpowers t) × (↥(zpowers x₁) × ↥(zpowers x₂)) ≃* ↥(ctxW t x₁ x₂) :=
    (MulEquiv.prodCongr (MulEquiv.refl _) eE).trans eW
  let pM1 : FzZ244 ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 4 × ZMod 4)) :=
    MulEquiv.prodMultiplicative (ZMod 2) (ZMod 4 × ZMod 4)
  let pM2 : Multiplicative (ZMod 4 × ZMod 4) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4)
  refine ⟨((pM1.trans (MulEquiv.prodCongr (MulEquiv.refl _) pM2)).trans
    ((MulEquiv.prodCongr ζP (MulEquiv.prodCongr ζ1 ζ2)).trans e3)).symm⟩

theorem fzl_card_Z (h : Ctx t L S x₁ x₂ lam rho tau) :
    Nat.card (fourGrp x₁ x₂) = 4 :=
  (WreathRel.fourGrp_eq_omega h.wreath).2.2

theorem fzl_Z_le_W (h : Ctx t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ ctxW t x₁ x₂ :=
  (S4A.pt_four_le_base x₁ x₂).trans le_sup_right

theorem fzl_Z_sq_eq_one (h : Ctx t L S x₁ x₂ lam rho tau) {z : G} (hz : z ∈ fourGrp x₁ x₂) :
    z ^ 2 = 1 :=
  (WreathRel.fourGrp_eq_omega h.wreath).2.1.2 z hz

theorem fzl_t_facts (h : Ctx t L S x₁ x₂ lam rho tau) :
    t ∈ ctxW t x₁ x₂ ∧ t ^ 2 = 1 ∧ (∀ w ∈ ctxW t x₁ x₂, w * t = t * w) ∧
      t ∉ fourGrp x₁ x₂ := by
  have htW : t ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left h.hyp.mem_twoCore
  refine ⟨htW, ?_, ?_, ?_⟩
  · simpa [h.hyp.ord_t] using pow_orderOf_eq_one t
  · intro w hw
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp h.abelian_W ⟨w, hw⟩ ⟨t, htW⟩)
  · intro ht
    have hmem : t ∈ twoCore t ⊓ baseGrp x₁ x₂ :=
      ⟨h.hyp.mem_twoCore, (S4A.pt_four_le_base x₁ x₂) ht⟩
    rw [S4A.pt_inf_base h.toCtx0, Subgroup.mem_bot] at hmem
    have h1 : orderOf t = 1 := orderOf_eq_one_iff.mpr hmem
    rw [h.hyp.ord_t] at h1
    norm_num at h1

theorem fzl_sq_mem_Z (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2) {w : G}
    (hw : w ∈ ctxW t x₁ x₂) : w ^ 2 ∈ fourGrp x₁ x₂ := by
  obtain ⟨p, hp, b, hb, rfl⟩ :=
    (mem_sup_iff_of_commute (S4A.pt_comm_base h.toCtx0)).mp hw
  have hp2 : p ^ 2 = 1 := by
    have hpz : p ∈ zpowers t := by
      rw [← twoCore_eq_zpowers h hK]
      exact hp
    rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hpz with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      simpa [h.hyp.ord_t] using pow_orderOf_eq_one t
  have hc : Commute p b := S4A.pt_comm_base h.toCtx0 p hp b hb
  rw [hc.mul_pow, hp2, one_mul]
  have : b ^ 2 ∈ Subgroup.closure {g : G | ∃ a ∈ baseGrp x₁ x₂, g = a ^ 2} :=
    Subgroup.subset_closure ⟨b, hb, rfl⟩
  rwa [← WreathRel.fourGrp_eq_mho h.wreath] at this

theorem fzl_exists_sq_Z (h : Ctx t L S x₁ x₂ lam rho tau) {z : G} (hz : z ∈ fourGrp x₁ x₂) :
    ∃ w ∈ ctxW t x₁ x₂, w ^ 2 = z := by
  have hz' := fourGrp_le_sq h hz
  refine Subgroup.closure_induction (p := fun x _ => ∃ w ∈ ctxW t x₁ x₂, w ^ 2 = x)
    ?_ ?_ ?_ ?_ hz'
  · intro x hx
    exact hx
  · exact ⟨1, Subgroup.one_mem _, by simp⟩
  · intro x y hx hy ihx ihy
    obtain ⟨wx, hwx, rfl⟩ := ihx
    obtain ⟨wy, hwy, rfl⟩ := ihy
    have hc : Commute wx wy :=
      congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W ⟨wx, hwx⟩ ⟨wy, hwy⟩)
    exact ⟨wx * wy, Subgroup.mul_mem _ hwx hwy, hc.mul_pow 2⟩
  · intro x hx ihx
    obtain ⟨w, hw, hw2⟩ := ihx
    exact ⟨w⁻¹, Subgroup.inv_mem _ hw, by rw [inv_pow, hw2]⟩

theorem fzl_invol_mem_W (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {w : G} (hw : w ∈ ctxW t x₁ x₂) (hw2 : w ^ 2 = 1) :
    w ∈ fourGrp x₁ x₂ ∨ ∃ z ∈ fourGrp x₁ x₂, w = t * z := by
  obtain ⟨p, hp, b, hb, rfl⟩ :=
    (mem_sup_iff_of_commute (S4A.pt_comm_base h.toCtx0)).mp hw
  have hpz : p ∈ zpowers t := by
    rw [← twoCore_eq_zpowers h hK]
    exact hp
  have ht2 : t ^ 2 = 1 := by simpa [h.hyp.ord_t] using pow_orderOf_eq_one t
  have hb2 : b ^ 2 = 1 := by
    have hc : Commute p b := S4A.pt_comm_base h.toCtx0 p hp b hb
    rw [hc.mul_pow] at hw2
    rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hpz with h1 | h1
    · rw [h1, one_pow, one_mul] at hw2
      exact hw2
    · rw [h1, ht2, one_mul] at hw2
      exact hw2
  have hbZ : b ∈ fourGrp x₁ x₂ := by
    have : b ∈ Subgroup.closure {a : G | a ∈ baseGrp x₁ x₂ ∧ a ^ 2 = 1} :=
      Subgroup.subset_closure ⟨hb, hb2⟩
    rwa [← (WreathRel.fourGrp_eq_omega h.wreath).1] at this
  rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hpz with h1 | h1
  · left
    rw [h1, one_mul]
    exact hbZ
  · right
    exact ⟨b, hbZ, by rw [h1]⟩

theorem fzl_z1_ne_z2 (h : Ctx t L S x₁ x₂ lam rho tau) :
    x₁ ^ 2 ≠ x₂ ^ 2 ∧ x₁ ^ 2 ≠ 1 ∧ x₂ ^ 2 ≠ 1 ∧ (x₁ * x₂) ^ 2 = x₁ ^ 2 * x₂ ^ 2 := by
  have hz1 : x₁ ^ 2 ≠ 1 := by
    intro h1
    have hd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [h.wreath.ord_x₁] at hd
    norm_num at hd
  have hz2 : x₂ ^ 2 ≠ 1 := by
    intro h1
    have hd : orderOf x₂ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [h.wreath.ord_x₂] at hd
    norm_num at hd
  have hne : x₁ ^ 2 ≠ x₂ ^ 2 := by
    intro heq
    have hmem : x₁ ^ 2 ∈ zpowers x₁ ⊓ zpowers x₂ := by
      refine ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers x₁) 2, ?_⟩
      rw [heq]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x₂) 2
    rw [h.wreath.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hz1 hmem
  have hc : Commute x₁ x₂ := h.wreath.comm
  exact ⟨hne, hz1, hz2, hc.mul_pow 2⟩

end CFSG.OddStandard.SmallF3.FritzII
