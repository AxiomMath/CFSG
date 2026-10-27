module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35c

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G]

@[expose] def fzbsX (t x₁ x₂ : G) : Subgroup G := zpowers t ⊔ baseGrp x₁ x₂

variable [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem fzbs_prod_sup_equiv {H₁ H₂ : Subgroup G}
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

theorem fzbs_exists_gen (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∃ q : G, zpowers q = twoCore t := by
  obtain ⟨g, hg⟩ := h.hyp.isCyclic.exists_generator
  refine ⟨(g : G), ?_⟩
  have htop : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => hg x⟩
  have hmap := MonoidHom.map_zpowers (twoCore t).subtype g
  rw [htop, Subgroup.map_top, Subgroup.range_subtype] at hmap
  exact hmap.symm

theorem fzbs_q_facts (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    {q : G} (hq : zpowers q = twoCore t) : orderOf q = 4 ∧ q ^ 2 = t := by
  have hord : orderOf q = 4 := by rw [← Nat.card_zpowers, hq, hK]
  have hq4 : q ^ 4 = 1 := by rw [← hord]; exact pow_orderOf_eq_one q
  have hq2sq : (q ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 from rfl, hq4]
  have hq2mem : q ^ 2 ∈ twoCore t := by
    rw [← hq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers q) 2
  have hq2ne : q ^ 2 ≠ 1 := by
    intro h1
    have hd : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hord] at hd
    norm_num at hd
  rcases h.hyp.eq_one_or_eq (q ^ 2) hq2mem hq2sq with h1 | h1
  · exact absurd h1 hq2ne
  · exact ⟨hord, h1⟩

theorem fzbs_K_sq (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4) {k : G}
    (hk : k ∈ twoCore t) : k ^ 2 = 1 ∨ k ^ 2 = t := by
  have hk4 : k ^ 4 = 1 := by
    have hpow := pow_card_eq_one' (G := ↥(twoCore t)) (x := ⟨k, hk⟩)
    rw [hK] at hpow
    simpa using congrArg Subtype.val hpow
  have hk2sq : (k ^ 2) ^ 2 = 1 := by
    rw [← pow_mul, show 2 * 2 = 4 from rfl, hk4]
  exact h.hyp.eq_one_or_eq (k ^ 2) ((twoCore t).pow_mem hk 2) hk2sq

theorem fzbs_card_W (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4) :
    Nat.card (ctxW t x₁ x₂) = 64 := by
  rw [S4A.pt_card_W h.toCtx0, hK]
  norm_num

theorem fzbs_X_le (h : Ctx t L S x₁ x₂ lam rho tau) :
    t ∈ fzbsX t x₁ x₂ ∧ fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ ∧ baseGrp x₁ x₂ ≤ fzbsX t x₁ x₂ ∧
      fzbsX t x₁ x₂ ≤ ctxW t x₁ x₂ := by
  refine ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers t), S4A.pt_four_le_base x₁ x₂,
    le_sup_right, ?_⟩
  exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left h.hyp.mem_twoCore)) le_sup_right

theorem fzbs_X_comm (h : Ctx t L S x₁ x₂ lam rho tau) {a b : G} (ha : a ∈ fzbsX t x₁ x₂)
    (hb : b ∈ fzbsX t x₁ x₂) : a * b = b * a := by
  have hle := (fzbs_X_le h).2.2.2
  exact congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W ⟨a, hle ha⟩ ⟨b, hle hb⟩)

theorem fzbs_t_not_mem_E (h : Ctx t L S x₁ x₂ lam rho tau) : t ∉ baseGrp x₁ x₂ := by
  intro ht
  have hmem : t ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨h.hyp.mem_twoCore, ht⟩
  rw [S4A.pt_inf_base h.toCtx0, Subgroup.mem_bot] at hmem
  have h1 : orderOf t = 1 := orderOf_eq_one_iff.mpr hmem
  rw [h.hyp.ord_t] at h1
  norm_num at h1

theorem fzbs_X_equiv (h : Ctx t L S x₁ x₂ lam rho tau) :
    Nonempty (↥(fzbsX t x₁ x₂) ≃* FzZ244) := by
  have hE : baseGrp x₁ x₂ = zpowers x₁ ⊔ zpowers x₂ := (h.wreath.baseGrp_eq).2.1
  have hc12 : Commute x₁ x₂ := h.wreath.comm
  have hcommE : ∀ u ∈ zpowers x₁, ∀ v ∈ zpowers x₂, Commute u v := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact hc12.zpow_zpow i j
  have hcommX : ∀ u ∈ zpowers t, ∀ v ∈ baseGrp x₁ x₂, Commute u v := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hct : Commute t v := S4A.pt_comm_base h.toCtx0 t h.hyp.mem_twoCore v hv
    exact hct.zpow_left i
  have hinfX : zpowers t ⊓ baseGrp x₁ x₂ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc zpowers t ⊓ baseGrp x₁ x₂ ≤ twoCore t ⊓ baseGrp x₁ x₂ :=
          inf_le_inf_right _ (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore)
      _ = ⊥ := S4A.pt_inf_base h.toCtx0
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
    (fzbs_prod_sup_equiv hcommE h.wreath.inf_eq_bot).some.trans (MulEquiv.subgroupCongr hE.symm)
  let eX : ↥(zpowers t) × ↥(baseGrp x₁ x₂) ≃* ↥(fzbsX t x₁ x₂) :=
    (fzbs_prod_sup_equiv hcommX hinfX).some.trans (MulEquiv.subgroupCongr (by rw [fzbsX]))
  let e3 : ↥(zpowers t) × (↥(zpowers x₁) × ↥(zpowers x₂)) ≃* ↥(fzbsX t x₁ x₂) :=
    (MulEquiv.prodCongr (MulEquiv.refl _) eE).trans eX
  let pM1 : FzZ244 ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 4 × ZMod 4)) :=
    MulEquiv.prodMultiplicative (ZMod 2) (ZMod 4 × ZMod 4)
  let pM2 : Multiplicative (ZMod 4 × ZMod 4) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4)
  refine ⟨((pM1.trans (MulEquiv.prodCongr (MulEquiv.refl _) pM2)).trans
    ((MulEquiv.prodCongr ζP (MulEquiv.prodCongr ζ1 ζ2)).trans e3)).symm⟩

theorem fzbs_invol_W (h : Ctx t L S x₁ x₂ lam rho tau) {w : G} (hw : w ∈ ctxW t x₁ x₂)
    (hw2 : w ^ 2 = 1) : w ∈ fourGrp x₁ x₂ ∨ ∃ z ∈ fourGrp x₁ x₂, w = t * z := by
  obtain ⟨p, hp, b, hb, rfl⟩ :=
    (mem_sup_iff_of_commute (S4A.pt_comm_base h.toCtx0)).mp hw
  have hc : Commute p b := S4A.pt_comm_base h.toCtx0 p hp b hb
  have hpb2 : p ^ 2 = (b ^ 2)⁻¹ := by
    have h2 : p ^ 2 * b ^ 2 = 1 := by rw [hc.mul_pow] at hw2; exact hw2
    exact eq_inv_of_mul_eq_one_left h2
  have hp2 : p ^ 2 = 1 := by
    have hb2E : b ^ 2 ∈ baseGrp x₁ x₂ := (baseGrp x₁ x₂).pow_mem hb 2
    have hmem : p ^ 2 ∈ twoCore t ⊓ baseGrp x₁ x₂ :=
      ⟨(twoCore t).pow_mem hp 2, by rw [hpb2]; exact (baseGrp x₁ x₂).inv_mem hb2E⟩
    rwa [S4A.pt_inf_base h.toCtx0, Subgroup.mem_bot] at hmem
  have hb2 : b ^ 2 = 1 := by
    have : (b ^ 2)⁻¹ = 1 := by rw [← hpb2, hp2]
    exact inv_eq_one.mp this
  have hbZ : b ∈ fourGrp x₁ x₂ := by
    have : b ∈ Subgroup.closure {a : G | a ∈ baseGrp x₁ x₂ ∧ a ^ 2 = 1} :=
      Subgroup.subset_closure ⟨hb, hb2⟩
    rwa [← (WreathRel.fourGrp_eq_omega h.wreath).1] at this
  rcases h.hyp.eq_one_or_eq p hp hp2 with h1 | h1
  · left; rw [h1, one_mul]; exact hbZ
  · right; exact ⟨b, hbZ, by rw [h1]⟩

theorem fzbs_mem_X_iff (h : Ctx t L S x₁ x₂ lam rho tau) {w : G} (hw : w ∈ ctxW t x₁ x₂) :
    w ∈ fzbsX t x₁ x₂ ↔ w ^ 2 ∈ fourGrp x₁ x₂ := by
  have hb2Z : ∀ b ∈ baseGrp x₁ x₂, b ^ 2 ∈ fourGrp x₁ x₂ := by
    intro b hb
    have : b ^ 2 ∈ Subgroup.closure {g : G | ∃ a ∈ baseGrp x₁ x₂, g = a ^ 2} :=
      Subgroup.subset_closure ⟨b, hb, rfl⟩
    rwa [← WreathRel.fourGrp_eq_mho h.wreath] at this
  constructor
  · intro hwX
    have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
      fun a ha b hb =>
        S4A.pt_comm_base h.toCtx0 a (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore ha) b hb
    obtain ⟨p, hp, e, he, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hwX
    have hc : Commute p e := S4A.pt_comm_base h.toCtx0 p
      (Subgroup.zpowers_le.mpr h.hyp.mem_twoCore hp) e he
    have hp2 : p ^ 2 = 1 := by
      rcases S4A.pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
      · rw [h1]; simp
      · rw [h1]; simpa [h.hyp.ord_t] using pow_orderOf_eq_one t
    rw [hc.mul_pow, hp2, one_mul]
    exact hb2Z e he
  · intro hwZ
    have hcomm : ∀ a ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
      fun a ha b hb => S4A.pt_comm_base h.toCtx0 a ha b hb
    obtain ⟨p, hp, e, he, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hw
    have hc : Commute p e := S4A.pt_comm_base h.toCtx0 p hp e he
    have he2Z : e ^ 2 ∈ fourGrp x₁ x₂ := hb2Z e he
    have hp2eq : p ^ 2 = (p * e) ^ 2 * (e ^ 2)⁻¹ := by rw [hc.mul_pow]; group
    have hp2Z : p ^ 2 ∈ fourGrp x₁ x₂ := by
      rw [hp2eq]
      exact (fourGrp x₁ x₂).mul_mem hwZ ((fourGrp x₁ x₂).inv_mem he2Z)
    have hp2 : p ^ 2 = 1 := by
      have hmem : p ^ 2 ∈ twoCore t ⊓ baseGrp x₁ x₂ :=
        ⟨(twoCore t).pow_mem hp 2, (S4A.pt_four_le_base x₁ x₂) hp2Z⟩
      rwa [S4A.pt_inf_base h.toCtx0, Subgroup.mem_bot] at hmem
    have hpt : p ∈ zpowers t := by
      rcases h.hyp.eq_one_or_eq p hp hp2 with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers t
    exact Subgroup.mul_mem (fzbsX t x₁ x₂)
      (Subgroup.mem_sup_left hpt) (Subgroup.mem_sup_right he)

theorem fzbs_W_sq (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4) {w : G}
    (hw : w ∈ ctxW t x₁ x₂) :
    w ^ 2 ∈ fourGrp x₁ x₂ ∨ ∃ z ∈ fourGrp x₁ x₂, w ^ 2 = t * z := by
  obtain ⟨p, hp, b, hb, rfl⟩ :=
    (mem_sup_iff_of_commute (S4A.pt_comm_base h.toCtx0)).mp hw
  have hc : Commute p b := S4A.pt_comm_base h.toCtx0 p hp b hb
  have hb2Z : b ^ 2 ∈ fourGrp x₁ x₂ := by
    have : b ^ 2 ∈ Subgroup.closure {g : G | ∃ a ∈ baseGrp x₁ x₂, g = a ^ 2} :=
      Subgroup.subset_closure ⟨b, hb, rfl⟩
    rwa [← WreathRel.fourGrp_eq_mho h.wreath] at this
  rcases fzbs_K_sq h hK hp with hp2 | hp2
  · left; rw [hc.mul_pow, hp2, one_mul]; exact hb2Z
  · right; exact ⟨b ^ 2, hb2Z, by rw [hc.mul_pow, hp2]⟩

theorem fzbs_W_cases (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    {q : G} (hq : zpowers q = twoCore t) :
    q ∉ fzbsX t x₁ x₂ ∧ ∀ w ∈ ctxW t x₁ x₂, w ∈ fzbsX t x₁ x₂ ∨ q * w ∈ fzbsX t x₁ x₂ := by
  have hqK : q ∈ twoCore t := by rw [← hq]; exact Subgroup.mem_zpowers q
  have hqW : q ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left hqK
  have hq2 : q ^ 2 = t := (fzbs_q_facts h hK hq).2
  refine ⟨fun hqX => ?_, ?_⟩
  · have hmem := (fzbs_mem_X_iff h hqW).mp hqX
    rw [hq2] at hmem
    exact (fzl_t_facts h).2.2.2 hmem
  · intro w hw
    by_cases hwX : w ∈ fzbsX t x₁ x₂
    · exact Or.inl hwX
    · refine Or.inr ((fzbs_mem_X_iff h ((ctxW t x₁ x₂).mul_mem hqW hw)).mpr ?_)
      have hw2notZ : w ^ 2 ∉ fourGrp x₁ x₂ :=
        fun hz => hwX ((fzbs_mem_X_iff h hw).mpr hz)
      have hcomm : Commute q w :=
        congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W ⟨q, hqW⟩ ⟨w, hw⟩)
      obtain hw2Z | ⟨z, hz, hw2z⟩ := fzbs_W_sq h hK hw
      · exact absurd hw2Z hw2notZ
      · rw [hcomm.mul_pow, hq2, hw2z, ← mul_assoc, S4A.t_mul_self h.hyp, one_mul]
        exact hz

end CFSG.OddStandard.SmallF3.FritzII
