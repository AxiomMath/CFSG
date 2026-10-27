module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AF1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma t_mem_ctxE (t x₁ x₂ : G) : t ∈ ctxE t x₁ x₂ := by
  rw [ctxE]; exact Subgroup.subset_closure (by simp)

private lemma y_mem_ctxE (t x₁ x₂ : G) : x₁ ^ 2 ∈ ctxE t x₁ x₂ := by
  rw [ctxE]; exact Subgroup.subset_closure (by simp)

private lemma z_mem_ctxE (t x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ ctxE t x₁ x₂ := by
  rw [ctxE]; exact Subgroup.subset_closure (by simp)

private lemma t_mem_ctxX (t tau x₁ x₂ : G) : t ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma tau_mem_ctxX (t tau x₁ x₂ : G) : tau ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma y_mem_ctxX (t tau x₁ x₂ : G) : x₁ ^ 2 ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma z_mem_ctxX (t tau x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]; exact Subgroup.subset_closure (by simp)

private lemma y_mem_baseGrp (x₁ x₂ : G) : x₁ ^ 2 ∈ baseGrp x₁ x₂ := by
  rw [baseGrp]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2

private lemma z_mem_baseGrp (x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := by
  rw [baseGrp]
  exact Subgroup.pow_mem _
    (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private lemma baseGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L := by
  rw [baseGrp]
  refine (Subgroup.closure_le (K := L)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact (generators_mem_L h).1
  · exact (generators_mem_L h).2.1

private lemma ctxE_le_ctxW (h : Ctx0 t L S x₁ x₂ lam rho) : ctxE t x₁ x₂ ≤ ctxW t x₁ x₂ := by
  rw [ctxE, ctxW]
  refine (Subgroup.closure_le (K := twoCore t ⊔ baseGrp x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  · exact Subgroup.mem_sup_right (y_mem_baseGrp x₁ x₂)
  · exact Subgroup.mem_sup_right (z_mem_baseGrp x₁ x₂)

private lemma ctxE_le_Pl (h : Ctx0 t L S x₁ x₂ lam rho) : ctxE t x₁ x₂ ≤ twoCore t ⊔ L := by
  rw [ctxE]
  refine (Subgroup.closure_le (K := twoCore t ⊔ L)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  · exact Subgroup.mem_sup_right (y_z_mem_L h).1
  · exact Subgroup.mem_sup_right (y_z_mem_L h).2

private lemma fourGrp_le_ctxE (t x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
  rw [fourGrp, ctxE]
  refine (Subgroup.closure_le
    (K := closure ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

private lemma ctxE_le_ctxX (t tau x₁ x₂ : G) : ctxE t x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxE]
  refine (Subgroup.closure_le (K := ctxX t tau x₁ x₂)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h
  · rw [h]; exact t_mem_ctxX t tau x₁ x₂
  · rw [h]; exact y_mem_ctxX t tau x₁ x₂
  · rw [h]; exact z_mem_ctxX t tau x₁ x₂

private lemma ctxX_le_sup (t tau x₁ x₂ : G) :
    ctxX t tau x₁ x₂ ≤ ctxE t x₁ x₂ ⊔ zpowers tau := by
  rw [ctxX]
  refine (Subgroup.closure_le (K := ctxE t x₁ x₂ ⊔ zpowers tau)).mpr ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with h | h | h | h
  · rw [h]; exact Subgroup.mem_sup_left (t_mem_ctxE t x₁ x₂)
  · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
  · rw [h]; exact Subgroup.mem_sup_left (y_mem_ctxE t x₁ x₂)
  · rw [h]; exact Subgroup.mem_sup_left (z_mem_ctxE t x₁ x₂)

private lemma zpowers_tau_le_ctxX (t tau x₁ x₂ : G) : zpowers tau ≤ ctxX t tau x₁ x₂ :=
  Subgroup.zpowers_le.mpr (tau_mem_ctxX t tau x₁ x₂)

private lemma t_commute_tau (h : Ctx t L S x₁ x₂ lam rho tau) : t * tau = tau * t := by
  have hτ : tau ∈ invCent t := h.toCtx0.le_invCent h.tau_mem
  exact (mem_invCent_iff.mp hτ).symm

private lemma commute_ty (h : Ctx0 t L S x₁ x₂ lam rho) : Commute t (x₁ ^ 2) := by
  have hyL : x₁ ^ 2 ∈ L := (y_z_mem_L h).1
  exact (mem_invCent_iff.mp (L_le_invCent h.hyp hyL)).symm

private lemma commute_tz (h : Ctx0 t L S x₁ x₂ lam rho) : Commute t ((x₁ * x₂) ^ 2) :=
  t_commute_z h

private lemma commute_tauy (h : Ctx t L S x₁ x₂ lam rho tau) : Commute tau (x₁ ^ 2) :=
  tau_commute_y h

private lemma commute_tauz (h : Ctx t L S x₁ x₂ lam rho tau) : Commute tau ((x₁ * x₂) ^ 2) :=
  tau_commute_z h

private lemma commute_yz (h : WreathRel x₁ x₂ lam) :
    Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) :=
  y_commute_z h

private lemma ctxX_gen_pairwise_comm (h : Ctx t L S x₁ x₂ lam rho tau) :
    ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G).Pairwise Commute := by
  have htt : Commute t tau := t_commute_tau h
  have hty : Commute t (x₁ ^ 2) := commute_ty h.toCtx0
  have htz : Commute t ((x₁ * x₂) ^ 2) := commute_tz h.toCtx0
  have htay : Commute tau (x₁ ^ 2) := commute_tauy h
  have htaz : Commute tau ((x₁ * x₂) ^ 2) := commute_tauz h
  have hyz : Commute (x₁ ^ 2) ((x₁ * x₂) ^ 2) := commute_yz h.wreath
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | exact htt
      | exact htt.symm
      | exact hty
      | exact hty.symm
      | exact htz
      | exact htz.symm
      | exact htay
      | exact htay.symm
      | exact htaz
      | exact htaz.symm
      | exact hyz
      | exact hyz.symm

private lemma ctxX_comm (h : Ctx t L S x₁ x₂ lam rho tau) :
    IsMulCommutative (ctxX t tau x₁ x₂) := by
  rw [ctxX]
  exact Subgroup.isMulCommutative_closure (ctxX_gen_pairwise_comm h)

private lemma ctxX_sq_one (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    ∀ x ∈ ctxX t tau x₁ x₂, x ^ 2 = 1 := by
  haveI : IsMulCommutative (ctxX t tau x₁ x₂) := ctxX_comm h
  intro x hx
  rw [ctxX] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · simpa [pow_two] using t_mul_self h.hyp
      · simpa [pow_two] using h44
      · simpa [pow_two] using (y_mul_self_ne_one h.wreath).1
      · simpa [pow_two] using (z_mul_self_ne_one h.toCtx0).1
  | one => simp
  | mul x y hx hy ihx ihy =>
      have hcomm : Commute x y :=
        congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(ctxX t tau x₁ x₂)) ⟨y, hy⟩)
      rw [hcomm.mul_pow, ihx, ihy, mul_one]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

private lemma tau_mem_centralizer_ctxE (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau ∈ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
  rw [ctxE, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact t_commute_tau h
  · exact (tau_commute_y h).symm
  · exact (tau_commute_z h).symm

private lemma ctxW_le_centralizer_ctxE (h : Ctx t L S x₁ x₂ lam rho tau) :
    ctxW t x₁ x₂ ≤ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have heW : e ∈ ctxW t x₁ x₂ := ctxE_le_ctxW h.toCtx0 he
  haveI : IsMulCommutative (ctxW t x₁ x₂) := h.toCtx0.abelian_W
  exact congrArg Subtype.val (mul_comm' (⟨e, heW⟩ : ↥(ctxW t x₁ x₂)) ⟨w, hw⟩)

private lemma mem_invCent_of_mem_centralizer_ctxE (h : Ctx t L S x₁ x₂ lam rho tau)
    {g : G} (hg : g ∈ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G)) : g ∈ invCent t := by
  rw [mem_invCent_iff]
  exact ((Subgroup.mem_centralizer_iff.mp hg) t (t_mem_ctxE t x₁ x₂)).symm

private lemma mem_ctxW_of_mem_centralizer_ctxE_of_mem_sup (h : Ctx t L S x₁ x₂ lam rho tau)
    {g : G} (hg : g ∈ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G))
    (hgPL : g ∈ twoCore t ⊔ L) : g ∈ ctxW t x₁ x₂ := by
  obtain ⟨p, hp, l, hl, hgl⟩ :=
    (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hgPL
  have hyL : x₁ ^ 2 ∈ L := (y_z_mem_L h.toCtx0).1
  have hzL : (x₁ * x₂) ^ 2 ∈ L := (y_z_mem_L h.toCtx0).2
  have hyE : x₁ ^ 2 ∈ ctxE t x₁ x₂ := y_mem_ctxE t x₁ x₂
  have hzE : (x₁ * x₂) ^ 2 ∈ ctxE t x₁ x₂ := z_mem_ctxE t x₁ x₂
  have hgy : Commute g (x₁ ^ 2) := ((Subgroup.mem_centralizer_iff.mp hg) _ hyE).symm
  have hgz : Commute g ((x₁ * x₂) ^ 2) := ((Subgroup.mem_centralizer_iff.mp hg) _ hzE).symm
  have hpy : Commute p (x₁ ^ 2) := twoCore_commute h.hyp p hp _ hyL
  have hpz : Commute p ((x₁ * x₂) ^ 2) := twoCore_commute h.hyp p hp _ hzL
  have hl_eq : p⁻¹ * g = l := by rw [hgl]; group
  have hly : l * x₁ ^ 2 = x₁ ^ 2 * l := by
    have h1 : Commute (p⁻¹ * g) (x₁ ^ 2) := (hpy.inv_left).mul_left hgy
    rwa [hl_eq] at h1
  have hlz : l * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * l := by
    have h1 : Commute (p⁻¹ * g) ((x₁ * x₂) ^ 2) := (hpz.inv_left).mul_left hgz
    rwa [hl_eq] at h1
  have hlA : l ∈ baseGrp x₁ x₂ := cent_fourGrp_of_ctx0 h.toCtx0 l hl hly hlz
  rw [hgl, ctxW]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hlA)

private lemma mem_ctxW_or_mul_tau_mem_ctxW_of_mem_centralizer_ctxE
    (h : Ctx t L S x₁ x₂ lam rho tau)
    {g : G} (hg : g ∈ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G)) :
    g ∈ ctxW t x₁ x₂ ∨ g * tau ∈ ctxW t x₁ x₂ := by
  have hgH : g ∈ invCent t := mem_invCent_of_mem_centralizer_ctxE h hg
  have htauH : tau ∈ invCent t := h.toCtx0.le_invCent h.tau_mem
  have hK : twoCore t ⊔ L ≤ invCent t :=
    sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  rcases mem_or_mem_or_mul_mem_of_relIndex_two (K := twoCore t ⊔ L) (S := invCent t)
      hK h.relIndex_two hgH htauH with h1 | h1 | h1
  · exact Or.inl (mem_ctxW_of_mem_centralizer_ctxE_of_mem_sup h hg h1)
  · exact absurd h1 h.tau_not_mem
  · exact Or.inr (mem_ctxW_of_mem_centralizer_ctxE_of_mem_sup h
      (Subgroup.mul_mem _ hg (tau_mem_centralizer_ctxE h)) h1)

theorem centralizer_E_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂ ⊔ zpowers tau := by
  apply le_antisymm
  · intro g hg
    rcases mem_ctxW_or_mul_tau_mem_ctxW_of_mem_centralizer_ctxE h hg with h1 | h1
    · exact Subgroup.mem_sup_left h1
    · rw [show g = (g * tau) * tau⁻¹ from (mul_inv_cancel_right g tau).symm]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers tau)))
  · exact sup_le (ctxW_le_centralizer_ctxE h)
      (Subgroup.zpowers_le.mpr (tau_mem_centralizer_ctxE h))

private lemma ctxX_card (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    Nat.card (ctxX t tau x₁ x₂) = 16 := by
  have hX_eq : ctxX t tau x₁ x₂ = ctxE t x₁ x₂ ⊔ zpowers tau :=
    le_antisymm (ctxX_le_sup t tau x₁ x₂)
      (sup_le (ctxE_le_ctxX t tau x₁ x₂) (zpowers_tau_le_ctxX t tau x₁ x₂))
  have hcomm_E_zp : ∀ a ∈ ctxE t x₁ x₂, ∀ b ∈ zpowers tau, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have ha_tau : Commute a tau :=
      (Subgroup.mem_centralizer_iff.mp (tau_mem_centralizer_ctxE h) a ha)
    exact ha_tau.zpow_right k
  have hE_inf_zp : ctxE t x₁ x₂ ⊓ zpowers tau = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxE, hxZ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
    have hkmod : tau ^ k = tau ^ (k % 2) :=
      zpow_eq_zpow_emod' (x := tau) k (by simpa using h44)
    have hx_cases : x = 1 ∨ x = tau := by
      rw [← hk, hkmod]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exact Or.inl (by rw [h0, zpow_zero])
      · exact Or.inr (by rw [h1, zpow_one])
    rcases hx_cases with h1 | h1
    · exact h1
    · exfalso
      exact h.tau_not_mem (ctxE_le_Pl h.toCtx0 (h1 ▸ hxE))
  have hcardE : Nat.card (ctxE t x₁ x₂) = 8 := h.m2_PT_attained.2
  have htau_ne_one : tau ≠ 1 := by
    intro h1
    exact h.tau_not_mem (by rw [h1]; exact Subgroup.one_mem _)
  have hord_tau : orderOf tau = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using h44) htau_ne_one
  have hcardZp : Nat.card (zpowers tau) = 2 := by rw [Nat.card_zpowers, hord_tau]
  rw [hX_eq, card_sup_of_commute hcomm_E_zp hE_inf_zp, hcardE, hcardZp]

theorem ctxX_elemAbelian_of (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    CFSG.Open.IsElemAbelian 2 (ctxX t tau x₁ x₂) ∧ Nat.card (ctxX t tau x₁ x₂) = 16 :=
  ⟨⟨ctxX_comm h, ctxX_sq_one h h44⟩, ctxX_card h h44⟩

private lemma tau_conj_eq_inv_of_mem_baseGrp (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ baseGrp x₁ x₂, tau * a * tau⁻¹ = a⁻¹ := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (h.wreath.baseGrp_eq).1
  intro a ha
  rw [baseGrp] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact h.tau_x₁
      · exact h.tau_x₂
  | one => simp
  | mul x y hx hy ihx ihy =>
      have hxy : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ :=
        congrArg Subtype.val (mul_comm' (⟨x⁻¹, Subgroup.inv_mem _ hx⟩ : ↥(baseGrp x₁ x₂))
          (⟨y⁻¹, Subgroup.inv_mem _ hy⟩ : ↥(baseGrp x₁ x₂)))
      calc tau * (x * y) * tau⁻¹ = (tau * x * tau⁻¹) * (tau * y * tau⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
        _ = y⁻¹ * x⁻¹ := hxy
        _ = (x * y)⁻¹ := by rw [mul_inv_rev]
  | inv x hx ihx =>
      have h1 : (tau * x * tau⁻¹)⁻¹ = tau * x⁻¹ * tau⁻¹ := by group
      rw [← h1, ihx]

private lemma mem_ctxE_of_mem_ctxW_of_commute_tau (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {w : G} (hw : w ∈ ctxW t x₁ x₂)
    (hcomm : w * tau = tau * w) : w ∈ ctxE t x₁ x₂ := by
  have hcomm_PA : ∀ a ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (baseGrp_le_L h.toCtx0 hb)
  rw [ctxW] at hw
  obtain ⟨p, hp, a, haA, hw_eq⟩ := (mem_sup_iff_of_commute hcomm_PA).mp hw
  have hp_zp : p ∈ zpowers t := by rwa [← h43]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp_zp
  have h_t_tau : Commute t tau := t_commute_tau h
  have hpt : Commute p tau := by simpa [hk] using h_t_tau.zpow_left k
  have hwt : Commute w tau := hcomm
  have ha_tau : Commute a tau := by
    have h1 : Commute (p⁻¹ * w) tau := (hpt.inv_left).mul_left hwt
    have ha_eq : a = p⁻¹ * w := by rw [hw_eq]; group
    simpa [← ha_eq] using h1
  have ha_conj : tau * a * tau⁻¹ = a⁻¹ := tau_conj_eq_inv_of_mem_baseGrp h a haA
  have ha_eq_inv : a = a⁻¹ := by
    have hconj : tau * a * tau⁻¹ = a := by
      rw [ha_tau.eq.symm]; group
    calc a = tau * a * tau⁻¹ := hconj.symm
      _ = a⁻¹ := ha_conj
  have ha_sq : a ^ 2 = 1 := by
    rw [pow_two]
    exact eq_inv_iff_mul_eq_one.mp ha_eq_inv
  have ha_four : a ∈ fourGrp x₁ x₂ := by
    rw [(h.wreath.fourGrp_eq_omega).1]
    exact Subgroup.subset_closure ⟨haA, ha_sq⟩
  have ha_E : a ∈ ctxE t x₁ x₂ := fourGrp_le_ctxE t x₁ x₂ ha_four
  have hpE : p ∈ ctxE t x₁ x₂ :=
    (Subgroup.zpowers_le.mpr (t_mem_ctxE t x₁ x₂)) hp_zp
  rw [hw_eq]
  exact Subgroup.mul_mem _ hpE ha_E

private lemma tau_mem_centralizer_ctxX (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau ∈ centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) := by
  haveI : IsMulCommutative (ctxX t tau x₁ x₂) := ctxX_comm h
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (congrArg Subtype.val (mul_comm' (⟨tau, tau_mem_ctxX t tau x₁ x₂⟩ :
    ↥(ctxX t tau x₁ x₂)) ⟨y, hy⟩)).symm

theorem centralizer_X_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) :
    centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) = ctxX t tau x₁ x₂ := by
  haveI : IsMulCommutative (ctxX t tau x₁ x₂) := (ctxX_elemAbelian_of h h44).1.1
  apply le_antisymm
  · intro g hg
    have hgE : g ∈ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact (Subgroup.mem_centralizer_iff.mp hg) e (ctxE_le_ctxX t tau x₁ x₂ he)
    have htauX : tau ∈ ctxX t tau x₁ x₂ := tau_mem_ctxX t tau x₁ x₂
    have hgtau_comm : g * tau = tau * g :=
      ((Subgroup.mem_centralizer_iff.mp hg) tau htauX).symm
    rcases mem_ctxW_or_mul_tau_mem_ctxW_of_mem_centralizer_ctxE h hgE with hgW | hgW
    · exact ctxE_le_ctxX t tau x₁ x₂
        (mem_ctxE_of_mem_ctxW_of_commute_tau h h43 hgW hgtau_comm)
    · have hgtau_cent : g * tau ∈ centralizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) :=
        Subgroup.mul_mem _ hg (tau_mem_centralizer_ctxX h)
      have hcommW : (g * tau) * tau = tau * (g * tau) :=
        ((Subgroup.mem_centralizer_iff.mp hgtau_cent) tau htauX).symm
      have hmemE : g * tau ∈ ctxE t x₁ x₂ :=
        mem_ctxE_of_mem_ctxW_of_commute_tau h h43 hgW hcommW
      have hg_eq : g = (g * tau) * tau := by
        rw [mul_assoc, show tau * tau = 1 from by simpa [pow_two] using h44, mul_one]
      rw [hg_eq]
      exact Subgroup.mul_mem _ (ctxE_le_ctxX t tau x₁ x₂ hmemE) htauX
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥(ctxX t tau x₁ x₂)) ⟨x, hx⟩)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
