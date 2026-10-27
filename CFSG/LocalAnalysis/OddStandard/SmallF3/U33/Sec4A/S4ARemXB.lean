module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemXA

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem conj_mem_L (h : Hyp G t L) {g : G} (hg : g ∈ invCent t) {x : G}
    (hx : x ∈ L) : g * x * g⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h hx
  have hmem : (⟨g, hg⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨g, hg⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

private theorem baseGrp_le_L (h : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L := by
  rw [baseGrp]
  refine (Subgroup.closure_le L).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact (generators_mem_L h).1
  · exact (generators_mem_L h).2.1

private theorem baseGrp_comm (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ baseGrp x₁ x₂, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (h.wreath.baseGrp_eq).1
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : baseGrp x₁ x₂) (⟨b, hb⟩ : baseGrp x₁ x₂))

private theorem ctxW_inf_L (h : Ctx t L S x₁ x₂ lam rho tau) :
    ctxW t x₁ x₂ ⊓ L = baseGrp x₁ x₂ := by
  have hAL : baseGrp x₁ x₂ ≤ L := baseGrp_le_L h.toCtx0
  have hcomm : ∀ a ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => twoCore_commute h.hyp a ha b (hAL hb)
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxW, hxL⟩ := hx
    have hxW' : x ∈ twoCore t ⊔ baseGrp x₁ x₂ := by simpa only [ctxW] using hxW
    obtain ⟨p, hp, a, ha, hxpa⟩ :=
      (mem_sup_iff_of_commute (P := twoCore t) (Q := baseGrp x₁ x₂) hcomm).mp hxW'
    have hpL : p ∈ L := by
      have hp_eq : p = x * a⁻¹ := by rw [hxpa]; group
      rw [hp_eq]
      exact Subgroup.mul_mem L hxL (Subgroup.inv_mem L (hAL ha))
    have hpbot : p ∈ twoCore t ⊓ L := ⟨hp, hpL⟩
    rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hpbot
    rw [hxpa, hpbot, one_mul]
    exact ha
  · exact le_inf (by intro a ha; exact Subgroup.mem_sup_right ha) hAL

private theorem fourGrp_le_baseGrp (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  rw [fourGrp, Subgroup.closure_le]
  rintro a (ha : a ∈ ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
  rcases ha with rfl | rfl
  · exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private theorem fourGrp_le_ctxE (t x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := by
  rw [fourGrp, ctxE]
  exact Subgroup.closure_mono (fun a ha => by rcases ha with rfl | rfl <;> simp)

private theorem ctxE_le_ctxX (t tau x₁ x₂ : G) : ctxE t x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
  rw [ctxE, ctxX]
  exact Subgroup.closure_mono (fun a ha => by rcases ha with rfl | rfl | rfl <;> simp)

private theorem fourGrp_le_ctxX (t tau x₁ x₂ : G) : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ :=
  le_trans (fourGrp_le_ctxE t x₁ x₂) (ctxE_le_ctxX t tau x₁ x₂)

private theorem ctxE_eq_sup (t x₁ x₂ : G) :
    ctxE t x₁ x₂ = zpowers t ⊔ fourGrp x₁ x₂ := by
  apply le_antisymm
  · rw [ctxE, Subgroup.closure_le]
    rintro x (hx : x ∈ ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
    rcases hx with hx | hx | hx
    · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
    · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  · apply sup_le
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
    · exact fourGrp_le_ctxE t x₁ x₂

private theorem ctxX_eq_sup (t tau x₁ x₂ : G) :
    ctxX t tau x₁ x₂ = ctxE t x₁ x₂ ⊔ zpowers tau := by
  apply le_antisymm
  · rw [ctxX, Subgroup.closure_le]
    rintro x (hx : x ∈ ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
    rcases hx with hx | hx | hx | hx
    · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
    · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hx]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · apply sup_le
    · exact ctxE_le_ctxX t tau x₁ x₂
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)

private theorem zpowers_t_commute_fourGrp (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ zpowers t, ∀ b ∈ fourGrp x₁ x₂, a * b = b * a := by
  have hty : t * x₁ ^ 2 = x₁ ^ 2 * t := by
    have hyH : x₁ ^ 2 ∈ invCent t := L_le_invCent h.hyp (y_z_mem_L h.toCtx0).1
    rw [mem_invCent_iff] at hyH
    exact hyH.symm
  have htz : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t := by
    have hzH : (x₁ * x₂) ^ 2 ∈ invCent t := L_le_invCent h.hyp (y_z_mem_L h.toCtx0).2
    rw [mem_invCent_iff] at hzH
    exact hzH.symm
  have htcent : t ∈ Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [fourGrp, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro b hb
    rcases hb with hb | hb
    · rw [hb]; exact hty.symm
    · rw [hb]; exact htz.symm
  have hle : zpowers t ≤ Subgroup.centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr htcent
  intro a ha b hb
  exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm

private theorem ctxE_commute_zpowers_tau (h : Ctx t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ ctxE t x₁ x₂, ∀ b ∈ zpowers tau, a * b = b * a := by
  have httau : t * tau = tau * t := (mem_invCent_iff.mp (h.toCtx0.le_invCent h.tau_mem)).symm
  have hytau : x₁ ^ 2 * tau = tau * x₁ ^ 2 := (tau_commute_y h).symm
  have hztau : (x₁ * x₂) ^ 2 * tau = tau * (x₁ * x₂) ^ 2 := (tau_commute_z h).symm
  have hEtau : tau ∈ Subgroup.centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
    rw [ctxE, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro b hb
    rcases hb with hb | hb | hb
    · rw [hb]; exact httau
    · rw [hb]; exact hytau
    · rw [hb]; exact hztau
  have hle : zpowers tau ≤ Subgroup.centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hEtau
  intro a ha b hb
  exact (Subgroup.mem_centralizer_iff.mp (hle hb)) a ha

private theorem tau_conj_baseGrp (h : Ctx t L S x₁ x₂ lam rho tau) {a : G}
    (ha : a ∈ baseGrp x₁ x₂) : tau * a * tau⁻¹ = a⁻¹ := by
  rw [baseGrp] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]; exact h.tau_x₁
      · rw [hx]; exact h.tau_x₂
  | one => simp
  | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := baseGrp_comm h x hx y hy
      have hcomm_inv : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
        have h2 : (x * y)⁻¹ = (y * x)⁻¹ := by rw [hxy]
        rw [mul_inv_rev, mul_inv_rev] at h2
        exact h2.symm
      calc tau * (x * y) * tau⁻¹
          = (tau * x * tau⁻¹) * (tau * y * tau⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
        _ = y⁻¹ * x⁻¹ := hcomm_inv
        _ = (x * y)⁻¹ := by rw [mul_inv_rev]
  | inv x hx ihx =>
      calc tau * x⁻¹ * tau⁻¹
          = (tau * x * tau⁻¹)⁻¹ := by group
        _ = (x⁻¹)⁻¹ := by rw [ihx]

private theorem mem_zpowers_tau_of_sq_one (h44 : tau ^ 2 = 1) {u : G} (hu : u ∈ zpowers tau) :
    u = 1 ∨ u = tau := by
  have ht2 : tau * tau = 1 := by simpa [pow_two] using h44
  let K : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = tau}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb) <;> rw [ha, hb] <;> simp [ht2]
      inv_mem' := by
        rintro a (ha | ha)
        · rw [ha]; simp
        · rw [ha]; exact Or.inr (inv_eq_of_mul_eq_one_right ht2) }
  have hle : zpowers tau ≤ K := Subgroup.zpowers_le.mpr (Or.inr rfl)
  exact hle hu

private theorem ctxE_inf_L (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t) :
    ctxE t x₁ x₂ ⊓ L = fourGrp x₁ x₂ := by
  have hVE : fourGrp x₁ x₂ ≤ ctxE t x₁ x₂ := fourGrp_le_ctxE t x₁ x₂
  have hVL : fourGrp x₁ x₂ ≤ L := le_trans (fourGrp_le_baseGrp x₁ x₂) (baseGrp_le_L h.toCtx0)
  apply le_antisymm
  · intro e he
    rw [Subgroup.mem_inf] at he
    obtain ⟨heE, heL⟩ := he
    have hE_eq : ctxE t x₁ x₂ = zpowers t ⊔ fourGrp x₁ x₂ := ctxE_eq_sup t x₁ x₂
    have he' : e ∈ zpowers t ⊔ fourGrp x₁ x₂ := by rw [← hE_eq]; exact heE
    obtain ⟨a, ha, v, hv, heq⟩ :=
      (mem_sup_iff_of_commute (P := zpowers t) (Q := fourGrp x₁ x₂)
        (zpowers_t_commute_fourGrp h)).mp he'
    have haP : a ∈ twoCore t := by rw [h43]; exact ha
    have haL : a ∈ L := by
      have haeq : a = e * v⁻¹ := by rw [heq]; group
      rw [haeq]
      exact Subgroup.mul_mem L heL (Subgroup.inv_mem L (hVL hv))
    have habot : a ∈ twoCore t ⊓ L := ⟨haP, haL⟩
    rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at habot
    rw [heq, habot, one_mul]
    exact hv
  · exact le_inf hVE hVL

private theorem ctxX_inf_PL_eq_ctxE (h : Ctx t L S x₁ x₂ lam rho tau)
    (h44 : tau ^ 2 = 1) :
    ctxX t tau x₁ x₂ ⊓ (twoCore t ⊔ L) = ctxE t x₁ x₂ := by
  have hEX : ctxE t x₁ x₂ ≤ ctxX t tau x₁ x₂ := ctxE_le_ctxX t tau x₁ x₂
  have hEPL : ctxE t x₁ x₂ ≤ twoCore t ⊔ L := by
    rw [ctxE, Subgroup.closure_le]
    rintro g (hg : g ∈ ({t, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
    rcases hg with hg | hg | hg
    · rw [hg]; exact Subgroup.mem_sup_left h.hyp.mem_twoCore
    · rw [hg]; exact Subgroup.mem_sup_right (y_z_mem_L h.toCtx0).1
    · rw [hg]; exact Subgroup.mem_sup_right (y_z_mem_L h.toCtx0).2
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxX, hxPL⟩ := hx
    have hX_eq : ctxX t tau x₁ x₂ = ctxE t x₁ x₂ ⊔ zpowers tau := ctxX_eq_sup t tau x₁ x₂
    have hx' : x ∈ ctxE t x₁ x₂ ⊔ zpowers tau := by rw [← hX_eq]; exact hxX
    obtain ⟨e, he, u, hu, hxeu⟩ :=
      (mem_sup_iff_of_commute (P := ctxE t x₁ x₂) (Q := zpowers tau)
        (ctxE_commute_zpowers_tau h)).mp hx'
    have hePL : e ∈ twoCore t ⊔ L := hEPL he
    have huPL : u ∈ twoCore t ⊔ L := by
      have heq : e⁻¹ * x = u := by rw [hxeu]; group
      rw [← heq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hePL) hxPL
    rcases mem_zpowers_tau_of_sq_one h44 hu with hu1 | hutau
    · have hxe : x = e := by rw [hxeu, hu1, mul_one]
      rw [hxe]; exact he
    · rw [hutau] at huPL
      exact absurd huPL h.tau_not_mem
  · exact le_inf hEX hEPL

private theorem conj_mem_ctxX (h : Ctx t L S x₁ x₂ lam rho tau) {g : G}
    (hgen : ∀ x ∈ ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G),
      g * x * g⁻¹ ∈ ctxX t tau x₁ x₂)
    {x : G} (hx : x ∈ ctxX t tau x₁ x₂) : g * x * g⁻¹ ∈ ctxX t tau x₁ x₂ := by
  have hX : ctxX t tau x₁ x₂ ≤ (ctxX t tau x₁ x₂).comap (MulAut.conj g).toMonoidHom := by
    change Subgroup.closure {t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} ≤
      (ctxX t tau x₁ x₂).comap (MulAut.conj g).toMonoidHom
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_comap.mpr (hgen x hx)
  have := Subgroup.mem_comap.mp (hX hx)
  simpa [MulAut.conj_apply] using this

private theorem mem_ctxM_of (h : Ctx t L S x₁ x₂ lam rho tau) {g : G}
    (hgH : g ∈ invCent t)
    (hgNA : g ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G))
    (hgτ : g * tau * g⁻¹ ∈ ctxX t tau x₁ x₂) :
    g ∈ ctxM t tau x₁ x₂ := by
  have hVX : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := fourGrp_le_ctxX t tau x₁ x₂
  have hgen : ∀ x ∈ ({t, tau, x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G),
      g * x * g⁻¹ ∈ ctxX t tau x₁ x₂ := by
    intro x hx
    rcases hx with hx | hx | hx | hx
    · rw [hx]
      have hcomm : g * t = t * g := mem_invCent_iff.mp hgH
      have : g * t * g⁻¹ = t := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]; exact Subgroup.subset_closure (by simp)
    · rw [hx]; exact hgτ
    · rw [hx]
      have hx₁A : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
      have hconjA : g * x₁ * g⁻¹ ∈ baseGrp x₁ x₂ :=
        (Subgroup.mem_normalizer_iff.mp hgNA x₁).mp hx₁A
      have hsq : g * x₁ ^ 2 * g⁻¹ = (g * x₁ * g⁻¹) ^ 2 := by rw [conj_pow]
      rw [hsq]
      exact hVX (by
        rw [WreathRel.fourGrp_eq_mho h.wreath]
        exact Subgroup.subset_closure ⟨g * x₁ * g⁻¹, hconjA, rfl⟩)
    · rw [hx]
      have hx₁x₂A : x₁ * x₂ ∈ baseGrp x₁ x₂ :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
      have hconjA : g * (x₁ * x₂) * g⁻¹ ∈ baseGrp x₁ x₂ :=
        (Subgroup.mem_normalizer_iff.mp hgNA (x₁ * x₂)).mp hx₁x₂A
      have hsq : g * (x₁ * x₂) ^ 2 * g⁻¹ = (g * (x₁ * x₂) * g⁻¹) ^ 2 := by rw [conj_pow]
      rw [hsq]
      exact hVX (by
        rw [WreathRel.fourGrp_eq_mho h.wreath]
        exact Subgroup.subset_closure ⟨g * (x₁ * x₂) * g⁻¹, hconjA, rfl⟩)
  change g ∈ normalizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G)
  apply mem_normalizer_of_conj_mem
  intro w hw
  exact conj_mem_ctxX h hgen hw

private theorem normalizes_baseGrp_of (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) {g : G} (hgH : g ∈ invCent t)
    (hgM : g ∈ ctxM t tau x₁ x₂) :
    g ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hAL : baseGrp x₁ x₂ ≤ L := baseGrp_le_L h.toCtx0
  have hVA : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := fourGrp_le_baseGrp x₁ x₂
  have hyV : x₁ ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hgNP : g ∈ normalizer ((twoCore t : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem (fun p hp => twoCore_conj_mem t hgH hp)
  have hgNL : g ∈ normalizer ((L : Subgroup G) : Set G) :=
    mem_normalizer_of_conj_mem (fun l hl => conj_mem_L h.hyp hgH hl)
  have hgNPL : g ∈ normalizer ((twoCore t ⊔ L : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro w hw
    obtain ⟨p, hp, l, hl, rfl⟩ := (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hw
    have hp' : g * p * g⁻¹ ∈ twoCore t := twoCore_conj_mem t hgH hp
    have hl' : g * l * g⁻¹ ∈ L := conj_mem_L h.hyp hgH hl
    have heq : g * (p * l) * g⁻¹ = (g * p * g⁻¹) * (g * l * g⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp') (Subgroup.mem_sup_right hl')
  have hgNXPL : g ∈
      normalizer (((ctxX t tau x₁ x₂ ⊓ (twoCore t ⊔ L)) : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro e he
    rw [Subgroup.mem_inf] at he
    obtain ⟨heX, hePL⟩ := he
    exact ⟨(Subgroup.mem_normalizer_iff.mp hgM e).mp heX,
      (Subgroup.mem_normalizer_iff.mp hgNPL e).mp hePL⟩
  have hgNE : g ∈ normalizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) := by
    rwa [ctxX_inf_PL_eq_ctxE h h44] at hgNXPL
  have hgNV : g ∈ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hgNEL : g ∈ normalizer (((ctxE t x₁ x₂ ⊓ L) : Subgroup G) : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro e he
      rw [Subgroup.mem_inf] at he
      obtain ⟨heE, heL⟩ := he
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgNE e).mp heE,
        (Subgroup.mem_normalizer_iff.mp hgNL e).mp heL⟩
    rwa [ctxE_inf_L h h43] at hgNEL
  apply mem_normalizer_of_conj_mem
  intro a ha
  have hkL : g * a * g⁻¹ ∈ L := conj_mem_L h.hyp hgH (hAL ha)
  have hky : (g * a * g⁻¹) * x₁ ^ 2 = x₁ ^ 2 * (g * a * g⁻¹) := by
    have hu : g⁻¹ * x₁ ^ 2 * g ∈ fourGrp x₁ x₂ :=
      ((Subgroup.mem_normalizer_iff''.mp hgNV) (x₁ ^ 2)).mp hyV
    have hcomm : a * (g⁻¹ * x₁ ^ 2 * g) = (g⁻¹ * x₁ ^ 2 * g) * a :=
      baseGrp_comm h a ha (g⁻¹ * x₁ ^ 2 * g) (hVA hu)
    calc (g * a * g⁻¹) * x₁ ^ 2
        = g * (a * (g⁻¹ * x₁ ^ 2 * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x₁ ^ 2 * g) * a) * g⁻¹ := by rw [hcomm]
      _ = (g * (g⁻¹ * x₁ ^ 2 * g) * g⁻¹) * (g * a * g⁻¹) := by group
      _ = x₁ ^ 2 * (g * a * g⁻¹) := by group
  have hkz : (g * a * g⁻¹) * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * (g * a * g⁻¹) := by
    have hu : g⁻¹ * (x₁ * x₂) ^ 2 * g ∈ fourGrp x₁ x₂ :=
      ((Subgroup.mem_normalizer_iff''.mp hgNV) ((x₁ * x₂) ^ 2)).mp hzV
    have hcomm : a * (g⁻¹ * (x₁ * x₂) ^ 2 * g) = (g⁻¹ * (x₁ * x₂) ^ 2 * g) * a :=
      baseGrp_comm h a ha (g⁻¹ * (x₁ * x₂) ^ 2 * g) (hVA hu)
    calc (g * a * g⁻¹) * (x₁ * x₂) ^ 2
        = g * (a * (g⁻¹ * (x₁ * x₂) ^ 2 * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * (x₁ * x₂) ^ 2 * g) * a) * g⁻¹ := by rw [hcomm]
      _ = (g * (g⁻¹ * (x₁ * x₂) ^ 2 * g) * g⁻¹) * (g * a * g⁻¹) := by group
      _ = (x₁ * x₂) ^ 2 * (g * a * g⁻¹) := by group
  exact cent_fourGrp_of_ctx0 h.toCtx0 (g * a * g⁻¹) hkL hky hkz

theorem normalizer_X_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) :
    invCent t ⊓ ctxM t tau x₁ x₂ = ctxW t x₁ x₂ ⊔ closure {tau, rho, lam} := by
  have hAL : baseGrp x₁ x₂ ≤ L := baseGrp_le_L h.toCtx0
  have hset : ({rho, lam, tau} : Set G) = {tau, rho, lam} := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hnorm : invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
      ctxW t x₁ x₂ ⊔ closure {tau, rho, lam} := by
    rw [h.norm_baseGrp, congrArg Subgroup.closure hset]
  have htH : t ∈ invCent t := by rw [mem_invCent_iff]
  have htauH : tau ∈ invCent t := h.toCtx0.le_invCent h.tau_mem
  have hrhoH : rho ∈ invCent t := L_le_invCent h.hyp h.toCtx0.rho_mem
  have hlamH : lam ∈ invCent t := L_le_invCent h.hyp (generators_mem_L h.toCtx0).2.2
  have htNA : t ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro a ha
    have hat : a * t = t * a :=
      Subgroup.mem_centralizer_iff.mp h.hyp.mem_centralizer a (hAL ha)
    have : t * a * t⁻¹ = a := by rw [← hat, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact ha
  have htτ : t * tau * t⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have hcomm : t * tau = tau * t := (mem_invCent_iff.mp htauH).symm
    have : t * tau * t⁻¹ = tau := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact Subgroup.subset_closure (by simp)
  have htM : t ∈ ctxM t tau x₁ x₂ := mem_ctxM_of h htH htNA htτ
  have htauNA : tau ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro a ha
    rw [tau_conj_baseGrp h ha]
    exact Subgroup.inv_mem (baseGrp x₁ x₂) ha
  have htauτ : tau * tau * tau⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have : tau * tau * tau⁻¹ = tau := by group
    rw [this]; exact Subgroup.subset_closure (by simp)
  have htauM : tau ∈ ctxM t tau x₁ x₂ := mem_ctxM_of h htauH htauNA htauτ
  have hx1H : x₁ ∈ invCent t := L_le_invCent h.hyp (generators_mem_L h.toCtx0).1
  have hx2H : x₂ ∈ invCent t := L_le_invCent h.hyp (generators_mem_L h.toCtx0).2.1
  have hx1NA : x₁ ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (H := baseGrp x₁ x₂) (Subgroup.subset_closure (by simp))
  have hx2NA : x₂ ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (H := baseGrp x₁ x₂) (Subgroup.subset_closure (by simp))
  have hx1τ : x₁ * tau * x₁⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have h1 : x₁ * tau * x₁⁻¹ = x₁ ^ 2 * tau := by
      calc x₁ * tau * x₁⁻¹
          = x₁ * (tau * x₁⁻¹ * tau⁻¹) * tau := by group
        _ = x₁ * (tau * x₁ * tau⁻¹)⁻¹ * tau := by
              rw [show tau * x₁⁻¹ * tau⁻¹ = (tau * x₁ * tau⁻¹)⁻¹ by group]
        _ = x₁ * (x₁⁻¹)⁻¹ * tau := by rw [h.tau_x₁]
        _ = x₁ ^ 2 * tau := by rw [inv_inv, pow_two]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  have hx2τ : x₂ * tau * x₂⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have h2 : x₂ * tau * x₂⁻¹ = x₂ ^ 2 * tau := by
      calc x₂ * tau * x₂⁻¹
          = x₂ * (tau * x₂⁻¹ * tau⁻¹) * tau := by group
        _ = x₂ * (tau * x₂ * tau⁻¹)⁻¹ * tau := by
              rw [show tau * x₂⁻¹ * tau⁻¹ = (tau * x₂ * tau⁻¹)⁻¹ by group]
        _ = x₂ * (x₂⁻¹)⁻¹ * tau := by rw [h.tau_x₂]
        _ = x₂ ^ 2 * tau := by rw [inv_inv, pow_two]
    rw [h2, WreathRel.x₂_sq h.wreath]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  have hx1M : x₁ ∈ ctxM t tau x₁ x₂ := mem_ctxM_of h hx1H hx1NA hx1τ
  have hx2M : x₂ ∈ ctxM t tau x₁ x₂ := mem_ctxM_of h hx2H hx2NA hx2τ
  have hrhoNA : rho ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro a ha
    have hconjW : rho * a * rho⁻¹ ∈ ctxW t x₁ x₂ :=
      (Subgroup.mem_normalizer_iff.mp h.toCtx0.rho_normalizes a).mp (Subgroup.mem_sup_right ha)
    have hconjL : rho * a * rho⁻¹ ∈ L := conj_mem_L h.hyp hrhoH (hAL ha)
    have hmem : rho * a * rho⁻¹ ∈ ctxW t x₁ x₂ ⊓ L := ⟨hconjW, hconjL⟩
    rwa [ctxW_inf_L h] at hmem
  have hrhoτ : rho * tau * rho⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have hcomm : rho * tau = tau * rho := h.tau_rho.symm
    have : rho * tau * rho⁻¹ = tau := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact Subgroup.subset_closure (by simp)
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := mem_ctxM_of h hrhoH hrhoNA hrhoτ
  have hlamNA : lam ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have hlam2 : lam * lam = 1 := by
      have := pow_orderOf_eq_one lam
      rw [h.wreath.ord_lam] at this
      simpa [pow_two] using this
    have hconj_x₂ : lam * x₂ * lam⁻¹ = x₁ := by
      rw [← h.wreath.conj_x₁]
      calc lam * (lam * x₁ * lam⁻¹) * lam⁻¹
          = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by group
        _ = x₁ := by rw [hlam2, ← mul_inv_rev, hlam2, inv_one, one_mul, mul_one]
    have hA : baseGrp x₁ x₂ ≤ (baseGrp x₁ x₂).comap (MulAut.conj lam).toMonoidHom := by
      change Subgroup.closure {x₁, x₂} ≤
        (baseGrp x₁ x₂).comap (MulAut.conj lam).toMonoidHom
      rw [Subgroup.closure_le]
      intro x hx
      apply Subgroup.mem_comap.mpr
      rcases hx with hx | hx
      · rw [hx]
        rw [show (MulAut.conj lam).toMonoidHom x₁ = x₂ from by
              simpa [MulAut.conj_apply] using h.wreath.conj_x₁]
        exact Subgroup.subset_closure (by simp)
      · rw [hx]
        rw [show (MulAut.conj lam).toMonoidHom x₂ = x₁ from by
              simpa [MulAut.conj_apply] using hconj_x₂]
        exact Subgroup.subset_closure (by simp)
    apply mem_normalizer_of_conj_mem
    intro a ha
    simpa [MulAut.conj_apply] using Subgroup.mem_comap.mp (hA ha)
  have hlamτ : lam * tau * lam⁻¹ ∈ ctxX t tau x₁ x₂ := by
    have hcomm : lam * tau = tau * lam := h.tau_lam.symm
    have : lam * tau * lam⁻¹ = tau := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact Subgroup.subset_closure (by simp)
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := mem_ctxM_of h hlamH hlamNA hlamτ
  have hAM : baseGrp x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
    rw [baseGrp]
    refine (Subgroup.closure_le (ctxM t tau x₁ x₂)).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hx1M
    · exact hx2M
  have hPM : twoCore t ≤ ctxM t tau x₁ x₂ := by
    rw [h43]
    exact Subgroup.zpowers_le.mpr htM
  have hWM : ctxW t x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
    rw [ctxW]
    exact sup_le hPM hAM
  have hWH : ctxW t x₁ x₂ ≤ invCent t :=
    sup_le (twoCore_le_invCent t) (le_trans hAL (L_le_invCent h.hyp))
  have hclM : closure {tau, rho, lam} ≤ ctxM t tau x₁ x₂ := by
    rw [Subgroup.closure_le]
    rintro x (hx : x ∈ ({tau, rho, lam} : Set G))
    rcases hx with rfl | rfl | rfl
    · exact htauM
    · exact hrhoM
    · exact hlamM
  have hclH : closure {tau, rho, lam} ≤ invCent t := by
    rw [Subgroup.closure_le]
    rintro x (hx : x ∈ ({tau, rho, lam} : Set G))
    rcases hx with rfl | rfl | rfl
    · exact htauH
    · exact hrhoH
    · exact hlamH
  apply le_antisymm
  · calc invCent t ⊓ ctxM t tau x₁ x₂
        ≤ invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) :=
          fun g hg => ⟨hg.1, normalizes_baseGrp_of h h43 h44 hg.1 hg.2⟩
      _ = ctxW t x₁ x₂ ⊔ closure {tau, rho, lam} := hnorm
  · exact sup_le (le_inf hWH hWM) (le_inf hclH hclM)

theorem exists_action_on_X_of (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) :
    ∃ ρ : ↥(ctxM t tau x₁ x₂) →* MulAut ↥(ctxX t tau x₁ x₂),
      (∀ (m : ↥(ctxM t tau x₁ x₂)) (x : ↥(ctxX t tau x₁ x₂)),
        ((ρ m x : ↥(ctxX t tau x₁ x₂)) : G) = (m : G) * (x : G) * (m : G)⁻¹) ∧
      ∀ m : ↥(ctxM t tau x₁ x₂), ρ m = 1 ↔ (m : G) ∈ ctxX t tau x₁ x₂ := by
  unfold ctxM
  refine ⟨(ctxX t tau x₁ x₂).normalizerMonoidHom, ?_, ?_⟩
  · intro m x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (ctxX t tau x₁ x₂) m x
  · intro m
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      centralizer_X_of h h43 h44]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
