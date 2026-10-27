module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Kernel
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WFive

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open scoped Matrix

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.act_mem_Vsub_of_mem_normalizer (hd : d.Hyp) {c : G}
    (hcL : c ∈ normalizer (d.L : Set G)) (hcA : c ∈ normalizer (d.A₁ : Set G)) {x : Gam h}
    (hx : Phi h x = d.act ⟨c, hcL⟩) {v : hypSU h 2 1} (hv : v ∈ Vsub h) :
    actΓ h x v ∈ Vsub h := by
  have h1 : c * d.η v * c⁻¹ ∈ d.A₁ := (mem_normalizer_iff.1 hcA _).1 ⟨v, hv, rfl⟩
  rw [d.conj_η_eq hcL hx] at h1
  obtain ⟨v', hv', he⟩ := h1
  have e : actΓ h x v = v' := by
    refine eq_of_innM_eq_of_sq hd.center_hypPSU (d.innM_eq_of_η_eq he.symm) ?_ (Vsub_sq hv')
    rw [← CFSG.RankThree.PartOne.U5K.Hyp.act_mul, Vsub_sq hv,
      CFSG.RankThree.PartOne.U5K.Hyp.act_one]
  rw [e]
  exact hv'

theorem Hyp.act_mem_Ssub_of_mem_normalizer (hd : d.Hyp) {c : G}
    (hcL : c ∈ normalizer (d.L : Set G)) (hcA : c ∈ normalizer (d.A₃ : Set G)) {x : Gam h}
    (hx : Phi h x = d.act ⟨c, hcL⟩) {g : hypSU h 2 1} (hg : g ∈ Ssub h) :
    actΓ h x g ∈ Ssub h := by
  have h1 : c * d.η g * c⁻¹ ∈ d.A₃ := (mem_normalizer_iff.1 hcA _).1 ⟨g, hg, rfl⟩
  rw [d.conj_η_eq hcL hx] at h1
  obtain ⟨g', hg', he⟩ := h1
  have e : actΓ h x g = g' := by
    refine eq_of_innM_eq_of_two hd.center_hypPSU (d.innM_eq_of_η_eq he.symm) (k := 2) ?_
      (Ssub_pow_four hg')
    rw [← act_pow]
    exact (congrArg (actΓ h x) (Ssub_pow_four hg)).trans
      (CFSG.RankThree.PartOne.U5K.Hyp.act_one x)
  rw [e]
  exact hg'

theorem Hyp.exists_semilinear (hd : d.Hyp) {c : G}
    (hc : c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G)) :
    ∃ (σ : K ≃+* K) (κ : K) (M : Matrix (Fin 2) (Fin 2) K), κ ≠ 0 ∧ M.det ≠ 0 ∧
      ∀ g ∈ Ssub h, ∃ g' ∈ Ssub h, c * d.η g * c⁻¹ = d.η g' ∧
        crd g' = κ • (M *ᵥ fun i => σ (crd g i)) := by
  have hcL := hd.centralizer_le_normalizer hc.2
  obtain ⟨x, hx⟩ := Phi_surjective h (d.act ⟨c, hcL⟩)
  have hV := fun v (hv : v ∈ Vsub h) =>
    hd.act_mem_Vsub_of_mem_normalizer hcL (hd.normalizer_B₁_le_normalizer_A₁ hc.1) hx hv
  obtain ⟨κ, M, hκ, hM, hcrd⟩ := exists_semilinear_crd (hV _ (ZPsub_le_Vsub z₁SU_mem_ZPsub))
    (hV _ (vSU_mem_Vsub (isHerm_e₂₂ h)))
  refine ⟨x.1.right, κ, M, hκ, hM, fun g hg => ?_⟩
  have hg' := hd.act_mem_Ssub_of_mem_normalizer hcL (hd.normalizer_B₁_le_normalizer_A₃ hc.1) hx hg
  exact ⟨actΓ h x g, hg', d.conj_η_eq hcL hx g, hcrd g hg hg'⟩

theorem Hyp.act_pow_four_of_commutator_mem_A₁ (hd : d.Hyp) {c : G}
    (hc : c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G))
    (hcA : ∀ a ∈ d.A₃, c * a * c⁻¹ * a⁻¹ ∈ d.A₁) :
    d.act ⟨c, hd.centralizer_le_normalizer hc.2⟩ ^ 4 = 1 := by
  set hcL := hd.centralizer_le_normalizer hc.2
  obtain ⟨x, hx⟩ := Phi_surjective h (d.act ⟨c, hcL⟩)
  have hA₃ := hd.normalizer_B₁_le_normalizer_A₃ hc.1
  have hS : ∀ g ∈ Ssub h, actΓ h x g ∈ Ssub h ∧ crd (actΓ h x g) = crd g := by
    intro g hg
    have hg' := hd.act_mem_Ssub_of_mem_normalizer hcL hA₃ hx hg
    refine ⟨hg', ?_⟩
    obtain ⟨v, hv, hve⟩ := hcA (d.η g) ⟨g, hg, rfl⟩
    have e : actΓ h x g = v * g := by
      refine d.η_injOn (Ssub_le_Usub hg') (mul_mem (Ssub_le_Usub (Vsub_le_Ssub hv))
        (Ssub_le_Usub hg)) ?_
      rw [← d.conj_η_eq hcL hx, map_mul, hve, inv_mul_cancel_right]
    rw [e, crd_mul (Vsub_le_Ssub hv) hg, (crd_eq_zero_iff (Vsub_le_Ssub hv)).2 hv, zero_add]
  rw [← hx]
  exact pow_four_eq_one_of_fixes (fun v hv =>
    hd.act_mem_Vsub_of_mem_normalizer hcL (hd.normalizer_B₁_le_normalizer_A₁ hc.1) hx hv) hS

theorem Hyp.mem_B₃_of_commutator_mem_A₁ (hd : d.Hyp) {c : G}
    (hc : c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G))
    (hcA : ∀ a ∈ d.A₃, c * a * c⁻¹ * a⁻¹ ∈ d.A₁) : c ∈ d.B₃ := by
  have hA₁ : ∀ {n : G}, n ∈ normalizer (d.B₁ : Set G) → ∀ a ∈ d.A₁, n * a * n⁻¹ ∈ d.A₁ :=
    fun hn a ha => (mem_normalizer_iff.1 (hd.normalizer_B₁_le_normalizer_A₁ hn) a).1 ha
  have hA₃ : ∀ {n : G}, n ∈ normalizer (d.B₁ : Set G) → ∀ a ∈ d.A₃, n * a * n⁻¹ ∈ d.A₃ :=
    fun hn a ha => (mem_normalizer_iff.1 (hd.normalizer_B₁_le_normalizer_A₃ hn) a).1 ha
  let R : Subgroup G :=
    { carrier := {c | c ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) ∧
        ∀ a ∈ d.A₃, c * a * c⁻¹ * a⁻¹ ∈ d.A₁}
      mul_mem' := by
        rintro c₁ c₂ ⟨hc₁, h₁⟩ ⟨hc₂, h₂⟩
        refine ⟨mul_mem hc₁ hc₂, fun a ha => ?_⟩
        have e : c₁ * c₂ * a * (c₁ * c₂)⁻¹ * a⁻¹ =
            c₁ * (c₂ * a * c₂⁻¹ * a⁻¹) * c₁⁻¹ * (c₁ * a * c₁⁻¹ * a⁻¹) := by group
        rw [e]
        exact mul_mem (hA₁ hc₁.1 _ (h₂ a ha)) (h₁ a ha)
      one_mem' := ⟨one_mem _, fun a ha => by
        rw [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact one_mem _⟩
      inv_mem' := by
        rintro c ⟨hc, h₁⟩
        refine ⟨inv_mem hc, fun a ha => ?_⟩
        have ha' : c⁻¹ * a * c⁻¹⁻¹ ∈ d.A₃ := hA₃ (inv_mem hc.1) a ha
        have := inv_mem (h₁ _ ha')
        rwa [show (c * (c⁻¹ * a * c⁻¹⁻¹) * c⁻¹ * (c⁻¹ * a * c⁻¹⁻¹)⁻¹)⁻¹ =
          c⁻¹ * a * c⁻¹⁻¹ * a⁻¹ by group] at this }
  have hR : R ≤ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) := fun _ hr => hr.1
  have hRn : normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      normalizer (R : Set G) := by
    intro n hn
    refine mem_normalizer_fintype fun r hr => ⟨mul_mem (mul_mem hn hr.1) (inv_mem hn),
      fun a ha => ?_⟩
    have ha' : n⁻¹ * a * n⁻¹⁻¹ ∈ d.A₃ := hA₃ (inv_mem hn.1) a ha
    have := hA₁ hn.1 _ (hr.2 _ ha')
    rwa [show n * (r * (n⁻¹ * a * n⁻¹⁻¹) * r⁻¹ * (n⁻¹ * a * n⁻¹⁻¹)⁻¹) * n⁻¹ =
      n * r * n⁻¹ * a * (n * r * n⁻¹)⁻¹ * a⁻¹ by group] at this
  have hR2 : IsPGroup 2 R := by
    rintro ⟨r, hr⟩
    refine ⟨3, Subtype.ext ?_⟩
    have hrL := hd.centralizer_le_normalizer hr.1.2
    have h4 := hd.act_pow_four_of_commutator_mem_A₁ hr.1 hr.2
    rw [← map_pow] at h4
    have hc4 : r ^ 4 ∈ zpowers d.t := by
      rw [← hd.sec3_1'.1]
      refine ⟨?_, pow_mem hr.1.2 4⟩
      have := (d.act_eq_one_iff _).1 h4
      rwa [Subgroup.coe_pow] at this
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hc4
    have ht2 : d.t ^ 2 = 1 := by rw [sq, hd.t_mul_t]
    have h8 : r ^ 8 = 1 := by
      rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
        zpow_mul, zpow_natCast, ht2, one_zpow]
    simpa using h8
  exact hd.le_B₃_of_normal hR hRn hR2 ⟨hc, hcA⟩

theorem Hyp.t_not_mem_centralizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.t ∉ centralizer (d.F : Set G) := by
  intro ht
  have hle : d.F ≤ d.A₁ := by
    rw [← hd.F_inf_centralizer_t hGMS]
    exact fun x hx => ⟨hx, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht x hx)⟩
  have h1 := Subgroup.card_le_of_le hle
  rw [hd.card_F hGMS, d.card_A₁] at h1
  have h4 := hd.four_le
  have : (2 ^ f) ^ 4 < (2 ^ f) ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem Hyp.A₃_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.A₃ ≤ normalizer (d.F : Set G) :=
  d.A₃_le_P.trans (hd.P_le_normalizer_F hGMS)

theorem Hyp.A₃_le_centralizer_F (hd : d.Hyp) : d.A₃ ≤ centralizer (d.F : Set G) :=
  Subgroup.le_centralizer_iff.1 hd.F_le_centralizer_A₃

theorem Hyp.elemAbMod_F_FA₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ElemAbMod d.F (d.F ⊔ d.A₃) :=
  ElemAbMod.sup_of_le_normalizer (hd.A₃_le_normalizer_F hGMS)
    (ElemAbMod.of_le d.elemAbMod_A₁_A₃ hd.A₁_le_F)

theorem Hyp.elemAbMod_F_FB₃ (hd : d.Hyp) : ElemAbMod d.F (d.F ⊔ d.B₃) :=
  ElemAbMod.sup_of_le_normalizer hd.B₃_le_normalizer_F
    (ElemAbMod.of_le hd.elemAbMod_A₁_B₃ hd.A₁_le_F)

theorem Hyp.exists_of_mem_FB₃ (hd : d.Hyp) {x : G} (hx : x ∈ d.F ⊔ d.B₃) :
    ∃ y ∈ d.F, ∃ a ∈ d.A₃, x = y * a ∨ x = y * (d.t * a) := by
  obtain ⟨y, hy, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hd.B₃_le_normalizer_F hx
  obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup (d.A₃_le_P.trans d.P_le_L) hb <;>
    subst b
  · exact ⟨y, hy, a, ha, Or.inl rfl⟩
  · exact ⟨y, hy, a, ha, Or.inr rfl⟩

theorem Hyp.t_not_mem_FA₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.t ∉ d.F ⊔ d.A₃ := by
  intro ht
  obtain ⟨y, hy, a, ha, e⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer (hd.A₃_le_normalizer_F hGMS) ht
  have haL : a ∈ d.L := d.A₃_le_P.trans d.P_le_L ha
  have hyA : y ∈ d.A₁ := by
    rw [← hd.F_inf_centralizer_t hGMS]
    refine ⟨hy, mem_centralizer_singleton_iff.2 ?_⟩
    have hy' : y = d.t * a⁻¹ := by rw [e, mul_inv_cancel_right]
    rw [hy', mul_assoc, hd.comm_t (inv_mem haL)]
  exact hd.t_not_mem_L (e ▸ mul_mem (d.A₁_le_P.trans d.P_le_L hyA) haL)

theorem Hyp.FB₃_inf_centralizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (d.F ⊔ d.B₃) ⊓ centralizer (d.F : Set G) = d.F ⊔ d.A₃ := by
  have hFc : d.F ≤ centralizer (d.F : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => hd.F_comm hGMS y hy x hx
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le_sup_left d.A₃_le_B₃ _)
    (sup_le hFc hd.A₃_le_centralizer_F))
  obtain ⟨y, hy, a, ha, e | e⟩ := hd.exists_of_mem_FB₃ hx.1
  · rw [e]
    exact mul_mem (mem_sup_left hy) (mem_sup_right ha)
  · exfalso
    apply hd.t_not_mem_centralizer_F hGMS
    have h1 : d.t * a ∈ centralizer (d.F : Set G) := by
      have := mul_mem (inv_mem (hFc hy)) (e ▸ hx.2)
      rwa [inv_mul_cancel_left] at this
    have := mul_mem h1 (inv_mem (hd.A₃_le_centralizer_F ha))
    rwa [mul_inv_cancel_right] at this

theorem Hyp.normalizer_FB₃_le_normalizer_F (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) ≤ normalizer (d.F : Set G) := by
  intro n hn
  set F' := d.F.map (MulAut.conj n).toMonoidHom with hF'
  have hF'FT : F' ≤ d.F ⊔ d.T := by
    rintro _ ⟨y, hy, rfl⟩
    have := (mem_normalizer_iff.1 hn y).1 (mem_sup_left hy)
    exact sup_le_sup_left (d.B₃_le_tP.trans hd.tP_le_T) _ this
  have hF'el : CFSG.IsElementaryAbelian 2 F' := by
    refine isElementaryAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hd.F_comm hGMS x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, hd.mul_self_eq_one_of_mem_F hGMS hx, map_one]
  have hcard : Nat.card F' = (2 ^ f) ^ 8 := by
    rw [hF', card_map_of_injective (MulAut.conj n).injective, hd.card_F hGMS]
  exact mem_normalizer_of_map_conj_eq ((hd.card_le_of_le_FT hGMS hF'FT hF'el).2 hcard.ge)

theorem Hyp.normalizer_FB₃_le_normalizer_FA₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) ≤
      normalizer ((d.F ⊔ d.A₃ : Subgroup G) : Set G) := by
  intro n hn
  rw [← hd.FB₃_inf_centralizer_F hGMS]
  exact Common.mem_normalizer_inf hn
    (Prelim.normalizer_le_normalizer_centralizer d.F (hd.normalizer_FB₃_le_normalizer_F hGMS hn))

theorem Hyp.normalizer_B₁_le_normalizer_FB₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) :
    normalizer (d.B₁ : Set G) ≤ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := fun _ hn =>
  Common.mem_normalizer_sup (hd.normalizer_B₁_le_normalizer_F hGMS hn) (hd.normalizer_B₁_le hn)

theorem Hyp.cr_mem_FA₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {n : G}
    (hn : n ∈ normalizer ((d.F ⊔ d.B₃ : Subgroup G) : Set G)) :
    n⁻¹ * d.t * n * d.t ∈ d.F ⊔ d.A₃ := by
  have h1 : n⁻¹ * d.t * n ∈ d.F ⊔ d.B₃ := by
    have := (mem_normalizer_iff.1 (inv_mem hn) d.t).1
      (mem_sup_right (mem_sup_left (mem_zpowers _)))
    rwa [inv_inv] at this
  obtain ⟨y, hy, a, ha, e | e⟩ := hd.exists_of_mem_FB₃ h1
  · exfalso
    apply hd.t_not_mem_FA₃ hGMS
    have h2 : n⁻¹ * d.t * n ∈ d.F ⊔ d.A₃ := e ▸ mul_mem (mem_sup_left hy) (mem_sup_right ha)
    have := (mem_normalizer_iff.1 (hd.normalizer_FB₃_le_normalizer_FA₃ hGMS hn) _).1 h2
    rwa [show n * (n⁻¹ * d.t * n) * n⁻¹ = d.t by group] at this
  · rw [e, mul_assoc, mul_assoc, (hd.comm_t (d.A₃_le_P.trans d.P_le_L ha)), ← mul_assoc d.t,
      hd.t_mul_t, one_mul]
    exact mul_mem (mem_sup_left hy) (mem_sup_right ha)

theorem Hyp.mem_normalizer_B₁_of_conj (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {x : G} (hxF : x ∈ normalizer (d.F : Set G))
    (hxt : (x * d.t * x⁻¹)⁻¹ * d.t ∈ d.F) : x ∈ normalizer (d.B₁ : Set G) := by
  set f₀ := (x * d.t * x⁻¹)⁻¹ * d.t with hf₀
  have hFc := hd.F_comm hGMS
  have hf₀inv : f₀⁻¹ = f₀ := inv_eq_of_mul_eq_one_right (hd.mul_self_eq_one_of_mem_F hGMS hxt)
  have hy : x * d.t * x⁻¹ = d.t * f₀ := by
    have e : x * d.t * x⁻¹ = d.t * f₀⁻¹ := by rw [hf₀]; group
    rw [e, hf₀inv]
  have hyy : (d.t * f₀) * (d.t * f₀) = 1 := by
    rw [← hy]
    calc x * d.t * x⁻¹ * (x * d.t * x⁻¹) = x * (d.t * d.t) * x⁻¹ := by group
      _ = 1 := by rw [hd.t_mul_t]; group
  have hf₀t : f₀ * d.t = d.t * f₀ := by
    have e : d.t * f₀ * d.t = f₀⁻¹ := by
      calc d.t * f₀ * d.t = (d.t * f₀ * (d.t * f₀)) * f₀⁻¹ := by group
        _ = f₀⁻¹ := by rw [hyy, one_mul]
    calc f₀ * d.t = d.t * (d.t * f₀ * d.t) := by
          rw [← mul_assoc, ← mul_assoc, hd.t_mul_t, one_mul]
      _ = d.t * f₀ := by rw [e, hf₀inv]
  have hf₀A : f₀ ∈ d.A₁ := by
    rw [← hd.F_inf_centralizer_t hGMS]
    exact ⟨hxt, mem_centralizer_singleton_iff.2 hf₀t⟩
  have hA : ∀ a ∈ d.A₁, x * a * x⁻¹ ∈ d.A₁ := by
    intro a ha
    have haF : x * a * x⁻¹ ∈ d.F := (mem_normalizer_iff.1 hxF a).1 (hd.A₁_le_F ha)
    rw [← hd.F_inf_centralizer_t hGMS]
    refine ⟨haF, mem_centralizer_singleton_iff.2 ?_⟩
    have hat : a * d.t = d.t * a := hd.comm_t (d.A₁_le_P.trans d.P_le_L ha)
    have h1 : (x * a * x⁻¹) * (x * d.t * x⁻¹) = (x * d.t * x⁻¹) * (x * a * x⁻¹) := by
      calc (x * a * x⁻¹) * (x * d.t * x⁻¹) = x * (a * d.t) * x⁻¹ := by group
        _ = x * (d.t * a) * x⁻¹ := by rw [hat]
        _ = (x * d.t * x⁻¹) * (x * a * x⁻¹) := by group
    rw [hy] at h1
    have h2 : (x * a * x⁻¹) * f₀ = f₀ * (x * a * x⁻¹) := hFc _ haF _ hxt
    have h3 : (x * a * x⁻¹) * d.t * f₀ = d.t * (x * a * x⁻¹) * f₀ := by
      calc (x * a * x⁻¹) * d.t * f₀ = (x * a * x⁻¹) * (d.t * f₀) := by group
        _ = d.t * f₀ * (x * a * x⁻¹) := h1
        _ = d.t * (f₀ * (x * a * x⁻¹)) := by group
        _ = d.t * ((x * a * x⁻¹) * f₀) := by rw [h2]
        _ = d.t * (x * a * x⁻¹) * f₀ := by group
    exact mul_right_cancel h3
  refine mem_normalizer_fintype fun b hb => ?_
  obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup (d.A₁_le_P.trans d.P_le_L) hb <;>
    subst b
  · exact mem_sup_right (hA a ha)
  · rw [show x * (d.t * a) * x⁻¹ = (x * d.t * x⁻¹) * (x * a * x⁻¹) by group, hy, mul_assoc]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mul_mem hf₀A (hA a ha)))

end Data

end CFSG.LocalAnalysis.EvenBN.U5
