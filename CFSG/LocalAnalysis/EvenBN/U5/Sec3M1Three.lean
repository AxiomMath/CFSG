module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Two
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem conj_sSU_mem_patSub_I₁ {g : hypSU h 2 1} (hg : g ∈ patSub h sI₄ isPattern_sI₄) :
    sSU h * g * (sSU h)⁻¹ ∈ patSub h sI₁ isPattern_sI₁ :=
  conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sI₄ isPattern_sI₁ (by decide) hg

theorem conj_sSU_mem_patSub_I₄ {g : hypSU h 2 1} (hg : g ∈ patSub h sI₁ isPattern_sI₁) :
    sSU h * g * (sSU h)⁻¹ ∈ patSub h sI₄ isPattern_sI₄ :=
  conj_perm_mem_patSub σs_σs σs_partner mat_sSU isPattern_sI₁ isPattern_sI₄ (by decide) hg

theorem map_conj_sSU_patSub_I₄ :
    (patSub h sI₄ isPattern_sI₄).map (MulAut.conj (sSU h)).toMonoidHom =
      patSub h sI₁ isPattern_sI₁ := by
  have hs : (sSU h)⁻¹ = sSU h := inv_eq_of_mul_eq_one_right sSU_mul_self
  refine le_antisymm ?_ fun g hg => ?_
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_sSU_mem_patSub_I₁ hg
  · refine ⟨_, conj_sSU_mem_patSub_I₄ hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hs]
    rw [← mul_assoc, ← mul_assoc, sSU_mul_self, one_mul, mul_assoc, sSU_mul_self, mul_one]

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

@[expose] def V₁ (d : Data G h) : Subgroup G :=
  (d.F ⊓ centralizer (d.I₄ : Set G)).map (MulAut.conj d.s).toMonoidHom

omit [Finite G] in
theorem s_mul_s (d : Data G h) : d.s * d.s = 1 := by
  rw [Data.s, ← map_mul, sSU_mul_self, map_one]

omit [Finite G] in
theorem s_inv (d : Data G h) : d.s⁻¹ = d.s := inv_eq_of_mul_eq_one_right d.s_mul_s

omit [Finite G] in
theorem mem_map_conj_s {X : Subgroup G} {x : G} :
    x ∈ X.map (MulAut.conj d.s).toMonoidHom ↔ d.s * x * d.s ∈ X := by
  rw [mem_map_equiv, MulAut.conj_symm_apply, d.s_inv]

omit [Finite G] in
theorem s_conj_s_conj (d : Data G h) (x : G) : d.s * (d.s * x * d.s) * d.s = x := by
  calc d.s * (d.s * x * d.s) * d.s = (d.s * d.s) * x * (d.s * d.s) := by group
    _ = x := by rw [d.s_mul_s, one_mul, mul_one]

theorem Hyp.U₁_eq_map (hd : d.Hyp) :
    d.U₁ = (d.P ⊓ centralizer (d.I₄ : Set G)).map (MulAut.conj d.s).toMonoidHom := by
  rw [hd.P_inf_centralizer_I₄, Data.s, ← d.pull_conj, map_conj_sSU_patSub_I₄]
  rfl

theorem Hyp.s_mem_centralizer_t (hd : d.Hyp) : d.s ∈ centralizer ({d.t} : Set G) :=
  hd.L_le_centralizer (d.η_mem _)

theorem Hyp.s_comm_t (hd : d.Hyp) : d.s * d.t = d.t * d.s :=
  (mem_centralizer_singleton_iff.1 hd.s_mem_centralizer_t)

theorem Hyp.map_conj_s_centralizer_t (hd : d.Hyp) :
    (centralizer ({d.t} : Set G)).map (MulAut.conj d.s).toMonoidHom =
      centralizer ({d.t} : Set G) := by
  ext x
  rw [mem_map_conj_s, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have hst := hd.s_comm_t
  constructor
  · intro e
    calc x * d.t = d.s * (d.s * x * d.s * d.t) * d.s := by
          rw [show d.s * (d.s * x * d.s * d.t) * d.s = (d.s * d.s) * x * (d.s * d.t * d.s) by
            group, hst, mul_assoc d.t, d.s_mul_s, one_mul, mul_one]
      _ = d.s * (d.t * (d.s * x * d.s)) * d.s := by rw [e]
      _ = d.t * x := by
          rw [show d.s * (d.t * (d.s * x * d.s)) * d.s = (d.s * d.t) * (d.s * x * d.s) * d.s by
            group, hst, show d.t * d.s * (d.s * x * d.s) * d.s = d.t * (d.s * d.s) * x *
              (d.s * d.s) by group, d.s_mul_s, mul_one, mul_one]
  · intro e
    calc d.s * x * d.s * d.t = d.s * x * (d.t * d.s) := by rw [mul_assoc, ← hst]
      _ = d.s * (x * d.t) * d.s := by group
      _ = d.s * (d.t * x) * d.s := by rw [e]
      _ = d.t * (d.s * x * d.s) := by rw [← mul_assoc, hst]; group

omit [Finite G] in
theorem V₁_le_centralizer_I₁ (d : Data G h) : d.V₁ ≤ centralizer (d.I₁ : Set G) := by
  intro x hx
  rw [V₁, mem_map_conj_s] at hx
  refine mem_centralizer_iff.2 fun i hi => ?_
  have hi4 : d.s * i * d.s ∈ d.I₄ := by
    rw [d.sec2_1_five.2.2.2.1]
    exact ⟨i, hi, by simp [MulAut.conj_apply, d.s_inv]⟩
  have e := mem_centralizer_iff.1 hx.2 _ hi4
  calc i * x = d.s * ((d.s * i * d.s) * (d.s * x * d.s)) * d.s := by
        rw [show d.s * ((d.s * i * d.s) * (d.s * x * d.s)) * d.s =
          (d.s * d.s) * i * (d.s * d.s) * x * (d.s * d.s) by group, d.s_mul_s]
        group
    _ = d.s * ((d.s * x * d.s) * (d.s * i * d.s)) * d.s := by rw [e]
    _ = x * i := by
        rw [show d.s * ((d.s * x * d.s) * (d.s * i * d.s)) * d.s =
          (d.s * d.s) * x * (d.s * d.s) * i * (d.s * d.s) by group, d.s_mul_s]
        group

theorem Hyp.isElementaryAbelian_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.IsElementaryAbelian 2 d.V₁ := by
  have : CFSG.IsElementaryAbelian 2 (d.F ⊓ centralizer (d.I₄ : Set G) : Subgroup G) :=
    isElementaryAbelian_of_le' (hd.isElementaryAbelian_F hGMS) inf_le_left
  exact CFSG.IsElementaryAbelian.map _

theorem Hyp.card_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card d.V₁ = (2 ^ f) ^ 4 := by
  rw [V₁, card_map_of_injective (MulAut.conj d.s).injective, hd.card_F_I₄ hGMS]

theorem Hyp.V₁_inf_centralizer_t (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V₁ ⊓ centralizer ({d.t} : Set G) = d.U₁ := by
  rw [V₁, ← hd.map_conj_s_centralizer_t, ← map_inf_eq _ _ (MulAut.conj d.s).toMonoidHom
      (MulAut.conj d.s).injective,
    hd.F_I₄_inf_centralizer_t hGMS, hd.U₁_eq_map]

theorem Hyp.U₁_le_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.U₁ ≤ d.V₁ := by
  rw [← hd.V₁_inf_centralizer_t hGMS]
  exact inf_le_left

theorem Hyp.V₁_inf_N₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V₁ ⊓ d.N₁ = d.U₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (hd.U₁_le_V₁ hGMS) d.U₁_le_N₁)
  rw [← hd.V₁_inf_centralizer_t hGMS]
  exact ⟨hx.1, hd.L_le_centralizer (d.pull_le_L _ hx.2)⟩

theorem Hyp.exists_mem_V₁_not_mem_U₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : ∃ w ∈ d.V₁, w ∉ d.U₁ := by
  by_contra hcon
  push Not at hcon
  have hle := Subgroup.card_le_of_le (show d.V₁ ≤ d.U₁ from hcon)
  rw [hd.card_V₁ hGMS, d.card_U₁] at hle
  have h4 := hd.four_le
  have : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem Hyp.t_mem_normalizer_V₁ (hd : d.Hyp) : d.t ∈ normalizer (d.V₁ : Set G) := by
  have ht : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  refine mem_normalizer_fintype fun x hx => ?_
  rw [ht]
  rw [SetLike.mem_coe, V₁, mem_map_conj_s] at hx ⊢
  have hst := hd.s_comm_t
  have e : d.s * (d.t * x * d.t) * d.s = d.t * (d.s * x * d.s) * d.t := by
    calc d.s * (d.t * x * d.t) * d.s = (d.s * d.t) * x * (d.t * d.s) := by group
      _ = (d.t * d.s) * x * (d.s * d.t) := by rw [hst]
      _ = d.t * (d.s * x * d.s) * d.t := by group
  rw [e]
  have hF := (mem_normalizer_iff.1 hd.t_mem_normalizer_F (d.s * x * d.s)).1 hx.1
  rw [ht] at hF
  refine Subgroup.mem_inf.2 ⟨hF, mem_centralizer_iff.2 fun i hi => ?_⟩
  have hit : i * d.t = d.t * i := hd.comm_t (d.pull_le_L _ hi)
  have e2 := mem_centralizer_iff.1 hx.2 i hi
  set y := d.s * x * d.s
  calc i * (d.t * y * d.t) = d.t * (i * y) * d.t := by
        rw [show i * (d.t * y * d.t) = (i * d.t) * y * d.t by group, hit]; group
    _ = d.t * (y * i) * d.t := by rw [e2]
    _ = d.t * y * d.t * i := by
        rw [show d.t * (y * i) * d.t = d.t * y * (i * d.t) by group, hit]; group

theorem Hyp.cr_V₁_mem (hd : d.Hyp) {x : G} (hx : x ∈ d.V₁) : x⁻¹ * d.t * x * d.t ∈ d.U₁ := by
  rw [V₁, mem_map_conj_s] at hx
  have hc := hd.cr_F_I₄_mem hx
  have e := d.cr_conj (c := d.s) (x := d.s * x * d.s) hd.s_mem_centralizer_t
  rw [d.s_inv, d.s_conj_s_conj] at e
  rw [hd.U₁_eq_map, mem_map_conj_s, e, d.s_conj_s_conj]
  exact hc

omit [Finite G] in
theorem s_conj_mul (d : Data G h) (a b : G) :
    d.s * (a * b) * d.s = (d.s * a * d.s) * (d.s * b * d.s) := by
  calc d.s * (a * b) * d.s = d.s * a * (d.s * d.s) * b * d.s := by rw [d.s_mul_s, mul_one]; group
    _ = _ := by group

theorem Hyp.cr_V₁_mul (hd : d.Hyp) {x y : G} (hx : x ∈ d.V₁) (hy : y ∈ d.V₁) :
    (x * y)⁻¹ * d.t * (x * y) * d.t = (x⁻¹ * d.t * x * d.t) * (y⁻¹ * d.t * y * d.t) := by
  rw [V₁, mem_map_conj_s] at hx hy
  have hs := hd.s_mem_centralizer_t
  have key : ∀ z : G, z⁻¹ * d.t * z * d.t =
      d.s * ((d.s * z * d.s)⁻¹ * d.t * (d.s * z * d.s) * d.t) * d.s := fun z => by
    have e := d.cr_conj (c := d.s) (x := d.s * z * d.s) hs
    rw [d.s_inv, d.s_conj_s_conj] at e
    exact e
  rw [key (x * y), key x, key y, d.s_conj_mul x y, hd.cr_F_mul hx.1 hy.1, d.s_conj_mul]

theorem Hyp.cr_eq_one_iff' (hd : d.Hyp) {x : G} :
    x⁻¹ * d.t * x * d.t = 1 ↔ x ∈ centralizer ({d.t} : Set G) := by
  have ht : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro e
    have e' : x⁻¹ * d.t * x = d.t :=
      (eq_inv_of_mul_eq_one_left e).trans ht
    calc x * d.t = x * (x⁻¹ * d.t * x) := by rw [e']
      _ = d.t * x := by group
  · intro e
    rw [mul_assoc x⁻¹, ← e]
    simp [hd.t_mul_t]

theorem Hyp.closure_commutator_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    closure {x : G | ∃ v ∈ d.V₁, x = v⁻¹ * (d.t⁻¹ * v * d.t)} = d.U₁ := by
  have ht : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t
  refine le_antisymm ((closure_le _).2 fun x ⟨v, hv, hx⟩ => ?_) fun u hu => ?_
  · rw [hx, ht, show v⁻¹ * (d.t * v * d.t) = v⁻¹ * d.t * v * d.t by group]
    exact hd.cr_V₁_mem hv
  · rw [hd.U₁_eq_map, mem_map_conj_s] at hu
    obtain ⟨c, hc, hca⟩ := hd.exists_F_I₄_cr_eq hGMS hu
    refine subset_closure ⟨d.s * c * d.s, ?_, ?_⟩
    · rw [V₁, mem_map_conj_s, d.s_conj_s_conj]
      exact hc
    · have e := d.cr_conj (c := d.s) (x := c) hd.s_mem_centralizer_t
      rw [d.s_inv] at e
      rw [ht, show (d.s * c * d.s)⁻¹ * (d.t * (d.s * c * d.s) * d.t) =
        (d.s * c * d.s)⁻¹ * d.t * (d.s * c * d.s) * d.t by group, e, hca, d.s_conj_s_conj]

theorem Hyp.D₁_le_normalizer_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.D₁ ≤ normalizer (d.V₁ : Set G) := by
  intro x hxD
  have hxI : d.s * x * d.s ∈ d.I := by
    rw [← d.sec2_1_five.2.1]
    exact ⟨x, d.D₁_le_I hxD, by simp [MulAut.conj_apply, d.s_inv]⟩
  refine mem_normalizer_fintype fun v hv => ?_
  rw [SetLike.mem_coe, V₁, mem_map_conj_s] at hv ⊢
  have e : d.s * (x * v * x⁻¹) * d.s =
      (d.s * x * d.s) * (d.s * v * d.s) * (d.s * x * d.s)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, d.s_inv]
    calc d.s * (x * v * x⁻¹) * d.s = d.s * x * (d.s * d.s) * v * (d.s * d.s) * x⁻¹ * d.s := by
          rw [d.s_mul_s]; group
      _ = _ := by group
  rw [e]
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hd.I_le_normalizer_F hGMS hxI) _).1 hv.1,
    mem_centralizer_iff.2 fun i hi => ?_⟩
  have hi' : i ∈ d.I := d.I₄_le_I hi
  set z := d.s * x * d.s with hz
  set w := d.s * v * d.s with hw
  have e1 : i * w = w * i := mem_centralizer_iff.1 hv.2 i hi
  have e2 : i * z = z * i := d.I_comm hi' hxI
  have e3 : i * z⁻¹ = z⁻¹ * i := d.I_comm hi' (inv_mem hxI)
  calc i * (z * w * z⁻¹) = z * (i * w) * z⁻¹ := by
        rw [show i * (z * w * z⁻¹) = (i * z) * w * z⁻¹ by group, e2]; group
    _ = z * (w * i) * z⁻¹ := by rw [e1]
    _ = z * w * z⁻¹ * i := by
        rw [show z * (w * i) * z⁻¹ = z * w * (i * z⁻¹) by group, e3]; group

theorem Hyp.D₁_regular_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∀ v ∈ d.V₁, v ∉ d.U₁ → ∀ w ∈ d.V₁, w ∉ d.U₁ →
      ∃! x : d.D₁, ((x : G) * v * (x : G)⁻¹)⁻¹ * w ∈ d.U₁ := by
  intro v hv hvU w hw hwU
  have hcrU : ∀ {z : G}, z ∈ d.V₁ → (z ∈ d.U₁ ↔ z⁻¹ * d.t * z * d.t = 1) := fun {z} hz => by
    rw [hd.cr_eq_one_iff', ← hd.V₁_inf_centralizer_t hGMS]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨hz, h1⟩⟩
  have hv1 : v⁻¹ * d.t * v * d.t ≠ 1 := fun e => hvU ((hcrU hv).2 e)
  have hw1 : w⁻¹ * d.t * w * d.t ≠ 1 := fun e => hwU ((hcrU hw).2 e)
  have hcrinv : ∀ {z : G}, z ∈ d.V₁ →
      z⁻¹⁻¹ * d.t * z⁻¹ * d.t = (z⁻¹ * d.t * z * d.t)⁻¹ := fun {z} hz => by
    have e := hd.cr_V₁_mul (inv_mem hz) hz
    rw [inv_mul_cancel, show (1 : G)⁻¹ * d.t * 1 * d.t = 1 by simp [hd.t_mul_t]] at e
    exact (eq_inv_of_mul_eq_one_left e.symm)
  have key : ∀ x : d.D₁, ((x : G) * v * (x : G)⁻¹)⁻¹ * w ∈ d.U₁ ↔
      (x : G) * (v⁻¹ * d.t * v * d.t) * (x : G)⁻¹ = w⁻¹ * d.t * w * d.t := by
    intro x
    have hxv : (x : G) * v * (x : G)⁻¹ ∈ d.V₁ :=
      (mem_normalizer_iff.1 (hd.D₁_le_normalizer_V₁ hGMS x.2) v).1 hv
    rw [hcrU (mul_mem (inv_mem hxv) hw), hd.cr_V₁_mul (inv_mem hxv) hw, hcrinv hxv,
      d.cr_conj (hd.D₁_le_centralizer_t x.2), inv_mul_eq_one]
  obtain ⟨x, hx, huniq⟩ := d.D₁_regular_U₁ _ (hd.cr_V₁_mem hv) hv1 _ (hd.cr_V₁_mem hw) hw1
  exact ⟨x, (key x).2 hx, fun y hy => huniq y ((key y).1 hy)⟩

theorem Hyp.exists_not_commute_of_isSylowOf (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {S : Subgroup G} (hS2 : IsSylowOf 2 S (centralizer (d.I₁ : Set G))) :
    ∃ x ∈ S, x * d.t ≠ d.t * x := by
  have := h.charP
  by_contra hcon
  push Not at hcon
  have hV2 : IsPGroup 2 d.V₁ := @CFSG.IsElementaryAbelian.isPGroup 2 d.V₁ _
    (hd.isElementaryAbelian_V₁ hGMS)
  have hB2 : IsPGroup 2 (d.V₁ ⊔ zpowers d.t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hV2 hd.isPGroup_zpowers_t (zpowers_le.2 hd.t_mem_normalizer_V₁)
  have hBH : d.V₁ ⊔ zpowers d.t ≤ centralizer (d.I₁ : Set G) :=
    sup_le d.V₁_le_centralizer_I₁ (zpowers_le.2 hd.t_mem_centralizer_I₁)
  obtain ⟨c, hcH, hle⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
      hS2 hB2 hBH
  have hconjS : ∀ x ∈ d.V₁ ⊔ zpowers d.t, c⁻¹ * x * c ∈ S := fun x hx =>
    hle (CFSG.ComponentClassification.AschbacherTheorem3.conj_mem_rightConjugate hx c)
  set t' := c * d.t * c⁻¹ with ht'def
  have hV' : ∀ w ∈ d.V₁, w * t' = t' * w := by
    intro w hw
    have h2 := hcon _ (hconjS w (mem_sup_left hw))
    calc w * t' = c * ((c⁻¹ * w * c) * d.t) * c⁻¹ := by rw [ht'def]; group
      _ = c * (d.t * (c⁻¹ * w * c)) * c⁻¹ := by rw [h2]
      _ = t' * w := by rw [ht'def]; group
  have ht' : t' * d.t = d.t * t' := by
    have h2 := hcon _ (hconjS d.t (mem_sup_right (mem_zpowers d.t)))
    calc t' * d.t = c * (d.t * (c⁻¹ * d.t * c)) * c⁻¹ := by rw [ht'def]; group
      _ = c * ((c⁻¹ * d.t * c) * d.t) * c⁻¹ := by rw [h2]
      _ = d.t * t' := by rw [ht'def]; group
  have ht'H : t' ∈ centralizer (d.I₁ : Set G) :=
    mul_mem (mul_mem hcH hd.t_mem_centralizer_I₁) (inv_mem hcH)
  have ht'C : t' ∈ centralizer ({d.t} : Set G) := mem_centralizer_singleton_iff.2 ht'
  have ht'L := hd.centralizer_le_normalizer ht'C
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨t', ht'L⟩)
  have hI := d.act_I₁_of_mem_centralizer ht'L hy ht'H
  have hU : ∀ u ∈ patSub h sI₁ isPattern_sI₁, actΓ h y u = u := fun u hu =>
    d.act_eq_of_η_eq_of_sq (mul_self_of_mem_patSub_I₁ hu) (by
      rw [← d.conj_η_eq ht'L hy, ← hV' _ (hd.U₁_le_V₁ hGMS ⟨u, hu, rfl⟩), mul_inv_cancel_right])
  have ht'2 : t' * t' = 1 := by
    rw [ht'def, show c * d.t * c⁻¹ * (c * d.t * c⁻¹) = c * (d.t * d.t) * c⁻¹ by group,
      hd.t_mul_t, mul_one, mul_inv_cancel]
  have hy2 : Phi h y ^ 2 = 1 := by
    have e : (⟨t', ht'L⟩ : normalizer (d.L : Set G)) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, sq, ht'2]; rfl)
    rw [hy, ← map_pow, e, map_one]
  obtain ⟨u₀, hu₀, hyu⟩ := exists_eq_innM_of_centralizes hd.two_le hI hU hy2
  have hlL : d.η u₀ ∈ d.L := d.η_mem u₀
  have hlU : d.η u₀ ∈ d.U₁ := ⟨u₀, hu₀, rfl⟩
  have hzC : (d.η u₀)⁻¹ * t' ∈ centralizer (d.L : Set G) := by
    have hm : (d.η u₀)⁻¹ * t' ∈ normalizer (d.L : Set G) :=
      mul_mem (inv_mem (le_normalizer hlL)) ht'L
    refine (d.act_eq_one_iff ⟨(d.η u₀)⁻¹ * t', hm⟩).1 ?_
    have e0 : (⟨(d.η u₀)⁻¹ * t', hm⟩ : normalizer (d.L : Set G)) =
        (⟨d.η u₀, le_normalizer (d.η_mem u₀)⟩ : normalizer (d.L : Set G))⁻¹ * ⟨t', ht'L⟩ := rfl
    rw [e0, map_mul, map_inv, ← hy, hyu, d.act_η, inv_mul_cancel]
  have hzt : (d.η u₀)⁻¹ * t' ∈ zpowers d.t := by
    rw [← hd.sec3_1'.1]
    exact Subgroup.mem_inf.2 ⟨hzC, mul_mem (inv_mem (hd.L_le_centralizer hlL)) ht'C⟩
  set l := d.η u₀ with hldef
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hzt
  rcases hd.zpow_t_eq j with e | e
  ·
    apply hd.sec3_1'.2.2.2.2.2 c⁻¹
    have : t' = l := by
      have := hj.symm
      rw [e] at this
      exact (inv_mul_eq_one.1 this).symm
    rw [inv_inv, ← ht'def, this]
    exact hlL
  ·
    have ht'l : t' = l * d.t := by
      have := hj.symm
      rw [e] at this
      rw [← this, mul_inv_cancel_left]
    obtain ⟨w, hw, hwU⟩ := hd.exists_mem_V₁_not_mem_U₁ hGMS
    apply hwU
    rw [← hd.V₁_inf_centralizer_t hGMS]
    refine Subgroup.mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hV' w hw
    rw [ht'l] at h1
    have hVc : ∀ a ∈ d.V₁, ∀ b ∈ d.V₁, a * b = b * a := fun a ha b hb =>
      Prelim.mul_comm_of_mem (hd.isElementaryAbelian_V₁ hGMS) ha hb
    have h2 := hVc l (hd.U₁_le_V₁ hGMS hlU) w hw
    calc w * d.t = l⁻¹ * (w * (l * d.t)) := by
          rw [← mul_assoc w l, ← h2]; group
      _ = l⁻¹ * (l * d.t * w) := by rw [h1]
      _ = d.t * w := by group

end Data

end CFSG.LocalAnalysis.EvenBN.U5
