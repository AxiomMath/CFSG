module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBModel
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem IsNaturalSection.eq_one {X A B : Subgroup G} {k : Type*} [Field k]
    (hN : IsNaturalSection X A B k) {x : G} (hx : x ∈ X)
    (htriv : ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ B) : x = 1 := by
  obtain ⟨φ, θ, hθA, hadd, hinj, -, hequiv⟩ := hN
  set M : Matrix (Fin 2) (Fin 2) k := (φ ⟨x, hx⟩ : Matrix (Fin 2) (Fin 2) k) with hM
  have key : ∀ v, M.mulVec v = v := by
    intro v
    have h1 := hequiv ⟨x, hx⟩ v
    have h2 := htriv (θ v) (hθA v)
    have h3 : (θ (M.mulVec v))⁻¹ * θ v ∈ B := by
      have := mul_mem h1 (inv_mem h2)
      have e : (θ (M.mulVec v))⁻¹ * (x * θ v * x⁻¹) * ((θ v)⁻¹ * (x * θ v * x⁻¹))⁻¹ =
          (θ (M.mulVec v))⁻¹ * θ v := by group
      rwa [e] at this
    have h4 := hadd (M.mulVec v) (v - M.mulVec v)
    rw [add_sub_cancel] at h4
    have h5 : θ (v - M.mulVec v) ∈ B := by
      have := inv_mem (mul_mem h4 (inv_mem h3))
      have e : ((θ (M.mulVec v) * θ (v - M.mulVec v))⁻¹ * θ v *
          ((θ (M.mulVec v))⁻¹ * θ v)⁻¹)⁻¹ = θ (v - M.mulVec v) := by group
      rwa [e] at this
    exact (sub_eq_zero.1 (hinj _ h5)).symm
  have hφ : φ ⟨x, hx⟩ = 1 := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    rw [Matrix.SpecialLinearGroup.coe_one]
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have := φ.injective (hφ.trans (map_one φ).symm)
  exact congrArg Subtype.val this

variable [Finite G]

theorem exists_isSylowOf_ne {k : Type*} [Field k] [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m)
    (hm : 1 ≤ m) {X : Subgroup G} (φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) k)
    (P : Subgroup G) : ∃ P' : Subgroup G, IsSylowOf 2 P' X ∧ P ≠ P' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := Prelim.ofSL φ (Timmesfeld.upperUnipotent k) with hR
  have hRs : IsSylowOf 2 R X := Prelim.isSylowOf_ofSL_upperUnipotent hk hm φ
  by_cases hPR : P = R
  swap
  · exact ⟨R, hRs, hPR⟩
  let g : Matrix.SpecialLinearGroup (Fin 2) k := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  set y : X := φ.symm g with hy
  refine ⟨R.map (MulAut.conj (y : G)).toMonoidHom, Prelim.isSylowOf_map_conj hRs y.2, ?_⟩
  intro heq
  have h10 : (g : Matrix (Fin 2) (Fin 2) k) 1 0 ≠ 0 := by simp [g]
  have hsup := EvenLinearTwoModule.upperUnipotent_sup_map_conj_eq_top h10
  have hRy : R.map (MulAut.conj (y : G)).toMonoidHom = Prelim.ofSL φ
      ((Timmesfeld.upperUnipotent k).map (MulAut.conj (φ y)).toMonoidHom) :=
    (Prelim.ofSL_map_conj φ _ y).symm
  have hφy : φ y = g := by simp [hy]
  rw [hφy] at hRy
  have hX : R ⊔ R.map (MulAut.conj (y : G)).toMonoidHom = X := by
    rw [hRy, hR, ← Prelim.ofSL_sup, hsup, Prelim.ofSL_top]
  rw [← heq, hPR, sup_idem] at hX
  have hcR := Prelim.card_of_isSylowOf hk hm φ hRs
  have hcX : Nat.card X = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr φ.toEquiv, SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk]
  rw [← hX, hcR] at hcX
  have ha : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h4 : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
  have h3 : 3 ≤ (2 ^ m) ^ 2 - 1 := by omega
  have := Nat.mul_le_mul_left (2 ^ m) h3
  omega

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

section Defs

variable (c : d.CaseBData)

@[expose] def Kt : Subgroup G := c.Kc.map (MulAut.conj d.t).toMonoidHom

@[expose] def F₁ : Subgroup G := d.F ⊓ centralizer (c.X : Set G)

@[expose] def F₂ : Subgroup G := d.F ⊓ centralizer (c.Y : Set G)

end Defs

variable {c : d.CaseBData} (hB : d.CaseBHyp)
include hB

theorem X_le_L₁ : c.X ≤ d.L₁ := c.X_le_M₁.trans hB.M₁_le_L₁

theorem Y_le_L₁ : c.Y ≤ d.L₁ := c.Y_le_M₁.trans hB.M₁_le_L₁

theorem X_le_Kc : c.X ≤ c.Kc := le_normalClosureIn (c.X_le_L₁ hB)

omit [Finite G] hB in
theorem Kc_le_L₁ : c.Kc ≤ d.L₁ := normalClosureIn_le_self _ _

omit hB in
theorem L₁_le_normalizer_Kc : d.L₁ ≤ normalizer (c.Kc : Set G) :=
  le_normalizer_normalClosureIn _ _

theorem commutator_Kc : ⁅c.Kc, c.Kc⁆ = c.Kc :=
  commutator_normalClosureIn (c.X_le_L₁ hB) (c.commutator_X hB.hyp)

theorem map_conj_t_L₁ : d.L₁.map (MulAut.conj d.t).toMonoidHom = d.L₁ :=
  map_conj_eq_of_mem_normalizer hB.hyp.t_mem_normalizer_L₁

theorem Kt_le_L₁ : c.Kt ≤ d.L₁ := by
  rw [← map_conj_t_L₁ hB]
  exact map_mono c.Kc_le_L₁

theorem L₁_le_normalizer_Kt : d.L₁ ≤ normalizer (c.Kt : Set G) := by
  intro g hg
  have hg' : d.t⁻¹ * g * d.t ∈ d.L₁ := by
    have := (mem_normalizer_iff.1 (inv_mem hB.hyp.t_mem_normalizer_L₁) g).1 hg
    rwa [inv_inv] at this
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(d.t⁻¹ * g * d.t) * y * (d.t⁻¹ * g * d.t)⁻¹,
    (mem_normalizer_iff.1 (c.L₁_le_normalizer_Kc hg') y).1 hy, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem commutator_Kt : ⁅c.Kt, c.Kt⁆ = c.Kt := by
  rw [Kt, ← map_commutator, c.commutator_Kc hB]

theorem X_le_normalizer_D : c.X ≤ normalizer (d.D : Set G) :=
  (c.X_le_L₁ hB).trans hB.hyp.L₁_le_normalizer_D

theorem L₁_le_normalizer_D_sup_X : d.L₁ ≤ normalizer ((d.D ⊔ c.X : Subgroup G) : Set G) := by
  rw [hB.L₁_eq]
  refine sup_le (fun x hx => le_normalizer (mem_sup_left hx)) fun m hm => ?_
  exact Common.mem_normalizer_sup (hB.hyp.L₁_le_normalizer_D (hB.M₁_le_L₁ hm))
    (c.M₁_le_normalizer_X hm)

theorem Kc_le_D_sup_X : c.Kc ≤ d.D ⊔ c.X :=
  normalClosureIn_le le_sup_right (c.L₁_le_normalizer_D_sup_X hB)

theorem Uc_eq : d.Uc c.S c.X = d.D ⊔ (c.X ⊓ c.S) := by
  have e : d.D ⊔ d.Kc c.X = d.D ⊔ c.X :=
    le_antisymm (sup_le le_sup_left (c.Kc_le_D_sup_X hB)) (sup_le_sup_left (c.X_le_Kc hB) _)
  rw [Uc, e, inf_comm]
  exact sup_inf_eq_of_le (c.D_le_S hB) (c.X_le_normalizer_D hB)

theorem commutatorElement_mem_F {a b : G} (ha : a ∈ d.D) (hb : b ∈ d.D) :
    a * b * a⁻¹ * b⁻¹ ∈ d.F := by
  have h1 := hB.mul_self_mem_F _ (mul_mem ha hb)
  have h2 := hB.mul_self_mem_F _ ha
  have h3 := hB.mul_self_mem_F _ hb
  have hcomm : Commute b (a * a)⁻¹ :=
    (Commute.inv_right (mem_centralizer_iff.1 (hB.D_le_centralizer_F hb) _ h2).symm)
  have e : a * b * a⁻¹ * b⁻¹ = (a * b) * (a * b) * ((a * a)⁻¹ * (b * b)⁻¹) := by
    calc a * b * a⁻¹ * b⁻¹ = a * b * a * ((a * a)⁻¹ * b) * (b * b)⁻¹ := by group
      _ = a * b * a * (b * (a * a)⁻¹) * (b * b)⁻¹ := by rw [hcomm.eq]
      _ = (a * b) * (a * b) * ((a * a)⁻¹ * (b * b)⁻¹) := by group
  rw [e]
  exact mul_mem h1 (mul_mem (inv_mem h2) (inv_mem h3))

theorem eq_one_of_mem_X {x : G} (hx : x ∈ c.X)
    (htriv : ∀ a ∈ d.D, a⁻¹ * (x * a * x⁻¹) ∈ d.F) : x = 1 := by
  obtain ⟨-, -, hN⟩ := hB.sec3_12 c.k inferInstance inferInstance c.card_k c.ψ
  exact hN.eq_one (Subgroup.mem_inf.2 ⟨c.X_le_M₁ hx, c.X_le_Kc hB hx⟩)
    fun a ha => htriv a (Subgroup.mem_inf.1 ha).2

theorem centerIn_Uc :
    CFSG.centerIn (d.Uc c.S c.X) = d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) := by
  rw [c.Uc_eq hB]
  apply le_antisymm
  · rintro z ⟨hzU, hzc⟩
    obtain ⟨e, he, x, hx, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (inf_le_left.trans (c.X_le_normalizer_D hB)) hzU
    have hcD : ∀ a ∈ d.D, a * (e * x) = (e * x) * a := fun a ha =>
      mem_centralizer_iff.1 hzc a (mem_sup_left ha)
    have hx1 : x = 1 := by
      refine c.eq_one_of_mem_X hB (Subgroup.mem_inf.1 hx).1 fun a ha => ?_
      have e1 : x * a * x⁻¹ = e⁻¹ * a * e := by
        calc x * a * x⁻¹ = e⁻¹ * ((e * x) * a) * (e * x)⁻¹ * e := by group
          _ = e⁻¹ * (a * (e * x)) * (e * x)⁻¹ * e := by rw [← hcD a ha]
          _ = e⁻¹ * a * e := by group
      rw [e1]
      have := commutatorElement_mem_F hB (inv_mem ha) (inv_mem he)
      rw [inv_inv, inv_inv] at this
      simpa only [mul_assoc] using this
    subst hx1
    simp only [mul_one] at hcD hzc ⊢
    refine Subgroup.mem_inf.2 ⟨?_, mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_iff.1 hzc y (mem_sup_right hy)⟩
    rw [← hB.centerIn_D]
    exact ⟨he, mem_centralizer_iff.2 fun a ha => by simpa using hcD a ha⟩
  · rintro z ⟨hzF, hzc⟩
    refine ⟨mem_sup_left (hB.F_le_D hzF), mem_centralizer_iff.2 fun y hy => ?_⟩
    have hle : d.D ⊔ (c.X ⊓ c.S) ≤ centralizer ({z} : Set G) := sup_le
      (fun a ha => mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (hB.D_le_centralizer_F ha) z hzF).symm)
      (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzc a ha))
    exact mem_centralizer_singleton_iff.1 (hle hy)

theorem lt_card_centerIn_Uc : (2 ^ f) ^ 4 < Nat.card (CFSG.centerIn (d.Uc c.S c.X)) := by
  by_contra hle
  push Not at hle
  exact hB.caseB (hB.sec3_13_one c.S c.S_syl c.P_le_S c.k inferInstance inferInstance c.card_k
    c.ψ hle).1

theorem isSylowOf_X_inf_S : IsSylowOf 2 (c.X ⊓ c.S) c.X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (c.isSylowOf_S_M₁ hB).inf_of_le_normalizer c.X_le_M₁ c.M₁_le_normalizer_X
  rwa [inf_assoc, inf_eq_right.2 c.X_le_M₁, inf_comm] at h1

theorem isSylowOf_Y_inf_S : IsSylowOf 2 (c.Y ⊓ c.S) c.Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (c.isSylowOf_S_M₁ hB).inf_of_le_normalizer c.Y_le_M₁ c.M₁_le_normalizer_Y
  rwa [inf_assoc, inf_eq_right.2 c.Y_le_M₁, inf_comm] at h1

theorem map_conj_t_X_inf_S :
    (c.X ⊓ c.S).map (MulAut.conj d.t).toMonoidHom = c.Y ⊓ c.S := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective, c.map_conj_t_X hB.hyp,
    map_conj_eq_of_mem_normalizer (c.t_mem_normalizer_S hB)]

theorem lt_card_F_X :
    2 ^ (2 * (2 * f)) < Nat.card (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) :
      Subgroup G) := by
  rw [← c.centerIn_Uc hB, show 2 ^ (2 * (2 * f)) = (2 ^ f) ^ 4 by ring]
  exact c.lt_card_centerIn_Uc hB

theorem lt_card_F_Y :
    2 ^ (2 * (2 * f)) < Nat.card (d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G) :
      Subgroup G) := by
  rw [← c.map_conj_t_X_inf_S hB, Prelim.inf_centralizer_map_conj hB.hyp.t_mem_normalizer_F,
    Prelim.card_map_conj]
  exact c.lt_card_F_X hB

theorem F_inf_centralizer_X_inf_centralizer_Y :
    d.F ⊓ centralizer (c.X : Set G) ⊓ centralizer (c.Y : Set G) = ⊥ := by
  rw [eq_bot_iff, ← hB.hyp.F_inf_centralizer_N₁ hB.gms]
  rintro z ⟨⟨hzF, hzX⟩, hzY⟩
  refine Subgroup.mem_inf.2 ⟨hzF, ?_⟩
  have hz : z ∈ centralizer ((c.X ⊔ c.Y : Subgroup G) : Set G) := by
    rw [Prelim.centralizer_sup_eq]
    exact Subgroup.mem_inf.2 ⟨hzX, hzY⟩
  rw [c.X_sup_Y] at hz
  exact centralizer_le (SetLike.coe_subset_coe.2 d.N₁_le_M₁) hz

theorem F_eq : c.F₁ ⊔ c.F₂ = d.F ∧ c.F₁ ⊓ c.F₂ = ⊥ ∧
    Nat.card c.F₁ = 2 ^ (2 * (2 * f)) ∧ Nat.card c.F₂ = 2 ^ (2 * (2 * f)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := hB.hyp.two_le
  obtain ⟨P', hP', hPP⟩ := exists_isSylowOf_ne c.card_k_eq (by omega) c.φX (c.X ⊓ c.S)
  obtain ⟨Q', hQ', hQQ⟩ := exists_isSylowOf_ne c.card_k_eq (by omega) c.φY (c.Y ⊓ c.S)
  have hFcard : Nat.card d.F = 2 ^ (4 * (2 * f)) := by
    rw [hB.hyp.card_F hB.gms]
    ring
  obtain ⟨-, -, hsup, hinf, hc1, hc2⟩ := sl2_pair_module_large c.card_k_eq (by omega) (by omega)
    (hB.hyp.isElementaryAbelian_F hB.gms) hFcard c.φX c.φY
    ((c.X_le_L₁ hB).trans hB.L₁_le_normalizer_F) ((c.Y_le_L₁ hB).trans hB.L₁_le_normalizer_F)
    (fun x hx y hy => (mem_centralizer_iff.1 (c.X_le_centralizer_Y hx) y hy).symm)
    (c.F_inf_centralizer_X_inf_centralizer_Y hB) (c.isSylowOf_X_inf_S hB) hP' hPP
    (c.isSylowOf_Y_inf_S hB) hQ' hQQ (c.lt_card_F_X hB) (c.lt_card_F_Y hB)
  exact ⟨hsup, hinf, hc1, hc2⟩

theorem L₁_le_normalizer_F₁ : d.L₁ ≤ normalizer (c.F₁ : Set G) := by
  rw [hB.L₁_eq]
  refine sup_le (fun a ha => mem_normalizer_of_mem_centralizer'
    (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left) (hB.D_le_centralizer_F ha))) ?_
  intro m hm
  exact Common.mem_normalizer_inf (hB.L₁_le_normalizer_F (hB.M₁_le_L₁ hm))
    (normalizer_le_normalizer_centralizer _ (c.M₁_le_normalizer_X hm))

theorem L₁_le_normalizer_F₂ : d.L₁ ≤ normalizer (c.F₂ : Set G) := by
  rw [hB.L₁_eq]
  refine sup_le (fun a ha => mem_normalizer_of_mem_centralizer'
    (centralizer_le (SetLike.coe_subset_coe.2 inf_le_left) (hB.D_le_centralizer_F ha))) ?_
  intro m hm
  exact Common.mem_normalizer_inf (hB.L₁_le_normalizer_F (hB.M₁_le_L₁ hm))
    (normalizer_le_normalizer_centralizer _ (c.M₁_le_normalizer_Y hm))

theorem Kc_le_centralizer_F₁ : c.Kc ≤ centralizer (c.F₁ : Set G) :=
  normalClosureIn_le (fun x hx => mem_centralizer_iff.2 fun _ hz =>
      (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 x hx).symm)
    ((c.L₁_le_normalizer_F₁ hB).trans (normalizer_le_normalizer_centralizer _))

theorem F_inf_centralizer_Kc : d.F ⊓ centralizer (c.Kc : Set G) = c.F₁ := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 (c.X_le_Kc hB)))
  · exact le_inf inf_le_left fun z hz => mem_centralizer_iff.2 fun k hk =>
      (mem_centralizer_iff.1 (c.Kc_le_centralizer_F₁ hB hk) z hz).symm

theorem map_conj_t_F₁ : c.F₁.map (MulAut.conj d.t).toMonoidHom = c.F₂ := by
  rw [F₁, ← Prelim.inf_centralizer_map_conj hB.hyp.t_mem_normalizer_F, c.map_conj_t_X hB.hyp]
  rfl

theorem map_conj_t_F₂ : c.F₂.map (MulAut.conj d.t).toMonoidHom = c.F₁ := by
  rw [F₂, ← Prelim.inf_centralizer_map_conj hB.hyp.t_mem_normalizer_F, c.map_conj_t_Y hB.hyp]
  rfl

theorem F_inf_centralizer_Kt : d.F ⊓ centralizer (c.Kt : Set G) = c.F₂ := by
  rw [Kt, Prelim.inf_centralizer_map_conj hB.hyp.t_mem_normalizer_F, c.F_inf_centralizer_Kc hB,
    c.map_conj_t_F₁ hB]

theorem Kt_le_centralizer_F₂ : c.Kt ≤ centralizer (c.F₂ : Set G) := fun k hk =>
  mem_centralizer_iff.2 fun z hz => by
    rw [← c.F_inf_centralizer_Kt hB] at hz
    exact (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 k hk).symm

theorem F₂_le_Kc : c.F₂ ≤ c.Kc := by
  obtain ⟨-, hinf, -, hc2⟩ := c.F_eq hB
  have hf := hB.hyp.two_le
  have hXF₂ : c.X ≤ normalizer (c.F₂ : Set G) := (c.X_le_L₁ hB).trans (c.L₁_le_normalizer_F₂ hB)
  have hcen : c.F₂ ⊓ centralizer (c.X : Set G) = ⊥ := by
    rw [eq_bot_iff, ← c.F_inf_centralizer_X_inf_centralizer_Y hB]
    rintro z ⟨⟨hzF, hzY⟩, hzX⟩
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hzF, hzX⟩, hzY⟩
  have hF₂ := commutator_eq_of_card c.card_k_eq (by omega) (by omega) c.φX
    (hB.hyp.isPGroup_F.to_le inf_le_left) hXF₂ hcen hc2
  change d.F ⊓ centralizer (c.Y : Set G) ≤ c.Kc
  rw [← hF₂]
  refine commutator_le.2 fun a ha x hx => ?_
  have hxK := c.X_le_Kc hB hx
  have h1 : a * x * a⁻¹ ∈ c.Kc :=
    (mem_normalizer_iff.1 (c.L₁_le_normalizer_Kc (hB.F_le_L₁ (Subgroup.mem_inf.1 ha).1)) x).1
      hxK
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem hxK)

theorem F₁_le_Kt : c.F₁ ≤ c.Kt := by
  rw [← c.map_conj_t_F₂ hB]
  exact map_mono (c.F₂_le_Kc hB)

theorem commutatorElement_mem_F_of_mem {a b : G} (ha : a ∈ c.Kc) (hb : b ∈ c.Kt) :
    ⁅a, b⁆ ∈ d.F := by
  obtain ⟨-, hinf, -⟩ := hB.sec3_12 c.k inferInstance inferInstance c.card_k c.ψ
  rw [← hinf]
  refine Subgroup.mem_inf.2 ⟨mem_sup_right ?_, mem_sup_right ?_⟩
  · have : b * a⁻¹ * b⁻¹ ∈ c.Kc :=
      (mem_normalizer_iff.1 (c.L₁_le_normalizer_Kc (c.Kt_le_L₁ hB hb)) _).1 (inv_mem ha)
    rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact mul_mem ha this
  · have : a * b * a⁻¹ ∈ c.Kt :=
      (mem_normalizer_iff.1 (c.L₁_le_normalizer_Kt hB (c.Kc_le_L₁ ha)) b).1 hb
    rw [commutatorElement_def]
    exact mul_mem this (inv_mem hb)

theorem exists_mul_F {z : G} (hz : z ∈ d.F) : ∃ z₁ ∈ c.F₁, ∃ z₂ ∈ c.F₂, z = z₁ * z₂ := by
  obtain ⟨hsup, -⟩ := c.F_eq hB
  have hFc := hB.hyp.isElementaryAbelian_F hB.gms
  rw [← hsup] at hz
  exact exists_mul_of_mem_sup_of_commute (fun x hx y hy =>
    Prelim.mul_comm_of_mem hFc (Subgroup.mem_inf.1 hx).1 (Subgroup.mem_inf.1 hy).1) hz

theorem commute_of_mem_Kc_of_mem_Kt {a b : G} (ha : a ∈ c.Kc) (hb : b ∈ c.Kt) :
    a * b = b * a := by
  obtain ⟨-, hinf, -⟩ := c.F_eq hB
  have hFc := hB.hyp.isElementaryAbelian_F hB.gms
  have hFab : ∀ x ∈ d.F, ∀ y ∈ d.F, x * y = y * x := fun _ hx _ hy =>
    Prelim.mul_comm_of_mem hFc hx hy
  have h2 : ⁅a, b⁆ ∈ c.F₂ := by
    refine commutatorElement_mem_of_perfect (c.commutator_Kc hB) hFab
      (fun k hk z hz => (mem_normalizer_iff.1 (hB.L₁_le_normalizer_F (c.Kc_le_L₁ hk)) z).1 hz)
      (fun k hk z hz => ?_) (fun k hk => c.commutatorElement_mem_F_of_mem hB hk hb) a ha
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := c.exists_mul_F hB hz
    have e1 : k * z₁ * k⁻¹ = z₁ := by
      rw [← mem_centralizer_iff.1 (c.Kc_le_centralizer_F₁ hB hk) z₁ hz₁, mul_inv_cancel_right]
    have e2 : (z₁ * z₂)⁻¹ * (k * (z₁ * z₂) * k⁻¹) = z₂⁻¹ * (k * z₂ * k⁻¹) := by
      calc (z₁ * z₂)⁻¹ * (k * (z₁ * z₂) * k⁻¹) = z₂⁻¹ * z₁⁻¹ * (k * z₁ * k⁻¹) *
          (k * z₂ * k⁻¹) := by group
        _ = z₂⁻¹ * (k * z₂ * k⁻¹) := by rw [e1]; group
    rw [e2]
    exact mul_mem (inv_mem hz₂)
      ((mem_normalizer_iff.1 (c.L₁_le_normalizer_F₂ hB (c.Kc_le_L₁ hk)) z₂).1 hz₂)
  have h1 : ⁅b, a⁆ ∈ c.F₁ := by
    refine commutatorElement_mem_of_perfect (c.commutator_Kt hB) hFab
      (fun k hk z hz => (mem_normalizer_iff.1 (hB.L₁_le_normalizer_F (c.Kt_le_L₁ hB hk)) z).1 hz)
      (fun k hk z hz => ?_) (fun k hk => ?_) b hb
    · obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := c.exists_mul_F hB hz
      have e1 : k * z₂ * k⁻¹ = z₂ := by
        rw [← mem_centralizer_iff.1 (c.Kt_le_centralizer_F₂ hB hk) z₂ hz₂, mul_inv_cancel_right]
      have hcomm : z₁ * z₂ = z₂ * z₁ := Prelim.mul_comm_of_mem hFc (Subgroup.mem_inf.1 hz₁).1
        (Subgroup.mem_inf.1 hz₂).1
      have e2 : (z₁ * z₂)⁻¹ * (k * (z₁ * z₂) * k⁻¹) = z₁⁻¹ * (k * z₁ * k⁻¹) := by
        rw [hcomm]
        calc (z₂ * z₁)⁻¹ * (k * (z₂ * z₁) * k⁻¹) = z₁⁻¹ * z₂⁻¹ * (k * z₂ * k⁻¹) *
            (k * z₁ * k⁻¹) := by group
          _ = z₁⁻¹ * (k * z₁ * k⁻¹) := by rw [e1]; group
      rw [e2]
      exact mul_mem (inv_mem hz₁)
        ((mem_normalizer_iff.1 (c.L₁_le_normalizer_F₁ hB (c.Kt_le_L₁ hB hk)) z₁).1 hz₁)
    · rw [← commutatorElement_inv]
      exact inv_mem (c.commutatorElement_mem_F_of_mem hB ha hk)
  have h12 : ⁅a, b⁆ ∈ c.F₁ ⊓ c.F₂ := by
    refine Subgroup.mem_inf.2 ⟨?_, h2⟩
    rw [← commutatorElement_inv]
    exact inv_mem h1
  rw [hinf, mem_bot] at h12
  exact commutatorElement_eq_one_iff_mul_comm.1 h12

theorem Kt_le_centralizer_Kc : c.Kt ≤ centralizer (c.Kc : Set G) := fun _ hb =>
  mem_centralizer_iff.2 fun _ ha => c.commute_of_mem_Kc_of_mem_Kt hB ha hb

theorem Kc_inf_Kt : c.Kc ⊓ c.Kt = ⊥ := by
  obtain ⟨-, hinf12, -⟩ := c.F_eq hB
  obtain ⟨-, hinf, -⟩ := hB.sec3_12 c.k inferInstance inferInstance c.card_k c.ψ
  rw [eq_bot_iff]
  rintro z ⟨hzK, hzKt⟩
  have hzF : z ∈ d.F := by
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨mem_sup_right hzK, mem_sup_right hzKt⟩
  have hz₁ : z ∈ c.F₁ := by
    rw [← c.F_inf_centralizer_Kc hB]
    exact Subgroup.mem_inf.2 ⟨hzF, c.Kt_le_centralizer_Kc hB hzKt⟩
  have hz₂ : z ∈ c.F₂ := by
    rw [← c.F_inf_centralizer_Kt hB]
    refine Subgroup.mem_inf.2 ⟨hzF, mem_centralizer_iff.2 fun b hb => ?_⟩
    exact (c.commute_of_mem_Kc_of_mem_Kt hB hzK hb).symm
  have : z ∈ c.F₁ ⊓ c.F₂ := Subgroup.mem_inf.2 ⟨hz₁, hz₂⟩
  rwa [hinf12] at this

theorem Kc_sup_Kt : c.Kc ⊔ c.Kt = d.L₁ := by
  obtain ⟨hsup12, -⟩ := c.F_eq hB
  obtain ⟨hsup, -⟩ := hB.sec3_12 c.k inferInstance inferInstance c.card_k c.ψ
  refine le_antisymm (sup_le c.Kc_le_L₁ (c.Kt_le_L₁ hB)) ?_
  have hF : d.F ≤ c.Kc ⊔ c.Kt := by
    rw [← hsup12]
    exact sup_le ((c.F₁_le_Kt hB).trans le_sup_right) ((c.F₂_le_Kc hB).trans le_sup_left)
  rw [← hsup]
  exact sup_le (sup_le hF le_sup_left) (sup_le hF le_sup_right)

theorem F_inf_Kc : d.F ⊓ c.Kc = c.F₂ := by
  refine le_antisymm (fun z hz => ?_) (le_inf inf_le_left (c.F₂_le_Kc hB))
  rw [← c.F_inf_centralizer_Kt hB]
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).1, mem_centralizer_iff.2 fun b hb => ?_⟩
  exact (c.commute_of_mem_Kc_of_mem_Kt hB (Subgroup.mem_inf.1 hz).2 hb).symm

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
