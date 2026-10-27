module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofTenOrders
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups Pointwise

section Generic

theorem sec3103_card_mul_le_of_finite {G : Type} [Group G] [Finite G] {D A B : Subgroup G}
    (hA : A ≤ D) (hB : B ≤ D) :
    Nat.card A * Nat.card B ≤ Nat.card D * Nat.card (A ⊓ B : Subgroup G) := by
  have hD : 0 < Nat.card D := Nat.card_pos
  have h1 : B.relIndex A * Nat.card (B ⊓ A : Subgroup G) = Nat.card A :=
    Subgroup.relIndex_mul_card B A
  have h2 : B.relIndex D * Nat.card (B ⊓ D : Subgroup G) = Nat.card D :=
    Subgroup.relIndex_mul_card B D
  rw [inf_eq_left.mpr hB] at h2
  have h3 : B.relIndex D ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    omega
  have h4 : B.relIndex A ≤ B.relIndex D := Subgroup.relIndex_le_of_le_right hA h3
  rw [inf_comm B A] at h1
  calc Nat.card A * Nat.card B
      = (B.relIndex A * Nat.card (A ⊓ B : Subgroup G)) * Nat.card B := by rw [h1]
    _ ≤ (B.relIndex D * Nat.card (A ⊓ B : Subgroup G)) * Nat.card B :=
        Nat.mul_le_mul (Nat.mul_le_mul h4 le_rfl) le_rfl
    _ = Nat.card D * Nat.card (A ⊓ B : Subgroup G) := by rw [← h2]; ring

theorem sec3103_comm_mem_of_sq_mem {G : Type} [Group G] {D F : Subgroup G}
    (hFD : D ≤ normalizer (F : Set G)) (hsq : ∀ x ∈ D, x * x ∈ F) :
    ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ F := by
  intro x hx y hy
  have h1 : (x * y) * (x * y) ∈ F := hsq _ (mul_mem hx hy)
  have h2 : y⁻¹ * (x * x)⁻¹ * y ∈ F := by
    have := (mem_normalizer_iff.1 (inv_mem (hFD hy)) (x * x)⁻¹).1 (inv_mem (hsq x hx))
    simpa using this
  have h3 : (y * y)⁻¹ ∈ F := inv_mem (hsq y hy)
  have e : x * y * x⁻¹ * y⁻¹ = ((x * y) * (x * y)) * (y⁻¹ * (x * x)⁻¹ * y) * (y * y)⁻¹ := by
    group
  rw [e]
  exact mul_mem (mul_mem h1 h2) h3

theorem sec3103_swap {G : Type} [Group G] {S F : Subgroup G} (hSF : S ≤ normalizer (F : Set G))
    {x u : G} (hx : x ∈ S) (hu : u ∈ S) (h : u⁻¹ * (x * u * x⁻¹) ∈ F) :
    x⁻¹ * (u * x * u⁻¹) ∈ F := by
  have h1 := (mem_normalizer_iff.1 (hSF (mul_mem (inv_mem hx) hu)) _).1 (inv_mem h)
  have e : x⁻¹ * (u * x * u⁻¹) =
      (x⁻¹ * u) * (u⁻¹ * (x * u * x⁻¹))⁻¹ * (x⁻¹ * u)⁻¹ := by group
  rw [e]
  exact h1

theorem sec3103_conj_mem_centralizerSection {G : Type} [Group G] {D F : Subgroup G} {c g : G}
    (hcD : c ∈ normalizer (D : Set G)) (hcF : c ∈ normalizer (F : Set G))
    (hg : g ∈ centralizerSection D F) : c * g * c⁻¹ ∈ centralizerSection D F := by
  obtain ⟨hgD, hgF, hg⟩ := hg
  refine ⟨mul_mem (mul_mem hcD hgD) (inv_mem hcD), mul_mem (mul_mem hcF hgF) (inv_mem hcF),
    fun y hy => ?_⟩
  have hy' : c⁻¹ * y * c ∈ D := by
    have := (mem_normalizer_iff.1 (inv_mem hcD) y).1 hy
    simpa using this
  have h1 := (mem_normalizer_iff.1 hcF _).1 (hg _ hy')
  have e : y⁻¹ * (c * g * c⁻¹ * y * (c * g * c⁻¹)⁻¹) =
      c * ((c⁻¹ * y * c)⁻¹ * (g * (c⁻¹ * y * c) * g⁻¹)) * c⁻¹ := by group
  rw [e]
  exact h1

theorem sec3103_comm_iff {G : Type} [Group G] {F : Subgroup G} {g h : G}
    (hg : g ∈ normalizer (F : Set G)) (hh : h ∈ normalizer (F : Set G)) :
    g * h * g⁻¹ * h⁻¹ ∈ F ↔
      proj F ⟨g, hg⟩ * proj F ⟨h, hh⟩ = proj F ⟨h, hh⟩ * proj F ⟨g, hg⟩ := by
  have hm : g * h * g⁻¹ * h⁻¹ ∈ normalizer (F : Set G) :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have e : (⟨g * h * g⁻¹ * h⁻¹, hm⟩ : normalizer (F : Set G)) =
      ⟨g, hg⟩ * ⟨h, hh⟩ * ⟨g, hg⟩⁻¹ * ⟨h, hh⟩⁻¹ := rfl
  have key : proj F ⟨g * h * g⁻¹ * h⁻¹, hm⟩ = 1 ↔ g * h * g⁻¹ * h⁻¹ ∈ F :=
    proj_eq_one_iff
  simp only [e, map_mul, map_inv] at key
  refine Iff.trans key.symm ?_
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem sec3103_conj_iff {G : Type} [Group G] {F : Subgroup G} {g h : G}
    (hg : g ∈ normalizer (F : Set G)) (hh : h ∈ normalizer (F : Set G)) :
    g⁻¹ * (h * g * h⁻¹) ∈ F ↔
      proj F ⟨h, hh⟩ * proj F ⟨g, hg⟩ = proj F ⟨g, hg⟩ * proj F ⟨h, hh⟩ := by
  have hm : g⁻¹ * (h * g * h⁻¹) ∈ normalizer (F : Set G) :=
    mul_mem (inv_mem hg) (mul_mem (mul_mem hh hg) (inv_mem hh))
  have e : (⟨g⁻¹ * (h * g * h⁻¹), hm⟩ : normalizer (F : Set G)) =
      ⟨g, hg⟩⁻¹ * (⟨h, hh⟩ * ⟨g, hg⟩ * ⟨h, hh⟩⁻¹) := rfl
  have key : proj F ⟨g⁻¹ * (h * g * h⁻¹), hm⟩ = 1 ↔ g⁻¹ * (h * g * h⁻¹) ∈ F :=
    proj_eq_one_iff
  simp only [e, map_mul, map_inv] at key
  refine Iff.trans key.symm ?_
  rw [inv_mul_eq_one, eq_mul_inv_iff_mul_eq]
  exact eq_comm

theorem sec3103_exists_of_mem_bar {G : Type} [Group G] {F X : Subgroup G} {u : Bar F}
    (hu : u ∈ bar F X) : ∃ a : normalizer (F : Set G), (a : G) ∈ X ∧ proj F a = u := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
  exact ⟨a, Subgroup.mem_subgroupOf.1 ha, rfl⟩

theorem sec3103_section_centralizer_le_center {G : Type} [Group G] [Finite G]
    {S F X Y : Subgroup G} (hS : IsPGroup 2 S) (hFS : F ≤ S)
    (hSF : S ≤ normalizer (F : Set G)) (hX : ¬ 2 ∣ Nat.card X)
    (hXS : X ≤ normalizer (S : Set G)) (hXF : X ≤ normalizer (F : Set G))
    (hYS : Y ≤ S)
    (hY : ∀ x ∈ S, (∀ a ∈ X, x⁻¹ * (a * x * a⁻¹) ∈ F) ↔ x ∈ Y)
    (hYn : S ≤ normalizer (Y : Set G))
    (hab : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ F) :
    ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ * s⁻¹ ∈ F := by
  have hFY : F ≤ Y := by
    intro f hf
    refine (hY f (hFS hf)).1 fun a ha => ?_
    have h1 : a * f * a⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 (hXF ha) f).1 hf
    exact F.mul_mem (F.inv_mem hf) h1
  have hSbar : IsPGroup 2 (bar F S) := isPGroup_bar (A := F) hS
  have hXdvd : Nat.card (bar F X) ∣ Nat.card X := by
    have h1 := Subgroup.card_map_dvd (X.subgroupOf (normalizer (F : Set G))) (proj F)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hXF).toEquiv] at h1
  have hXbar_odd : ¬ 2 ∣ Nat.card (bar F X) := fun h => hX (dvd_trans h hXdvd)
  have hXbar_norm : bar F X ≤ normalizer ((bar F S : Subgroup (Bar F)) : Set (Bar F)) :=
    bar_le_normalizer_bar hFS hXS
  have hYbar : bar F S ⊓ centralizer ((bar F X : Subgroup (Bar F)) : Set (Bar F)) = bar F Y := by
    ext u
    obtain ⟨z, rfl⟩ := proj_surjective u
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, mem_bar_iff hFS z, mem_bar_iff hFY z]
    constructor
    · rintro ⟨hzS, hcen⟩
      refine (hY (z : G) hzS).1 fun a ha => ?_
      have haN : a ∈ normalizer (F : Set G) := hXF ha
      have hmem : proj F ⟨a, haN⟩ ∈ bar F X := proj_mem_bar ha
      exact (sec3103_conj_iff z.2 haN).2 (hcen _ hmem)
    · intro hzY
      refine ⟨hYS hzY, fun h hh => ?_⟩
      obtain ⟨a, haX, rfl⟩ := sec3103_exists_of_mem_bar (SetLike.mem_coe.1 hh)
      exact (sec3103_conj_iff z.2 a.2).1 ((hY (z : G) (hYS hzY)).2 hzY (a : G) haX)
  have hYab : bar F Y ≤ centralizer ((bar F Y : Subgroup (Bar F)) : Set (Bar F)) := by
    intro u hu
    obtain ⟨z, rfl⟩ := proj_surjective u
    have hz : (z : G) ∈ Y := (mem_bar_iff hFY z).1 hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨x, hx, rfl⟩ := sec3103_exists_of_mem_bar (SetLike.mem_coe.1 hv)
    exact (sec3103_comm_iff x.2 z.2).1 (hab _ hx _ hz)
  have hn : bar F S ≤ normalizer ((bar F S ⊓ centralizer ((bar F X : Subgroup (Bar F)) :
      Set (Bar F)) : Subgroup (Bar F)) : Set (Bar F)) := by
    rw [hYbar]
    exact bar_le_normalizer_bar hFY hYn
  obtain ⟨hsup, hcomm⟩ := yamada_sup_eq hSbar hXbar_odd hXbar_norm hn
  rw [hYbar] at hsup hcomm
  have hsub : bar F S ≤ centralizer ((bar F Y : Subgroup (Bar F)) : Set (Bar F)) := by
    have h := sup_le hYab hcomm
    rwa [hsup] at h
  intro y hy s hs
  have hyN : y ∈ normalizer (F : Set G) := hSF (hYS hy)
  have hsN : s ∈ normalizer (F : Set G) := hSF hs
  have hcs : proj F ⟨s, hsN⟩ ∈ bar F S := proj_mem_bar hs
  have hpy : proj F ⟨y, hyN⟩ ∈ bar F Y := proj_mem_bar hy
  refine (sec3103_comm_iff hyN hsN).2 ?_
  exact Subgroup.mem_centralizer_iff.1 (hsub hcs) (proj F ⟨y, hyN⟩) hpy

end Generic

section K9a

open CFSG.RankThree.PartOne.U5K.Hyp
open scoped Matrix

section Sec3103Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem sec3103_uSU_conj (c : K) {g : hypSU h 2 1} (hg : g ∈ Ssub h) :
    uSU h c * g * (uSU h c)⁻¹ ∈ Ssub h ∧
      crd (uSU h c * g * (uSU h c)⁻¹) = !![1, c; 0, 1] *ᵥ crd g := by
  have hdet : (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]; simp
  exact ⟨lev_conj_mem_Ssub _ (isUnit_det_upper c) hg, crd_lev ⟨!![1, c; 0, 1], hdet⟩ hg⟩

theorem sec3103_rSU_conj {g : hypSU h 2 1} (hg : g ∈ Ssub h) :
    rSU h * g * (rSU h)⁻¹ ∈ Ssub h ∧
      crd (rSU h * g * (rSU h)⁻¹) = (swapSL h : Matrix (Fin 2) (Fin 2) K) *ᵥ crd g := by
  have hS : IsUnit ((swapSL h : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have hR : rSU h = lev (hK := h) ((swapSL h : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) hS := by
    rw [rSU_eq_leviSU, lev_eq_leviSU]
  rw [hR]
  exact ⟨lev_conj_mem_Ssub _ hS hg, crd_lev (swapSL h) hg⟩

theorem sec3103_swapSL_coe :
    ((swapSL h : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

theorem sec3103_rSU_uSU_conj (c : K) {g : hypSU h 2 1} (hg : g ∈ Ssub h) :
    rSU h * uSU h c * (rSU h)⁻¹ * g * (rSU h * uSU h c * (rSU h)⁻¹)⁻¹ ∈ Ssub h ∧
      crd (rSU h * uSU h c * (rSU h)⁻¹ * g * (rSU h * uSU h c * (rSU h)⁻¹)⁻¹) =
        (swapSL h : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (!![1, c; 0, 1] *ᵥ ((swapSL h : Matrix (Fin 2) (Fin 2) K) *ᵥ crd g)) := by
  have hRi : (rSU h)⁻¹ = rSU h := inv_eq_of_mul_eq_one_right (rSU_mul_self (h := h))
  have hR1 := sec3103_rSU_conj hg
  have hU1 := sec3103_uSU_conj c hR1.1
  have hR2 := sec3103_rSU_conj hU1.1
  have hfact : rSU h * uSU h c * (rSU h)⁻¹ * g * (rSU h * uSU h c * (rSU h)⁻¹)⁻¹ =
      rSU h * (uSU h c * (rSU h * g * (rSU h)⁻¹) * (uSU h c)⁻¹) * (rSU h)⁻¹ := by
    simp only [mul_inv_rev, inv_inv, hRi, mul_assoc]
  rw [hfact]
  exact ⟨hR2.1, by rw [hR2.2, hU1.2, hR1.2]⟩

end Sec3103Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec3103_crd_eq_of_mem {g w : hypSU h 2 1} (hg : g ∈ Ssub h) (hwg : w * g * w⁻¹ ∈ Ssub h)
    (hA : d.η (g⁻¹ * (w * g * w⁻¹)) ∈ d.A₁) : crd (w * g * w⁻¹) = crd g := by
  obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 hA
  have hvg : v = g⁻¹ * (w * g * w⁻¹) :=
    d.η_injOn (Ssub_le_Usub (Vsub_le_Ssub hv)) (Ssub_le_Usub (mul_mem (inv_mem hg) hwg)) hve
  have hw : w * g * w⁻¹ = g * v := by rw [hvg, mul_inv_cancel_left]
  rw [hw, crd_mul hg (Vsub_le_Ssub hv), (crd_eq_zero_iff (Vsub_le_Ssub hv)).2 hv, add_zero]

theorem sec3103_eq_of_fixed_U₁_U₁r (hd : d.Hyp) {a : G} (ha : a ∈ d.A₃)
    (h1 : ∀ u ∈ d.U₁, a⁻¹ * (u * a * u⁻¹) ∈ d.A₁)
    (h2 : ∀ u ∈ d.U₁.map (MulAut.conj d.r).toMonoidHom, a⁻¹ * (u * a * u⁻¹) ∈ d.A₁) :
    a ∈ d.A₁ := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 ha
  have hr : d.r = d.η (rSU h) := rfl
  have hA1 : d.η (g⁻¹ * (uSU h 1 * g * (uSU h 1)⁻¹)) ∈ d.A₁ := by
    have e1 : d.η (g⁻¹ * (uSU h 1 * g * (uSU h 1)⁻¹)) =
        (d.η g)⁻¹ * (d.η (uSU h 1) * d.η g * (d.η (uSU h 1))⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e1]
    exact h1 _ (d.η_uSU_mem 1)
  have hU1eq : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) *ᵥ crd g = crd g :=
    (sec3103_uSU_conj 1 hg).2.symm.trans (sec3103_crd_eq_of_mem hg (sec3103_uSU_conj 1 hg).1 hA1)
  have hW := sec3103_rSU_uSU_conj 1 hg
  have hA2 : d.η (g⁻¹ * (rSU h * uSU h 1 * (rSU h)⁻¹ * g * (rSU h * uSU h 1 * (rSU h)⁻¹)⁻¹)) ∈ d.A₁ := by
    have hmemr : d.r * d.η (uSU h 1) * d.r⁻¹ ∈ d.U₁.map (MulAut.conj d.r).toMonoidHom :=
      Subgroup.mem_map.2 ⟨d.η (uSU h 1), d.η_uSU_mem 1, rfl⟩
    have e2 : d.η (g⁻¹ * (rSU h * uSU h 1 * (rSU h)⁻¹ * g * (rSU h * uSU h 1 * (rSU h)⁻¹)⁻¹)) =
        (d.η g)⁻¹ * (d.r * d.η (uSU h 1) * d.r⁻¹ * d.η g * (d.r * d.η (uSU h 1) * d.r⁻¹)⁻¹) := by
      simp only [hr, map_mul, map_inv]
    rw [e2]
    exact h2 _ hmemr
  have hcrdW := sec3103_crd_eq_of_mem hg hW.1 hA2
  rw [hW.2] at hcrdW
  have e0 := congrFun hU1eq 0
  have e1 := congrFun hcrdW 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, sec3103_swapSL_coe] at e0 e1
  have hx1 : crd g 1 = 0 := by linear_combination e0
  have hx0 : crd g 0 = 0 := by linear_combination e1
  have hz : crd g = 0 := by
    funext i
    fin_cases i
    · simpa using hx0
    · simpa using hx1
  exact Subgroup.mem_map_of_mem d.η ((crd_eq_zero_iff hg).1 hz)

end Data

end K9a

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec3103_A₃_le_D (hd : d.Hyp) {S : Subgroup G} (hP : d.P ≤ S) (sa : d.Sec39a S)
    (hFD : d.F ≤ d.D) : d.A₃ ≤ d.D := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := d.sec2_1_two hd.two_le
  rw [h8]
  refine sup_le (sup_le (hd.A₁_le_F.trans hFD) ?_) ?_
  · intro x hx
    have : x ∈ S ⊓ centralizer (d.I₂ : Set G) := ⟨hP hx.1, hx.2⟩
    rw [← sa.cD₂] at this
    exact this.1
  · intro x hx
    have : x ∈ S ⊓ centralizer (d.I₅ : Set G) := ⟨hP hx.1, hx.2⟩
    rw [← sa.cD₅] at this
    exact this.1

theorem Hyp.sec3103_mem_F_of_fixed (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hDB : d.D ≤ d.B₆) (hFD : d.F ≤ d.D) (hA₃D : d.A₃ ≤ d.D) (htD : d.t ∉ d.D)
    {x : G} (hx : x ∈ d.D)
    (h1 : ∀ u ∈ d.U₁, x⁻¹ * (u * x * u⁻¹) ∈ d.F)
    (h2 : ∀ u ∈ d.U₁.map (MulAut.conj d.r).toMonoidHom, x⁻¹ * (u * x * u⁻¹) ∈ d.F) :
    x ∈ d.F := by
  obtain ⟨ψ, -, hker, -, hequi⟩ := hd.exists_B₆_hom hGMS
  have hFA₁ : d.F ⊓ d.A₃ ≤ d.A₁ := by
    obtain ⟨-, -, -, -, -, -, hFB3, -⟩ := hd.sec3_4 hGMS
    rw [← hFB3]
    exact inf_le_inf_left _ d.A₃_le_B₃
  have hr : ∀ u ∈ d.U₁.map (MulAut.conj d.r).toMonoidHom, u ∈ d.N₁ := by
    intro u hu
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    exact mul_mem (mul_mem d.r_mem_N₁ (d.U₁_le_N₁ hu')) (inv_mem d.r_mem_N₁)
  have key : ∀ u ∈ d.N₁, x⁻¹ * (u * x * u⁻¹) ∈ d.F → ∀ a : ↥d.A₃,
      ψ ⟨x, hDB hx⟩ = QuotientGroup.mk a → (a : G)⁻¹ * (u * a * u⁻¹) ∈ d.A₁ := by
    intro u hu hf a ha
    have huc : u ∈ normalizer (d.B₃ : Set G) ⊓ centralizer ({d.t} : Set G) :=
      ⟨hd.N₁_le_normalizer_B₃ hu, hd.N₁_le_centralizer_t hu⟩
    have huD : u * x * u⁻¹ ∈ d.D := (mem_normalizer_iff.1 (hd.N₁_le_normalizer_D hu) x).1 hx
    have hua : u * a * u⁻¹ ∈ d.A₃ := (mem_normalizer_iff.1 (d.N₁_le_normalizer_A₃ hu) a).1 a.2
    have heq := hequi u huc ⟨x, hDB hx⟩ a (hDB huD) hua ha
    have hfD : x⁻¹ * (u * x * u⁻¹) ∈ d.D := mul_mem (inv_mem hx) huD
    have hmul : (⟨u * x * u⁻¹, hDB huD⟩ : d.B₆) =
        ⟨x, hDB hx⟩ * ⟨x⁻¹ * (u * x * u⁻¹), hDB hfD⟩ :=
      Subtype.ext (by simp)
    have hker1 : ψ ⟨x⁻¹ * (u * x * u⁻¹), hDB hfD⟩ = 1 := by
      have : (⟨x⁻¹ * (u * x * u⁻¹), hDB hfD⟩ : d.B₆) ∈ ψ.ker := by
        rw [hker]
        exact Subgroup.mem_subgroupOf.2 (mem_sup_left hf)
      exact this
    rw [hmul, map_mul, hker1, mul_one, ha] at heq
    have := QuotientGroup.eq.1 heq
    have := Subgroup.mem_subgroupOf.1 this
    simpa using this
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨x, hDB hx⟩)
  have hfixa : (a : G) ∈ d.A₁ := by
    refine sec3103_eq_of_fixed_U₁_U₁r hd a.2
      (fun u hu => key u (d.U₁_le_N₁ hu) (h1 u hu) a ha.symm)
      (fun u hu => key u (hr u hu) (h2 u hu) a ha.symm)
  have hψ1 : ψ ⟨x, hDB hx⟩ = 1 := by
    rw [← ha]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hfixa)
  have hxFB : x ∈ d.F ⊔ d.B₃ := by
    have : (⟨x, hDB hx⟩ : d.B₆) ∈ ψ.ker := hψ1
    rw [hker] at this
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨y, hy, a₀, ha₀, e | e⟩ := hd.exists_of_mem_FB₃ hxFB
  ·
    have hA₃F : d.A₃ ≤ normalizer (d.F : Set G) := hd.A₃_le_normalizer_F hGMS
    have key2 : ∀ u ∈ d.N₁, x⁻¹ * (u * x * u⁻¹) ∈ d.F → a₀⁻¹ * (u * a₀ * u⁻¹) ∈ d.A₁ := by
      intro u hu hf
      have huF : u ∈ normalizer (d.F : Set G) := d.N₁_le_normalizer_F hu
      have huA : u * a₀ * u⁻¹ ∈ d.A₃ := (mem_normalizer_iff.1 (d.N₁_le_normalizer_A₃ hu) a₀).1 ha₀
      have hy1 : y⁻¹ * (u * y * u⁻¹) ∈ d.F :=
        mul_mem (inv_mem hy) ((mem_normalizer_iff.1 huF y).1 hy)
      have hc : a₀⁻¹ * (y⁻¹ * (u * y * u⁻¹))⁻¹ * a₀⁻¹⁻¹ ∈ d.F :=
        (mem_normalizer_iff.1 (inv_mem (hA₃F ha₀)) _).1 (inv_mem hy1)
      have e1 : a₀⁻¹ * (u * a₀ * u⁻¹) =
          (a₀⁻¹ * (y⁻¹ * (u * y * u⁻¹))⁻¹ * a₀⁻¹⁻¹) * (x⁻¹ * (u * x * u⁻¹)) := by
        rw [e]; group
      have hF1 : a₀⁻¹ * (u * a₀ * u⁻¹) ∈ d.F := by
        rw [e1]
        exact mul_mem hc hf
      exact hFA₁ (Subgroup.mem_inf.2 ⟨hF1, mul_mem (inv_mem ha₀) huA⟩)
    have : a₀ ∈ d.A₁ :=
      sec3103_eq_of_fixed_U₁_U₁r hd ha₀ (fun u hu => key2 u (d.U₁_le_N₁ hu) (h1 u hu))
        (fun u hu => key2 u (hr u hu) (h2 u hu))
    rw [e]
    exact mul_mem hy (hd.A₁_le_F this)
  · exfalso
    apply htD
    have : d.t = y⁻¹ * x * a₀⁻¹ := by rw [e]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (hFD hy)) hx) (inv_mem (hA₃D ha₀))

end Data

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec3103_V₁_inf_section (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hA₃D : d.A₃ ≤ d.D) : d.V₁ ⊓ centralizerSection d.D d.F = ⊥ := by
  by_contra hne
  set K₁ : Subgroup G := d.V₁ ⊓ centralizerSection d.D d.F with hK₁
  haveI := hd.isElementaryAbelian_V₁ hGMS
  have hV₂ : IsPGroup 2 d.V₁ := CFSG.IsElementaryAbelian.isPGroup 2 d.V₁
  have hK2 : IsPGroup 2 K₁ := hV₂.to_le inf_le_left
  have htN : zpowers d.t ≤ normalizer (K₁ : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_fintype fun v hv => ?_
    have hv' : v ∈ K₁ := hv
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.1 hd.t_mem_normalizer_V₁ v).1 (Subgroup.mem_inf.1 hv').1
    · exact sec3103_conj_mem_centralizerSection hd.t_mem_normalizer_D hd.t_mem_normalizer_F
        (Subgroup.mem_inf.1 hv').2
  have hY : ∀ y ∈ zpowers d.t, ∃ k : ℕ, y ^ 2 ^ k ∈ centralizer (K₁ : Set G) := by
    intro y hy
    obtain ⟨k, hk⟩ := hd.isPGroup_zpowers_t ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact one_mem _
  have hne2 := Prelim.inf_centralizer_ne_bot_of_pow_mem hK2 hne htN hY
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne2
  obtain ⟨hu₁, hut⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨huV, hus⟩ := Subgroup.mem_inf.1 hu₁
  have huC : u ∈ centralizer ({d.t} : Set G) := mem_centralizer_iff.2 fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact mem_centralizer_iff.1 hut _ (mem_zpowers _)
  have huU : u ∈ d.U₁ := by
    rw [← hd.V₁_inf_centralizer_t hGMS]
    exact Subgroup.mem_inf.2 ⟨huV, huC⟩
  have huN₁ : u ∈ d.N₁ := d.U₁_le_N₁ huU
  have hFA₁ : d.F ⊓ d.A₃ ≤ d.A₁ := by
    obtain ⟨-, -, -, -, -, -, hFB3, -⟩ := hd.sec3_4 hGMS
    rw [← hFB3]
    exact inf_le_inf_left _ d.A₃_le_B₃
  have hAcomm : ∀ a ∈ d.A₃, u * a * u⁻¹ * a⁻¹ ∈ d.A₁ := by
    intro a ha
    have h1 : a⁻¹ * (u * a * u⁻¹) ∈ d.F := hus.2.2 a (hA₃D ha)
    have h2 : a⁻¹ * (u * a * u⁻¹) ∈ d.A₃ :=
      mul_mem (inv_mem ha) ((mem_normalizer_iff.1 (d.N₁_le_normalizer_A₃ huN₁) a).1 ha)
    have h3 : a⁻¹ * (u * a * u⁻¹) ∈ d.A₁ := hFA₁ (Subgroup.mem_inf.2 ⟨h1, h2⟩)
    have h4 := (mem_normalizer_iff.1 (s2a2_A₃_le_normalizer_A₁ d ha) _).1 h3
    have e : a * (a⁻¹ * (u * a * u⁻¹)) * a⁻¹ = u * a * u⁻¹ * a⁻¹ := by group
    rwa [e] at h4
  have huc : u ∈ normalizer (d.B₁ : Set G) ⊓ centralizer ({d.t} : Set G) := by
    refine ⟨?_, huC⟩
    rw [hd.normalizer_B₁_eq]
    exact hd.N₁_le_normalizer_B₃ huN₁
  have huB₃ : u ∈ d.B₃ := hd.mem_B₃_of_commutator_mem_A₁ huc hAcomm
  have hP₁ : u ∈ d.P := d.U₁_le_P huU
  obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup (d.A₃_le_P.trans d.P_le_L) huB₃
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨-, hbot⟩⟩ := d.sec2_1_two hd.two_le
    have hmem : u ∈ d.A₃ ⊓ (d.P ⊓ centralizer (d.I₁ : Set G)) := by
      refine Subgroup.mem_inf.2 ⟨e ▸ ha, ?_⟩
      rw [← d.U₁_eq hd.two_le]
      exact huU
    rw [hbot] at hmem
    exact hu1 (Subtype.ext (Subgroup.mem_bot.1 hmem))
  · have : d.t = u * a⁻¹ := by rw [e]; group
    exact hd.t_not_mem_L (this ▸ d.P_le_L (mul_mem hP₁ (inv_mem (d.A₃_le_P ha))))

theorem Hyp.sec3103_Zt_le_D (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {S : Subgroup G} (hSDV : S = d.D ⊔ d.V₁) (hSD : S ≤ normalizer (d.D : Set G))
    (hSF : S ≤ normalizer (d.F : Set G)) (hFD : d.F ≤ d.D) (hsq : ∀ x ∈ d.D, x * x ∈ d.F)
    (hA₃D : d.A₃ ≤ d.D) : S ⊓ centralizerSection S d.F ≤ d.D := by
  intro g hg
  obtain ⟨hgS, hgN⟩ := Subgroup.mem_inf.1 hg
  have hgc : ∀ y ∈ S, y⁻¹ * (g * y * g⁻¹) ∈ d.F := hgN.2.2
  have hDS : d.D ≤ S := hSDV ▸ le_sup_left
  have hV₁S : d.V₁ ≤ S := hSDV ▸ le_sup_right
  have hV₁D : d.V₁ ≤ normalizer (d.D : Set G) := hV₁S.trans hSD
  have hmul : ((d.D ⊔ d.V₁ : Subgroup G) : Set G) = (d.D : Set G) * (d.V₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hV₁D
  have hg' : g ∈ ((d.D ⊔ d.V₁ : Subgroup G) : Set G) := hSDV ▸ hgS
  rw [hmul] at hg'
  obtain ⟨x, hx, v, hv, hxv⟩ := hg'
  have hvS : v ∈ S := hV₁S hv
  have hvs : v ∈ centralizerSection d.D d.F := by
    refine ⟨hSD hvS, hSF hvS, fun y hy => ?_⟩
    have hyS : y ∈ S := hDS hy
    have h1 := hgc y hyS
    have hy'D : v * y * v⁻¹ ∈ d.D := (mem_normalizer_iff.1 (hSD hvS) y).1 hy
    have hcomm := sec3103_comm_mem_of_sq_mem (fun z hz => hSF (hDS hz)) hsq
      (v * y * v⁻¹)⁻¹ (inv_mem hy'D) x hx
    have e : y⁻¹ * (v * y * v⁻¹) =
        (y⁻¹ * (g * y * g⁻¹)) * ((v * y * v⁻¹)⁻¹ * x * (v * y * v⁻¹)⁻¹⁻¹ * x⁻¹)⁻¹ := by
      rw [← hxv]; group
    rw [e]
    exact mul_mem h1 (inv_mem hcomm)
  have hv1 : v = 1 := by
    have : v ∈ d.V₁ ⊓ centralizerSection d.D d.F := Subgroup.mem_inf.2 ⟨hv, hvs⟩
    rw [hd.sec3103_V₁_inf_section hGMS hA₃D] at this
    exact Subgroup.mem_bot.1 this
  have hg1 : g = x := by
    rw [← hxv, hv1]
    exact mul_one x
  rw [hg1]
  exact hx

end Data

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec310Three_of_hyp (hp : d.CaseHyp) (k : d.Know93) (h1 : d.Sec3_10_one)
    (h2 : d.Sec3_10_two) : d.Sec310Three := by
  intro S hS hPS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGMS := hp.gms
  have hd := hp.hyp
  have O := sec3101Orders_of_hyp hp k S hS hPS
  have sa := k.s9a S hS hPS
  have se := k.s9e
  obtain ⟨hSED, hEchar, hDchar⟩ := k.s9_1 S hS hPS
  obtain ⟨-, -, -, hZD, hsq⟩ := k.s9_2 S hS hPS
  obtain ⟨-, -, -, -, -, -, -, -, -, hc10, -, hc12⟩ := h1 S hS hPS
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hES : d.E ≤ S := hSED ▸ le_sup_left
  have hDS : d.D ≤ S := hSED ▸ le_sup_right
  have hFD : d.F ≤ d.D := hZD ▸ inf_le_left
  have hFS : d.F ≤ S := hFD.trans hDS
  have hSE : S ≤ normalizer (d.E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 (by
      haveI : (d.E.subgroupOf S).Characteristic := hEchar
      infer_instance)
  have hSD : S ≤ normalizer (d.D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).1 (by
      haveI : (d.D.subgroupOf S).Characteristic := hDchar
      infer_instance)
  have hSF : S ≤ normalizer (d.F : Set G) := by
    have := normalizer_le_normalizer_centerIn d.D
    rw [hZD] at this
    exact hSD.trans this
  have hV₁S : d.V₁ ≤ S := (hd.s4o_V₁_le_E hGMS).trans hES
  have hC₁ : S ⊓ centralizer (d.I₁ : Set G) = d.V₁ := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf hV₁S d.V₁_le_centralizer_I₁) ?_).symm
    rw [O.c₁, hd.card_V₁ hGMS]
  have hSDV : S = d.D ⊔ d.V₁ := by
    rw [← hC₁]
    exact hc12.1
  have hA₃D : d.A₃ ≤ d.D := sec3103_A₃_le_D hd hPS sa hFD
  have hDB : d.D ≤ d.B₆ := sa.B₆_eq ▸ le_sup_left
  have hYeq : (d.E ⊓ d.D) ⊔ d.F = d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) := by
    rw [sup_comm]
    exact hc10
  rw [hYeq]
  set Y : Subgroup G := d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) with hY
  have hYS : Y ≤ S := sup_le hFS inf_le_left
  have hYD : Y ≤ d.D := by
    refine sup_le hFD ?_
    rw [← sa.cD₅]
    exact inf_le_left
  have hYn : S ≤ normalizer (Y : Set G) := by
    rw [← hYeq]
    intro s hs
    exact Common.mem_normalizer_sup (mem_normalizer_inf (hSE hs) (hSD hs)) (hSF hs)
  have hIS : d.I ≤ normalizer (S : Set G) := by
    rw [hSDV]
    intro i hi
    exact Common.mem_normalizer_sup (hd.s2a2_I_le_D hGMS hi) (hd.s4o_I_le_normalizer_V₁ hGMS hi)
  have hI₅odd : Odd (Nat.card d.I₅) :=
    (Data.odd_card_I d).of_dvd_nat (Subgroup.card_dvd_of_le d.I₅_le_I)
  obtain ⟨hsolv, hcop⟩ := s4o_sc (H := d.I₅) hS2 hI₅odd
  have hXS : d.I₅ ≤ normalizer (S : Set G) := d.I₅_le_I.trans hIS
  have hXF : d.I₅ ≤ normalizer (d.F : Set G) := d.I₅_le_I.trans (hd.I_le_normalizer_F hGMS)
  have hYiff : ∀ x ∈ S, (∀ a ∈ d.I₅, x⁻¹ * (a * x * a⁻¹) ∈ d.F) ↔ x ∈ Y := by
    intro x hx
    constructor
    · intro hfix
      obtain ⟨c, hc, n, hn, hcn⟩ :=
        Common.exists_mem_inf_centralizer_mul_of_coprime hFS hSF hXS hXF hsolv hcop hx hfix
      rw [hcn]
      exact mul_mem (mem_sup_right hc) (mem_sup_left hn)
    · intro hx'
      have hmul : ((d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) : Subgroup G) : Set G) =
          (d.F : Set G) * ((S ⊓ centralizer (d.I₅ : Set G) : Subgroup G) : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hSF)
      have hx'' : x ∈ ((d.F ⊔ (S ⊓ centralizer (d.I₅ : Set G)) : Subgroup G) : Set G) := hx'
      rw [hmul] at hx''
      obtain ⟨f₀, hf₀, c, hc, hfc⟩ := hx''
      intro a ha
      have hcS : c ∈ S := (Subgroup.mem_inf.1 hc).1
      have hcC : a * c = c * a := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 a ha
      have hac : a * c * a⁻¹ = c := by rw [hcC, mul_inv_cancel_right]
      have hfa : f₀⁻¹ * (a * f₀ * a⁻¹) ∈ d.F :=
        mul_mem (inv_mem hf₀) ((mem_normalizer_iff.1 (hXF ha) f₀).1 hf₀)
      have hx0 : x = f₀ * c := hfc.symm
      have e : x⁻¹ * (a * x * a⁻¹) = c⁻¹ * (f₀⁻¹ * (a * f₀ * a⁻¹)) * (a * c * a⁻¹) := by
        rw [hx0]; group
      rw [e, hac]
      have := (mem_normalizer_iff.1 (hSF (inv_mem hcS)) _).1 hfa
      simpa using this
  have hcen : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ * s⁻¹ ∈ d.F :=
    sec3103_section_centralizer_le_center hS2 hFS hSF
      (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hI₅odd)) hXS hXF hYS hYiff hYn
      (fun x hx y hy => sec3103_comm_mem_of_sq_mem (fun z hz => hSF (hDS hz)) hsq x (hYD hx) y
        (hYD hy))
  set Zt : Subgroup G := S ⊓ centralizerSection S d.F with hZt
  have hYZ : Y ≤ Zt := by
    intro y hy
    refine Subgroup.mem_inf.2 ⟨hYS hy, Subgroup.le_normalizer (hYS hy), hSF (hYS hy),
      fun x hx => ?_⟩
    have h1 := (mem_normalizer_iff.1 (hSF (inv_mem hx)) _).1 (hcen y hy x hx)
    have e : x⁻¹ * (y * x * y⁻¹) = x⁻¹ * (y * x * y⁻¹ * x⁻¹) * x⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have hZD' : Zt ≤ d.D := hd.sec3103_Zt_le_D hGMS hSDV hSD hSF hFD hsq hA₃D
  set Zr : Subgroup G := Zt.map (MulAut.conj d.r).toMonoidHom with hZr
  have hrD : d.r ∈ normalizer (d.D : Set G) := hd.N₁_le_normalizer_D d.r_mem_N₁
  have hrF : d.r ∈ normalizer (d.F : Set G) := d.N₁_le_normalizer_F d.r_mem_N₁
  have hZrD : Zr ≤ d.D := by
    rintro _ ⟨z, hz, rfl⟩
    exact (mem_normalizer_iff.1 hrD z).1 (hZD' hz)
  have key1 : ∀ z ∈ Zt, ∀ u ∈ d.U₁, z⁻¹ * (u * z * u⁻¹) ∈ d.F := by
    intro z hz u hu
    have huS : u ∈ S := hV₁S (hd.U₁_le_V₁ hGMS hu)
    have hzS : z ∈ S := (Subgroup.mem_inf.1 hz).1
    exact sec3103_swap hSF hzS huS ((Subgroup.mem_inf.1 hz).2.2.2 u huS)
  have hinf : Zt ⊓ Zr ≤ d.F := by
    intro x hx
    obtain ⟨hxZ, hxr⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨x', hx', hxx'⟩ := hxr
    have hxD : x ∈ d.D := hZD' hxZ
    refine hd.sec3103_mem_F_of_fixed hGMS hDB hFD hA₃D se.t_not_mem_D hxD
      (fun u hu => key1 x hxZ u hu) (fun u hu => ?_)
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    have h3 := (mem_normalizer_iff.1 hrF _).1 (key1 x' hx' u' hu')
    have e : x⁻¹ * ((MulAut.conj d.r).toMonoidHom u' * x * ((MulAut.conj d.r).toMonoidHom u')⁻¹) =
        d.r * (x'⁻¹ * (u' * x' * u'⁻¹)) * d.r⁻¹ := by
      rw [← hxx']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact h3
  have hcardmul := sec3103_card_mul_le_of_finite hZD' hZrD
  have hcardr : Nat.card Zr = Nat.card Zt :=
    Subgroup.card_map_of_injective (MulAut.conj d.r).injective
  have hinfc : Nat.card (Zt ⊓ Zr : Subgroup G) ≤ (2 ^ f) ^ 8 := by
    have := Subgroup.card_le_of_le hinf
    rwa [hd.card_F hGMS] at this
  have hZcard : Nat.card Zt ≤ (2 ^ f) ^ 12 := by
    rw [hcardr, se.card_D] at hcardmul
    have h5 : Nat.card Zt * Nat.card Zt ≤ (2 ^ f) ^ 12 * (2 ^ f) ^ 12 := by
      calc Nat.card Zt * Nat.card Zt ≤ (2 ^ f) ^ 16 * Nat.card (Zt ⊓ Zr : Subgroup G) := hcardmul
        _ ≤ (2 ^ f) ^ 16 * (2 ^ f) ^ 8 := Nat.mul_le_mul_left _ hinfc
        _ = (2 ^ f) ^ 12 * (2 ^ f) ^ 12 := by ring
    exact Nat.mul_self_le_mul_self_iff.1 h5
  have hYcard : Nat.card Y = (2 ^ f) ^ 12 := by
    have key := Common.card_sup_mul_card_inf_eq (A := d.F) (B := S ⊓ centralizer (d.I₅ : Set G))
      (inf_le_left.trans hSF)
    have hFinf : d.F ⊓ (S ⊓ centralizer (d.I₅ : Set G)) = d.F ⊓ centralizer (d.I₅ : Set G) := by
      rw [← inf_assoc, inf_of_le_left hFS]
    rw [hFinf, O.cF₅, hd.card_F hGMS, O.c₅] at key
    have hq : 0 < (2 ^ f) ^ 2 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [key]
    ring
  exact (Subgroup.eq_of_le_of_card_ge hYZ (hZcard.trans hYcard.ge)).symm

end Data

namespace CaseBParts

theorem sec310Three : Sec310ThreeStatement :=
  fun _ _ _ _ _ _ _ _ hp k h1 h2 => Data.sec310Three_of_hyp hp k h1 h2

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
