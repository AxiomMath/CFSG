module

public import CFSG.CGT.Foote81L6.Normalizer.OrderThreeCard
public import CFSG.CGT.Foote81L6.Normalizer.GBasic
public import CFSG.CGT.Foote81L6.Normalizer.Lemma8
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def commZ {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)
    (p : G) : Subgroup G :=
  closure {c | ∃ j : ℤ, ∃ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁),
    c = p ^ j * z * (p ^ j)⁻¹ * z⁻¹}

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n) {p : G}

theorem mem_normalizer_Z_of_comm
    (hcomm : ∀ x ∈ D.T₁, p * x * p⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)) :
    p ∈ normalizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G) := by
  refine TStruct.mem_normalizer_of_forall_conj_mem fun z hz => ?_
  have hzT₁ : z ∈ D.T₁ := sup_le D.A_le_T₁
    (sup_le (zpowers_le.2 (D.B₀B₁_le_T₁ (mem_sup_left D.b₀_mem)))
      (zpowers_le.2 (D.B₀B₁_le_T₁ (mem_sup_right D.b₁_mem)))) hz
  rw [show p * z * p⁻¹ = (p * z * p⁻¹ * z⁻¹) * z by group]
  exact mul_mem (hcomm z hzT₁) hz

theorem commZ_le_Z (hcomm : ∀ x ∈ D.T₁, p * x * p⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)) :
    commZ D p ≤ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
  have hpN := mem_normalizer_Z_of_comm D hcomm
  refine (closure_le _).2 ?_
  rintro _ ⟨j, z, hz, rfl⟩
  exact mul_mem ((mem_normalizer_iff.1 (zpow_mem hpN j) z).1 hz) (inv_mem hz)

variable {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F)

include hF in
theorem mem_normalizer_of_comm
    (hcomm : ∀ x ∈ D.T₁, p * x * p⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)) :
    p ∈ normalizer (F : Set G) := by
  haveI := hF.finite
  refine TStruct.mem_normalizer_of_forall_conj_mem fun v hv => ?_
  rw [show p * v * p⁻¹ = (p * v * p⁻¹ * v⁻¹) * v by group]
  exact mul_mem (Z_le_E64 D hF (hcomm v (D.le_T₁_of_isE64 hF hv))) hv

variable (hcomm : ∀ x ∈ D.T₁, p * x * p⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁))
  [IsMulCommutative ↥F]

include hF in
theorem ρ_pbar_pow_three (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x) :
    NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) ^ 3 = 1 := by
  refine MulEquiv.ext fun v => Subtype.ext ?_
  rw [← map_pow, ← map_pow, NBar.ρ_π, Subgroup.coe_pow]
  exact hcube v (D.le_T₁_of_isE64 hF v.2)

include hF in
theorem ρ_pbar_ne_one (hmove : ∃ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), p * z * p⁻¹ ≠ z) :
    NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) ≠ 1 := by
  obtain ⟨z, hz, hpz⟩ := hmove
  intro h
  apply hpz
  have := (ρ_π_eq_self_iff (F := F) ⟨p, mem_normalizer_of_comm D hF hcomm⟩ ⟨z, Z_le_E64 D hF hz⟩).1
    (by rw [h, MulAut.one_apply])
  exact this

include hF in
theorem orderOf_pbar (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x)
    (hmove : ∃ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), p * z * p⁻¹ ≠ z) :
    orderOf (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · apply NBar.ρ_injective F
    rw [map_pow, ρ_pbar_pow_three D hF hcomm hcube, map_one]
  · intro h
    exact ρ_pbar_ne_one D hF hcomm hmove (by rw [h, map_one])

include hF in
theorem pbar_comm (x : ↥(normalizer (F : Set G))) (hx : (x : G) ∈ D.T₁) :
    NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩ * NBar.π F x =
      NBar.π F x * NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩ := by
  set pN : ↥(normalizer (F : Set G)) := ⟨p, mem_normalizer_of_comm D hF hcomm⟩
  have h : NBar.π F x = NBar.π F (pN * x * pN⁻¹) := by
    refine π_eq_of_inv_mul_mem _ _ ?_
    have hc := Z_le_E64 D hF (hcomm x hx)
    have e : ((x : G))⁻¹ * ((pN * x * pN⁻¹ : ↥(normalizer (F : Set G))) : G) =
        (x : G)⁻¹ * (p * x * p⁻¹ * (x : G)⁻¹) * (x : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, pN]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (inv_mem x.2) _).1 hc
  rw [map_mul, map_mul, map_inv] at h
  calc NBar.π F pN * NBar.π F x
      = (NBar.π F pN * NBar.π F x * (NBar.π F pN)⁻¹) * NBar.π F pN := by group
    _ = NBar.π F x * NBar.π F pN := by rw [← h]

include hF in
theorem commV_pbar_le_Z (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x) {w : ↥F}
    (hw : w ∈ commV (zpowers (NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩)))) :
    (w : G) ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
  set x := NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) with hx
  have hx3 := ρ_pbar_pow_three D hF hcomm hcube
  have hxv : ∀ v : ↥F, ((x v * v⁻¹ : ↥F) : G) ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) := by
    intro v
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hx, NBar.ρ_π]
    exact hcomm v (D.le_T₁_of_isE64 hF v.2)
  have hle : commV (zpowers x) ≤ (D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)).comap F.subtype := by
    refine (closure_le _).2 ?_
    rintro _ ⟨y, hy, v, rfl⟩
    rcases eq_one_or_of_mem_zpowers hx3 hy with rfl | rfl | rfl
    · rw [MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    · exact hxv v
    · rw [show ((x * x) v * v⁻¹ : ↥F) = (x (x v) * (x v)⁻¹) * (x v * v⁻¹) by
        rw [MulAut.mul_apply]; group]
      exact mul_mem (hxv (x v)) (hxv v)
  exact hle hw

include hF in
theorem mem_commV_iff (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x) (w : ↥F) :
    w ∈ commV (zpowers (NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩))) ↔
      (w : G) ∈ commZ D p := by
  haveI := hF.finite
  set pN : ↥(normalizer (F : Set G)) := ⟨p, mem_normalizer_of_comm D hF hcomm⟩ with hpN
  set x := NBar.ρ F (NBar.π F pN) with hx
  have hx3 : x ^ 3 = 1 := ρ_pbar_pow_three D hF hcomm hcube
  have hV : ∀ v : ↥F, v * v = 1 := fun v => Subtype.ext (hF.mul_self v v.2)
  have hxj : ∀ (j : ℤ) (v : ↥F), (((x ^ j) v : ↥F) : G) = p ^ j * v * (p ^ j)⁻¹ := by
    intro j v
    rw [hx, ← map_zpow, ← map_zpow, NBar.ρ_π, Subgroup.coe_zpow]
  constructor
  · intro hw
    have hle : commSub (commV (zpowers x)) (zpowers x) ≤ (commZ D p).comap F.subtype := by
      refine (closure_le _).2 ?_
      rintro _ ⟨y, hy, u, hu, rfl⟩
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hy
      show ((((x ^ j) u * u⁻¹ : ↥F)) : G) ∈ commZ D p
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hxj]
      exact subset_closure ⟨j, u, commV_pbar_le_Z D hF hcomm hcube hu, rfl⟩
    exact hle (commV_le_commSub hV hx3 hw)
  · intro hw
    have hle : commZ D p ≤ (commV (zpowers x)).map F.subtype := by
      refine (closure_le _).2 ?_
      rintro _ ⟨j, z, hz, rfl⟩
      refine ⟨(x ^ j) ⟨z, Z_le_E64 D hF hz⟩ * (⟨z, Z_le_E64 D hF hz⟩ : ↥F)⁻¹,
        subset_closure ⟨x ^ j, zpow_mem (mem_zpowers x) j, _, rfl⟩, ?_⟩
      rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hxj]
    obtain ⟨w', hw', hw'w⟩ := hle hw
    rw [show w = w' from Subtype.ext hw'w.symm]
    exact hw'

include hF in
theorem pbar_fix_b (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x) :
    NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) ⟨D.b₀, D.b₀_mem_E64 hF⟩ =
        ⟨D.b₀, D.b₀_mem_E64 hF⟩ ∧
      NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) ⟨D.b₁, D.b₁_mem_E64 hF⟩ =
        ⟨D.b₁, D.b₁_mem_E64 hF⟩ := by
  have hb₀ : p * D.b₀ * p⁻¹ = D.b₀ := by
    have h := hcomm D.b₀ (D.B₀B₁_le_T₁ (mem_sup_left D.b₀_mem))
    obtain ⟨d₀, hd₀R, -, hd₀F, -, -⟩ := D.exists_d₀ hF
    obtain ⟨htv, hd₀1⟩ := isTransvectionWith_d₀ D hF hd₀R hd₀F
    have hc := pbar_comm D hF hcomm ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀R⟩
      (D.B₀B₁_le_T₁ (mem_sup_left (mem_inf.1 hd₀R).1))
    have hcρ := congrArg (NBar.ρ F) hc
    rw [map_mul, map_mul] at hcρ
    have := B1.tv_comm_centre htv hd₀1 hcρ
    have h2 := congrArg Subtype.val this
    rwa [NBar.ρ_π] at h2
  have hb₁ : p * D.b₁ * p⁻¹ = D.b₁ := by
    obtain ⟨d₁, hd₁R, -, hd₁F, -, -⟩ := D.exists_d₁ hF
    obtain ⟨htv, hd₁1⟩ := isTransvectionWith_d₁ D hF hd₁R hd₁F
    have hc := pbar_comm D hF hcomm ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁R⟩
      (D.B₀B₁_le_T₁ (mem_sup_right (mem_inf.1 hd₁R).1))
    have hcρ := congrArg (NBar.ρ F) hc
    rw [map_mul, map_mul] at hcρ
    have := B1.tv_comm_centre htv hd₁1 hcρ
    have h2 := congrArg Subtype.val this
    rwa [NBar.ρ_π] at h2
  exact ⟨(ρ_π_eq_self_iff _ _).2 hb₀, (ρ_π_eq_self_iff _ _).2 hb₁⟩

include hF in
theorem map_commV_pbar (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x) :
    (commV (zpowers (NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩)))).map
      F.subtype = commZ D p := by
  ext g
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_commV_iff D hF hcomm hcube w).1 hw
  · intro hg
    have hgF : g ∈ F := Z_le_E64 D hF (commZ_le_Z D hcomm hg)
    exact ⟨⟨g, hgF⟩, (mem_commV_iff D hF hcomm hcube ⟨g, hgF⟩).2 hg, rfl⟩

include hF hcomm in
theorem card_commZ (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x)
    (hmove : ∃ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), p * z * p⁻¹ ≠ z) :
    Nat.card (commZ D p) = 4 := by
  haveI := hF.finite
  set x := NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) with hx
  have hV : ∀ v : ↥F, v * v = 1 := fun v => Subtype.ext (hF.mul_self v v.2)
  rw [← map_commV_pbar D hF hcomm hcube, card_map_of_injective F.subtype_injective]
  set W : Subgroup ↥F := (D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁)).subgroupOf F with hW
  have hW16 : Nat.card W ≤ 16 := by
    rw [hW, Nat.card_congr (subgroupOfEquivOfLe (Z_le_E64 D hF)).toEquiv, card_Z D]
  have hUW : commV (zpowers x) ≤ W := fun w hw => by
    rw [hW, mem_subgroupOf]
    exact commV_pbar_le_Z D hF hcomm hcube hw
  obtain ⟨hb₀, hb₁⟩ := pbar_fix_b D hF hcomm hcube
  refine card_commV_zpowers_eq_four hV hF.2.2 (ρ_pbar_pow_three D hF hcomm hcube)
    (ρ_pbar_ne_one D hF hcomm hmove) hW16 hUW (b₀ := ⟨D.b₀, D.b₀_mem_E64 hF⟩)
    (b₁ := ⟨D.b₁, D.b₁_mem_E64 hF⟩) ?_ ?_ hb₀ hb₁ ?_ ?_ ?_
  · rw [hW, mem_subgroupOf]; exact mem_sup_right (mem_sup_left (mem_zpowers _))
  · rw [hW, mem_subgroupOf]; exact mem_sup_right (mem_sup_right (mem_zpowers _))
  · exact fun h => D.b₀_ne_one (congrArg Subtype.val h)
  · exact fun h => D.b₁_ne_one (congrArg Subtype.val h)
  · intro h
    have hb : D.b₀ = D.b₁ := congrArg Subtype.val h
    have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨D.b₀_mem, hb ▸ D.b₁_mem⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    exact D.b₀_ne_one this

include hF hcomm in
theorem commZ_inf (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x) :
    commZ D p ⊓ (zpowers D.b₀ ⊔ zpowers D.b₁) = ⊥ := by
  haveI := hF.finite
  set x := NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) with hx
  have hV : ∀ v : ↥F, v * v = 1 := fun v => Subtype.ext (hF.mul_self v v.2)
  have hinf0 := commV_zpowers_inf_eq hV (ρ_pbar_pow_three D hF hcomm hcube)
  obtain ⟨hb₀, hb₁⟩ := pbar_fix_b D hF hcomm hcube
  have hfixG : zpowers D.b₀ ⊔ zpowers D.b₁ ≤ (fixV (zpowers x)).map F.subtype :=
    sup_le (zpowers_le.2 ⟨⟨D.b₀, D.b₀_mem_E64 hF⟩, mem_fixV_zpowers_iff_apply.2 hb₀, rfl⟩)
      (zpowers_le.2 ⟨⟨D.b₁, D.b₁_mem_E64 hF⟩, mem_fixV_zpowers_iff_apply.2 hb₁, rfl⟩)
  rw [eq_bot_iff]
  rintro g ⟨hgA, hgB⟩
  obtain ⟨w, hw, rfl⟩ := hfixG hgB
  have hwU : w ∈ commV (zpowers x) := (mem_commV_iff D hF hcomm hcube w).2 hgA
  have : w ∈ commV (zpowers x) ⊓ fixV (zpowers x) := ⟨hwU, hw⟩
  rw [hinf0, mem_bot] at this
  rw [this, map_one]
  exact one_mem _

end CFSG.CGT.Foote81L6.Normalizer
