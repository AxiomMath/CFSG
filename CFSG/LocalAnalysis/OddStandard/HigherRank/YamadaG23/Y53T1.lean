module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Dihed
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Cosets

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem closure_pair_eq_sup_zpowers {Γ : Type} [Group Γ] (a b : Γ) :
    closure ({a, b} : Set Γ) = zpowers a ⊔ zpowers b := by
  have h : ({a, b} : Set Γ) = {a} ∪ {b} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [h, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]

private theorem mem_zpowers_of_eq_one_or {Γ : Type} [Group Γ] {x h : Γ}
    (hh : h = 1 ∨ h = x) : h ∈ Subgroup.zpowers x := by
  rcases hh with h1 | hx
  · rw [h1]; exact Subgroup.one_mem _
  · rw [hx]; exact Subgroup.mem_zpowers x

private theorem mem_zpowers_of_map_mem {Γ Δ : Type} [Group Γ] [Group Δ] (φ : Γ ≃* Δ)
    {Y X : Γ} (h : φ X ∈ Subgroup.zpowers (φ Y)) : X ∈ Subgroup.zpowers Y := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← map_zpow] at hn
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, φ.injective hn⟩

private theorem d8_sq_aux : ∀ a b : DihedralGroup 4, a ^ 2 = 1 → b ^ 2 = 1 → a * b ≠ b * a →
    ∀ w : DihedralGroup 4, w ^ 2 = 1 ∨ w ^ 2 = (b * a) ^ 2 := by
  decide

private theorem d8_comm_aux : ∀ a b : DihedralGroup 4, a ^ 2 = 1 → b ^ 2 = 1 → a * b ≠ b * a →
    ∀ w v : DihedralGroup 4, ⁅w, v⁆ = 1 ∨ ⁅w, v⁆ = (b * a) ^ 2 := by
  decide

private theorem y5_t_d_not_comm {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    c.s.t * c.d ≠ c.d * c.s.t := by
  intro h
  have hz1 : c.s.fr.z = 1 := by
    have hd := y5_dtd hH
    have ht : c.d * c.s.t * c.d⁻¹ = c.s.t := by rw [← h]; group
    rw [ht] at hd
    have h' := congrArg (· * c.s.t⁻¹) hd
    simpa using h'.symm
  have hord := s3_z_order c.s (lfactsA_of_setting hH.hS hH.hZ c.s)
  rw [hz1, orderOf_one] at hord
  norm_num at hord

private theorem y5_dt_sq {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    (c.d * c.s.t) ^ 2 = c.s.fr.z := by
  have hd2 : c.d * c.d = 1 := by rw [← pow_two]; exact y5_d_sq c
  have ht2 : c.s.t * c.s.t = 1 := by
    rw [← pow_two]; simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
  have h := y5_dtd hH
  rw [pow_two]
  calc (c.d * c.s.t) * (c.d * c.s.t)
      = (c.d * c.s.t * c.d) * c.s.t := by group
    _ = (c.d * c.s.t * c.d⁻¹) * c.s.t := by rw [inv_eq_of_mul_eq_one_right hd2]
    _ = (c.s.fr.z * c.s.t) * c.s.t := by rw [h]
    _ = c.s.fr.z := by rw [mul_assoc, ht2, mul_one]

theorem y5_R_eq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.R = s.fr.S ⊔ zpowers s.t := by
  apply le_antisymm
  · intro r hr
    have hrM : r ∈ L ⊔ centIn s.H L := by
      have h := s3_R_eq s hH.hS
      rw [h] at hr
      exact hr.2
    rw [f3_centIn_H_L hH] at hrM
    obtain ⟨ℓ, hℓL, i, rfl⟩ := y5_mem_L_sup_t s hrM
    have htR : s.t ∈ s.R := s3_t_mem_R s
    have hℓR : ℓ ∈ s.R := by
      have : ℓ = (ℓ * s.t ^ i) * (s.t ^ i)⁻¹ := by group
      rw [this]
      exact s.R.mul_mem hr (s.R.inv_mem (s.R.zpow_mem htR i))
    have hℓS : ℓ ∈ s.fr.S := by
      rw [← s3_R_inf_L s]
      exact Subgroup.mem_inf.mpr ⟨hℓR, hℓL⟩
    exact Subgroup.mul_mem_sup hℓS (Subgroup.zpow_mem_zpowers s.t i)
  · exact sup_le s.S_le_R (Subgroup.zpowers_le.mpr (s3_t_mem_R s))

theorem y5_T_eq_R_g {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.s.T = c.s.R ⊔ zpowers c.g := by
  apply le_antisymm
  · intro x hx
    have hgT : c.g ∈ c.s.T := (c.g_spec hRT).1
    have hgR : c.g ∉ c.s.R := (c.g_spec hRT).2.1
    rcases y5_T_cosets hH x hx c.g hgT with hxR | hgR' | hxig
    · exact Subgroup.mem_sup_left hxR
    · exact absurd hgR' hgR
    · have hgmem : c.g ∈ c.s.R ⊔ zpowers c.g := Subgroup.mem_sup_right (Subgroup.mem_zpowers c.g)
      have hxmem : c.g * (x⁻¹ * c.g)⁻¹ ∈ c.s.R ⊔ zpowers c.g :=
        Subgroup.mul_mem _ hgmem (Subgroup.inv_mem _ (Subgroup.mem_sup_left hxig))
      have : c.g * (x⁻¹ * c.g)⁻¹ = x := by group
      rwa [this] at hxmem
  · exact sup_le c.s.R_le_T (Subgroup.zpowers_le.mpr (c.g_spec hRT).1)

theorem y5_T1_eq_S_C0 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R = c.s.T) :
    c.e.T₁ = c.s.fr.S ⊔ C0 c.e := by
  have hcd : C0 c.e = zpowers c.s.t ⊔ zpowers c.d := by
    rw [c.intro5.gen, closure_pair_eq_sup_zpowers]
  rw [hcd, y5_T1_eq hH, ← hRT, y5_R_eq hH]
  ac_rfl

theorem y5_T1_eq_Sg_C0 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.e.T₁ = (c.s.fr.S ⊔ zpowers c.g) ⊔ C0 c.e := by
  have hcd : C0 c.e = zpowers c.s.t ⊔ zpowers c.d := by
    rw [c.intro5.gen, closure_pair_eq_sup_zpowers]
  rw [hcd, y5_T1_eq hH, y5_T_eq_R_g hH hRT, y5_R_eq hH]
  ac_rfl

theorem y5_S_normal_T1 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    (c.s.fr.S.subgroupOf c.e.T₁).Normal :=
  hH.h32.2.1.2

theorem y5_Sg_le_T1 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.s.fr.S ⊔ zpowers c.g ≤ c.e.T₁ :=
  sup_le hH.h32.2.1.1 (Subgroup.zpowers_le.mpr (c.e.T_le (c.g_spec hRT).1))

theorem y5_Sg_normal_T1 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ((c.s.fr.S ⊔ zpowers c.g).subgroupOf c.e.T₁).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (y5_Sg_le_T1 hH hRT),
    y5_T1_eq_Sg_C0 hH hRT]
  apply sup_le
  · exact Subgroup.le_normalizer
  · have hSle : c.s.fr.S ≤ c.e.T₁ := hH.h32.2.1.1
    have hSnorm : (c.s.fr.S.subgroupOf c.e.T₁).Normal := hH.h32.2.1.2
    have hNS : C0 c.e ≤ Subgroup.normalizer (c.s.fr.S : Set G) :=
      inf_le_left.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mp hSnorm)
    have hcomm : c.d * c.g = c.g * c.d := by
      have h := (c.g_spec hRT).2.2.2.2
      calc c.d * c.g = (c.g * c.d * c.g⁻¹) * c.g := by rw [h]
        _ = c.g * c.d := by group
    have hcent : C0 c.e ≤ Subgroup.centralizer ({c.g} : Set G) := by
      rw [c.intro5.gen, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (s3_comm_t_of_mem_T c.s (c.g_spec hRT).1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hNg : C0 c.e ≤ Subgroup.normalizer (Subgroup.zpowers c.g : Set G) := by
      refine hcent.trans ?_
      rw [Subgroup.zpowers_eq_closure, ← Subgroup.normalizer_singleton]
      exact Subgroup.normalizer_le_normalizer_closure ({c.g} : Set G)
    exact (le_inf hNS hNg).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem y5_Z_normal_T1 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    (c.s.fr.Z.subgroupOf c.e.T₁).Normal := by
  have hZle : c.s.fr.Z ≤ c.e.T₁ := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr (hH.h32.2.1.1 (s3_A_le_S c.s (s3_z_mem_A c.s)))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZle, Subgroup.le_normalizer_iff]
  intro x hx w hw
  rw [SFrame.Z] at hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← conj_zpow, s3_conj_z c.s (lfactsA_of_setting hH.hS hH.hZ c.s) c.e hH.h32 hx]
  exact Subgroup.zpow_mem_zpowers c.s.fr.z n

theorem y5_C0_card (c : Ctx5 G L) : Nat.card ↥(C0 c.e) = 8 := by
  obtain ⟨φ⟩ := c.intro5.dihedral
  rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]

theorem y5_C0_inf_A {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : C0 c.e ⊓ c.s.fr.A = c.s.fr.Z := by
  have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC0, hxA⟩ := Subgroup.mem_inf.mp hx
    have hxcent : x ∈ Subgroup.centralizer (c.s.fr.A : Set G) := (Subgroup.mem_inf.mp hxC0).2
    have : x ∈ cen c.s.fr.A := Subgroup.mem_inf.mpr ⟨hxA, hxcent⟩
    rwa [hA.cen_A] at this
  · rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨s3_zt_le_C0 c.s hA c.e (Subgroup.subset_closure (by simp)), s3_z_mem_A c.s⟩)

theorem y5_C0_sq_Z {c : Ctx5 G L} (hH : F33Hyp c.s c.e) : ∀ x ∈ C0 c.e, x ^ 2 ∈ c.s.fr.Z := by
  have hz : (c.d * c.s.t) ^ 2 = c.s.fr.z := y5_dt_sq hH
  obtain ⟨φ⟩ := c.intro5.dihedral
  have hnc : c.s.t * c.d ≠ c.d * c.s.t := y5_t_d_not_comm hH
  have htC : c.s.t ∈ C0 c.e := by
    rw [c.intro5.gen]; exact Subgroup.subset_closure (by simp)
  have hdC : c.d ∈ C0 c.e := by
    rw [c.intro5.gen]; exact Subgroup.subset_closure (by simp)
  intro x hx
  let T : ↥(C0 c.e) := ⟨c.s.t, htC⟩
  let D : ↥(C0 c.e) := ⟨c.d, hdC⟩
  let X : ↥(C0 c.e) := ⟨x, hx⟩
  have hT2 : T ^ 2 = 1 := by
    apply Subtype.ext; show c.s.t ^ 2 = 1
    simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
  have hD2 : D ^ 2 = 1 := by
    apply Subtype.ext; show c.d ^ 2 = 1; exact y5_d_sq c
  have hnc' : φ T * φ D ≠ φ D * φ T := by
    intro h
    apply hnc
    have hTD : T * D = D * T := φ.injective (by rw [map_mul, map_mul, h])
    simpa [T, D] using congrArg Subtype.val hTD
  have hY : (φ D * φ T) ^ 2 = φ ((D * T) ^ 2) := by rw [map_pow, map_mul]
  have hYval : Subgroup.subtype (C0 c.e) ((D * T) ^ 2) = c.s.fr.z := by
    rw [map_pow, map_mul]
    exact hz
  have hmemsq : X ^ 2 ∈ Subgroup.zpowers ((D * T) ^ 2) := by
    refine mem_zpowers_of_map_mem φ (Y := (D * T) ^ 2) (X := X ^ 2) ?_
    have h := d8_sq_aux (φ T) (φ D) (by rw [← map_pow, hT2, map_one])
      (by rw [← map_pow, hD2, map_one]) hnc' (φ X)
    rw [hY, ← map_pow] at h
    exact mem_zpowers_of_eq_one_or h
  have hzpow : Subgroup.zpowers ((D * T) ^ 2) ≤
      (Subgroup.zpowers c.s.fr.z).comap (Subgroup.subtype (C0 c.e)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_comap, hYval]
    exact Subgroup.mem_zpowers c.s.fr.z
  have hx2 : ((X ^ 2 : ↥(C0 c.e)) : G) ∈ Subgroup.zpowers c.s.fr.z := hzpow hmemsq
  change x ^ 2 ∈ Subgroup.zpowers c.s.fr.z
  simpa [X] using hx2

theorem y5_C0_comm_Z {c : Ctx5 G L} (hH : F33Hyp c.s c.e) :
    ∀ x ∈ C0 c.e, ∀ y ∈ C0 c.e, ⁅x, y⁆ ∈ c.s.fr.Z := by
  have hz : (c.d * c.s.t) ^ 2 = c.s.fr.z := y5_dt_sq hH
  obtain ⟨φ⟩ := c.intro5.dihedral
  have hnc : c.s.t * c.d ≠ c.d * c.s.t := y5_t_d_not_comm hH
  have htC : c.s.t ∈ C0 c.e := by
    rw [c.intro5.gen]; exact Subgroup.subset_closure (by simp)
  have hdC : c.d ∈ C0 c.e := by
    rw [c.intro5.gen]; exact Subgroup.subset_closure (by simp)
  intro x hx y hy
  let T : ↥(C0 c.e) := ⟨c.s.t, htC⟩
  let D : ↥(C0 c.e) := ⟨c.d, hdC⟩
  let X : ↥(C0 c.e) := ⟨x, hx⟩
  let Y : ↥(C0 c.e) := ⟨y, hy⟩
  have hT2 : T ^ 2 = 1 := by
    apply Subtype.ext; show c.s.t ^ 2 = 1
    simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
  have hD2 : D ^ 2 = 1 := by
    apply Subtype.ext; show c.d ^ 2 = 1; exact y5_d_sq c
  have hnc' : φ T * φ D ≠ φ D * φ T := by
    intro h
    apply hnc
    have hTD : T * D = D * T := φ.injective (by rw [map_mul, map_mul, h])
    simpa [T, D] using congrArg Subtype.val hTD
  have hY : (φ D * φ T) ^ 2 = φ ((D * T) ^ 2) := by rw [map_pow, map_mul]
  have hYval : Subgroup.subtype (C0 c.e) ((D * T) ^ 2) = c.s.fr.z := by
    rw [map_pow, map_mul]
    exact hz
  have hmemcomm : ⁅X, Y⁆ ∈ Subgroup.zpowers ((D * T) ^ 2) := by
    refine mem_zpowers_of_map_mem φ (Y := (D * T) ^ 2) (X := ⁅X, Y⁆) ?_
    have h := d8_comm_aux (φ T) (φ D) (by rw [← map_pow, hT2, map_one])
      (by rw [← map_pow, hD2, map_one]) hnc' (φ X) (φ Y)
    rw [hY] at h
    have hφ : φ ⁅X, Y⁆ = ⁅φ X, φ Y⁆ := by
      simp only [commutatorElement_def, map_mul, map_inv]
    rw [hφ]
    exact mem_zpowers_of_eq_one_or h
  have hzpow : Subgroup.zpowers ((D * T) ^ 2) ≤
      (Subgroup.zpowers c.s.fr.z).comap (Subgroup.subtype (C0 c.e)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_comap, hYval]
    exact Subgroup.mem_zpowers c.s.fr.z
  have hxy : ((⁅X, Y⁆ : ↥(C0 c.e)) : G) ∈ Subgroup.zpowers c.s.fr.z := hzpow hmemcomm
  change ⁅x, y⁆ ∈ Subgroup.zpowers c.s.fr.z
  have hcoee : ((⁅X, Y⁆ : ↥(C0 c.e)) : G) = ⁅x, y⁆ := rfl
  rwa [hcoee] at hxy

end CFSG.OddStandard.HigherRank.YamadaG23
