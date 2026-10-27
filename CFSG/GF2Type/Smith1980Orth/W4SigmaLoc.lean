module

public import CFSG.GF2Type.Smith1980Orth.S2Coord
public import CFSG.GF2Type.Smith1980Orth.S2Lbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Pre

variable (D : S2Pre S)

theorem mem_V_iff {y : G} : y ∈ V S D.g D.t ↔ y ∈ S.QG ∧ S.cl y ∈ Vt S D.g D.t :=
  Iff.rfl

theorem V_comm {x y : G} (hx : x ∈ V S D.g D.t) (hy : y ∈ V S D.g D.t) : x * y = y * x :=
  (S.polar_cl_eq_zero_iff hx.1 hy.1).mp
    (polar_eq_zero_of_mem_Vt D.good.H D.good.ht1 hx.2 hy.2)

theorem V_mul_self {x : G} (hx : x ∈ V S D.g D.t) : x * x = 1 :=
  (sq x).symm.trans
    ((S.q_cl_eq_zero_iff hx.1).mp (q_eq_zero_of_mem_Vt D.good.H D.good.ht1 hx.2))

theorem a_mem_V : D.g * S.z * D.g⁻¹ ∈ V S D.g D.t :=
  ⟨D.good.H.conj_mem, cl_a_mem_Vt D.good.ht⟩

theorem card_V (hw : S.width = 4) : Nat.card (V S D.g D.t) = 32 := by
  change Nat.card (S.clPre (Vt S D.g D.t)) = 32
  rw [S.card_clPre, S.card_submodule, D.finrank_Vt, hw]
  norm_num

private theorem cases_of_mem_sup {s : S.O} (hs : s ∈ D.Obar ⊔ zpowers D.t) :
    s = 1 ∨ s = D.k ∨ s = D.k * D.k ∨ s = D.t ∨ s = D.k * D.t ∨ s = D.k * D.k * D.t := by
  rcases D.mem_Obar_sup_cases hs with h | h | h | h
  · rw [D.Obar_eq_zpowers] at h
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp h
    have hpow : D.k ^ n = D.k ^ (n % 3) := by simpa using zpow_eq_zpow_emod' n D.k_cube
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · exact Or.inl (by rw [hpow, h, zpow_zero])
    · exact Or.inr (Or.inl (by rw [hpow, h, zpow_one]))
    · exact Or.inr (Or.inr (Or.inl (by rw [hpow, h, zpow_two])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [h, pow_two])))))

private theorem apply_coord_zero_of_mem_sup {s : S.O} (hs : s ∈ D.Obar ⊔ zpowers D.t)
    (σ : Vt S D.g D.t) :
    ((s = 1 ∨ s = D.t) ∧ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, 0)) = D.coord (σ, 0)) ∨
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, 0)) = D.coord (0, σ) ∨
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, 0)) = D.coord (σ, σ) := by
  rcases D.cases_of_mem_sup hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨Or.inl rfl, rfl⟩
  · refine Or.inr (Or.inl ?_)
    rw [D.k_apply_coord, add_zero]
  · refine Or.inr (Or.inr ?_)
    rw [coe_mul_apply, D.k_apply_coord, D.k_apply_coord, add_zero, zero_add]
  · refine Or.inl ⟨Or.inr rfl, ?_⟩
    rw [D.t_apply_coord, add_zero]
  · refine Or.inr (Or.inl ?_)
    rw [coe_mul_apply, D.t_apply_coord, add_zero, D.k_apply_coord, add_zero]
  · refine Or.inr (Or.inr ?_)
    rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, add_zero, D.k_apply_coord, add_zero,
      D.k_apply_coord, zero_add]

theorem exists_pure_of_isConj {x : G} (hxQ : x ∈ S.QG) (hx : IsConj S.z x) (hxz : x ≠ S.z) :
    ∃ s : Vt S D.g D.t, s ≠ 0 ∧
      (S.cl x = D.coord (s, 0) ∨ S.cl x = D.coord (0, s) ∨ S.cl x = D.coord (s, s)) := by
  have hF : S6.FusionCtl S D.g := S6.fusionCtl_of_lemma_3_13 D.good.H D.good.noAll
  obtain ⟨k, hk⟩ := isConj_iff.mp hx
  obtain ⟨m, hm, hmx⟩ := hF k (hk ▸ hxQ) (hk ▸ hxz)
  have hcl : S.cl x = (S.ρ ⟨m, hm⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) := by
    rw [ρ_cl_conj_z S ⟨m, hm⟩ D.good.H.conj_mem]
    congr 1
    exact ((mul_conj_z S m D.g).trans (hmx.trans hk)).symm
  obtain ⟨s, hs, c, hc, hsc⟩ := D.exists_mul_Cbar
    (MonoidHom.mem_range.mpr ⟨⟨m, hm⟩, rfl⟩ : S.ρ ⟨m, hm⟩ ∈ S.Mbar)
  have hcaV : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) ∈ Vt S D.g D.t :=
    D.Cbar_apply_mem_Vt hc (cl_a_mem_Vt D.good.ht)
  obtain ⟨σ, hσ⟩ : ∃ σ : Vt S D.g D.t,
      (σ : S.Qt) = (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) := ⟨⟨_, hcaV⟩, rfl⟩
  have hσ0 : σ ≠ 0 := by
    intro h
    have h0 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) = 0 := by
      rw [← hσ]
      exact congrArg Subtype.val h
    exact cl_conj_z_ne_zero S D.good.H.conj_mem D.good.H.conj_ne
      ((LinearEquiv.map_eq_zero_iff _).mp h0)
  have hx' : S.cl x = (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, 0)) := by
    rw [hcl, hsc, coe_mul_apply, D.coord_apply_zero_right, hσ]
  refine ⟨σ, hσ0, ?_⟩
  rcases D.apply_coord_zero_of_mem_sup hs σ with ⟨-, h⟩ | h | h
  · exact Or.inl (hx'.trans h)
  · exact Or.inr (Or.inl (hx'.trans h))
  · exact Or.inr (Or.inr (hx'.trans h))

theorem eq_one_or_eq_t_of_fix_Vt {m : S.O} (hm : m ∈ S.Mbar)
    (hfix : ∀ u ∈ Vt S D.g D.t, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) : m = 1 ∨ m = D.t := by
  obtain ⟨s, hs, c, hc, rfl⟩ := D.exists_mul_Cbar hm
  have ha : S.cl (D.g * S.z * D.g⁻¹) ∈ Vt S D.g D.t := cl_a_mem_Vt D.good.ht
  have ha0 : aV D.good.ht ≠ 0 := aV_ne_zero D.good.H D.good.ht
  have hcaV : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) ∈ Vt S D.g D.t :=
    D.Cbar_apply_mem_Vt hc ha
  obtain ⟨σ, hσ⟩ : ∃ σ : Vt S D.g D.t,
      (σ : S.Qt) = (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (D.g * S.z * D.g⁻¹)) := ⟨⟨_, hcaV⟩, rfl⟩
  have hsσ : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, 0)) = D.coord (aV D.good.ht, 0) := by
    rw [D.coord_apply_zero_right, D.coord_apply_zero_right, hσ]
    exact hfix _ ha
  have hs' : s = 1 ∨ s = D.t := by
    rcases D.apply_coord_zero_of_mem_sup hs σ with ⟨h, -⟩ | h | h
    · exact h
    · exfalso
      rw [h] at hsσ
      exact ha0 (Prod.mk.inj (D.coord.injective hsσ)).1.symm
    · exfalso
      rw [h] at hsσ
      have h2 := Prod.mk.inj (D.coord.injective hsσ)
      exact ha0 (h2.1.symm.trans h2.2)
  have hc1 : c = 1 := by
    refine D.eq_of_apply_eq_of_mem_Vt hc (one_mem _) fun u hu => ?_
    have h1 := hfix u hu
    have hcu := D.Cbar_apply_mem_Vt hc hu
    rcases hs' with rfl | rfl
    · exact h1
    · rw [coe_mul_apply, D.t_apply_of_mem hcu] at h1
      exact h1
  subst hc1
  rcases hs' with rfl | rfl
  · exact Or.inl (mul_one _)
  · exact Or.inr (mul_one _)

theorem mem_V_of_comm {q : G} (hq : q ∈ S.QG) (hcomm : ∀ v ∈ V S D.g D.t, q * v = v * q) :
    q ∈ V S D.g D.t := by
  obtain ⟨⟨u', v'⟩, hq'⟩ : ∃ p : Vt S D.g D.t × Vt S D.g D.t, S.cl q = D.coord p :=
    ⟨D.coord.symm (S.cl q), (D.coord.apply_symm_apply _).symm⟩
  have hv' : v' = 0 := by
    refine D.betaV_nondegenerate.1 v' fun s => ?_
    obtain ⟨y, hyQ, hy⟩ := S.exists_cl (s : S.Qt)
    have hyV : y ∈ V S D.g D.t := ⟨hyQ, by rw [hy]; exact s.2⟩
    have h := (D.commute_iff_coord hq hyQ hq'
      (hy.trans (D.coord_apply_zero_right s).symm)).mp (hcomm y hyV)
    rwa [LinearMap.BilinForm.zero_right, zero_add] at h
  refine ⟨hq, ?_⟩
  rw [hq', hv']
  exact D.mem_Vt_iff_coord.mpr ⟨u', rfl⟩

theorem comm_of_ρ_eq_t {x : G} (hxM : x ∈ S.M) (hx : S.ρ ⟨x, hxM⟩ = D.t) (hxx : x * x = 1)
    {v : G} (hv : v ∈ V S D.g D.t) : x * v = v * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hcv : S.cl v ∈ CFSG.RankThree.OrthogonalInvolutions.commSpace
      (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [D.commSpace_eq]
    exact hv.2
  obtain ⟨wt, hwt⟩ := CFSG.RankThree.OrthogonalInvolutions.mem_commSpace.mp hcv
  obtain ⟨w, hwQ, hw⟩ := S.exists_cl wt
  have hxwQ : x * w * x⁻¹ ∈ S.QG := S.conj_mem_QG hxM hwQ
  have hcQ : x * w * x⁻¹ * w⁻¹ ∈ S.QG := S.QG.mul_mem hxwQ (S.QG.inv_mem hwQ)
  have h1 : S.cl (x * w * x⁻¹) = (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl w) := by
    have h := S.ρ_cl ⟨x, hxM⟩ hwQ
    rw [hx] at h
    exact h.symm
  have hcl : S.cl (x * w * x⁻¹ * w⁻¹) = S.cl v := by
    rw [S.cl_mul hxwQ (S.QG.inv_mem hwQ), S.cl_inv hwQ, h1, hw, ← hwt, ZModModule.sub_eq_add]
  obtain ⟨c, hc⟩ : ∃ c, c = x * w * x⁻¹ * w⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hcQ hcl
  have hcV : c ∈ V S D.g D.t := ⟨hcQ, by rw [hcl]; exact hv.2⟩
  have hcc : c * c = 1 := D.V_mul_self hcV
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    rw [hc, hxi]
    calc x * (x * w * x * w⁻¹) * x = (x * x) * (w * x * w⁻¹ * x) := by group
      _ = w * x * w⁻¹ * x := by rw [hxx, one_mul]
      _ = (x * w * x * w⁻¹)⁻¹ := by
        rw [show (x * w * x * w⁻¹)⁻¹ = w * x⁻¹ * w⁻¹ * x⁻¹ by group, hxi]
  have hxc' : x * c = c * x := by
    have h2 : x * c * x⁻¹ = c := hxc.trans (inv_eq_of_mul_eq_one_right hcc)
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h2]
  rcases (S.cl_eq_cl_iff hcQ hv.1).mp hcl with h | h
  · rw [h]
    exact hxc'
  · rw [h, ← mul_assoc, hxc', mul_assoc, S.z_comm hxM, ← mul_assoc]

theorem exists_cl_comm_eq {x : G} (hxM : x ∈ S.M) (hx : S.ρ ⟨x, hxM⟩ = D.t) {v : G}
    (hv : v ∈ V S D.g D.t) : ∃ q ∈ S.QG, S.cl (q * x * q⁻¹ * x⁻¹) = S.cl v := by
  obtain ⟨s, hs⟩ : ∃ s : Vt S D.g D.t, (s : S.Qt) = S.cl v := ⟨⟨_, hv.2⟩, rfl⟩
  obtain ⟨q, hqQ, hq⟩ := S.exists_cl (D.coord (0, s))
  refine ⟨q, hqQ, ?_⟩
  have hxqQ : x * q⁻¹ * x⁻¹ ∈ S.QG := S.conj_mem_QG hxM (S.QG.inv_mem hqQ)
  have h1 : S.cl (x * q⁻¹ * x⁻¹) = (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) := by
    have h := S.ρ_cl ⟨x, hxM⟩ (S.QG.inv_mem hqQ)
    rw [hx, S.cl_inv hqQ] at h
    exact h.symm
  have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
  have e2 : D.coord (0, s) + D.coord (0 + s, s) = D.coord (s, 0) := by
    rw [← map_add]
    congr 1
    exact Prod.ext (by simp) (ZModModule.add_self s)
  rw [e, S.cl_mul hqQ hxqQ, h1, hq, D.t_apply_coord, e2, D.coord_apply_zero_right, hs]

theorem exists_comm_iff (φ : Vt S D.g D.t →ₗ[ZMod 2] ZMod 2) :
    ∃ q ∈ S.QG, ∀ (y : G) (hy : y ∈ V S D.g D.t),
      q * y = y * q ↔ φ ⟨S.cl y, ((D.mem_V_iff).mp hy).2⟩ = 0 := by
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Vt S D.g D.t, ∀ y, D.betaV s₀ y = φ y :=
    ⟨(D.betaV.toDual D.betaV_nondegenerate).symm φ, fun y =>
      LinearMap.BilinForm.apply_toDual_symm_apply φ y⟩
  obtain ⟨q, hqQ, hq⟩ := S.exists_cl (D.coord (0, s₀))
  refine ⟨q, hqQ, fun y hy => ?_⟩
  have hyc : S.cl y = D.coord (⟨S.cl y, ((D.mem_V_iff).mp hy).2⟩, 0) :=
    (D.coord_apply_zero_right (⟨S.cl y, ((D.mem_V_iff).mp hy).2⟩ : Vt S D.g D.t)).symm
  rw [D.commute_iff_coord hqQ hy.1 hq hyc, hs₀, LinearMap.BilinForm.zero_left, zero_add]

private theorem conj_mem_V_of_mem_Rbar {m : G} (hm : m ∈ S.M)
    (hr : S.ρ ⟨m, hm⟩ ∈ Rbar S D.g D.t) {y : G} (hy : y ∈ V S D.g D.t) :
    m * y * m⁻¹ ∈ V S D.g D.t := by
  refine ⟨S.conj_mem_QG hm hy.1, ?_⟩
  have h := apply_mem_Vt_of_mem_Rbar D.good.H.conj_mem hr hy.2
  rw [S.ρ_cl ⟨m, hm⟩ hy.1] at h
  exact h

private theorem mem_normalizer_V_of_mem_Rbar {m : G} (hm : m ∈ S.M)
    (hr : S.ρ ⟨m, hm⟩ ∈ Rbar S D.g D.t) : m ∈ normalizer (V S D.g D.t : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => D.conj_mem_V_of_mem_Rbar hm hr hy, fun hy => ?_⟩
  have hm' : m⁻¹ ∈ S.M := S.M.inv_mem hm
  have hr' : S.ρ ⟨m⁻¹, hm'⟩ ∈ Rbar S D.g D.t := by
    have e : (⟨m⁻¹, hm'⟩ : S.M) = (⟨m, hm⟩ : S.M)⁻¹ := rfl
    rw [e, map_inv]
    exact inv_mem hr
  have h := D.conj_mem_V_of_mem_Rbar hm' hr' hy
  have e : m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y := by group
  rwa [e] at h

theorem isConj_of_mem_V (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ)
    {v : G} (hv : v ∈ V S D.g D.t) (hv1 : v ≠ 1) : IsConj S.z v := by
  by_cases hvz : v = S.z
  · rw [hvz]
  have hcl0 : S.cl v ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hv.1).mp h with h | h
    · exact hv1 h
    · exact hvz h
  obtain ⟨e, he, hea⟩ := hP.transitive ⟨S.cl v, hv.2⟩ fun h => hcl0 (congrArg Subtype.val h)
  obtain ⟨r, hr, her⟩ := mem_RmodN.mp he
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  have hcl : S.cl v = S.cl ((m : G) * D.g * S.z * ((m : G) * D.g)⁻¹) := by
    have h := her (aV D.good.ht)
    rw [hea] at h
    exact h.trans (ρ_cl_conj_z S m D.good.H.conj_mem)
  have hbQ : (m : G) * D.g * S.z * ((m : G) * D.g)⁻¹ ∈ S.QG :=
    conj_mem_QG' S m.2 D.good.H.conj_mem
  have hbz : (m : G) * D.g * S.z * ((m : G) * D.g)⁻¹ ≠ S.z :=
    conj_ne_z' S m.2 D.good.H.conj_ne
  have hb1 : (m : G) * D.g * S.z * ((m : G) * D.g)⁻¹ ≠ 1 := conj_z_ne_one S _
  rcases (S.cl_eq_cl_iff hbQ hv.1).mp hcl.symm with h | h
  · exact isConj_iff.mpr ⟨(m : G) * D.g, h.symm⟩
  · obtain ⟨u, -, hu⟩ := S.exists_conj_eq_mul_z hbQ hb1 hbz
    refine isConj_iff.mpr ⟨u * ((m : G) * D.g), ?_⟩
    rw [h, ← hu]
    group

theorem exists_conj_eq_of_mem_V
    (hP : PGL25Case D.good.H D.good.C D.good.ht D.good.ht1 D.good.hVQ) {v w : G}
    (hv : v ∈ V S D.g D.t) (hw : w ∈ V S D.g D.t) (hv1 : v ≠ 1) (hvz : v ≠ S.z) (hw1 : w ≠ 1)
    (hwz : w ≠ S.z) :
    ∃ m ∈ S.M, m ∈ normalizer (V S D.g D.t : Set G) ∧ m * v * m⁻¹ = w := by
  have hcl0 : ∀ {y : G}, y ∈ V S D.g D.t → y ≠ 1 → y ≠ S.z → S.cl y ≠ 0 := fun hy hy1 hyz h => by
    rcases (S.cl_eq_zero_iff hy.1).mp h with h | h
    · exact hy1 h
    · exact hyz h
  obtain ⟨e₁, he₁, h₁⟩ := hP.transitive ⟨S.cl v, hv.2⟩
    fun h => hcl0 hv hv1 hvz (congrArg Subtype.val h)
  obtain ⟨e₂, he₂, h₂⟩ := hP.transitive ⟨S.cl w, hw.2⟩
    fun h => hcl0 hw hw1 hwz (congrArg Subtype.val h)
  have he : e₂ * e₁⁻¹ ∈ RmodN S D.g D.t := mul_mem he₂ (inv_mem he₁)
  have hevw : (e₂ * e₁⁻¹) ⟨S.cl v, hv.2⟩ = ⟨S.cl w, hw.2⟩ := by
    rw [LinearEquiv.mul_apply, ← h₁, show e₁⁻¹ (e₁ (aV D.good.ht)) = aV D.good.ht from
      e₁.symm_apply_apply _, h₂]
  obtain ⟨r, hr, her⟩ := mem_RmodN.mp he
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar hr)
  have hcl : S.cl w = S.cl ((m : G) * v * (m : G)⁻¹) := by
    have h := her ⟨S.cl v, hv.2⟩
    rw [hevw] at h
    exact h.trans (S.ρ_cl m hv.1)
  have hbQ : (m : G) * v * (m : G)⁻¹ ∈ S.QG := S.conj_mem_QG m.2 hv.1
  have hb0 : S.cl ((m : G) * v * (m : G)⁻¹) ≠ 0 := by
    rw [← hcl]
    exact hcl0 hw hw1 hwz
  have hb1 : (m : G) * v * (m : G)⁻¹ ≠ 1 := fun h =>
    hb0 ((S.cl_eq_zero_iff hbQ).mpr (Or.inl h))
  have hbz : (m : G) * v * (m : G)⁻¹ ≠ S.z := fun h =>
    hb0 ((S.cl_eq_zero_iff hbQ).mpr (Or.inr h))
  have hmN : (m : G) ∈ normalizer (V S D.g D.t : Set G) :=
    D.mem_normalizer_V_of_mem_Rbar m.2 hr
  rcases (S.cl_eq_cl_iff hbQ hw.1).mp hcl.symm with h | h
  · exact ⟨m, m.2, hmN, h.symm⟩
  · obtain ⟨u, huQ, hu⟩ := S.exists_conj_eq_mul_z hbQ hb1 hbz
    have huM : u ∈ S.M := S.QG_le_M huQ
    have huN : u ∈ normalizer (V S D.g D.t : Set G) :=
      D.mem_normalizer_V_of_mem_Rbar huM
        (by rw [(S.ρ_eq_one_iff ⟨u, huM⟩).mpr huQ]; exact one_mem _)
    refine ⟨u * m, S.M.mul_mem huM m.2, mul_mem huN hmN, ?_⟩
    rw [h, ← hu]
    group

end S2Pre

end CFSG.GF2Type.Smith1980Orth
