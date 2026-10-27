module

public import CFSG.GF2Type.Smith1980Orth.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Pre

section Linear

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem two_le_finrank_of_ne {U : Submodule (ZMod 2) V} {a b : V} (ha : a ∈ U)
    (hb : b ∈ U) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) : 2 ≤ finrank (ZMod 2) U := by
  by_contra h
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp (by omega : finrank (ZMod 2) U ≤ 1)
  obtain ⟨c₁, h₁⟩ := hv ⟨a, ha⟩
  obtain ⟨c₂, h₂⟩ := hv ⟨b, hb⟩
  have key : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases key c₁ with rfl | rfl
  · exact ha0 (by simpa using (congrArg Subtype.val h₁).symm)
  rcases key c₂ with rfl | rfl
  · exact hb0 (by simpa using (congrArg Subtype.val h₂).symm)
  exact hab (by simpa using (congrArg Subtype.val h₁).symm.trans (congrArg Subtype.val h₂))

private theorem finrank_map_of_injOn {A : Submodule (ZMod 2) V} (f : V →ₗ[ZMod 2] V)
    (hf : ∀ u ∈ A, f u = 0 → u = 0) : finrank (ZMod 2) (A.map f) = finrank (ZMod 2) A := by
  have hinj : Function.Injective (f.domRestrict A) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    exact Subtype.ext (hf u u.2 hu)
  rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]

private theorem finrank_le_finrank_commSpace {A B : Submodule (ZMod 2) V}
    (y : V ≃ₗ[ZMod 2] V) (hAB : Disjoint A B) (hy : ∀ u ∈ A, y u ∈ B) :
    finrank (ZMod 2) A ≤ finrank (ZMod 2) (commSpace y) := by
  set f : V →ₗ[ZMod 2] V := LinearMap.id + (y : V →ₗ[ZMod 2] V)
  have hfu : ∀ u, f u = u + y u := fun u => rfl
  have hinj : ∀ u ∈ A, f u = 0 → u = 0 := by
    intro u hu h0
    rw [hfu] at h0
    have hB : u ∈ B := by
      rw [eq_neg_of_add_eq_zero_left h0]
      exact B.neg_mem (hy u hu)
    exact Submodule.disjoint_def.mp hAB u hu hB
  have hle : A.map f ≤ commSpace y := by
    rintro _ ⟨u, hu, rfl⟩
    refine mem_commSpace.mpr ⟨u, ?_⟩
    rw [hfu, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
  calc finrank (ZMod 2) A = finrank (ZMod 2) (A.map f) := (finrank_map_of_injOn f hinj).symm
    _ ≤ finrank (ZMod 2) (commSpace y) := Submodule.finrank_mono hle

end Linear

variable {M1 : Subgroup S.O} (D : S2Pre S M1)

@[expose] noncomputable def Wk : Submodule (ZMod 2) S.Qt :=
  (Vt S D.g D.t).map ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)

@[expose] noncomputable def Wkt : Submodule (ZMod 2) S.Qt :=
  D.Wk.map ((D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)

theorem mem_Wk_iff {x : S.Qt} :
    x ∈ D.Wk ↔ ∃ v ∈ Vt S D.g D.t, (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = x :=
  Submodule.mem_map

theorem mem_Wkt_iff {x : S.Qt} :
    x ∈ D.Wkt ↔ ∃ w ∈ D.Wk, (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = x :=
  Submodule.mem_map

theorem k_apply_mem_Wk {v : S.Qt} (hv : v ∈ Vt S D.g D.t) :
    (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ D.Wk :=
  Submodule.mem_map_of_mem hv

private theorem t_k_apply_Vt {v : S.Qt} (hv : v ∈ Vt S D.g D.t) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      ((D.k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
  rw [D.t_k_apply, D.t_apply_of_mem hv]

private theorem k_sq_eq_inv : D.k ^ 2 = D.k⁻¹ :=
  (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact D.k_cube)).symm

private theorem k_k_k_apply (v : S.Qt) :
    (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) =
      v := by
  have h : ((D.k ^ 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    rw [D.k_cube]
    rfl
  rwa [pow_three, coe_mul_apply, coe_mul_apply] at h

theorem t_apply_mem_Wkt {x : S.Qt} (hx : x ∈ D.Wk) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ D.Wkt :=
  Submodule.mem_map_of_mem hx

theorem Wkt_eq : D.Wkt = (Vt S D.g D.t).map
    (((D.k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
  ext x
  rw [D.mem_Wkt_iff, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv, rfl⟩ := D.mem_Wk_iff.mp hw
    exact ⟨v, hv, (D.t_k_apply_Vt hv).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, D.k_apply_mem_Wk hv, D.t_k_apply_Vt hv⟩

theorem mem_Wkt_iff_inv {x : S.Qt} :
    x ∈ D.Wkt ↔ ∃ v ∈ Vt S D.g D.t, ((D.k⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = x := by
  rw [D.Wkt_eq]
  exact Submodule.mem_map

theorem k_apply_mem_Wkt {x : S.Qt} (hx : x ∈ D.Wk) :
    (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ D.Wkt := by
  obtain ⟨v, hv, rfl⟩ := D.mem_Wk_iff.mp hx
  refine D.mem_Wkt_iff_inv.mpr ⟨v, hv, ?_⟩
  rw [← D.k_sq_eq_inv, pow_two, coe_mul_apply]

theorem finrank_Wk : finrank (ZMod 2) D.Wk = S.width := by
  rw [Wk, LinearEquiv.finrank_map_eq, D.finrank_Vt]

theorem finrank_Wkt : finrank (ZMod 2) D.Wkt = S.width := by
  rw [Wkt, LinearEquiv.finrank_map_eq, D.finrank_Wk]

theorem disjoint_Vt_Wk : Disjoint (Vt S D.g D.t) D.Wk := by
  rw [Submodule.disjoint_def]
  intro x hxV hxW
  obtain ⟨v, hv, rfl⟩ := D.mem_Wk_iff.mp hxW
  rw [D.eq_zero_of_k_apply_mem hv hxV, map_zero]

theorem disjoint_Wk_Wkt : Disjoint D.Wk D.Wkt := by
  rw [Submodule.disjoint_def]
  intro x hxW hxW'
  obtain ⟨v, hv, rfl⟩ := D.mem_Wk_iff.mp hxW
  obtain ⟨v', hv', he⟩ := D.mem_Wkt_iff_inv.mp hxW'
  have h1 : v' = (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
    rw [← he, apply_inv_apply_O]
  have h2 : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) v' = v := by
    rw [h1]
    exact D.k_k_k_apply v
  have h0 : v' = 0 := D.eq_zero_of_k_apply_mem hv' (h2 ▸ hv)
  rw [← he, h0, map_zero]

theorem disjoint_Vt_Wkt : Disjoint (Vt S D.g D.t) D.Wkt := by
  rw [Submodule.disjoint_def]
  intro x hxV hxW
  obtain ⟨v, hv, rfl⟩ := D.mem_Wkt_iff_inv.mp hxW
  exact D.eq_zero_of_k_apply_mem hxV (by rwa [apply_inv_apply_O])

theorem isCompl_Vt_Wk : IsCompl (Vt S D.g D.t) D.Wk :=
  (Submodule.isCompl_iff_disjoint _ _ (by
    rw [S.finrank_Qt_eq_two_mul_width, D.finrank_Vt, D.finrank_Wk]; omega)).mpr D.disjoint_Vt_Wk

private theorem comm_apply_O {c d : S.O} (h : c * d = d * c) (v : S.Qt) :
    (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((d : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (d : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
  rw [← coe_mul_apply, ← coe_mul_apply, h]

theorem apply_mem_Vt {c : S.O} (hct : c * D.t = D.t * c) {v : S.Qt}
    (hv : v ∈ Vt S D.g D.t) : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S D.g D.t := by
  rw [← D.fixSpace_eq, mem_fixSpace] at hv ⊢
  rw [← comm_apply_O hct, hv]

theorem apply_mem_Wk {c : S.O} (hct : c * D.t = D.t * c) (hck : c * D.k = D.k * c) {x : S.Qt}
    (hx : x ∈ D.Wk) : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ D.Wk := by
  obtain ⟨v, hv, rfl⟩ := D.mem_Wk_iff.mp hx
  rw [comm_apply_O hck]
  exact D.k_apply_mem_Wk (D.apply_mem_Vt hct hv)

theorem Cbar_comm_k {c : S.O} (hc : c ∈ D.Cbar) : c * D.k = D.k * c :=
  (mem_centralizer_iff.mp hc.2 D.k (mem_sup_left D.k_mem_Obar)).symm

theorem Cbar_apply_mem_Vt {c : S.O} (hc : c ∈ D.Cbar) {v : S.Qt}
    (hv : v ∈ Vt S D.g D.t) : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S D.g D.t :=
  D.apply_mem_Vt (D.comm_of_mem_Cbar hc) hv

theorem two_le_finrank_commSpace_of_comm {c : S.O} (hck : c * D.k = D.k * c) (hc1 : c ≠ 1) :
    2 ≤ finrank (ZMod 2) (commSpace (c : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  obtain ⟨u, hcu⟩ : ∃ u, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ u := by
    by_contra hall
    push Not at hall
    exact hc1 (Subtype.ext (LinearEquiv.ext fun x => hall x))
  have hv0 : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ≠ 0 := sub_ne_zero.mpr hcu
  have hkv : (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) =
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
        (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by
    rw [map_sub, comm_apply_O hck]
  refine two_le_finrank_of_ne (a := (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u)
    (b := (D.k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u))
    (sub_mem_commSpace _ _) (by rw [hkv]; exact sub_mem_commSpace _ _) hv0 ?_ ?_
  · intro h
    exact hv0 ((D.k : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp h)
  · intro h
    exact hv0 (D.k_fix_eq_zero _ h.symm)

open scoped Pointwise in
theorem mem_Obar_sup_cases {s : S.O} (hs : s ∈ D.Obar ⊔ zpowers D.t) :
    s ∈ D.Obar ∨ s = D.t ∨ s = D.k * D.t ∨ s = D.k ^ 2 * D.t := by
  have hle : zpowers D.t ≤ normalizer (D.Obar : Set S.O) :=
    zpowers_le.mpr (S4.mem_normalizer_of_conj_le fun p hp =>
      D.conj_mem_Obar_of_mem_M1 D.t_mem_M1 hp)
  have hs' : s ∈ (D.Obar : Set S.O) * (zpowers D.t : Set S.O) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hs
  obtain ⟨o, ho, m, hm, rfl⟩ := Set.mem_mul.mp hs'
  rcases (Setting.mem_zpowers_iff_of_mul_self D.t_mul_t).mp hm with rfl | rfl
  · left
    rw [mul_one]
    exact ho
  · rw [D.Obar_eq_zpowers] at ho
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ho
    have hpow : D.k ^ n = D.k ^ (n % 3) := by simpa using zpow_eq_zpow_emod' n D.k_cube
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · right; left
      rw [hpow, h, zpow_zero, one_mul]
    · right; right; left
      rw [hpow, h, zpow_one]
    · right; right; right
      rw [hpow, h]
      norm_num

end S2Pre

section Full

namespace S2Pre

variable (D : S2Pre S)

include D in
theorem two_le_finrank_commSpace_of_ne_one {y : S.O}
    (hy : y ∈ S.Mbar) (hy1 : y ≠ 1) :
    2 ≤ finrank (ZMod 2) (commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  obtain ⟨s, hs, c, hc, rfl⟩ := D.exists_mul_Cbar hy
  have hct := D.comm_of_mem_Cbar hc
  have hck := D.Cbar_comm_k hc
  have h8 := D.four_le
  rcases D.mem_Obar_sup_cases hs with hso | rfl | rfl | rfl
  ·
    rw [D.Obar_eq_zpowers] at hso
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hso
    refine D.two_le_finrank_commSpace_of_comm ?_ hy1
    rw [mul_assoc, hck, ← mul_assoc, ((Commute.refl D.k).zpow_left n).eq, mul_assoc]
  ·
    have h := finrank_le_finrank_commSpace ((D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      D.disjoint_Wk_Wkt (by
        intro u hu
        rw [coe_mul_apply]
        exact D.t_apply_mem_Wkt (D.apply_mem_Wk hct hck hu))
    rw [D.finrank_Wk] at h
    omega
  ·
    have h := finrank_le_finrank_commSpace ((D.k * D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      D.disjoint_Vt_Wk (by
        intro u hu
        simp only [coe_mul_apply]
        rw [D.t_apply_of_mem (D.apply_mem_Vt hct hu)]
        exact D.k_apply_mem_Wk (D.apply_mem_Vt hct hu))
    rw [D.finrank_Vt] at h
    omega
  ·
    have h := finrank_le_finrank_commSpace ((D.k ^ 2 * D.t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
      D.disjoint_Vt_Wkt (by
        intro u hu
        simp only [pow_two, coe_mul_apply]
        rw [D.t_apply_of_mem (D.apply_mem_Vt hct hu)]
        exact D.k_apply_mem_Wkt (D.k_apply_mem_Wk (D.apply_mem_Vt hct hu)))
    rw [D.finrank_Vt] at h
    omega

include D in
theorem two_le_finrank_commSpace {y : S.O} (hy : y ∈ S.Mbar)
    (_hy2 : y * y = 1) (hy1 : y ≠ 1) :
    2 ≤ finrank (ZMod 2) (commSpace (y : S.Qt ≃ₗ[ZMod 2] S.Qt)) :=
  D.two_le_finrank_commSpace_of_ne_one hy hy1

end S2Pre

end Full

end CFSG.GF2Type.Smith1980Orth
