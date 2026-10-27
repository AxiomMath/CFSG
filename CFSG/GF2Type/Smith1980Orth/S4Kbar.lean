module

public import CFSG.GF2Type.Smith1980Orth.S3ThmAHalf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

private theorem sub_mem_of_add {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {P : Submodule (ZMod 2) V} {u a : V} (h1 : u - a ∈ P) (h2 : u ∈ P) : a ∈ P := by
  have := P.sub_mem h2 h1
  rwa [sub_sub_cancel] at this

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable (D : S2Data S)

local notation "ρV" => D.resC

theorem coord_mem_fixSpace_Cbar_iff (c : D.Cbar) (u w : Vt S D.g D.t) :
    D.coord (u, w) ∈ fixSpace ((c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ↔
      u ∈ fixSpace (ρV c) ∧ w ∈ fixSpace (ρV c) := by
  rw [mem_fixSpace, D.Cbar_apply_coord, mem_fixSpace, mem_fixSpace]
  constructor
  · intro h
    exact Prod.mk.inj (D.coord.injective h)
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

private theorem coord_sub_coord (u w u' w' : Vt S D.g D.t) :
    D.coord (u, w) - D.coord (u', w') = D.coord (u - u', w - w') := by
  rw [← map_sub]
  rfl

theorem eq_one_of_sub_mem {P : Submodule (ZMod 2) (Vt S D.g D.t)} {s : S.O}
    (hs : s ∈ D.Obar ⊔ zpowers D.t) (c' : D.Cbar) {a₀ : Vt S D.g D.t} (ha₀ : a₀ ∉ P)
    (h1 : ∃ p q : Vt S D.g D.t, p ∈ P ∧ q ∈ P ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (ρV c' a₀, 0)) - D.coord (a₀, 0) = D.coord (p, q))
    (h2 : ∃ p q : Vt S D.g D.t, p ∈ P ∧ q ∈ P ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, ρV c' a₀)) - D.coord (0, a₀) = D.coord (p, q)) :
    s = 1 := by
  obtain ⟨p, q, hp, hq, e1⟩ := h1
  obtain ⟨p', q', hp', hq', e2⟩ := h2
  set u := ρV c' a₀ with hu
  have hn : (0 : Vt S D.g D.t) - a₀ = a₀ := by rw [zero_sub, neg_vec_eq (K := ZMod 2)]
  have hkk : ∀ x y : Vt S D.g D.t,
      ((D.k * D.k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (x, y)) = D.coord (x + y, x) := by
    intro x y
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, D.k_apply_coord, D.k_apply_coord]
    congr 1
    refine Prod.ext rfl ?_
    show y + (x + y) = x
    rw [add_comm y, add_assoc, add_self_vec (K := ZMod 2), add_zero]
  have hcaseA : D.coord (0, u) - D.coord (a₀, 0) = D.coord (p, q) → False := fun e => by
    rw [coord_sub_coord, hn] at e
    have h := (Prod.mk.inj (D.coord.injective e)).1
    exact ha₀ (by rw [h]; exact hp)
  have hcaseB : D.coord (u, u) - D.coord (a₀, 0) = D.coord (p, q) → False := fun e => by
    rw [coord_sub_coord, sub_zero] at e
    obtain ⟨h1, h2⟩ := Prod.mk.inj (D.coord.injective e)
    exact ha₀ (sub_mem_of_add (by rw [h1]; exact hp) (by rw [h2]; exact hq))
  rcases D.mem_sup_cases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exfalso
    rw [D.k_apply_coord, add_zero] at e1
    exact hcaseA e1
  · exfalso
    rw [hkk, add_zero] at e1
    exact hcaseB e1
  ·
    exfalso
    rw [D.t_apply_coord, zero_add, coord_sub_coord, sub_zero] at e2
    obtain ⟨h1, h2⟩ := Prod.mk.inj (D.coord.injective e2)
    exact ha₀ (sub_mem_of_add (by rw [h2]; exact hq') (by rw [h1]; exact hp'))
  · exfalso
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, D.t_apply_coord, add_zero, D.k_apply_coord,
      add_zero] at e1
    exact hcaseA e1
  · exfalso
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, D.t_apply_coord, add_zero, hkk, add_zero] at e1
    exact hcaseB e1

theorem sub_mem_of_mem_Lbar {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hxC : S.ρ ⟨_, hxM⟩ ∈ D.Cbar)
    (hfix : S.fixQt (k * S.z * k⁻¹) = S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)))
    (hΔ : S.clSub (S.QG ⊓ S.Qa k) ≤ S.commQt (k * S.z * k⁻¹)) {m : S.M}
    (hmL : (m : G) ∈ S.L0 k) {ℓ : S.O} (hmℓ : S.ρ m = ℓ) :
    ∀ u w : Vt S D.g D.t, u ∈ fixSpace (ρV ⟨_, hxC⟩) → w ∈ fixSpace (ρV ⟨_, hxC⟩) →
      ∃ p q : Vt S D.g D.t, p ∈ commSpace (ρV ⟨_, hxC⟩) ∧ q ∈ commSpace (ρV ⟨_, hxC⟩) ∧
        (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, w)) - D.coord (u, w) = D.coord (p, q) := by
  intro u w hu hw
  have hv : D.coord (u, w) ∈ S.fixQt (k * S.z * k⁻¹) := by
    rw [S.fixQt_of_mem hxM]
    exact (D.coord_mem_fixSpace_Cbar_iff ⟨_, hxC⟩ u w).mpr ⟨hu, hw⟩
  rw [hfix] at hv
  obtain ⟨y, hy, hyQ, hycl⟩ := S.mem_clSub_iff.mp hv
  have hc := SMK.commutator_mem_Dl S hmL hy
  have hmem : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, w)) - D.coord (u, w) ∈
      S.commQt (k * S.z * k⁻¹) := by
    rw [← hycl, ← hmℓ, ← S.cl_commutator m.2 hyQ]
    exact hΔ (S.cl_mem_clSub hc hc.1)
  rw [S.commQt_of_mem hxM] at hmem
  obtain ⟨p, q, hp, hq, e⟩ := (D.mem_commSpace_iff_coord_of_mem_Cbar hxC).mp hmem
  exact ⟨p, q, hp, hq, e⟩

theorem lbar_mem_Cbar {k : G} (hxM : k * S.z * k⁻¹ ∈ S.M)
    (hxC : S.ρ ⟨_, hxM⟩ ∈ D.Cbar)
    (hfix : S.fixQt (k * S.z * k⁻¹) = S.clSub (S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)))
    (hΔ : S.clSub (S.QG ⊓ S.Qa k) ≤ S.commQt (k * S.z * k⁻¹))
    {a₀ : Vt S D.g D.t} (ha₀ : a₀ ∈ fixSpace (ρV ⟨_, hxC⟩))
    (ha₀P : a₀ ∉ commSpace (ρV ⟨_, hxC⟩)) :
    ∀ ℓ ∈ S.Lbar k, ∃ hℓ : ℓ ∈ D.Cbar,
      ∀ a ∈ fixSpace (ρV ⟨_, hxC⟩), ρV ⟨ℓ, hℓ⟩ a - a ∈ commSpace (ρV ⟨_, hxC⟩) := by
  intro ℓ hℓL
  obtain ⟨m, hm, hmℓ⟩ := hℓL
  have hmL : (m : G) ∈ S.L0 k := mem_subgroupOf.mp hm
  have hkey := D.sub_mem_of_mem_Lbar hxM hxC hfix hΔ hmL hmℓ
  have hℓM : ℓ ∈ S.Mbar := ⟨m, hmℓ⟩
  obtain ⟨s, hs, c', hc', e⟩ := D.exists_mul_Cbar hℓM
  have hρ : ∀ v, (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c' : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := fun v => by
    rw [e, Subgroup.coe_mul, LinearEquiv.mul_apply]
  have hc'c : ∀ u w : Vt S D.g D.t, (c' : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (u, w)) =
      D.coord (ρV ⟨c', hc'⟩ u, ρV ⟨c', hc'⟩ w) := fun u w => D.Cbar_apply_coord ⟨c', hc'⟩ u w
  have hs1 : s = 1 := by
    refine D.eq_one_of_sub_mem hs ⟨c', hc'⟩ ha₀P ?_ ?_
    · obtain ⟨p, q, hp, hq, e1⟩ := hkey a₀ 0 ha₀ (Submodule.zero_mem _)
      refine ⟨p, q, hp, hq, ?_⟩
      have h3 := hc'c a₀ 0
      rw [map_zero] at h3
      rw [← h3, ← hρ]
      exact e1
    · obtain ⟨p, q, hp, hq, e1⟩ := hkey 0 a₀ (Submodule.zero_mem _) ha₀
      refine ⟨p, q, hp, hq, ?_⟩
      have h3 := hc'c 0 a₀
      rw [map_zero] at h3
      rw [← h3, ← hρ]
      exact e1
  have hℓc : ℓ = c' := by rw [e, hs1, one_mul]
  have hℓC : ℓ ∈ D.Cbar := hℓc ▸ hc'
  refine ⟨hℓC, fun a ha => ?_⟩
  obtain ⟨p, q, hp, -, hpq⟩ := hkey a 0 ha (Submodule.zero_mem _)
  have h4 : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (a, 0)) =
      D.coord (ρV ⟨ℓ, hℓC⟩ a, ρV ⟨ℓ, hℓC⟩ 0) := D.Cbar_apply_coord ⟨ℓ, hℓC⟩ a 0
  rw [h4, map_zero, coord_sub_coord, sub_zero] at hpq
  rw [(Prod.mk.inj (D.coord.injective hpq)).1]
  exact hp

end S2Data

end CFSG.GF2Type.Smith1980Orth
