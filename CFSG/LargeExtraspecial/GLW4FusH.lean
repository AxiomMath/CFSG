module

public import CFSG.LargeExtraspecial.GLW4FusMain
public import CFSG.LargeExtraspecial.GLW4Dnu

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {K : Type*} [Group K] [Finite K]

namespace Lev

variable {T : Setting K} {ι : K →* S.O} {V W : Submodule (ZMod 2) S.Qt} (L : Lev T ι V W)
include L

omit [Finite K] in
theorem Emap_conj_eq_zero {m y : K} (hy : y ∈ T.Qa m) :
    Emap (ι y) (ι (m * T.z * m⁻¹)) = 0 := by
  rw [T.Qa_eq_map m] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hfix := (L.layered y' hy').fix
  refine LinearMap.ext fun v => ?_
  set u := (((ι m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
  have hv : v = (ι m : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by rw [Config.apply_inv_apply]
  have h1 : dm (ι (m * T.z * m⁻¹)) v =
      (ι m : S.Qt ≃ₗ[ZMod 2] S.Qt) (dm (ι T.z) u) := by
    rw [hv, dm_apply, dm_apply, map_mul, map_mul, map_inv, Config.mul_apply, Config.mul_apply,
      Config.inv_apply_apply, map_sub]
  rw [Emap_apply, h1, LinearMap.zero_apply, dm_apply]
  change ((ι ((MulAut.conj m).toMonoidHom y') : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) _ - _ = 0
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv, Config.mul_apply,
    Config.mul_apply, Config.inv_apply_apply, hfix _ (L.dm_mem u), sub_self]

omit [Finite K] in
theorem Emap_eq_zero_of_cl_left {α β : K} (hα : α ∈ T.QG) (hβ : β ∈ T.QG) (h0 : T.cl α = 0) :
    Emap (ι α) (ι β) = 0 := by
  rcases (T.cl_eq_zero_iff hα).mp h0 with rfl | rfl
  · rw [map_one]
    exact LinearMap.ext fun x => by simp [Emap_apply, dm_one]
  · exact L.Emap_z_left hβ

omit [Finite K] in
theorem Emap_eq_zero_of_cl_right {α β : K} (hα : α ∈ T.QG) (hβ : β ∈ T.QG) (h0 : T.cl β = 0) :
    Emap (ι α) (ι β) = 0 := by
  rcases (T.cl_eq_zero_iff hβ).mp h0 with rfl | rfl
  · rw [map_one]
    exact LinearMap.ext fun x => by simp [Emap_apply, dm_one]
  · exact L.Emap_z_right hα

theorem vanishing_of_conj {X : Subgroup T.O} {A B : Submodule (ZMod 2) T.Qt}
    (hP : Pair T X A B) (hXM : X ≤ T.Mbar)
    (h3 : ∀ m : K, m * T.z * m⁻¹ ∈ T.QG → m * T.z * m⁻¹ ≠ T.z →
      3 ≤ finrank (ZMod 2) (T.clSub (T.QG ⊓ T.Qa m)))
    {m : K} (hmQ : m * T.z * m⁻¹ ∈ T.QG) {a b : T.Qt} (ha : a ∈ A) (hb : b ∈ B) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hcl : T.cl (m * T.z * m⁻¹) = a + b) :
    ∀ α ∈ T.QG, ∀ β ∈ T.QG, T.cl α ∈ A → T.cl β ∈ B →
      polar T.q (T.cl α) (T.cl β) = 0 → Emap (ι α) (ι β) = 0 := by
  have hab : polar T.q a b = 0 := by
    have h0 := T.q_cl_conj_z hmQ
    rw [hcl, QuadraticMap.map_add T.q a b, hP.q_A a ha, hP.q_B b hb, zero_add, zero_add] at h0
    exact h0
  intro α hα β hβ hαA hβB h0
  by_cases hα0 : T.cl α = 0
  · exact L.Emap_eq_zero_of_cl_left hα hβ hα0
  by_cases hβ0 : T.cl β = 0
  · exact L.Emap_eq_zero_of_cl_right hα hβ hβ0
  obtain ⟨s, hsX, hsa, hsb⟩ := exists_mem_apply_eq_pair hP ha hb hαA hβB ha0 hb0 hα0 hβ0 hab h0
  obtain ⟨⟨h, hh⟩, rfl⟩ := hXM hsX
  have hx' : (h * m) * T.z * (h * m)⁻¹ = h * (m * T.z * m⁻¹) * h⁻¹ := by group
  have hx'Q : (h * m) * T.z * (h * m)⁻¹ ∈ T.QG := by rw [hx']; exact T.conj_mem_QG hh hmQ
  have e := T.ρ_cl ⟨h, hh⟩ hmQ
  dsimp only at e
  have hclx' : T.cl ((h * m) * T.z * (h * m)⁻¹) = T.cl α + T.cl β := by
    rw [hx', ← e, hcl, map_add, hsa, hsb]
  have hne' : (h * m) * T.z * (h * m)⁻¹ ≠ T.z := fun he => by
    rw [he, T.cl_z] at hclx'
    have h1 : T.cl α = T.cl β := by
      rw [eq_neg_of_add_eq_zero_left hclx'.symm, ZModModule.neg_eq_self]
    have h2 : T.cl α ∈ A ⊓ B := ⟨hαA, h1 ▸ hβB⟩
    rw [hP.inf_eq] at h2
    exact hα0 h2
  obtain ⟨y, hy, hycl⟩ := exists_mem_inf_cl_eq hP hXM hx'Q hne' hαA hβB hclx'
    (h3 (h * m) hx'Q hne')
  have hE0 := L.Emap_conj_eq_zero hy.2
  have hyβ : T.cl ((h * m) * T.z * (h * m)⁻¹) = T.cl (y * β) := by
    rw [hclx', T.cl_mul hy.1 hβ, hycl]
  rw [L.Emap_cl_right hy.1 hx'Q (T.QG.mul_mem hy.1 hβ) hyβ, L.Emap_mul_right' hy.1 hy.1 hβ]
    at hE0
  have hyy : y * y = 1 := by
    have := (T.q_cl_eq_zero_iff hy.1).mp (by rw [hycl]; exact hP.q_A _ hαA)
    rwa [pow_two] at this
  have hyy' : Emap (ι y) (ι y) = 0 := Emap_self (by rw [← map_mul, hyy, map_one])
  rw [hyy', zero_add] at hE0
  rw [L.Emap_cl_left hα hy.1 hβ hycl.symm]
  exact hE0

theorem fusion {X : Subgroup T.O} {A B : Submodule (ZMod 2) T.Qt}
    (hP : Pair T X A B) (hXM : X ≤ T.Mbar) (hV6 : finrank (ZMod 2) V = 6)
    {q : QuadraticForm (ZMod 2) V} (hq : q.polarBilin.Nondegenerate) {R : Set K}
    (hRM : ∀ r ∈ R, r ∈ T.M)
    (hRA : ∀ r (hr : r ∈ R), ∀ a ∈ A, (T.ρ ⟨r, hRM r hr⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) a ∈ A)
    (hRB : ∀ r (hr : r ∈ R), ∀ b ∈ B, (T.ρ ⟨r, hRM r hr⟩ : T.Qt ≃ₗ[ZMod 2] T.Qt) b ∈ B)
    (hR : ∀ g ∈ omegaGroup q hq, ∃ r ∈ R, ∀ v : V,
      ((g v : V) : S.Qt) = (ι r : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
    (h3 : ∀ m : K, m * T.z * m⁻¹ ∈ T.QG → m * T.z * m⁻¹ ≠ T.z →
      3 ≤ finrank (ZMod 2) (T.clSub (T.QG ⊓ T.Qa m)))
    (k : K) (hk : k * T.z * k⁻¹ ∈ T.QG) :
    T.cl (k * T.z * k⁻¹) ∈ A ∨ T.cl (k * T.z * k⁻¹) ∈ B := by
  have hv : T.cl (k * T.z * k⁻¹) ∈ A ⊔ B := by rw [hP.sup_eq]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
  by_cases ha0 : a = 0
  · right
    rw [← hab, ha0, zero_add]
    exact hb
  by_cases hb0 : b = 0
  · left
    rw [← hab, hb0, add_zero]
    exact ha
  exact (L.false_of_vanishing hP hV6 hq hRM hRA hRB hR ha ha0
    (L.vanishing_of_conj hP hXM h3 hk ha hb ha0 hb0 hab.symm)).elim

end Lev

end CFSG.LargeExtraspecial.GLW4
