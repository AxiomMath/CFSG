module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.M24S.NSForm
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.M24S.NSB

open Matrix GL4 CFSG.CGT.M24S.NSSecond CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {T H : Subgroup G} {t : G} (c : NatCoord T H t)

@[expose] def IsCaseB (x : G) : Prop :=
  x ∈ H ⊓ Subgroup.centralizer ({t} : Set G) ∧ x ^ 2 = 1 ∧ blk (c.mat x) = ℓ₀ ∧
    (top (c.mat x) = ![0, 1, 0] ∨ top (c.mat x) = ![0, 1, 1])

variable {c}

theorem IsCaseB.mat_eq {x : G} (hx : IsCaseB c x) : c.mat x = mk4 (top (c.mat x)) ℓ₀ := by
  rw [← hx.2.2.1]
  exact eq_mk4 _ (c.mat_mulVec_e0 hx.1)

theorem IsCaseB.inv_eq {x : G} (hx : IsCaseB c x) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hx.2.1)

theorem IsCaseB.commute_iff {x s : G} (hx : IsCaseB c x) (hs : s ∈ T) :
    s * x = x * s ↔ c.mat x *ᵥ c.vec s = c.vec s := by
  rw [← c.vec_conj hx.1.1 hs]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    have h1 := c.eq_of_vec_eq (c.conj_mem hx.1.1 hs) hs h
    calc s * x = x * s * x⁻¹ * x := by rw [h1]
      _ = x * s := by group

theorem IsCaseB.exists_eq_commutator {x s' : G} (hx : IsCaseB c x) (hs' : s' ∈ T)
    (hs'x : s' * x = x * s') : ∃ r ∈ T, s' = r * (x * r * x⁻¹) := by
  have hfix := (hx.commute_iff hs').1 hs'x
  rw [hx.mat_eq] at hfix
  obtain ⟨u, hu⟩ := exists_of_mulVec_eq _ hx.2.2.2 _ hfix
  obtain ⟨r, hr, hru⟩ := c.exists_vec_eq u
  refine ⟨r, hr, c.eq_of_vec_eq hs' (T.mul_mem hr (c.conj_mem hx.1.1 hr)) ?_⟩
  rw [c.vec_mul hr (c.conj_mem hx.1.1 hr), c.vec_conj hx.1.1 hr, hru, ← hu, hx.mat_eq, top_mk4]

theorem IsCaseB.card_centralizer_T {x : G} (hx : IsCaseB c x) :
    Nat.card (T ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 4 := by
  let f : ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) →
      {w : Fin 4 → ZMod 2 // mk4 (top (c.mat x)) ℓ₀ *ᵥ w = w} := fun s =>
    ⟨c.vec s, by
      rw [← hx.mat_eq]
      exact (hx.commute_iff s.2.1).1 (Subgroup.mem_centralizer_singleton_iff.1 s.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun s s' h => Subtype.ext (c.eq_of_vec_eq s.2.1 s'.2.1 (congrArg Subtype.val h)),
      fun w => ?_⟩
    obtain ⟨s, hs, hsw⟩ := c.exists_vec_eq w.1
    have hsx : s * x = x * s := (hx.commute_iff hs).2 (by
      rw [hsw]
      exact (congrArg (· *ᵥ (w : Fin 4 → ZMod 2)) hx.mat_eq).trans w.2)
    exact ⟨⟨s, hs, Subgroup.mem_centralizer_singleton_iff.2 hsx⟩, Subtype.ext hsw⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  exact card_fixed_four _ hx.2.2.2

theorem IsCaseB.exists_lift_of_commute {x : G} (hx : IsCaseB c x)
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM1 : M.det = 1) (hMe : M *ᵥ e0 = e0)
    (hMx : M * c.mat x = c.mat x * M) :
    ∃ g ∈ H ⊓ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({t} : Set G),
      c.mat g = M := by
  obtain ⟨g, hg, hgM⟩ := c.exists_mat_eq M hM1
  have hgK : g ∈ H ⊓ Subgroup.centralizer ({t} : Set G) :=
    ⟨hg, (c.mem_centralizer_iff hg).2 (by rw [hgM]; exact hMe)⟩
  have hxH := hx.1.1
  have hxi := hx.inv_eq
  have hyH : g * x * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg)
  have hs'T : x⁻¹ * (g * x * g⁻¹) ∈ T := by
    rw [← c.mat_eq_one_iff (H.mul_mem (H.inv_mem hxH) hyH), c.mat_mul (H.inv_mem hxH) hyH,
      c.mat_mul (H.mul_mem hg hxH) (H.inv_mem hg), c.mat_mul hg hxH, hgM, hMx, ← hgM,
      Matrix.mul_assoc, c.mat_mul_inv hg, Matrix.mul_one, c.mat_inv_mul hxH]
  set s' := x⁻¹ * (g * x * g⁻¹) with hs'
  have hy2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, ← pow_two, hx.2.1,
      mul_one, mul_inv_cancel]
  have hxs' : x * s' = g * x * g⁻¹ := by rw [hs', mul_inv_cancel_left]
  have hs'x : s' * x = x * s' := by
    have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right (mul_self_of_mem_T c hs'T)
    calc s' * x = s'⁻¹ * x⁻¹ := by rw [hs'i, hxi]
      _ = (x * s')⁻¹ := (mul_inv_rev x s').symm
      _ = x * s' := by rw [hxs', inv_eq_of_mul_eq_one_right hy2]
  obtain ⟨r, hr, hrs⟩ := hx.exists_eq_commutator hs'T hs'x
  have hd : x⁻¹ * (r * (x * s') * r⁻¹) = 1 := by
    have hc1 : x⁻¹ * r * x⁻¹⁻¹ ∈ T := c.conj_mem (H.inv_mem hxH) hr
    have hc2 : s' * r⁻¹ ∈ T := T.mul_mem hs'T (T.inv_mem hr)
    have e : x⁻¹ * (r * (x * s') * r⁻¹) = (x⁻¹ * r * x⁻¹⁻¹) * (s' * r⁻¹) := by group
    rw [e]
    refine c.eq_of_vec_eq (T.mul_mem hc1 hc2) T.one_mem ?_
    have hvs' : c.vec s' = c.vec r + c.mat x *ᵥ c.vec r := by
      rw [hrs, c.vec_mul hr (c.conj_mem hxH hr), c.vec_conj hxH hr]
    rw [c.vec_mul hc1 hc2, c.vec_mul hs'T (T.inv_mem hr), c.vec_conj (H.inv_mem hxH) hr, hxi,
      vec_inv c hr, hvs', c.vec_one]
    rw [show c.mat x *ᵥ c.vec r + (c.vec r + c.mat x *ᵥ c.vec r + c.vec r) =
      (c.mat x *ᵥ c.vec r + c.mat x *ᵥ c.vec r) + (c.vec r + c.vec r) by abel, vec_add_self,
      vec_add_self, add_zero]
  have hconj : (r * g) * x * (r * g)⁻¹ = x := by
    have e : (r * g) * x * (r * g)⁻¹ = r * (x * s') * r⁻¹ := by rw [hxs']; group
    rw [e]
    calc r * (x * s') * r⁻¹ = x * (x⁻¹ * (r * (x * s') * r⁻¹)) := by group
      _ = x := by rw [hd, mul_one]
  have hrg : r * g ∈ H := H.mul_mem (c.le hr) hg
  refine ⟨r * g, ⟨⟨hrg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
    mul_mem (c.E_le (c.T_le_E hr)).2 hgK.2⟩, ?_⟩
  · calc r * g * x = (r * g) * x * (r * g)⁻¹ * (r * g) := by group
      _ = x * (r * g) := by rw [hconj]
  · rw [c.mat_mul (c.le hr) hg, (c.mat_eq_one_iff (c.le hr)).2 hr, Matrix.one_mul, hgM]

end CFSG.CGT.M24S.NSB
