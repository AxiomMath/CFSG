module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferComparison
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup

section Inducing

variable {G : Type*} [Group G] {S : Subgroup G} {f : NormCocycle S} {α : G ≃* G}
  {τ : CocycleExtension f ≃* CocycleExtension f} (hτ : ∀ x, ((τ x).snd : G) = α x.snd)
include hτ

theorem map_mem_of_inducing {s : G} (hs : s ∈ S) : α s ∈ S := by
  rw [← show ((τ ⟨0, ⟨s, hs⟩⟩).snd : G) = α s from hτ _]
  exact (τ ⟨0, ⟨s, hs⟩⟩).snd.2

theorem symm_map_mem_of_inducing {s : G} (hs : s ∈ S) : α.symm s ∈ S := by
  have h := hτ (τ.symm ⟨0, ⟨s, hs⟩⟩)
  rw [MulEquiv.apply_symm_apply] at h
  have h' : α.symm s = ((τ.symm ⟨0, ⟨s, hs⟩⟩).snd : G) := by
    rw [MulEquiv.symm_apply_eq]
    exact h
  rw [h']
  exact (τ.symm ⟨0, ⟨s, hs⟩⟩).snd.2

theorem eq_mk_one_of_inducing (e : ZMod 2) : τ ⟨e, 1⟩ = ⟨e, 1⟩ := by
  have hsnd : (τ ⟨e, 1⟩).snd = 1 := Subtype.ext (by rw [hτ]; simp)
  rcases zmod_two_cases e with rfl | rfl
  · exact map_one τ
  · exact CocycleExtension.mulEquiv_eq_mk_one_one τ CocycleExtension.mk_one_one_ne_one hsnd

@[expose] def inducedAut : S ≃* S where
  toFun s := ⟨α s, map_mem_of_inducing hτ s.2⟩
  invFun s := ⟨α.symm s, symm_map_mem_of_inducing hτ s.2⟩
  left_inv s := Subtype.ext (α.symm_apply_apply (s : G))
  right_inv s := Subtype.ext (α.apply_symm_apply (s : G))
  map_mul' s t := Subtype.ext (map_mul α (s : G) t)

@[simp] theorem coe_inducedAut (s : S) : (inducedAut hτ s : G) = α s := rfl

end Inducing

namespace IsRightTransversal

variable {G : Type*} [Group G] {S : Subgroup G} {I : Type*} {r : I → G}
  (hr : IsRightTransversal S r)

section AutIndex

variable (α : G ≃* G)

@[expose] noncomputable def autIndex (i : I) : I := hr.index (α (r i))

@[expose] noncomputable def autCoef (i : I) : S :=
  ⟨α (r i) * (r (hr.autIndex α i))⁻¹, hr.mul_inv_mem_index _⟩

theorem map_r (i : I) : α (r i) = hr.autCoef α i * r (hr.autIndex α i) := by
  change α (r i) = α (r i) * (r (hr.autIndex α i))⁻¹ * r (hr.autIndex α i)
  rw [inv_mul_cancel_right]

theorem autIndex_eq_of_eq {i j : I} {s : G} (hs : s ∈ S) (h : α (r i) = s * r j) :
    hr.autIndex α i = j :=
  hr.index_eq_iff.2 (by rw [h, mul_inv_cancel_right]; exact hs)

theorem coe_autCoef_eq_of_eq {i j : I} {s : G} (hs : s ∈ S) (h : α (r i) = s * r j) :
    (hr.autCoef α i : G) = s := by
  change α (r i) * (r (hr.autIndex α i))⁻¹ = s
  rw [hr.autIndex_eq_of_eq α hs h, h, mul_inv_cancel_right]

variable {α}

theorem autIndex_act (hα : ∀ s ∈ S, α s ∈ S) (i : I) (g : G) :
    hr.autIndex α (hr.act i g) = hr.act (hr.autIndex α i) (α g) ∧
      (hr.autCoef α i : G)⁻¹ * α (hr.coef i g) * hr.autCoef α (hr.act i g) =
        hr.coef (hr.autIndex α i) (α g) := by
  have h1 : α (r i * g) = α (hr.coef i g) * hr.autCoef α (hr.act i g) *
      r (hr.autIndex α (hr.act i g)) := by
    rw [hr.r_mul i g, map_mul, hr.map_r α (hr.act i g), mul_assoc]
  have h2 : α (r i * g) = hr.autCoef α i * hr.coef (hr.autIndex α i) (α g) *
      r (hr.act (hr.autIndex α i) (α g)) := by
    rw [map_mul, hr.map_r α i, mul_assoc, hr.r_mul (hr.autIndex α i) (α g), ← mul_assoc]
  have hs₁ : α (hr.coef i g) * (hr.autCoef α (hr.act i g) : G) ∈ S :=
    S.mul_mem (hα _ (hr.coef i g).2) (hr.autCoef α _).2
  have hs₂ : (hr.autCoef α i : G) * hr.coef (hr.autIndex α i) (α g) ∈ S :=
    S.mul_mem (hr.autCoef α i).2 (hr.coef _ _).2
  have heq := h1.symm.trans h2
  have hidx : hr.autIndex α (hr.act i g) = hr.act (hr.autIndex α i) (α g) := by
    apply hr.eq_of_mul_inv_mem
    have : r (hr.autIndex α (hr.act i g)) * (r (hr.act (hr.autIndex α i) (α g)))⁻¹ =
        (α (hr.coef i g) * (hr.autCoef α (hr.act i g) : G))⁻¹ *
          ((hr.autCoef α i : G) * hr.coef (hr.autIndex α i) (α g)) := by
      rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, heq, mul_inv_cancel_right]
    rw [this]
    exact S.mul_mem (S.inv_mem hs₁) hs₂
  refine ⟨hidx, ?_⟩
  rw [hidx] at heq
  rw [mul_assoc, mul_right_cancel heq, inv_mul_cancel_left]

theorem autIndex_surjective (hα : ∀ s ∈ S, α s ∈ S) : Function.Surjective (hr.autIndex α) := by
  intro j
  refine ⟨hr.index (α.symm (r j)), hr.autIndex_eq_of_eq α
    (s := (α (α.symm (r j) * (r (hr.index (α.symm (r j))))⁻¹))⁻¹)
    (S.inv_mem (hα _ (hr.mul_inv_mem_index _))) ?_⟩
  rw [map_mul, map_inv, MulEquiv.apply_symm_apply, mul_inv_rev, inv_inv, inv_mul_cancel_right]

theorem autIndex_bijective [Finite I] (hα : ∀ s ∈ S, α s ∈ S) :
    Function.Bijective (hr.autIndex α) :=
  ⟨Finite.injective_iff_surjective.2 (hr.autIndex_surjective hα), hr.autIndex_surjective hα⟩

end AutIndex

section Transport

variable {f : NormCocycle S}

@[expose] noncomputable def transportCoord (α : G ≃* G)
    (τ : CocycleExtension f ≃* CocycleExtension f) (i : I) (g : G) : ZMod 2 :=
  ((⟨0, hr.autCoef α i⟩ : CocycleExtension f)⁻¹ * τ ⟨0, hr.coef i g⟩ *
    ⟨0, hr.autCoef α (hr.act i g)⟩).fst

@[expose] noncomputable def transportSum [Fintype I] (α : G ≃* G)
    (τ : CocycleExtension f ≃* CocycleExtension f) (g : G) : ZMod 2 :=
  ∑ i, hr.transportCoord α τ i g

variable {α : G ≃* G} {τ : CocycleExtension f ≃* CocycleExtension f}
  (hτ : ∀ x, ((τ x).snd : G) = α x.snd)
include hτ

theorem transport_spec (i : I) (g : G) :
    (⟨0, hr.autCoef α i⟩ : CocycleExtension f)⁻¹ * τ ⟨0, hr.coef i g⟩ *
        ⟨0, hr.autCoef α (hr.act i g)⟩ =
      ⟨hr.transportCoord α τ i g, hr.coef (hr.autIndex α i) (α g)⟩ := by
  refine CocycleExtension.ext rfl (Subtype.ext ?_)
  simp only [CocycleExtension.mul_snd, CocycleExtension.inv_snd, Subgroup.coe_mul,
    Subgroup.coe_inv, hτ]
  exact (hr.autIndex_act (fun _ hs => map_mem_of_inducing hτ hs) i g).2

theorem transportCoord_one (i : I) : hr.transportCoord α τ i 1 = 0 := by
  have h := hr.transport_spec hτ i 1
  rw [hr.act_one, hr.coef_one, eq_mk_one_of_inducing hτ 0, ← CocycleExtension.one_def,
    mul_one, inv_mul_cancel] at h
  exact (congrArg CocycleExtension.fst h).symm

theorem transportCoord_mul (i : I) (g k : G) :
    hr.transportCoord α τ i g + hr.transportCoord α τ (hr.act i g) k +
        f (hr.coef (hr.autIndex α i) (α g)) (hr.coef (hr.act (hr.autIndex α i) (α g)) (α k)) =
      f (hr.coef i g) (hr.coef (hr.act i g) k) + hr.transportCoord α τ i (g * k) := by
  have hT : τ ⟨0, hr.coef i g⟩ * τ ⟨0, hr.coef (hr.act i g) k⟩ =
      ⟨f (hr.coef i g) (hr.coef (hr.act i g) k), 1⟩ * τ ⟨0, hr.coef i (g * k)⟩ := by
    rw [← map_mul, ← eq_mk_one_of_inducing hτ, ← map_mul, CocycleExtension.mk_mul_mk,
      CocycleExtension.mk_mul_mk, f.map_one_left, one_mul, hr.coef_mul, zero_add, zero_add,
      add_zero, add_zero]
  have key : (⟨0, hr.autCoef α i⟩ : CocycleExtension f)⁻¹ * τ ⟨0, hr.coef i g⟩ *
        ⟨0, hr.autCoef α (hr.act i g)⟩ *
      ((⟨0, hr.autCoef α (hr.act i g)⟩ : CocycleExtension f)⁻¹ *
        τ ⟨0, hr.coef (hr.act i g) k⟩ * ⟨0, hr.autCoef α (hr.act (hr.act i g) k)⟩) =
      ⟨f (hr.coef i g) (hr.coef (hr.act i g) k), 1⟩ *
        ((⟨0, hr.autCoef α i⟩ : CocycleExtension f)⁻¹ * τ ⟨0, hr.coef i (g * k)⟩ *
          ⟨0, hr.autCoef α (hr.act i (g * k))⟩) := by
    rw [hr.act_mul i g k]
    have hc := Subgroup.mem_center_iff.1
      (CocycleExtension.mk_one_mem_center (f := f) (f (hr.coef i g) (hr.coef (hr.act i g) k)))
    calc _ = (⟨0, hr.autCoef α i⟩ : CocycleExtension f)⁻¹ *
          (τ ⟨0, hr.coef i g⟩ * τ ⟨0, hr.coef (hr.act i g) k⟩) *
            ⟨0, hr.autCoef α (hr.act (hr.act i g) k)⟩ := by group
      _ = _ := by
          rw [hT, ← mul_assoc _ (⟨_, 1⟩ : CocycleExtension f), hc]
          simp only [mul_assoc]
  rw [hr.transport_spec hτ, hr.transport_spec hτ, hr.transport_spec hτ,
    CocycleExtension.mk_mul_mk, CocycleExtension.mk_one_mul,
    (hr.autIndex_act (fun _ hs => map_mem_of_inducing hτ hs) i g).1] at key
  exact congrArg CocycleExtension.fst key

variable [Fintype I]

theorem transportSum_one : hr.transportSum α τ 1 = 0 :=
  Finset.sum_eq_zero fun i _ => hr.transportCoord_one hτ i

theorem transportSum_mul (g k : G) :
    hr.transportSum α τ g + hr.transportSum α τ k + hr.transportSum α τ (g * k) =
      hr.transfer₂ f g k + hr.transfer₂ f (α g) (α k) := by
  have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hr.transportCoord_mul hτ i g k
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hr.sum_act (fun j => hr.transportCoord α τ j k) g,
    (hr.autIndex_bijective fun _ hs => map_mem_of_inducing hτ hs).sum_comp
      (fun j => f (hr.coef j (α g)) (hr.coef (hr.act j (α g)) (α k)))] at hsum
  simp only [transportSum, transfer₂_apply]
  grind

@[expose] noncomputable def transferAut :
    CocycleExtension (hr.transferCocycle f) ≃* CocycleExtension (hr.transferCocycle f) where
  toFun x := ⟨x.fst + hr.transportSum α τ x.snd, α x.snd⟩
  invFun x := ⟨x.fst + hr.transportSum α τ (α.symm x.snd), α.symm x.snd⟩
  left_inv x := by
    refine CocycleExtension.ext ?_ (α.symm_apply_apply x.snd)
    change x.fst + hr.transportSum α τ x.snd + hr.transportSum α τ (α.symm (α x.snd)) = x.fst
    rw [MulEquiv.symm_apply_apply, add_assoc, zmod_two_add_self, add_zero]
  right_inv x := by
    refine CocycleExtension.ext ?_ (α.apply_symm_apply x.snd)
    change x.fst + hr.transportSum α τ (α.symm x.snd) + hr.transportSum α τ (α.symm x.snd) =
      x.fst
    rw [add_assoc, zmod_two_add_self, add_zero]
  map_mul' x y := by
    refine CocycleExtension.ext ?_ (map_mul α x.snd y.snd)
    change x.fst + y.fst + hr.transfer₂ f x.snd y.snd + hr.transportSum α τ (x.snd * y.snd) =
      x.fst + hr.transportSum α τ x.snd + (y.fst + hr.transportSum α τ y.snd) +
        hr.transfer₂ f (α x.snd) (α y.snd)
    have := hr.transportSum_mul hτ x.snd y.snd
    grind

@[simp] theorem transferAut_apply (x : CocycleExtension (hr.transferCocycle f)) :
    hr.transferAut hτ x = ⟨x.fst + hr.transportSum α τ x.snd, α x.snd⟩ := rfl

theorem transferAut_mk_one_one : hr.transferAut hτ ⟨1, 1⟩ = ⟨1, 1⟩ := by
  rw [transferAut_apply]
  refine CocycleExtension.ext ?_ (map_one α)
  change 1 + hr.transportSum α τ 1 = 1
  rw [hr.transportSum_one hτ, add_zero]

@[expose] noncomputable def restrictAut (μ : S → ZMod 2)
    (hμ : ∀ s t : S, hr.transfer₂ f s t + coboundary μ s t = f s t) :
    CocycleExtension f ≃* CocycleExtension f where
  toFun x := ⟨x.fst + hr.transportSum α τ x.snd + μ x.snd + μ (inducedAut hτ x.snd),
    inducedAut hτ x.snd⟩
  invFun x := ⟨x.fst + hr.transportSum α τ ((inducedAut hτ).symm x.snd) +
    μ ((inducedAut hτ).symm x.snd) + μ x.snd, (inducedAut hτ).symm x.snd⟩
  left_inv x := by
    refine CocycleExtension.ext ?_ ((inducedAut hτ).symm_apply_apply x.snd)
    change x.fst + hr.transportSum α τ x.snd + μ x.snd + μ (inducedAut hτ x.snd) +
      hr.transportSum α τ ((inducedAut hτ).symm (inducedAut hτ x.snd)) +
      μ ((inducedAut hτ).symm (inducedAut hτ x.snd)) + μ (inducedAut hτ x.snd) = x.fst
    rw [MulEquiv.symm_apply_apply]
    grind
  right_inv x := by
    refine CocycleExtension.ext ?_ ((inducedAut hτ).apply_symm_apply x.snd)
    change x.fst + hr.transportSum α τ ((inducedAut hτ).symm x.snd) +
      μ ((inducedAut hτ).symm x.snd) + μ x.snd +
      hr.transportSum α τ ((inducedAut hτ).symm x.snd) + μ ((inducedAut hτ).symm x.snd) +
      μ (inducedAut hτ ((inducedAut hτ).symm x.snd)) = x.fst
    rw [MulEquiv.apply_symm_apply]
    grind
  map_mul' x y := by
    refine CocycleExtension.ext ?_ (map_mul (inducedAut hτ) x.snd y.snd)
    change x.fst + y.fst + f x.snd y.snd + hr.transportSum α τ (x.snd * y.snd : S) +
        μ (x.snd * y.snd) + μ (inducedAut hτ (x.snd * y.snd)) =
      x.fst + hr.transportSum α τ x.snd + μ x.snd + μ (inducedAut hτ x.snd) +
        (y.fst + hr.transportSum α τ y.snd + μ y.snd + μ (inducedAut hτ y.snd)) +
        f (inducedAut hτ x.snd) (inducedAut hτ y.snd)
    have h1 := hr.transportSum_mul hτ x.snd y.snd
    have h2 := hμ x.snd y.snd
    have h3 := hμ (inducedAut hτ x.snd) (inducedAut hτ y.snd)
    rw [map_mul, Subgroup.coe_mul]
    rw [coboundary_apply] at h2 h3
    rw [coe_inducedAut, coe_inducedAut] at h3
    grind

@[simp] theorem restrictAut_apply (μ : S → ZMod 2)
    (hμ : ∀ s t : S, hr.transfer₂ f s t + coboundary μ s t = f s t) (x : CocycleExtension f) :
    hr.restrictAut hτ μ hμ x =
      ⟨x.fst + hr.transportSum α τ x.snd + μ x.snd + μ (inducedAut hτ x.snd),
        inducedAut hτ x.snd⟩ := rfl

theorem restrictAut_eq_conj (μ : S → ZMod 2)
    (hμ : ∀ s t : S, hr.transfer₂ f s t + coboundary μ s t = f s t) (e : ZMod 2) (s : S) :
    hr.restrictAut hτ μ hμ ⟨e, s⟩ =
      ⟨(hr.transferAut hτ ⟨e + μ s, s⟩).fst + μ (inducedAut hτ s), inducedAut hτ s⟩ := by
  rw [restrictAut_apply, transferAut_apply]
  refine CocycleExtension.ext ?_ rfl
  change e + hr.transportSum α τ s + μ s + μ (inducedAut hτ s) =
    e + μ s + hr.transportSum α τ s + μ (inducedAut hτ s)
  ring

end Transport

section Cover

variable [Fintype I] {f : NormCocycle S} {E : Type*} [Group E] {π : E →* G} {z : E}

theorem exists_transfer_mulEquiv (hodd : Odd (Fintype.card I)) (hπ : IsCentralDoubleExt π z)
    (ι : S.comap π ≃* CocycleExtension f) (hι : ∀ x, ((ι x).snd : G) = π x) :
    ∃ (Ψ : E ≃* CocycleExtension (hr.transferCocycle f)) (C : G → ZMod 2),
      (∀ x, (Ψ x).snd = π x) ∧ Ψ z = ⟨1, 1⟩ ∧ C 1 = 0 ∧
      (∀ s t : S, f s t = hr.transfer₂ f s t + coboundary C s t) ∧
      ∀ x : S.comap π, Ψ x = ⟨(ι x).fst + C (π x), π x⟩ := by
  have hzS : z ∈ S.comap π := by
    rw [Subgroup.mem_comap, hπ.map_z]
    exact S.one_mem
  have hιz : ι ⟨z, hzS⟩ = ⟨1, 1⟩ := by
    refine CocycleExtension.mulEquiv_eq_mk_one_one ι ?_ (Subtype.ext ?_)
    · intro h
      exact hπ.ne_one (congrArg Subtype.val h)
    · rw [hι]
      exact hπ.map_z
  have hιz' : ((ι.symm ⟨1, 1⟩ : S.comap π) : E) = z := by
    rw [← hιz, MulEquiv.symm_apply_apply]
  let u₀ : S → E := fun s => (ι.symm ⟨0, s⟩ : E)
  have hu₀ : ∀ s : S, π (u₀ s) = s := by
    intro s
    have h := hι (ι.symm ⟨0, s⟩)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hu₀1 : u₀ 1 = 1 := by
    change ((ι.symm 1 : S.comap π) : E) = 1
    rw [map_one]
    rfl
  have hιe : ∀ e : ZMod 2, ((ι.symm ⟨e, 1⟩ : S.comap π) : E) = z ^ e.val := by
    intro e
    rw [← CocycleExtension.mk_one_pow_val, map_pow, Subgroup.coe_pow, hιz']
  have hf : ∀ s t : S, u₀ s * u₀ t = z ^ (f s t).val * u₀ (s * t) := by
    intro s t
    change ((ι.symm ⟨0, s⟩ : S.comap π) : E) * (ι.symm ⟨0, t⟩ : S.comap π) =
      z ^ (f s t).val * (ι.symm ⟨0, s * t⟩ : S.comap π)
    rw [← Subgroup.coe_mul, ← map_mul, CocycleExtension.mk_mul_mk, ← hιe, ← Subgroup.coe_mul,
      ← map_mul, CocycleExtension.mk_one_mul, zero_add, zero_add, add_zero]
  obtain ⟨u, h, C, hu, -, huS, hh, hhS, hC1, hC⟩ :=
    hr.exists_section_eq_transfer_add_coboundary hπ hodd u₀ hu₀ hu₀1 f hf
  obtain ⟨Ψ, hΨ, hΨz, hΨu⟩ := hπ.exists_mulEquiv_of_section u hu (hr.transferCocycle f) C
    (fun g k => by rw [hh, hC g k]; rfl)
  refine ⟨Ψ, C, hΨ, hΨz, hC1, fun s t => by rw [← hhS s t, hC s t], fun x => ?_⟩
  have hdecomp : ι x = ⟨(ι x).fst, 1⟩ * ⟨0, (ι x).snd⟩ := by
    rw [CocycleExtension.mk_one_mul]
    exact CocycleExtension.ext (add_zero _).symm rfl
  have hx : (x : E) = z ^ (ι x).fst.val * u₀ (ι x).snd := by
    have h1 : x = ι.symm ⟨(ι x).fst, 1⟩ * ι.symm ⟨0, (ι x).snd⟩ := by
      rw [← map_mul, ← hdecomp, MulEquiv.symm_apply_apply]
    exact (congrArg Subtype.val h1).trans (by rw [Subgroup.coe_mul, hιe])
  have hsnd : ((ι x).snd : G) = π x := hι x
  calc Ψ x = Ψ (z ^ (ι x).fst.val * u₀ (ι x).snd) := by rw [← hx]
    _ = ⟨(ι x).fst, 1⟩ * ⟨C (ι x).snd, (ι x).snd⟩ := by
        rw [map_mul, ← huS, hΨu, map_pow, hΨz, CocycleExtension.mk_one_pow_val]
    _ = ⟨(ι x).fst + C (π x), π x⟩ := by
        rw [CocycleExtension.mk_one_mul, hsnd]

theorem transport_eq_transferAut {α : G ≃* G} {τ : CocycleExtension f ≃* CocycleExtension f}
    (hτ : ∀ x, ((τ x).snd : G) = α x.snd) [Group.IsPerfect E]
    (Ψ : E ≃* CocycleExtension (hr.transferCocycle f)) (hΨ : ∀ x, (Ψ x).snd = π x)
    (φ : E ≃* E) (hφ : ∀ x, π (φ x) = α (π x)) (x : E) :
    Ψ (φ x) = hr.transferAut hτ (Ψ x) := by
  have : Group.IsPerfect (CocycleExtension (hr.transferCocycle f)) :=
    Group.IsPerfect.ofSurjective (f := Ψ.toMonoidHom) Ψ.surjective
  let W : MulAut (CocycleExtension (hr.transferCocycle f)) :=
    (Ψ.symm.trans (φ.trans Ψ)).trans (hr.transferAut hτ).symm
  have hW : W = 1 := by
    apply eq_one_of_forall_inv_mul_mem_center
    intro y
    apply CocycleExtension.mem_center_of_snd_eq_one
    have h2 : (W y).snd = y.snd := by
      change α.symm (Ψ (φ (Ψ.symm y))).snd = y.snd
      rw [hΨ, hφ, ← hΨ, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    rw [CocycleExtension.mul_snd, CocycleExtension.inv_snd, h2, inv_mul_cancel]
  have hWx := congrArg (fun w : MulAut _ => w (Ψ x)) hW
  change (hr.transferAut hτ).symm (Ψ (φ (Ψ.symm (Ψ x)))) = Ψ x at hWx
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_eq] at hWx
  exact hWx

theorem odd_index_central_double_cover_transfer_and_automorphism_transport
    (hodd : Odd (Fintype.card I)) {α : G ≃* G} {τ : CocycleExtension f ≃* CocycleExtension f}
    (hτ : ∀ x, ((τ x).snd : G) = α x.snd) (μ : S → ZMod 2)
    (hμ : ∀ s t : S, hr.transfer₂ f s t + coboundary μ s t = f s t) [Group.IsPerfect E]
    (hπ : IsCentralDoubleExt π z) (ι : S.comap π ≃* CocycleExtension f)
    (hι : ∀ x, ((ι x).snd : G) = π x) :
    Function.Bijective (hr.autIndex α) ∧ (∀ i, α (r i) = hr.autCoef α i * r (hr.autIndex α i)) ∧
    (∀ i g, (⟨0, hr.autCoef α i⟩ : CocycleExtension f)⁻¹ * τ ⟨0, hr.coef i g⟩ *
        ⟨0, hr.autCoef α (hr.act i g)⟩ =
      ⟨hr.transportCoord α τ i g, hr.coef (hr.autIndex α i) (α g)⟩) ∧
    ((∀ k, hr.transfer₂ f 1 k = 0) ∧ (∀ g, hr.transfer₂ f g 1 = 0) ∧
      ∀ g h k, hr.transfer₂ f g h + hr.transfer₂ f (g * h) k =
        hr.transfer₂ f h k + hr.transfer₂ f g (h * k)) ∧
    (∀ e g, hr.transferAut hτ ⟨e, g⟩ = ⟨e + hr.transportSum α τ g, α g⟩) ∧
    hr.transferAut hτ ⟨1, 1⟩ = ⟨1, 1⟩ ∧
    ∃ Ψ : E ≃* CocycleExtension (hr.transferCocycle f),
      (∀ x, (Ψ x).snd = π x) ∧ Ψ z = ⟨1, 1⟩ ∧
      (∀ φ : E ≃* E, (∀ x, π (φ x) = α (π x)) → ∀ x, Ψ (φ x) = hr.transferAut hτ (Ψ x)) ∧
      ∃ ι' : S.comap π ≃* CocycleExtension f,
        (∀ x : S.comap π, ι' x = ⟨(Ψ x).fst + μ ⟨π x, x.2⟩, ⟨π x, x.2⟩⟩) ∧
        ((ι'.symm ⟨1, 1⟩ : S.comap π) : E) = z ∧
        (∀ (e : ZMod 2) (s : S), hr.restrictAut hτ μ hμ ⟨e, s⟩ =
          ⟨(hr.transferAut hτ ⟨e + μ s, s⟩).fst + μ (inducedAut hτ s), inducedAut hτ s⟩) ∧
        ∀ φ : E ≃* E, (∀ x, π (φ x) = α (π x)) →
          ∀ (x : E) (hx : π x ∈ S) (hφx : π (φ x) ∈ S),
            ι' ⟨φ x, hφx⟩ = hr.restrictAut hτ μ hμ (ι' ⟨x, hx⟩) := by
  obtain ⟨Ψ, -, hΨ, hΨz, -, -, -⟩ := hr.exists_transfer_mulEquiv hodd hπ ι hι
  obtain ⟨ι', hι'⟩ := exists_comap_mulEquiv Ψ hΨ f μ hμ
  have hzS : z ∈ S.comap π := by
    rw [Subgroup.mem_comap, hπ.map_z]
    exact S.one_mem
  refine ⟨hr.autIndex_bijective fun _ hs => map_mem_of_inducing hτ hs, hr.map_r α,
    hr.transport_spec hτ, hr.transfer₂_isNormCocycle f, fun e g => rfl,
    hr.transferAut_mk_one_one hτ, Ψ, hΨ, hΨz,
    fun φ hφ x => hr.transport_eq_transferAut hτ Ψ hΨ φ hφ x, ι', hι', ?_,
    hr.restrictAut_eq_conj hτ μ hμ, ?_⟩
  · have h1 : ι' ⟨z, hzS⟩ = ⟨1, 1⟩ := by
      refine CocycleExtension.mulEquiv_eq_mk_one_one ι' ?_ ?_
      · intro h
        exact hπ.ne_one (congrArg Subtype.val h)
      · rw [hι']
        exact Subtype.ext hπ.map_z
    rw [← h1, MulEquiv.symm_apply_apply]
  · intro φ hφ x hx hφx
    have hfst : (Ψ (φ x)).fst = (Ψ x).fst + hr.transportSum α τ (π x) := by
      rw [hr.transport_eq_transferAut hτ Ψ hΨ φ hφ x, transferAut_apply, hΨ]
    have hσ : (⟨π (φ x), hφx⟩ : S) = inducedAut hτ ⟨π x, hx⟩ := Subtype.ext (hφ x)
    rw [hι', hι', restrictAut_apply]
    refine CocycleExtension.ext ?_ hσ
    change (Ψ (φ x)).fst + μ ⟨π (φ x), hφx⟩ = (Ψ x).fst + μ ⟨π x, hx⟩ +
      hr.transportSum α τ (π x) + μ ⟨π x, hx⟩ + μ (inducedAut hτ ⟨π x, hx⟩)
    rw [hfst, hσ]
    grind

end Cover

end IsRightTransversal

end CFSG.ComponentClassification.CentralCover
