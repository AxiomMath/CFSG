module

public import CFSG.LargeExtraspecial.S8KE
public import CFSG.LargeExtraspecial.S9GenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

theorem eq_smul_of_commute_actsTv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (h2 : 2 ≤ finrank (ZMod 2) V) (θ : V →ₗ[ZMod 2] V)
    (hθ : ∀ (c : V) (μ : Dual (ZMod 2) V), μ c = 0 →
      ∀ x, θ (x + μ x • c) = θ x + μ (θ x) • c) :
    ∃ a : ZMod 2, θ = a • (1 : Module.End (ZMod 2) V) := by
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun v => ?_
  by_cases hv : v = 0
  · rw [hv]
    exact fun h => h.ne_zero 0 rfl
  have hP : (ZMod 2) ∙ v < ⊤ := by
    refine Submodule.lt_top_of_finrank_lt_finrank ?_
    rw [finrank_span_singleton hv]
    omega
  obtain ⟨μ, hμ0, hμP⟩ := Submodule.exists_le_ker_of_lt_top _ hP
  have hμv : μ v = 0 := hμP (Submodule.mem_span_singleton_self v)
  obtain ⟨x, hx⟩ : ∃ x, μ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ0 (LinearMap.ext h)
  have hx1 : μ x = 1 := zmod2_eq_one_of_ne_zero hx
  have h := hθ v μ hμv x
  rw [map_add, hx1, one_smul, add_right_inj] at h
  intro hli
  have hmem : θ v ∈ (ZMod 2) ∙ v := by
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  have h0 : a • v + (1 : ZMod 2) • θ v = 0 := by
    rw [one_smul, ← ha]
    exact S9.add_self_eq_zero_zmod2 _
  exact one_ne_zero ((LinearIndependent.pair_iff.mp hli) a 1 h0).2

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

section Form

variable {t : S.O} [hN : NQHyp S g t]

@[expose] noncomputable def indO (c : S.O) : ZMod 2 := open Classical in if c = 1 then 0 else 1

theorem indO_one : indO (1 : S.O) = 0 := by simp [indO]

theorem indO_eq_zero_iff {c : S.O} : indO c = 0 ↔ c = 1 := by
  unfold indO
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem indO_mul (htt : t * t = 1) {c d : S.O} (hc : c ∈ zpowers t) (hd : d ∈ zpowers t) :
    indO (c * d) = indO c + indO d := by
  rcases eq_one_or_eq_of_mem_zpowers htt hc with h1 | h1 <;>
    rcases eq_one_or_eq_of_mem_zpowers htt hd with h2 | h2 <;> rw [h1, h2]
  · rw [one_mul, indO_one, add_zero]
  · rw [one_mul, indO_one, zero_add]
  · rw [mul_one, indO_one, add_zero]
  · rw [htt, indO_one]
    unfold indO
    split_ifs <;> decide

variable (S g t) in
@[expose] noncomputable def nComm (x y : Nbar S g t) : S.O :=
  (x : S.O) * y * (x : S.O)⁻¹ * (y : S.O)⁻¹

theorem nComm_mem (x y : Nbar S g t) : nComm S g t x y ∈ zpowers t :=
  hN.comm _ x.2 _ y.2

theorem zpowers_commute {c : S.O} (hc : c ∈ zpowers t) (x : Nbar S g t) :
    c * x = x * c := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hc
  exact (Commute.zpow_left (commute_of_mem_Rbar hN.conj_mem (Nbar_le_Rbar x.2)).symm i).eq

theorem nComm_congr {x x' y y' : Nbar S g t} (hx : nqMk x = nqMk x') (hy : nqMk y = nqMk y') :
    nComm S g t x y = nComm S g t x' y' := by
  rw [nqMk_eq_iff] at hx hy
  obtain ⟨c, hc⟩ : ∃ c, c = (x : S.O)⁻¹ * x' := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = (y : S.O)⁻¹ * y' := ⟨_, rfl⟩
  rw [← hc] at hx
  rw [← hd] at hy
  have ex : (x' : S.O) = x * c := by rw [hc]; group
  have ey : (y' : S.O) = y * d := by rw [hd]; group
  have hcx := zpowers_commute hx x
  have hcy := zpowers_commute hx y
  have hdx := zpowers_commute hy x
  have hdy := zpowers_commute hy y
  have hcd : c * d = d * c := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self t i j).eq
  unfold nComm
  rw [ex, ey]
  symm
  set X : S.O := (x : S.O) with hX
  set Y : S.O := (y : S.O) with hY
  calc X * c * (Y * d) * (X * c)⁻¹ * (Y * d)⁻¹ = X * (c * Y) * d * c⁻¹ * X⁻¹ * d⁻¹ * Y⁻¹ := by
        group
    _ = X * (Y * c) * d * c⁻¹ * X⁻¹ * d⁻¹ * Y⁻¹ := by rw [hcy]
    _ = X * Y * (c * d * c⁻¹) * X⁻¹ * d⁻¹ * Y⁻¹ := by group
    _ = X * Y * (d * X⁻¹) * d⁻¹ * Y⁻¹ := by rw [hcd]; group
    _ = X * Y * (X⁻¹ * d) * d⁻¹ * Y⁻¹ := by
        rw [show d * X⁻¹ = X⁻¹ * d by
          calc d * X⁻¹ = X⁻¹ * (X * d) * X⁻¹ := by group
            _ = X⁻¹ * (d * X) * X⁻¹ := by rw [hdx]
            _ = X⁻¹ * d := by group]
    _ = X * Y * X⁻¹ * Y⁻¹ := by group

theorem nComm_mul_left (x x' y : Nbar S g t) :
    nComm S g t (x * x') y = nComm S g t x' y * nComm S g t x y := by
  have hc := zpowers_commute (nComm_mem x' y) x
  unfold nComm at hc ⊢
  simp only [Subgroup.coe_mul]
  calc (x : S.O) * x' * y * ((x : S.O) * x')⁻¹ * (y : S.O)⁻¹ =
      x * ((x' : S.O) * y * (x' : S.O)⁻¹ * (y : S.O)⁻¹) * (x : S.O)⁻¹ *
        ((x : S.O) * y * (x : S.O)⁻¹ * (y : S.O)⁻¹) := by group
    _ = ((x' : S.O) * y * (x' : S.O)⁻¹ * (y : S.O)⁻¹) * x * (x : S.O)⁻¹ *
        ((x : S.O) * y * (x : S.O)⁻¹ * (y : S.O)⁻¹) := by rw [← hc]
    _ = _ := by group

theorem nComm_mul_right (x y y' : Nbar S g t) :
    nComm S g t x (y * y') = nComm S g t x y' * nComm S g t x y := by
  have hc := zpowers_commute (nComm_mem x y') (x * y * x⁻¹)
  unfold nComm at hc ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
  calc (x : S.O) * (y * y') * (x : S.O)⁻¹ * ((y : S.O) * y')⁻¹ =
      ((x : S.O) * y * (x : S.O)⁻¹) *
        ((x : S.O) * y' * (x : S.O)⁻¹ * (y' : S.O)⁻¹) * (y : S.O)⁻¹ := by group
    _ = ((x : S.O) * y' * (x : S.O)⁻¹ * (y' : S.O)⁻¹) *
        ((x : S.O) * y * (x : S.O)⁻¹) * (y : S.O)⁻¹ := by rw [hc]
    _ = _ := by group

noncomputable def nqRepr (u : NQ S g t) : Nbar S g t :=
  (nqMk_surjective (S := S) (g := g) (t := t) u).choose

theorem nqMk_nqRepr (u : NQ S g t) : nqMk (nqRepr u) = u :=
  (nqMk_surjective (S := S) (g := g) (t := t) u).choose_spec

noncomputable def nqFormFun (u v : NQ S g t) : ZMod 2 :=
  indO (nComm S g t (nqRepr u) (nqRepr v))

theorem nqFormFun_mk (x y : Nbar S g t) :
    nqFormFun (nqMk x) (nqMk y) = indO (nComm S g t x y) := by
  unfold nqFormFun
  rw [nComm_congr (nqMk_nqRepr (nqMk x)) (nqMk_nqRepr (nqMk y))]

theorem nqFormFun_add_left (htt : t * t = 1) (u u' v : NQ S g t) :
    nqFormFun (u + u') v = nqFormFun u v + nqFormFun u' v := by
  obtain ⟨x, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) u
  obtain ⟨x', rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) u'
  obtain ⟨y, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) v
  rw [← nqMk_mul, nqFormFun_mk, nqFormFun_mk, nqFormFun_mk, nComm_mul_left,
    indO_mul htt (nComm_mem _ _) (nComm_mem _ _), add_comm]

theorem nqFormFun_add_right (htt : t * t = 1) (u v v' : NQ S g t) :
    nqFormFun u (v + v') = nqFormFun u v + nqFormFun u v' := by
  obtain ⟨x, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) u
  obtain ⟨y, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) v
  obtain ⟨y', rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) v'
  rw [← nqMk_mul, nqFormFun_mk, nqFormFun_mk, nqFormFun_mk, nComm_mul_right,
    indO_mul htt (nComm_mem _ _) (nComm_mem _ _), add_comm]

theorem nqFormFun_zero_left (v : NQ S g t) : nqFormFun (0 : NQ S g t) v = 0 := by
  obtain ⟨y, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) v
  have h0 : (0 : NQ S g t) = nqMk 1 := ((nqMk_eq_zero_iff _).mpr (one_mem _)).symm
  rw [h0, nqFormFun_mk, indO_eq_zero_iff]
  unfold nComm
  simp

theorem nqFormFun_zero_right (u : NQ S g t) : nqFormFun u (0 : NQ S g t) = 0 := by
  obtain ⟨x, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) u
  have h0 : (0 : NQ S g t) = nqMk 1 := ((nqMk_eq_zero_iff _).mpr (one_mem _)).symm
  rw [h0, nqFormFun_mk, indO_eq_zero_iff]
  unfold nComm
  simp

variable (S g t) in
noncomputable def nqForm (htt : t * t = 1) : LinearMap.BilinForm (ZMod 2) (NQ S g t) :=
  LinearMap.mk₂ (ZMod 2) (nqFormFun (S := S) (g := g) (t := t)) (nqFormFun_add_left htt)
    (fun c u v => by
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, zero_smul, nqFormFun_zero_left]
      · rw [one_smul, one_smul])
    (nqFormFun_add_right htt)
    (fun c u v => by
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, zero_smul, nqFormFun_zero_right]
      · rw [one_smul, one_smul])

theorem nqForm_mk (htt : t * t = 1) (x y : Nbar S g t) :
    nqForm S g t htt (nqMk x) (nqMk y) = indO (nComm S g t x y) :=
  nqFormFun_mk x y

theorem nqForm_self (htt : t * t = 1) (u : NQ S g t) : nqForm S g t htt u u = 0 := by
  obtain ⟨x, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) u
  rw [nqForm_mk, indO_eq_zero_iff]
  unfold nComm
  group

theorem nComm_nConjC (σ : CMt S t) (x y : Nbar S g t) :
    nComm S g t (S9.nConjC σ x) (S9.nConjC σ y) = nComm S g t x y := by
  have hc := nComm_mem x y
  have hσt := (mem_CMt.mp σ.2).2
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hc
  have e : nComm S g t (S9.nConjC σ x) (S9.nConjC σ y) =
      (σ : S.O) * nComm S g t x y * (σ : S.O)⁻¹ := by
    unfold nComm
    simp only [S9.coe_nConjC]
    group
  rw [e, ← hi, (Commute.zpow_right hσt i).eq, mul_inv_cancel_right]

theorem nqForm_nqLinC_mk (htt : t * t = 1) (σ : CMt S t) (x y : Nbar S g t) :
    nqForm S g t htt (S9.nqLinC σ (nqMk x)) (S9.nqLinC σ (nqMk y)) =
      nqForm S g t htt (nqMk x) (nqMk y) :=
  (congrArg₂ (fun a b => nqForm S g t htt a b) (S9.nqLinC_mk σ x) (S9.nqLinC_mk σ y)).trans
    ((nqForm_mk htt _ _).trans ((congrArg indO (nComm_nConjC σ x y)).trans
      (nqForm_mk htt x y).symm))

theorem nqForm_nqLinC (htt : t * t = 1) (σ : CMt S t) (u v : NQ S g t) :
    nqForm S g t htt (S9.nqLinC σ u) (S9.nqLinC σ v) = nqForm S g t htt u v :=
  (congrArg₂ (fun a b => nqForm S g t htt (S9.nqLinC σ a) (S9.nqLinC σ b))
    (nqMk_nqRepr u).symm (nqMk_nqRepr v).symm).trans
    ((nqForm_nqLinC_mk htt σ (nqRepr u) (nqRepr v)).trans
      (congrArg₂ (fun a b => nqForm S g t htt a b) (nqMk_nqRepr u) (nqMk_nqRepr v)))

theorem nqForm_nondegenerate (htt : t * t = 1)
    (hZ : ∀ x ∈ Nbar S g t, (∀ y ∈ Nbar S g t, y * x = x * y) → x ∈ zpowers t) :
    (nqForm S g t htt).Nondegenerate := by
  have halt : (nqForm S g t htt).IsAlt := fun u => nqForm_self htt u
  refine (LinearMap.IsAlt.isRefl halt).nondegenerate_iff_separatingLeft.mpr fun u hu => ?_
  obtain ⟨x, rfl⟩ := nqMk_surjective (S := S) (g := g) (t := t) u
  refine (nqMk_eq_zero_iff _).mpr (hZ _ x.2 fun y hy => ?_)
  have h1 := hu (nqMk ⟨y, hy⟩)
  rw [nqForm_mk, indO_eq_zero_iff] at h1
  unfold nComm at h1
  calc y * (x : S.O) = ((x : S.O) * y * (x : S.O)⁻¹ * y⁻¹)⁻¹ * (x * y) := by group
    _ = x * y := by rw [h1, inv_one, one_mul]

theorem ker_nqComm_eq (htt : t * t = 1)
    (hZ : ∀ x ∈ Nbar S g t, (∀ y ∈ Nbar S g t, y * x = x * y) → x ∈ zpowers t)
    (σ : CMt S t) (hσσ : (σ : S.O) * σ = 1) :
    LinearMap.ker (nqComm S g t σ) =
      (nqForm S g t htt).orthogonal (LinearMap.range (nqComm S g t σ)) := by
  have hnd := nqForm_nondegenerate htt hZ
  have hσ1 : σ * σ = 1 := Subtype.ext hσσ
  have hinv : ∀ v : NQ S g t, S9.nqLinC σ (S9.nqLinC σ v) = v := fun v =>
    (S9.nqLinC_comp σ σ v).trans ((congrArg (fun s => S9.nqLinC s v) hσ1).trans
      (S9.nqLinC_one v))
  have hle : LinearMap.ker (nqComm S g t σ) ≤
      (nqForm S g t htt).orthogonal (LinearMap.range (nqComm S g t σ)) := by
    intro x hx
    have hx' : S9.nqLinC σ x + x = 0 := (nqComm_apply σ x).symm.trans hx
    have hσx : S9.nqLinC σ x = x :=
      (eq_neg_of_add_eq_zero_left hx').trans (S9.neg_eq_self_zmod2 x)
    intro w hw
    have hy := hw.choose_spec
    change nqForm S g t htt w x = 0
    have e1 : nqForm S g t htt w x =
        nqForm S g t htt (S9.nqLinC σ hw.choose) x + nqForm S g t htt hw.choose x :=
      (congrArg (fun a => nqForm S g t htt a x) (hy.symm.trans (nqComm_apply σ _))).trans
        (LinearMap.map_add₂ _ _ _ _)
    have e2 : nqForm S g t htt (S9.nqLinC σ hw.choose) x = nqForm S g t htt hw.choose x :=
      (congrArg (fun a => nqForm S g t htt (S9.nqLinC σ hw.choose) a) hσx.symm).trans
        (nqForm_nqLinC htt σ _ _)
    exact e1.trans ((congrArg (· + nqForm S g t htt hw.choose x) e2).trans
      (S9.add_self_eq_zero_zmod2 _))
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd (LinearMap.range (nqComm S g t σ))
  have h2 := LinearMap.finrank_range_add_finrank_ker (nqComm S g t σ)
  omega

end Form

end CFSG.LargeExtraspecial.S8
