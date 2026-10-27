module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import Mathlib.GroupTheory.IsPerfect
import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv

variable {X : Type*} [Group X] (K : Subgroup X)

@[expose] noncomputable def autQuot : MulAut K →* MulAut (K ⧸ center K) where
  toFun φ := QuotientGroup.congr (center K) (center K) φ (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

@[expose] noncomputable def actQuot : normalizer (K : Set X) →* MulAut (K ⧸ center K) :=
  (autQuot K).comp (K.normalizerMonoidHom)

@[expose] noncomputable def conjAutAlt8 :
    Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
      (by norm_num))

@[expose] noncomputable def actPerm (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) :
    normalizer (K : Set X) →* Perm (Fin 8) :=
  (conjAutAlt8.symm : MulAut (alternatingGroup (Fin 8)) ≃* Perm (Fin 8)).toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (actQuot K))

variable {K}

private lemma wt_normalizerHom_mul_inv_mul_comm {X : Type*} [Group X] {K : Subgroup X}
    (y : normalizer (K : Set X)) {a b : K}
    (hb : K.normalizerMonoidHom y b * b⁻¹ ∈ Subgroup.center K) :
    K.normalizerMonoidHom y (a * b) * (a * b)⁻¹ =
      (K.normalizerMonoidHom y a * a⁻¹) * (K.normalizerMonoidHom y b * b⁻¹) := by
  rw [Subgroup.mem_center_iff] at hb
  simp only [map_mul, mul_inv_rev]
  rw [mul_assoc (K.normalizerMonoidHom y a) (K.normalizerMonoidHom y b) (b⁻¹ * a⁻¹),
      ← mul_assoc (K.normalizerMonoidHom y b) b⁻¹ a⁻¹,
      ← hb a⁻¹,
      ← mul_assoc (K.normalizerMonoidHom y a) a⁻¹ (K.normalizerMonoidHom y b * b⁻¹)]

theorem actQuot_apply_mk (y : normalizer (K : Set X)) (k k' : K) (hk : (k' : X) = y * k * y⁻¹) :
    actQuot K y (QuotientGroup.mk k) = QuotientGroup.mk k' := by
  have h1 : actQuot K y (QuotientGroup.mk k)
      = QuotientGroup.mk (K.normalizerMonoidHom y k) := by
    change QuotientGroup.congr (center K) (center K) (K.normalizerMonoidHom y)
        (Subgroup.map_center_eq (K.normalizerMonoidHom y)) (QuotientGroup.mk k) =
      QuotientGroup.mk (K.normalizerMonoidHom y k)
    exact QuotientGroup.congr_mk (center K) (center K) (K.normalizerMonoidHom y)
      (Subgroup.map_center_eq (K.normalizerMonoidHom y)) k
  rw [h1]
  exact congrArg (fun z : K => QuotientGroup.mk z)
    (Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; exact hk.symm))

theorem actPerm_spec (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) (y : normalizer (K : Set X))
    (k k' : K) (hk : (k' : X) = y * k * y⁻¹) :
    ((e (QuotientGroup.mk k') : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      actPerm K e y * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) *
        (actPerm K e y)⁻¹ := by
  have hconj : MulAut.conjNormal (actPerm K e y) = MulAut.congr e (actQuot K y) := by
    change conjAutAlt8 (actPerm K e y) = MulAut.congr e (actQuot K y)
    simp only [actPerm, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  have h2 : ((MulAut.conjNormal (actPerm K e y)) (e (QuotientGroup.mk k)) : Perm (Fin 8)) =
      actPerm K e y * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) *
        (actPerm K e y)⁻¹ :=
    MulAut.conjNormal_apply _ _
  have h3 : ((MulAut.congr e (actQuot K y)) (e (QuotientGroup.mk k)) : Perm (Fin 8)) =
      ((e (QuotientGroup.mk k') : alternatingGroup (Fin 8)) : Perm (Fin 8)) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rw [actQuot_apply_mk y k k' hk]
  rw [← hconj] at h3
  rw [← h3]
  exact h2

theorem actPerm_eq_of_spec (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    (y : normalizer (K : Set X)) {σ : Perm (Fin 8)}
    (hσ : ∀ k k' : K, (k' : X) = y * k * y⁻¹ →
      ((e (QuotientGroup.mk k') : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
        σ * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) * σ⁻¹) :
    actPerm K e y = σ := by
  let π := actPerm K e y
  have hπspec : ∀ k k' : K, (k' : X) = y * k * y⁻¹ →
      ((e (QuotientGroup.mk k') : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
        π * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) * π⁻¹ := by
    intro k k' hk
    exact actPerm_spec e y k k' hk
  have hcomm : ∀ a ∈ alternatingGroup (Fin 8), (σ⁻¹ * π) * a = a * (σ⁻¹ * π) := by
    intro a ha
    obtain ⟨q, hq⟩ := e.surjective ⟨a, ha⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have ha' : a = ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) :=
      (congrArg Subtype.val hq).symm
    rw [ha']
    set k' : K := ⟨(y : X) * (k : X) * (y : X)⁻¹,
      (Subgroup.mem_normalizer_iff.1 y.2 k).1 k.2⟩ with hk'def
    have hk' : (k' : X) = (y : X) * (k : X) * (y : X)⁻¹ := rfl
    have hA := hπspec k k' hk'
    have hB := hσ k k' hk'
    have heq : π * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) * π⁻¹ =
        σ * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) * σ⁻¹ := by
      rw [← hA, hB]
    calc (σ⁻¹ * π) * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8))
        = σ⁻¹ * (π * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) * π⁻¹)
            * π := by group
      _ = σ⁻¹ * (σ * ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8))
            * σ⁻¹) * π := by rw [heq]
      _ = ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8))
            * (σ⁻¹ * π) := by group
  have h1 : σ⁻¹ * π = 1 :=
    CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating (α := Fin 8)
      (by rw [Nat.card_fin]; norm_num) hcomm
  have hπσ : π = σ := by
    calc π = σ * (σ⁻¹ * π) := by group
      _ = σ * 1 := by rw [h1]
      _ = σ := by simp
  exact hπσ

theorem actPerm_of_mem (e : K ⧸ center K ≃* alternatingGroup (Fin 8)) (k : K)
    (hk : (k : X) ∈ normalizer (K : Set X)) :
    actPerm K e ⟨k, hk⟩ = ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) := by
  refine actPerm_eq_of_spec e ⟨k, hk⟩ ?_
  intro k₁ k₁' hk₁
  have hkk : k₁' = k * k₁ * k⁻¹ := by
    apply Subtype.ext
    simpa using hk₁
  rw [hkk]
  simp [map_mul]

theorem actPerm_of_mem_centralizer (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    (y : normalizer (K : Set X)) (hy : (y : X) ∈ centralizer (K : Set X)) : actPerm K e y = 1 := by
  refine actPerm_eq_of_spec e y ?_
  intro k k' hk
  have hcent := Subgroup.mem_centralizer_iff.1 hy k k.2
  have hk' : k' = k := by
    apply Subtype.ext
    rw [hk, ← hcent, Subgroup.coe_inv]
    group
  rw [hk']
  simp

theorem mem_centralizer_of_actPerm_eq_one (e : K ⧸ center K ≃* alternatingGroup (Fin 8))
    (hK : ⁅K, K⁆ = K) (y : normalizer (K : Set X)) (h : actPerm K e y = 1) :
    (y : X) ∈ centralizer (K : Set X) := by
  classical
  let φ : MulAut K := K.normalizerMonoidHom y
  have hspec : ∀ k : K,
      ((e (QuotientGroup.mk (φ k)) : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
        ((e (QuotientGroup.mk k) : alternatingGroup (Fin 8)) : Perm (Fin 8)) := by
    intro k
    have h1 := actPerm_spec e y k (φ k)
      (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv])
    rw [h1, h]
    simp
  have hmk : ∀ k : K, (φ k : K ⧸ center K) = (k : K ⧸ center K) := by
    intro k
    exact e.injective (Subtype.ext (hspec k))
  have hc : ∀ k : K, (φ k)⁻¹ * k ∈ Subgroup.center K := by
    intro k
    rw [← QuotientGroup.eq]
    exact hmk k
  have hf_center : ∀ k : K, φ k * k⁻¹ ∈ Subgroup.center K := by
    intro k
    have hcc : ((φ k)⁻¹ * k)⁻¹ ∈ Subgroup.center K :=
      (Subgroup.center K).inv_mem (hc k)
    have hφc : φ k * k⁻¹ = k * ((φ k)⁻¹ * k)⁻¹ * k⁻¹ := by group
    rw [hφc]
    convert hcc using 1
    rw [Subgroup.mem_center_iff.1 hcc k]
    group
  let f : K →* K :=
  { toFun := fun k => φ k * k⁻¹
    map_one' := by simp
    map_mul' := fun a b => wt_normalizerHom_mul_inv_mul_comm y (hf_center b) }
  let F : K →* Subgroup.center K := f.codRestrict (Subgroup.center K) hf_center
  haveI : Group.IsPerfect K := (Subgroup.isPerfect_iff).mpr hK
  have hcomm : commutator K ≤ F.ker := Abelianization.commutator_subset_ker F
  have hker_top : F.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top]
    exact hcomm
  have hF : F = 1 := MonoidHom.ker_eq_top_iff.mp hker_top
  have hφk : ∀ k : K, φ k = k := by
    intro k
    have h1 : f k = 1 := by
      have h2 : F k = 1 := by rw [hF]; rfl
      have := congrArg Subtype.val h2
      simpa [F] using this
    have h2 : φ k * k⁻¹ = 1 := by simpa [f] using h1
    exact mul_inv_eq_one.mp h2
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hval : (y : X) * k * (y : X)⁻¹ = k := by
    have h' := congrArg Subtype.val (hφk ⟨k, hk⟩)
    simpa [φ] using h'
  have h' : (y : X) * k = k * (y : X) := by
    calc (y : X) * k = ((y : X) * k * (y : X)⁻¹) * (y : X) := by group
      _ = k * (y : X) := by rw [hval]
  exact h'.symm

end CFSG.OddStandard.AltStdSec.SwapPartner
