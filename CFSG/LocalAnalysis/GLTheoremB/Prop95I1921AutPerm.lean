module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

section AutPerm

variable {K : Type*} [Group K]

@[expose] noncomputable def quotAutOfCentre (φ : MulAut K) : MulAut (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) φ (Subgroup.map_center_eq φ)

theorem quotAutOfCentre_mk (φ : MulAut K) (x : K) :
    quotAutOfCentre φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk _ _ _ _ _

@[expose] noncomputable def quotAutOfCentreHom : MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun := quotAutOfCentre
  map_one' := MulEquiv.ext fun q => by
    induction q using QuotientGroup.induction_on with
    | H l => simp [quotAutOfCentre_mk]
  map_mul' a b := MulEquiv.ext fun q => by
    induction q using QuotientGroup.induction_on with
    | H l => simp [quotAutOfCentre_mk]

theorem eq_one_of_forall_mk_eq_aut (hperf : commutator K = ⊤) (φ : MulAut K)
    (h : ∀ x : K, (QuotientGroup.mk (φ x) : K ⧸ Subgroup.center K) = QuotientGroup.mk x) :
    φ = 1 := by
  have hcent : ∀ x : K, x⁻¹ * φ x ∈ Subgroup.center K := by
    intro x
    have : (QuotientGroup.mk (x⁻¹ * φ x) : K ⧸ Subgroup.center K) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h x]
      exact inv_mul_cancel _
    exact (QuotientGroup.eq_one_iff _).1 this
  let c : K →* K :=
    { toFun := fun x => x⁻¹ * φ x
      map_one' := by simp
      map_mul' := fun x y => by
        have hx := (Subgroup.mem_center_iff.1 (hcent x)) (y⁻¹)
        calc (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by simp [mul_assoc]
          _ = (x⁻¹ * φ x) * y⁻¹ * φ y := by
            rw [mul_assoc y⁻¹, ← hx]
            simp [mul_assoc]
          _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by simp [mul_assoc] }
  have hker : commutator K ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.1 (hcent x) (c y)).symm
  have hc1 : ∀ x : K, c x = 1 := fun x => by
    have : x ∈ c.ker := hker (hperf ▸ Subgroup.mem_top x)
    exact this
  refine MulEquiv.ext fun x => ?_
  have h2 : x⁻¹ * φ x = 1 := hc1 x
  show φ x = x
  exact (inv_mul_eq_one.1 h2).symm

end AutPerm

theorem exists_autToPerm_of_perfect {K : Type*} [Group K] (hperf : commutator K = ⊤) {n : ℕ}
    (hn : 5 ≤ n) (hn6 : n ≠ 6) (e : (K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin n)) :
    ∃ θ : MulAut K →* Equiv.Perm (Fin n), Function.Injective θ ∧
      (∀ φ : MulAut K, InducesOn e φ (MulAut.conjNormal (H := alternatingGroup (Fin n)) (θ φ))) ∧
      (∀ k : K, θ (MulAut.conj k) =
        ((e (QuotientGroup.mk k) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  let c : Equiv.Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n))) hbij
  let θ : MulAut K →* Equiv.Perm (Fin n) :=
    c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp quotAutOfCentreHom)
  have hθ : ∀ φ : MulAut K, MulAut.conjNormal (H := alternatingGroup (Fin n)) (θ φ) =
      MulAut.congr e (quotAutOfCentre φ) := by
    intro φ
    exact c.apply_symm_apply (MulAut.congr e (quotAutOfCentre φ))
  have hind : ∀ (φ : MulAut K) (a : K),
      e (QuotientGroup.mk (φ a)) =
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) (θ φ)) (e (QuotientGroup.mk a)) := by
    intro φ a
    rw [hθ, MulAut.congr_apply]
    simp [quotAutOfCentre_mk]
  refine ⟨θ, ?_, fun φ a => hind φ a, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 : MulAut.conjNormal (H := alternatingGroup (Fin n)) (θ φ) = 1 := by
      rw [hφ, map_one]
    rw [hθ] at h1
    have h2 : quotAutOfCentre φ = 1 :=
      (MulAut.congr e).injective (by rw [h1, map_one])
    refine eq_one_of_forall_mk_eq_aut hperf φ fun x => ?_
    have h3 := congrArg (fun ψ : MulAut (K ⧸ Subgroup.center K) => ψ (QuotientGroup.mk x)) h2
    simpa [quotAutOfCentre_mk] using h3
  · intro k
    apply hbij.1
    rw [hθ, MulAut.conjNormal_val]
    refine MulEquiv.ext fun x => ?_
    obtain ⟨q, rfl⟩ := e.surjective x
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [MulAut.congr_apply]
      simp [quotAutOfCentre_mk]

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
