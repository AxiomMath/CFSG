module

public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
public import CFSG.LocalAnalysis.GLTheoremB.AltAut

public section

namespace CFSG.LocalAnalysis.GLTheoremB

namespace S7

open Equiv Equiv.Perm

section Aut

open scoped commutatorElement

variable {L : Type*} [Group L]

@[expose] noncomputable def nuHom (e : (L ⧸ Subgroup.center L) ≃* ↥Alt7) : MulAut L →* S :=
  (permOfAut e).comp (quotAutHom (Subgroup.center L) (MonoidHom.id (MulAut L))
    (fun φ => Subgroup.map_center_eq φ))

theorem nuHom_spec (e : (L ⧸ Subgroup.center L) ≃* ↥Alt7) (φ : MulAut L) (x : L) :
    ((e (QuotientGroup.mk (φ x)) : ↥Alt7) : S) =
      nuHom e φ * (e (QuotientGroup.mk x) : S) * (nuHom e φ)⁻¹ := by
  have h := permOfAut_spec e (quotAutHom (Subgroup.center L) (MonoidHom.id (MulAut L))
    (fun φ => Subgroup.map_center_eq φ) φ) (QuotientGroup.mk x)
  have h2 := quotAutHom_mk (Subgroup.center L) (MonoidHom.id (MulAut L))
    (fun φ => Subgroup.map_center_eq φ) φ x
  have h3 : (quotAutHom (Subgroup.center L) (MonoidHom.id (MulAut L))
      (fun φ => Subgroup.map_center_eq φ) φ) (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := h2
  rw [h3] at h
  exact h

theorem eq_one_of_forall_mk_eq (hperf : commutator L = ⊤) (φ : MulAut L)
    (h : ∀ x : L, (QuotientGroup.mk (φ x) : L ⧸ Subgroup.center L) = QuotientGroup.mk x) :
    φ = 1 := by
  have hcent : ∀ x : L, x⁻¹ * φ x ∈ Subgroup.center L := by
    intro x
    have : (QuotientGroup.mk (x⁻¹ * φ x) : L ⧸ Subgroup.center L) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h x]
      exact inv_mul_cancel _
    exact (QuotientGroup.eq_one_iff _).1 this
  let c : L →* L :=
    { toFun := fun x => x⁻¹ * φ x
      map_one' := by simp
      map_mul' := fun x y => by
        have hx := (Subgroup.mem_center_iff.1 (hcent x)) (y⁻¹)
        calc (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by simp [mul_assoc]
          _ = (x⁻¹ * φ x) * y⁻¹ * φ y := by
            rw [mul_assoc y⁻¹, ← hx]
            simp [mul_assoc]
          _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by simp [mul_assoc] }
  have hker : commutator L ≤ c.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.1 (hcent x) (c y)).symm
  have hc1 : ∀ x : L, c x = 1 := fun x => by
    have : x ∈ c.ker := hker (hperf ▸ Subgroup.mem_top x)
    exact this
  refine MulEquiv.ext fun x => ?_
  have := hc1 x
  have h2 : x⁻¹ * φ x = 1 := this
  show φ x = x
  exact (inv_mul_eq_one.1 h2).symm

theorem nuHom_injective (e : (L ⧸ Subgroup.center L) ≃* ↥Alt7) (hperf : commutator L = ⊤) :
    Function.Injective (nuHom e) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  refine eq_one_of_forall_mk_eq hperf φ fun x => ?_
  have h := nuHom_spec e φ x
  rw [hφ, inv_one, one_mul, mul_one] at h
  have h2 : e (QuotientGroup.mk (φ x)) = e (QuotientGroup.mk x) := Subtype.ext h
  exact e.injective h2

theorem nuHom_conj (e : (L ⧸ Subgroup.center L) ≃* ↥Alt7) (l : L) :
    nuHom e (MulAut.conj l) = ((e (QuotientGroup.mk l) : ↥Alt7) : S) := by
  apply conjEquiv.injective
  refine MulEquiv.ext fun a => ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm a)
  have hxa : e (QuotientGroup.mk x) = a := by rw [hx]; simp
  apply Subtype.ext
  have h := nuHom_spec e (MulAut.conj l) x
  rw [← hxa]
  simp only [conjEquiv, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply]
  rw [← h]
  simp [MulAut.conj_apply]

end Aut

section Normalizer

variable {H : Type*} [Group H]

@[expose] noncomputable def FL (L : Subgroup H) (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Alt7) :
    ↥(Subgroup.normalizer (L : Set H)) →* S :=
  (nuHom e).comp L.normalizerMonoidHom

theorem FL_of_mem (L : Subgroup H) (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Alt7) (l : ↥L) :
    FL L e ⟨(l : H), Subgroup.le_normalizer l.2⟩ = ((e (QuotientGroup.mk l) : ↥Alt7) : S) := by
  have h : L.normalizerMonoidHom ⟨(l : H), Subgroup.le_normalizer l.2⟩ = MulAut.conj l := by
    ext x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp [MulAut.conj_apply]
  show nuHom e (L.normalizerMonoidHom ⟨(l : H), Subgroup.le_normalizer l.2⟩) = _
  rw [h, nuHom_conj]

theorem FL_of_centralizes (L : Subgroup H) (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Alt7) {c : H}
    (hc : c ∈ Subgroup.centralizer (L : Set H)) :
    FL L e ⟨c, Subgroup.centralizer_le_normalizer (L : Set H) hc⟩ = 1 := by
  have h : L.normalizerMonoidHom ⟨c, Subgroup.centralizer_le_normalizer (L : Set H) hc⟩ = 1 := by
    ext x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have := (Subgroup.mem_centralizer_iff.1 hc) (x : H) x.2
    show c * (x : H) * c⁻¹ = (x : H)
    rw [← this]
    group
  show nuHom e (L.normalizerMonoidHom ⟨c, _⟩) = 1
  rw [h, map_one]

theorem centralizes_of_FL_eq_one (L : Subgroup H) (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Alt7)
    (hperf : commutator ↥L = ⊤) {x : H} (hx : x ∈ Subgroup.normalizer (L : Set H))
    (h : FL L e ⟨x, hx⟩ = 1) : x ∈ Subgroup.centralizer (L : Set H) := by
  have h1 : L.normalizerMonoidHom ⟨x, hx⟩ = 1 :=
    nuHom_injective e hperf (h.trans (map_one (nuHom e)).symm)
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h2 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : H)) h1
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
  calc l * x = (x * l * x⁻¹) * x := by rw [h2]
    _ = x * l := by group

end Normalizer

end S7

end CFSG.LocalAnalysis.GLTheoremB
