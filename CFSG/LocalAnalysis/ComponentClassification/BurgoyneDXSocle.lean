module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSpin
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBFinal
public import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne
open CFSG.ComponentClassification.UnbalancingLocal
open scoped MatrixGroups

section Fix

variable {L : Type} [Group L] [Finite L]

theorem apply_eq_of_map_eq {Q : Subgroup L} {F : Type} [Field F]
    (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, F)) {c : L} (hcZ : c ∈ center L) (hcQ : c ∈ Q)
    (hc2 : orderOf c = 2) (σ : MulAut L) (hσ : Q.map σ.toMonoidHom = Q) : σ c = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσc : σ c ∈ Q := hσ ▸ mem_map_of_mem _ hcQ
  have hσZ : σ c ∈ center L := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := σ.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hcZ g']
  set d : Q := ⟨c, hcQ⟩⁻¹ * ⟨σ c, hσc⟩ with hd
  have himZ : ∀ x : Q, (x : L) ∈ center L →
      e (QuotientGroup.mk' (pPrimeCore 2 Q) x) ∈ center (SL(2, F)) := by
    intro x hx
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    obtain ⟨y'', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 Q) y'
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (mem_center_iff.mp hx y'')
  have hsq : ∀ z ∈ center (SL(2, F)), z = 1 ∨ z = -1 := by
    intro z hz
    obtain ⟨r, hr, hrz⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).1 hz
    have hr2 : r * r = 1 := by
      have : r ^ 2 = 1 := by simpa using hr
      rwa [pow_two] at this
    rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
    · left
      ext i j
      rw [← hrz, Matrix.SpecialLinearGroup.coe_one]
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
    · right
      ext i j
      rw [← hrz, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hodd : ∀ x ∈ pPrimeCore 2 Q, Odd (orderOf x) := by
    intro x hx
    have hdvd : orderOf (⟨x, hx⟩ : pPrimeCore 2 Q) ∣ Nat.card (pPrimeCore 2 Q) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card)
  have himne : ∀ x : Q, orderOf (x : L) = 2 → e (QuotientGroup.mk' (pPrimeCore 2 Q) x) ≠ 1 := by
    intro x hx h
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have := hodd x h
    rw [← Subgroup.orderOf_coe, hx] at this
    exact (Nat.not_even_iff_odd.mpr this) even_two
  have hσc2 : orderOf (σ c) = 2 := by rw [MulEquiv.orderOf_eq]; exact hc2
  have hc' := hsq _ (himZ ⟨c, hcQ⟩ hcZ)
  have hσc' := hsq _ (himZ ⟨σ c, hσc⟩ hσZ)
  have hc'' := hc'.resolve_left (himne ⟨c, hcQ⟩ hc2)
  have hσc'' := hσc'.resolve_left (himne ⟨σ c, hσc⟩ hσc2)
  have hdO : d ∈ pPrimeCore 2 Q := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← MulEquiv.map_eq_one_iff e,
      hd, map_mul, map_mul, map_inv, map_inv, hc'', hσc'', inv_mul_cancel]
  have hd2 : (d : L) * d = 1 := by
    have hc2' : c * c = 1 := by rw [← pow_two, ← hc2, pow_orderOf_eq_one]
    have hσ2 : σ c * σ c = 1 := by rw [← map_mul, hc2', map_one]
    change (c⁻¹ * σ c) * (c⁻¹ * σ c) = 1
    rw [mul_assoc, ← mul_assoc (σ c), ← (mem_center_iff.mp hσZ c⁻¹), mul_assoc, ← mul_assoc,
      hσ2, mul_one, ← mul_inv_rev, hc2', inv_one]
  have hdodd := hodd d hdO
  have hd1 : (d : L) = 1 := by
    have h12 : orderOf (d : L) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hd2])
    rcases (Nat.dvd_prime Nat.prime_two).1 h12 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [← Subgroup.orderOf_coe, h] at hdodd
      exact absurd hdodd (by decide)
  change c⁻¹ * σ c = 1 at hd1
  exact (inv_mul_eq_one.mp hd1).symm

end Fix


section Socle

attribute [local instance] GeneralizedFitting.normal

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)

@[expose] def socleHom : K ⧸ pPrimeCore 2 K →* GeneralizedFitting.subgroup (rhoZ K).range :=
  (liftHom K).codRestrict _ fun x => by
    rw [← liftHom_range_eq K hq hsimple hnab]
    exact ⟨x, rfl⟩

theorem coe_socleHom (x : K ⧸ pPrimeCore 2 K) :
    (socleHom K hq hsimple hnab x : (rhoZ K).range) = liftHom K x := rfl

theorem socleHom_surjective : Function.Surjective (socleHom K hq hsimple hnab) := by
  rintro ⟨y, hy⟩
  rw [← liftHom_range_eq K hq hsimple hnab] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

theorem ker_socleHom : (socleHom K hq hsimple hnab).ker = center (K ⧸ pPrimeCore 2 K) := by
  rw [← ker_liftHom K hq]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem socleHom_phiO (g : J) (x : K ⧸ pPrimeCore 2 K) :
    socleHom K hq hsimple hnab (phiO K g x) =
      MulAut.conjNormal ((rhoZ K).rangeRestrict g) (socleHom K hq hsimple hnab x) := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, coe_socleHom, coe_socleHom, liftHom_conj]

theorem map_ker_socleHom (s : MulAut (K ⧸ pPrimeCore 2 K)) :
    (socleHom K hq hsimple hnab).ker.map (s : K ⧸ pPrimeCore 2 K →* K ⧸ pPrimeCore 2 K) =
      (socleHom K hq hsimple hnab).ker := by
  rw [ker_socleHom, ← MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance s

@[expose] def socleAut (s : MulAut (K ⧸ pPrimeCore 2 K)) :
    MulAut (GeneralizedFitting.subgroup (rhoZ K).range) :=
  descendAut (socleHom K hq hsimple hnab) (socleHom_surjective K hq hsimple hnab) s
    (map_ker_socleHom K hq hsimple hnab s)

theorem socleHom_socleAut (s : MulAut (K ⧸ pPrimeCore 2 K)) (x : K ⧸ pPrimeCore 2 K) :
    socleHom K hq hsimple hnab (s x) =
      socleAut K hq hsimple hnab s (socleHom K hq hsimple hnab x) :=
  (descendAut_apply _ _ _ _ x).symm

end Socle

section Cover

attribute [local instance] GeneralizedFitting.normal

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)
  (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact p.Prime] in
include hq in
theorem exists_cover8 (hp2 : p ≠ 2)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F) :
    ∃ α : Sp8 F →* K ⧸ pPrimeCore 2 K,
      (∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x)) ∧ Function.Surjective α ∧
        center (K ⧸ pPrimeCore 2 K) = (center (Sp8 F)).map α := by
  have hK : ringChar F ≠ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.OrthAut.ringChar_ne_two_of_ne_two (F := F) hp2
  set β : Sp8 F →* (rhoZ K).range := (GeneralizedFitting.subgroup (rhoZ K).range).subtype.comp
    (θ.symm.toMonoidHom.comp (pi8 F)) with hβ
  have hβr : β.range = (liftHom K).range := by
    rw [liftHom_range_eq K hq hsimple hnab]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (θ.symm (pi8 F x)).2
    · intro hy
      obtain ⟨x, hx⟩ := pi8_surjective F (θ ⟨y, hy⟩)
      refine ⟨x, ?_⟩
      change ((θ.symm (pi8 F x) : GeneralizedFitting.subgroup _) : (rhoZ K).range) = y
      rw [hx, MulEquiv.symm_apply_apply]
  have hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* Sp8 F),
      Function.Surjective π → π.ker ≤ center E → IsPGroup 2 π.ker →
        ∃ s : Sp8 F →* E, ∀ x, π (s x) = x := by
    intro E _ _ π hπ hker2 h2'
    obtain ⟨s, hs, -⟩ :=
      CFSG.LieType.Steinberg.spinPlus_central_two_extension_splitting (by norm_num) hK hπ hker2 h2'
    exact ⟨s, hs⟩
  obtain ⟨α, hαβ, hαs, hZ⟩ := exists_cover K hsplit hq hβr
  have hkerβ : β.ker = center (Sp8 F) := by
    rw [← ker_pi8 F]
    ext x
    simp only [hβ, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      have h' : θ.symm (pi8 F x) = 1 := Subtype.ext h
      rwa [MulEquiv.map_eq_one_iff] at h'
    · intro h
      rw [h, map_one]
      rfl
  refine ⟨α, fun x => Subtype.ext (hαβ x), hαs, ?_⟩
  rw [hZ, hkerβ]


instance isPerfect_Sp8' : Group.IsPerfect (Sp8 F) :=
  CFSG.LieType.Universal.Spin.isPerfect_spinGroup_quadPlus (by norm_num)

include hq in
theorem cover_liftAut (hp2 : p ≠ 2) (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F)
    {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x)) (g : J) (x : Sp8 F) :
    α (liftAut F hp2 (socleAction θ ((rhoZ K).rangeRestrict g)) x) = phiO K g (α x) := by
  have key := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
    (θ := socleHom K hq hsimple hnab) (ker_socleHom K hq hsimple hnab).le
    (α.comp (liftAut F hp2 (socleAction θ ((rhoZ K).rangeRestrict g))).toMonoidHom)
    ((phiO K g).toMonoidHom.comp α) fun y => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [hα, pi8_liftAut, socleHom_phiO, hα]
      change θ.symm (θ (MulAut.conjNormal ((rhoZ K).rangeRestrict g) (θ.symm (pi8 F y)))) = _
      rw [MulEquiv.symm_apply_apply]
  exact DFunLike.congr_fun key x

include hq in
theorem cover_liftAut_socleAut (hp2 : p ≠ 2)
    (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F)
    {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x))
    (s : MulAut (K ⧸ pPrimeCore 2 K)) (x : Sp8 F) :
    α (liftAut F hp2 (MulAut.congr θ (socleAut K hq hsimple hnab s)) x) = s (α x) := by
  set γ : MulAut (P8 F) := MulAut.congr θ (socleAut K hq hsimple hnab s) with hγ
  have hcomp : ∀ y, socleHom K hq hsimple hnab (α (liftAut F hp2 γ y)) =
      socleHom K hq hsimple hnab (s (α y)) := by
    intro y
    rw [hα, pi8_liftAut, socleHom_socleAut, hα]
    change θ.symm (θ (socleAut K hq hsimple hnab s (θ.symm (pi8 F y)))) = _
    rw [MulEquiv.symm_apply_apply]
  have key := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
    (θ := socleHom K hq hsimple hnab) (ker_socleHom K hq hsimple hnab).le
    (α.comp (liftAut F hp2 γ).toMonoidHom) (s.toMonoidHom.comp α) hcomp
  exact DFunLike.congr_fun key x

end Cover

end CFSG.ComponentClassification.Burgoyne.DX
