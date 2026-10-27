module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXPicture
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSchur
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXFamily
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXSocle

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open CFSG Subgroup CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.B
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.UnbalancingLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.G2D4Models.Twin
open scoped MatrixGroups Pointwise

section Center

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem map_mem_center8 (σ : Sp8 F ≃* Sp8 F) {z : Sp8 F} (hz : z ∈ center (Sp8 F)) :
    σ z ∈ center (Sp8 F) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := σ.surjective g
  rw [← map_mul, ← map_mul, mem_center_iff.mp hz g']

theorem triality_sq_moves_negOne8 (h2 : (2 : F) ≠ 0) {ρ : Sp8 F ≃* Sp8 F} (hρ : IsTriality ρ) :
    ρ (ρ (negOne8 F)) ≠ negOne8 F := by
  rw [negOne8_eq_z2_mul_z3, map_mul, triality_z2 h2 ρ hρ, triality_z3 h2 ρ hρ, map_mul,
    triality_z3 h2 ρ hρ, triality_z0 h2 ρ hρ]
  intro h
  have h1 := congrArg (spinAction (quadPlus 4 F)) h
  rw [spinAction_z0_mul_z2, spinAction_z2_mul_z3] at h1
  have h3 : -(1 : F) = 1 := by
    have := congrFun (LinearEquiv.congr_fun h1 (Pi.single (Sum.inl 0) 1)) (Sum.inl 0)
    simpa using this
  apply h2
  linear_combination -h3

theorem exists_aut_negOne8 (h2 : (2 : F) ≠ 0) {ρ : Sp8 F ≃* Sp8 F} (hρ : IsTriality ρ)
    {c' : Sp8 F} (hc'Z : c' ∈ center (Sp8 F)) (hc'1 : c' ≠ 1) :
    ∃ σ : Sp8 F ≃* Sp8 F, σ c' = negOne8 F := by
  have hZK := isKleinFour_center8 F h2
  set b := negOne8 F with hb
  have hbZ : b ∈ center (Sp8 F) := negOne8_mem_center F
  have hb1 : b ≠ 1 := negOne8_ne_one F h2
  have hρbZ := map_mem_center8 ρ hbZ
  have hρρbZ := map_mem_center8 ρ hρbZ
  have hρb1 : ρ b ≠ 1 := fun h => hb1 (ρ.injective (by rw [h, map_one]))
  have hρρb1 : ρ (ρ b) ≠ 1 := fun h => hρb1 (ρ.injective (by rw [h, map_one]))
  have hρb : ρ b ≠ b := triality_moves_negOne8 h2 hρ
  have hρρb : ρ (ρ b) ≠ b := triality_sq_moves_negOne8 h2 hρ
  have hρρbρb : ρ (ρ b) ≠ ρ b := fun h => hρb (ρ.injective h)
  by_cases h1 : c' = b
  · exact ⟨MulEquiv.refl _, h1⟩
  by_cases h2' : c' = ρ b
  · exact ⟨ρ.symm, by rw [h2', MulEquiv.symm_apply_apply]⟩
  set B : center (Sp8 F) := ⟨b, hbZ⟩
  set B' : center (Sp8 F) := ⟨ρ b, hρbZ⟩
  have hB1 : B ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hB'1 : B' ≠ 1 := fun h => hρb1 (congrArg Subtype.val h)
  have hBB' : B ≠ B' := fun h => hρb (congrArg Subtype.val h).symm
  have hc : (⟨c', hc'Z⟩ : center (Sp8 F)) = B * B' :=
    IsKleinFour.eq_mul_of_ne_all hB1 hB'1 hBB' (fun h => hc'1 (congrArg Subtype.val h))
      (fun h => h1 (congrArg Subtype.val h)) (fun h => h2' (congrArg Subtype.val h))
  have hρρ : (⟨ρ (ρ b), hρρbZ⟩ : center (Sp8 F)) = B * B' :=
    IsKleinFour.eq_mul_of_ne_all hB1 hB'1 hBB' (fun h => hρρb1 (congrArg Subtype.val h))
      (fun h => hρρb (congrArg Subtype.val h)) (fun h => hρρbρb (congrArg Subtype.val h))
  have hc'eq : c' = ρ (ρ b) := congrArg Subtype.val (hc.trans hρρ.symm)
  exact ⟨ρ.symm.trans ρ.symm, by
    rw [hc'eq, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]⟩

end Center

section Fix

variable {G L : Type} [Group G] [Group L]

theorem map_perfectLift_le (α : G →* L) {Q : Subgroup L} {β : MulAut G} {τ : MulAut L}
    (hβ : ∀ x, α (β x) = τ (α x)) (hτ : Q.map τ.toMonoidHom = Q) :
    ⁅Q.comap α, Q.comap α⁆.map β.toMonoidHom ≤ ⁅Q.comap α, Q.comap α⁆ := by
  have h1 : (Q.comap α).map β.toMonoidHom ≤ Q.comap α := by
    rintro _ ⟨x, hx, rfl⟩
    change α (β x) ∈ Q
    rw [hβ, ← hτ]
    exact mem_map_of_mem _ hx
  rw [map_commutator]
  exact commutator_mono h1 h1

theorem apply_eq_of_lift (α : G →* L) {Q : Subgroup L}
    (hinj : ∀ x ∈ ⁅Q.comap α, Q.comap α⁆, α x = 1 → x = 1) {β : MulAut G} {τ : MulAut L}
    (hβ : ∀ x, α (β x) = τ (α x)) (hτ : Q.map τ.toMonoidHom = Q) {c' : G}
    (hc' : c' ∈ ⁅Q.comap α, Q.comap α⁆) (hτc : τ (α c') = α c') : β c' = c' := by
  have hβc' : β c' ∈ ⁅Q.comap α, Q.comap α⁆ :=
    map_perfectLift_le α hβ hτ (mem_map_of_mem _ hc')
  have h := hinj _ (mul_mem hβc' (inv_mem hc')) (by rw [map_mul, map_inv, hβ, hτc, mul_inv_cancel])
  exact mul_inv_eq_one.mp h

end Fix

section Adapted

attribute [local instance] GeneralizedFitting.normal

variable {J : Type} [Group J] [Finite J] (K : Subgroup J) [K.Normal]
  (hq : IsQuasisimple (K ⧸ pPrimeCore 2 K))
  (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup (rhoZ K).range))
  (hnab : ∃ a b : GeneralizedFitting.subgroup (rhoZ K).range, a * b ≠ b * a)
  (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]

omit [Finite F] [Fact p.Prime] [CharP F p]
  in
include hq in
theorem ker_cover8_le_center {θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F}
    {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x)) :
    α.ker ≤ center (Sp8 F) := by
  intro x hx
  have h1 := hα x
  rw [MonoidHom.mem_ker.mp hx, map_one] at h1
  rw [← ker_pi8, MonoidHom.mem_ker]
  exact (MulEquiv.map_eq_one_iff θ.symm).1 h1.symm

omit [Finite F] [Fact p.Prime]
  in
include hq in
theorem isPGroup_ker_cover8 (hp2 : p ≠ 2) {θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F}
    {α : Sp8 F →* K ⧸ pPrimeCore 2 K}
    (hα : ∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x)) : IsPGroup 2 α.ker := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, pow_two]
  exact mul_self_eq_one_of_mem_center8 F (two_ne_zero8 F hp2)
    (ker_cover8_le_center K hq hsimple hnab F hα x.2)

theorem liftAut_congr_mul (hp2 : p ≠ 2) (δ γ : MulAut (P8 F)) :
    liftAut F hp2 (MulAut.congr δ γ) = liftAut F hp2 δ * liftAut F hp2 γ * (liftAut F hp2 δ)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

include hq hsimple hnab in
theorem exists_adapted_picture (hp2 : p ≠ 2) {ρ : Sp8 F ≃* Sp8 F} (htri : IsTriality ρ)
    (θ₀ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F) {t : J} {Y : Subgroup J}
    {s : MulAut (K ⧸ pPrimeCore 2 K)} {Q : Subgroup (K ⧸ pPrimeCore 2 K)} (hQQ : ⁅Q, Q⁆ = Q)
    (hQs : Q ≤ autFixed s) {p₁ n₁ : ℕ} [Fact p₁.Prime] (hp₁ : p₁ ≠ 2)
    (e : Q ⧸ pPrimeCore 2 Q ≃* SL(2, GaloisField p₁ n₁)) {c : K ⧸ pPrimeCore 2 K}
    (hcZ : c ∈ center (K ⧸ pPrimeCore 2 K)) (hcQ : c ∈ Q) (hc2 : orderOf c = 2)
    (hnorm : ∀ g ∈ closure (insert t (Y : Set J)), Q.map (phiO K g).toMonoidHom = Q) :
    ∃ (θ : GeneralizedFitting.subgroup (rhoZ K).range ≃* P8 F)
      (α : Sp8 F →* K ⧸ pPrimeCore 2 K),
      (∀ x, socleHom K hq hsimple hnab (α x) = θ.symm (pi8 F x)) ∧ Function.Surjective α ∧
      α (negOne8 F) = c ∧ negOne8 F ∈ ⁅Q.comap α, Q.comap α⁆ ∧
      (∀ g ∈ closure (insert t (Y : Set J)),
        socleAction θ ((rhoZ K).rangeRestrict g) ∈ projectivePointFamilyAut (Q8 F)) ∧
      MulAut.congr θ (socleAut K hq hsimple hnab s) ∈ projectivePointFamilyAut (Q8 F) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero8 F hp2
  have hF₁ : ringChar (GaloisField p₁ n₁) ≠ 2 := by
    rw [ringChar.eq (GaloisField p₁ n₁) p₁]
    exact hp₁
  obtain ⟨α₀, hα₀, hα₀s, hZ₀⟩ := exists_cover8 K hq hsimple hnab F hp2 θ₀
  have hker₀ := ker_cover8_le_center K hq hsimple hnab F hα₀
  have hker₀2 := isPGroup_ker_cover8 K hq hsimple hnab F hp2 hα₀
  have key := perfectLift_spec (G := Sp8 F) (L := K ⧸ pPrimeCore 2 K) α₀
    hα₀s hker₀ hker₀2 hQQ (F := GaloisField p₁ n₁) hF₁ e
  have hQ₀map := key.1
  have hQ₀inj := key.2.2
  have hcQ' : c ∈ ⁅Q.comap α₀, Q.comap α₀⁆.map α₀ := by
    rw [hQ₀map]
    exact hcQ
  have hc3 := Subgroup.mem_map.mp hcQ'
  obtain ⟨c', hc'⟩ := hc3
  have hc'Q := hc'.1
  have hc'c := hc'.2
  have hc'Z : c' ∈ center (Sp8 F) := by
    rw [hZ₀] at hcZ
    have hz3 := Subgroup.mem_map.mp hcZ
    obtain ⟨z, hzz⟩ := hz3
    have hz := hzz.1
    have hzc := hzz.2
    have hk : c' * z⁻¹ ∈ α₀.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hc'c, hzc, mul_inv_cancel]
    have := mul_mem (hker₀ hk) hz
    rwa [inv_mul_cancel_right] at this
  have hc'1 : c' ≠ 1 := by
    rintro rfl
    rw [map_one] at hc'c
    rw [← hc'c, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hfixg : ∀ g ∈ closure (insert t (Y : Set J)),
      liftAut F hp2 (socleAction θ₀ ((rhoZ K).rangeRestrict g)) c' = c' := by
    intro g hg
    refine apply_eq_of_lift α₀ hQ₀inj (cover_liftAut K hq hsimple hnab F hp2 θ₀ hα₀ g)
      (hnorm g hg) hc'Q ?_
    rw [hc'c]
    exact apply_eq_of_map_eq e hcZ hcQ hc2 (phiO K g) (hnorm g hg)
  have hsQ : Q.map s.toMonoidHom = Q := by
    refine le_antisymm ?_ fun x hx => ⟨x, hx, hQs hx⟩
    rintro _ ⟨x, hx, rfl⟩
    have : s x = x := hQs hx
    change s x ∈ Q
    rw [this]
    exact hx
  have hfixs : liftAut F hp2 (MulAut.congr θ₀ (socleAut K hq hsimple hnab s)) c' = c' := by
    refine apply_eq_of_lift α₀ hQ₀inj (cover_liftAut_socleAut K hq hsimple hnab F hp2 θ₀ hα₀ s)
      hsQ hc'Q ?_
    rw [hc'c]
    exact hQs hcQ
  have hσ3 := exists_aut_negOne8 h2 htri hc'Z hc'1
  obtain ⟨σ, hσ⟩ := hσ3
  have hσδ : liftAut F hp2 (descend8 F σ) = σ := liftAut_descend8 F hp2 σ
  have hσsymm : σ.symm (negOne8 F) = c' := by rw [← hσ, MulEquiv.symm_apply_apply]
  have hfam : ∀ γ : MulAut (P8 F), liftAut F hp2 γ c' = c' →
      MulAut.congr (descend8 F σ) γ ∈ projectivePointFamilyAut (Q8 F) := by
    intro γ hγ
    rw [← liftAut_negOne8_iff F hp2 htri, liftAut_congr_mul, hσδ, MulAut.mul_apply,
      MulAut.mul_apply]
    change σ (liftAut F hp2 γ (σ.symm (negOne8 F))) = negOne8 F
    rw [hσsymm, hγ, hσ]
  refine ⟨θ₀.trans (descend8 F σ), α₀.comp σ.symm.toMonoidHom, fun x => ?_, ?_, ?_, ?_,
    fun g hg => ?_, ?_⟩
  · change socleHom K hq hsimple hnab (α₀ (σ.symm x)) =
      θ₀.symm ((descend8 F σ).symm (pi8 F x))
    rw [hα₀]
    congr 1
    rw [MulEquiv.eq_symm_apply, ← pi8_descend8, MulEquiv.apply_symm_apply]
  · intro y
    obtain ⟨x, rfl⟩ := hα₀s y
    exact ⟨σ x, by simp⟩
  · change α₀ (σ.symm (negOne8 F)) = c
    rw [hσsymm, hc'c]
  ·
    have hcomap : Q.comap (α₀.comp σ.symm.toMonoidHom) = (Q.comap α₀).map σ.toMonoidHom := by
      ext x
      constructor
      · intro hx
        exact Subgroup.mem_map.mpr ⟨σ.symm x, hx, by simp⟩
      · intro hx
        have hy3 := Subgroup.mem_map.mp hx
        obtain ⟨y, hyy⟩ := hy3
        rw [← hyy.2]
        change α₀ (σ.symm (σ y)) ∈ Q
        rw [MulEquiv.symm_apply_apply]
        exact hyy.1
    rw [hcomap, ← map_commutator, ← hσ]
    exact mem_map_of_mem _ hc'Q
  · rw [socleAction_trans']
    exact hfam _ (hfixg g hg)
  · rw [congr_trans]
    exact hfam _ hfixs

end Adapted

end CFSG.ComponentClassification.Burgoyne.DX
