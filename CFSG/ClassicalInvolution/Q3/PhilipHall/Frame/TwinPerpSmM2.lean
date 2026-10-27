module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallBlock

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.M2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
  CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

set_option linter.unusedSectionVars false


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem twin_mem_of_mem_of_ne_one (h : PerpHypS n Y R S t) {N : Subgroup Y} {x : Y}
    (hxK : x ∈ tightCore R) (hxN : x ∈ N) {k : ℕ} (hx : x ^ 2 ^ k = 1) (hx1 : x ≠ 1) : t ∈ N := by
  have hz : IsUniqueInvolution (tightCore R) t := uniqueInv_core h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h'
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact absurd hm hx1
    · exact h'
  have hy : orderOf (x ^ 2 ^ (m - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hm]; exact pow_dvd_pow 2 (Nat.sub_le m 1)), hm,
      Nat.pow_div (Nat.sub_le m 1) two_pos]
    have : m - (m - 1) = 1 := by omega
    rw [this, pow_one]
  have hy1 : x ^ 2 ^ (m - 1) ≠ 1 := fun h' => by
    rw [h', orderOf_one] at hy
    omega
  have hyK : x ^ 2 ^ (m - 1) ∈ tightCore R := (tightCore R).pow_mem hxK _
  have hy2 : (x ^ 2 ^ (m - 1)) * (x ^ 2 ^ (m - 1)) = 1 := by
    have := pow_orderOf_eq_one (x ^ 2 ^ (m - 1))
    rwa [hy, pow_two] at this
  have hyt : x ^ 2 ^ (m - 1) = t := (hz.unique _ hyK hy2).resolve_left hy1
  rw [← hyt]
  exact N.pow_mem hxN _

theorem twin_mem_of_noQ8Outer (h : PerpHypS n Y R S t) {N : Subgroup Y} [N.Normal]
    (hC : Subgroup.centralizer (N : Set Y) = ⊥)
    (hO : ∀ φ : QuaternionGroup 2 →* Outer N, ¬ Function.Injective φ) : t ∈ N := by
  by_contra htN
  obtain ⟨φ, hφ, hφK⟩ := exists_q8 h
  apply hO ((outerHom N).comp φ)
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  have hxN : φ x ∈ N := (outerHom_eq_one_iff hC).mp hx
  have hφx : φ x ≠ 1 := fun h' => hx1 (hφ (h'.trans (map_one φ).symm))
  have h8' : x ^ 8 = 1 := orderOf_dvd_iff_pow_eq_one.mp (orderOf_q8_dvd x)
  have h8 : φ x ^ 2 ^ 3 = 1 := by
    rw [← map_pow, show (2 : ℕ) ^ 3 = 8 by norm_num, h8', map_one]
  exact htN (twin_mem_of_mem_of_ne_one h (hφK x) hxN h8 hφx)

theorem twin_false_of_model (h : PerpHypS n Y R S t) {P : Type} [Group P]
    (e : ↥(genFittingFStar Y) ≃* P) (htT : t ∈ genFittingFStar Y) {u : P}
    (hu : e ⟨t, htT⟩ = u) (H₁ H₂ : Subgroup P)
    (hK₁ : CFSG.Open.IsComponentOf H₁ (Subgroup.centralizer ({u} : Set P)))
    (hK₂ : CFSG.Open.IsComponentOf H₂ (Subgroup.centralizer ({u} : Set P)))
    (hA : NoQ8Fix P (H₁ ⊔ H₂)) : False := by
  have hq₁ : CFSG.IsQuasisimple ↥H₁ := isQuasisimple_of_open hK₁.2.2
  have hq₂ : CFSG.IsQuasisimple ↥H₂ := isQuasisimple_of_open hK₂.2.2
  have hs₁ := hK₁.2.1
  have hs₂ := hK₂.2.1
  haveI hsimple := h.core.simple
  haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
    Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
  have hK₀solv : Group.IsSolvable ↥(tightCore R) := isSolvable_core h
  have hsubK : CFSG.Open.IsSubnormal (tightCore R) (Subgroup.centralizer ({t} : Set Y)) :=
    isSubnormal_core h
  have hcomp : ∀ H : Subgroup P, CFSG.IsQuasisimple ↥H →
      CFSG.Open.IsSubnormal H (Subgroup.centralizer ({u} : Set P)) →
      CFSG.IsQuasisimple ↥((H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype) ∧
        CFSG.Open.IsSubnormal ((H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype)
          (Subgroup.centralizer ({t} : Set Y)) := by
    intro H hq hs
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.equivMapOfInjective H e.symm.toMonoidHom e.symm.injective).trans
        (Subgroup.equivMapOfInjective _ (genFittingFStar Y).subtype
          (genFittingFStar Y).subtype_injective)) hq, ?_⟩
    have h1 := (hs.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype
    rw [← hu, map_centralizer_mulEquiv e ⟨t, htT⟩,
      TwinSmall.map_centralizer_subtype (genFittingFStar Y) ⟨t, htT⟩] at h1
    exact h1.trans (isSubnormal_inf_normal _ (genFittingFStar Y))
  obtain ⟨hq₁', hs₁'⟩ := hcomp H₁ hq₁ hs₁
  obtain ⟨hq₂', hs₂'⟩ := hcomp H₂ hq₂ hs₂
  have hc₁ := commute_of_solvable_subnormal hs₁' hq₁' hsubK hK₀solv
  have hc₂ := commute_of_solvable_subnormal hs₂' hq₂' hsubK hK₀solv
  obtain ⟨φ, hφi, hφK⟩ := exists_q8 h
  let ψ : QuaternionGroup 2 →* MulAut P :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp φ)
  have hψ : ∀ q p, ψ q p = e ⟨φ q * (e.symm p : Y) * (φ q)⁻¹, by
      exact hTn.conj_mem _ (e.symm p).2 _⟩ := fun q p => rfl
  refine hA ψ ?_ ?_
  · rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : φ q ∈ Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h2 := congrArg (fun α : MulAut P => α (e ⟨x, hx⟩)) hq
      simp only [hψ, MulAut.one_apply, MulEquiv.symm_apply_apply] at h2
      have h3 := congrArg (fun y : ↥(genFittingFStar Y) => (y : Y)) (e.injective h2)
      simp only at h3
      calc x * φ q = (φ q * x * (φ q)⁻¹) * φ q := by rw [h3]
        _ = φ q * x := by group
    rw [hC, Subgroup.mem_bot] at h1
    exact hφi (h1.trans (map_one φ).symm)
  · intro a p hp
    let Fix : Subgroup P :=
      { carrier := {p | ψ a p = p}
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [map_mul, hx, hy]
        one_mem' := map_one _
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          rw [map_inv, hx] }
    have hfixH : ∀ H : Subgroup P,
        (∀ x ∈ (H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype,
          ∀ y ∈ tightCore R, x * y = y * x) → H ≤ Fix := by
      intro H hcH p hp
      show ψ a p = p
      rw [hψ]
      have hmem : ((e.symm p : ↥(genFittingFStar Y)) : Y) ∈
          (H.map e.symm.toMonoidHom).map (genFittingFStar Y).subtype :=
        ⟨e.symm p, ⟨p, hp, rfl⟩, rfl⟩
      have hcomm := hcH _ hmem (φ a) (hφK a)
      have hx : φ a * ((e.symm p : ↥(genFittingFStar Y)) : Y) * (φ a)⁻¹ =
          ((e.symm p : ↥(genFittingFStar Y)) : Y) := by
        rw [← hcomm]
        group
      have : (⟨φ a * (e.symm p : Y) * (φ a)⁻¹, hTn.conj_mem _ (e.symm p).2 _⟩ :
          ↥(genFittingFStar Y)) = e.symm p := Subtype.ext hx
      rw [this, MulEquiv.apply_symm_apply]
    exact (sup_le (hfixH H₁ hc₁) (hfixH H₂ hc₂) hp : p ∈ Fix)

section Block

open CFSG.ClassicalInvolution.Q3.TA3.Frame
open scoped MatrixGroups

theorem twin_false_of_simple (h : PerpHypS n Y R S t) {P : Type} [Group P]
    (e : ↥(genFittingFStar Y) ≃* P) (htT : t ∈ genFittingFStar Y) {u : P}
    (hu : e ⟨t, htT⟩ = u) {H : Subgroup P} [IsSimpleGroup H] [Group.IsPerfect H]
    (hHt : H ≤ Subgroup.centralizer ({u} : Set P))
    (hmax : ∀ M : Subgroup P, M ≤ Subgroup.centralizer ({u} : Set P) → ⁅M, M⁆ = M → M ≤ H)
    (hfix : NoQ8Fix P H) : False := by
  have hK : IsComponentOf H (Subgroup.centralizer ({u} : Set P)) :=
    isComponentOf_of_normal hHt (FL4.normal_of_perfect_max hHt
      (Subgroup.isPerfect_iff.mp inferInstance) hmax) FL4.isQuasisimple_of_simple
  exact twin_false_of_model h e htT hu H H hK hK (by rw [sup_idem]; exact hfix)

theorem twin_false_of_block (h : PerpHypS n Y R S t) {P : Type} [Group P]
    (e : ↥(genFittingFStar Y) ≃* P) (htT : t ∈ genFittingFStar Y) {u : P}
    (hu : e ⟨t, htT⟩ = u) {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (β : SL(2, F) × SL(2, F) →* P) (hinl : Function.Injective (β.comp (MonoidHom.inl _ _)))
    (hinr : Function.Injective (β.comp (MonoidHom.inr _ _)))
    (hHt : β.range ≤ Subgroup.centralizer ({u} : Set P)) (hHp : ⁅β.range, β.range⁆ = β.range)
    (hmax : ∀ M : Subgroup P, M ≤ Subgroup.centralizer ({u} : Set P) → ⁅M, M⁆ = M →
      M ≤ β.range)
    (hfix : NoQ8Fix P β.range) : False := by
  set C := Subgroup.centralizer ({u} : Set P) with hC
  have hnH := FL4.normal_of_perfect_max hHt hHp hmax
  have hle1 : (β.comp (MonoidHom.inl _ _)).range ≤ β.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have hle2 : (β.comp (MonoidHom.inr _ _)).range ≤ β.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, rfl⟩
  have hK1 : IsComponentOf (β.comp (MonoidHom.inl _ _)).range C :=
    ⟨hle1.trans hHt, IsSubnormal.step hle1 (FL4.normal_inl β) (IsSubnormal.step hHt hnH
      (IsSubnormal.refl C)), isQuasisimple_of_equiv_sl2 h4 (MonoidHom.ofInjective hinl).symm⟩
  have hK2 : IsComponentOf (β.comp (MonoidHom.inr _ _)).range C :=
    ⟨hle2.trans hHt, IsSubnormal.step hle2 (FL4.normal_inr β) (IsSubnormal.step hHt hnH
      (IsSubnormal.refl C)), isQuasisimple_of_equiv_sl2 h4 (MonoidHom.ofInjective hinr).symm⟩
  refine twin_false_of_model h e htT hu _ _ hK1 hK2 (noQ8Fix_mono hfix ?_)
  rintro _ ⟨⟨a, b⟩, rfl⟩
  have e' : β (a, b) = (β.comp (MonoidHom.inl _ _)) a * (β.comp (MonoidHom.inr _ _)) b := by
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply,
      MonoidHom.inr_apply]
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  rw [e']
  exact mul_mem (Subgroup.mem_sup_left ⟨a, rfl⟩) (Subgroup.mem_sup_right ⟨b, rfl⟩)

end Block

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.M2
