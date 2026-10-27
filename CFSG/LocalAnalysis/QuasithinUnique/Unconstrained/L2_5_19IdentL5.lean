module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentL5Orth
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabL5Key
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1
open scoped commutatorElement
open Matrix

section Index

theorem commutator_le_of_card_dvd {G : Type*} [Group G] [Finite G] {D K₁ : Subgroup G}
    (hK : K₁ ≤ D) (h : Nat.card D ∣ 2 * Nat.card K₁) : ⁅D, D⁆ ≤ K₁ := by
  have hcard : Nat.card ↥(K₁.subgroupOf D) = Nat.card K₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hidx : (K₁.subgroupOf D).index * Nat.card K₁ = Nat.card D := by
    rw [← hcard]
    exact Subgroup.index_mul_card _
  have hpos : 0 < Nat.card K₁ := Nat.card_pos
  have hdvd : (K₁.subgroupOf D).index ∣ 2 := by
    rw [← hidx] at h
    exact Nat.dvd_of_mul_dvd_mul_right hpos h
  have hne : (K₁.subgroupOf D).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h12 : (K₁.subgroupOf D).index = 1 ∨ (K₁.subgroupOf D).index = 2 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rcases h12 with h1 | h2
  · have htop := Subgroup.index_eq_one.mp h1
    have hDK : D ≤ K₁ := Subgroup.subgroupOf_eq_top.mp htop
    exact hDK (D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb))
  · have key : ⁅(⟨a, ha⟩ : ↥D), (⟨b, hb⟩ : ↥D)⁆ ∈ K₁.subgroupOf D := by
      rw [commutatorElement_def]
      rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
        Subgroup.mul_mem_iff_of_index_two h2, inv_mem_iff, inv_mem_iff]
      tauto
    exact key

theorem card_map_subgroupOf {G Q : Type*} [Group G] [Group Q] {X C : Subgroup G} (hCX : C ≤ X)
    (π : ↥X →* Q) (hπ : Function.Injective π) :
    Nat.card ↥((C.subgroupOf X).map π) = Nat.card ↥C := by
  rw [Subgroup.card_map_of_injective hπ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv

end Index

section Setting

variable {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G}

omit [Finite G] in
theorem IdentSetting.card_cent_dvd_of_outer (hs : IdentSetting X K t) (φ : ↥X ≃* Tab.L5.S)
    (a : Tab.L5.S) (hα : MulAut.congr φ hs.conjAut = MulAut.conj a * Tab.L5.dl) :
    Nat.card ↥(X ⊓ Subgroup.centralizer ({t} : Set G)) ∣ 720 := by
  have haa : (hs.conjAut : MulAut ↥X) * hs.conjAut = 1 := MulEquiv.ext fun y => hs.conjAut_conjAut y
  have hα2 : (MulAut.conj a * Tab.L5.dl) * (MulAut.conj a * Tab.L5.dl) = 1 := by
    rw [← hα, ← map_mul, haa, map_one]
  have hsym : (a : Tab.L5.M5)ᵀ = a := Tab.L5.symm_of_sq a hα2
  set c : Tab.L5.M5 := ((a⁻¹ : Tab.L5.S) : Tab.L5.M5) with hc
  have hcsym : cᵀ = c := by
    rw [hc, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose, hsym]
  have hcdet : c.det ≠ 0 := by
    rw [hc, (a⁻¹ : Tab.L5.S).2]
    exact one_ne_zero
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  have hCX : C ≤ X := inf_le_left
  set D : Subgroup Tab.L5.S := (C.subgroupOf X).map φ.toMonoidHom with hD
  have hform : ∀ g ∈ D, (g : Tab.L5.M5)ᵀ * c * g = c := by
    rintro g ⟨x, hx, hxg⟩
    have hxg' : φ x = g := hxg
    have hxt : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_subgroupOf.mp hx).2
    have hfix : MulAut.congr φ hs.conjAut g = g := by
      rw [← hxg']
      show φ (hs.conjAut (φ.symm (φ x))) = φ x
      rw [MulEquiv.symm_apply_apply, hs.conjAut_of_mem_cent hxt]
    rw [hα, MulAut.mul_apply, MulAut.conj_apply] at hfix
    have h1 : Tab.L5.dl g = a⁻¹ * g * a := by
      calc Tab.L5.dl g = a⁻¹ * (a * Tab.L5.dl g * a⁻¹) * a := by group
        _ = a⁻¹ * g * a := by rw [hfix]
    have h2 : g.transpose = a⁻¹ * g⁻¹ * a := by
      rw [← Tab.L5.dl_inv, h1]
      group
    have h3 : g.transpose * a⁻¹ * g = a⁻¹ := by
      calc g.transpose * a⁻¹ * g = (a⁻¹ * g⁻¹ * a) * a⁻¹ * g := by rw [h2]
        _ = a⁻¹ := by group
    have h4 := congrArg (fun z : Tab.L5.S => (z : Tab.L5.M5)) h3
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose] using h4
  have hdvd := Tab.L5.Orth.card_dvd_of_form hcsym hcdet D hform
  rwa [hD, card_map_subgroupOf hCX φ.toMonoidHom φ.injective] at hdvd

end Setting

theorem tabIdentFor_l5Two : TabIdentFor @Ident.FamL5Two := by
  intro G _ _ X K t hs hX
  obtain ⟨hsimple, hmodel⟩ := hX
  have hZ : Subgroup.center ↥X = ⊥ := hs.center_eq_bot_of_simple hsimple
  have hmodel' := hmodel
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hmodel'
  have hcard2 : Nat.card F = 2 := by simpa using hcard
  obtain ⟨φ⟩ : Nonempty (↥X ≃* Tab.L5.S) :=
    ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 5 F hcard2)⟩
  obtain ⟨a, ε, hε, hα⟩ := Tab.L5.aut_form (MulAut.congr φ hs.conjAut)
  interval_cases ε
  ·
    exfalso
    simp only [pow_zero, mul_one] at hα
    have hx : ∀ y : ↥X, hs.conjAut y = φ.symm a * y * (φ.symm a)⁻¹ := by
      intro y
      apply φ.injective
      have h1 := congrArg (fun f : MulAut Tab.L5.S => f (φ y)) hα
      simp only [MulAut.conj_apply] at h1
      have h2 : (MulAut.congr φ hs.conjAut) (φ y) = φ (hs.conjAut y) := by
        show φ (hs.conjAut (φ.symm (φ y))) = _
        rw [MulEquiv.symm_apply_apply]
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h2, h1]
    exact hs.false_of_inner hsimple φ
      (fun y hy B => Tab.L5.involution_centralizer_component_free hy B) (φ.symm a) hx
  ·
    simp only [pow_one] at hα
    set C : Subgroup G := X ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
    have hCX : C ≤ X := inf_le_left
    have hKC : K ≤ C := hs.comp.1
    have hdvd : Nat.card ↥C ∣ 720 := hs.card_cent_dvd_of_outer φ a hα
    have hKdvd : Nat.card ↥K ∣ 720 := (Subgroup.card_dvd_of_le hKC).trans hdvd
    have hA6 : IsA6 K := by
      rcases hs.ktype with hbig | hL32 | hA6
      · exfalso
        have h1 := hbig.card_ge
        have h2 := Nat.le_of_dvd (by norm_num) hKdvd
        omega
      · exfalso
        have h := hL32.card_eq
        rw [h] at hKdvd
        exact absurd hKdvd (by norm_num)
      · exact hA6
    have h360 := hA6.card_eq
    refine ⟨?_, ?_, fun hbig => ?_, fun hL32 => ?_, fun _ => Or.inr (Or.inl ⟨hA6, hmodel⟩)⟩
    · rw [hZ]
      exact (by simp [IsPGroup] : IsPGroup 2 (⊥ : Subgroup ↥X))
    ·
      apply hs.eq_perfectResidual_of_map φ.toMonoidHom
      · rw [(MonoidHom.ker_eq_bot_iff _).mpr φ.injective]
        exact bot_le
      · have hKX : K ≤ X := hs.K_le
        have hle : (K.subgroupOf X).map φ.toMonoidHom ≤ (C.subgroupOf X).map φ.toMonoidHom :=
          Subgroup.map_mono (fun y hy => hKC hy)
        apply commutator_le_of_card_dvd hle
        rw [card_map_subgroupOf hCX φ.toMonoidHom φ.injective,
          card_map_subgroupOf hKX φ.toMonoidHom φ.injective, h360]
        exact hdvd
    · have h1 := hbig.card_ge
      omega
    · have h1 := hL32.card_eq
      omega

end CFSG.QuasithinUnique.Id2519
