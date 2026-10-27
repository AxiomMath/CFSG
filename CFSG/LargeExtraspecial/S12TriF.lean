module

public import CFSG.Timmesfeld.Transvection.QTwoSp
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.Fischer.Classification.Recognition.Main
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.LargeExtraspecial.S12TriA

public section

namespace CFSG.LargeExtraspecial.S12Tri

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Subgroup Matrix CFSG.Open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (h : commutator H = ⊤) : commutator G = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← apply_mem_commutator_iff φ, h]
  exact mem_top _

theorem triResult_symp {G : Type} [Group G] {D : Set G} {t : G} (htG : t ∉ commutator G)
    (h2 : ∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    TriResult G t := by
  obtain ⟨m, hm, b, halt, hnd, φ, hφ⟩ := h2
  obtain ⟨ψ, -⟩ := CFSG.Timmesfeld.Transvection.QTwo.exists_sympEquiv_of_isometry b halt hnd φ hφ
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · right; right
    let ρ : CFSG.ComponentClassification.PresentationLocal.sympFour ≃*
        TauCeti.GLSymplectic (Fin 2) (ZMod 2) :=
      (CFSG.Timmesfeld.Transvection.QTwo.glFourEquiv.subgroupMap _).trans
        (MulEquiv.subgroupCongr CFSG.Timmesfeld.Transvection.QTwo.map_sympFour)
    let ω : CFSG.ComponentClassification.PresentationLocal.sympFour ≃* Equiv.Perm (Fin 6) :=
      MulEquiv.ofBijective CFSG.ComponentClassification.PresentationLocal.omegaPerm
        ⟨CFSG.ComponentClassification.PresentationLocal.omegaPerm_injective,
          CFSG.ComponentClassification.PresentationLocal.omegaPerm_surjective⟩
    exact ⟨(commutatorEquiv (ψ.trans (ρ.symm.trans ω))).trans
      (MulEquiv.subgroupCongr (alternatingGroup.commutator_perm_eq (by simp)))⟩
  · exfalso
    have hperf : Group.IsPerfect (TauCeti.GLSymplectic (Fin m) (ZMod 2)) := by
      have := CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin (ZMod 2) m
        (Or.inr (Or.inr ⟨by simp, hm3⟩))
      exact Group.IsPerfect.ofSurjective
        (f := (TauCeti.GLSymplecticFin.mulEquivGLSymplectic m (ZMod 2)).toMonoidHom)
        (MulEquiv.surjective _)
    apply htG
    rw [commutator_eq_top_of_mulEquiv ψ hperf.commutator_eq_top]
    exact mem_top t

theorem false_unitary {G : Type} [Group G] {D : Set G} {t : G} (htG : t ∉ commutator G)
    (h4 : ∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) : False := by
  obtain ⟨m, hm, hmodel⟩ := h4
  obtain ⟨φ, -⟩ := fischerCentralQuotientModel_iff_U2.1 hmodel
  apply htG
  rw [commutator_eq_top_of_mulEquiv (φ.trans (Unitary.u2Equiv m)) (Unitary.commutator_PG hm)]
  exact mem_top t

theorem mem_commutator_of_perfect {X : Type*} [Group X] {C : Subgroup X}
    (h : commutator C = ⊤) {c : X} (hc : c ∈ C) : c ∈ commutator X := by
  have h1 : c ∈ (commutator C).map C.subtype := ⟨⟨c, hc⟩, h ▸ mem_top _, rfl⟩
  rw [map_subtype_commutator] at h1
  exact commutator_mono le_top le_top h1

theorem commutator_eq_top_of_isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H]
    (hna : ∃ a b : H, a * b ≠ b * a) : commutator H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator H) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hc : ⁅a, b⁆ ∈ commutator H := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hab hc
  · exact h

theorem triGood_fi24
    {X : Type} [Group X] [Finite X] {d : X} (hd2 : orderOf d = 2)
    (hdX : d ∉ commutator X) {L : Subgroup X} (eL : L ≃* CFSG.Blueprint.NativeSporadic.Fi23)
    (hCL : centralizer ({d} : Set X) = zpowers d ⊔ L)
    (hcomm : zpowers d ≤ centralizer (L : Set X)) : TriGood X d := by
  have hLs : IsSimpleGroup L :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 eL
  have hLna : ∃ a b : L, a * b ≠ b * a :=
    Recognition.exists_not_commute_of_isSimpleGroup (by
      rw [Nat.card_congr eL.toEquiv]
      exact Recognition.card_Fi23_not_prime)
  have hLp : commutator L = ⊤ := commutator_eq_top_of_isSimpleGroup hLna
  have hLX : ∀ l ∈ L, l ∈ commutator X := fun l hl => mem_commutator_of_perfect hLp hl
  have hEq : (commutator X ⊓ centralizer {d} : Subgroup X) = L := by
    apply le_antisymm
    · rintro c ⟨hcX, hcC⟩
      rw [hCL] at hcC
      let f : zpowers d × L →* X := MonoidHom.noncommCoprod (zpowers d).subtype L.subtype
        fun x l => ((mem_centralizer_iff.1 (hcomm x.2)) l l.2).symm
      have hle : zpowers d ⊔ L ≤ f.range := sup_le
        (fun x hx => ⟨(⟨x, hx⟩, 1), show x * ((1 : L) : X) = x by rw [OneMemClass.coe_one,
          mul_one]⟩)
        (fun l hl => ⟨(1, ⟨l, hl⟩), show ((1 : zpowers d) : X) * l = l by
          rw [OneMemClass.coe_one, one_mul]⟩)
      obtain ⟨⟨⟨x, hx⟩, ⟨l, hl⟩⟩, hxl⟩ := hle hcC
      have hxl' : x * l = c := hxl
      have hx2 : x = 1 ∨ x = d := by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
        rw [← zpow_mod_orderOf, hd2]
        rcases (show n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 by omega) with h0 | h1
        · rw [h0, zpow_zero]
          exact Or.inl rfl
        · rw [h1, zpow_one]
          exact Or.inr rfl
      rcases hx2 with rfl | rfl
      · rw [← hxl', one_mul]
        exact hl
      · exfalso
        apply hdX
        have : x = c * l⁻¹ := by rw [← hxl', mul_inv_cancel_right]
        rw [this]
        exact (commutator X).mul_mem hcX ((commutator X).inv_mem (hLX l hl))
    · intro l hl
      exact ⟨hLX l hl, hCL ▸ (le_sup_right : L ≤ zpowers d ⊔ L) hl⟩
  let e : (commutator X ⊓ centralizer {d} : Subgroup X) ≃* L := MulEquiv.subgroupCongr hEq
  obtain ⟨a, b, hab⟩ := hLna
  refine triGood_of_isSimpleGroup e.isSimpleGroup ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  rw [← map_mul, ← map_mul] at h
  exact e.symm.injective h

theorem triGood_hasType
    {G : Type} [Group G] {D : Set G} (hH : Hyp G D) {t : G} (ht : t ∈ D)
    (htG : t ∉ commutator G) {k : Fin 3} (hk : HasType k G D) : TriGood G t := by
  obtain ⟨-, -, Dk, -, -, hloc, hrec⟩ :=
    CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full k
  obtain ⟨iso, hiso⟩ := hrec G D hH.pair hH.center hH.simple hk
  have hd : iso t ∈ Dk := hiso ▸ ⟨t, ht, rfl⟩
  have hdX : iso t ∉ commutator (Carrier k) := by rwa [apply_mem_commutator_iff]
  have hd2 : orderOf (iso t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact Pair.orderOf_eq_two hH.pair ht
  have := Pair.finite hH.pair
  have : Finite (Carrier k) := Finite.of_equiv G iso.toEquiv
  refine TriGood.of_mulEquiv iso ?_
  have hl := hloc (iso t) hd
  fin_cases k
  · exact absurd (mem_commutator_of_perfect (hl.1 rfl).1 (mem_centralizer_singleton_iff.2 rfl))
      hdX
  · exact absurd (mem_commutator_of_perfect (hl.2.1 rfl).1
      (mem_centralizer_singleton_iff.2 rfl)) hdX
  · obtain ⟨L, ⟨eL⟩, hCL, -, hcomm⟩ := hl.2.2 rfl
    exact triGood_fi24 hd2 hdX eL hCL hcomm

end CFSG.LargeExtraspecial.S12Tri
