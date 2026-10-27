module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelCo3
import CFSG.Quasithin.Recognition.F4Fusion
import CFSG.Sporadic.Co3

public noncomputable section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup CFSG.Sporadic.Schreier.Co3 CFSG.GH74.M12 CFSG.GH74.M12.Hyp CFSG.Blueprint

@[expose] def co3MtoP
    : co3M →* co3P := inclusion co3M_le_P

theorem co3MtoP_coe
    (x : co3M) : ((co3MtoP x : co3P) : Equiv.Perm (Fin 276)) = x := by
  simp [co3MtoP]

@[expose] def fendelTheta0 :
    co3M ≃* centralizer ({co3ZP} : Set co3P) :=
  (subgroupOfEquivOfLe co3M_le_P).symm.trans (MulEquiv.subgroupCongr co3M_subgroupOf_eq)

theorem fendelTheta0_coe
    (x : co3M) :
    (((fendelTheta0 x : centralizer ({co3ZP} : Set co3P)) : co3P) : Equiv.Perm (Fin 276)) =
      x := by
  simp [fendelTheta0]

theorem fendelTheta0_eq
    (x : co3M) :
    ((fendelTheta0 x : centralizer ({co3ZP} : Set co3P)) : co3P) = co3MtoP x := by
  apply Subtype.ext
  rw [fendelTheta0_coe, co3MtoP_coe]

theorem fendelTheta0_z :
    ((fendelTheta0 co3ZM : centralizer ({co3ZP} : Set co3P)) : co3P) = co3ZP := by
  apply Subtype.ext
  rw [fendelTheta0_coe, co3ZM_coe]
  rfl

theorem fendelTheta0_t :
    ((fendelTheta0 co3TtM : centralizer ({co3ZP} : Set co3P)) : co3P) = co3TtP := by
  apply Subtype.ext
  rw [fendelTheta0_coe, co3TtM_coe]
  rfl

theorem co3P_isSimpleGroup
    : IsSimpleGroup co3P :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 co3PermEquiv.symm

theorem fendel_co3_fusion
    (x : co3M) (hx : orderOf x = 2) :
    IsConj co3ZP (co3MtoP x) ↔ x = co3ZM ∨ IsConj fendelA x := by
  have h := fendel_fusion fendelTheta0 co3P_isSimpleGroup fendelLocalData_co3 fendelTheta0_z x hx
  rwa [fendelTheta0_eq] at h

theorem co3P_two_classes
    (w : co3P) (hw : orderOf w = 2) : IsConj co3ZP w ∨ IsConj co3TtP w := by
  have h := fendel_two_classes fendelTheta0 co3P_isSimpleGroup fendelLocalData_co3
    fendelTheta0_z w hw
  rwa [fendelTheta0_t] at h

theorem co3P_not_isConj
    : ¬ IsConj co3ZP co3TtP := by
  have h := fendel_not_isConj_t1 fendelTheta0 fendelLocalData_co3 fendelTheta0_z
  rwa [fendelTheta0_t] at h

@[expose] def fendelZM1
    : co3M1 := fendelKtoM1 fendelZK

theorem fendelZM1_coe :
    ((fendelZM1 : co3M1) : Equiv.Perm (Fin 276)) = co3Z := by
  rw [fendelZM1, fendelKtoM1_coe]
  rfl

@[expose] def co3Kappa1G :
    co3M1 →* G12 :=
  co3Kappa1.codRestrict NativeSporadic.M12 fun m => by
    rw [← co3Kappa1_range]
    exact MonoidHom.mem_range.2 ⟨m, rfl⟩

theorem co3Kappa1G_coe
    (m : co3M1) : (co3Kappa1G m : Equiv.Perm (Fin 12)) = co3Kappa1 m := by
  simp [co3Kappa1G]

theorem co3Kappa1G_z
    : co3Kappa1G fendelZM1 = fendelWG⁻¹ * Jelt * fendelWG := by
  have h := fendelKappaG_z
  rw [fendelKappaG_apply] at h
  have h1 : fendelK1G fendelZK = fendelWG⁻¹ * Jelt * fendelWG := by
    rw [← h]
    group
  rw [← h1]
  apply Subtype.ext
  rw [co3Kappa1G_coe, fendelK1G_coe, fendelZM1]

theorem fendel_eq_of_card_two {Q : Type*} [Group Q] (hQ : Nat.card Q = 2) {x y : Q} (hx : x ≠ 1)
    (hy : y ≠ 1) : x = y := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; norm_num)
  by_contra hxy
  have h3 : 3 ≤ Nat.card Q := by
    classical
    have : Fintype Q := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card]
    have hs : ({1, x, y} : Finset Q).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hy]),
        Finset.card_pair hxy]
    rw [← hs]
    exact Finset.card_le_univ _
  omega

section Iso

variable
    {G : Type} [Group G] [Finite G] {s : G} (θ : co3M ≃* centralizer ({s} : Set G))

theorem fendel_H_iso
    (hAsc : S_Asc03_simple) (hG : IsSimpleGroup G) (hθ : (θ co3ZM : G) = s) :
    ∃ φ : centralizer ({(θ co3TtM : G)} : Set G) ≃* co3M1,
      φ (fendelT1 θ co3TtM) = co3TtM1 ∧ φ (fendelSH θ co3TtM) = fendelZM1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, B, hπs, hπk, hB, hsB, hsc⟩ :=
    fendel_H_split θ hAsc hG fendelLocalData_co3 hθ fendelM12Data_co3
  have hBi : B.index = 2 := by
    rw [hB.index_eq_card, Nat.card_zpowers, ← Subgroup.orderOf_coe]
    exact fendel_orderOf_t1 θ fendelLocalData_co3
  have hBn : B.Normal := normal_of_index_eq_two hBi
  have hLn : co3L1.Normal := co3L1_normal
  set pH : centralizer ({(θ co3TtM : G)} : Set G) →* G12 × (_ ⧸ B) :=
    π.prod (QuotientGroup.mk' B) with hpH
  set pM : co3M1 →* G12 × (co3M1 ⧸ co3L1) := co3Kappa1G.prod (QuotientGroup.mk' co3L1) with hpM
  have hdisj := disjoint_iff.1 hB.disjoint
  have hpHi : Function.Injective pH := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h1 : π h = 1 := congrArg Prod.fst hh
    have h2 : (QuotientGroup.mk' B h : _ ⧸ B) = 1 := congrArg Prod.snd hh
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 : h ∈ zpowers (fendelT1 θ co3TtM) := by rw [← hπk]; exact h1
    have h4 : h ∈ zpowers (fendelT1 θ co3TtM) ⊓ B := mem_inf.2 ⟨h3, h2⟩
    rwa [hdisj, mem_bot] at h4
  have hpMi : Function.Injective pM := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : co3Kappa1G m = 1 := congrArg Prod.fst hm
    have h2 : (QuotientGroup.mk' co3L1 m : co3M1 ⧸ co3L1) = 1 := congrArg Prod.snd hm
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h1' : co3Kappa1 m = 1 := by
      rw [← co3Kappa1G_coe, h1, OneMemClass.coe_one]
    have h3 : m ∈ co3Z1 := by
      rw [co3Z1, ← co3Kappa1_ker]
      exact h1'
    have h4 : m ∈ co3L1 ⊓ co3Z1 := mem_inf.2 ⟨h2, h3⟩
    rwa [co3L1_inf_Z1, mem_bot] at h4
  have hcardB2 : Nat.card (centralizer ({(θ co3TtM : G)} : Set G) ⧸ B) = 2 := by
    rw [← index_eq_card, hBi]
  have hcardL2 : Nat.card (co3M1 ⧸ co3L1) = 2 := by rw [← index_eq_card, co3L1_index]
  have hcardH : Nat.card (centralizer ({(θ co3TtM : G)} : Set G)) = Nat.card G12 * 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    have ho : orderOf (fendelT1 θ co3TtM) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact fendel_orderOf_t1 θ fendelLocalData_co3
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv, hπk,
      Nat.card_zpowers, ho] at h1
    exact h1
  have hpHb : Function.Bijective pH := hpHi.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hcardB2, hcardH])
  have hpMb : Function.Bijective pM := hpMi.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hcardL2, card_co3M1, card_G12])
  obtain ⟨g1, hg1⟩ := exists_conj_of_central_involution _ hsc
  set g0 : G12 := fendelWG⁻¹ * g1⁻¹ with hg0
  have hg0s : g0 * π (fendelSH θ co3TtM) * g0⁻¹ = co3Kappa1G fendelZM1 := by
    rw [co3Kappa1G_z, ← hg1, hg0]
    group
  set e2 : (centralizer ({(θ co3TtM : G)} : Set G) ⧸ B) ≃* (co3M1 ⧸ co3L1) :=
    mulEquivOfPrimeCardEq hcardB2 hcardL2
  set φ : centralizer ({(θ co3TtM : G)} : Set G) ≃* co3M1 :=
    (MulEquiv.ofBijective pH hpHb).trans
    ((MulEquiv.prodCongr (MulAut.conj g0) e2).trans (MulEquiv.ofBijective pM hpMb).symm) with hφ
  refine ⟨φ, ?_, ?_⟩
  · rw [hφ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
    have ht1 : π (fendelT1 θ co3TtM) = 1 := by
      rw [← MonoidHom.mem_ker, hπk]
      exact mem_zpowers _
    have ht0 : co3Kappa1G co3TtM1 = 1 := by
      apply Subtype.ext
      rw [co3Kappa1G_coe, co3Kappa1_t, OneMemClass.coe_one]
    have hnB : (QuotientGroup.mk' B (fendelT1 θ co3TtM) : _ ⧸ B) ≠ 1 := by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      intro h
      have h4 : fendelT1 θ co3TtM ∈ zpowers (fendelT1 θ co3TtM) ⊓ B := mem_inf.2 ⟨mem_zpowers _, h⟩
      rw [hdisj, mem_bot] at h4
      have h5 := congrArg Subtype.val h4
      exact fendel_ne_one (fendel_orderOf_t1 θ fendelLocalData_co3) h5
    have hnL : (QuotientGroup.mk' co3L1 co3TtM1 : co3M1 ⧸ co3L1) ≠ 1 := by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      intro h
      exact co3Tt_not_mem_L (mem_subgroupOf.1 h)
    have he2 : e2 (QuotientGroup.mk' B (fendelT1 θ co3TtM)) =
        QuotientGroup.mk' co3L1 co3TtM1 :=
      fendel_eq_of_card_two hcardL2 (by rwa [Ne, MulEquiv.map_eq_one_iff]) hnL
    rw [MulEquiv.ofBijective_apply, MulEquiv.ofBijective_apply, hpH, hpM, MonoidHom.prod_apply,
      MonoidHom.prod_apply]
    refine Prod.ext ?_ ?_
    · show (MulAut.conj g0) (π (fendelT1 θ co3TtM)) = co3Kappa1G co3TtM1
      rw [ht1, ht0, map_one]
    · exact he2
  · rw [hφ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
    have hsB' : (QuotientGroup.mk' B (fendelSH θ co3TtM) : _ ⧸ B) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hsB
    have hzL : (QuotientGroup.mk' co3L1 fendelZM1 : co3M1 ⧸ co3L1) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact co3ZM_mem_L1
    rw [MulEquiv.ofBijective_apply, MulEquiv.ofBijective_apply, hpH, hpM, MonoidHom.prod_apply,
      MonoidHom.prod_apply]
    refine Prod.ext ?_ ?_
    · show (MulAut.conj g0) (π (fendelSH θ co3TtM)) = co3Kappa1G fendelZM1
      rw [MulAut.conj_apply, hg0s]
    · show e2 (QuotientGroup.mk' B (fendelSH θ co3TtM)) = QuotientGroup.mk' co3L1 fendelZM1
      rw [hsB', hzL, map_one]

end Iso

section Order

variable
    {G : Type} [Group G] [Finite G] {s : G} (θ : co3M ≃* centralizer ({s} : Set G))

theorem fendel_H2
    (hG : IsSimpleGroup G) (hθ : (θ co3ZM : G) = s) (x : co3M)
    (hx : orderOf x = 2) : IsConj s (θ x : G) ↔ IsConj co3ZP (co3MtoP x) := by
  rw [fendel_fusion θ hG fendelLocalData_co3 hθ x hx, fendel_co3_fusion x hx]

theorem fendel_card
    (hAsc : S_Asc03_simple) (hG : IsSimpleGroup G) (hθ : (θ co3ZM : G) = s) :
    Nat.card G = Nat.card co3P := by
  have hD := fendelLocalData_co3
  obtain ⟨φ, hφT1, hφs⟩ := fendel_H_iso θ hAsc hG hθ
  have hP := co3P_isSimpleGroup
  set φt : centralizer ({s} : Set G) →* co3P := (centralizer ({co3ZP} : Set co3P)).subtype.comp
    (fendelTheta0.toMonoidHom.comp θ.symm.toMonoidHom) with hφtdef
  set φu : centralizer ({(θ co3TtM : G)} : Set G) →* co3P :=
    (inclusion co3M1_le_P).comp φ.toMonoidHom with hφudef
  have hφt : ∀ y : co3M, φt (θ y) = (fendelTheta0 y : co3P) := by
    intro y
    simp [hφtdef]
  have hφu_inj : Function.Injective φu := by
    rw [hφudef, MonoidHom.coe_comp]
    exact (inclusion_injective co3M1_le_P).comp φ.injective
  have hφuS : φu (fendelSH θ co3TtM) = co3ZP := by
    rw [hφudef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφs]
    apply Subtype.ext
    rw [coe_inclusion, fendelZM1_coe]
    rfl
  have hφur : φu.range = centralizer ({co3TtP} : Set co3P) := by
    rw [← co3M1_subgroupOf_eq]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [mem_subgroupOf, hφudef, MonoidHom.comp_apply, coe_inclusion]
      exact (φ x).2
    · intro hy
      refine ⟨φ.symm ⟨y, mem_subgroupOf.1 hy⟩, ?_⟩
      rw [hφudef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [coe_inclusion]
  refine CFSG.Quasithin.card_eq_of_two_class_data (t := s) (u := (θ co3TtM : G)) (t' := co3ZP)
    (u' := co3TtP) (fendel_orderOf_s θ hD hθ) (fendel_orderOf_t1 θ hD)
    (fendel_not_isConj_t1 θ hD hθ) (fendel_two_classes θ hG hD hθ)
    (fendel_orderOf_s fendelTheta0 hD fendelTheta0_z)
    (by rw [← fendelTheta0_t]; exact fendel_orderOf_t1 fendelTheta0 hD) co3P_not_isConj
    co3P_two_classes φt ?_ ?_ ?_ ?_ φu hφu_inj hφur ?_ ?_
  · rw [hφtdef, MonoidHom.coe_comp, MonoidHom.coe_comp]
    exact (centralizer ({co3ZP} : Set co3P)).subtype_injective.comp
      (fendelTheta0.injective.comp θ.symm.injective)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [hφtdef, MonoidHom.comp_apply]
      exact Subtype.coe_prop _
    · intro hy
      refine ⟨θ (fendelTheta0.symm ⟨y, hy⟩), ?_⟩
      rw [hφt, MulEquiv.apply_symm_apply]
  · intro h
    have e : (⟨s, h⟩ : centralizer ({s} : Set G)) = θ co3ZM := Subtype.ext hθ.symm
    rw [e, hφt, fendelTheta0_z]
  · intro x hx
    obtain ⟨y, rfl⟩ := θ.surjective x
    have hyo : orderOf y = 2 := by rw [← fendel_orderOf θ]; exact hx
    rw [hφt, fendel_fusion θ hG hD hθ y hyo, fendelTheta0_eq, fendel_co3_fusion y hyo]
  · intro h
    have e : (⟨θ co3TtM, h⟩ : centralizer ({(θ co3TtM : G)} : Set G)) = fendelT1 θ co3TtM := rfl
    rw [e, hφudef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφT1]
    apply Subtype.ext
    rw [coe_inclusion]
    rfl
  · intro x hx
    constructor
    · intro hc
      have hxt : (x : G) * θ co3TtM = θ co3TtM * x := mem_centralizer_singleton_iff.1 x.2
      obtain ⟨h, hht, hhs⟩ := fendel_conj_in_H θ hG hD hθ hxt hc
      set hH : centralizer ({(θ co3TtM : G)} : Set G) := ⟨h, mem_centralizer_singleton_iff.2 hht⟩
      have e : hH * fendelSH θ co3TtM * hH⁻¹ = x := Subtype.ext hhs
      refine isConj_iff.2 ⟨φu hH, ?_⟩
      rw [← hφuS, ← map_inv, ← map_mul, ← map_mul, e]
    · intro hc
      have hxr : φu x ∈ centralizer ({co3TtP} : Set co3P) := hφur ▸ MonoidHom.mem_range.2 ⟨x, rfl⟩
      have hxt : φu x * (fendelTheta0 co3TtM : co3P) = (fendelTheta0 co3TtM : co3P) * φu x := by
        rw [fendelTheta0_t]
        exact mem_centralizer_singleton_iff.1 hxr
      obtain ⟨m, hmt, hms⟩ := fendel_conj_in_H fendelTheta0 hP hD fendelTheta0_z hxt hc
      have hmr : m ∈ φu.range := by
        rw [hφur, mem_centralizer_singleton_iff, ← fendelTheta0_t]
        exact hmt
      obtain ⟨h, rfl⟩ := hmr
      have e : φu (h * fendelSH θ co3TtM * h⁻¹) = φu x := by
        rw [map_mul, map_mul, map_inv, hφuS]
        exact hms
      have e2 := hφu_inj e
      refine isConj_iff.2 ⟨(h : G), ?_⟩
      have e3 := congrArg Subtype.val e2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e3
      exact e3

theorem fendel_order
    (hG : IsSimpleGroup G) (hθ : (θ co3ZM : G) = s)
    (hM12 : S_Asc03_simple) :
    (∀ x : co3M, orderOf x = 2 → (IsConj s (θ x : G) ↔ IsConj co3ZP (co3MtoP x))) ∧
      Nat.card G = 495766656000 :=
  ⟨fendel_H2 θ hG hθ, (fendel_card θ hM12 hG hθ).trans card_co3P⟩

end Order

end CFSG.EvenSmallLie.SympSix
