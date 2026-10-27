module

public import CFSG.LocalAnalysis.WeakClosure81.InFSqComponents

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.LocalAnalysis.WeakClosure81 (isComponent_map_conjAut orbitClosure_normal)
open scoped Pointwise commutatorElement

theorem quasisimple_and_centralQuotient_of_ker_le {A B C : Type} [Group A] [Group B]
    [Group C] (hB : CFSG.IsQuasisimple B) (f : A →* B)
    (hf : Function.Surjective f) (g : A →* C) (hg : Function.Surjective g)
    (hker : f.ker ≤ g.ker) [Nontrivial C] :
    CFSG.IsQuasisimple C ∧ Nonempty (B ⧸ Subgroup.center B ≃* C ⧸ Subgroup.center C) := by
  obtain ⟨h, hh⟩ : ∃ h : B →* C, ∀ a, h (f a) = g a :=
    ⟨f.liftOfSurjective hf ⟨g, hker⟩,
      fun a => f.liftOfRightInverse_comp_apply _ _ ⟨g, hker⟩ a⟩
  have hsurj : Function.Surjective h := by
    intro c
    obtain ⟨a, rfl⟩ := hg c
    exact ⟨f a, hh a⟩
  have hne : ∃ b, h b ≠ 1 := by
    obtain ⟨c, hc⟩ := exists_ne (1 : C)
    obtain ⟨b, rfl⟩ := hsurj c
    exact ⟨b, hc⟩
  exact ⟨CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hB hsurj hne,
    ⟨CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hB hsurj
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hB hne)⟩⟩

theorem isComponent_of_conj_dichotomy {Q : Type} [Group Q] [Finite Q] {K T : Subgroup Q}
    (hK : CFSG.IsQuasisimple ↥K)
    (hconj : ∀ t ∈ T, K.map (MulAut.conj t).toMonoidHom = K ∨
      ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hKT : K ⊔ T = ⊤) :
    CFSG.IsComponent K ∧ orbitClosure K T ⊔ T = ⊤ := by
  have hFtop : orbitClosure K T ⊔ T = ⊤ := by
    refine le_antisymm le_top ?_
    calc ⊤ = K ⊔ T := hKT.symm
      _ ≤ orbitClosure K T ⊔ T := sup_le_sup_right (le_orbitClosure K T) T
  have hFnorm : (orbitClosure K T).Normal := orbitClosure_normal hFtop
  have hFle : orbitClosure K T ≤ Subgroup.normalizer (K : Set Q) := by
    refine orbitClosure_le fun t ht => ?_
    rcases hconj t ht with heq | hcomm
    · rw [heq]
      exact Subgroup.le_normalizer
    · have hcomm' : ⁅K.map (MulAut.conj t).toMonoidHom, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hcomm
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm').trans
        (Subgroup.centralizer_le_normalizer (K : Set Q))
  have hKn : (K.subgroupOf (orbitClosure K T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_orbitClosure K T)).mpr hFle
  have hsub : K.IsSubnormal :=
    CFSG.Assembly.IsSubnormal.top_iff.mp
      (CFSG.Assembly.IsSubnormal.step (le_orbitClosure K T) hKn
        (CFSG.Assembly.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hFnorm)))
  exact ⟨⟨hK, hsub⟩, hFtop⟩

theorem isComponentOf_minimalNormal_quotient {Q : Type} [Group Q] [Finite Q]
    {K T : Subgroup Q} (hK : CFSG.IsComponent K) (hT : IsPGroup 2 T)
    (hKT : orbitClosure K T ⊔ T = ⊤) (Y : Subgroup Q) [Y.Normal]
    (X : Subgroup (Q ⧸ Y)) (hXn : X.Normal) (hXne : X ≠ ⊥)
    (hXmin : ∀ N : Subgroup (Q ⧸ Y), N.Normal → N ≤ X → N = ⊥ ∨ N = X)
    (hXnc : ¬ IsMulCommutative X) (L : Subgroup (Q ⧸ Y))
    (hL : CFSG.Open.IsComponentOf L X) :
    IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧
      Nonempty (↥L ≃* ↥K ⧸ Subgroup.center ↥K) := by
  classical
  let π : Q →* Q ⧸ Y := QuotientGroup.mk' Y
  let F : Subgroup Q := orbitClosure K T
  let Fbar : Subgroup (Q ⧸ Y) := F.map π
  have : Finite (Q ⧸ Y) := QuotientGroup.finite
  have hFnorm : F.Normal := orbitClosure_normal hKT
  have hFbarnorm : Fbar.Normal := hFnorm.map π (QuotientGroup.mk'_surjective Y)
  have : F.Normal := hFnorm
  have : Fbar.Normal := hFbarnorm
  have : X.Normal := hXn
  have hQF2 : IsPGroup 2 (Q ⧸ F) := by
    have : (F.subgroupOf (⊤ : Subgroup Q)).Normal := hFnorm.subgroupOf ⊤
    have htop : IsPGroup 2 (↥(⊤ : Subgroup Q) ⧸ F.subgroupOf ⊤) :=
      CFSG.Quasithin.F112R.isPGroup_quotient_of_sup_eq (p := 2) (G := Q)
        (L := F) (Q := T) (K := ⊤) hT le_top
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hFnorm]; exact le_top) hKT
    have he : (F.subgroupOf (⊤ : Subgroup Q)).map
        (Subgroup.topEquiv (G := Q)).toMonoidHom = F := by
      ext x
      simp [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    exact IsPGroup.of_equiv htop
      (QuotientGroup.congr (F.subgroupOf ⊤) F Subgroup.topEquiv he)
  have hHF2 : IsPGroup 2 ((Q ⧸ Y) ⧸ Fbar) := by
    let ψq : Q →* (Q ⧸ Y) ⧸ Fbar := (QuotientGroup.mk' Fbar).comp π
    have hψq : Function.Surjective ψq :=
      (QuotientGroup.mk'_surjective Fbar).comp (QuotientGroup.mk'_surjective Y)
    have hkerq : F ≤ ψq.ker := by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map_of_mem π hx
    exact hQF2.of_surjective (QuotientGroup.lift F ψq hkerq)
      (QuotientGroup.lift_surjective_of_surjective F ψq hψq hkerq)
  have hperfX : ⁅X, X⁆ = X := by
    rcases hXmin ⁅X, X⁆ (Subgroup.commutator_normal X X)
      (Subgroup.commutator_le_left X X) with hbot | htop
    · exfalso
      apply hXnc
      have hle : X ≤ Subgroup.centralizer (X : Set (Q ⧸ Y)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      exact isMulCommutative_iff.mpr fun a b =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle a.2) b b.2).symm)
    · exact htop
  have hXFbar : X ≤ Fbar := by
    let ψX : ↥X →* ((Q ⧸ Y) ⧸ Fbar) :=
      (QuotientGroup.mk' Fbar).comp
        ((Fbar ⊔ X).subtype.comp (Subgroup.inclusion le_sup_right))
    have hψXker : ψX.ker = Fbar.subgroupOf X := by
      ext x
      change (QuotientGroup.mk' Fbar) (x : Q ⧸ Y) = 1 ↔ (x : Q ⧸ Y) ∈ Fbar
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hq : IsPGroup 2 (↥X ⧸ Fbar.subgroupOf X) := by
      have h1 : IsPGroup 2 (↥X ⧸ ψX.ker) :=
        IsPGroup.of_equiv (hHF2.to_subgroup ψX.range)
          (QuotientGroup.quotientKerEquivRange ψX).symm
      exact IsPGroup.of_equiv h1 (QuotientGroup.quotientMulEquivOfEq hψXker)
    have hperfXtop : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⊤ := by
      apply Subgroup.map_injective X.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperfX]
    have : (Fbar.subgroupOf X).Normal := hFbarnorm.subgroupOf X
    exact Subgroup.subgroupOf_eq_top.mp
      (CFSG.Quasithin.F112R.normal_eq_top_of_perfect_of_pGroup_quotient
        (Fbar.subgroupOf X) hq hperfXtop)
  have hLq : CFSG.IsQuasisimple ↥L :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥L)).mpr hL.2.2
  have hLcomp : CFSG.IsComponent L := by
    have hLX : CFSG.Assembly.IsSubnormal L X :=
      CFSG.Assembly.isSubnormal_iff_open.mpr hL.2.1
    have hXtop : CFSG.Assembly.IsSubnormal X ⊤ :=
      CFSG.Assembly.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hXn)
    exact ⟨hLq, CFSG.Assembly.IsSubnormal.top_iff.mp (hLX.trans hXtop)⟩
  have hncL : ¬ IsMulCommutative ↥L := by
    intro hcomm
    obtain ⟨a, b, hab⟩ := hLq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) b
    exact hab (by rw [← map_mul, ← map_mul, isMulCommutative_iff.mp hcomm a' b'])
  have hfamily : ∀ a : T, (K.map (MulAut.conj (a : Q)).toMonoidHom).map π = ⊥ ∨
      CFSG.IsComponent ((K.map (MulAut.conj (a : Q)).toMonoidHom).map π) := by
    intro a
    have hKa : CFSG.IsComponent (K.map (MulAut.conj (a : Q)).toMonoidHom) :=
      isComponent_map_conjAut hK (a : Q)
    by_cases hbot : (K.map (MulAut.conj (a : Q)).toMonoidHom).map π = ⊥
    · exact Or.inl hbot
    · refine Or.inr ⟨CFSG.LocalCores.isQuasisimple_map hKa.1 π ?_,
        hKa.2.map (QuotientGroup.mk'_surjective Y)⟩
      intro hle
      exact hbot ((Subgroup.map_eq_bot_iff _).mpr hle)
  have hexists : ∃ a : T, (K.map (MulAut.conj (a : Q)).toMonoidHom).map π = L := by
    by_contra hnone
    push Not at hnone
    have hleC : Fbar ≤ Subgroup.centralizer (L : Set (Q ⧸ Y)) := by
      rw [Subgroup.map_le_iff_le_comap]
      refine orbitClosure_le fun a ha => ?_
      have hKa_le : (K.map (MulAut.conj a).toMonoidHom).map π ≤
          Subgroup.centralizer (L : Set (Q ⧸ Y)) := by
        rcases hfamily ⟨a, ha⟩ with hbot | hcomp
        · rw [hbot]
          exact bot_le
        · rcases CFSG.LocalCores.distinct_components_commute hLcomp hcomp with heq | hcomm
          · exact absurd heq.symm (hnone ⟨a, ha⟩)
          · rw [Subgroup.commutator_comm] at hcomm
            exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact (Subgroup.map_le_iff_le_comap).mp hKa_le
    have hLleFbar : L ≤ Fbar := hL.1.trans hXFbar
    have hLleC : L ≤ Subgroup.centralizer (L : Set (Q ⧸ Y)) :=
      hLleFbar.trans hleC
    have hcomm : IsMulCommutative ↥L :=
      isMulCommutative_iff.mpr fun a b =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hLleC a.2) b b.2).symm)
    exact hncL hcomm
  obtain ⟨a₀, hL_eq⟩ := hexists
  have hFbar_le_layer : Fbar ≤ CFSG.layer (Q ⧸ Y) := by
    change F.map π ≤ CFSG.layer (Q ⧸ Y)
    refine (Subgroup.map_le_iff_le_comap (f := π)).mpr ?_
    refine orbitClosure_le fun a ha => ?_
    refine (Subgroup.map_le_iff_le_comap (f := π)
      (K := K.map (MulAut.conj a).toMonoidHom)
      (H := CFSG.layer (Q ⧸ Y))).mp ?_
    rcases hfamily ⟨a, ha⟩ with hbot | hcomp
    · have h : (K.map (MulAut.conj a).toMonoidHom).map π = ⊥ := by
        simpa only [Subtype.coe_mk] using hbot
      rw [h]
      exact bot_le
    · simpa only [Subtype.coe_mk] using CFSG.LocalCores.component_le_layer hcomp
  let Zbar : Subgroup (Q ⧸ Y) := (Subgroup.center ↥Fbar).map Fbar.subtype
  have hZbar_cent : Zbar ≤ Subgroup.centralizer (Fbar : Set (Q ⧸ Y)) := fun z hz =>
    ((CFSG.LocalCores.mem_map_center_iff Fbar).mp hz).2
  have hZL_le_Zbar : (Subgroup.center ↥L).map L.subtype ≤ Zbar := by
    have hcentL := CFSG.LocalCores.center_component_le_centralizer_layer hLcomp
    have hcentF : (Subgroup.center ↥L).map L.subtype ≤
        Subgroup.centralizer (Fbar : Set (Q ⧸ Y)) :=
      hcentL.trans (Subgroup.centralizer_le hFbar_le_layer)
    intro z hz
    rw [CFSG.LocalCores.mem_map_center_iff]
    exact ⟨(hL.1.trans hXFbar) ((Subgroup.map_subtype_le (Subgroup.center ↥L)) hz),
      hcentF hz⟩
  have hZL_le_X : (Subgroup.center ↥L).map L.subtype ≤ X :=
    (Subgroup.map_subtype_le _).trans hL.1
  have hZbar_norm : Zbar.Normal := by
    have : Fbar.Normal := hFbarnorm
    exact ConjAct.normal_of_characteristic_of_normal
      (H := Fbar) (K := Subgroup.center ↥Fbar)
  have hXZ_norm : (Zbar ⊓ X).Normal := by
    have : Zbar.Normal := hZbar_norm
    infer_instance
  have hZL : Subgroup.center ↥L = ⊥ := by
    rcases hXmin (Zbar ⊓ X) hXZ_norm inf_le_right with hNbot | hNtop
    · have hZmapbot : (Subgroup.center ↥L).map L.subtype = ⊥ := by
        have hle : (Subgroup.center ↥L).map L.subtype ≤ Zbar ⊓ X :=
          le_inf hZL_le_Zbar hZL_le_X
        rw [hNbot] at hle
        exact le_bot_iff.mp hle
      exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hZmapbot
    · exfalso
      have hXleZ : X ≤ Zbar := by
        rw [← hNtop]
        exact inf_le_left
      have hXleC : X ≤ Subgroup.centralizer (Fbar : Set (Q ⧸ Y)) :=
        hXleZ.trans hZbar_cent
      have hLleFbar : L ≤ Fbar := hL.1.trans hXFbar
      have hLleC : L ≤ Subgroup.centralizer (L : Set (Q ⧸ Y)) :=
        (hL.1.trans hXleC).trans (Subgroup.centralizer_le hLleFbar)
      exact hncL (isMulCommutative_iff.mpr fun a b =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hLleC a.2) b b.2).symm))
  let eL : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZL).trans QuotientGroup.quotientBot
  have hsimpleL : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2.1
    exact eL.symm.isSimpleGroup
  let c : Q ≃* Q := MulAut.conj (a₀ : Q)
  let φ : ↥K →* ↥L :=
    MonoidHom.codRestrict (π.comp (c.toMonoidHom.comp K.subtype)) L fun k => by
      change π (c.toMonoidHom (k : Q)) ∈ L
      rw [← hL_eq]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_map_of_mem c.toMonoidHom k.2)
  have hφsurj : Function.Surjective φ := by
    intro l
    have hl : (l : Q ⧸ Y) ∈ (K.map c.toMonoidHom).map π := by
      rw [hL_eq]
      exact l.2
    obtain ⟨q, hq, hql⟩ := hl
    obtain ⟨k, hk, hqk⟩ := hq
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    change π (c.toMonoidHom (k : Q)) = (l : Q ⧸ Y)
    rw [hqk, hql]
  have hφne : ∃ k, φ k ≠ 1 := by
    have : Nontrivial ↥L := hsimpleL.toNontrivial
    obtain ⟨l, hl⟩ := exists_ne (1 : ↥L)
    obtain ⟨k, hk⟩ := hφsurj l
    exact ⟨k, by rw [hk]; exact hl⟩
  let e₁ : ↥K ⧸ Subgroup.center ↥K ≃* ↥L ⧸ Subgroup.center ↥L :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hK.1 hφsurj
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hK.1 hφne)
  refine ⟨hsimpleL, ?_, ⟨eL.symm.trans e₁.symm⟩⟩
  by_contra h
  push Not at h
  exact hncL (isMulCommutative_iff.mpr h)

end CFSG.GroupTheory
