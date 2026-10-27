module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecStd

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace B5a

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem perfect_le_of_le_sup {P N R : Subgroup G} [Group.IsPerfect P]
    (hRN : R ≤ normalizer (N : Set G)) (hR : Group.IsSolvable R) (hP : P ≤ N ⊔ R) : P ≤ N := by
  set U := N ⊔ R with hU
  have hNU : N ≤ U := le_sup_left
  have hUN : U ≤ normalizer (N : Set G) := sup_le le_normalizer hRN
  have : (N.subgroupOf U).Normal := (normal_subgroupOf_iff_le_normalizer hNU).mpr hUN
  let φ : ↥R →* ↥U ⧸ N.subgroupOf U :=
    (QuotientGroup.mk' (N.subgroupOf U)).comp (inclusion le_sup_right)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hu' : (⟨u, hu⟩ : ↥U) ∈ ((R.subgroupOf U ⊔ N.subgroupOf U : Subgroup ↥U) : Set ↥U) := by
      have h1 : R.subgroupOf U ⊔ N.subgroupOf U = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : (x : G) ∈ N ⊔ R := x.2
        have h2 : (N ⊔ R).subgroupOf U = N.subgroupOf U ⊔ R.subgroupOf U := by
          apply map_injective U.subtype_injective
          rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_rfl, map_subgroupOf_eq_of_le hNU,
            map_subgroupOf_eq_of_le le_sup_right]
        have h3 : x ∈ (N ⊔ R).subgroupOf U := hx
        rw [h2, sup_comm] at h3
        exact h3
      rw [h1]
      exact mem_top _
    rw [mul_normal] at hu'
    obtain ⟨r, hr, n, hn, hrn⟩ := hu'
    refine ⟨⟨r, hr⟩, ?_⟩
    show (QuotientGroup.mk (inclusion le_sup_right ⟨(r : G), hr⟩) : ↥U ⧸ N.subgroupOf U) =
      QuotientGroup.mk ⟨u, hu⟩
    rw [QuotientGroup.eq]
    have h4 : (inclusion le_sup_right ⟨(r : G), hr⟩ : ↥U) = r := Subtype.ext rfl
    rw [h4, ← hrn, show r⁻¹ * (r * n) = n by group]
    exact hn
  have : Group.IsSolvable (↥U ⧸ N.subgroupOf U) := Group.isSolvable_of_surjective hφ
  have hPU : P ≤ U := hP
  have : Group.IsPerfect (P.subgroupOf U) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPU).symm.toMonoidHom)
      (subgroupOfEquivOfLe hPU).symm.surjective
  have h5 := CatalogueBLinearTwo.perfect_le_normal_of_solvable_quotient (N.subgroupOf U)
    (P.subgroupOf U)
  intro p hp
  exact h5 (show (⟨p, hPU hp⟩ : ↥U) ∈ P.subgroupOf U from hp)

omit [Finite G] in
theorem exists_mul_of_mem_sup_oddCoreIn {A W : Subgroup G} (hAW : A ≤ W) {x : G}
    (hx : x ∈ A ⊔ oddCoreIn W) : ∃ a ∈ A, ∃ o ∈ oddCoreIn W, a * o = x := by
  have hOW : oddCoreIn W ≤ W := map_subtype_le _
  have hxW : x ∈ W := (sup_le hAW hOW) hx
  have h1 : (A ⊔ oddCoreIn W).subgroupOf W = A.subgroupOf W ⊔ pPrimeCore 2 W := by
    apply map_injective W.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (sup_le hAW hOW), map_subgroupOf_eq_of_le hAW]
    rfl
  have h2 : (⟨x, hxW⟩ : ↥W) ∈ ((A.subgroupOf W ⊔ pPrimeCore 2 W : Subgroup ↥W) : Set ↥W) := by
    rw [SetLike.mem_coe, ← h1]
    exact hx
  rw [mul_normal] at h2
  obtain ⟨a, ha, o, ho, hao⟩ := h2
  exact ⟨a, ha, o, mem_map_of_mem _ ho, congrArg Subtype.val hao⟩

theorem mem_normalizer_of_map_le {U : Subgroup G} {g : G}
    (hle : U.map (MulAut.conj g).toMonoidHom ≤ U) : g ∈ normalizer (U : Set G) := by
  have heq : U.map (MulAut.conj g).toMonoidHom = U := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [mem_normalizer_iff_map_conj_eq]
  exact heq

end B5a

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem card_secImage_mul {Y : Subgroup X} (hYG : Y ≤ h.secG0 y) :
    Nat.card (h.secImage y Y) * Nat.card ↥(Y ⊓ h.secB0 y) = Nat.card Y := by
  set φ := (h.secMk y).subgroupMap (Y.subgroupOf (h.secG0 y)) with hφ
  have hker : Nat.card φ.ker = Nat.card ↥(Y ⊓ h.secB0 y) := by
    have hYB : Y ⊓ h.secB0 y ≤ h.secG0 y := inf_le_left.trans hYG
    have h1 : φ.ker = ((Y ⊓ h.secB0 y).subgroupOf (h.secG0 y)).subgroupOf
        (Y.subgroupOf (h.secG0 y)) := by
      ext z
      rw [MonoidHom.mem_ker, mem_subgroupOf, mem_subgroupOf]
      constructor
      · intro hz
        have h2 : h.secMk y (z : ↥(h.secG0 y)) = 1 := congrArg Subtype.val hz
        rw [← MonoidHom.mem_ker, ker_secMk] at h2
        exact mem_inf.mpr ⟨z.2, h2⟩
      · intro hz
        apply Subtype.ext
        show h.secMk y (z : ↥(h.secG0 y)) = 1
        rw [← MonoidHom.mem_ker, ker_secMk]
        exact (mem_inf.mp hz).2
    rw [h1, Nat.card_congr (subgroupOfEquivOfLe (show (Y ⊓ h.secB0 y).subgroupOf (h.secG0 y) ≤
      Y.subgroupOf (h.secG0 y) from fun _ hg => (mem_inf.mp hg).1)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hYB).toEquiv]
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ
    ((h.secMk y).subgroupMap_surjective _)).toEquiv, hker,
    Nat.card_congr (subgroupOfEquivOfLe hYG).toEquiv] at h2
  exact h2.symm

theorem secMk_mem_oddCoreIn (hc : h.SecCond y) {o : X} (ho : o ∈ oddCoreIn h.W)
    (hoG : o ∈ h.secG0 y) :
    h.secMk y ⟨o, hoG⟩ ∈ oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y))) := by
  have hOW : oddCoreIn h.W ≤ h.W := map_subtype_le _
  set Wp := normalizer (h.secImage y h.B : Set (h.secBar y)) with hWp
  set M := ((oddCoreIn h.W).subgroupOf (h.secW0 y)).map (h.secPhi y) with hM
  have hn0 : ((oddCoreIn h.W).subgroupOf (h.secW0 y)).Normal := by
    refine ⟨fun x hx w => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    have h1 := B5a.conj_mem_oddCoreIn hx (inv_mem w.2.1)
    simpa only [coe_mul, coe_inv, inv_inv] using h1
  have hn : M.Normal := hn0.map _ (secPhi_surjective hc)
  have hodd : Nat.Coprime 2 (Nat.card M) := by
    have h1 : Nat.card M ∣ Nat.card ((oddCoreIn h.W).subgroupOf (h.secW0 y)) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ((oddCoreIn h.W).subgroupOf (h.secW0 y)) ∣ Nat.card (oddCoreIn h.W) :=
      Subgroup.card_comap_dvd_of_injective _ _ (h.secW0 y).subtype_injective
    exact Nat.coprime_two_left.mpr (Odd.of_dvd_nat (B5a.odd_card_oddCoreIn h.W) (h1.trans h2))
  have hle : M ≤ pPrimeCore 2 ↥Wp := le_sSup ⟨hn, hodd⟩
  have hoW0 : o ∈ h.secW0 y := ⟨hOW ho, hoG⟩
  have h3 : h.secPhi y ⟨o, hoW0⟩ ∈ pPrimeCore 2 ↥Wp :=
    hle (mem_map_of_mem _ (show (⟨o, hoW0⟩ : ↥(h.secW0 y)) ∈
      (oddCoreIn h.W).subgroupOf (h.secW0 y) from ho))
  exact mem_map_of_mem _ h3

theorem secMk_mem_normalizer_JO (hc : h.SecCond y) {g : X} (hgW : g ∈ h.W) (hgG : g ∈ h.secG0 y)
    (hgN : g ∈ normalizer ((GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W : Subgroup X) : Set X)) :
    h.secMk y ⟨g, hgG⟩ ∈ normalizer ((h.secImage y (GSLit.fixedLayer h.J h.B) ⊔
      oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y))) : Subgroup (h.secBar y)) :
        Set (h.secBar y)) := by
  set Wp := normalizer (h.secImage y h.B : Set (h.secBar y)) with hWp
  set Jb := GSLit.fixedLayer h.J h.B with hJb
  have hJbW : Jb ≤ h.W := (B5a.fixedLayer_le_V h).trans V_le_W
  have hJbG : Jb ≤ h.secG0 y := (B5a.fixedLayer_le_V h).trans (h.V_le_G0 y)
  set q := h.secMk y ⟨g, hgG⟩ with hq
  have hqW : q ∈ Wp := secMk_mem_normalizer hgG hgW
  have hJ : ∀ z ∈ h.secImage y Jb, q * z * q⁻¹ ∈ h.secImage y Jb ⊔ oddCoreIn Wp := by
    rintro _ ⟨j, hj, rfl⟩
    have hj' : (j : X) ∈ Jb := hj
    have h1 : (g : X) * j * g⁻¹ ∈ Jb ⊔ oddCoreIn h.W :=
      (mem_normalizer_iff.mp hgN j).mp (mem_sup_left hj')
    obtain ⟨j', hj', o, ho, hjo⟩ := B5a.exists_mul_of_mem_sup_oddCoreIn hJbW h1
    have hoG : o ∈ h.secG0 y := by
      have h2 : o = j'⁻¹ * (g * j * g⁻¹) := by rw [← hjo]; group
      rw [h2]
      exact mul_mem (inv_mem (hJbG hj')) (mul_mem (mul_mem hgG j.2) (inv_mem hgG))
    have h3 : q * h.secMk y j * q⁻¹ = h.secMk y ⟨j', hJbG hj'⟩ * h.secMk y ⟨o, hoG⟩ := by
      rw [hq, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      exact hjo.symm
    rw [h3]
    exact mul_mem (mem_sup_left (mem_map_of_mem _ (show (⟨j', hJbG hj'⟩ : ↥(h.secG0 y)) ∈
      Jb.subgroupOf (h.secG0 y) from hj'))) (mem_sup_right (secMk_mem_oddCoreIn hc ho hoG))
  have hO : ∀ z ∈ oddCoreIn Wp, q * z * q⁻¹ ∈ h.secImage y Jb ⊔ oddCoreIn Wp := by
    intro z hz
    exact mem_sup_right ((mem_normalizer_iff.mp
      (B5a.mem_normalizer_oddCoreIn (le_normalizer hqW)) z).mp hz)
  set U := h.secImage y Jb ⊔ oddCoreIn Wp with hU
  have hle : U.map (MulAut.conj q).toMonoidHom ≤ U := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hJ z hz
    · rintro _ ⟨z, hz, rfl⟩
      exact hO z hz
  have heq : U.map (MulAut.conj q).toMonoidHom = U := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (MulAut.conj q).injective]
  rw [mem_normalizer_iff_map_conj_eq]
  exact heq

theorem sylow_layer_secBar (hc : h.SecCond y) :
    ∃ R : Subgroup (h.secBar y),
      R ≤ h.secImage y h.S ⊓ normalizer (h.secImage y h.B : Set (h.secBar y)) ∧
      R ≤ layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))) ⊓
        normalizer ((GSLit.fixedLayer (h.secImage y (h.secJ0 y)) (h.secImage y h.B) ⊔
          oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y))) :
            Subgroup (h.secBar y)) : Set (h.secBar y)) ∧
      ∃ R' : Sylow 2 ↥(layerIn (normalizer (h.secImage y h.B : Set (h.secBar y))) ⊓
        normalizer ((GSLit.fixedLayer (h.secImage y (h.secJ0 y)) (h.secImage y h.B) ⊔
          oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y))) :
            Subgroup (h.secBar y)) : Set (h.secBar y))),
        (R' : Subgroup _) = R.subgroupOf (layerIn (normalizer (h.secImage y h.B :
          Set (h.secBar y))) ⊓ normalizer ((GSLit.fixedLayer (h.secImage y (h.secJ0 y))
            (h.secImage y h.B) ⊔ oddCoreIn (normalizer (h.secImage y h.B : Set (h.secBar y))) :
              Subgroup (h.secBar y)) : Set (h.secBar y))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [layerIn_secW hc, secFixedLayer_B hc]
  obtain ⟨R, hRQ, hRM, R₁, hR₁⟩ := h.sylow_layer
  set Wp := normalizer (h.secImage y h.B : Set (h.secBar y)) with hWp
  set Mp := h.secImage y h.V ⊓ normalizer ((h.secImage y (GSLit.fixedLayer h.J h.B) ⊔ oddCoreIn Wp :
    Subgroup (h.secBar y)) : Set (h.secBar y)) with hMp
  have hRG : R ≤ h.secG0 y := hRQ.trans hc.Q_le
  have hJbV : (GSLit.fixedLayer h.J h.B) ≤ h.V := B5a.fixedLayer_le_V h
  have hJbG : (GSLit.fixedLayer h.J h.B) ≤ h.secG0 y := hJbV.trans (h.V_le_G0 y)
  have hRbar : h.secImage y R ≤ Mp := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' : (r : X) ∈ R := hr
    refine mem_inf.mpr ⟨mem_map_of_mem _ (show r ∈ h.V.subgroupOf (h.secG0 y) from
      (hRM hr').1), ?_⟩
    exact secMk_mem_normalizer_JO hc (hRQ hr').2 r.2 (hRM hr').2
  refine ⟨h.secImage y R, ?_, hRbar, ?_⟩
  · rw [hWp, hc.normalizer_secB,
      ← secImage_inf ((h.secB0_le_B y).trans (h.B_le.trans inf_le_left))]
    exact secImage_mono hRQ
  set Y := h.V ⊓ h.secPre y Mp with hY
  have hYG : Y ≤ h.secG0 y := inf_le_right.trans (secPre_le_G0 Mp)
  have hYimg : h.secImage y Y = Mp := by
    apply le_antisymm
    · exact (secImage_mono inf_le_right).trans (secImage_secPre Mp).le
    · intro m hm
      obtain ⟨v, hv, rfl⟩ := mem_map.mp (mem_inf.mp hm).1
      refine mem_map_of_mem _ (show v ∈ Y.subgroupOf (h.secG0 y) from mem_inf.mpr ⟨hv, ?_⟩)
      exact ⟨v, hm, rfl⟩
  have hRY : R ≤ Y := by
    intro r hr
    refine mem_inf.mpr ⟨(hRM hr).1, ⟨⟨r, hRG hr⟩, ?_, rfl⟩⟩
    rw [SetLike.mem_coe, mem_comap]
    exact hRbar (mem_map_of_mem _ (show (⟨r, hRG hr⟩ : ↥(h.secG0 y)) ∈
      R.subgroupOf (h.secG0 y) from hr))
  have hYM : Y ≤ h.V ⊓ normalizer (((GSLit.fixedLayer h.J h.B) ⊔ oddCoreIn h.W : Subgroup X) :
      Set X) := by
    intro v hv
    obtain ⟨hvV, hvM⟩ := mem_inf.mp hv
    have hvG : v ∈ h.secG0 y := h.V_le_G0 y hvV
    have hvW : v ∈ h.W := V_le_W hvV
    have hqv : h.secMk y ⟨v, hvG⟩ ∈ Mp := secMk_mem_of_mem_secPre hvM
    set Rs := h.secPre y (oddCoreIn Wp) with hRs
    have hBRs : h.secB0 y ≤ Rs := secB0_le_secPre _
    have hRsG : Rs ≤ h.secG0 y := secPre_le_G0 _
    have hJR : h.secB0 y ≤ (GSLit.fixedLayer h.J h.B) ⊔ Rs := hBRs.trans le_sup_right
    have hJRG : (GSLit.fixedLayer h.J h.B) ⊔ Rs ≤ h.secG0 y := sup_le hJbG hRsG
    have hJRimg : h.secImage y ((GSLit.fixedLayer h.J h.B) ⊔ Rs) =
        h.secImage y (GSLit.fixedLayer h.J h.B) ⊔ oddCoreIn Wp := by
      rw [secImage_sup hJbG hRsG, secImage_secPre]
    have hvN : v ∈ normalizer (((GSLit.fixedLayer h.J h.B) ⊔ Rs : Subgroup X) : Set X) := by
      have h1 := (mem_inf.mp hqv).2
      rw [← hJRimg, normalizer_secImage hJR hJRG,
        secMk_mem_secImage_iff (hJR.trans le_normalizer)] at h1
      exact h1
    have hRsK : Rs ≤ h.W ⊓ coreActionKernel h.V := by
      intro r hr
      have hrG := hRsG hr
      have hr' : h.secMk y ⟨r, hrG⟩ ∈ oddCoreIn Wp := secMk_mem_of_mem_secPre hr
      have hrW : r ∈ h.W := by
        have h1 : h.secMk y ⟨r, hrG⟩ ∈ Wp := map_subtype_le _ hr'
        rw [hWp, hc.normalizer_secB, secMk_mem_secImage_iff ((h.secB0_le_B y).trans
          le_normalizer)] at h1
        exact h1
      refine mem_inf.mpr ⟨hrW, mem_coreActionKernel_of_mem_ker_secRho hc
        (w := ⟨r, hrW, hrG⟩) ?_⟩
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' _ (h.secPhi y ⟨r, hrW, hrG⟩) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      obtain ⟨o, ho, hoe⟩ := mem_map.mp hr'
      have h2 : o = h.secPhi y ⟨r, hrW, hrG⟩ := Subtype.ext hoe
      rw [← h2]
      exact pPrimeCore_le_oddTwoCore _ ho
    have : Group.IsSolvable ↥(h.W ⊓ coreActionKernel h.V) := isSolvable_kernel_V
    have hRss : Group.IsSolvable Rs :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hRsK)
    have hOVW : oddCoreIn h.V ≤ oddCoreIn h.W :=
      B5a.oddCoreIn_le_of_le_normalizer V_le_W (OddQuot.le_normalizer_layerIn _)
    have hRsN : Rs ≤ normalizer (((GSLit.fixedLayer h.J h.B) ⊔ oddCoreIn h.W : Subgroup X) :
        Set X) := by
      intro r hr
      have hrW := (mem_inf.mp (hRsK hr)).1
      have hrK := (mem_inf.mp (hRsK hr)).2
      apply B5a.mem_normalizer_of_map_le
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨j, hj, rfl⟩
        have h1 := (mem_coreActionKernel.mp (inv_mem hrK)).2 j (hJbV hj)
        have h2 : (MulAut.conj r).toMonoidHom j = j * (j⁻¹ * r⁻¹⁻¹ * j * r⁻¹) := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          group
        rw [h2]
        exact mul_mem (mem_sup_left hj) (mem_sup_right (hOVW h1))
      · rintro _ ⟨o, ho, rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp
          (B5a.mem_normalizer_oddCoreIn (le_normalizer hrW)) o).mp ho)
    have hvO : v ∈ normalizer (oddCoreIn h.W : Set X) :=
      B5a.mem_normalizer_oddCoreIn (le_normalizer hvW)
    have hvH : v ∈ normalizer ((((GSLit.fixedLayer h.J h.B) ⊔ Rs) ⊔ oddCoreIn h.W :
        Subgroup X) : Set X) :=
      B5a.mem_normalizer_sup hvN hvO
    have hJbp : Group.IsPerfect (GSLit.fixedLayer h.J h.B) :=
      B5a.isPerfect_of_isPComponent_subgroupOf
        ((GSLit.fixedLayer_le_inf h.J h.B).trans (inf_le_inf_right _ h.J_le))
        (B5a.isPComponent_fixedLayer h)
    have : Group.IsPerfect ((GSLit.fixedLayer h.J h.B).map (MulAut.conj v).toMonoidHom) :=
      Group.IsPerfect.map _
    have hJv : (GSLit.fixedLayer h.J h.B).map (MulAut.conj v).toMonoidHom ≤
        (GSLit.fixedLayer h.J h.B) ⊔ oddCoreIn h.W := by
      apply B5a.perfect_le_of_le_sup hRsN hRss
      have h1 : (GSLit.fixedLayer h.J h.B).map (MulAut.conj v).toMonoidHom ≤
          (((GSLit.fixedLayer h.J h.B) ⊔ Rs) ⊔ oddCoreIn h.W).map (MulAut.conj v).toMonoidHom :=
        map_mono (le_sup_left.trans le_sup_left)
      have h2 : (((GSLit.fixedLayer h.J h.B) ⊔ Rs) ⊔ oddCoreIn h.W).map
          (MulAut.conj v).toMonoidHom = ((GSLit.fixedLayer h.J h.B) ⊔ Rs) ⊔ oddCoreIn h.W :=
        mem_normalizer_iff_map_conj_eq.mp hvH
      rw [h2] at h1
      refine h1.trans (sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (le_sup_right.trans le_sup_left))
    refine mem_inf.mpr ⟨hvV, B5a.mem_normalizer_of_map_le ?_⟩
    have h3 : (oddCoreIn h.W).map (MulAut.conj v).toMonoidHom = oddCoreIn h.W :=
      mem_normalizer_iff_map_conj_eq.mp hvO
    rw [Subgroup.map_sup, h3]
    exact sup_le hJv le_sup_right
  have hVBR : h.V ⊓ h.secB0 y ≤ R := by
    have hVBM : h.V ⊓ h.secB0 y ≤ h.V ⊓ normalizer (((GSLit.fixedLayer h.J h.B) ⊔
        oddCoreIn h.W : Subgroup X) :
        Set X) := by
      intro b hb
      obtain ⟨hbV, hbB⟩ := mem_inf.mp hb
      refine mem_inf.mpr ⟨hbV, B5a.mem_normalizer_of_map_le ?_⟩
      have hbW : b ∈ h.W := V_le_W hbV
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨j, hj, rfl⟩
        have h1 : j * b = b * j :=
          (mem_centralizer_iff.mp (h.V_le_centralizer_secB0 y (hJbV hj)) b hbB).symm
        have h2 : (MulAut.conj b).toMonoidHom j = j := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [← h1, mul_inv_cancel_right]
        rw [h2]
        exact mem_sup_left hj
      · rintro _ ⟨o, ho, rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp
          (B5a.mem_normalizer_oddCoreIn (le_normalizer hbW)) o).mp ho)
    have hp : IsPGroup 2 ((h.V ⊓ h.secB0 y).subgroupOf (h.V ⊓ normalizer
        (((GSLit.fixedLayer h.J h.B) ⊔
        oddCoreIn h.W : Subgroup X) : Set X))) :=
      ((h.isPGroup_secB0 y).to_le inf_le_right).comap_subtype
    have hn : ((h.V ⊓ h.secB0 y).subgroupOf (h.V ⊓ normalizer (((GSLit.fixedLayer h.J h.B) ⊔
        oddCoreIn h.W : Subgroup X) : Set X))).Normal := by
      refine ⟨fun x hx m => ?_⟩
      rw [mem_subgroupOf] at hx ⊢
      have h1 : (m : X) * x * (m : X)⁻¹ = x := by
        have h2 : (m : X) * x = x * m :=
          (mem_centralizer_iff.mp (h.V_le_centralizer_secB0 y (mem_inf.mp m.2).1) x
            (mem_inf.mp hx).2).symm
        rw [h2, mul_inv_cancel_right]
      simp only [coe_mul, coe_inv]
      rw [h1]
      exact hx
    intro b hb
    have h1 : (⟨b, hVBM hb⟩ : ↥(h.V ⊓ normalizer (((GSLit.fixedLayer h.J h.B) ⊔
        oddCoreIn h.W : Subgroup X) : Set X))) ∈ (R₁ : Subgroup _) := hp.le_sylow_of_normal R₁ hb
    rw [hR₁] at h1
    exact h1
  have hYB : Y ⊓ h.secB0 y = R ⊓ h.secB0 y :=
    le_antisymm (le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right |>.trans hVBR)
      inf_le_right) (inf_le_inf_right _ hRY)
  have hodd : ¬ 2 ∣ R.relIndex (h.V ⊓ normalizer (((GSLit.fixedLayer h.J h.B) ⊔
      oddCoreIn h.W : Subgroup X) :
      Set X)) := by
    rw [relIndex, ← hR₁]
    exact R₁.not_dvd_index
  have hrel := Subgroup.relIndex_mul_relIndex R Y _ hRY hYM
  have hodd' : ¬ 2 ∣ R.relIndex Y := fun h2 => hodd (hrel ▸ dvd_mul_of_dvd_left h2 _)
  have hc1 := card_secImage_mul hRG
  have hc2 := card_secImage_mul hYG
  rw [hYimg, hYB] at hc2
  have hc3 := Subgroup.relIndex_mul_card (H := R) (K := Y)
  rw [inf_of_le_left hRY] at hc3
  have hc4 := Subgroup.card_mul_index ((h.secImage y R).subgroupOf Mp)
  rw [Nat.card_congr (subgroupOfEquivOfLe hRbar).toEquiv] at hc4
  have hpos : 0 < Nat.card (h.secImage y R) * Nat.card ↥(R ⊓ h.secB0 y) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hidx : ((h.secImage y R).subgroupOf Mp).index = R.relIndex Y := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card (h.secImage y R) * Nat.card ↥(R ⊓ h.secB0 y) *
          ((h.secImage y R).subgroupOf Mp).index
        = Nat.card Mp * Nat.card ↥(R ⊓ h.secB0 y) := by rw [← hc4]; ring
      _ = Nat.card Y := hc2
      _ = R.relIndex Y * Nat.card R := hc3.symm
      _ = Nat.card (h.secImage y R) * Nat.card ↥(R ⊓ h.secB0 y) * R.relIndex Y := by
          rw [← hc1]; ring
  have hR2 : IsPGroup 2 (h.secImage y R) :=
    (((B5a.isPGroup_S h).to_le (hRQ.trans inf_le_left)).comap_subtype
      (K := h.secG0 y)).map (h.secMk y)
  have hodd'' : ¬ 2 ∣ ((h.secImage y R).subgroupOf Mp).index := by
    rw [hidx]
    exact hodd'
  refine ⟨(hR2.comap_subtype (K := Mp)).toSylow
    (show ¬ 2 ∣ ((h.secImage y R).comap Mp.subtype).index from hodd''), ?_⟩
  exact IsPGroup.toSylow_coe _ _

end Hyp52

end CFSG.ComponentClassification.GSThmB
