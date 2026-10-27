module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF89.Sp4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF89.S6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF89.Kernel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF89.Tools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF89.Core
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofJ3
public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofApply
import CFSG.RankThree.PartTwo.Sec8.Item87ProofTools
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (InducesOuterTheta thetaQuotMulAut compAction)
open Subgroup


theorem kF89NotJ3_of (h84 : Pair84A) (hcent : KF89JCentA) : KF89NotJ3 := by
  intro G _ _ A c L a b X n h Y hY hIJ _h8 hA6 hJ3
  obtain ⟨eJ⟩ := hJ3
  have hout : InducesOuterTheta a X := by
    rcases h84 G A c L a b X n h with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  have haN : a ∈ normalizer (X : Set G) := hout.1
  have hAab := h.mem_partTwoF.1
  have ha3 : a ^ 3 = 1 := hAab.2 a h.a_mem
  have hbA : b ∈ A := h.isGammaIndex.1
  have hb1 : b ≠ 1 := h.isGammaIndex.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hXb : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  have hX : X ≤ centralizer ({b} : Set G) := by
    obtain ⟨X', -, hX'⟩ := hXb
    rw [← hX']
    exact map_subtype_le X'
  obtain ⟨-, ⟨eC⟩⟩ := projSp_and_barCentralizer h hout hA6
  set C := barCentralizer (zpowers a) X with hCdef
  set e6 := perm6EquivOfSp42 eC with he6
  have hPmap := map_perfectResidual_eq_alternatingGroup e6 hA6
  obtain ⟨s, hs2, ⟨w₀, hw₀P, hw₀3, hw₀1, hsw₀⟩, hsout⟩ :=
    exists_outer_involution_of_perm6 e6 (perfectResidual C) hPmap
  set H := centralizer ({a} : Set G) with hHdef
  set J := sec8J X a with hJdef
  have hJXC : J ≤ X ⊓ H := Item87Proof.residual_le _
  have hJX : J ≤ X := hJXC.trans inf_le_left
  have hJH : J ≤ H := hJXC.trans inf_le_right
  have hJperf : Group.IsPerfect J := Item87Proof.isPerfect_residual _
  have hJY : J ≤ Y := le_sup_right.trans hIJ
  have hd3 : ∃ j : ℕ, a ^ 3 ^ j = 1 := ⟨1, by simpa using ha3⟩
  set f₁ : J →* X ⧸ aschbacherSolvableCore 3 X :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp (Subgroup.inclusion hJX) with hf₁
  have hf₁range : f₁.range = (perfectResidual C).map C.subtype := by
    have h1 := KFacts.imageModTheta_perfectResidual_centralizer_eq haN hd3
    change imageModTheta X J = inSubgroup perfectResidual C at h1
    rw [← show inSubgroup perfectResidual C = (perfectResidual C).map C.subtype from rfl, ← h1]
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Subgroup.inclusion hJX j, Subgroup.mem_subgroupOf.mpr j.2, rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨⟨x', Subgroup.mem_subgroupOf.mp hx'⟩, rfl⟩
  obtain ⟨t', ht'M, ht's⟩ : ∃ t' : X, t' ∈ (X ⊓ H).subgroupOf X ∧
      (t' : X ⧸ aschbacherSolvableCore 3 X) = (s : X ⧸ aschbacherSolvableCore 3 X) := by
    have hs : (s : X ⧸ aschbacherSolvableCore 3 X) ∈ imageModTheta X (X ⊓ H) := by
      rw [KFacts.imageModTheta_centralizer_eq haN hd3]
      exact s.2
    obtain ⟨t', ht', hts⟩ := hs
    exact ⟨t', ht', hts⟩
  set t : G := (t' : G) with htdef
  have htX : t ∈ X := t'.2
  have htH : t ∈ H := (Subgroup.mem_subgroupOf.mp ht'M).2
  obtain ⟨ι⟩ := id hA6
  have eP : f₁.range ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupCongr hf₁range).trans
      ((Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).symm.trans ι)
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  have h360 : Nat.card f₁.range = 360 := by rw [Nat.card_congr eP.toEquiv, hA6card]
  have hJne : J ≠ ⊥ := by
    intro hJ0
    have h1 : f₁.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨j, rfl⟩
      have hj : (j : G) = 1 := mem_bot.mp ((le_bot_iff.mpr hJ0) j.2)
      have : j = 1 := Subtype.ext hj
      rw [this, map_one]
      exact Subgroup.one_mem _
    rw [h1, Subgroup.card_bot] at h360
    norm_num at h360
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbH : b ∈ H := mem_centralizer_singleton_iff.mpr (hAc b hbA a h.a_mem)
  have hbJ : ∀ y ∈ J, b * y = y * b := fun y hy =>
    (mem_centralizer_singleton_iff.mp (hX (hJX hy))).symm
  have hbN : b ∈ normalizer (Y : Set G) :=
    Item812Res3.mem_normalizer_of_commute_perfect hY hbH hJne hJperf hJY hbJ
  have htinv : t⁻¹ ∈ X ⊓ H := (X ⊓ H).inv_mem ⟨htX, htH⟩
  have htJ : ∀ y ∈ J, t⁻¹ * y * t ∈ J := by
    intro y hy
    have := conj_mem_inSubgroup_perfectResidual htinv hy
    rwa [inv_inv] at this
  have htN : t ∈ normalizer (Y : Set G) :=
    mem_normalizer_of_normalizes_perfect hY htH hJne hJperf hJY htJ
  set f₂ : J →* (Y ⧸ aschbacherSolvableCore 3 Y) ⧸ center (Y ⧸ aschbacherSolvableCore 3 Y) :=
    (QuotientGroup.mk' (center (Y ⧸ aschbacherSolvableCore 3 Y))).comp
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).comp (Subgroup.inclusion hJY)) with hf₂
  set β := actHat Y ⟨b, hbN⟩ with hβ
  set τ := actHat Y ⟨t, htN⟩ with hτ
  obtain ⟨Y₀, hY₀, hY₀Y⟩ := id hY
  have hYq : IsQuasisimple (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [← hY₀Y]
    exact LocalCores.isQuasisimple_of_mulEquiv
      (Item812Res2.thetaQuotEquiv (Y₀.equivMapOfInjective _ (Subgroup.subtype_injective _)))
      hY₀.2.2
  have hZŶ : center ((Y ⧸ aschbacherSolvableCore 3 Y) ⧸
      center (Y ⧸ aschbacherSolvableCore 3 Y)) = ⊥ :=
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.K423Cover.center_quot_eq_bot hYq.2.1 hYq.2.2
  have hOutŶ : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ((Y ⧸ aschbacherSolvableCore 3 Y) ⧸ center (Y ⧸ aschbacherSolvableCore 3 Y))) ≤ 2 :=
    CFSG.Sporadic.Schreier.outer_card_le_of_equiv Sec4.card_outer_J3 eJ
  have hβ3 : β ^ 3 = 1 := by
    rw [hβ, ← map_pow]
    have : (⟨b, hbN⟩ : normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  obtain ⟨y, hyβ, hy3⟩ := exists_conj_eq_of_pow_three hOutŶ hZŶ hβ3
  have htb : (⟨t, htN⟩ : normalizer (Y : Set G)) * ⟨b, hbN⟩ = ⟨b, hbN⟩ * ⟨t, htN⟩ :=
    Subtype.ext (mem_centralizer_singleton_iff.mp (hX htX))
  have hτβ : τ * β = β * τ := by rw [hτ, hβ, ← map_mul, ← map_mul, htb]
  have hτy : τ y = y := by
    have h1 : MulAut.conj (τ y) = MulAut.conj y := by
      have h2 : MulAut.conj (τ y) = τ * MulAut.conj y * τ⁻¹ := by
        ext x
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [h2, hyβ, hτβ, mul_inv_cancel_right]
    exact Sec4.Res423Two.conj_injective_of_center hZŶ h1
  have hf₂b : ∀ j : J, β (f₂ j) = f₂ j := by
    intro j
    change actHat Y ⟨b, hbN⟩ (((Subgroup.inclusion hJY j : Y) :
      Y ⧸ aschbacherSolvableCore 3 Y) : (Y ⧸ aschbacherSolvableCore 3 Y) ⧸
        center (Y ⧸ aschbacherSolvableCore 3 Y)) = _
    rw [actHat_mk]
    congr 2
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    change b * (j : G) * b⁻¹ = j
    rw [hbJ _ j.2, mul_inv_cancel_right]
  have hKy : f₂.range ≤ centralizer ({y} : Set _) := by
    rintro _ ⟨j, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hf₂b j
    rw [← hyβ, MulAut.conj_apply] at h1
    calc f₂ j * y = y * f₂ j * y⁻¹ * y := by rw [h1]
      _ = y * f₂ j := by group
  have ha1 : a ≠ 1 := h.a_ne_one
  have hb'c : b ∉ zpowers a := by
    intro hbk
    have hab : a ∈ zpowers b := by
      have hle : zpowers b ≤ zpowers a := zpowers_le.mpr hbk
      have heq : zpowers b = zpowers a :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime ha3 ha1,
            orderOf_eq_prime hb3 hb1])
      rw [heq]
      exact mem_zpowers a
    obtain ⟨haN', hnot⟩ := hout
    apply hnot
    have hay : ∀ y ∈ X, a * y = y * a := by
      intro y hy
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hab
      have hyb : y * b = b * y := mem_centralizer_singleton_iff.mp (hX hy)
      exact (Commute.zpow_left (show Commute b y from hyb.symm) j).eq
    rw [KFacts.thetaQuotMulAut_compAction_eq_one haN' hay]
    exact ⟨1, map_one _⟩
  have hy1 : y ≠ 1 := by
    intro hy1
    have hβ1 : β = 1 := by rw [← hyβ, hy1, map_one]
    set σb := thetaQuotMulAut Y (compAction Y ⟨b, hbN⟩) with hσb
    have hσb1 : σb = 1 := by
      refine CFSG.AGLEmbeddingD2.Wilson.Proving.eq_one_of_isPerfect_of_mul_inv_mem_center hYq.1 σb
        fun k => ?_
      have h1 : β (k : (Y ⧸ aschbacherSolvableCore 3 Y) ⧸
          center (Y ⧸ aschbacherSolvableCore 3 Y)) = k := by rw [hβ1]; rfl
      have h2 : ((σb k : Y ⧸ aschbacherSolvableCore 3 Y) :
          (Y ⧸ aschbacherSolvableCore 3 Y) ⧸ center (Y ⧸ aschbacherSolvableCore 3 Y)) = k := h1
      rw [QuotientGroup.eq] at h2
      have h3 := (center (Y ⧸ aschbacherSolvableCore 3 Y)).inv_mem h2
      rw [mul_inv_rev, inv_inv] at h3
      have h4 := Subgroup.mem_center_iff.mp h3 (σb k)
      have h5 : σb k * k⁻¹ = (k⁻¹ * σb k) := by
        calc σb k * k⁻¹ = σb k * k⁻¹ * σb k * (σb k)⁻¹ := by group
          _ = (k⁻¹ * σb k) * σb k * (σb k)⁻¹ := by
            rw [show σb k * k⁻¹ * σb k = σb k * (k⁻¹ * σb k) by group, h4]
          _ = k⁻¹ * σb k := by group
      rw [h5]
      exact h3
    have hθle := theta_map_le_of_mem_thetaComponentsAt hY
    have hcomm : ∀ z ∈ Y₀, (⟨b, hbH⟩ : H) * z * (⟨b, hbH⟩ : H)⁻¹ * z⁻¹ ∈
        aschbacherSolvableCore 3 H := by
      intro z hz
      have hzY : (z : G) ∈ Y := hY₀Y ▸ ⟨z, hz, rfl⟩
      set w : Y := ⟨z, hzY⟩ with hw
      have h1 : σb (w : Y ⧸ aschbacherSolvableCore 3 Y) = w := by rw [hσb1]; rfl
      have h2 : ((Y.normalizerMonoidHom ⟨b, hbN⟩ w : Y) : Y ⧸ aschbacherSolvableCore 3 Y) =
          (w : Y ⧸ aschbacherSolvableCore 3 Y) := h1
      rw [QuotientGroup.eq] at h2
      have h3 : Y.normalizerMonoidHom ⟨b, hbN⟩ w * w⁻¹ ∈ aschbacherSolvableCore 3 Y := by
        have h4 := (aschbacherSolvableCore 3 Y).inv_mem h2
        rw [mul_inv_rev, inv_inv] at h4
        have hn : (aschbacherSolvableCore 3 Y).Normal := by
          have := Sec4.aschbacherSolvableCore_characteristic Y
          infer_instance
        have h5 := hn.conj_mem _ h4 w
        rwa [show w * (w⁻¹ * Y.normalizerMonoidHom ⟨b, hbN⟩ w) * w⁻¹ =
          Y.normalizerMonoidHom ⟨b, hbN⟩ w * w⁻¹ by group] at h5
      obtain ⟨v, hv, hvG⟩ := hθle ⟨_, h3, rfl⟩
      have hveq : (⟨b, hbH⟩ : H) * z * (⟨b, hbH⟩ : H)⁻¹ * z⁻¹ = v := by
        apply Subtype.ext
        have hvG' : (v : G) = b * (z : G) * b⁻¹ * (z : G)⁻¹ := by
          rw [show (v : G) = H.subtype v from rfl, hvG]
          simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [Sec4.normalizerMonoidHom_apply_coe]
        rw [hvG']
        simp
      rw [hveq]
      exact hv
    have hY₀Y' : Y₀.map H.subtype = Y := hY₀Y
    have hIJ₀ : sec8I L a ⊔ sec8J X a ≤ Y₀.map H.subtype := by rw [hY₀Y']; exact hIJ
    exact hb'c (hcent G A c L a b X n h Y₀ hY₀ hIJ₀ ⟨b, hbH⟩ hbA hcomm)
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hS : IsSimpleGroup f₁.range := MulEquiv.isSimpleGroup eP
  have hns : ¬ Group.IsSolvable f₁.range := by
    intro hsol
    have : Group.IsSolvable (alternatingGroup (Fin 6)) :=
      Group.isSolvable_of_surjective (f := eP.toMonoidHom) eP.surjective
    have hc := commutator_alternatingGroup_eq_top (α := Fin 6) (by simp)
    have : Nontrivial (alternatingGroup (Fin 6)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hA6card]; norm_num
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (alternatingGroup (Fin 6))).ne hc
  have h3 : ¬ 3 ∣ Nat.card f₁.ker := by
    set ψ : f₁.ker →* aschbacherSolvableCore 3 X :=
      ((Subgroup.inclusion hJX).comp f₁.ker.subtype).codRestrict _ (fun j => by
        have := j.2
        rw [MonoidHom.mem_ker] at this
        exact (QuotientGroup.eq_one_iff _).mp this) with hψ
    have hψi : Function.Injective ψ := by
      intro j j' hjj
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun x : aschbacherSolvableCore 3 X => ((x : X) : G)) hjj
      exact this
    have hdvd := Subgroup.card_dvd_of_injective ψ hψi
    exact fun h3 => (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
      (h3.trans hdvd)
  have hsol : Group.IsSolvable f₂.ker := by
    set N : Subgroup Y := (center (Y ⧸ aschbacherSolvableCore 3 Y)).comap
      (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) with hN
    have hθN : aschbacherSolvableCore 3 Y ≤ N := fun x hx => by
      show (QuotientGroup.mk' _ x) ∈ center _
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      rw [h1]
      exact Subgroup.one_mem _
    have hNsol : Group.IsSolvable N := by
      set g : N →* center (Y ⧸ aschbacherSolvableCore 3 Y) :=
        ((QuotientGroup.mk' (aschbacherSolvableCore 3 Y)).comp N.subtype).codRestrict _
          (fun x => x.2) with hg
      have hθs : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
        (solvable_prime_complement_core_characterization Nat.prime_three).1
      have hZs : Group.IsSolvable (center (Y ⧸ aschbacherSolvableCore 3 Y)) :=
        Group.isSolvable_of_comm fun x y => Subtype.ext
          (Subgroup.mem_center_iff.mp y.2 x)
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hθN) g ?_
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (x : Y) = 1 :=
        congrArg Subtype.val hx
      exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩
    set ψ₂ : f₂.ker →* N :=
      ((Subgroup.inclusion hJY).comp f₂.ker.subtype).codRestrict _ (fun j => by
        have := j.2
        rw [MonoidHom.mem_ker] at this
        exact (QuotientGroup.eq_one_iff (N := center (Y ⧸ aschbacherSolvableCore 3 Y))
          (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (Subgroup.inclusion hJY j))).mp this)
      with hψ₂
    have hψ₂i : Function.Injective ψ₂ := by
      intro j j' hjj
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun x : N => ((x : Y) : G)) hjj
      exact this
    exact Group.isSolvable_of_isSolvable_injective hψ₂i
  have hdvd : Nat.card f₂.range ∣ 1080 ∨ Nat.card f₂.range ∣ 243 := by
    have h1 := Subgroup.card_dvd_of_le hKy
    rcases CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_centralizer_of_equiv_J3_dichotomy
      eJ hy3 hy1 with h | h
    · left; rwa [h] at h1
    · right; rwa [h] at h1
  have hker := ker_eq_of_simple f₁ f₂ hS hns hsol h360 h3 hdvd
  have htJ' : ∀ j : J, t * (j : G) * t⁻¹ ∈ J := fun j =>
    conj_mem_inSubgroup_perfectResidual (Subgroup.mem_inf.mpr ⟨htX, htH⟩) j.2
  set α : J → J := fun j => ⟨t * (j : G) * t⁻¹, htJ' j⟩ with hα
  set σ₁ : X ⧸ aschbacherSolvableCore 3 X → X ⧸ aschbacherSolvableCore 3 X :=
    fun x => (s : X ⧸ aschbacherSolvableCore 3 X) * x * (s : X ⧸ aschbacherSolvableCore 3 X)⁻¹
    with hσ₁
  have h₁ : ∀ j : J, f₁ (α j) = σ₁ (f₁ j) := by
    intro j
    show ((Subgroup.inclusion hJX (α j) : X) : X ⧸ aschbacherSolvableCore 3 X) =
      (s : X ⧸ aschbacherSolvableCore 3 X) *
        ((Subgroup.inclusion hJX j : X) : X ⧸ aschbacherSolvableCore 3 X) *
          (s : X ⧸ aschbacherSolvableCore 3 X)⁻¹
    rw [← ht's, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
  have h₂ : ∀ j : J, f₂ (α j) = τ (f₂ j) := by
    intro j
    change _ = actHat Y ⟨t, htN⟩ (((Subgroup.inclusion hJY j : Y) :
      Y ⧸ aschbacherSolvableCore 3 Y) : (Y ⧸ aschbacherSolvableCore 3 Y) ⧸
        center (Y ⧸ aschbacherSolvableCore 3 Y))
    rw [actHat_mk]
    congr 2
  have hsQ2 : (s : X ⧸ aschbacherSolvableCore 3 X) * (s : X ⧸ aschbacherSolvableCore 3 X) = 1 := by
    rw [← Subgroup.coe_mul, ← sq, hs2, Subgroup.coe_one]
  have hσinv : ∀ x ∈ f₁.range, σ₁ (σ₁ x) = x := by
    intro x _
    simp only [hσ₁]
    calc (s : X ⧸ aschbacherSolvableCore 3 X) * ((s : X ⧸ aschbacherSolvableCore 3 X) * x *
          (s : X ⧸ aschbacherSolvableCore 3 X)⁻¹) * (s : X ⧸ aschbacherSolvableCore 3 X)⁻¹ =
        ((s : X ⧸ aschbacherSolvableCore 3 X) * (s : X ⧸ aschbacherSolvableCore 3 X)) * x *
          ((s : X ⧸ aschbacherSolvableCore 3 X) * (s : X ⧸ aschbacherSolvableCore 3 X))⁻¹ := by
          group
      _ = x := by rw [hsQ2]; group
  have hσout : ∀ g ∈ f₁.range, ∃ x ∈ f₁.range, σ₁ x ≠ g * x * g⁻¹ := by
    intro g hg
    rw [hf₁range] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨x', hx', hne⟩ := hsout g' hg'
    refine ⟨(x' : X ⧸ aschbacherSolvableCore 3 X), hf₁range ▸ ⟨x', hx', rfl⟩, fun heq => hne ?_⟩
    apply Subtype.ext
    simpa [hσ₁] using heq
  have hw : ∃ w ∈ f₁.range, w ^ 3 = 1 ∧ w ≠ 1 ∧ σ₁ w = w := by
    refine ⟨(w₀ : X ⧸ aschbacherSolvableCore 3 X), hf₁range ▸ ⟨w₀, hw₀P, rfl⟩, ?_, ?_, ?_⟩
    · rw [← Subgroup.coe_pow, hw₀3, Subgroup.coe_one]
    · intro h1
      exact hw₀1 (Subtype.ext h1)
    · show (s : X ⧸ aschbacherSolvableCore 3 X) * (w₀ : X ⧸ aschbacherSolvableCore 3 X) *
        (s : X ⧸ aschbacherSolvableCore 3 X)⁻¹ = w₀
      rw [← Subgroup.coe_mul, hsw₀, Subgroup.coe_mul, mul_inv_cancel_right]
  have hZ₁ : ∀ x ∈ f₁.range, (∀ z ∈ f₁.range, x * z = z * x) → x = 1 := by
    intro x hx hc
    have hZA : center (alternatingGroup (Fin 6)) = ⊥ := alternatingGroup.center_eq_bot (by simp)
    have h1 : eP ⟨x, hx⟩ ∈ center (alternatingGroup (Fin 6)) := by
      rw [mem_center_iff]
      intro z
      obtain ⟨z', rfl⟩ := eP.surjective z
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc z' z'.2).symm
    rw [hZA, mem_bot, MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hτ2 := transfer_involution hker h₁ h₂ hσinv
  have hτo := transfer_outer hker h₁ h₂ hσout
  obtain ⟨w, hwK, hw3, hw1, hτw⟩ := transfer_fixed hker h₁ h₂ hw
  have hZK := transfer_center hker hZ₁
  have hK360 : Nat.card f₂.range = 360 := by rw [← card_range_eq hker, h360]
  exact false_of_J3_outer_on_A6 eJ (orderOf_eq_prime hy3 hy1) f₂.range hK360 hZK hKy τ hτy hτ2 hτo
    hwK hw3 hw1 hτw

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF89
