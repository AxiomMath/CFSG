module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.Quasithin.SteinbergCFSolvableOffenderProducts
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQSolv
import CFSG.GroupTheory.ConjTransport
import CFSG.Quasithin.Background.FFC4Case2
import CFSG.CGT.PushingUpLit.BHS6.ThreeEightS3
import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.GroupTheory.GLnTwoSplitting.Transvection

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (fixV commV IsElemAbelian2 BinaryNaturalSL)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet O2Trivial)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)

variable {W : Type} [CommGroup W]

theorem gomiGstar0_le_pPrimePCore (Y : Subgroup (MulAut W)) :
    gomiGstar0 Y ≤ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y :=
  sSup_le fun _ hA => hA.2

theorem isSolvable_inSubgroup_pPrimePCore_two {G : Type} [Group G] [Finite G] (Y : Subgroup G) :
    Group.IsSolvable ↥(CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y) := by
  have := CFSG.OddStandard.SmallF3.Omega.aor_isSolvable_pPrimePCore_two ↥Y
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (CFSG.GH74.GLS.pPrimePCore 2 ↥Y) Y.subtype
      Y.subtype_injective).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective (CFSG.GH74.GLS.pPrimePCore 2 ↥Y) Y.subtype
      Y.subtype_injective).symm.injective

theorem isSolvable_gomiGstar0 [Finite W] (Y : Subgroup (MulAut W)) :
    Group.IsSolvable ↥(gomiGstar0 Y) := by
  have := isSolvable_inSubgroup_pPrimePCore_two Y
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (gomiGstar0_le_pPrimePCore Y))
    (Subgroup.inclusion_injective (gomiGstar0_le_pPrimePCore Y))

theorem pCore_two_eq_bot_of_o2Trivial {N : Subgroup (MulAut W)} (hO2 : O2Trivial N) :
    CFSG.pCore 2 ↥N = ⊥ := by
  set P : Subgroup (MulAut W) := (CFSG.pCore 2 ↥N).map N.subtype with hP
  have hPN : (P.subgroupOf N).Normal := by
    have hPsub : P.subgroupOf N = CFSG.pCore 2 ↥N := by
      rw [hP]
      exact Subgroup.comap_map_eq_self_of_injective (f := N.subtype) N.subtype_injective _
    rw [hPsub]
    infer_instance
  have hP2 : IsPGroup 2 P := by
    rw [hP]
    exact (pCore_isPGroup (p := 2) (G := ↥N)).map N.subtype
  have hbot : P = ⊥ := hO2 P (Subgroup.map_subtype_le _) hPN hP2
  exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.pCore 2 ↥N) N.subtype_injective).mp
    (hP ▸ hbot)

section Binary

open CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Offender

variable [Fact (∀ w : W, w * w = 1)]

private theorem ofMul_sub (x : MulAut W) (v : W) :
    Additive.ofMul (x v * v⁻¹) = binaryLin x (Additive.ofMul v) - Additive.ofMul v := by
  rw [ofMul_mul, ofMul_inv, binaryLin_apply, sub_eq_add_neg]

private theorem ofMul_mem_commGL_iff {H : Subgroup (MulAut W)} {v : W} :
    Additive.ofMul v ∈ commGL (H.map binaryLin) ⊤ ↔ v ∈ commV H := by
  constructor
  · intro hv
    have h : ∀ w ∈ commGL (H.map binaryLin) ⊤, Additive.toMul w ∈ commV H := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, hg, u, -, rfl⟩ := hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
        have hy : Additive.toMul (binaryLin x u - u) =
            x (Additive.toMul u) * (Additive.toMul u)⁻¹ := by
          have hu : u = Additive.ofMul (Additive.toMul u) := (ofMul_toMul u).symm
          rw [sub_eq_add_neg, toMul_add, toMul_neg, hu, binaryLin_apply, toMul_ofMul,
            toMul_ofMul]
        simp only [MonoidHom.id_apply]
        rw [hy]
        exact Subgroup.subset_closure ⟨x, hx, Additive.toMul u, rfl⟩
      | zero => rw [toMul_zero]; exact Subgroup.one_mem _
      | add a b _ _ ha hb => rw [toMul_add]; exact Subgroup.mul_mem _ ha hb
      | smul c a _ ha =>
        rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul, toMul_zero]; exact Subgroup.one_mem _
        · simpa using ha
    simpa using h (Additive.ofMul v) hv
  · intro hv
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨x, hx, u, rfl⟩ := hy
      rw [ofMul_sub]
      exact Submodule.subset_span ⟨binaryLin x, ⟨x, hx, rfl⟩, Additive.ofMul u, trivial, rfl⟩
    | one => rw [ofMul_one]; exact Submodule.zero_mem _
    | mul a b _ _ ha hb => rw [ofMul_mul]; exact Submodule.add_mem _ ha hb
    | inv a _ ha => rw [ofMul_inv]; exact Submodule.neg_mem _ ha

private theorem card_commV_eq_card_commGL (H : Subgroup (MulAut W)) :
    Nat.card (commV H) = Nat.card (commGL (H.map binaryLin) ⊤) :=
  Nat.card_congr
    { toFun := fun v => ⟨Additive.ofMul v.1, ofMul_mem_commGL_iff.mpr v.2⟩
      invFun := fun w => ⟨Additive.toMul w.1, ofMul_mem_commGL_iff.mp (by
        rw [ofMul_toMul]; exact w.2)⟩
      left_inv := fun v => by simp
      right_inv := fun w => by simp }

private theorem card_fixV_eq_card_fixGL (H : Subgroup (MulAut W)) :
    Nat.card (fixV H) = Nat.card (fixGL (H.map binaryLin)) := by
  have h1 : Nat.card {w : Additive W // ∀ g ∈ H, binaryLin g w = w} =
      Nat.card {w : W // ∀ g ∈ H, g w = w} :=
    card_fixed_binaryLin (MonoidHom.id (MulAut W)) H
  have h2 : Nat.card (fixGL (H.map binaryLin)) =
      Nat.card {w : Additive W // ∀ g ∈ H, binaryLin g w = w} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    constructor
    · intro h g hg
      exact h (binaryLin g) (Subgroup.mem_map_of_mem _ hg)
    · intro h g hg
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
      exact h a ha
  rw [h2, h1]
  rfl

private theorem weight_map_binaryLin (H : Subgroup (MulAut W)) :
    weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (H.map binaryLin) =
      Nat.card H * Nat.card (fixV H) := by
  rw [weight, Subgroup.card_map_of_injective (f := binaryLin) binaryLin_injective,
    card_fixV_eq_card_fixGL]

private theorem isElementaryAbelian_map_of_isElemAbelian2 {A : Subgroup (MulAut W)}
    (hA : IsElemAbelian2 A) : IsElementaryAbelian 2 (A.map binaryLin) := by
  obtain ⟨hc, hs⟩ := hA
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    have haeq : a = ⟨binaryLin x, Subgroup.mem_map_of_mem binaryLin hx⟩ :=
      Subtype.ext hxa.symm
    have hbeq : b = ⟨binaryLin y, Subgroup.mem_map_of_mem binaryLin hy⟩ :=
      Subtype.ext hyb.symm
    rw [haeq, hbeq]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, hc x hx y hy]
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    have haeq : a = ⟨binaryLin x, Subgroup.mem_map_of_mem binaryLin hx⟩ :=
      Subtype.ext hxa.symm
    rw [haeq]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hs x hx, map_one]

private theorem isElemAbelian2_of_isElementaryAbelian_map {A : Subgroup (MulAut W)}
    (hA : IsElementaryAbelian 2 (A.map binaryLin)) : IsElemAbelian2 A := by
  have := hA
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · have h := mul_comm' (⟨binaryLin a, Subgroup.mem_map_of_mem binaryLin ha⟩ :
        ↥(A.map binaryLin)) ⟨binaryLin b, Subgroup.mem_map_of_mem binaryLin hb⟩
    have h' := congrArg Subtype.val h
    apply binaryLin_injective
    rw [map_mul, map_mul]
    simpa using h'
  · have h2 : binaryLin a ^ 2 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A.map binaryLin) (binaryLin a)
        (Subgroup.mem_map_of_mem binaryLin ha)
    apply binaryLin_injective
    rw [map_pow, map_one, pow_two]
    exact h2

private theorem isElemAbelian2_iff_map (A : Subgroup (MulAut W)) :
    IsElemAbelian2 A ↔ IsElementaryAbelian 2 (A.map binaryLin) :=
  ⟨isElementaryAbelian_map_of_isElemAbelian2, isElemAbelian2_of_isElementaryAbelian_map⟩

end Binary

section Dictionary

open CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open CFSG.Quasithin.SteinbergCF

variable [Fact (∀ w : W, w * w = 1)]

omit [Fact (∀ w : W, w * w = 1)] in
private theorem gomiGstar0_le_self (Y : Subgroup (MulAut W)) : gomiGstar0 Y ≤ Y :=
  sSup_le fun _ hB => hB.1.1.1

private theorem minOffender_map_minimal_of_mem_gomiPstar0 (Y : Subgroup (MulAut W))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiPstar0Set Y) :
    ∀ C : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W), ⊥ < C → C < A.map binaryLin →
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) C <
        weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (A.map binaryLin) := by
  obtain ⟨hAP, -⟩ := hA
  obtain ⟨hAPset, hAPmin⟩ := hAP
  obtain ⟨hAY, hAne, hAe, hAbest⟩ := hAPset
  intro C hC0 hCA
  have hCB : C ≤ binaryLin.range := hCA.le.trans (Subgroup.map_le_range binaryLin A)
  set B : Subgroup (MulAut W) := C.comap binaryLin with hB
  have hBmap : B.map binaryLin = C := by
    rw [hB, Subgroup.map_comap_eq_self hCB]
  have hBA : B ≤ A := by
    have h := Subgroup.comap_mono (f := binaryLin) hCA.le
    rw [Subgroup.comap_map_eq_self_of_injective binaryLin_injective] at h
    rwa [hB]
  have hBne : B ≠ ⊥ := fun h => hC0.ne' (by rw [← hBmap, h, Subgroup.map_bot binaryLin])
  have hBltA : B < A := by
    refine lt_of_le_of_ne hBA fun h => hCA.ne (by rw [← hBmap, h])
  have hle : weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (B.map binaryLin) ≤
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (A.map binaryLin) := by
    have h := hAbest B hBA
    rwa [weight_map_binaryLin, weight_map_binaryLin]
  have hwC : weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) C ≤
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (A.map binaryLin) := by
    rw [← hBmap]; exact hle
  rcases lt_or_eq_of_le hwC with hlt | heq
  · exact hlt
  · exfalso
    have hBe : IsElemAbelian2 B :=
      ⟨fun x hx y hy => hAe.1 x (hBA hx) y (hBA hy), fun x hx => hAe.2 x (hBA hx)⟩
    have hwBA : Nat.card A * Nat.card (fixV A) = Nat.card B * Nat.card (fixV B) := by
      have h3 : weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (A.map binaryLin) =
          weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (B.map binaryLin) := by
        rw [hBmap]; exact heq.symm
      rwa [weight_map_binaryLin, weight_map_binaryLin] at h3
    have hBbest : ∀ D : Subgroup (MulAut W), D ≤ B →
        Nat.card D * Nat.card (fixV D) ≤ Nat.card B * Nat.card (fixV B) := by
      intro D hD
      rw [← hwBA]
      exact hAbest D (hD.trans hBA)
    have hBP : B ∈ Pset Y := ⟨hBA.trans hAY, hBne, hBe, hBbest⟩
    have hwA : Nat.card A * Nat.card (fixV A) = Nat.card B * Nat.card (fixV B) := hwBA
    exact hBltA.ne (hAPmin B hBP hBA hwA)

private theorem isMinOffender_map_of_mem_gomiPstar0 (Y : Subgroup (MulAut W))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiPstar0Set Y) :
    IsMinOffender ((gomiGstar0 Y).map binaryLin) (A.map binaryLin) := by
  have hAmem : A ∈ gomiPstar0Set Y := hA
  obtain ⟨hAP, -⟩ := hA
  obtain ⟨hAPset, hAPmin⟩ := hAP
  obtain ⟨hAY, hAne, hAe, hAbest⟩ := hAPset
  have hAN : A ≤ gomiGstar0 Y := le_sSup hAmem
  have hAmap : A.map binaryLin ≤ (gomiGstar0 Y).map binaryLin := Subgroup.map_mono hAN
  have hne : A.map binaryLin ≠ ⊥ := fun h => hAne
    (Subgroup.map_injective (f := binaryLin) binaryLin_injective
      (h.trans (Subgroup.map_bot binaryLin).symm))
  have helem : IsElementaryAbelian 2 (A.map binaryLin) :=
    (isElemAbelian2_iff_map A).mp hAe
  have hweight_le : weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) ⊥ ≤
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (A.map binaryLin) := by
    have hbot : Nat.card (⊥ : Subgroup (MulAut W)) *
        Nat.card (fixV (⊥ : Subgroup (MulAut W))) = Nat.card (Additive W) := by
      have htop : fixV (⊥ : Subgroup (MulAut W)) = ⊤ := by
        ext v; simp [CFSG.Quasithin.mem_fixV]
      rw [Subgroup.card_bot, one_mul, htop, Subgroup.card_top]
      rfl
    have h := hAbest ⊥ bot_le
    rw [hbot] at h
    rwa [weight_map_binaryLin, weight_bot]
  refine ⟨hAmap, hne, helem, ?_, ?_⟩
  · rw [← weight_bot (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W))]
    exact hweight_le
  · exact minOffender_map_minimal_of_mem_gomiPstar0 Y hAmem

private theorem mem_minOffenderSet_of_mem_gomiPstar0 (Y : Subgroup (MulAut W))
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiPstar0Set Y) :
    A.map binaryLin ∈ minOffenderSet ((gomiGstar0 Y).map binaryLin) :=
  mem_minOffenderSet_iff.mpr (isMinOffender_map_of_mem_gomiPstar0 Y hA)

private theorem mem_gomiPstar0_Pset [Finite W] (Y : Subgroup (MulAut W))
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} {A : Subgroup (MulAut W)}
    (hG : G = (gomiGstar0 Y).map binaryLin)
    (hweightle : ∀ B ≤ G, IsElementaryAbelian 2 B →
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) B ≤ Nat.card (Additive W))
    (hweight : ∀ B ∈ offenderSet G,
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) B = Nat.card (Additive W))
    (hmin : A.map binaryLin ∈ minOffenderSet G) :
    A ∈ Pset Y ∧ A ≤ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y := by
  obtain ⟨hAoff, -⟩ := hmin
  have hAoff' : A.map binaryLin ∈ offenderSet G := hAoff
  obtain ⟨hAG, hAne, hAe, -⟩ := hAoff
  have hN : A ≤ gomiGstar0 Y := by
    have h : A ≤ G.comap binaryLin := (Subgroup.map_le_iff_le_comap).mp (hG ▸ hAG)
    rwa [hG, Subgroup.comap_map_eq_self_of_injective binaryLin_injective] at h
  have hAY : A ≤ Y := hN.trans (gomiGstar0_le_self Y)
  have hAe2 : IsElemAbelian2 A := (isElemAbelian2_iff_map A).mpr hAe
  have hAne2 : A ≠ ⊥ := fun h => hAne (by rw [h, Subgroup.map_bot binaryLin])
  have hAO : A ≤ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y :=
    hN.trans (gomiGstar0_le_pPrimePCore Y)
  refine ⟨⟨hAY, hAne2, hAe2, fun B hBA => ?_⟩, hAO⟩
  have hBG : B.map binaryLin ≤ G := hG ▸ Subgroup.map_mono (hBA.trans hN)
  have hBe : IsElemAbelian2 B :=
    ⟨fun x hx y hy => hAe2.1 x (hBA hx) y (hBA hy),
      fun x hx => hAe2.2 x (hBA hx)⟩
  have h1 : weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (B.map binaryLin) ≤
      Nat.card (Additive W) :=
    hweightle _ hBG ((isElemAbelian2_iff_map B).mp hBe)
  have h2 : weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) (A.map binaryLin) =
      Nat.card (Additive W) := hweight _ hAoff'
  rw [← weight_map_binaryLin B, ← weight_map_binaryLin A, h2]
  exact h1

private theorem mem_gomiPstar0_of_mem_minOffenderSet [Finite W] (Y : Subgroup (MulAut W))
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} {A : Subgroup (MulAut W)}
    (hG : G = (gomiGstar0 Y).map binaryLin)
    (hcard2 : ∀ B ∈ minOffenderSet G, Nat.card B = 2)
    (hweightle : ∀ B ≤ G, IsElementaryAbelian 2 B →
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) B ≤ Nat.card (Additive W))
    (hweight : ∀ B ∈ offenderSet G,
      weight (MonoidHom.id (Additive W ≃ₗ[ZMod 2] Additive W)) B = Nat.card (Additive W))
    (hmin : A.map binaryLin ∈ minOffenderSet G) : A ∈ gomiPstar0Set Y := by
  obtain ⟨hPset, hAO⟩ := mem_gomiPstar0_Pset Y hG hweightle hweight hmin
  have hAcard : Nat.card A = 2 := by
    have h := hcard2 (A.map binaryLin) hmin
    rwa [Subgroup.card_map_of_injective (f := binaryLin) binaryLin_injective] at h
  refine ⟨⟨hPset, ?_⟩, hAO⟩
  intro B hBP hBA hweq
  have hBne : B ≠ ⊥ := hBP.2.1
  have hBcard : Nat.card B = 2 := by
    have hdvd : Nat.card B ∣ Nat.card A := Subgroup.card_dvd_of_le hBA
    rw [hAcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hBne
    · exact h1
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hAcard, hBcard])

omit [Fact (∀ w : W, w * w = 1)] in
private theorem map_conj_eq_self {H : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (H : Set (MulAut W))) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    exact (Subgroup.mem_normalizer_iff.mp hg h).mp hh
  · intro x hx
    have hg' : g⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut W)) := Subgroup.inv_mem _ hg
    have hx' : g⁻¹ * x * g ∈ H := (Subgroup.mem_normalizer_iff.mp hg' x).mp hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hx', ?_⟩
    show g * (g⁻¹ * x * g) * g⁻¹ = x
    group

private def factor {r : ℕ} (L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W))
    (i : Fin r) : Subgroup (MulAut W) :=
  (naturalFactor L i).comap binaryLin

private theorem factor_map (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) :
    (factor L i).map binaryLin = naturalFactor L i :=
  Subgroup.map_comap_eq_self ((hS.S_le i).trans (hG ▸ Subgroup.map_le_range binaryLin _))

private theorem factor_le_gomiGstar0 (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) :
    factor L i ≤ gomiGstar0 Y := by
  have h := Subgroup.comap_mono (f := binaryLin) (hG ▸ hS.S_le i)
  rwa [Subgroup.comap_map_eq_self_of_injective binaryLin_injective] at h

private theorem card_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) :
    Nat.card (factor L i) = 6 := by
  have h := Nat.card_congr (Subgroup.equivMapOfInjective (factor L i) binaryLin
    binaryLin_injective).toEquiv
  rw [factor_map Y hS hG i] at h
  rw [h]
  obtain ⟨e⟩ := hS.S_iso i
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

private theorem iSup_offenderSet_eq (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (_hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (_hP : (gomiPstar0Set Y).Nonempty) :
    (⨆ A ∈ offenderSet G, A) = G := by
  refine le_antisymm (iSup₂_le fun A hA => hA.1) ?_
  have hNle : gomiGstar0 Y ≤ (⨆ A ∈ offenderSet G, A).comap binaryLin := by
    refine sSup_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hmem : A.map binaryLin ∈ offenderSet G := by
      have h := (mem_minOffenderSet_of_mem_gomiPstar0 Y hA).1
      rwa [← hG] at h
    exact le_iSup₂ (f := fun B (_ : B ∈ offenderSet G) => B) (A.map binaryLin) hmem
  have h := (Subgroup.map_le_iff_le_comap).mpr hNle
  rw [← hG] at h
  exact h

private theorem iSup_naturalFactor_eq (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    (⨆ i, naturalFactor L i) = G := by
  rw [← hS.B_eq]
  exact iSup_offenderSet_eq Y hS hG hP

private theorem iSup_factor_eq (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    (⨆ i, factor L i) = gomiGstar0 Y := by
  apply Subgroup.map_injective (f := binaryLin) binaryLin_injective
  rw [Subgroup.map_iSup, ← hG]
  exact (iSup_congr fun i => factor_map Y hS hG i).trans (iSup_naturalFactor_eq Y hS hG hP)

private theorem le_range_of_eq {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {N : Subgroup (MulAut W)} (hG : G = N.map binaryLin) : G ≤ binaryLin.range := by
  rw [hG]; exact Subgroup.map_le_range binaryLin _

private theorem gomiGstar0_le_normalizer_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty)
    (i : Fin r) : gomiGstar0 Y ≤ Subgroup.normalizer (factor L i : Set (MulAut W)) := by
  rw [← iSup_factor_eq Y hS hG hP]
  refine iSup_le fun j => ?_
  by_cases h : j = i
  · subst h; exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (factor L i : Set (MulAut W)))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hx' : binaryLin x ∈ naturalFactor L j := by
      rw [← factor_map Y hS hG j]; exact Subgroup.mem_map_of_mem binaryLin hx
    have hy' : binaryLin y ∈ naturalFactor L i := by
      rw [← factor_map Y hS hG i]; exact Subgroup.mem_map_of_mem binaryLin hy
    have hc := (hS.S_comm j i h (binaryLin x) hx' (binaryLin y) hy').symm
    exact binaryLin_injective (by rw [map_mul, map_mul, hc])

private theorem orbitSpan_le_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty)
    {A : Subgroup (MulAut W)} (i : Fin r) (hA : A ≤ factor L i) :
    gomiOrbitSpan Y A ≤ factor L i := by
  refine iSup_le fun g => iSup_le fun hg => ?_
  calc A.map (MulAut.conj g).toMonoidHom ≤ (factor L i).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hA
    _ = factor L i := map_conj_eq_self (gomiGstar0_le_normalizer_factor Y hS hG hP i hg)

omit [Fact (∀ w : W, w * w = 1)] in
private theorem orbitSpan_map_conj (Y : Subgroup (MulAut W)) {A : Subgroup (MulAut W)}
    {g : MulAut W} (hg : g ∈ gomiGstar0 Y) :
    (gomiOrbitSpan Y A).map (MulAut.conj g).toMonoidHom = gomiOrbitSpan Y A := by
  refine le_antisymm ?_ ?_
  · rw [gomiOrbitSpan]
    simp only [Subgroup.map_iSup]
    refine iSup_le fun n => iSup_le fun hn => ?_
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj n).toMonoidHom =
        (MulAut.conj (g * n)).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    exact le_iSup₂_of_le (g * n) (Subgroup.mul_mem _ hg hn) le_rfl
  · rw [gomiOrbitSpan]
    refine iSup_le fun n => iSup_le fun hn => ?_
    have hgn : g⁻¹ * n ∈ gomiGstar0 Y := Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hn
    have h1 : A.map (MulAut.conj n).toMonoidHom =
        (A.map (MulAut.conj (g⁻¹ * n)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [h1]
    exact Subgroup.map_mono (le_iSup₂_of_le (g⁻¹ * n) hgn le_rfl)

private theorem perm_three_exists_conj_ne (σ : Equiv.Perm (Fin 3)) (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) :
    ∃ c : Equiv.Perm (Fin 3), c * σ * c⁻¹ ≠ σ ∧ c * σ * c⁻¹ ≠ 1 := by
  revert σ; decide

end Dictionary

section Orbit

open CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open CFSG.Quasithin.SteinbergCF

variable [Fact (∀ w : W, w * w = 1)] [Finite W]

omit [Finite W] in
private theorem exists_conj_ne_in_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) {a : MulAut W}
    (haT : a ∈ factor L i) (ha : orderOf a = 2) :
    ∃ t ∈ factor L i, t * a * t⁻¹ ≠ a ∧ t * a * t⁻¹ ≠ 1 := by
  obtain ⟨e₁⟩ := hS.S_iso i
  let e : ↥(factor L i) ≃* Equiv.Perm (Fin 3) :=
    (Subgroup.equivMapOfInjective (factor L i) binaryLin binaryLin_injective).trans
      ((MulEquiv.subgroupCongr (factor_map Y hS hG i)).trans e₁)
  let aT : ↥(factor L i) := ⟨a, haT⟩
  have horder_aT : orderOf aT = 2 := by
    rw [← Subgroup.orderOf_coe aT]
    exact ha
  have hσ2 : (e aT) ^ 2 = 1 := by
    rw [← map_pow, ← horder_aT, pow_orderOf_eq_one, map_one]
  have hσ1 : e aT ≠ 1 := by
    intro h
    have h1 : aT = 1 := e.injective (by rw [h, map_one])
    have h2 : a = 1 := congrArg Subtype.val h1
    rw [h2] at ha
    simp at ha
  obtain ⟨c, hc1, hc2⟩ := perm_three_exists_conj_ne (e aT) hσ2 hσ1
  set t : MulAut W := ((e.symm c : ↥(factor L i)) : MulAut W) with ht_def
  have ht : t ∈ factor L i := (e.symm c).2
  have hta : t * a * t⁻¹ ≠ a := by
    intro h
    have h' : ((e.symm c : ↥(factor L i)) * aT * (e.symm c : ↥(factor L i))⁻¹) = aT :=
      Subtype.ext h
    have h2 := congrArg e h'
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    exact hc1 h2
  have ht1 : t * a * t⁻¹ ≠ 1 := by
    intro h
    have h' : ((e.symm c : ↥(factor L i)) * aT * (e.symm c : ↥(factor L i))⁻¹) = 1 :=
      Subtype.ext h
    have h2 := congrArg e h'
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_one] at h2
    exact hc2 h2
  exact ⟨t, ht, hta, ht1⟩

omit [Fact (∀ w : W, w * w = 1)] [Finite W] in
private theorem orbitSpan_self_le (Y : Subgroup (MulAut W)) (A : Subgroup (MulAut W)) :
    A ≤ gomiOrbitSpan Y A := by
  have h1 : A.map (MulAut.conj (1 : MulAut W)).toMonoidHom = A := by
    ext x
    simp
  rw [gomiOrbitSpan]
  exact le_iSup₂_of_le (1 : MulAut W) (Subgroup.one_mem _) (le_of_eq h1.symm)

omit [Fact (∀ w : W, w * w = 1)] [Finite W] in
private theorem zpowers_conj_ne {A : Subgroup (MulAut W)} {a t : MulAut W}
    (hAeq : A = Subgroup.zpowers a) (ha : orderOf a = 2)
    (hta : t * a * t⁻¹ ≠ a) (ht1 : t * a * t⁻¹ ≠ 1) :
    A.map (MulAut.conj t).toMonoidHom ≠ A := by
  intro hEq
  have hBz : A.map (MulAut.conj t).toMonoidHom = Subgroup.zpowers (t * a * t⁻¹) := by
    rw [hAeq, map_conj_zpowers]
  rw [hBz, hAeq] at hEq
  have hmem : t * a * t⁻¹ ∈ Subgroup.zpowers a := by
    rw [← hEq]; exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hmod : a ^ k = a ^ (k % (2 : ℤ)) := by
    have h := zpow_mod_orderOf a k
    rw [ha] at h
    exact h.symm
  have heq : t * a * t⁻¹ = a ^ (k % (2 : ℤ)) := by rw [← hk, hmod]
  have h2c : k % (2 : ℤ) = 0 ∨ k % (2 : ℤ) = 1 := by omega
  rcases h2c with h0 | h1
  · apply ht1; rw [heq, h0]; simp
  · apply hta; rw [heq, h1]; simp

omit [Fact (∀ w : W, w * w = 1)] in
private theorem card_sup_conj_eq_six {A : Subgroup (MulAut W)} {t : MulAut W}
    {P : Subgroup (MulAut W)} (hAcard : Nat.card A = 2)
    (hBne : A.map (MulAut.conj t).toMonoidHom ≠ A)
    (hBt_le : A.map (MulAut.conj t).toMonoidHom ≤ P) (hA : A ≤ P)
    (hcardP : Nat.card P = 6) :
    Nat.card ↥(A ⊔ A.map (MulAut.conj t).toMonoidHom) = 6 := by
  set B : Subgroup (MulAut W) := A.map (MulAut.conj t).toMonoidHom with hBdef
  have hdvd : Nat.card ↥(A ⊔ B) ∣ 6 := by
    rw [← hcardP]
    exact Subgroup.card_dvd_of_le (sup_le hA hBt_le)
  have h2dvd : 2 ∣ Nat.card ↥(A ⊔ B) := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hne2 : Nat.card ↥(A ⊔ B) ≠ 2 := by
    intro h2
    have hAsup : A ⊔ B = A :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h2, hAcard])).symm
    have hBcard : Nat.card ↥B = 2 := by
      rw [hBdef, Subgroup.card_map_of_injective (MulAut.conj t).injective, hAcard]
    have hBeq : B = A := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [← hAsup]; exact le_sup_right
      · rw [hAcard, hBcard]
    exact hBne hBeq
  obtain ⟨k, hk⟩ := h2dvd
  have hk6 : k ∣ 3 := by
    rw [hk] at hdvd
    rw [show (6 : ℕ) = 2 * 3 from by norm_num] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hk6 with h1 | h3
  · exfalso; exact hne2 (by rw [hk, h1])
  · rw [hk, h3]

private theorem orbitSpan_eq_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty)
    {A : Subgroup (MulAut W)} (i : Fin r) (hA : A ≤ factor L i) (hAcard : Nat.card A = 2) :
    gomiOrbitSpan Y A = factor L i := by
  have hle : gomiOrbitSpan Y A ≤ factor L i := orbitSpan_le_factor Y hS hG hP i hA
  have hAle : A ≤ gomiOrbitSpan Y A := orbitSpan_self_le Y A
  obtain ⟨a, hAeq, ha⟩ := exists_zpowers_eq_of_card_eq_prime Nat.prime_two hAcard
  have haT : a ∈ factor L i := by
    rw [hAeq] at hA; exact hA (Subgroup.mem_zpowers a)
  obtain ⟨t, ht, hta, ht1⟩ := exists_conj_ne_in_factor Y hS hG i haT ha
  set B : Subgroup (MulAut W) := A.map (MulAut.conj t).toMonoidHom with hBdef
  have hBne : B ≠ A := zpowers_conj_ne hAeq ha hta ht1
  have hBt_le : B ≤ factor L i := by
    calc B ≤ (factor L i).map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hA
      _ = factor L i := map_conj_eq_self (Subgroup.le_normalizer ht)
  have hBle : B ≤ gomiOrbitSpan Y A := by
    have hnorm := orbitSpan_map_conj (A := A) Y (factor_le_gomiGstar0 Y hS hG i ht)
    calc B ≤ (gomiOrbitSpan Y A).map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hAle
      _ = gomiOrbitSpan Y A := hnorm
  have hBne' : A.map (MulAut.conj t).toMonoidHom ≠ A := hBne
  have hcard6 : Nat.card ↥(A ⊔ B) = 6 :=
    card_sup_conj_eq_six hAcard hBne' hBt_le hA (card_factor Y hS hG i)
  have hEq : A ⊔ B = factor L i :=
    Subgroup.eq_of_le_of_card_ge (sup_le hA hBt_le)
      (by rw [card_factor Y hS hG i, hcard6])
  refine le_antisymm hle ?_
  rw [← hEq]
  exact sup_le hAle hBle

private theorem gomiNSet_subset_range (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    gomiNSet Y ⊆ Set.range (factor L) := by
  rintro K ⟨A, hA, rfl⟩
  have hminA : A.map binaryLin ∈ minOffenderSet G := by
    have h := mem_minOffenderSet_of_mem_gomiPstar0 Y hA
    rwa [← hG] at h
  obtain ⟨i, hi, hicard⟩ := (hS.min_iff (A.map binaryLin)).mp hminA
  have hA_le : A ≤ factor L i := by
    rw [show factor L i = (naturalFactor L i).comap binaryLin from rfl,
      ← Subgroup.map_le_iff_le_comap]
    exact hi
  have hAcard : Nat.card A = 2 := by
    rw [← Subgroup.card_map_of_injective (f := binaryLin) binaryLin_injective]
    exact hicard
  exact ⟨i, (orbitSpan_eq_factor Y hS hG hP i hA_le hAcard).symm⟩

private theorem range_subset_gomiNSet (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    Set.range (factor L) ⊆ gomiNSet Y := by
  rintro K ⟨i, rfl⟩
  obtain ⟨e₁⟩ := hS.S_iso i
  have hswap : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := by
    refine orderOf_eq_prime ?_ ?_ <;> decide
  let bT : ↥(naturalFactor L i) := e₁.symm (Equiv.swap (0 : Fin 3) 1)
  have hbT : orderOf bT = 2 := by
    have h1 : bT = e₁.symm (Equiv.swap (0 : Fin 3) 1) := rfl
    rw [h1, MulEquiv.orderOf_eq e₁.symm (Equiv.swap (0 : Fin 3) 1), hswap]
  let B : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W) :=
    Subgroup.zpowers ((bT : naturalFactor L i) : Additive W ≃ₗ[ZMod 2] Additive W)
  have hBle : B ≤ naturalFactor L i := Subgroup.zpowers_le.mpr bT.2
  have hBcard : Nat.card B = 2 := by
    rw [show B = Subgroup.zpowers ((bT : naturalFactor L i) :
      Additive W ≃ₗ[ZMod 2] Additive W) from rfl, Nat.card_zpowers]
    rw [Subgroup.orderOf_coe bT]; exact hbT
  let A : Subgroup (MulAut W) := B.comap binaryLin
  have hAmap : A.map binaryLin = B :=
    Subgroup.map_comap_eq_self
      (hBle.trans ((hS.S_le i).trans (le_range_of_eq (N := gomiGstar0 Y) hG)))
  have hAcard : Nat.card A = 2 := by
    rw [← Subgroup.card_map_of_injective (f := binaryLin) binaryLin_injective, hAmap]
    exact hBcard
  have hmin : A.map binaryLin ∈ minOffenderSet G := by
    rw [hAmap]
    exact (hS.min_iff B).mpr ⟨i, hBle, hBcard⟩
  have hcard2 : ∀ B' ∈ minOffenderSet G, Nat.card B' = 2 := by
    intro B' hB'
    obtain ⟨j, -, hj⟩ := (hS.min_iff B').mp hB'
    exact hj
  have hP0 : A ∈ gomiPstar0Set Y :=
    mem_gomiPstar0_of_mem_minOffenderSet Y hG hcard2 hS.weight_le hS.weight_eq hmin
  have hA_le : A ≤ factor L i := by
    rw [show factor L i = (naturalFactor L i).comap binaryLin from rfl,
      ← Subgroup.map_le_iff_le_comap]
    rw [hAmap]; exact hBle
  exact ⟨A, hP0, (orbitSpan_eq_factor Y hS hG hP i hA_le hAcard).symm⟩

private theorem gomiNSet_eq_range (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    gomiNSet Y = Set.range (factor L) :=
  Set.Subset.antisymm (gomiNSet_subset_range Y hS hG hP) (range_subset_gomiNSet Y hS hG hP)

private def psi : Subgroup W ≃o Submodule (ZMod 2) (Additive W) :=
  Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)

omit [Finite W] in
private theorem mem_psi {X : Subgroup W} {x : Additive W} :
    x ∈ psi X ↔ Additive.toMul x ∈ X := Iff.rfl

omit [Finite W] in
private theorem psi_commV (H : Subgroup (MulAut W)) :
    psi (commV H) = commGL (H.map binaryLin) ⊤ := by
  ext x
  rw [mem_psi]
  have h := ofMul_mem_commGL_iff (H := H) (v := Additive.toMul x)
  rw [ofMul_toMul] at h
  exact h.symm

omit [Finite W] in
private theorem psi_fixV (H : Subgroup (MulAut W)) :
    psi (fixV H) = fixGL (H.map binaryLin) := by
  ext x
  rw [mem_psi, mem_fixGL, CFSG.Quasithin.mem_fixV]
  constructor
  · intro h g hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    exact congrArg Additive.ofMul (h a ha)
  · intro h g hg
    exact Additive.ofMul.injective (h (binaryLin g) (Subgroup.mem_map_of_mem _ hg))

end Orbit

section Final

open CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Layer
open CFSG.Quasithin.SteinbergCF

variable [Fact (∀ w : W, w * w = 1)] [Finite W]

omit [Finite W] in
private theorem commGL_naturalFactor_eq (_Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (i : Fin r) : commGL (naturalFactor L i) ⊤ = commGL (L i) ⊤ := by
  have hspan : (⨆ j, commGL (L j) ⊤) ⊔ fixGL (⨆ j, L j) = ⊤ :=
    codisjoint_iff.mp hS.V_compl.2
  have hcompl := isCompl_plane_planeComplement hS.I_indep hS.V_compl i
  have hLle : L i ≤ naturalFactor L i :=
    (hS.S_derived i) ▸ Subgroup.commutator_le_self (naturalFactor L i)
  refine le_antisymm ?_ (commGL_mono hLle)
  refine Submodule.span_le.mpr ?_
  rintro w ⟨b, hb, u, -, rfl⟩
  obtain ⟨ui, hui, uc, huc, rfl⟩ := Submodule.mem_sup.mp (show u ∈
    commGL (L i) ⊤ ⊔ planeComplement (fun j => commGL (L j) ⊤) (fixGL (⨆ j, L j)) i from by
      rw [codisjoint_iff.mp hcompl.2]; exact Submodule.mem_top)
  have hbuc : b uc = uc := fix_planeComplement hb huc
  have hbui : b ui ∈ commGL (L i) ⊤ :=
    apply_mem_of_mem_submoduleStab (mem_submoduleStab.mpr hb.1) hui
  simp only [MonoidHom.id_apply] at hbuc hbui ⊢
  rw [map_add, hbuc]
  have hsub : b ui + uc - (ui + uc) = b ui - ui := by abel
  rw [hsub]
  exact Submodule.sub_mem _ hbui hui

private theorem card_commV_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) :
    Nat.card (commV (factor L i)) = 4 := by
  rw [card_commV_eq_card_commGL, factor_map Y hS hG i, commGL_naturalFactor_eq Y hS i]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hS.finrank_I i, Nat.card_zmod]
  norm_num

omit [Finite W] in
private theorem faithful_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) :
    ∀ h ∈ factor L i, (∀ u ∈ commV (factor L i), h u = u) → h = 1 := by
  intro h hh hfix
  have hspan : (⨆ j, commGL (L j) ⊤) ⊔ fixGL (⨆ j, L j) = ⊤ :=
    codisjoint_iff.mp hS.V_compl.2
  have hmem : binaryLin h ∈ naturalFactor L i := by
    rw [← factor_map Y hS hG i]; exact Subgroup.mem_map_of_mem binaryLin hh
  have hfixI : ∀ v ∈ commGL (L i) ⊤, binaryLin h v = v := by
    intro v hv
    have hv' : v ∈ psi (commV (factor L i)) := by
      rw [psi_commV, factor_map Y hS hG i, commGL_naturalFactor_eq Y hS i]
      exact hv
    rw [mem_psi] at hv'
    calc binaryLin h v = binaryLin h (Additive.ofMul (Additive.toMul v)) := by rw [ofMul_toMul]
      _ = Additive.ofMul (h (Additive.toMul v)) := binaryLin_apply h _
      _ = Additive.ofMul (Additive.toMul v) := by rw [hfix _ hv']
      _ = v := ofMul_toMul v
  have hone : binaryLin h = 1 := eq_one_of_mem_planeSupport hspan hmem hfixI
  exact binaryLin_injective (by rw [hone, map_one])

private theorem binaryNaturalSL_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) :
    BinaryNaturalSL (factor L i) (commV (factor L i)) ⊥ 2 1 := by
  have hV : ∀ v : W, v ^ 2 = 1 := fun v => by
    simpa [pow_two] using (Fact.out : ∀ w : W, w * w = 1) v
  have h := CFSG.Quasithin.FFC.binaryNaturalSL_two_of_s3 hV
    (card_factor Y hS hG i) (card_commV_factor Y hS hG i)
    (CFSG.Quasithin.FFC.commV_invariant_self (factor L i))
    (faithful_factor Y hS hG i)
    (fun _ _ c hc => by rw [Subgroup.mem_bot] at hc; rw [hc, map_one]; exact Subgroup.one_mem _)
    (by rw [inf_bot_eq])
  simpa using h

omit [Finite W] in
private theorem isSLn_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (i : Fin r) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn ↥(factor L i) 2 1 := by
  obtain ⟨e₁⟩ := hS.S_iso i
  refine ⟨ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod]; norm_num, ⟨?_⟩⟩
  exact (Subgroup.equivMapOfInjective (factor L i) binaryLin binaryLin_injective).trans
    ((MulEquiv.subgroupCongr (factor_map Y hS hG i)).trans
      (e₁.trans (CFSG.CGT.PushingUpLit.BHS6.s3Equiv.trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 2)))))

omit [Finite W] in
private theorem iSupIndep_factor (_Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L) :
    iSupIndep (factor L) :=
  CFSG.RankThree.Classical.iSupIndep_comap_of_injective binaryLin_injective hS.S_indep

omit [Finite W] in
private theorem iSupIndep_commV_factor (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) :
    iSupIndep (fun i : Fin r => commV (factor L i)) := by
  have h : iSupIndep (fun i : Fin r => psi (commV (factor L i))) := by
    have h1 : (fun i : Fin r => psi (commV (factor L i))) = (fun i => commGL (L i) ⊤) := by
      funext i
      rw [psi_commV, factor_map Y hS hG i, commGL_naturalFactor_eq Y hS i]
    rw [h1]; exact hS.I_indep
  exact iSupIndep.map_orderIso psi.symm h

omit [Finite W] in
private theorem iSup_commV_factor_eq (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    (⨆ i : Fin r, commV (factor L i)) = commV (gomiGstar0 Y) := by
  apply psi.injective
  rw [OrderIso.map_iSup]
  simp only [psi_commV, factor_map Y hS hG, commGL_naturalFactor_eq Y hS]
  rw [show (gomiGstar0 Y).map binaryLin = G from hG.symm,
    ← iSup_naturalFactor_eq Y hS hG hP, hS.B_comm]

omit [Finite W] in
private theorem commV_sup_fixV_gomiGstar0 (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    commV (gomiGstar0 Y) ⊔ fixV (gomiGstar0 Y) = ⊤ := by
  apply psi.injective
  rw [OrderIso.map_sup, psi_commV, psi_fixV, OrderIso.map_top,
    show (gomiGstar0 Y).map binaryLin = G from hG.symm, ← iSup_naturalFactor_eq Y hS hG hP,
    hS.B_comm, hS.B_fix]
  exact codisjoint_iff.mp hS.V_compl.2

omit [Finite W] in
private theorem disjoint_commV_fixV_gomiGstar0 (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    Disjoint (commV (gomiGstar0 Y)) (fixV (gomiGstar0 Y)) := by
  rw [disjoint_iff]
  apply psi.injective
  rw [OrderIso.map_inf, psi_commV, psi_fixV, OrderIso.map_bot,
    show (gomiGstar0 Y).map binaryLin = G from hG.symm, ← iSup_naturalFactor_eq Y hS hG hP,
    hS.B_comm, hS.B_fix]
  exact disjoint_iff.mp hS.V_compl.1

private theorem sSup_gomiNSet (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    sSup (gomiNSet Y) = gomiGstar0 Y := by
  rw [gomiNSet_eq_range Y hS hG hP, sSup_range]
  exact iSup_factor_eq Y hS hG hP

private theorem sSupIndep_gomiNSet (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    sSupIndep (gomiNSet Y) := by
  rw [gomiNSet_eq_range Y hS hG hP]
  exact iSupIndep.sSupIndep_range (iSupIndep_factor Y hS)

private theorem commute_gomiNSet (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    (gomiNSet Y).Pairwise (fun N N' => ∀ x ∈ N, ∀ y ∈ N', x * y = y * x) := by
  rw [gomiNSet_eq_range Y hS hG hP]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne x hx y hy
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hx' : binaryLin x ∈ naturalFactor L i := by
    rw [← factor_map Y hS hG i]; exact Subgroup.mem_map_of_mem binaryLin hx
  have hy' : binaryLin y ∈ naturalFactor L j := by
    rw [← factor_map Y hS hG j]; exact Subgroup.mem_map_of_mem binaryLin hy
  have hc := hS.S_comm i j hij (binaryLin x) hx' (binaryLin y) hy'
  exact binaryLin_injective (by rw [map_mul, map_mul, hc])

private theorem iSup_commV_gomiNSet (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    (⨆ N : ↥(gomiNSet Y), commV (N : Subgroup (MulAut W))) = commV (gomiGstar0 Y) := by
  rw [gomiNSet_eq_range Y hS hG hP]
  have h : (⨆ N : ↥(Set.range (factor L)), commV (N : Subgroup (MulAut W))) =
      ⨆ i : Fin r, commV (factor L i) := by
    refine le_antisymm (iSup_le fun N => ?_) (iSup_le fun i => ?_)
    · obtain ⟨j, hj⟩ := N.2
      rw [← hj]
      exact le_iSup (fun i : Fin r => commV (factor L i)) j
    · exact le_iSup (fun N : ↥(Set.range (factor L)) => commV (N : Subgroup (MulAut W)))
        ⟨factor L i, ⟨i, rfl⟩⟩
  rw [h]
  exact iSup_commV_factor_eq Y hS hG hP

private theorem iSupIndep_commV_gomiNSet (Y : Subgroup (MulAut W)) {r : ℕ}
    {L : Fin r → Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)}
    {G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W)} (hS : OffenderS3Products G L)
    (hG : G = (gomiGstar0 Y).map binaryLin) (hP : (gomiPstar0Set Y).Nonempty) :
    iSupIndep (fun N : ↥(gomiNSet Y) => commV (N : Subgroup (MulAut W))) := by
  rw [gomiNSet_eq_range Y hS hG hP]
  have hne : ∀ i, factor L i ≠ ⊥ := by
    intro i hbot
    have hc := card_factor Y hS hG i
    rw [hbot, Subgroup.card_bot] at hc
    exact absurd hc (by norm_num)
  have hinj : Function.Injective (fun i : Fin r =>
      (⟨factor L i, ⟨i, rfl⟩⟩ : ↥(Set.range (factor L)))) := by
    intro i j h
    exact (iSupIndep_factor Y hS).injective hne (congrArg Subtype.val h)
  let ee : Fin r ≃ ↥(Set.range (factor L)) :=
    Equiv.ofBijective (fun i => (⟨factor L i, ⟨i, rfl⟩⟩ : ↥(Set.range (factor L))))
      ⟨hinj, fun N => by obtain ⟨i, hi⟩ := N.2; exact ⟨i, Subtype.ext hi⟩⟩
  have heq : (fun N : ↥(Set.range (factor L)) => commV (N : Subgroup (MulAut W))) =
      (fun i : Fin r => commV (factor L i)) ∘ ee.symm := by
    funext N
    show commV (N : Subgroup (MulAut W)) = commV (factor L (ee.symm N))
    congr 1
    exact (congrArg Subtype.val (ee.apply_symm_apply N)).symm
  rw [heq]
  exact (iSupIndep_commV_factor Y hS hG).comp (f := ee.symm) ee.symm.injective

theorem gomiFact31_holds : GomiFact31 := by
  intro W _ _ hW Y hP hO2
  have : Fact (∀ w : W, w * w = 1) := ⟨fun w => by simpa [pow_two] using hW w⟩
  have := isSolvable_gomiGstar0 Y
  have hpcore : CFSG.pCore 2 ↥(gomiGstar0 Y) = ⊥ := pCore_two_eq_bot_of_o2Trivial hO2
  set G : Subgroup (Additive W ≃ₗ[ZMod 2] Additive W) := (gomiGstar0 Y).map binaryLin with hG
  set e : ↥(gomiGstar0 Y) ≃* ↥G :=
    Subgroup.equivMapOfInjective (gomiGstar0 Y) binaryLin binaryLin_injective with he
  have hGsolv : Group.IsSolvable ↥G :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  have hGp : CFSG.pCore 2 ↥G = ⊥ := by
    have hmap : (CFSG.pCore 2 ↥(gomiGstar0 Y)).map e.toMonoidHom = CFSG.pCore 2 ↥G :=
      pCore_map_iso 2 e
    rw [← hmap, hpcore, Subgroup.map_bot]
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hoff : (CFSG.Quasithin.SteinbergCF.offenderSet G).Nonempty := by
    obtain ⟨A₀, hA₀⟩ := hP
    refine ⟨A₀.map binaryLin, ?_⟩
    have h := (mem_minOffenderSet_of_mem_gomiPstar0 Y hA₀).1
    rwa [← hG] at h
  obtain ⟨-, -, r, L, -, -, -, hS⟩ :=
    CFSG.Quasithin.SteinbergCF.solvable_faithful_offenders_generate_natural_S3_products
      hGsolv hGp hoff
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro N hN
    rw [gomiNSet_eq_range Y hS hG hP] at hN
    obtain ⟨i, rfl⟩ := hN
    exact isSLn_factor Y hS hG i
  · exact sSupIndep_gomiNSet Y hS hG hP
  · exact commute_gomiNSet Y hS hG hP
  · exact sSup_gomiNSet Y hS hG hP
  · intro N hN
    rw [gomiNSet_eq_range Y hS hG hP] at hN
    obtain ⟨i, rfl⟩ := hN
    exact binaryNaturalSL_factor Y hS hG i
  · exact iSupIndep_commV_gomiNSet Y hS hG hP
  · exact iSup_commV_gomiNSet Y hS hG hP
  · exact commV_sup_fixV_gomiGstar0 Y hS hG hP
  · exact disjoint_commV_fixV_gomiGstar0 Y hS hG hP

end Final

end CFSG.GroupTheory

end
