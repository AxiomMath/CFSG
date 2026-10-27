module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22Weak
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Lemma22TwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderLinear

public section

namespace CFSG.ComponentClassification.Asc76.Lemma22

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  benderBorel_sylowCenter le_sylowCenter_of_card)
open CFSG.ComponentClassification.AS76b (oddCoreIn)
open CFSG.SignalizerFunctor.Helpers (relativeWeakClosure subgroup_le_relative_weak_closure
  relative_weak_closure_le)
open scoped commutatorElement MatrixGroups

theorem commute_of_mulEquiv_psl2 {n : ℕ} (hn : 2 ≤ n) {Y : Type*} [Group Y] [Finite Y]
    (e : Y ≃* PSL(2, GaloisField 2 n)) {B : Subgroup Y} (hB : IsPGroup 2 B) :
    ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
  have : Finite PSL(2, GaloisField 2 n) := Finite.of_equiv Y e.toEquiv
  have hBorel := (CFSG.Open.bender_psl2_borel_full n hn).map_mulEquiv e.symm
  obtain ⟨Q, hBQ⟩ := hB.exists_le_sylow
  obtain ⟨-, -, hZ, hQ⟩ := benderBorel_sylowCenter hBorel Q
  have hle := le_sylowCenter_of_card (T := (Q : Subgroup Y)) (by rw [hZ, hQ, pow_one])
  intro x hx y hy
  exact (mem_sylowCenter.mp (hle (hBQ hy))).2 x (hBQ hx)

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_bar {K X Y : Subgroup G} (hXY : X ≤ Y)
    (hYN : Y ≤ normalizer (K : Set G)) (hY2 : IsPGroup 2 Y)
    (h : bar K Y ≤ normalizer (bar K X : Set (Bar K))) : Y ≤ normalizer (X : Set G) := by
  have hXN : X ≤ normalizer (K : Set G) := hXY.trans hYN
  have hYO : Y ⊓ oddCoreIn K = ⊥ :=
    two_subgroup_of_odd_eq_bot _ (oddCoreIn K) hY2.to_inf_left (core_odd K) inf_le_right
  have hYX : Y ⊓ (X ⊔ oddCoreIn K) ≤ X := by
    rintro p ⟨hpY, hpX⟩
    have hON : X ≤ normalizer (oddCoreIn K : Set G) :=
      hXN.trans (normalizer_le_normalizer_core K)
    rw [sup_comm] at hpX
    obtain ⟨o, ho, x, hx, rfl⟩ := NormalizedProduct.coordinates (oddCoreIn K) X hON p hpX
    have hoY : o ∈ Y := by
      have h1 := Y.mul_mem hpY (Y.inv_mem (hXY hx))
      simpa using h1
    have ho1 : o = 1 := by
      have hmem : o ∈ Y ⊓ oddCoreIn K := ⟨hoY, ho⟩
      rw [hYO] at hmem
      exact hmem
    rw [ho1, one_mul]
    exact hx
  have hconj : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X := by
    intro y hy x hx
    let y' : normalizer (K : Set G) := ⟨y, hYN hy⟩
    let x' : normalizer (K : Set G) := ⟨x, hXN hx⟩
    have h1 : toBar K (y' * x' * y'⁻¹) ∈ bar K X := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp (h (toBar_mem_bar K hy)) _).mp (toBar_mem_bar K hx)
    have h2 : y * x * y⁻¹ ∈ X ⊔ oddCoreIn K := (toBar_mem_bar_iff hXN _).mp h1
    exact hYX ⟨Y.mul_mem (Y.mul_mem hy (hXY hx)) (Y.inv_mem hy), h2⟩
  intro y hy
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hconj y hy x, fun hx => ?_⟩
  have h1 := hconj y⁻¹ (inv_mem hy) _ hx
  simpa [mul_assoc] using h1

theorem bar_inf_of_le_isPGroup {K A B S : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hS2 : IsPGroup 2 S) :
    bar K A ⊓ bar K B = bar K (A ⊓ B) := by
  refine le_antisymm ?_ (le_inf (bar_mono K inf_le_left) (bar_mono K inf_le_right))
  rintro z ⟨hzA, hzB⟩
  obtain ⟨a, ha, rfl⟩ := (mem_bar_iff K A z).mp hzA
  obtain ⟨b, hb, hba⟩ := (mem_bar_iff K B _).mp hzB
  have hab : b = a := toBar_injOn_of_isPGroup hS2 (hBS hb) (hAS ha) hba
  exact toBar_mem_bar K ⟨ha, hab ▸ hb⟩

theorem nonempty_mulEquiv_bar {K P : Subgroup G} (hPN : P ≤ normalizer (K : Set G))
    (hP2 : IsPGroup 2 P) : Nonempty (P ≃* bar K P) := by
  let f : P →* Bar K := (toBar K).comp (inclusion hPN)
  have hf : Function.Injective f := fun u v h => by
    have h1 := toBar_injOn_of_isPGroup (u := inclusion hPN u) (v := inclusion hPN v) hP2 u.2 v.2 h
    have h2 : ((inclusion hPN u : normalizer (K : Set G)) : G) = inclusion hPN v :=
      congrArg Subtype.val h1
    exact Subtype.ext h2
  have hrange : f.range = bar K P := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact toBar_mem_bar K p.2
    · intro hz
      obtain ⟨h, hh, rfl⟩ := (mem_bar_iff K P z).mp hz
      exact ⟨⟨h, hh⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)⟩

theorem le_normalizer_of_dihedral {K J T R : Subgroup G} (hK : TightlyEmbedded K)
    (hJ : TightlyEmbedded J) (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hRT : ¬ R ≤ normalizer (T : Set G))
    (hTc : IsCyclic T) (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) :
    R ≤ normalizer ((R ⊓ normalizer (T : Set G) : Subgroup G) : Set G) := by
  set C := R ⊓ normalizer (T : Set G) with hCdef
  have hcard := card_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR
  have hCc : IsCyclic C := by
    rcases normalizer_alternative hJ hKJ hT hR hTR with hn | ⟨φ, hφ, -⟩
    · exact absurd hn hRT
    · have hbij : Function.Bijective φ := by
        have := Fintype.ofFinite T
        have := Fintype.ofFinite C
        refine (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφ, ?_⟩
        simpa only [Nat.card_eq_fintype_card] using hcard.symm
      exact isCyclic_of_surjective φ hbij.2
  obtain ⟨n, hn, ⟨e⟩⟩ := hRd
  set m := 2 ^ (n - 1) with hm
  have hm0 : m ≠ 0 := by positivity
  have : NeZero m := ⟨hm0⟩
  have hCR : C ≤ R := inf_le_left
  set C' : Subgroup (DihedralGroup m) := (C.subgroupOf R).map e.toMonoidHom with hC'def
  have hC'card : Nat.card C' = Nat.card C := by
    rw [hC'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCR).toEquiv]
  have hnormal : C'.Normal → R ≤ normalizer (C : Set G) := by
    intro hN
    have hN' : (C.subgroupOf R).Normal := by
      have h1 : C.subgroupOf R = C'.comap e.toMonoidHom := by
        rw [hC'def, Subgroup.comap_map_eq_self_of_injective e.injective]
      rw [h1]
      exact hN.comap _
    exact (normal_subgroupOf_iff_le_normalizer hCR).mp hN'
  by_cases h2 : 2 < Nat.card C
  ·
    have : IsCyclic C' := by
      have : IsCyclic (C.subgroupOf R) := isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe hCR).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hCR).symm.surjective
      exact isCyclic_of_surjective ((C.subgroupOf R).equivMapOfInjective _ e.injective).toMonoidHom
        (MulEquiv.surjective _)
    exact hnormal (normal_of_le_rotations (le_rotations_of_isCyclic this (hC'card ▸ h2)))
  ·
    by_cases hm2 : m = 2
    ·
      have hR4 : Nat.card R = 2 ^ 2 := by
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hm2]
        norm_num
      have hRc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hR4
      have hN : (C.subgroupOf R).Normal := ⟨fun a ha g => by
        rw [hRc.is_comm.comm g a, mul_inv_cancel_right]
        exact ha⟩
      exact (normal_subgroupOf_iff_le_normalizer hCR).mp hN
    ·
      have heven : Even m := by
        rw [hm]
        exact (Nat.even_pow' (by omega)).mpr even_two
      have hZcard : Nat.card (AschbacherTheorem3.centerOf R) = 2 := by
        have h1 : (center R).map R.subtype = AschbacherTheorem3.centerOf R :=
          AschbacherToolkit.Bender.map_center_eq_sylowCenter R
        rw [← h1, Subgroup.card_map_of_injective R.subtype_injective,
          Nat.card_congr (Subgroup.centerCongr e).toEquiv]
        exact card_center_dihedralGroup heven hm2 hm0
      obtain ⟨z, hz1, hzZ⟩ : ∃ z, z ≠ 1 ∧ z ∈ AschbacherTheorem3.centerOf R := by
        obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
          ((Subgroup.one_lt_card_iff_ne_bot (AschbacherTheorem3.centerOf R)).mp (by omega))
        exact ⟨z, fun h => hz1 (Subtype.ext h), hz⟩
      have hZeq : ∀ w ∈ AschbacherTheorem3.centerOf R, w ≠ 1 → w = z := by
        intro w hw hw1
        by_contra hwz
        have h3 : 2 < Nat.card (AschbacherTheorem3.centerOf R) := by
          have := Fintype.ofFinite (AschbacherTheorem3.centerOf R)
          rw [Nat.card_eq_fintype_card, Fintype.two_lt_card_iff]
          exact ⟨1, ⟨w, hw⟩, ⟨z, hzZ⟩, fun h => hw1 (congrArg Subtype.val h).symm,
            fun h => hz1 (congrArg Subtype.val h).symm, fun h => hwz (congrArg Subtype.val h)⟩
        omega
      have hzC : z ∈ C := by
        refine ⟨hzZ.1, centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun t ht => ?_)⟩
        have htN : t ∈ normalizer (AschbacherTheorem3.centerOf R : Set G) :=
          normalizer_le_normalizer_centerOf R (hTR ht)
        have h1 : t * z * t⁻¹ ∈ AschbacherTheorem3.centerOf R :=
          (mem_normalizer_iff.mp htN z).mp hzZ
        have h2 : t * z * t⁻¹ ≠ 1 := fun h => hz1 (by
          rw [mul_inv_eq_one] at h
          exact mul_left_cancel (h.trans (mul_one t).symm))
        have h3 := hZeq _ h1 h2
        rw [mul_inv_eq_iff_eq_mul] at h3
        exact h3
      have hZC : AschbacherTheorem3.centerOf R ≤ C := by
        intro w hw
        by_cases hw1 : w = 1
        · rw [hw1]
          exact one_mem C
        · rw [hZeq w hw hw1]
          exact hzC
      have hCeq : AschbacherTheorem3.centerOf R = C :=
        Subgroup.eq_of_le_of_card_ge hZC (by omega)
      rw [← hCeq]
      exact le_normalizer.trans (normalizer_le_normalizer_centerOf R)

theorem inf_normalizer_normal (h3 : AschbacherTheorem3.Theorem3Statement)
    {K J T R : Subgroup G} (hK : TightlyEmbedded K) (hJ : TightlyEmbedded J)
    (hKJ : Odd (Nat.card (K ⊓ J : Subgroup G)))
    (hfac : (Nat.card K).factorization 2 = (Nat.card J).factorization 2)
    (hT : IsSylowOf 2 T (J ⊓ normalizer (K : Set G))) (hT1 : T ≠ ⊥) (hR : IsSylowOf 2 R K)
    (hTR : T ≤ normalizer (R : Set G)) (hmK : 1 < CFSG.Open.pRank 2 K) :
    ((R ⊓ normalizer (T : Set G)).subgroupOf R).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
  by_cases hRT : R ≤ normalizer (T : Set G)
  · rw [inf_eq_left.mpr hRT]
    exact le_normalizer
  have hTJ : T ≤ J := hT.le.trans inf_le_left
  have hTK : T ≤ normalizer (K : Set G) := hT.le.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTKb := inf_eq_bot_of_le hKJ hT2 hTJ
  have hKN : K ≤ normalizer (K : Set G) := le_normalizer
  have hRN : R ≤ normalizer (K : Set G) := hR.le.trans hKN
  have hS2 : IsPGroup 2 (R ⊔ T : Subgroup G) := hR.isPGroup.to_sup_of_normal_left' hT2 hTR
  have hSN : R ⊔ T ≤ normalizer (K : Set G) := sup_le hRN hTK
  have hSsyl : IsSylowOf 2 (R ⊔ T) (K ⊔ T) := isSylowOf_sup hR hT2 hTK hTR hTKb
  have hSNT := isSylowOf_sup_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR
  have hSbar : bar K (R ⊔ T) ⊓ normalizer (bar K T : Set (Bar K)) =
      bar K ((R ⊔ T) ⊓ normalizer (T : Set G)) :=
    (bar_inf_normalizer (sup_le hKN hTK) ((core_le K).trans le_sup_left) hT2 hTK hSsyl.le hS2
      hSNT).1
  have hRbar : bar K (R ⊔ T) ⊓ bar K K = bar K R := by
    rw [← bar_inf_of_core_le (core_le K), sup_inf_eq hR.le hTR hTKb]
  have hbarS : bar K (R ⊔ T) = bar K R ⊔ bar K T := bar_sup hRN hTK
  have hbarKT : bar K R ⊔ bar K T ≤ bar K K ⊔ bar K T := sup_le_sup_right (bar_mono K hR.le) _
  have hSKT : bar K (R ⊔ T) ≤ bar K K ⊔ bar K T := by
    rw [hbarS]
    exact hbarKT
  have hNRbar : bar K R ⊓ normalizer (bar K T : Set (Bar K)) =
      bar K (R ⊓ normalizer (T : Set G)) := by
    have h1 : bar K R ⊓ normalizer (bar K T : Set (Bar K)) =
        bar K R ⊓ (bar K (R ⊔ T) ⊓ normalizer (bar K T : Set (Bar K))) := by
      rw [← inf_assoc, inf_eq_left.mpr (bar_mono K (le_sup_left : R ≤ R ⊔ T))]
    rw [h1, hSbar, bar_inf_of_le_isPGroup le_sup_left inf_le_left hS2, ← inf_assoc,
      inf_eq_left.mpr (le_sup_left : R ≤ R ⊔ T)]
  have hsuff := le_normalizer_of_bar (K := K) (inf_le_left : R ⊓ normalizer (T : Set G) ≤ R)
    hRN hR.isPGroup
  rcases thm3Conclusion h3 hK hJ hKJ hfac hT hT1 hR hTR with
      ⟨hcyc, hRtype, -⟩ | h2 | ⟨n, hn, hO, -, hOc, hOel, -, ⟨eL⟩⟩ |
      ⟨x, -, -, -, -, hW, hNW, -, -⟩ | ⟨hN5, -, hZ1, -, ⟨eZ⟩, -, -⟩
  ·
    obtain ⟨E, hER, hE, hE4⟩ := exists_isElemAbelian_le hR hmK
    have hE2 : IsPGroup 2 E := hR.isPGroup.to_le hER
    have hEb : ∀ y ∈ bar K E, y ^ 2 = 1 := by
      intro y hy
      obtain ⟨u, hu, rfl⟩ := (mem_bar_iff K E y).mp hy
      have hu2 : u ^ 2 = 1 := Subtype.ext (by simpa using hE.2 _ hu)
      rw [← map_pow, hu2, map_one]
    have hEcard : Nat.card (bar K E) = Nat.card E := card_bar_of_isPGroup hE2 (hER.trans hRN)
    rw [hRbar] at hRtype
    have hRd : AschbacherTheorem3.IsDihedralTwoGroup (bar K R) := by
      rcases hRtype with hc | ⟨k, hk, ⟨eQ⟩⟩ | hd
      · exfalso
        have := card_le_two_of_isCyclic (bar_mono K hER) hc hEb
        omega
      · exfalso
        have : NeZero (2 ^ (k - 2)) := ⟨by positivity⟩
        have := card_le_two_of_quaternion eQ (bar_mono K hER) hEb
        omega
      · exact hd
    obtain ⟨k, hk, ⟨eD⟩⟩ := hRd
    obtain ⟨eR⟩ := nonempty_mulEquiv_bar hRN hR.isPGroup
    obtain ⟨eT⟩ := nonempty_mulEquiv_bar hTK hT2
    have hTc : IsCyclic T := isCyclic_of_surjective eT.symm.toMonoidHom eT.symm.surjective
    exact le_normalizer_of_dihedral hK hJ hKJ hfac hT hT1 hR hTR hRT hTc
      ⟨k, hk, ⟨eR.trans eD⟩⟩
  ·
    exfalso
    have h1 := le_normalizer_of_bar (le_sup_right : T ≤ R ⊔ T) hSN hS2 (hSKT.trans h2)
    exact hRT (le_sup_left.trans h1)
  ·
    have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (bar K K ⊔ bar K T)) := fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa using hOel.2 _ x.2)⟩
    have hAc : ∀ a ∈ CFSG.Open.pCoreOf 2 (bar K K ⊔ bar K T),
        ∀ a' ∈ CFSG.Open.pCoreOf 2 (bar K K ⊔ bar K T), a * a' = a' * a := fun a ha a' ha' =>
      congrArg Subtype.val (hOel.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
    have hAL : ∀ a ∈ CFSG.Open.pCoreOf 2 (bar K K ⊔ bar K T),
        ∀ b ∈ AschbacherTheorem3.oTwoPrime (bar K K), a * b = b * a := fun a ha b hb =>
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hOc ha) b hb).symm
    have hL : ∀ B : Subgroup (Bar K), B ≤ AschbacherTheorem3.oTwoPrime (bar K K) →
        IsPGroup 2 B → ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      intro B hB hB2 x hx y hy
      have h1 := commute_of_mulEquiv_psl2 hn eL (B := B.subgroupOf _)
        (hB2.comap_subtype) ⟨x, hB hx⟩ hx ⟨y, hB hy⟩ hy
      exact congrArg Subtype.val h1
    have hSle : bar K (R ⊔ T) ≤ CFSG.Open.pCoreOf 2 (bar K K ⊔ bar K T) ⊔
        AschbacherTheorem3.oTwoPrime (bar K K) := by
      rw [← hO]
      intro y hy
      obtain ⟨j, hj⟩ := (isPGroup_bar hS2) ⟨y, hy⟩
      exact subset_closure ⟨hSKT hy, j, by simpa using congrArg Subtype.val hj⟩
    have hSc := isMulCommutative_of_le_sup hO2 hAc hAL hL (isPGroup_bar hS2) hSle
    intro r hr
    rw [mem_normalizer_iff]
    have hRc : ∀ u ∈ R, ∀ v ∈ R, u * v = v * u := by
      intro u hu v hv
      let u' : normalizer (K : Set G) := ⟨u, hRN hu⟩
      let v' : normalizer (K : Set G) := ⟨v, hRN hv⟩
      have h1 := hSc _ (toBar_mem_bar K (h := u') (mem_sup_left hu)) _
        (toBar_mem_bar K (h := v') (mem_sup_left hv))
      rw [← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (toBar_injOn_of_isPGroup (u := u' * v') (v := v' * u') hS2
        (mul_mem (mem_sup_left hu) (mem_sup_left hv)) (mul_mem (mem_sup_left hv) (mem_sup_left hu))
        h1)
      exact h2
    intro c
    constructor
    · intro hc
      rw [hRc r hr c hc.1, mul_inv_cancel_right]
      exact hc
    · intro hc
      have hcR : c ∈ R := by
        have h1 := R.mul_mem (R.mul_mem (R.inv_mem hr) hc.1) hr
        simpa [mul_assoc] using h1
      rw [hRc r hr c hcR, mul_inv_cancel_right] at hc
      exact hc
  ·
    have hSN' := le_normalizer_of_bar (inf_le_left : (R ⊔ T) ⊓ normalizer (T : Set G) ≤ R ⊔ T)
      hSN hS2 (by rw [← hSbar, ← hW]; exact hSKT.trans hNW)
    intro r hr
    have hr' := hSN' (mem_sup_left hr)
    have h1 : R ⊓ normalizer (T : Set G) = (R ⊔ T) ⊓ normalizer (T : Set G) ⊓ R := by
      rw [inf_comm ((R ⊔ T) ⊓ normalizer (T : Set G)) R, ← inf_assoc,
        inf_eq_left.mpr (le_sup_left : R ≤ R ⊔ T)]
    rw [h1]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hr', le_normalizer hr⟩
  ·
    set Wb := relativeWeakClosure (bar K K) (bar K T) (bar K (R ⊔ T)) with hWb
    have hTW : bar K T ≤ Wb :=
      subgroup_le_relative_weak_closure _ _ _ (bar_mono K le_sup_right)
    have hWS : Wb ≤ bar K (R ⊔ T) := relative_weak_closure_le _ _ _
    have hTbc : ∀ a ∈ bar K T, ∀ b ∈ bar K T, a * b = b * a := by
      intro a ha b hb
      have hc : ∀ u v : AschbacherTheorem3.centerOf Wb, u * v = v * u := fun u v =>
        Subtype.ext ((mem_centralizer_iff.mp v.2.2) u u.2.1)
      have h1 := hc (eZ.symm ⟨a, ha⟩) (eZ.symm ⟨b, hb⟩)
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (eZ.symm.injective h1)
    have hZK : AschbacherTheorem3.centerOf Wb ≤ bar K K := by
      rw [hZ1, commutator_le]
      intro u hu v hv
      have hTKn : bar K T ≤ normalizer (bar K K : Set (Bar K)) := bar_le_normalizer hTK hKN
      exact commutatorElement_mem_of_mem_sup hTKn hTbc ((hWS.trans hSKT) hu) ((hWS.trans hSKT) hv)
    have hZle : AschbacherTheorem3.centerOf Wb ≤ bar K (R ⊓ normalizer (T : Set G)) := by
      rw [← hNRbar]
      intro w hw
      refine ⟨?_, ?_⟩
      · rw [← hRbar]
        exact ⟨hWS hw.1, hZK hw⟩
      · exact centralizer_le_normalizer _ (centralizer_le hTW hw.2)
    have hcardZ : Nat.card (AschbacherTheorem3.centerOf Wb) = Nat.card T := by
      rw [Nat.card_congr eZ.toEquiv, card_bar_of_isPGroup hT2 hTK]
    have hcardN : Nat.card (bar K (R ⊓ normalizer (T : Set G))) = Nat.card T := by
      rw [card_bar_of_isPGroup (hR.isPGroup.to_le inf_le_left) (inf_le_left.trans hRN),
        card_inf_normalizer hK hJ hKJ hfac hT hT1 hR hTR]
    have heq : AschbacherTheorem3.centerOf Wb = bar K (R ⊓ normalizer (T : Set G)) :=
      Subgroup.eq_of_le_of_card_ge hZle (by rw [hcardZ, hcardN])
    refine hsuff ?_
    rw [← heq]
    exact (((bar_mono K (le_sup_left : R ≤ R ⊔ T)).trans hSKT).trans hN5).trans
      (normalizer_le_normalizer_centerOf Wb)

end CFSG.ComponentClassification.Asc76.Lemma22
