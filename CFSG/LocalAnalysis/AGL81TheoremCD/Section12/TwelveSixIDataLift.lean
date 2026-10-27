module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.GroupTheory.Frattini.PSubgroupLift
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.RankThreeUC.AGL81C Subgroup

private lemma exists_sl2_inverting_pair (F : Type*) [Field F] [CharP F 2] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F,
      a ^ 3 = 1 ∧ b * a * b⁻¹ = a⁻¹ ∧
        a ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
  let A : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩
  let B : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩
  have hA3 : A ^ 3 = 1 := by
    refine Subtype.ext ?_
    show (A : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, Matrix.mul_fin_two,
      Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have hB2 : B * B = 1 := by
    refine Subtype.ext ?_
    show (B : Matrix (Fin 2) (Fin 2) F) * B = 1
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have hBAB : B * A * B = A ^ 2 := by
    refine Subtype.ext ?_
    show ((B : Matrix (Fin 2) (Fin 2) F) * A) * B = (A : Matrix (Fin 2) (Fin 2) F) ^ 2
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two, pow_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, B, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have hA2inv : A ^ 2 = A⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hA3])
  have hBA : B * A * B⁻¹ = A⁻¹ := by
    rw [inv_eq_of_mul_eq_one_left hB2, hBAB, hA2inv]
  have hAnc : A ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro hA
    have h := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hA 0
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F ↦ M 1 1) h
    simp [A, Matrix.scalar_apply] at h11
  exact ⟨A, B, hA3, hBA, hAnc⟩

theorem exists_ne_one_pow_three_eq_one_inv_of_isPSLType_two {n : ℕ} {X : Type} [Group X]
    (hX : IsPSLType 2 (GaloisField 2 n) X) :
    ∃ x w : X, x ≠ 1 ∧ x ^ 3 = 1 ∧ w * x * w⁻¹ = x⁻¹ := by
  obtain ⟨e⟩ := hX
  classical
  obtain ⟨A, B, hA3, hBA, hAnc⟩ := exists_sl2_inverting_pair (GaloisField 2 n)
  let q : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) →*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)))
  have hqA : q A ≠ 1 := by
    intro h1
    exact hAnc (QuotientGroup.eq_one_iff A |>.mp h1)
  have hqA3 : q A ^ 3 = 1 := by
    rw [← map_pow, hA3, map_one]
  have hqBA : q B * q A * (q B)⁻¹ = (q A)⁻¹ := by
    have h : q B * q A * (q B)⁻¹ = q (B * A * B⁻¹) := by
      simp [map_mul, map_inv, mul_assoc]
    rw [h, hBA, map_inv]
  refine ⟨e.symm (q A), e.symm (q B), ?_, ?_, ?_⟩
  · intro h1
    exact hqA (e.symm.injective (h1.trans (map_one e.symm).symm))
  · rw [← map_pow, hqA3, map_one]
  · have h1 : e.symm (q B) * e.symm (q A) * (e.symm (q B))⁻¹ =
        e.symm (q B * q A * (q B)⁻¹) := by
      simp [map_mul, map_inv]
    rw [h1, hqBA, map_inv]

variable {G : Type} [Group G] [Finite G]

private lemma exists_inverting_element_of_sylow_complement {L H : Type*} [Group L] [Finite L]
    [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    {A : Subgroup L} {Astar : Subgroup H} [IsMulCommutative Astar]
    (hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A (Astar.comap f))
    (hAmap : A.map f = Astar) (hAdisj : A ⊓ f.ker = ⊥) {w : L}
    (hwnorm : f w ∈ Subgroup.normalizer (Astar : Set H))
    (hwinv : ∀ y ∈ Astar, f w * y * (f w)⁻¹ = y⁻¹) :
    ∃ m ∈ Subgroup.normalizer (A : Set L), ∀ a ∈ A, m * a * m⁻¹ = a⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAle : A ≤ Astar.comap f := by
    rw [← Subgroup.map_le_iff_le_comap, hAmap]
  obtain ⟨n, hnN, m, hmNorm, hnm⟩ :=
    CFSG.GroupTheory.exists_mul_mem_comap_and_normalizer (p := 3) f hAle hAsyl hwnorm
  have hnA : f n ∈ Astar := hnN
  have hfmul : f n * f m = f w := by
    rw [← map_mul, ← hnm]
  have hfm : f m = (f n)⁻¹ * f w := by
    rw [← hfmul]
    group
  have hmA : ∀ a ∈ A, m * a * m⁻¹ = a⁻¹ := by
    intro a ha
    have hma : m * a * m⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hmNorm a).mp ha
    have hfaA : f a ∈ Astar := by
      rw [← hAmap]
      exact Subgroup.mem_map_of_mem f ha
    have hfa : f (m * a * m⁻¹) = (f a)⁻¹ := by
      have h1 : f (m * a * m⁻¹) = f m * f a * (f m)⁻¹ := by
        rw [map_mul, map_mul, map_inv]
      rw [h1, hfm]
      calc (f n)⁻¹ * f w * f a * ((f n)⁻¹ * f w)⁻¹
          = (f n)⁻¹ * (f w * f a * (f w)⁻¹) * f n := by group
        _ = (f n)⁻¹ * (f a)⁻¹ * f n := by rw [hwinv (f a) hfaA]
        _ = (f a)⁻¹ := by
            have hcomm : (f n)⁻¹ * (f a)⁻¹ = (f a)⁻¹ * (f n)⁻¹ := by
              have hc := mul_comm' (⟨(f n)⁻¹, Astar.inv_mem hnA⟩ : Astar)
                (⟨(f a)⁻¹, Astar.inv_mem hfaA⟩ : Astar)
              simpa using congrArg (fun z : Astar => (z : H)) hc
            rw [hcomm, mul_assoc, inv_mul_cancel, mul_one]
    have hmem : (m * a * m⁻¹) * a = 1 := by
      have hker : (m * a * m⁻¹) * a ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, hfa, inv_mul_cancel]
      have hAb : (m * a * m⁻¹) * a ∈ A := A.mul_mem hma ha
      have hbot : (m * a * m⁻¹) * a ∈ (⊥ : Subgroup L) := by
        rw [← hAdisj]
        exact ⟨hAb, hker⟩
      exact hbot
    exact eq_inv_of_mul_eq_one_left hmem
  exact ⟨m, hmNorm, hmA⟩

private lemma exists_sylow_three_map_of_card_three {L H : Type*} [Group L] [Finite L]
    [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    (hkerP : IsPGroup 2 f.ker) {Astar : Subgroup H} (hAstar : Nat.card Astar = 3) :
    ∃ A : Subgroup L, CFSG.ABGLocalTools.IsSylowOf 3 A (Astar.comap f) ∧
      A.map f = Astar ∧ A ⊓ f.ker = ⊥ ∧ Nat.card A = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker3 : ¬ 3 ∣ Nat.card f.ker := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hkerP
    rw [hk]
    intro hdvd
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
    norm_num at h32
  let N : Subgroup L := Astar.comap f
  have hNcard : Nat.card N = Nat.card f.ker * 3 := by
    rw [show N = Astar.comap f from rfl,
      CFSG.GroupTheory.card_comap_eq_card_ker_mul_card f hf Astar, hAstar]
  obtain ⟨Q⟩ : Nonempty (Sylow 3 N) := inferInstance
  let A : Subgroup L := (Q : Subgroup N).map N.subtype
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf 3 A N := ⟨Q, rfl⟩
  have hA3 : Nat.card A = 3 := by
    rw [hAsyl.card_eq]
    have hfac : (Nat.card N).factorization 3 = 1 := by
      rw [hNcard, Nat.factorization_mul (Nat.card_pos.ne') (by norm_num), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hker3, Nat.Prime.factorization_self (by norm_num)]
    rw [hfac, pow_one]
  have hA3grp : IsPGroup 3 A := Q.isPGroup'.map N.subtype
  have hAdisj : A ⊓ f.ker = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) A f.ker hA3grp hkerP)
  have hAmap : A.map f = Astar := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact Subgroup.map_subtype_le (Q : Subgroup N)
    · have hdvd : Nat.card (A.map f) ∣ Nat.card A := Subgroup.card_map_dvd (H := A) f
      rw [hA3] at hdvd
      have hne : Nat.card (A.map f) ≠ 1 := by
        intro h1
        have hbot : A.map f = ⊥ := Subgroup.card_eq_one.mp h1
        have hAle : A ≤ f.ker := by
          intro a ha
          have hmem : f a ∈ A.map f := Subgroup.mem_map_of_mem f ha
          rw [hbot] at hmem
          exact hmem
        have hAbot : A = ⊥ := by
          rw [eq_bot_iff]
          intro a ha
          have hmem : a ∈ A ⊓ f.ker := ⟨ha, hAle ha⟩
          rw [hAdisj] at hmem
          exact hmem
        have hc1 : Nat.card A = 1 := by rw [hAbot, Subgroup.card_bot]
        rw [hc1] at hA3
        norm_num at hA3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd h1 hne
      · rw [h3, hAstar]
  exact ⟨A, hAsyl, hAmap, hAdisj, hA3⟩

private lemma conj_mk_zpowers_eq_inv {C P : Subgroup G} (hPC : P ≤ C)
    [(P.subgroupOf C).Normal] {x w : G} (hx : x ∈ C) (hw : w ∈ C)
    (hwx : w * x * w⁻¹ * x ∈ P) :
    QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩ ∈
        Subgroup.normalizer (Subgroup.zpowers (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩)
          : Set (↥C ⧸ P.subgroupOf C)) ∧
      ∀ y ∈ Subgroup.zpowers (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩),
        QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩ * y *
          (QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩)⁻¹ = y⁻¹ := by
  classical
  have hwxC : w * x * w⁻¹ ∈ C := C.mul_mem (C.mul_mem hw hx) (C.inv_mem hw)
  have hwxC' : w * x * w⁻¹ * x ∈ C := hPC hwx
  have hconjval : QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩ *
      QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩ *
      (QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩)⁻¹ =
      QuotientGroup.mk' (P.subgroupOf C) ⟨w * x * w⁻¹, hwxC⟩ := by
    show QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩ *
      QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩ *
      (QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩)⁻¹ =
      QuotientGroup.mk' (P.subgroupOf C) ⟨w * x * w⁻¹, hwxC⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hwxq : QuotientGroup.mk' (P.subgroupOf C) ⟨w * x * w⁻¹, hwxC⟩ =
      (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩)⁻¹ := by
    have h1 : QuotientGroup.mk' (P.subgroupOf C) ⟨w * x * w⁻¹, hwxC⟩ *
        QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩ = 1 := by
      rw [show QuotientGroup.mk' (P.subgroupOf C) ⟨w * x * w⁻¹, hwxC⟩ *
        QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩ =
        QuotientGroup.mk' (P.subgroupOf C) (⟨w * x * w⁻¹, hwxC⟩ * ⟨x, hx⟩) from
          (map_mul _ _ _).symm]
      have h2 : (⟨w * x * w⁻¹, hwxC⟩ * ⟨x, hx⟩ : ↥C) =
          ⟨w * x * w⁻¹ * x, hwxC'⟩ := Subtype.ext rfl
      rw [h2]
      exact (QuotientGroup.eq_one_iff _).mpr hwx
    exact eq_inv_of_mul_eq_one_left h1
  have hqconj : MulAut.conj (QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩)
      (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩) =
      (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩)⁻¹ := by
    rw [MulAut.conj_apply, hconjval, hwxq]
  constructor
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Subgroup.zpowers (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩)).map
      (MulAut.conj (QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩)) =
      Subgroup.zpowers (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩)
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (MulAut.conj (QuotientGroup.mk' (P.subgroupOf C) ⟨w, hw⟩)
      (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩)) =
      Subgroup.zpowers (QuotientGroup.mk' (P.subgroupOf C) ⟨x, hx⟩)
    rw [hqconj, Subgroup.zpowers_inv]
  · intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← MulAut.conj_apply, map_zpow, hqconj, inv_zpow]

theorem exists_card_three_inverted_of_mem_of_pGroup {C P : Subgroup G} (hPC : P ≤ C)
    (hCP : C ≤ normalizer (P : Set G)) (hP : IsPGroup 2 P) {x w : G} (hx : x ∈ C) (hw : w ∈ C)
    (hx1 : x ∉ P) (hx3 : x ^ 3 ∈ P) (hwx : w * x * w⁻¹ * x ∈ P) :
    ∃ W : Subgroup G, W ≤ C ∧ Nat.card W = 3 ∧ ∃ s ∈ C, ∀ y ∈ W, s * y * s⁻¹ = y⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPn : (P.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mpr hCP
  letI : (P.subgroupOf C).Normal := hPn
  let f : ↥C →* (↥C ⧸ P.subgroupOf C) := QuotientGroup.mk' (P.subgroupOf C)
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  let q : ↥C ⧸ P.subgroupOf C := f ⟨x, hx⟩
  have hq1 : q ≠ 1 := by
    intro h
    exact hx1 ((QuotientGroup.eq_one_iff (⟨x, hx⟩ : ↥C)).mp h)
  have hq3 : q ^ 3 = 1 := by
    show f ⟨x, hx⟩ ^ 3 = 1
    rw [← map_pow]
    have h : (⟨x, hx⟩ : ↥C) ^ 3 = ⟨x ^ 3, hPC hx3⟩ := Subtype.ext rfl
    rw [h]
    exact (QuotientGroup.eq_one_iff _).mpr hx3
  have hqord : orderOf q = 3 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hq3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq1
    · exact h
  let Astar : Subgroup (↥C ⧸ P.subgroupOf C) := Subgroup.zpowers q
  have hAstar : Nat.card Astar = 3 := by
    rw [show Astar = Subgroup.zpowers q from rfl, Nat.card_zpowers, hqord]
  have hkerP : IsPGroup 2 f.ker := by
    rw [show f.ker = P.subgroupOf C from QuotientGroup.ker_mk' _]
    exact hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  have hker3 : ¬ 3 ∣ Nat.card f.ker := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hkerP
    rw [hk]
    intro hdvd
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd
    norm_num at h32
  obtain ⟨hwnorm, hwinv⟩ := conj_mk_zpowers_eq_inv (P := P) hPC hx hw hwx
  obtain ⟨A, hAsyl, hAmap, hAdisj, hA3⟩ :=
    exists_sylow_three_map_of_card_three f hf hkerP hAstar
  haveI : IsMulCommutative Astar := Subgroup.zpowers_isMulCommutative q
  obtain ⟨m, hmNorm, hmA⟩ :=
    exists_inverting_element_of_sylow_complement f hf hAsyl hAmap hAdisj hwnorm hwinv
  refine ⟨A.map C.subtype, Subgroup.map_subtype_le A, ?_, ⟨C.subtype m, m.2, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective, hA3]
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : C.subtype m * C.subtype a * (C.subtype m)⁻¹ = C.subtype (m * a * m⁻¹) := by
      simp [map_mul, map_inv, mul_assoc]
    rw [h1, hmA a ha, map_inv]

private lemma exists_mem_lift_pCore_quotient {I C : Subgroup G} (hCI : C ≤ I)
    (hcov : C ⊔ (pCore 2 ↥I).map I.subtype = I) (xb : ↥I ⧸ pCore 2 ↥I) :
    ∃ x : G, ∃ hx : x ∈ C, QuotientGroup.mk' (pCore 2 ↥I) ⟨x, hCI hx⟩ = xb := by
  classical
  let P : Subgroup G := (pCore 2 ↥I).map I.subtype
  have hPI : P ≤ I := Subgroup.map_subtype_le _
  have hPin : I ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype I (pCore 2 ↥I)
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥I) xb
  haveI : (P.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPI).mpr hPin
  have hsup : (C.subgroupOf I) ⊔ (P.subgroupOf I) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCI hPI, hcov, Subgroup.subgroupOf_self]
  have hy' : y ∈ (C.subgroupOf I) ⊔ (P.subgroupOf I) := by rw [hsup]; trivial
  obtain ⟨c, hcC, p, hpP, hcp⟩ := Subgroup.mem_sup_of_normal_right.mp hy'
  obtain ⟨p₀, hp₀, hpp⟩ := Subgroup.mem_map.mp hpP
  have hpker : QuotientGroup.mk' (pCore 2 ↥I) p = 1 := by
    rw [show p = ⟨I.subtype p₀, p₀.2⟩ from Subtype.ext hpp.symm]
    exact (QuotientGroup.eq_one_iff _).mpr hp₀
  refine ⟨(c : G), hcC, ?_⟩
  calc QuotientGroup.mk' (pCore 2 ↥I) (⟨(c : G), hCI hcC⟩ : ↥I) =
      QuotientGroup.mk' (pCore 2 ↥I) c := rfl
    _ = QuotientGroup.mk' (pCore 2 ↥I) c * 1 := (mul_one _).symm
    _ = QuotientGroup.mk' (pCore 2 ↥I) c * QuotientGroup.mk' (pCore 2 ↥I) p := by rw [hpker]
    _ = QuotientGroup.mk' (pCore 2 ↥I) (c * p) :=
      (map_mul (QuotientGroup.mk' (pCore 2 ↥I)) c p).symm
    _ = QuotientGroup.mk' (pCore 2 ↥I) y := by rw [hcp]
    _ = xb := hy


theorem exists_card_three_inverted_of_sup_pCore_eq {n : ℕ} {I C : Subgroup G}
    (hI : IsPSLType 2 (GaloisField 2 n) (↥I ⧸ pCore 2 ↥I))
    (hcov : C ⊔ (pCore 2 ↥I).map I.subtype = I) :
    ∃ W : Subgroup G, W ≤ C ∧ Nat.card W = 3 ∧ ∃ s ∈ C, ∀ y ∈ W, s * y * s⁻¹ = y⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup G := (pCore 2 ↥I).map I.subtype
  have hCI : C ≤ I := hcov ▸ le_sup_left
  have hPI : P ≤ I := Subgroup.map_subtype_le _
  have hPp : IsPGroup 2 P := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).map I.subtype
  have hPin : I ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.ABGLocalTools.le_normalizer_map_subtype I (pCore 2 ↥I)
  let φ : ↥I →* (↥I ⧸ pCore 2 ↥I) := QuotientGroup.mk' (pCore 2 ↥I)
  obtain ⟨xb, wb, hxb1, hxb3, hwb⟩ :=
    exists_ne_one_pow_three_eq_one_inv_of_isPSLType_two hI
  obtain ⟨x, hxC, hxφ'⟩ := exists_mem_lift_pCore_quotient hCI hcov xb
  obtain ⟨w, hwC, hwφ'⟩ := exists_mem_lift_pCore_quotient hCI hcov wb
  have hxφ : φ ⟨x, hCI hxC⟩ = xb := hxφ'
  have hwφ : φ ⟨w, hCI hwC⟩ = wb := hwφ'
  have hxP' : x ∉ C ⊓ P := by
    intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx.2
    have hxpcore : (⟨x, hCI hxC⟩ : ↥I) ∈ pCore 2 ↥I := by
      rw [show (⟨x, hCI hxC⟩ : ↥I) = y from Subtype.ext hyx.symm]
      exact hy
    have h1 : φ ⟨x, hCI hxC⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hxpcore
    exact hxb1 (hxφ ▸ h1)
  have hx3P' : x ^ 3 ∈ C ⊓ P := by
    have hx3C : x ^ 3 ∈ C := C.pow_mem hxC 3
    refine ⟨hx3C, ?_⟩
    have h1 : (⟨x ^ 3, hCI hx3C⟩ : ↥I) = ⟨x, hCI hxC⟩ ^ 3 := Subtype.ext rfl
    have hq : φ ⟨x ^ 3, hCI hx3C⟩ = 1 := by
      rw [h1, map_pow, hxφ, hxb3]
    exact Subgroup.mem_map_of_mem I.subtype ((QuotientGroup.eq_one_iff _).mp hq)
  have hwxP' : w * x * w⁻¹ * x ∈ C ⊓ P := by
    have hwxC : w * x * w⁻¹ * x ∈ C :=
      C.mul_mem (C.mul_mem (C.mul_mem hwC hxC) (C.inv_mem hwC)) hxC
    refine ⟨hwxC, ?_⟩
    have h1 : (⟨w * x * w⁻¹ * x, hCI hwxC⟩ : ↥I) =
        ⟨w, hCI hwC⟩ * ⟨x, hCI hxC⟩ * ⟨w, hCI hwC⟩⁻¹ * ⟨x, hCI hxC⟩ := Subtype.ext rfl
    have hq : φ ⟨w * x * w⁻¹ * x, hCI hwxC⟩ = 1 := by
      rw [h1]
      simp only [map_mul, map_inv, hwφ, hxφ, hwb, inv_mul_cancel]
    exact Subgroup.mem_map_of_mem I.subtype ((QuotientGroup.eq_one_iff _).mp hq)
  have hCnorm : C ≤ Subgroup.normalizer ((C ⊓ P : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hc1 : C.map ((MulAut.conj c) : G →* G) = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hc)
    have hc2 : P.map ((MulAut.conj c) : G →* G) = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPin (hCI hc))
    rw [Subgroup.map_inf C P ((MulAut.conj c) : G →* G) (MulAut.conj c).injective, hc1, hc2]
  obtain ⟨W, hWC, hWcard, s, hsC, hsinv⟩ :=
    exists_card_three_inverted_of_mem_of_pGroup (C := C) (P := C ⊓ P) inf_le_left hCnorm
      hPp.to_inf_right hxC hwC hxP' hx3P' hwxP'
  exact ⟨W, hWC, hWcard, s, hsC, hsinv⟩

private lemma exists_conj_eq_of_le_sup_pGroup {I O V : Subgroup G} (hOI : O ≤ I)
    (hIO : I ≤ normalizer (O : Set G)) (hO : IsPGroup 2 O) (hVI : V ≤ I)
    (hV : IsPGroup 3 V) {s : G} (hsV : ∀ v ∈ V, s * v * s⁻¹ ∈ V ⊔ O) :
    ∃ k ∈ V ⊔ O, ∀ x : G, x ∈ V.map ((MulAut.conj s) : G →* G) ↔ k⁻¹ * x * k ∈ V := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set VO : Subgroup G := V ⊔ O with hVO
  have hVOI : VO ≤ I := sup_le hVI hOI
  have hdisj : V ⊓ O = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) V O hV hO)
  haveI hOnI : (O.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOI).mpr hIO
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hO
    rw [hj]
    intro hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) hdvd) (by norm_num)
  have hrel : V.relIndex VO = Nat.card O := by
    have hsup : VO.subgroupOf I = O.subgroupOf I ⊔ V.subgroupOf I := by
      rw [show VO = O ⊔ V from (sup_comm V O), Subgroup.subgroupOf_sup hOI hVI]
    have h3 : (V.subgroupOf I).relIndex (VO.subgroupOf I) =
        (V.subgroupOf I).relIndex (O.subgroupOf I) := by
      rw [hsup]
      exact CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal _ _
    have h1 := Subgroup.relIndex_subgroupOf (H := V) (K := VO) hVOI
    have h2 := Subgroup.relIndex_subgroupOf (H := V) (K := O) hOI
    have h4 := Subgroup.relIndex_mul_card (H := V) (K := O)
    rw [hdisj, Subgroup.card_bot, mul_one] at h4
    rw [← h1, h3, h2, h4]
  have hVsyl : CFSG.ABGLocalTools.IsSylowOf 3 V VO := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_sup_left, hV, by rw [hrel]; exact hO3⟩
  have hsVO : V.map ((MulAut.conj s) : G →* G) ≤ VO := by
    rintro y ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using hsV v hv
  have hcard_conj : Nat.card (V.map ((MulAut.conj s) : G →* G)) = Nat.card V :=
    Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hsVsyl : CFSG.ABGLocalTools.IsSylowOf 3
      (V.map ((MulAut.conj s) : G →* G)) VO := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hsVO, hV.map _, ?_⟩
    have h1 := Subgroup.relIndex_mul_card
      (H := V.map ((MulAut.conj s) : G →* G)) (K := VO)
    rw [inf_eq_left.mpr hsVO, hcard_conj] at h1
    have h2 := Subgroup.relIndex_mul_card (H := V) (K := VO)
    rw [inf_eq_left.mpr le_sup_left] at h2
    have hrel' : (V.map ((MulAut.conj s) : G →* G)).relIndex VO = V.relIndex VO :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
    rw [hrel', hrel]
    exact hO3
  exact hVsyl.exists_mem_conj hsVsyl

theorem exists_conj_mem_of_conj_mem_sup {I O V : Subgroup G} (hOI : O ≤ I)
    (hIO : I ≤ normalizer (O : Set G)) (hO : IsPGroup 2 O) (hVI : V ≤ I) (hV : IsPGroup 3 V)
    {s : G} (hs : s ∈ I) (hsV : ∀ v ∈ V, s * v * s⁻¹ ∈ V ⊔ O) :
    ∃ t ∈ I, ∀ v ∈ V, t * v * t⁻¹ ∈ V ∧ (s * v * s⁻¹)⁻¹ * (t * v * t⁻¹) ∈ O := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set VO : Subgroup G := V ⊔ O with hVO
  have hVOI : VO ≤ I := sup_le hVI hOI
  haveI : (O.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOI).mpr hIO
  obtain ⟨k, hkVO, hkconj⟩ := exists_conj_eq_of_le_sup_pGroup hOI hIO hO hVI hV hsV
  have hkI : k⁻¹ ∈ I := I.inv_mem (hVOI hkVO)
  have hksup : (⟨k⁻¹, hkI⟩ : ↥I) ∈ (V.subgroupOf I) ⊔ (O.subgroupOf I) := by
    rw [← Subgroup.subgroupOf_sup hVI hOI]
    exact VO.inv_mem hkVO
  obtain ⟨v, hvV, o, hoO, hvo⟩ := Subgroup.mem_sup_of_normal_right.mp hksup
  have hkval : k = (o : G)⁻¹ * (v : G)⁻¹ := by
    have h1 : (v : G) * (o : G) = k⁻¹ := by simpa using congrArg Subtype.val hvo
    calc k = (k⁻¹)⁻¹ := (inv_inv k).symm
      _ = ((v : G) * (o : G))⁻¹ := by rw [h1]
      _ = (o : G)⁻¹ * (v : G)⁻¹ := mul_inv_rev _ _
  refine ⟨(o : G) * s, I.mul_mem (hOI hoO) hs, ?_⟩
  intro v₀ hv₀
  have hsv : s * v₀ * s⁻¹ ∈ V.map ((MulAut.conj s) : G →* G) := by
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem ((MulAut.conj s) : G →* G) hv₀
  have hkV : k⁻¹ * (s * v₀ * s⁻¹) * k ∈ V := (hkconj _).mp hsv
  have hkey : k⁻¹ * (s * v₀ * s⁻¹) * k =
      (v : G) * (((o : G) * s) * v₀ * ((o : G) * s)⁻¹) * (v : G)⁻¹ := by
    rw [hkval]
    group
  have hyV : ((o : G) * s) * v₀ * ((o : G) * s)⁻¹ ∈ V := by
    have h1 : (v : G) * (((o : G) * s) * v₀ * ((o : G) * s)⁻¹) * (v : G)⁻¹ ∈ V :=
      hkey ▸ hkV
    have h2 : ((o : G) * s) * v₀ * ((o : G) * s)⁻¹ =
        (v : G)⁻¹ * ((v : G) * (((o : G) * s) * v₀ * ((o : G) * s)⁻¹) * (v : G)⁻¹) *
          (v : G) := by
      group
    rw [h2]
    exact V.mul_mem (V.mul_mem (V.inv_mem hvV) h1) hvV
  have hyI : ((o : G) * s) * v₀ * ((o : G) * s)⁻¹ ∈ I := hVI hyV
  have hyO : ((((o : G) * s) * v₀ * ((o : G) * s)⁻¹)⁻¹ * (o : G) *
      (((o : G) * s) * v₀ * ((o : G) * s)⁻¹)) ∈ O := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hIO (I.inv_mem hyI)) (o : G)).mp hoO
  refine ⟨hyV, ?_⟩
  have hsv_eq : s * v₀ * s⁻¹ =
      (o : G)⁻¹ * (((o : G) * s) * v₀ * ((o : G) * s)⁻¹) * (o : G) := by
    group
  rw [hsv_eq]
  have h3 : ((o : G)⁻¹ * (((o : G) * s) * v₀ * ((o : G) * s)⁻¹) * (o : G))⁻¹ *
      (((o : G) * s) * v₀ * ((o : G) * s)⁻¹) =
      (o : G)⁻¹ * (((((o : G) * s) * v₀ * ((o : G) * s)⁻¹))⁻¹ * (o : G) *
        (((o : G) * s) * v₀ * ((o : G) * s)⁻¹)) := by
    group
  rw [h3]
  exact O.mul_mem (O.inv_mem hoO) hyO

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
