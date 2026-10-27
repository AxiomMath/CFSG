module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourCentral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourExtension
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitDihedralExtension
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitHypothesisISupport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveTwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple

public section

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open CFSG.Open AschbacherToolkit

theorem hasDihedralGenerators_dihedralGroup {k : ℕ} (hk : 2 ≤ k) :
    HasDihedralGenerators (DihedralGroup k) := by
  have : NeZero k := ⟨by omega⟩
  refine ⟨DihedralGroup.r 1, DihedralGroup.sr 0, ?_, ?_, ?_, ?_⟩
  · have hr : ∀ i : ZMod k, DihedralGroup.r i ∈ Subgroup.zpowers (DihedralGroup.r 1) :=
      fun i => Subgroup.mem_zpowers_iff.mpr ⟨(i.val : ℤ), by simp⟩
    rw [eq_top_iff]
    rintro (i | i) -
    · exact Subgroup.mem_sup_left (hr i)
    · have h : DihedralGroup.sr i = DihedralGroup.r (-i) * DihedralGroup.sr 0 := by
        rw [DihedralGroup.r_mul_sr, zero_sub, neg_neg]
      rw [h]
      exact Subgroup.mul_mem_sup (hr _) (Subgroup.mem_zpowers _)
  · rw [sq, DihedralGroup.sr_mul_self]
  · rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
      DihedralGroup.inv_r]
    simp
  · intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [DihedralGroup.r_one_zpow] at hj
    cases hj

theorem exists_orderOf_eq_two_pow_of_zpowers {G : Type*} [Group G] {y : G}
    (hy : IsPGroup 2 (Subgroup.zpowers y)) : ∃ k : ℕ, orderOf y = 2 ^ k := by
  obtain ⟨n, hn⟩ := hy ⟨y, Subgroup.mem_zpowers y⟩
  have h : y ^ 2 ^ n = 1 := congrArg Subtype.val hn
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h)
  exact ⟨k, hk⟩

theorem isCyclic_of_central_of_sq_ne_one {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hr : CFSG.Open.pRank 2 Q ≤ 1) {y : G} (hyQ : y ∈ Q)
    (hyc : ∀ q ∈ Q, q * y = y * q) (hy2 : y ^ 2 ≠ 1) : IsCyclic Q := by
  rcases SectionSix.cyclic_or_quaternion_of_pRank_le_one hQ hr with hcyc | ⟨n, hn, ⟨e⟩⟩
  · exact hcyc
  · exfalso
    have hm : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc : e ⟨y, hyQ⟩ ∈ Subgroup.center (QuaternionGroup (2 ^ (n - 2))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨q, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hyc q q.2))
    have hdvd := Subgroup.orderOf_dvd_natCard _ hc
    rw [CFSG.Semidihedral.QuaternionAutomorphismLifting.center_card _ hm, MulEquiv.orderOf_eq,
      Subgroup.orderOf_mk] at hdvd
    exact hy2 (orderOf_dvd_iff_pow_eq_one.mp hdvd)

theorem pow_four_eq_one_of_quotient {G : Type} [Group G] [Finite G] (hG : Group.IsPerfect G)
    (P : Sylow 2 G) {a : (P : Subgroup G)} (ha2 : (a : G) ^ 2 ∈ Subgroup.center G)
    (Z₀ : Subgroup (P : Subgroup G)) [Z₀.Normal] (hZ₀ : Z₀ = Subgroup.zpowers (a ^ 2))
    (h : (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P : Subgroup G) ⧸ Z₀ ≃* DihedralGroup (2 ^ (n - 1)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty ((P : Subgroup G) ⧸ Z₀ ≃* SemidihedralGroup n))) :
    a ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZg : Z₀.map (P : Subgroup G).subtype = Subgroup.zpowers ((a : G) ^ 2) := by
    rw [hZ₀, MonoidHom.map_zpowers]
    rfl
  have hZgc : Z₀.map (P : Subgroup G).subtype ≤ Subgroup.center G :=
    hZg ▸ Subgroup.zpowers_le.mpr ha2
  have hZgp : IsPGroup 2 (Z₀.map (P : Subgroup G).subtype) :=
    (P.isPGroup'.to_subgroup Z₀).map _
  have h8 := central_sylow_commutator P hZgc hZgp
  rw [hG.commutator_eq_top, inf_top_eq] at h8
  have hZD : Z₀ ≤ commutator (P : Subgroup G) := by
    intro z hz
    have hzg : (z : G) ∈ Z₀.map (P : Subgroup G).subtype := ⟨z, hz, rfl⟩
    rw [h8] at hzg
    obtain ⟨-, q, hq, hqz⟩ := hzg
    rwa [← Subtype.ext hqz]
  have hZc : Z₀ ≤ Subgroup.center (P : Subgroup G) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZgc ⟨z, hz, rfl⟩) g)
  have hsq : (a ^ 2) ^ 2 = 1 → a ^ 4 = 1 := fun h1 => by rw [← pow_mul] at h1; exact h1
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  ·
    let f := e.toMonoidHom.comp (QuotientGroup.mk' Z₀)
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Z₀)
    have hker : f.ker = Z₀ := by
      ext g
      simp [f]
    have hk : 2 ≤ 2 ^ (n - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcard := dihedral_central_extension_card_le f hf (hker ▸ hZc)
      (hasDihedralGenerators_dihedralGroup hk)
    rw [hker, inf_of_le_left hZD, hZ₀, Nat.card_zpowers] at hcard
    apply hsq
    have hpos := orderOf_pos (a ^ 2)
    rcases (show orderOf (a ^ 2) = 1 ∨ orderOf (a ^ 2) = 2 by omega) with h1 | h1
    · rw [orderOf_eq_one_iff] at h1
      rw [h1, one_pow]
    · have h2 := pow_orderOf_eq_one (a ^ 2)
      rwa [h1] at h2
  ·
    let f := e.toMonoidHom.comp (QuotientGroup.mk' Z₀)
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Z₀)
    have hker : f.ker = Z₀ := by
      ext g
      simp [f]
    have hbot := semidihedral_central_extension hn f hf (hker ▸ hZc)
    rw [hker, inf_of_le_left hZD] at hbot
    have h1 : a ^ 2 = 1 := by
      have : a ^ 2 ∈ Z₀ := hZ₀ ▸ Subgroup.mem_zpowers _
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    apply hsq
    rw [h1, one_pow]

theorem orderOf_eq_four_of_inner {G : Type} [Group G] [Finite G] (hG : Group.IsPerfect G)
    (hrank : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G))
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo G) {y : G}
    (hy2 : IsPGroup 2 (Subgroup.zpowers y)) (hyZ : y ^ 2 ∈ Subgroup.center G)
    (hyNZ : y ∉ Subgroup.center G)
    (hR : CFSG.Open.pRank 2 (Subgroup.centralizer ({y} : Set G)) ≤ 1)
    (P : Sylow 2 G) (hyP : y ∈ (P : Subgroup G)) :
    orderOf y = 4 ∧
      (P : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G) ≤ Subgroup.zpowers y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy1 : y ≠ 1 := fun h => hyNZ (h ▸ Subgroup.one_mem _)
  have hysq : y ^ 2 ≠ 1 := by
    intro h
    have h2 := AschbacherKnownGroup.Lemma38.two_le_pRank_centralizer_involution hrank
      (Subgroup.mem_top y) h
    rw [top_inf_eq] at h2
    omega
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_zpowers hy2
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply hysq
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    have h1 : 2 ^ k ∣ 2 ^ 1 := Nat.pow_dvd_pow 2 (by omega)
    simpa using h1
  have hQcyc : IsCyclic ((P : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
    refine isCyclic_of_central_of_sq_ne_one (P.isPGroup'.to_le inf_le_left)
      ((CFSG.SectionRank.pRank_mono one_lt_two inf_le_right).trans hR)
      ⟨hyP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ ?_ hysq
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp hq.2
  set a : (P : Subgroup G) := ⟨y, hyP⟩ with ha
  have hamap : (Subgroup.centralizer ({a} : Set (P : Subgroup G))).map (P : Subgroup G).subtype =
      (P : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, congrArg Subtype.val hp⟩
    · rintro ⟨hgP, hg⟩
      exact ⟨⟨g, hgP⟩, Subtype.ext hg, rfl⟩
  have hcyc : IsCyclic (Subgroup.centralizer ({a} : Set (P : Subgroup G))) := by
    have e := (Subgroup.centralizer ({a} : Set (P : Subgroup G))).equivMapOfInjective
      (P : Subgroup G).subtype (P : Subgroup G).subtype_injective
    rw [hamap] at e
    exact isCyclic_of_injective e.toMonoidHom e.injective
  have haord : orderOf a = orderOf y := Subgroup.orderOf_mk _ _
  have ha : 2 < orderOf a := by
    rw [haord, hk]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hPne : (P : Subgroup G) ≠ ⊥ := fun h => hy1 (by
    have := hyP
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hinv : ¬ AtMostOneInvolution (P : Subgroup G) := by
    intro h
    have := twoRank_eq_one_of_sylow P h hPne
    unfold CFSG.Open.twoRank at this
    omega
  rcases cyclic_centralizer_shape P.isPGroup' hinv ha hcyc with hD | hSD | hCa
  · exact (hnd ⟨P, hD⟩).elim
  ·
    exfalso
    obtain ⟨n, hn, hS⟩ := hSD
    have hz2 : orderOf (y ^ 2 ^ (k - 1)) = 2 := by
      have h := orderOf_pow_orderOf_div (x := y) (n := 2) (by rw [hk]; positivity)
        (by rw [hk]; exact dvd_pow_self 2 (by omega))
      have hdiv : 2 ^ k / 2 = 2 ^ (k - 1) := by
        have h2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
        rw [h2, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
      rwa [hk, hdiv] at h
    have hzc : y ^ 2 ^ (k - 1) ∈ Subgroup.center G := by
      have : y ^ 2 ^ (k - 1) = (y ^ 2) ^ 2 ^ (k - 2) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega
      rw [this]
      exact Subgroup.pow_mem _ hyZ _
    exact semidihedral_perfect_no_central_involution hG P hn hS hzc hz2
  ·
    have ha2 : a ^ 2 ∈ Subgroup.center (P : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hyZ g)
    have : (Subgroup.zpowers (a ^ 2)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr ha2)
    have hshape := quotient_dihedral_or_semidihedral P.isPGroup' hinv ha hCa ha2
      (Subgroup.zpowers (a ^ 2)) rfl
    have h4 := pow_four_eq_one_of_quotient hG P (a := a) hyZ (Subgroup.zpowers (a ^ 2)) rfl hshape
    have hy4 : y ^ 4 = 1 := congrArg Subtype.val h4
    refine ⟨?_, ?_⟩
    · have hdvd := orderOf_dvd_of_pow_eq_one hy4
      rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at hdvd
      rw [hk, show k = 2 by omega]
      norm_num
    · intro g hg
      have hgC : (⟨g, hg.1⟩ : (P : Subgroup G)) ∈ Subgroup.centralizer ({a} : Set (P : Subgroup G))
          := Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
            (Subgroup.mem_centralizer_singleton_iff.mp hg.2))
      rw [hCa] at hgC
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgC
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, congrArg Subtype.val hj⟩

theorem inner_case_cyclic_four {X : Type} [Group X] [Finite X] (A : Subgroup X)
    (hA : CFSG.Open.aschbacherThm5IsSemisimple A)
    (hrank : 2 ≤ CFSG.Open.pRank 2 A)
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo A)
    {y : X} (hyA : y ∈ A) (hy2 : IsPGroup 2 (Subgroup.zpowers y))
    (hyZ : ∀ a ∈ A, y ^ 2 * a = a * y ^ 2) (hyNZ : ∃ a ∈ A, y * a ≠ a * y)
    (hR : CFSG.Open.pRank 2 (A ⊓ Subgroup.centralizer ({y} : Set X)) ≤ 1) :
    ∃ P : Sylow 2 ↥(A ⊓ Subgroup.centralizer ({y} : Set X)),
      IsCyclic (P : Subgroup ↥(A ⊓ Subgroup.centralizer ({y} : Set X))) ∧ Nat.card P = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : Group.IsPerfect A := AschbacherTheorem5.semisimple_perfect A hA
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_zpowers hy2
  set y' : A := ⟨y, hyA⟩ with hy'
  have hy'o : orderOf y' = orderOf y := Subgroup.orderOf_mk _ _
  have hy'2 : IsPGroup 2 (Subgroup.zpowers y') :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hy'o, hk])
  have hy'Z : y' ^ 2 ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hyZ g g.2).symm
  have hy'NZ : y' ∉ Subgroup.center A := by
    obtain ⟨b, hb, hne⟩ := hyNZ
    intro h
    exact hne (congrArg Subtype.val (Subgroup.mem_center_iff.mp h ⟨b, hb⟩)).symm
  have hR' : CFSG.Open.pRank 2 (Subgroup.centralizer ({y'} : Set A)) ≤ 1 := by
    refine (CFSG.SectionRank.pRank_le_map one_lt_two A.subtype A.subtype_injective _).trans
      ((CFSG.SectionRank.pRank_mono one_lt_two ?_).trans hR)
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hg))⟩
  have hrank' : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup A) := by
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup A]
  have hcore := fun (P : Sylow 2 A) (hP : y' ∈ (P : Subgroup A)) =>
    orderOf_eq_four_of_inner hG hrank' hnd hy'2 hy'Z hy'NZ hR' P hP
  obtain ⟨P₀, hP₀⟩ := hy'2.exists_le_sylow
  have hy'4 : orderOf y' = 4 := (hcore P₀ (hP₀ (Subgroup.mem_zpowers y'))).1
  set C := A ⊓ Subgroup.centralizer ({y} : Set X) with hC
  have hyC : y ∈ C := ⟨hyA, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  set yC : C := ⟨y, hyC⟩ with hyCdef
  have hyCo : orderOf yC = orderOf y := Subgroup.orderOf_mk _ _
  have hyC2 : IsPGroup 2 (Subgroup.zpowers yC) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hyCo, hk])
  obtain ⟨R, hRy⟩ := hyC2.exists_le_sylow
  let ι : C →* A := Subgroup.inclusion (inf_le_left : C ≤ A)
  have hιy : ι yC = y' := rfl
  have hRle : (R : Subgroup C) ≤ Subgroup.zpowers yC := by
    intro r hr
    have hQ2 : IsPGroup 2 ((R : Subgroup C).map ι) := R.isPGroup'.map ι
    obtain ⟨P, hQP⟩ := hQ2.exists_le_sylow
    have hyP : y' ∈ (P : Subgroup A) := hQP ⟨yC, hRy (Subgroup.mem_zpowers yC), rfl⟩
    have hιr : ι r ∈ (P : Subgroup A) ⊓ Subgroup.centralizer ({y'} : Set A) := by
      refine Subgroup.mem_inf.mpr ⟨hQP ⟨r, hr, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp r.2.2)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ((hcore P hyP).2 hιr)
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, Subgroup.inclusion_injective
      (inf_le_left : C ≤ A) ?_⟩
    show ι (yC ^ j) = ι r
    rw [map_zpow, hιy, hj]
  have hReq : (R : Subgroup C) = Subgroup.zpowers yC := le_antisymm hRle hRy
  refine ⟨R, (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨yC, hReq.symm⟩, ?_⟩
  have hcard : Nat.card (R : Subgroup C) = 4 := by
    rw [hReq, Nat.card_zpowers, hyCo, ← hy'o, hy'4]
  exact hcard

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
