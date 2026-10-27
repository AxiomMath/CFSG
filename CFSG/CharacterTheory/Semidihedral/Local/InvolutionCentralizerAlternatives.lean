module

public import CFSG.CharacterTheory.Semidihedral.Local.DerivedInvolutionsConjugate
public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizerSplit
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

theorem sylow_semidihedral_equiv [Finite G] (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (S' : Sylow 2 G) : Nonempty (SemidihedralGroup n ≃* S') := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S S'
  exact ⟨f.trans (S.equivSMul g)⟩

theorem self_mem_center_centralizer (t : G) :
    (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer {t}) ∈
      Subgroup.center (Subgroup.centralizer {t}) :=
  Subgroup.mem_center_iff.mpr fun x =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem exists_sylow_centralizer_inf [Finite G] (t : G) (ht : orderOf t = 2) :
    ∃ S_t : Sylow 2 G, t ∈ S_t ∧ ∃ P : Sylow 2 (Subgroup.centralizer {t}),
      (P : Subgroup (Subgroup.centralizer {t})) =
        (Subgroup.centralizer {t} ⊓ (S_t : Subgroup G)).subgroupOf
          (Subgroup.centralizer {t}) := by
  set C := Subgroup.centralizer {t} with hCdef
  have htc := self_mem_center_centralizer t
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := Sylow.nonempty
  have htP : (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ (P : Subgroup C) :=
    Principal.mem_sylow_of_mem_center_of_orderOf_eq htc (k := 1)
      (by rw [Subgroup.orderOf_mk, ht, pow_one]) P
  obtain ⟨S_t, hPS⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  have htS : t ∈ (S_t : Subgroup G) := hPS (Subgroup.mem_map_of_mem _ htP)
  refine ⟨S_t, htS, P, ?_⟩
  have hR2 : IsPGroup 2 ((C ⊓ (S_t : Subgroup G)).subgroupOf C) :=
    (S_t.isPGroup'.to_le inf_le_right).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hPR : (P : Subgroup C) ≤ (C ⊓ (S_t : Subgroup G)).subgroupOf C := fun c hc =>
    Subgroup.mem_subgroupOf.mpr ⟨c.2, hPS (Subgroup.mem_map_of_mem _ hc)⟩
  exact (P.is_maximal' hR2 hPR).symm

theorem le_card_sylow_centralizer_of_perfect [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (hperf : commutator G = ⊤) (t : G) (ht : orderOf t = 2)
    (P : Sylow 2 (Subgroup.centralizer {t})) : 2 ^ n ≤ Nat.card P := by
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  obtain ⟨-, -, hiff⟩ := semidihedral_derived_involutions_conjugate n hn S f
  obtain ⟨c, hc⟩ := isConj_iff.mp ((hiff hperf t).mp ht).symm
  set z : G := ((f (r n) ^ 2 ^ (n - 2) : S) : G) with hzdef
  have hzc : (f (r n) ^ 2 ^ (n - 2) : S) ∈ Subgroup.center S := by
    have h := image_z_mem_center hn f
    rwa [show 2 ^ (n - 1) / 2 = 2 ^ (n - 2) from modulus_div_two n hn3] at h
  set Q := (S : Subgroup G).map (MulAut.conj c).toMonoidHom with hQdef
  have hQC : Q ≤ Subgroup.centralizer {t} := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    have hsz : s * z = z * s := by
      have h := Subgroup.mem_center_iff.mp hzc ⟨s, hs⟩
      exact congrArg Subtype.val h
    change c * s * c⁻¹ * (c * z * c⁻¹) = c * z * c⁻¹ * (c * s * c⁻¹)
    simp only [mul_assoc, inv_mul_cancel_left]
    rw [← mul_assoc s, hsz, mul_assoc]
  have hQcard : Nat.card Q = 2 ^ n := by
    rw [hQdef, Subgroup.card_map_of_injective (MulAut.conj c).injective,
      ← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n hn3]
  have hQ2 : IsPGroup 2 (Q.subgroupOf (Subgroup.centralizer {t})) :=
    IsPGroup.of_card (n := n) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, hQcard])
  obtain ⟨P₂, hP₂⟩ := hQ2.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Subgroup.centralizer {t}) P P₂
  calc 2 ^ n = Nat.card (Q.subgroupOf (Subgroup.centralizer {t})) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQC).toEquiv, hQcard]
    _ ≤ Nat.card (g • P : Sylow 2 (Subgroup.centralizer {t})) := Subgroup.card_le_of_le hP₂
    _ = Nat.card P := (Nat.card_congr (P.equivSMul g).toEquiv).symm

theorem semidihedral_involution_centralizer_alternatives [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) (t : G) (ht : orderOf t = 2) :
    let C := Subgroup.centralizer {t}
    ∃ S_t : Sylow 2 G, t ∈ S_t ∧
      let R := C ⊓ (S_t : Subgroup G)
      let A : Prop := R = S_t ∧ Nonempty (SemidihedralGroup n ≃* S_t) ∧
        (Subgroup.center S_t).map (S_t : Subgroup G).subtype = Subgroup.zpowers t ∧
        ∃ (K : Subgroup C) (_ : K.Normal), K.map C.subtype = Subgroup.zpowers t ∧
          ∃ T : Sylow 2 (C ⧸ K), Nonempty (T ≃* DihedralGroup (2 ^ (n - 2)))
      let B : Prop := IsKleinFour R ∧
        ∃ (N : Subgroup C) (_ : N.Normal), (Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∧
          (∀ N' : Subgroup C, Odd (Nat.card N') → (∃ k : ℕ, N'.index = 2 ^ k) → N' = N) ∧
          N.Characteristic ∧ (∀ x : C, x ∈ N ↔ Odd (orderOf x)) ∧
          (N : Set C) * (R.subgroupOf C : Set C) = Set.univ ∧ N ⊓ R.subgroupOf C = ⊥ ∧
          Function.Bijective ((QuotientGroup.mk' N).comp (R.subgroupOf C).subtype)
      (∃ P : Sylow 2 C, (P : Subgroup C) = R.subgroupOf C) ∧ Xor A B ∧
        (commutator G = ⊤ → A) := by
  intro C
  have hn3 : 3 ≤ n := Nat.le_of_succ_le hn
  obtain ⟨S_t, htS, P, hP⟩ := exists_sylow_centralizer_inf t ht
  obtain ⟨f_t⟩ := sylow_semidihedral_equiv n S f S_t
  refine ⟨S_t, htS, ?_⟩
  intro R A B
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set tC : C := ⟨t, htC⟩ with htCdef
  have htc : tC ∈ Subgroup.center C := self_mem_center_centralizer t
  have ht2 : orderOf tC = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  set t' : (S_t : Subgroup G) := ⟨t, htS⟩ with ht'def
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hcardS : Nat.card (S_t : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr f_t.toEquiv, CFSG.Semidihedral.card n hn3]
  have hP4 : IsKleinFour R → Nat.card P = 4 := by
    intro hK
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact IsKleinFour.card_four
  have hAB : A → B → False := by
    rintro ⟨hRS, -⟩ ⟨hK, -⟩
    have h4 : Nat.card R = 4 := IsKleinFour.card_four
    rw [hRS, hcardS] at h4
    have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have hA : t' ∈ Subgroup.zpowers (f_t (r n) ^ (2 ^ (n - 1) / 2)) → A := by
    intro hcen
    have hFin := finite_of_semidihedral hn3 f_t
    have ht'z : t' = f_t (r n) ^ (2 ^ (n - 1) / 2) := by
      rcases (KleinFourOddKernel.mem_zpowers_involution _ t' (image_z_orderOf hn3 f_t)).mp
        hcen with h | h
      · rw [h, orderOf_one] at ht'2
        exact absurd ht'2 (by decide)
      · exact h
    have ht'c : t' ∈ Subgroup.center S_t := ht'z ▸ image_z_mem_center hn f_t
    have hRS : R = S_t := by
      refine inf_eq_right.mpr fun s hs => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ht'c ⟨s, hs⟩)
    have hcS : Subgroup.center S_t = Subgroup.zpowers t' := by
      rw [(supplied_center n hn f_t).1, ht'z]
      rfl
    have hcen' : (Subgroup.center S_t).map (S_t : Subgroup G).subtype = Subgroup.zpowers t := by
      rw [hcS, MonoidHom.map_zpowers]
      rfl
    let eP : (P : Subgroup C) ≃* (S_t : Subgroup G) :=
      (MulEquiv.subgroupCongr hP).trans
        ((Subgroup.subgroupOfEquivOfLe inf_le_left).trans (MulEquiv.subgroupCongr hRS))
    obtain ⟨-, -, -, -, -, -, -, T, e, -⟩ :=
      CentralQuotients.central_involution_dihedral_quotient P n hn (f_t.trans eP.symm) tC htc
        ht2
    refine ⟨hRS, ⟨f_t⟩, hcen', CentralQuotients.ambientZ tC htc,
      CentralQuotients.ambientZ_normal tC htc, ?_, T, ⟨e.symm⟩⟩
    change (Subgroup.zpowers tC).map C.subtype = Subgroup.zpowers t
    rw [MonoidHom.map_zpowers]
    rfl
  have hB : t' ∉ Subgroup.zpowers (f_t (r n) ^ (2 ^ (n - 1) / 2)) → B := by
    intro hcen
    obtain ⟨hcent, hK⟩ := centralizer_eq_closure hn f_t t' ht'2 hcen
    have hRmap : R = (Subgroup.centralizer {t'}).map (S_t : Subgroup G).subtype := by
      ext x
      constructor
      · rintro ⟨hxC, hxS⟩
        refine ⟨⟨x, hxS⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxC)
      · rintro ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hy
        refine Subgroup.mem_inf.mpr ⟨?_, y.2⟩
        change (y : G) ∈ Subgroup.centralizer {t}
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hy
    have hK' : IsKleinFour (Subgroup.centralizer {t'}) := by
      rw [hcent]
      exact hK
    have hRK : IsKleinFour R := by
      rw [hRmap]
      exact isKleinFour_of_mulEquiv ((Subgroup.centralizer {t'}).equivMapOfInjective _
        (Subgroup.subtype_injective _))
    have hPK : IsKleinFour (P : Subgroup C) :=
      isKleinFour_of_mulEquiv ((MulEquiv.subgroupCongr hP).trans
        (Subgroup.subgroupOfEquivOfLe inf_le_left)).symm
    have hS2 : Nonempty (DihedralGroup (2 ^ (2 - 1)) ≃* (P : Subgroup C)) := by
      show Nonempty (DihedralGroup 2 ≃* (P : Subgroup C))
      exact IsKleinFour.nonempty_mulEquiv
    obtain ⟨N, hNnormal, ⟨hNodd, k, hk⟩, -, hchar, hmem, hmul, hinf, hbij⟩ :=
      Principal.dihedral_central_involution_normal_odd_complement P le_rfl hS2 ⟨tC, htc, ht2⟩
    change (N : Set C) * ((P : Subgroup C) : Set C) = Set.univ at hmul
    rw [hP] at hmul hinf hbij
    exact ⟨hRK, N, hNnormal, ⟨hNodd, k, hk⟩,
      fun N' hN'odd ⟨a, ha⟩ => hall_eq_of_odd_mem N hNodd hk hmem N' hN'odd ha, hchar, hmem,
      hmul, hinf, hbij⟩
  refine ⟨⟨P, hP⟩, ?_, fun hperf => ?_⟩
  · by_cases hcen : t' ∈ Subgroup.zpowers (f_t (r n) ^ (2 ^ (n - 1) / 2))
    · exact Or.inl ⟨hA hcen, hAB (hA hcen)⟩
    · exact Or.inr ⟨hB hcen, fun h => hAB h (hB hcen)⟩
  · by_cases hcen : t' ∈ Subgroup.zpowers (f_t (r n) ^ (2 ^ (n - 1) / 2))
    · exact hA hcen
    · have h4 := hP4 (hB hcen).1
      have hle := le_card_sylow_centralizer_of_perfect n hn S f hperf t ht P
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega

end CFSG.Semidihedral.Local
