module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Klein
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Red
public import CFSG.RankThree.PartTwo.KFacts.AutPSUInner
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3Psu

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (coe_glAut)
open Matrix
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs

variable {K : Type} [Field K]

theorem eq_one_of_mem_unitaryScalars (h : UnitaryFieldData 3 3 K) (h3 : (3 : K) = 0)
    {g : unitarySU 3 3 K 3} (hg : g ∈ unitaryScalars h 3) : g = 1 := by
  obtain ⟨c, -, hc3, hgc⟩ := mem_unitaryScalars.1 hg
  have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hc1 : c = 1 := Units.ext (KDRank3SmallF12Core.eq_one_of_pow_three h3 hc3')
  apply Subtype.ext
  rw [Subgroup.coe_one, hgc, hc1, map_one]

theorem mk_eq_one_iff (h : UnitaryFieldData 3 3 K) (h3 : (3 : K) = 0) (g : unitarySU 3 3 K 3) :
    (QuotientGroup.mk g : unitaryPSU h 3) = 1 ↔ g = 1 :=
  ⟨fun hg => eq_one_of_mem_unitaryScalars h h3 ((QuotientGroup.eq_one_iff g).1 hg),
    fun hg => by simp [hg]⟩

theorem conj_eq_one_iff {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {y : G} :
    MulAut.conj y = 1 ↔ y = 1 := by
  constructor
  · intro hy
    have hc : y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut G => φ g) hy
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      exact (mul_inv_eq_iff_eq_mul.1 h).symm
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  · rintro rfl
    rw [map_one]

theorem conj_injective_of_center {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {x y : G}
    (h : MulAut.conj x = MulAut.conj y) : x = y := by
  have : MulAut.conj (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have := (conj_eq_one_iff hZ).1 this
  exact (inv_mul_eq_one.1 this).symm

theorem comm_of_conj_comm (h : UnitaryFieldData 3 3 K) (h3 : (3 : K) = 0)
    (hZ : Subgroup.center (unitaryPSU h 3) = ⊥) (g g' : unitarySU 3 3 K 3)
    (hc : MulAut.conj (QuotientGroup.mk g : unitaryPSU h 3) *
        MulAut.conj (QuotientGroup.mk g') =
      MulAut.conj (QuotientGroup.mk g') * MulAut.conj (QuotientGroup.mk g)) :
    g * g' = g' * g := by
  have h1 : (QuotientGroup.mk (g * g') : unitaryPSU h 3) = QuotientGroup.mk (g' * g) := by
    apply conj_injective_of_center hZ
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, hc]
  exact inv_mul_eq_one.1 (eq_one_of_mem_unitaryScalars h h3 (QuotientGroup.eq.1 h1))

theorem center_trivial (h : UnitaryFieldData 3 3 K) :
    Subgroup.center (unitaryPSU h 3) = ⊥ :=
  center_unitaryPSU_three_eq_bot h (by norm_num)

theorem pow_eq_one_of_conj_pow (h : UnitaryFieldData 3 3 K) (h3 : (3 : K) = 0) (g : unitarySU 3 3 K 3)
    (k : ℕ) (hk : MulAut.conj (QuotientGroup.mk g : unitaryPSU h 3) ^ k = 1) : g ^ k = 1 := by
  rw [← map_pow] at hk
  have h1 := (conj_eq_one_iff (center_trivial h)).1 hk
  rw [← QuotientGroup.mk_pow] at h1
  exact (mk_eq_one_iff h h3 _).1 h1

theorem exists_lift (h : UnitaryFieldData 3 3 K) (v : MulAut (unitaryPSU h 3)) :
    ∃ A : unitarySU 3 3 K 3, v ∈ inner (unitaryPSU h 3) →
      MulAut.conj (QuotientGroup.mk A : unitaryPSU h 3) = v := by
  by_cases hv : v ∈ inner (unitaryPSU h 3)
  · obtain ⟨y, rfl⟩ := hv
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨A, fun _ => rfl⟩
  · exact ⟨1, fun h' => absurd h' hv⟩

theorem psuConj_mem_inner (h : UnitaryFieldData 3 3 K) (A : unitaryIsom3 h) :
    psuConj h A ∈ inner (unitaryPSU h 3) := by
  have hN := norm_det_of_mem_unitaryIsom3 A.2
  set d : Kˣ := GeneralLinearGroup.det (A : GL (Fin 3) K) with hd_def
  have hdval : (d : K) = ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det := by
    rw [hd_def, GeneralLinearGroup.val_det_apply]
  rw [← hdval] at hN
  have hN' : (d : K) * (d : K) ^ 27 = 1 := by
    unfold UnitaryFieldData.norm at hN
    rw [h.bar_apply] at hN
    norm_num at hN
    exact hN
  have hd28' : (d : K) ^ 28 = 1 := by
    calc (d : K) ^ 28 = (d : K) * (d : K) ^ 27 := by ring
      _ = 1 := hN'
  have hd28 : d ^ 28 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, hd28'])
  have hu3 : (d ^ 19) ^ 3 = d := by
    rw [← pow_mul, show 19 * 3 = 28 * 2 + 1 by norm_num, pow_add, pow_mul, hd28, one_pow,
      one_mul, pow_one]
  have hnorm : h.norm ((d ^ 19 : Kˣ) : K) = 1 := by
    unfold UnitaryFieldData.norm
    rw [h.bar_apply, Units.val_pow_eq_pow_val]
    norm_num
    rw [← pow_mul, ← pow_add, show 19 + 19 * 27 = 28 * 19 by norm_num, pow_mul]
    rw [show (d : K) ^ 28 = 1 from hd28']
    simp
  exact psuConj_mem_range_conj_of_det_eq_pow (A := A) (u := d ^ 19) hnorm
    (by rw [hu3])

theorem range_psuConj_le_inner (h : UnitaryFieldData 3 3 K) {x : MulAut (unitaryPSU h 3)}
    (hx : x ∈ (psuConj h).range) : x ∈ inner (unitaryPSU h 3) := by
  obtain ⟨A, rfl⟩ := hx
  exact psuConj_mem_inner h A

theorem conj_mem_inner {G : Type} [Group G] (g : MulAut G) {x : MulAut G}
    (hx : x ∈ inner G) : g⁻¹ * x * g ∈ inner G := by
  have := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal G).conj_mem x hx g⁻¹
  simpa using this

theorem mul_conj_mul_inv' {G : Type} [Group G] (φ : MulAut G) (x : G) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  apply MulEquiv.ext
  intro z
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem conj_pow' {G : Type} [Group G] (x g : G) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  induction n with
  | zero => group
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    group

theorem mat_pow_eq_one {A : unitarySU 3 3 K 3} {n : ℕ} (hA : A ^ n = 1) :
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ n = 1 := by
  have := congrArg (fun x : unitarySU 3 3 K 3 => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hA
  simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this

theorem mat_mul_comm {A B : unitarySU 3 3 K 3} (hAB : A * B = B * A) :
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have := congrArg (fun x : unitarySU 3 3 K 3 => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hAB
  simpa [Subgroup.coe_mul, Units.val_mul] using this

theorem mat_sq_eq_one {A : unitarySU 3 3 K 3} (hA : A ^ 2 = 1) :
    ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [← sq]
  exact mat_pow_eq_one hA

theorem subtype_eq_of_mat_eq {A B : unitarySU 3 3 K 3}
    (hAB : ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    A = B :=
  Subtype.ext (Units.ext hAB)

theorem klein_psu (h : UnitaryFieldData 3 3 K) (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0) :
    KleinFour3 (inner (unitaryPSU h 3)) := by
  intro g₁ g₂ k hg₁ hg₂ hg1 hg2 hne1 hne2 hne hcomm hk hk3 hkg1 hkg2
  obtain ⟨y₁, rfl⟩ := hg₁
  obtain ⟨y₂, rfl⟩ := hg₂
  obtain ⟨yk, rfl⟩ := hk
  obtain ⟨A₁, rfl⟩ := QuotientGroup.mk_surjective y₁
  obtain ⟨A₂, rfl⟩ := QuotientGroup.mk_surjective y₂
  obtain ⟨Ak, rfl⟩ := QuotientGroup.mk_surjective yk
  have hA1 : A₁ ^ 2 = 1 := pow_eq_one_of_conj_pow h h3 A₁ 2 hg1
  have hA2 : A₂ ^ 2 = 1 := pow_eq_one_of_conj_pow h h3 A₂ 2 hg2
  have hAk : Ak ^ 3 = 1 := pow_eq_one_of_conj_pow h h3 Ak 3 hk3
  have hA1ne : A₁ ≠ 1 := fun e => hne1 (by rw [e]; simp)
  have hA2ne : A₂ ≠ 1 := fun e => hne2 (by rw [e]; simp)
  have hA12 : A₁ ≠ A₂ := fun e => hne (by rw [e])
  have hc12 : A₁ * A₂ = A₂ * A₁ := comm_of_conj_comm h h3 (center_trivial h) A₁ A₂ hcomm
  have hck1 : Ak * A₁ = A₁ * Ak := comm_of_conj_comm h h3 (center_trivial h) Ak A₁ hkg1
  have hck2 : Ak * A₂ = A₂ * Ak := comm_of_conj_comm h h3 (center_trivial h) Ak A₂ hkg2
  have hd1 := ((mem_unitarySU_iff h).1 A₁.2).1
  have hd2 := ((mem_unitarySU_iff h).1 A₂.2).1
  have hdk := ((mem_unitarySU_iff h).1 Ak.2).1
  have key := KDRank3SmallF12Klein.klein_core hK h3 (g₁ := ((A₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (g₂ := ((A₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (k := ((Ak : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (mat_sq_eq_one hA1) (mat_sq_eq_one hA2) hd1 hd2
    (fun e => hA1ne (Subtype.ext (Units.ext e)))
    (fun e => hA2ne (Subtype.ext (Units.ext e)))
    (fun e => hA12 (Subtype.ext (Units.ext e)))
    (mat_mul_comm hc12) (mat_pow_eq_one hAk) (mat_mul_comm hck1) (mat_mul_comm hck2)
  have hAk1 : Ak = 1 := Subtype.ext (Units.ext key)
  rw [hAk1, QuotientGroup.mk_one, map_one]

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3Psu

end
