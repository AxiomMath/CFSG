module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U48
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Fix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 equivSU4 center_SU4 card_SU4)

theorem twoPart_two_pow_mul_odd (k m : ℕ) (hm : ¬ 2 ∣ m) (hm0 : m ≠ 0) :
    twoPart (2 ^ k * m) = 2 ^ k := by
  unfold twoPart
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem twoPart_25920 : twoPart 25920 = 2 ^ 6 := by
  have : (25920 : ℕ) = 2 ^ 6 * 405 := by norm_num
  rw [this]
  exact twoPart_two_pow_mul_odd 6 405 (by norm_num) (by norm_num)

noncomputable section Simple

variable {G : Type} [Group G] [Finite G] {X L : Subgroup G}

@[expose] def lModel (hcat : catalogIs ↥L S9.isU4eight) : ↥L ≃* SU4 :=
  (bridge_u4eight hcat).some.trans equivSU4

@[expose] def pquotEquiv (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) :
    PQuot 3 L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_bot_of_isU4eight hL hcat)).trans
    QuotientGroup.quotientBot

theorem pquotEquiv_mk (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) (x : ↥L) :
    pquotEquiv hL hcat (QuotientGroup.mk x) = x := rfl

theorem center_pquot_eq_bot (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) :
    Subgroup.center (PQuot 3 L) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hc : lModel hcat (pquotEquiv hL hcat z) ∈ Subgroup.center SU4 := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, hy⟩ := (lModel hcat).surjective w
    obtain ⟨q, rfl⟩ := (pquotEquiv hL hcat).surjective y
    rw [← hy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hz q]
  rw [center_SU4, Subgroup.mem_bot] at hc
  rw [Subgroup.mem_bot]
  apply (pquotEquiv hL hcat).injective
  apply (lModel hcat).injective
  rw [hc, map_one, map_one]

@[expose] def psimpleEquiv (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) :
    PSimple 3 L ≃* PQuot 3 L :=
  (QuotientGroup.quotientMulEquivOfEq (center_pquot_eq_bot hL hcat)).trans
    QuotientGroup.quotientBot

@[expose] def psModel (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) :
    PSimple 3 L ≃* SU4 :=
  ((psimpleEquiv hL hcat).trans (pquotEquiv hL hcat)).trans (lModel hcat)

theorem psModel_mk (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight)
    (q : PQuot 3 L) : psModel hL hcat (QuotientGroup.mk q) = lModel hcat (pquotEquiv hL hcat q) :=
  rfl

theorem catalogIs_psimple (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) :
    catalogIs (PSimple 3 L) S9.isU4eight :=
  (catalogIs_congr ((psimpleEquiv hL hcat).trans (pquotEquiv hL hcat))).2 hcat

@[expose] def indAut (e : ↥L ≃* SU4) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    MulAut SU4 :=
  MulAut.congr e (conjL L b hb)

theorem indAut_apply (e : ↥L ≃* SU4) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : indAut e b hb (e x) = e (conjL L b hb x) := by
  simp [indAut, MulAut.congr_apply]

theorem indAut_psModel (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) (b : G)
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (q : PQuot 3 L) :
    indAut (lModel hcat) b hb (psModel hL hcat (QuotientGroup.mk q)) =
      psModel hL hcat (QuotientGroup.mk (barAut L b hb q)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [psModel_mk, psModel_mk, pquotEquiv_mk, barAut_mk, pquotEquiv_mk, indAut_apply]

theorem conjL_eq_iff (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    conjL L b hb x = x ↔ (x : G) ∈ cx b := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 := congrArg (fun z : ↥L => (z : G)) h
    simp only [conjL_apply] at h2
    calc (x : G) * b = b * (b⁻¹ * (x : G) * b) := by group
      _ = b * (x : G) := by rw [h2]
  · intro h
    apply Subtype.ext
    rw [conjL_apply]
    calc b⁻¹ * (x : G) * b = b⁻¹ * ((x : G) * b) := by rw [mul_assoc]
      _ = b⁻¹ * (b * (x : G)) := by rw [h]
      _ = x := by group

theorem map_cent_eq (e : ↥L ≃* SU4) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    ((L ⊓ cx b).subgroupOf L).map e.toMonoidHom = fixSub (indAut e b hb) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    show indAut e b hb (e x) = e x
    rw [indAut_apply, (conjL_eq_iff b hb x).2 (Subgroup.mem_inf.1 hx).2]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨(e.symm y).2, (conjL_eq_iff b hb (e.symm y)).1 ?_⟩
    apply e.injective
    rw [← indAut_apply, e.apply_symm_apply]
    exact hy

@[expose] def centEquiv (e : ↥L ≃* SU4) (b : G) (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    ↥(L ⊓ cx b) ≃* ↥(fixSub (indAut e b hb)) :=
  (((Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ cx b ≤ L)).symm).trans
    (e.subgroupMap _)).trans (MulEquiv.subgroupCongr (map_cent_eq e b hb))

theorem indRel_barAut' {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    indRel 3 L b (QuotientGroup.mk l : PQuot 3 L)
      (barAut L b hb (QuotientGroup.mk l : PQuot 3 L)) :=
  ⟨l, conjL L b hb l, rfl, rfl, rfl⟩

theorem indRel_iff_barAut {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) (q q' : PQuot 3 L) :
    indRel 3 L b q q' ↔ barAut L b hb q = q' := by
  constructor
  · rintro ⟨l, l', rfl, rfl, h⟩
    rw [barAut_mk]
    congr 1
    exact (Subtype.ext h).symm
  · rintro rfl
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact indRel_barAut' hb l

theorem pquotEquiv_barAut (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (q : PQuot 3 L) :
    pquotEquiv hL hcat (barAut L b hb q) = conjL L b hb (pquotEquiv hL hcat q) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [barAut_mk, pquotEquiv_mk, pquotEquiv_mk]

@[expose] def pqModel (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) :
    PQuot 3 L ≃* SU4 :=
  (pquotEquiv hL hcat).trans (lModel hcat)

@[expose] def fixedPointsEquiv (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight)
    {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    {q : PQuot 3 L // indRel 3 L b q q} ≃ ↥(fixSub (indAut (lModel hcat) b hb)) :=
  Equiv.subtypeEquiv (pqModel hL hcat).toEquiv fun q => by
    rw [indRel_iff_barAut hb, mem_fixSub]
    show barAut L b hb q = q ↔ indAut (lModel hcat) b hb (lModel hcat (pquotEquiv hL hcat q)) =
      lModel hcat (pquotEquiv hL hcat q)
    rw [indAut_apply, ← pquotEquiv_barAut hL hcat hb]
    exact ⟨fun h => by rw [h], fun h => (pqModel hL hcat).injective h⟩

theorem card_fixedPoints (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    Nat.card {q : PQuot 3 L // indRel 3 L b q q} = Nat.card ↥(fixSub (indAut (lModel hcat) b hb)) :=
  Nat.card_congr (fixedPointsEquiv hL hcat hb)

end Simple

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
