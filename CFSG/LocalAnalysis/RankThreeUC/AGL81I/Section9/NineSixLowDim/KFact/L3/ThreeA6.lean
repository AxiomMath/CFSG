module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs
public import CFSG.RankThree.PartOne.N1322.Pure
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.RepresentationTheory

section Helpers

variable {q : ℕ} [Fact q.Prime]

private lemma injective_or_eq_smul_one {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) {M : Matrix (Fin 3) (Fin 3) (ZMod q)}
    (hM : ∀ h ∈ H, M * (h : Matrix (Fin 3) (Fin 3) (ZMod q)) = h * M) (ζ : ZMod q) :
    (∀ v, (M - ζ • 1) *ᵥ v = 0 → v = 0) ∨ M = ζ • 1 := by
  set N := M - ζ • (1 : Matrix (Fin 3) (Fin 3) (ZMod q)) with hNdef
  have hN : ∀ h ∈ H, N * (h : Matrix (Fin 3) (Fin 3) (ZMod q)) = h * N := by
    intro h hh
    rw [hNdef, sub_mul, mul_sub, hM h hh, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rcases hirr (LinearMap.ker N.mulVecLin) (by
    rintro ⟨h, hh⟩ w hw
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Subgroup.coe_subtype] at hw ⊢
    rw [Matrix.mulVec_mulVec, hN h hh, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]) with h | h
  · left
    intro v hv
    have hv' : v ∈ LinearMap.ker N.mulVecLin := by simpa using hv
    simpa [h] using hv'
  · right
    have hN0 : N = 0 := by
      ext i j
      have hj : Pi.single j 1 ∈ LinearMap.ker N.mulVecLin := h ▸ Submodule.mem_top
      have := congrFun (LinearMap.mem_ker.mp hj) i
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at this
      simpa using this
    exact sub_eq_zero.mp hN0

private lemma exists_cube_root (hq3 : q % 3 = 1) :
    ∃ ω : ZMod q, ω ^ 2 + ω + 1 = 0 := by
  have hdvd : 3 ∣ Fintype.card (ZMod q)ˣ := by
    rw [ZMod.card_units]
    have := Nat.div_add_mod q 3
    have h1 : 1 ≤ q := (Fact.out : q.Prime).one_lt.le
    exact ⟨q / 3, by omega⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  refine ⟨u, ?_⟩
  have h3 : (u : ZMod q) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have h1 : (u : ZMod q) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have : ((u : ZMod q) - 1) * ((u : ZMod q) ^ 2 + u + 1) = 0 := by
    linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)

private lemma mem_center_of_pow_three (hq3 : q % 3 = 1) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) {c : GL (Fin 3) (ZMod q)}
    (hc : ∀ h ∈ H, c * h = h * c) (hc3 : c ^ 3 = 1) :
    c ∈ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  obtain ⟨ω, hω⟩ := exists_cube_root hq3
  set M := (c : Matrix (Fin 3) (Fin 3) (ZMod q)) with hMdef
  have hM : ∀ h ∈ H, M * (h : Matrix (Fin 3) (Fin 3) (ZMod q)) = h * M := fun h hh => by
    rw [hMdef, ← Matrix.GeneralLinearGroup.coe_mul, hc h hh, Matrix.GeneralLinearGroup.coe_mul]
  have hM3 : M * (M * M) = 1 := by
    rw [← pow_three, hMdef, ← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hprod : (M - (1 : ZMod q) • 1) * ((M - ω • 1) * (M - (ω ^ 2) • 1)) = 0 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, one_smul,
      hM3]
    linear_combination (norm := module) hω • ((1 - ω) • (1 : Matrix (Fin 3) (Fin 3) (ZMod q)) -
      M * M + ω • M)
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  have key : ∃ ζ : ZMod q, M = ζ • 1 := by
    rcases injective_or_eq_smul_one hirr hM 1 with h1 | h1
    · rcases injective_or_eq_smul_one hirr hM ω with h2 | h2
      · rcases injective_or_eq_smul_one hirr hM (ω ^ 2) with h3 | h3
        · exfalso
          have hv : (Pi.single 0 1 : Fin 3 → ZMod q) ≠ 0 := by
            intro h; simpa using congrFun h 0
          apply hv
          apply h3; apply h2; apply h1
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hprod, Matrix.zero_mulVec]
        · exact ⟨_, h3⟩
      · exact ⟨_, h2⟩
    · exact ⟨_, h1⟩
  obtain ⟨ζ, hζ⟩ := key
  exact ⟨ζ, by rw [← hMdef, hζ, Matrix.smul_one_eq_diagonal]; rfl⟩

private lemma eq_one_of_mem_center {x : GL (Fin 3) (ZMod q)}
    (hx : x ∈ Subgroup.center (GL (Fin 3) (ZMod q)))
    (hdet : (x : Matrix (Fin 3) (Fin 3) (ZMod q)).det = 1) (hord : ¬ 3 ∣ orderOf x) : x = 1 := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hx
  have hc3 : c ^ 3 = 1 := by
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at hdet
    exact hdet
  have hx3 : x ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hc, ← map_pow, hc3, map_one, Units.val_one]
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (by rw [h]) hord

private lemma pow_mem_center_of_mul {h z : GL (Fin 3) (ZMod q)}
    (hz : ∀ y : GL (Fin 3) (ZMod q), z * y = y * z) {n : ℕ}
    (hn : (h * z) ^ n ∈ Subgroup.center (GL (Fin 3) (ZMod q))) :
    h ^ n ∈ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  have hzc : z ∈ Subgroup.center (GL (Fin 3) (ZMod q)) :=
    Subgroup.mem_center_iff.mpr fun y => (hz y).symm
  have hcomm : Commute h z := (hz h).symm
  have : h ^ n = (h * z) ^ n * (z ^ n)⁻¹ := by rw [hcomm.mul_pow, mul_inv_cancel_right]
  rw [this]
  exact Subgroup.mul_mem _ hn (Subgroup.inv_mem _ (Subgroup.pow_mem _ hzc n))

private lemma coe_mem_center_of_mem_center (hq3 : q % 3 = 1) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hZ : Nat.card (Subgroup.center H) = 3) {c : H}
    (hc : c ∈ Subgroup.center H) :
    (c : GL (Fin 3) (ZMod q)) ∈ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  apply mem_center_of_pow_three hq3 hirr
  · intro h hh
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨h, hh⟩)).symm
  · have h9 : (⟨c, hc⟩ : Subgroup.center H) ^ Nat.card (Subgroup.center H) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h9
    have := congrArg (fun z : Subgroup.center H => ((z : H) : GL (Fin 3) (ZMod q))) h9
    simpa using this

private lemma mem_center_of_coe_mem_center {H : Subgroup (GL (Fin 3) (ZMod q))} {c : H}
    (hc : (c : GL (Fin 3) (ZMod q)) ∈ Subgroup.center (GL (Fin 3) (ZMod q))) :
    c ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  exact fun y => Subtype.ext (hc y)

private lemma psi_eq_one_iff (hq3 : q % 3 = 1) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hZ : Nat.card (Subgroup.center H) = 3)
    (e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) (c : H) :
    e (QuotientGroup.mk c) = 1 ↔
      (c : GL (Fin 3) (ZMod q)) ∈ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]
  exact ⟨coe_mem_center_of_mem_center hq3 hirr hZ, mem_center_of_coe_mem_center⟩

private lemma mem_center_of_commute_alt6 (hq3 : q % 3 = 1) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hZ : Nat.card (Subgroup.center H) = 3)
    (e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)) {g x : GL (Fin 3) (ZMod q)}
    (hgH : g ∈ H) (hxH : x ∈ H) (hcomm : g * x = x * g)
    (hg3 : g ^ 3 ∈ Subgroup.center (GL (Fin 3) (ZMod q)))
    (hg1 : g ∉ Subgroup.center (GL (Fin 3) (ZMod q))) {n : ℕ} (hn : ¬ 3 ∣ n)
    (hxn : x ^ n ∈ Subgroup.center (GL (Fin 3) (ZMod q))) :
    x ∈ Subgroup.center (GL (Fin 3) (ZMod q)) := by
  have hψ := psi_eq_one_iff hq3 hirr hZ e
  set a := e (QuotientGroup.mk (⟨g, hgH⟩ : H)) with ha
  set b := e (QuotientGroup.mk (⟨x, hxH⟩ : H)) with hb
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← map_pow, ← QuotientGroup.mk_pow, hψ, Subgroup.coe_pow]
    exact hg3
  have ha1 : (a : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hg1 ((hψ _).mp (Subtype.ext h))
  have hbn : b ^ n = 1 := by
    rw [hb, ← map_pow, ← QuotientGroup.mk_pow, hψ, Subgroup.coe_pow]
    exact hxn
  have hab : (b : Equiv.Perm (Fin 6)) * a = a * b := by
    have : b * a = a * b := by
      rw [ha, hb, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (congrArg _ (Subtype.ext hcomm.symm))
    exact congrArg Subtype.val this
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine CFSG.RankThree.PartTwo.Sec14.Item148PtRes.pow_three_eq_one_of_commute_six
      (x := (a : Equiv.Perm (Fin 6))) ?_ ha1 b.2 hab
    rw [← Subgroup.coe_pow, ha3, Subgroup.coe_one]
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn
  have hb1 : b ^ Nat.gcd 3 n = 1 := pow_gcd_eq_one.mpr ⟨hb3, hbn⟩
  rw [hcop, pow_one] at hb1
  exact (hψ _).mp hb1

private lemma five_le_of_mod_three (hq3 : q % 3 = 1) : 5 ≤ q := by
  have h2 := (Fact.out : q.Prime).two_le
  by_contra h
  interval_cases q
  · simp at hq3
  · simp at hq3
  · exact absurd (Fact.out : (4 : ℕ).Prime) (by decide)

private lemma commute_of_mul_scalar {g z x w : GL (Fin 3) (ZMod q)}
    (hz : ∀ y : GL (Fin 3) (ZMod q), z * y = y * z) (hw : ∀ y : GL (Fin 3) (ZMod q), w * y = y * w)
    (h : g * z * (x * w) = x * w * (g * z)) : g * x = x * g := by
  have h1 : g * z * (x * w) = g * x * (z * w) := by
    rw [show g * z * (x * w) = g * (z * x) * w by simp only [mul_assoc], hz x]
    simp only [mul_assoc]
  have h2 : x * w * (g * z) = x * g * (z * w) := by
    rw [show x * w * (g * z) = x * (w * g) * z by simp only [mul_assoc], hw g,
      mul_assoc, mul_assoc, hw z, mul_assoc]
  exact mul_right_cancel (h1.symm.trans (h.trans h2))

end Helpers

theorem eq_one_of_threeA6 (hA6 : CFSG.RankThree.PartOne.N1322.KF1322ThreeA6Norm) {q : ℕ}
    [Fact q.Prime] (hq3 : q % 3 = 1) {A : Subgroup (GL (Fin 3) (ZMod q))}
    (hA : IsElemModScalars 3 A) {H : Subgroup (GL (Fin 3) (ZMod q))}
    (hirr : IsIrreducibleMatrixRep H.subtype) (hperf : Group.IsPerfect H)
    (hZ : Nat.card (Subgroup.center H) = 3)
    (hiso : Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 6)))
    (hnA : ∀ g ∈ A, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hnX : ∀ y ∈ fixSetThree 3 A, ∀ x ∈ H, y * x * y⁻¹ ∈ H) :
    ∀ x ∈ fixSetThree 3 A, x = 1 := by
  intro x hx
  obtain ⟨hdet, hord, g, hgA, hgZ, hgx⟩ := hx
  have hq5 := five_le_of_mod_three hq3
  obtain ⟨e⟩ := hiso
  obtain ⟨xh, hxH, zx, hzx, rfl⟩ :=
    hA6 q hq5 H hirr hperf hZ ⟨e⟩ x (hnX x ⟨hdet, hord, g, hgA, hgZ, hgx⟩)
  obtain ⟨gh, hgH, zg, hzg, rfl⟩ := hA6 q hq5 H hirr hperf hZ ⟨e⟩ g (hnA g hgA)
  have hzgc : zg ∈ Subgroup.center (GL (Fin 3) (ZMod q)) :=
    Subgroup.mem_center_iff.mpr fun y => (hzg y).symm
  have hzxc : zx ∈ Subgroup.center (GL (Fin 3) (ZMod q)) :=
    Subgroup.mem_center_iff.mpr fun y => (hzx y).symm
  have hxc := mem_center_of_commute_alt6 hq3 hirr hZ e hgH hxH
    (commute_of_mul_scalar hzg hzx hgx) (pow_mem_center_of_mul hzg (hA.pow_mem _ hgA))
    (fun h => hgZ (Subgroup.mul_mem _ h hzgc)) hord
    (pow_mem_center_of_mul hzx (by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _))
  exact eq_one_of_mem_center (Subgroup.mul_mem _ hxc hzxc) hdet hord

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
