module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypDefs
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine

public section

open scoped MatrixGroups
open CFSG.GorensteinWalter

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

section TorusDataAux

open Matrix

variable {K : Type*} [Field K]

private def tdDiag (a : Kˣ) : SL(2, K) :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two_of]⟩

private theorem tdDiag_mem_borel (a : Kˣ) : tdDiag a ∈ sl2Borel K := by
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
  simp [tdDiag]

private theorem tdDiag_conj (a : Kˣ) (x : K) :
    tdDiag a * sl2UpperUnipotent x * (tdDiag a)⁻¹ =
      sl2UpperUnipotent ((a : K) ^ 2 * x) := by
  rw [sl2Borel_conj_upperUnipotent (tdDiag_mem_borel a)]
  simp [tdDiag]

private theorem tdDiag_conj_psl2 (a : Kˣ) (x : K) :
    psl2QuotientMap K (tdDiag a) * psl2QuotientMap K (sl2UpperUnipotent x) *
      (psl2QuotientMap K (tdDiag a))⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent ((a : K) ^ 2 * x)) := by
  rw [← map_inv, ← map_mul, ← map_mul, tdDiag_conj]

private theorem tdConjMemUnip {A : SL(2, K)} (hA : A ∈ sl2Borel K) {h : PSL2 K}
    (hh : h ∈ psl2UpperUnipotentSubgroup K) :
    psl2QuotientMap K A * h * (psl2QuotientMap K A)⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff h).1 hh
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hA]
  exact (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨_, rfl⟩

private theorem tdMemNormalizer {A : SL(2, K)} (hA : A ∈ sl2Borel K) :
    psl2QuotientMap K A ∈
      Subgroup.normalizer (psl2UpperUnipotentSubgroup K : Set (PSL2 K)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨fun hh => tdConjMemUnip hA hh, fun hh => ?_⟩
  have := tdConjMemUnip (inv_mem hA) hh
  simpa [mul_assoc] using this

private theorem tdUnipPow (x : K) (n : ℕ) :
    psl2QuotientMap K (sl2UpperUnipotent x) ^ n =
      psl2QuotientMap K (sl2UpperUnipotent ((n : K) * x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← map_mul, sl2UpperUnipotent_mul, Nat.cast_succ, add_mul, one_mul]

private theorem tdUnipInj {x y : K}
    (h : psl2QuotientMap K (sl2UpperUnipotent x) = psl2QuotientMap K (sl2UpperUnipotent y)) :
    x = y := by
  have hcenter : sl2UpperUnipotent (x - y) ∈ Subgroup.center (SL(2, K)) := by
    have hq : psl2QuotientMap K (sl2UpperUnipotent (x - y)) = 1 := by
      rw [sub_eq_add_neg, ← sl2UpperUnipotent_mul, map_mul, ← sl2UpperUnipotent_inv, map_inv, h,
        mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hscalar :=
    Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have h01 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply sub_eq_zero.mp
  simpa [sl2UpperUnipotent] using h01.symm

private theorem td_intCast_pow_prime (p : ℕ) [Fact p.Prime] [CharP K p] (b : ℤ) :
    (b : K) ^ p = b := by
  have h := congrArg (ZMod.castHom (dvd_refl p) K) (ZMod.pow_card (b : ZMod p))
  rwa [map_pow, map_intCast] at h

private theorem tdUnitPowNotInt (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K] (n : ℕ)
    (hn : 3 ≤ n) (hp5 : 5 ≤ p) (hcard : Nat.card K = p ^ n) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {c : ℕ} (hc0 : 0 < c) (hc6 : c ≤ 6) (b : ℤ) :
    (g : K) ^ c ≠ (b : K) := by
  intro hb
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have hpow : (g : K) ^ (c * p) = (g : K) ^ c := by
    rw [pow_mul, hb]
    exact td_intCast_pow_prime p b
  have e : c * p = c * (p - 1) + c := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [Nat.mul_succ]
  have h1 : (g : K) ^ (c * (p - 1)) = 1 := by
    have h2 : (g : K) ^ (c * (p - 1)) * (g : K) ^ c = 1 * (g : K) ^ c := by
      rw [one_mul, ← pow_add, ← e]
      exact hpow
    exact mul_right_cancel₀ (pow_ne_zero c hg0) h2
  have h3 : g ^ (c * (p - 1)) = 1 := Units.ext (by simpa using h1)
  have h4 : orderOf g = p ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hcard]
  have h5 : 0 < c * (p - 1) := Nat.mul_pos hc0 (by omega)
  have h6 := Nat.le_of_dvd h5 (orderOf_dvd_of_pow_eq_one h3)
  rw [h4] at h6
  have h7 : 25 * p ≤ p ^ 3 := by
    have h7a : 5 * 5 ≤ p * p := Nat.mul_le_mul hp5 hp5
    have h7b : 5 * 5 * p ≤ p * p * p := Nat.mul_le_mul_right p h7a
    have h7c : p ^ 3 = p * p * p := by ring
    omega
  have h8 : p ^ 3 ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  have h9 : c * (p - 1) ≤ 6 * (p - 1) := Nat.mul_le_mul_right _ hc6
  omega

private def tdPre (H : Subgroup (PSL2 K)) : AddSubgroup K where
  carrier := {x | psl2QuotientMap K (sl2UpperUnipotent x) ∈ H}
  add_mem' := by
    intro a b ha hb
    have ha' : psl2QuotientMap K (sl2UpperUnipotent a) ∈ H := ha
    have hb' : psl2QuotientMap K (sl2UpperUnipotent b) ∈ H := hb
    show psl2QuotientMap K (sl2UpperUnipotent (a + b)) ∈ H
    rw [← sl2UpperUnipotent_mul, map_mul]
    exact H.mul_mem ha' hb'
  zero_mem' := by
    show psl2QuotientMap K (sl2UpperUnipotent 0) ∈ H
    rw [sl2UpperUnipotent_zero, map_one]
    exact H.one_mem
  neg_mem' := by
    intro a ha
    have ha' : psl2QuotientMap K (sl2UpperUnipotent a) ∈ H := ha
    show psl2QuotientMap K (sl2UpperUnipotent (-a)) ∈ H
    rw [← sl2UpperUnipotent_inv, map_inv]
    exact H.inv_mem ha'

private theorem tdCardPre [Finite K] (p : ℕ) (H : Subgroup (PSL2 K))
    (hHU : H ≤ psl2UpperUnipotentSubgroup K)
    (hHcard : Nat.card (psl2UpperUnipotentSubgroup K) = p * Nat.card H) :
    Nat.card K = p * Nat.card (tdPre H) := by
  have hN : Nat.card (tdPre H) = Nat.card H := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : tdPre H => (⟨psl2QuotientMap K (sl2UpperUnipotent (x : K)), x.2⟩ : H)) ⟨?_, ?_⟩)
    · intro x y hxy
      apply Subtype.ext
      have h2 : psl2QuotientMap K (sl2UpperUnipotent (x : K)) =
          psl2QuotientMap K (sl2UpperUnipotent (y : K)) := congrArg Subtype.val hxy
      exact tdUnipInj h2
    · rintro ⟨h, hh⟩
      obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff h).1 (hHU hh)
      exact ⟨⟨x, hh⟩, rfl⟩
  rw [← psl2UpperUnipotentSubgroup_card K, hHcard, hN]

private theorem tdExistsInt (p : ℕ) [Fact p.Prime] [Finite K] {H' : AddSubgroup K}
    (hcard : Nat.card K = p * Nat.card H') {t : K} (ht : ∀ x ∈ H', t * x ∈ H') :
    ∃ b : ℤ, t = b := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpos : 0 < Nat.card H' := by
    haveI : Nonempty H' := ⟨⟨0, H'.zero_mem⟩⟩
    exact Nat.card_pos
  have hidx : H'.index = p := by
    have h1 : Nat.card H' * H'.index = Nat.card H' * p := by
      rw [AddSubgroup.card_mul_index, hcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hne : H' ≠ ⊤ := by
    intro htop
    rw [htop, AddSubgroup.index_top] at hidx
    omega
  have hc : ∃ c : K, c ∉ H' := by
    by_contra hall
    push Not at hall
    apply hne
    ext x
    exact ⟨fun _ => AddSubgroup.mem_top x, fun _ => hall x⟩
  obtain ⟨c, hcH⟩ := hc
  have hQ : Nat.card (K ⧸ H') = p := by
    rw [← AddSubgroup.index_eq_card, hidx]
  have hq0 : (c : K ⧸ H') ≠ 0 := by
    intro h0
    exact hcH ((QuotientAddGroup.eq_zero_iff c).mp h0)
  have hord : addOrderOf (c : K ⧸ H') = p := by
    have hdvd : addOrderOf (c : K ⧸ H') ∣ p := by
      rw [← hQ]
      exact addOrderOf_dvd_natCard _
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hq0
    · exact h1
  have hS : AddSubgroup.zmultiples (c : K ⧸ H') = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [Nat.card_zmultiples, hord, hQ]
  have hspan : ∀ x : K, ∃ k : ℤ, -(k • c) + x ∈ H' := by
    intro x
    have hx : (x : K ⧸ H') ∈ AddSubgroup.zmultiples (c : K ⧸ H') := by
      rw [hS]
      exact AddSubgroup.mem_top _
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    refine ⟨k, ?_⟩
    rw [← QuotientAddGroup.mk_zsmul] at hk
    exact QuotientAddGroup.eq.mp hk
  obtain ⟨m, hm⟩ := hspan (t * c)
  obtain ⟨u, hu_def⟩ : ∃ u : K, u = t - (m : K) := ⟨_, rfl⟩
  have hbase : ∀ h ∈ H', u * h ∈ H' := by
    intro h hh
    have e : u * h = t * h + -(m • h) := by
      rw [hu_def]
      simp only [zsmul_eq_mul]
      ring
    rw [e]
    exact add_mem (ht h hh) (neg_mem (zsmul_mem hh m))
  have huc : u * c ∈ H' := by
    have e : u * c = -(m • c) + t * c := by
      rw [hu_def]
      simp only [zsmul_eq_mul]
      ring
    rw [e]
    exact hm
  have hu : ∀ x : K, u * x ∈ H' := by
    intro x
    obtain ⟨k, hk⟩ := hspan x
    have e : u * x = k • (u * c) + u * (-(k • c) + x) := by
      simp only [zsmul_eq_mul]
      ring
    rw [e]
    exact add_mem (zsmul_mem huc k) (hbase _ hk)
  have hu0 : u = 0 := by
    by_contra hne0
    apply hne
    ext y
    refine ⟨fun _ => AddSubgroup.mem_top y, fun _ => ?_⟩
    have hy := hu (u⁻¹ * y)
    rwa [mul_inv_cancel_left₀ hne0] at hy
  have ht0 : t - (m : K) = 0 := by
    rw [← hu_def]
    exact hu0
  exact ⟨m, sub_eq_zero.mp ht0⟩

private theorem tdConjPow (A : PSL2 K) (s : K)
    (hA : ∀ x : K, A * psl2QuotientMap K (sl2UpperUnipotent x) * A⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent (s * x))) (j : ℕ) (x : K) :
    A ^ j * psl2QuotientMap K (sl2UpperUnipotent x) * (A ^ j)⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent (s ^ j * x)) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have e : ∀ a b y : PSL2 K, a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by
      intro a b y
      simp only [_root_.mul_inv_rev, mul_assoc]
    rw [pow_succ' A j, e, ih, hA, pow_succ' s j, mul_assoc]

private theorem tdNoStable (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K] (n : ℕ) (hn : 3 ≤ n)
    (hp5 : 5 ≤ p) (hcard : Nat.card K = p ^ n) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {j : ℕ} (hj1 : 1 ≤ j) (hj3 : j ≤ 3)
    (H : Subgroup (PSL2 K)) (hHU : H ≤ psl2UpperUnipotentSubgroup K)
    (hHcard : Nat.card (psl2UpperUnipotentSubgroup K) = p * Nat.card H) :
    ∃ h ∈ H, psl2QuotientMap K (tdDiag g) ^ j * h * (psl2QuotientMap K (tdDiag g) ^ j)⁻¹ ∉ H := by
  by_contra hcon
  push Not at hcon
  have hstab : ∀ x ∈ tdPre H, ((g : K) ^ 2) ^ j * x ∈ tdPre H := by
    intro x hx
    have hx' : psl2QuotientMap K (sl2UpperUnipotent x) ∈ H := hx
    have h1 := hcon _ hx'
    rw [tdConjPow (psl2QuotientMap K (tdDiag g)) ((g : K) ^ 2) (tdDiag_conj_psl2 g) j x] at h1
    exact h1
  obtain ⟨b, hb⟩ := tdExistsInt p (tdCardPre p H hHU hHcard) hstab
  rw [← pow_mul] at hb
  exact tdUnitPowNotInt p n hn hp5 hcard hg (c := 2 * j) (by omega) (by omega) b hb

end TorusDataAux

theorem psl2_torus_data_hyperplane (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) (hn : 3 ≤ n) :
    ∃ (U : Subgroup PSL(2, GaloisField p n)) (σ : PSL(2, GaloisField p n)),
      Nat.card U = p ^ n ∧ (∀ u ∈ U, u ^ p = 1) ∧ (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) ∧
      MovesHyperplanes p U σ := by
  have hcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p n)ˣ)
  refine ⟨psl2UpperUnipotentSubgroup (GaloisField p n),
    psl2QuotientMap (GaloisField p n) (tdDiag g), ?_, ?_, ?_, ?_⟩
  · rw [psl2UpperUnipotentSubgroup_card, hcard]
  · intro u hu
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    rw [tdUnipPow, CharP.cast_eq_zero, zero_mul, sl2UpperUnipotent_zero, map_one]
  · intro u hu v hv
    obtain ⟨x, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    obtain ⟨y, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff v).1 hv
    rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]
  · unfold MovesHyperplanes
    refine ⟨tdMemNormalizer (tdDiag_mem_borel g), ?_⟩
    intro j hj1 hj3 H hHU hHcard
    exact tdNoStable p n hn hp5 hcard hg hj1 hj3 H hHU hHcard

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
