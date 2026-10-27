module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6B
public import CFSG.Mathlib.RingTheory.UnitOrderOf

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open
open scoped commutatorElement

theorem isElemAbelian_comap_of_le_lift {K C : Type} [Group K] [Finite K] [Group C] [Finite C]
    (π : K →* C) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K)
    {q : ℕ} (hkerq : ∀ k ∈ π.ker, k ^ q = 1)
    {Y B : Subgroup C} (hYperf : commutator ↥Y = ⊤) (hYmult : TrivialMultiplierT ↥Y)
    (hBY : B ≤ Y) (hB : IsElemAbelian q B) : IsElemAbelian q (Subgroup.comap π B) := by
  classical
  obtain ⟨hHsup, -, -, hDdisj, -⟩ := lift_perfect_trivialMult π hπ hker hYperf hYmult
  set H : Subgroup K := Subgroup.comap π Y with hH
  set D : Subgroup K := ⁅H, H⁆ with hD
  have hcomapB : Subgroup.comap π B ≤ H := Subgroup.comap_mono hBY
  have hdecomp : ∀ b ∈ Subgroup.comap π B, ∃ k ∈ π.ker, ∃ d ∈ D, k * d = b := by
    intro b hb
    have hbH : b ∈ H := hcomapB hb
    have hb' : b ∈ π.ker ⊔ D := hHsup.symm ▸ hbH
    exact Subgroup.mem_sup_of_normal_left.mp hb'
  have hcent : ∀ k ∈ π.ker, ∀ x : K, x * k = k * x :=
    fun k hk x => Subgroup.mem_center_iff.mp (hker hk) x
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨ka, hka, da, hda, hka_da⟩ := hdecomp a a.2
    obtain ⟨kb, hkb, db, hdb, hkb_db⟩ := hdecomp b b.2
    have hpa : π da = π a := by
      rw [← hka_da, map_mul, MonoidHom.mem_ker.mp hka, one_mul]
    have hpb : π db = π b := by
      rw [← hkb_db, map_mul, MonoidHom.mem_ker.mp hkb, one_mul]
    haveI hBcomm : IsMulCommutative ↥B := hB.1
    have hcommB : π da * π db = π db * π da := by
      rw [hpa, hpb]
      exact congrArg Subtype.val
        (mul_comm' ⟨π a, Subgroup.mem_comap.mp a.2⟩ ⟨π b, Subgroup.mem_comap.mp b.2⟩)
    have hDH : D ≤ H := by
      rw [hD]
      exact Subgroup.commutator_le_self H
    have hcD : ⁅da, db⁆ ∈ D := Subgroup.commutator_mem_commutator (hDH hda) (hDH hdb)
    have hcKer : ⁅da, db⁆ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcommB
    have hc1 : ⁅da, db⁆ = 1 := by
      have hmem : ⁅da, db⁆ ∈ D ⊓ π.ker := Subgroup.mem_inf.mpr ⟨hcD, hcKer⟩
      rw [hDdisj] at hmem
      simpa using hmem
    have hdcomm : da * db = db * da := commutatorElement_eq_one_iff_mul_comm.mp hc1
    have hkakb : ka * kb = kb * ka := (hcent ka hka kb).symm
    have hkbda : da * kb = kb * da := hcent kb hkb da
    have hkadb : db * ka = ka * db := hcent ka hka db
    have hab : (ka * da) * (kb * db) = (ka * kb) * (da * db) := by
      calc (ka * da) * (kb * db) = ka * (da * (kb * db)) := by rw [mul_assoc]
        _ = ka * ((da * kb) * db) := by rw [← mul_assoc da kb db]
        _ = ka * ((kb * da) * db) := by rw [hkbda]
        _ = ka * (kb * (da * db)) := by rw [mul_assoc kb da db]
        _ = (ka * kb) * (da * db) := by rw [← mul_assoc]
    have hba : (kb * db) * (ka * da) = (kb * ka) * (db * da) := by
      calc (kb * db) * (ka * da) = kb * (db * (ka * da)) := by rw [mul_assoc]
        _ = kb * ((db * ka) * da) := by rw [← mul_assoc db ka da]
        _ = kb * ((ka * db) * da) := by rw [hkadb]
        _ = kb * (ka * (db * da)) := by rw [mul_assoc ka db da]
        _ = (kb * ka) * (db * da) := by rw [← mul_assoc]
    calc a * b = (ka * da) * (kb * db) := by rw [hka_da, hkb_db]
      _ = (ka * kb) * (da * db) := hab
      _ = (kb * ka) * (db * da) := by rw [hkakb, hdcomm]
      _ = (kb * db) * (ka * da) := hba.symm
      _ = b * a := by rw [hkb_db, hka_da]
  · obtain ⟨k, hk, d, hd, hkd⟩ := hdecomp x hx
    have hx' : π x ∈ B := Subgroup.mem_comap.mp hx
    have hpd : π d = π x := by
      rw [← hkd, map_mul, MonoidHom.mem_ker.mp hk, one_mul]
    have hdqD : d ^ q ∈ D := Subgroup.pow_mem D hd q
    have hdqker : d ^ q ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hpd]
      exact hB.2 (π x) hx'
    have hdq1 : d ^ q = 1 := by
      have hmem : d ^ q ∈ D ⊓ π.ker := Subgroup.mem_inf.mpr ⟨hdqD, hdqker⟩
      rw [hDdisj] at hmem
      simpa using hmem
    have hcomm : Commute k d := (hcent k hk d).symm
    rw [← hkd, hcomm.mul_pow, hkerq k hk, hdq1, one_mul]

theorem comap_le_normalizer_of_lift_twoGroup {K C : Type} [Group K] [Finite K] [Group C]
    (π : K →* C) (hker : π.ker ≤ Subgroup.center K) (hodd : Odd (Nat.card π.ker))
    {Y B : Subgroup C} (hBY : B ≤ Subgroup.normalizer (Y : Set C)) {S : Subgroup K}
    (hS2 : IsPGroup 2 ↥S) (hSY : Subgroup.comap π Y = S ⊔ π.ker) :
    Subgroup.comap π B ≤ Subgroup.normalizer (S : Set K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ b ∈ Subgroup.comap π B, ∀ x ∈ S, b * x * b⁻¹ ∈ S := by
    intro b hb x hx
    have hbN : π b ∈ Subgroup.normalizer (Y : Set C) := hBY hb
    have hxY : π x ∈ Y := by
      have hx' : x ∈ Subgroup.comap π Y := hSY.symm ▸ Subgroup.mem_sup_left hx
      exact Subgroup.mem_comap.mp hx'
    have hmem : b * x * b⁻¹ ∈ Subgroup.comap π Y := by
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hbN (π x)).mp hxY
    rw [hSY] at hmem
    obtain ⟨s, hs, z, hz, hsz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    obtain ⟨a, ha⟩ := hS2.exists_card_eq
    have hxpow : x ^ Nat.card ↥S = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := ↥S) (x := ⟨x, hx⟩))
    have hspow : s ^ Nat.card ↥S = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (G := ↥S) (x := ⟨s, hs⟩))
    have hconjpow : (b * x * b⁻¹) ^ Nat.card ↥S = 1 := by
      rw [← MulAut.conj_apply, ← map_pow, hxpow, map_one]
    have hszpow : (s * z) ^ Nat.card ↥S = 1 := by rw [hsz, hconjpow]
    have hcomm : Commute s z := Subgroup.mem_center_iff.mp (hker hz) s
    have hzpow : z ^ Nat.card ↥S = 1 := by
      have h := hszpow
      rw [hcomm.mul_pow, hspow, one_mul] at h
      exact h
    have hz2 : orderOf z ∣ Nat.card ↥S := orderOf_dvd_of_pow_eq_one hzpow
    have hzord : orderOf z ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard π.ker hz
    have hcop : Nat.Coprime (Nat.card ↥S) (Nat.card π.ker) := by
      rw [ha]
      exact (Nat.coprime_two_left.mpr hodd).pow_left a
    have hz1 : z = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hz2 hzord)
    rw [← hsz, hz1, mul_one]
    exact hs
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key b hb x
  · intro hx
    have hbinv : b⁻¹ ∈ Subgroup.comap π B := (Subgroup.comap π B).inv_mem hb
    have h := key b⁻¹ hbinv (b * x * b⁻¹) hx
    simpa [mul_assoc] using h

theorem comap_inf_centralizer_le_ker {K C : Type} [Group K] [Group C] (π : K →* C)
    {B Y : Subgroup C} {S : Subgroup K} (hSY : Subgroup.map π S = Y)
    (hBY : B ⊓ Subgroup.centralizer (Y : Set C) = ⊥) :
    Subgroup.comap π B ⊓ Subgroup.centralizer (S : Set K) ≤ π.ker := by
  intro x hx
  obtain ⟨hxB, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [MonoidHom.mem_ker]
  have hxcent : π x ∈ Subgroup.centralizer (Y : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hSY] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    simpa only [map_mul] using congrArg (⇑π) (hxC s hs)
  have hmem : π x ∈ B ⊓ Subgroup.centralizer (Y : Set C) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mp hxB, hxcent⟩
  rw [hBY] at hmem
  simpa using hmem

theorem subgroupOf_inf_centralizer_pair {G : Type*} [Group G] (H : Subgroup G) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) :
    (H ⊓ Subgroup.centralizer ({a, b} : Set G)).subgroupOf H =
      Subgroup.centralizer ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨-, hxc⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
    rw [Subgroup.mem_centralizer_iff] at hxc ⊢
    intro y hy
    rcases hy with rfl | rfl
    · exact Subtype.ext (hxc a (by simp))
    · exact Subtype.ext (hxc b (by simp))
  · intro hx
    have hxa : a * (x : G) = (x : G) * a :=
      congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨a, ha⟩ (by simp))
    have hxb : b * (x : G) = (x : G) * b :=
      congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨b, hb⟩ (by simp))
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · exact hxa
    · exact hxb

theorem exists_center_eq_zpowers_of_card_three {X : Type} [Group X] [Finite X]
    (h3 : Nat.card (Subgroup.center X) = 3) :
    ∃ z : X, z ∈ Subgroup.center X ∧ orderOf z = 3 ∧ Subgroup.center X = Subgroup.zpowers z := by
  classical
  haveI : Finite ↥(Subgroup.center X) := Subtype.finite
  have hnt : Nontrivial ↥(Subgroup.center X) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h3]; norm_num)
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center X))
  have hdvd : orderOf z ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center X) z.2
    rw [h3, Subgroup.orderOf_coe] at h
    exact h
  have hne : orderOf z ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    exact hz1
  have hord : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  refine ⟨(z : X), z.2, ?_, ?_⟩
  · show orderOf (z : X) = 3
    rw [Subgroup.orderOf_coe]
    exact hord
  · refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers (z : X))
      (K := Subgroup.center X) (Subgroup.zpowers_le.mpr z.2) ?_).symm
    rw [Nat.card_zpowers, h3]
    show 3 ≤ orderOf (z : X)
    rw [Subgroup.orderOf_coe, hord]

theorem card_closure_lift_triple {K C : Type} [Group K] [Finite K] [Group C] (π : K →* C)
    {z e f : K} (hker : π.ker = Subgroup.zpowers z) (hz3 : orderOf z = 3)
    (h9 : Nat.card (Subgroup.closure ({π e, π f} : Set C)) = 9) :
    Nat.card (Subgroup.closure ({z, e, f} : Set K)) = 27 := by
  classical
  set H : Subgroup K := Subgroup.closure ({z, e, f} : Set K) with hH
  have hzH : z ∈ H := Subgroup.subset_closure (by simp)
  have hkerH : π.ker ≤ H := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hzH
  have hzker : z ∈ π.ker := by
    rw [hker]
    exact Subgroup.mem_zpowers z
  have hz1 : π z = 1 := MonoidHom.mem_ker.mp hzker
  have hmapH : Subgroup.map π H = Subgroup.closure ({π e, π f} : Set C) := by
    rw [hH, MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton]
    rw [hz1]
    simp
  have hkercard : Nat.card π.ker = 3 := by rw [hker, Nat.card_zpowers, hz3]
  have h := Subgroup.relIndex_mul_card π.ker H
  rw [Subgroup.relIndex_ker, inf_eq_left.mpr hkerH, hmapH, h9, hkercard] at h
  omega

theorem exists_unit_orderOf_three_algebraicClosure (F : Type) [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∃ ω : (AlgebraicClosure F)ˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ orderOf ω = 3 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard2 : Nat.card F = 2 ^ (n * 2) := by rw [hF, pow_mul]
  have hcardF : Fintype.card F = 2 ^ (n * 2) := by
    rw [← Nat.card_eq_fintype_card, hcard2]
  haveI hcharF : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) hcardF
  let Ω := AlgebraicClosure F
  have h3 : ((3 : ℕ) : Ω) ≠ 0 := by
    have h2 : ((2 : ℕ) : Ω) = 0 := CharP.cast_eq_zero Ω 2
    have he : ((3 : ℕ) : Ω) = ((2 : ℕ) : Ω) + 1 := by norm_num
    rw [he, h2, zero_add]
    exact one_ne_zero
  obtain ⟨ω, hω⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := Ω) (n := 3) h3
  refine ⟨ω, ?_, ?_, hω⟩
  · have h := pow_orderOf_eq_one ω
    rwa [hω] at h
  · intro h1
    have hord : orderOf ω = 1 := by rw [h1]; exact orderOf_one
    omega

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
