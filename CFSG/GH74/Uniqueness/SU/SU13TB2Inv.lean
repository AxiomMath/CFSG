module

public import CFSG.GroupTheory.OddInversion
public import CFSG.RankThree.Asc83Table.GL23
public import CFSG.GH74.Uniqueness.SU.SU13TB0Syl
public import CFSG.GH74.Uniqueness.SU.SU13TB1Conj
public import CFSG.GH74.Uniqueness.SU.SU13TB1Core
public import CFSG.GH74.Uniqueness.SU.SU4Quot
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB CFSG.RankThree.Asc83Table

@[expose] def IsInv23 (g : GL23) : Prop := g * g = 1 ∧ g ≠ 1

@[expose] def IsCen23 (g : GL23) : Prop := ∀ x : GL23, x * g = g * x

instance : DecidablePred IsInv23 := fun g => by unfold IsInv23; infer_instance

instance : DecidablePred IsCen23 := fun g => by unfold IsCen23; infer_instance

@[expose] def m1 : GL23 := gl23 !![2, 0; 0, 2] !![2, 0; 0, 2] (by decide) (by decide)

theorem gl_central : ∀ g : GL23, IsInv23 g → IsCen23 g → g = m1 := by decide +kernel

theorem gl_card_centralizer : ∀ g : GL23, IsInv23 g → ¬ IsCen23 g →
    Fintype.card {x : GL23 // x * g = g * x} = 4 := by decide +kernel

theorem gl_conj : ∀ g h : GL23, IsInv23 g → ¬ IsCen23 g → IsInv23 h → ¬ IsCen23 h →
    ∃ x : GL23, x * g * x⁻¹ = h := by decide +kernel

variable {G : Type} [Group G]

theorem exists_conj_of_involution_coset {D : Subgroup G} (hD : Odd (Nat.card D)) {w v : G}
    (hw : orderOf w = 2) (hv : orderOf v = 2) (h : v * w⁻¹ ∈ D) :
    ∃ s ∈ D, s * w * s⁻¹ = v := by
  have hwD : w ∉ D := CFSG.OddInversion.notMem_of_odd_card hD hw
  have hv' : orderOf ((v * w⁻¹) * w) = 2 := by rw [inv_mul_cancel_right]; exact hv
  have hJ : v * w⁻¹ ∈ CFSG.OddInversion.invertedSet D w :=
    (CFSG.OddInversion.orderOf_mul_eq_two_iff hw hwD h).mp hv'
  obtain ⟨s, hs, hss⟩ := CFSG.OddInversion.exists_sq_eq_of_mem_invertedSet hD hJ
  refine ⟨s, hs.1, ?_⟩
  have hsw : w * s * w⁻¹ = s⁻¹ := hs.2
  have : s * w * s⁻¹ = s ^ 2 * w := by
    calc s * w * s⁻¹ = s * (w * s⁻¹ * w⁻¹) * w := by group
      _ = s * (w * s * w⁻¹)⁻¹ * w := by group
      _ = s * s * w := by rw [hsw, inv_inv]
      _ = s ^ 2 * w := by rw [pow_two]
  rw [this, hss]; group

section M

variable [Finite G] {M : Subgroup G} {z : G}

theorem eq_one_of_mem_oc_of_sq {x : G} (hx : x ∈ oc M) (hx2 : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have h2 : orderOf x ∣ Nat.card (oc M) := by
    have := Subgroup.orderOf_dvd_natCard (oc M) hx
    exact this
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat (odd_card_oc M) h2
  have : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp this

theorem proj_ne_one {u : G} (hu : u ∈ M) (hu2 : orderOf u = 2) : proj M ⟨u, hu⟩ ≠ 1 := by
  intro h
  have h1 : (⟨u, hu⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by rw [← ker_proj M]; exact h
  have h2 : u ∈ oc M := mem_oc.mpr ⟨hu, h1⟩
  have := eq_one_of_mem_oc_of_sq h2 (by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hu2)
  rw [this, orderOf_one] at hu2
  exact absurd hu2 (by norm_num)

theorem involution_cases (f : Mbar M ≃* GL23) (hzM : z ∈ M) (hz : orderOf z = 2)
    (hzc : ∀ m ∈ M, m * z = z * m) {u : G} (hu : u ∈ M) (hu2 : orderOf u = 2) (huz : u ≠ z) :
    IsInv23 (f (proj M ⟨u, hu⟩)) ∧ ¬ IsCen23 (f (proj M ⟨u, hu⟩)) := by
  have hinv : ∀ {w : G} (hw : w ∈ M), orderOf w = 2 → IsInv23 (f (proj M ⟨w, hw⟩)) := by
    intro w hw hw2
    refine ⟨?_, fun h => proj_ne_one hw hw2 (f.injective (by rw [h, map_one]))⟩
    rw [← map_mul, ← map_mul]
    have : (⟨w, hw⟩ : ↥M) * ⟨w, hw⟩ = 1 :=
      Subtype.ext (by simp only [Subgroup.coe_one, ← pow_two]; exact sq_eq_one_of_orderOf_eq_two hw2)
    rw [this, map_one, map_one]
  refine ⟨hinv hu hu2, fun hcen => huz ?_⟩
  have hzcen : IsCen23 (f (proj M ⟨z, hzM⟩)) := by
    intro x
    obtain ⟨y, rfl⟩ := f.surjective x
    obtain ⟨m, rfl⟩ := proj_surjective M y
    have hmz : proj M m * proj M ⟨z, hzM⟩ = proj M ⟨z, hzM⟩ * proj M m := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hzc m m.2
    calc f (proj M m) * f (proj M ⟨z, hzM⟩) = f (proj M m * proj M ⟨z, hzM⟩) := (map_mul f _ _).symm
      _ = f (proj M ⟨z, hzM⟩ * proj M m) := by rw [hmz]
      _ = f (proj M ⟨z, hzM⟩) * f (proj M m) := map_mul f _ _
  have e1 := gl_central _ (hinv hu hu2) hcen
  have e2 := gl_central _ (hinv hzM hz) hzcen
  have e3 : proj M ⟨u, hu⟩ = proj M ⟨z, hzM⟩ := f.injective (e1.trans e2.symm)
  have h4 : (⟨u, hu⟩ : ↥M)⁻¹ * ⟨z, hzM⟩ ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.mp e3
  have h5 : u⁻¹ * z ∈ oc M := mem_oc.mpr ⟨M.mul_mem (M.inv_mem hu) hzM, h4⟩
  have hcomm : u * z = z * u := hzc u hu
  have hu2' : u * u = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hu2
  have hz2' : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have h6 : (u⁻¹ * z) * (u⁻¹ * z) = 1 := by
    have hcu : Commute u⁻¹ z := (Commute.inv_left (show Commute u z from hcomm))
    calc (u⁻¹ * z) * (u⁻¹ * z) = u⁻¹ * u⁻¹ * (z * z) := by rw [mul_assoc, ← mul_assoc z u⁻¹, ← hcu.eq]; group
      _ = 1 := by rw [hz2', mul_one]; rw [← mul_inv_rev, hu2']; simp
  have := eq_one_of_mem_oc_of_sq h5 h6
  rw [inv_mul_eq_one] at this
  exact this

theorem exists_conj_of_involutions (f : Mbar M ≃* GL23) (hzM : z ∈ M) (hz : orderOf z = 2)
    (hzc : ∀ m ∈ M, m * z = z * m) {u v : G} (hu : u ∈ M) (hv : v ∈ M) (hu2 : orderOf u = 2)
    (hv2 : orderOf v = 2) (huz : u ≠ z) (hvz : v ≠ z) : ∃ m ∈ M, m * u * m⁻¹ = v := by
  obtain ⟨hui, huc⟩ := involution_cases f hzM hz hzc hu hu2 huz
  obtain ⟨hvi, hvc⟩ := involution_cases f hzM hz hzc hv hv2 hvz
  obtain ⟨x, hx⟩ := gl_conj _ _ hui huc hvi hvc
  obtain ⟨xb, rfl⟩ := f.surjective x
  obtain ⟨m, rfl⟩ := proj_surjective M xb
  have h1 : proj M (m * ⟨u, hu⟩ * m⁻¹) = proj M ⟨v, hv⟩ := by
    apply f.injective
    simp only [map_mul, map_inv]
    exact hx
  have h2 : (m * ⟨u, hu⟩ * m⁻¹)⁻¹ * ⟨v, hv⟩ ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.mp h1
  have hwM : (m : G) * u * (m : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem m.2 hu) (M.inv_mem m.2)
  have h3 : ((m : G) * u * (m : G)⁻¹)⁻¹ * v ∈ oc M := by
    refine mem_oc.mpr ⟨M.mul_mem (M.inv_mem hwM) hv, ?_⟩
    have e : (⟨((m : G) * u * (m : G)⁻¹)⁻¹ * v, M.mul_mem (M.inv_mem hwM) hv⟩ : ↥M) =
        (m * ⟨u, hu⟩ * m⁻¹)⁻¹ * ⟨v, hv⟩ := by
      apply Subtype.ext; simp
    rw [e]; exact h2
  have h4 : v * ((m : G) * u * (m : G)⁻¹)⁻¹ ∈ oc M := by
    have := conj_mem_oc hwM h3
    simpa [mul_assoc] using this
  have hw2 : orderOf ((m : G) * u * (m : G)⁻¹) = 2 := by rw [orderOf_conj_eq]; exact hu2
  obtain ⟨s, hs, hsw⟩ := exists_conj_of_involution_coset (odd_card_oc M) hw2 hv2 h4
  refine ⟨s * m, M.mul_mem (oc_le M hs) m.2, ?_⟩
  rw [← hsw]; group

theorem eq_of_central_sylow (f : Mbar M ≃* GL23) (hzM : z ∈ M) (hz : orderOf z = 2)
    (hzc : ∀ m ∈ M, m * z = z * m) (hcard : Nat.card M = 432) {R : Subgroup G} (hR : IsSylowIn M R)
    {y : G} (hy : y ∈ R) (hy2 : orderOf y = 2) (hyc : ∀ s ∈ R, s * y = y * s) : y = z := by
  by_contra hne
  have hyM : y ∈ M := hR.1 hy
  obtain ⟨hyi, hyn⟩ := involution_cases f hzM hz hzc hyM hy2 hne
  have hR16 : Nat.card R = 16 := by
    obtain ⟨-, k, m, hk, hm, hX⟩ := isSylowIn_iff_card.mp hR
    rw [hcard] at hX
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    have hk9 : k < 9 := by
      by_contra hk9
      have : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hk9)
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hm2; simp at hm2
        · exact h0
      nlinarith
    rw [hk]
    interval_cases k <;> omega
  have hbar : Nat.card (barImage M R) = 16 := by
    rw [← Nat.card_congr (mulEquivBarImage M hR.2.1 hR.1).toEquiv, hR16]
  set yb : Mbar M := proj M ⟨y, hyM⟩ with hyb
  have hle : barImage M R ≤ centralizer ({yb} : Set (Mbar M)) := by
    intro w hw
    obtain ⟨r, hr, rfl⟩ := (mem_barImage M).mp hw
    rw [mem_centralizer_singleton_iff, hyb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hyc r hr
  have hdvd : 16 ∣ Nat.card (centralizer ({yb} : Set (Mbar M))) := by
    rw [← hbar]; exact Subgroup.card_dvd_of_le hle
  have hcent : Nat.card (centralizer ({yb} : Set (Mbar M))) = 4 := by
    have hg := gl_card_centralizer _ hyi hyn
    rw [← Nat.card_eq_fintype_card] at hg
    rw [← hg]
    refine Nat.card_congr ?_
    refine
      { toFun := fun a => ⟨f a.1, ?_⟩
        invFun := fun x => ⟨f.symm x.1, ?_⟩
        left_inv := fun a => Subtype.ext (f.symm_apply_apply _)
        right_inv := fun x => Subtype.ext (f.apply_symm_apply _) }
    · have := mem_centralizer_singleton_iff.mp a.2
      rw [← map_mul, ← map_mul, this]
    · have h1 := x.2
      have h2 : f.symm x.1 * yb = yb * f.symm x.1 := by
        apply f.injective
        rw [map_mul, map_mul, f.apply_symm_apply]
        exact h1
      exact mem_centralizer_singleton_iff.mpr h2
  rw [hcent] at hdvd
  omega

end M

end CFSG.GH74.Uniqueness.SU.SU13
