module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Block
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Q8Lin
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OddCoreDim2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
import CFSG.GH74.Uniqueness.Bender.Frame311

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_isPGroup_two_oGroup_of_finrank_le_two (hQ : Q.Nondegenerate)
    (h : Module.finrank (ZMod 3) V ≤ 2) : IsPGroup 2 (OGroup Q) := by
  rcases Nat.lt_or_ge (Module.finrank (ZMod 3) V) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Module.finrank (ZMod 3) V) 1 with h0 | h1
    · have h0' : Module.finrank (ZMod 3) V = 0 := by omega
      have h00 : ∀ x : V, x = 0 := finrank_zero_iff_forall_zero.mp h0'
      haveI : Subsingleton (OGroup Q) :=
        ⟨fun _ _ => Subtype.ext (LinearEquiv.ext fun x => (h00 _).trans (h00 _).symm)⟩
      exact fun g => ⟨0, Subsingleton.elim _ _⟩
    · exact IsPGroup.of_card (n := 1) (by rw [natCard_oGroup_one hQ (by omega)]; rfl)
  · exact isPGroup_two_oGroup_of_finrank_two hQ (by omega)

theorem fj_odd_block_fix (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    (hU : Module.finrank (ZMod 3) (commSp s) ≤ 2) {g : OGroup Q}
    (hg : g ∈ Subgroup.centralizer ({s} : Set (OGroup Q))) (hodd : Odd (orderOf g)) :
    ∃ p ∈ omegaGroup (nondegenerate_restrict_fixSp hQ hs), blockHom hs (p, 1) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← range_blockHom hQ hs] at hg
  obtain ⟨⟨p, c⟩, rfl⟩ := MonoidHom.mem_range.mp hg
  have hord : orderOf (p, c) = orderOf (blockHom hs (p, c)) :=
    (orderOf_injective (blockHom hs) (blockHom_injective hs) _).symm
  have hlcm : orderOf (p, c) = Nat.lcm (orderOf p) (orderOf c) := Prod.orderOf (p, c)
  have hoddpc : Odd (orderOf (p, c)) := hord ▸ hodd
  have hcodd : Odd (orderOf c) :=
    hoddpc.of_dvd_nat (hlcm ▸ Nat.dvd_lcm_right _ _)
  have hpodd : Odd (orderOf p) :=
    hoddpc.of_dvd_nat (hlcm ▸ Nat.dvd_lcm_left _ _)
  have hP := fj_isPGroup_two_oGroup_of_finrank_le_two
    (nondegenerate_restrict_commSp hQ hs) hU
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) c
  have hk0 : k = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf c := hk ▸ dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr h2)
  have hc1 : c = 1 := by
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  subst hc1
  exact ⟨p, CFSG.GH74.Uniqueness.Bender.mem_of_mul_self_mem_of_odd hpodd
    (mul_self_mem_omegaGroup (nondegenerate_restrict_fixSp hQ hs) p), rfl⟩

theorem fj_block_quaternion (hQ : Q.Nondegenerate) {s : OGroup Q} (hs : s * s = 1)
    {q r : OGroup Q} (hq : q ∈ Subgroup.centralizer ({s} : Set (OGroup Q)))
    (hr : r ∈ Subgroup.centralizer ({s} : Set (OGroup Q)))
    (hqr : q * q = r * r) (hyy : (q * q) * (q * q) = 1) (hrq : r * q = q⁻¹ * r) :
    ∃ (a : OGroup (Q.restrict (fixSp s))) (c : OGroup (Q.restrict (commSp s))),
      blockHom hs (a, c) = q * q ∧ a * a = 1 ∧ c * c = 1 ∧ 4 ∣ invDim a ∧ 4 ∣ invDim c := by
  rw [← range_blockHom hQ hs] at hq hr
  obtain ⟨⟨q₁, q₂⟩, rfl⟩ := MonoidHom.mem_range.mp hq
  obtain ⟨⟨r₁, r₂⟩, rfl⟩ := MonoidHom.mem_range.mp hr
  have hinj := blockHom_injective hs
  have hqr' : (q₁, q₂) * (q₁, q₂) = (r₁, r₂) * (r₁, r₂) := by
    apply hinj
    rw [map_mul, map_mul]
    exact hqr
  have hyy' : (q₁, q₂) * (q₁, q₂) * ((q₁, q₂) * (q₁, q₂)) = 1 := by
    apply hinj
    rw [map_mul, map_mul, map_one]
    exact hyy
  have hrq' : (r₁, r₂) * (q₁, q₂) = (q₁, q₂)⁻¹ * (r₁, r₂) := by
    apply hinj
    rw [map_mul, map_mul, map_inv]
    exact hrq
  have hq1 := Prod.ext_iff.mp hqr'
  have hy1 := Prod.ext_iff.mp hyy'
  have hr1 := Prod.ext_iff.mp hrq'
  have h1 := four_dvd_invDim_of_quaternion (nondegenerate_restrict_fixSp hQ hs)
    hq1.1 hy1.1 hr1.1
  have h2 := four_dvd_invDim_of_quaternion (nondegenerate_restrict_commSp hQ hs)
    hq1.2 hy1.2 hr1.2
  exact ⟨q₁ * q₁, q₂ * q₂, map_mul (blockHom hs) (q₁, q₂) (q₁, q₂), hy1.1, hy1.2, h1.1,
    h2.1⟩

theorem fj_pi_mul_blockHom_piOrth_one {s : OGroup Q} (hs : s * s = 1) :
    piOrth Q * blockHom hs (piOrth (Q.restrict (fixSp s)), 1) = s := by
  have h : blockHom hs (piOrth (Q.restrict (fixSp s)), piOrth (Q.restrict (commSp s))) *
      blockHom hs (piOrth (Q.restrict (fixSp s)), 1) =
      blockHom hs (1, piOrth (Q.restrict (commSp s))) := by
    rw [← map_mul]
    congr 1
    ext <;> simp [piOrth_mul_self]
  rwa [blockHom_piOrth_piOrth hs, blockHom_one_piOrth hs] at h

theorem fj_block_cases (hn : Module.finrank (ZMod 3) V ≤ 8) {s : OGroup Q} (hs : s * s = 1)
    {y : OGroup Q} {a : OGroup (Q.restrict (fixSp s))} {c : OGroup (Q.restrict (commSp s))}
    (hy : blockHom hs (a, c) = y) (haa : a * a = 1) (hcc : c * c = 1)
    (ha4 : 4 ∣ invDim a) (hc4 : 4 ∣ invDim c)
    (hy1 : y ≠ 1) (hyπ : y ≠ piOrth Q) (hys : y ≠ s) (hysπ : s ≠ piOrth Q * y) :
    (c = 1 ∧ 5 ≤ Module.finrank (ZMod 3) (fixSp s)) ∨
      (a = 1 ∧ 5 ≤ Module.finrank (ZMod 3) (commSp s)) := by
  have hsum := finrank_fixSp_add_finrank_commSp (Q := Q) s
  have hale := invDim_le a
  have hcle := invDim_le c
  have ha0 := invDim_eq_zero_iff haa
  have hc0 := invDim_eq_zero_iff hcc
  have haf := invDim_eq_finrank_iff haa
  have hcf := invDim_eq_finrank_iff hcc
  by_cases ha1 : a = 1
  · right
    refine ⟨ha1, ?_⟩
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hy1 (by rw [← hy, ha1]; exact map_one (blockHom hs))
    have hcπ : c ≠ piOrth (Q.restrict (commSp s)) := by
      rintro rfl
      exact hys (by rw [← hy, ha1, blockHom_one_piOrth hs])
    have h0 : invDim c ≠ 0 := fun h => hc1 (hc0.mp h)
    have hf : invDim c ≠ Module.finrank (ZMod 3) (commSp s) := fun h => hcπ (hcf.mp h)
    omega
  · have hane : invDim a ≠ 0 := fun h => ha1 (ha0.mp h)
    by_cases hc1 : c = 1
    · left
      refine ⟨hc1, ?_⟩
      have haπ : a ≠ piOrth (Q.restrict (fixSp s)) := by
        rintro rfl
        exact hysπ (by rw [← hy, hc1, fj_pi_mul_blockHom_piOrth_one hs])
      have hf : invDim a ≠ Module.finrank (ZMod 3) (fixSp s) := fun h => haπ (haf.mp h)
      omega
    · exfalso
      have hcne : invDim c ≠ 0 := fun h => hc1 (hc0.mp h)
      have haeq : invDim a = Module.finrank (ZMod 3) (fixSp s) := by omega
      have hceq : invDim c = Module.finrank (ZMod 3) (commSp s) := by omega
      apply hyπ
      rw [← hy, haf.mp haeq, hcf.mp hceq, blockHom_piOrth_piOrth hs]

end CFSG.OddStandard.SmallF3.Omega
