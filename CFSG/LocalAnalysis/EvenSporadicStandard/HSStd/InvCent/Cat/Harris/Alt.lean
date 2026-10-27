module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.Setup
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harris.AltPerm
import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentM10Alt
import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harris

open Subgroup CFSG.ComponentClassification.CatFC
open scoped commutatorElement
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem alt_numeric_2880 {n r : ℕ} (hr : 1 ≤ r) (hrn : 2 * r ≤ n)
    (h : 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial = 2880) : n = 10 ∨ n = 11 := by
  generalize hm : n - 2 * r = m at h
  have hP : 0 < 2 ^ (r - 1) * r.factorial := Nat.mul_pos (by positivity) (Nat.factorial_pos r)
  have hr5 : r ≤ 5 := by
    by_contra hh
    have h1 : 720 ≤ r.factorial := by
      have := Nat.factorial_le (show 6 ≤ r by omega)
      norm_num [Nat.factorial] at this
      exact this
    have h2 : 32 ≤ 2 ^ (r - 1) := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 32 * 720 ≤ 2 ^ (r - 1) * r.factorial := Nat.mul_le_mul h2 h1
    have h4 : 32 * 720 ≤ 2 ^ (r - 1) * r.factorial * m.factorial :=
      h3.trans (Nat.le_mul_of_pos_right _ (Nat.factorial_pos m))
    omega
  have hm6 : m ≤ 6 := by
    by_contra hh
    have h1 : 5040 ≤ m.factorial := by
      have := Nat.factorial_le (show 7 ≤ m by omega)
      norm_num [Nat.factorial] at this
      exact this
    have h4 : 5040 ≤ 2 ^ (r - 1) * r.factorial * m.factorial :=
      h1.trans (Nat.le_mul_of_pos_left _ hP)
    omega
  interval_cases r <;> interval_cases m <;> norm_num [Nat.factorial] at h <;> omega

theorem card_fixed_cases {N : ℕ} (h360 : 360 ∣ N) (hdvd : N ∣ 2880) (h : 2880 ≤ 2 * N) :
    N = 1440 ∨ N = 2880 := by
  obtain ⟨m, rfl⟩ := h360
  have hm : m ≤ 8 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  interval_cases m <;> omega

variable {G : Type} [Group G] [Finite G] {S : Subgroup G} [S.Normal] {t : G}

theorem alt_arm_false (h : Cfg G S t)
    (ζ : ↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))
    {n : ℕ} (hn : 5 ≤ n) (θ : ↥S ≃* alternatingGroup (Fin n)) : False := by
  have hσ : orderOf (MulAut.conjNormal t : MulAut ↥S) = 2 := orderOf_conjNormal h.cent h.ord
  have hdvd := card_fixed_dvd (S := S) ζ
  have h360 := dvd_card_fixed h ζ
  have hFS : Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) ∣ Nat.card ↥S :=
    Subgroup.card_subgroup_dvd_card _
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hS_alt : Nat.card ↥S = n.factorial / 2 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  by_cases hn6 : n = 5 ∨ n = 6
  · rcases hn6 with rfl | rfl
    · have h60 : Nat.card ↥S = 60 := by
        rw [hS_alt]
        rfl
      have := Nat.le_of_dvd (by norm_num) (h360.trans hFS)
      omega
    · have h360S : Nat.card ↥S = 360 := by
        rw [hS_alt]
        rfl
      have hF : Nat.card ↥(fixedSubgroup (MulAut.conjNormal t : MulAut ↥S)) = Nat.card ↥S := by
        rw [h360S] at hFS ⊢
        exact Nat.dvd_antisymm hFS h360
      have htop := Subgroup.eq_top_of_card_eq _ hF
      have hσ1 : (MulAut.conjNormal t : MulAut ↥S) = 1 := by
        refine MulEquiv.ext fun x => ?_
        have hx : x ∈ fixedSubgroup (MulAut.conjNormal t : MulAut ↥S) := by
          rw [htop]
          exact Subgroup.mem_top x
        exact hx
      rw [hσ1, orderOf_one] at hσ
      omega
  · have hn7 : 7 ≤ n := by omega
    have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n
      (by omega) (by omega)
    let ι : G → Equiv.Perm (Fin n) := fun g =>
      (Equiv.ofBijective _ hbij).symm (MulAut.congr θ (MulAut.conjNormal g : MulAut ↥S))
    have hι : Function.Injective ι := by
      intro g g' hgg
      have h1 := (Equiv.ofBijective _ hbij).symm.injective hgg
      exact conjNormal_injective (S := S) h.cent ((MulAut.congr θ).injective h1)
    have hG : Nat.card G ≤ 2 * Nat.card ↥S := by
      have h1 := Nat.card_le_card_of_injective ι hι
      rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
        Fintype.card_fin] at h1
      have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      rw [hS_alt, Nat.mul_div_cancel' h2]
      exact h1
    have hle := card_centralizer_le_mul (S := S) t hG
    rw [card_centralizer_eq ζ, ← card_fixedSubgroup_eq t] at hle
    have hcases := card_fixed_cases h360 hdvd hle
    obtain ⟨r, hr1, hrn, hcard⟩ := card_fixedSubgroup_alt hn7 θ hσ
    rcases hcases with h1440 | h2880
    · exact alt_numeric_cases hr1 hrn (Or.inr (hcard.symm.trans h1440))
    · have hn1011 := alt_numeric_2880 hr1 hrn (hcard.symm.trans h2880)
      have hinf : Nat.card ↥(S ⊓ centralizer ({t} : Set G)) =
          Nat.card ↥(centralizer ({t} : Set G)) := by
        rw [← card_fixedSubgroup_eq t, h2880, card_centralizer_eq ζ]
      have hEq : S ⊓ centralizer ({t} : Set G) = centralizer ({t} : Set G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right hinf.ge
      have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
      have htS : t ∈ S := by
        have : t ∈ S ⊓ centralizer ({t} : Set G) := by
          rw [hEq]
          exact htC
        exact this.1
      let z : ↥S := ⟨t, htS⟩
      have hz2 : z * z = 1 := by
        apply Subtype.ext
        have := h.ord
        have h2 : t ^ 2 = 1 := by rw [← this]; exact pow_orderOf_eq_one t
        simpa [sq] using h2
      have hz1 : z ≠ 1 := by
        intro hz
        have : t = 1 := congrArg Subtype.val hz
        have h5 := h.ord
        rw [this, orderOf_one] at h5
        omega
      let s : Equiv.Perm (Fin n) := ((θ z : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
      have hs2 : s * s = 1 := by
        have : θ (z * z) = 1 := by rw [hz2, map_one]
        rw [map_mul] at this
        have h3 := congrArg Subtype.val this
        simpa using h3
      have hs1 : s ≠ 1 := by
        intro hs
        apply hz1
        apply θ.injective
        apply Subtype.ext
        simpa [s] using hs
      have hsign : Equiv.Perm.sign s = 1 :=
        Equiv.Perm.mem_alternatingGroup.1 (θ z).2
      obtain ⟨u, v, hu, hv, hus, hvs, huv⟩ := alt_involution_comm n hn1011 s hs2 hs1 hsign
      let u' : ↥S := θ.symm ⟨u, Equiv.Perm.mem_alternatingGroup.2 hu⟩
      let v' : ↥S := θ.symm ⟨v, Equiv.Perm.mem_alternatingGroup.2 hv⟩
      have hu'z : u' * z = z * u' := by
        apply θ.injective
        apply Subtype.ext
        simpa [u', s] using hus
      have hv'z : v' * z = z * v' := by
        apply θ.injective
        apply Subtype.ext
        simpa [v', s] using hvs
      have hcomm : u' * v' * u'⁻¹ * v'⁻¹ = z := by
        apply θ.injective
        apply Subtype.ext
        simpa [u', v', s] using huv
      have hu'C : (u' : G) ∈ centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hu'z
      have hv'C : (v' : G) ∈ centralizer ({t} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val hv'z
      have hmem := commutator_mem_derived hu'C hv'C
      have heq : (u' : G) * v' * (u' : G)⁻¹ * (v' : G)⁻¹ = t := by
        have := congrArg Subtype.val hcomm
        simpa using this
      rw [heq] at hmem
      exact t_not_mem_derived h ζ hmem

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harris
