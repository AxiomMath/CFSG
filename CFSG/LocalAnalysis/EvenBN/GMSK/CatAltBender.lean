module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootGeneric
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Quasithin.SteinbergCBAlternatingAut
import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.AltBender

open Equiv Subgroup CFSG.Blueprint

theorem three_pow_dvd_factorial (n : ℕ) : 3 ^ n ∣ (3 * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = (3 * n + 2) + 1 by ring, Nat.factorial_succ,
      show 3 * n + 2 = (3 * n + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ, pow_succ]
    have h3 : 3 ∣ 3 * n + 2 + 1 := ⟨n + 1, by ring⟩
    calc 3 ^ n * 3 ∣ (3 * n).factorial * (3 * n + 2 + 1) := Nat.mul_dvd_mul ih h3
      _ ∣ (3 * n + 1 + 1 + 1) * ((3 * n + 1 + 1) * ((3 * n + 1) * (3 * n).factorial)) :=
        ⟨(3 * n + 1 + 1) * (3 * n + 1), by ring⟩

theorem four_add_two_mul_lt_three_pow {v : ℕ} (hv : 2 ≤ v) : 4 + 2 * v < 3 ^ v := by
  induction v, hv using Nat.le_induction with
  | base => norm_num
  | succ v hv ih =>
    rw [pow_succ]
    omega

theorem unitaryThree_dvd_sq (q : ℕ) :
    ((q ^ 3 + 1) * (q ^ 2 - 1)) ∣ (q ^ 6 - 1) ^ 2 := by
  have h1 : q ^ 3 + 1 ∣ q ^ 6 - 1 := by
    have : q ^ 6 - 1 = (q ^ 3 + 1) * (q ^ 3 - 1) := by
      rw [← Nat.sq_sub_sq, one_pow, ← pow_mul]
    rw [this]
    exact dvd_mul_right _ _
  have h2 : q ^ 2 - 1 ∣ q ^ 6 - 1 := Nat.pow_sub_one_dvd_pow_sub_one q (by norm_num)
  rw [show (q ^ 6 - 1) ^ 2 = (q ^ 6 - 1) * (q ^ 6 - 1) from sq _]
  exact Nat.mul_dvd_mul h1 h2

theorem padicValNat_three_sixtyFour_pow_sub_one {n : ℕ} (hn : n ≠ 0) :
    padicValNat 3 (64 ^ n - 1) = 2 + padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := padicValNat.pow_sub_pow (p := 3) (x := 64) (y := 1) (by decide) (by norm_num)
    (by norm_num) (by norm_num) hn
  rw [one_pow] at h
  rw [h]
  congr 1
  rw [show (64 - 1 : ℕ) = 3 ^ 2 * 7 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem le_of_three_pow_dvd_card_PSU3 {X : Type} [Group X] {n j : ℕ}
    (h : LieModel X .PSU 3 2 n) (hj : 3 ^ j ∣ Nat.card X) :
    j ≤ 4 + 2 * padicValNat 3 n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := two_le_of_lieModel_PSU3 h
  have hN := card_mul_gcd_of_lieModel_PSU3 h
  set q := 2 ^ n with hq
  have hcop : Nat.Coprime (3 ^ j) (q ^ 3) := by
    apply Nat.Coprime.pow
    rw [hq, Nat.coprime_comm]
    exact Nat.Coprime.pow_left _ (by norm_num)
  have h1 : 3 ^ j ∣ q ^ 3 * ((q ^ 3 + 1) * (q ^ 2 - 1)) := by
    rw [← mul_assoc, ← hN]
    exact dvd_mul_of_dvd_left hj _
  have h2 : 3 ^ j ∣ (q ^ 6 - 1) ^ 2 :=
    (hcop.dvd_of_dvd_mul_left h1).trans (unitaryThree_dvd_sq q)
  have hq6 : q ^ 6 = 64 ^ n := by
    rw [hq, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hpos : q ^ 6 - 1 ≠ 0 := by
    have : 1 < q ^ 6 := by
      rw [hq6]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have h3 := (padicValNat_dvd_iff_le (pow_ne_zero 2 hpos)).1 h2
  rw [padicValNat.pow, hq6, padicValNat_three_sixtyFour_pow_sub_one (by omega)] at h3
  omega

theorem card_ne_factorial_div_two_of_lieModel_PSU3 {X : Type} [Group X] {n : ℕ}
    (h : LieModel X .PSU 3 2 n) {k : ℕ} (hk : 5 ≤ k) : Nat.card X ≠ k.factorial / 2 := by
  intro hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn := two_le_of_lieModel_PSU3 h
  have : Finite X := finite_of_lieModel_PSU3 h
  have hX0 : Nat.card X ≠ 0 := Nat.card_pos.ne'
  have h2k : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hkX : k.factorial = 2 * Nat.card X := by
    rw [hX]
    exact (Nat.mul_div_cancel' h2k).symm
  have hv2 : padicValNat 2 k.factorial = 3 * n + 1 := by
    rw [hkX, padicValNat.mul (by norm_num) hX0, padicValNat.self (by norm_num),
      ← Nat.factorization_def _ Nat.prime_two, factorization_two_card_of_lieModel_PSU3 h]
    ring
  have hk2 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := 2) (n := k) (by omega)
  rw [hv2] at hk2
  norm_num at hk2
  have h3 : 3 ^ n ∣ Nat.card X := by
    have h1 : 3 ^ n ∣ 2 * Nat.card X :=
      hkX ▸ (three_pow_dvd_factorial n).trans (Nat.factorial_dvd_factorial (by omega))
    exact (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h1
  have hle := le_of_three_pow_dvd_card_PSU3 h h3
  have hv : padicValNat 3 n ≤ 1 := by
    by_contra hv
    have h4 := four_add_two_mul_lt_three_pow (show 2 ≤ padicValNat 3 n by omega)
    have h5 : 3 ^ padicValNat 3 n ≤ n := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    omega
  have hn6 : n ≤ 6 := by omega
  have hcard := card_of_lieModel_PSU3 h
  have hfac : (3 * n + 2).factorial ≤ k.factorial := Nat.factorial_le (by omega)
  interval_cases n
  · norm_num at hcard
    rw [hcard] at hkX
    by_cases hk8 : k = 8
    · subst hk8
      norm_num [Nat.factorial] at hkX
    · have := Nat.factorial_le (show 9 ≤ k by omega)
      rw [hkX] at this
      norm_num [Nat.factorial] at this
  all_goals
    norm_num at hcard
    rw [hcard] at hkX
    rw [hkX] at hfac
    norm_num [Nat.factorial] at hfac

theorem three_dvd_factorial_div_two {k : ℕ} (hk : 3 ≤ k) : 3 ∣ k.factorial / 2 :=
  Nat.dvd_div_of_mul_dvd ((show 3 * 2 ∣ Nat.factorial 3 by decide).trans
    (Nat.factorial_dvd_factorial hk))

theorem not_two_pow_six_dvd_card_of_alt_six {D : Type*} [Group D]
    (η : D ≃* alternatingGroup (Fin 6)) (S : Subgroup D) : ¬ 2 ^ 6 ∣ Nat.card S := by
  intro h
  have hD : Nat.card D = 360 := by
    rw [Nat.card_congr η.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have := h.trans (hD ▸ Subgroup.card_subgroup_dvd_card S)
  norm_num at this

theorem mul_comm_of_conj_eq {G : Type*} [Group G] {g x : G} (h : g * x * g⁻¹ = x) :
    g * x = x * g := by
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [h]

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification in
theorem exists_card_eq_factorial_div_two {m : ℕ} (hm : 5 ≤ m) (hm6 : m ≠ 6) {D : Type*}
    [Group D] [Finite D] (η : D ≃* alternatingGroup (Fin m)) (α : MulAut D) (hα : orderOf α = 2)
    (S : Subgroup D) (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSn : (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    ∃ k : ℕ, 5 ≤ k ∧ Nat.card S = k.factorial / 2 := by
  have hm' : m = 5 ∨ 7 ≤ m := by omega
  have hmemC : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ α d = d := fun d => Iff.rfl
  let β : MulAut (alternatingGroup (Fin m)) := η.symm.trans (α.trans η)
  have hβ : ∀ g, β g = η (α (η.symm g)) := fun g => rfl
  obtain ⟨σ, hσ⟩ := CFSG.Milestones.alternating_automorphism_permutation hm' β
  have hσ' : ∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = σ * g * σ⁻¹ :=
    fun g => hσ g
  have hinj := Quasithin.SteinbergCB.conjPerm_injective (n := m) (by omega)
  have hconj : ∀ τ : Perm (Fin m),
      (∀ g : alternatingGroup (Fin m), (η (α (η.symm g)) : Perm (Fin m)) = τ * g * τ⁻¹) →
        Quasithin.SteinbergCB.conjPerm m τ = β := fun τ hτ =>
    MulEquiv.ext fun g => Subtype.ext (by rw [Quasithin.SteinbergCB.conjPerm_apply, hβ, hτ])
  have hα2 : ∀ d, α (α d) = d := by
    have h : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    intro d
    have := congrArg (fun γ : MulAut D => γ d) h
    simpa [sq] using this
  have hσσ : σ * σ = 1 := by
    apply hinj
    rw [map_mul, hconj σ hσ', map_one]
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.mul_apply, hβ, hβ, MulEquiv.symm_apply_apply, hα2, MulEquiv.apply_symm_apply,
      MulAut.one_apply]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hβ1 : β = 1 := by rw [← hconj σ hσ', h1, map_one]
    have hα1 : α ≠ 1 := fun h => by
      rw [h, orderOf_one] at hα
      omega
    apply hα1
    refine MulEquiv.ext fun d => ?_
    have := congrArg (fun γ : MulAut (alternatingGroup (Fin m)) => γ (η d)) hβ1
    simp only [hβ, MulEquiv.symm_apply_apply, MulAut.one_apply] at this
    exact η.injective this
  have hσ2 : orderOf σ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq, hσσ]) hσ1
  let ι : D →* Perm (Fin m) :=
    (alternatingGroup (Fin m)).subtype.comp (η : D →* alternatingGroup (Fin m))
  have hι : Function.Injective ι := (alternatingGroup (Fin m)).subtype_injective.comp η.injective
  have hιA : ∀ d, ι d ∈ alternatingGroup (Fin m) := fun d => (η d).2
  have hfix : ∀ d, d ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) ↔ σ * ι d = ι d * σ := by
    intro d
    rw [hmemC]
    have h := hσ' (η d)
    rw [MulEquiv.symm_apply_apply] at h
    constructor
    · intro hd
      rw [hd] at h
      exact mul_comm_of_conj_eq h.symm
    · intro hd
      apply η.injective
      apply Subtype.ext
      rw [h]
      change σ * ι d * σ⁻¹ = ι d
      rw [hd, mul_inv_cancel_right]
  set S' := S.map ι with hS'def
  set M := alternatingGroup (Fin m) ⊓ centralizer ({σ} : Set (Perm (Fin m))) with hMdef
  have hS'M : S' ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hιA s, mem_centralizer_singleton_iff.2 ((hfix s).1 (hSα hs)).symm⟩
  have hS'n : (S'.subgroupOf M).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    have hgA : (g : Perm (Fin m)) ∈ alternatingGroup (Fin m) := (mem_inf.1 g.2).1
    have hgC : (g : Perm (Fin m)) ∈ centralizer ({σ} : Set (Perm (Fin m))) := (mem_inf.1 g.2).2
    have hcg : ι (η.symm ⟨g, hgA⟩) = g := by
      change ((η (η.symm ⟨g, hgA⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = g
      rw [MulEquiv.apply_symm_apply]
    have hcC : η.symm ⟨g, hgA⟩ ∈ α.toMonoidHom.eqLocus (MonoidHom.id D) :=
      (hfix _).2 (by rw [hcg]; exact (mem_centralizer_singleton_iff.1 hgC).symm)
    have hmem := hSn.conj_mem ⟨s, hSα hs⟩ (mem_subgroupOf.2 hs) ⟨_, hcC⟩
    rw [mem_subgroupOf] at hmem
    refine ⟨_, hmem, ?_⟩
    change ι (η.symm ⟨g, hgA⟩ * s * (η.symm ⟨g, hgA⟩)⁻¹) =
      (g : Perm (Fin m)) * x * (g : Perm (Fin m))⁻¹
    rw [map_mul, map_mul, map_inv, hcg, hsx]
  have hMN : (M.subgroupOf (centralizer ({σ} : Set (Perm (Fin m))))).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨?_, ?_⟩
    · exact (inferInstance : (alternatingGroup (Fin m)).Normal).conj_mem _ hxA _
    · exact mul_mem (mul_mem g.2 hxC) (inv_mem g.2)
  have hS'q : CFSG.Assembly.IsQuasisimple S' := by
    have hSq := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1
    rw [AssemblyBPredicates.isQuasisimple_iff_native]
    exact (isQuasisimple_congr (S.equivMapOfInjective ι hι)).1 hSq
  have hcomp : CFSG.Assembly.IsComponentOf S'
      (⊤ ⊓ normalizer ((zpowers σ : Subgroup (Perm (Fin m))) : Set (Perm (Fin m)))) := by
    rw [top_inf_eq, ← centralizer_singleton_eq_normalizer_zpowers hσ2]
    exact ⟨hS'M.trans inf_le_right, CFSG.Assembly.IsSubnormal.step hS'M hS'n
      (CFSG.Assembly.IsSubnormal.step inf_le_right hMN (CFSG.Assembly.IsSubnormal.refl _)),
      hS'q⟩
  obtain ⟨hF5, hS'eq⟩ := ordinary_permutation_local_component_fixed_support (T := ⊤) le_top
    Nat.prime_two le_top (isPGroup_zpowers_of_orderOf_eq_two hσ2) hcomp
  classical
  have : Nontrivial (MulAction.fixedPoints (zpowers σ) (Fin m)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  refine ⟨_, hF5, ?_⟩
  rw [Nat.card_congr (S.equivMapOfInjective ι hι).toEquiv, ← hS'def, hS'eq,
    Subgroup.card_map_of_injective Perm.ofSubtype_injective, nat_card_alternatingGroup]

end CFSG.LocalAnalysis.EvenBN.GMSK.AltBender

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint AltBender

theorem fixedRootSelectorOf_alternating_U3 :
    FixedRootSelectorOf T_U3 SurvU3 fun D _ =>
      ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)) := by
  intro D _ _ _ ⟨m, hm, ⟨η⟩⟩ n α S d
  exfalso
  obtain ⟨hn, hU⟩ := d.type
  by_cases hm6 : m = 6
  · subst hm6
    refine not_two_pow_six_dvd_card_of_alt_six η S ?_
    have h := Nat.ordProj_dvd (Nat.card S) 2
    rw [factorization_two_card_of_lieModel_PSU3 hU] at h
    exact (pow_dvd_pow 2 (by omega)).trans h
  · obtain ⟨k, hk, hcard⟩ := exists_card_eq_factorial_div_two hm hm6 η α d.orderOf_eq S
      d.le_fixed d.normal (isSimpleGroup_of_lieModel_PSU3 hU) (exists_mul_ne_of_lieModel_PSU3 hU)
    exact card_ne_factorial_div_two_of_lieModel_PSU3 hU hk hcard

theorem fixedRootSelectorOf_alternating_Sz :
    FixedRootSelectorOf T_Sz SurvSz fun D _ =>
      ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)) := by
  intro D _ _ _ ⟨m, hm, ⟨η⟩⟩ n α S d
  exfalso
  have hS : LieModel S .twistedB2 0 2 n := d.type
  by_cases hm6 : m = 6
  · subst hm6
    refine not_two_pow_six_dvd_card_of_alt_six η S ?_
    have h := Nat.ordProj_dvd (Nat.card S) 2
    rw [factorization_two_card_of_lieModel_twistedB2 hS] at h
    exact (pow_dvd_pow 2 (by have := three_le_of_lieModel_twistedB2 hS; omega)).trans h
  · obtain ⟨k, hk, hcard⟩ := exists_card_eq_factorial_div_two hm hm6 η α d.orderOf_eq S
      d.le_fixed d.normal (isSimpleGroup_of_lieModel_twistedB2 hS)
      (exists_mul_ne_of_lieModel_twistedB2 hS)
    exact not_three_dvd_card_of_lieModel_twistedB2 hS
      (hcard ▸ three_dvd_factorial_div_two (by omega))

end CFSG.LocalAnalysis.EvenBN.GMSK
