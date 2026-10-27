module

public import CFSG.LocalAnalysis.SectionRank.OddCover.AltForm
public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {K : Type*} [Field K]

@[expose] def slU (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [det_fin_two]⟩

@[expose] def slD (a : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩

theorem coe_slU (t : K) : ((slU t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, t; 0, 1] :=
  rfl

theorem coe_slD (a : Kˣ) : ((slD a : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] :=
  rfl

theorem slU_add (s t : K) : slU (s + t) = slU s * slU t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slU, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem slU_zero : slU (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_slU]

theorem slD_mul_slU (a : Kˣ) (t : K) : slD a * slU t = slU ((a : K) ^ 2 * t) * slD a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_slU, coe_slD, Matrix.mul_apply, Fin.sum_univ_two, sq, mul_assoc]
  field_simp

theorem eq_zero_of_slU_mem_center {t : K}
    (h : slU t ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K)) : t = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have h01 := congrFun (congrFun hr 0) 1
  simpa [coe_slU, Matrix.scalar_apply, Matrix.diagonal_apply_ne] using h01.symm

@[expose] noncomputable def pslMk : SpecialLinearGroup (Fin 2) K →*
    ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.mk' _

@[expose] noncomputable def pslU : Multiplicative K →* ProjectiveSpecialLinearGroup (Fin 2) K where
  toFun t := pslMk (slU t.toAdd)
  map_one' := by rw [toAdd_one, slU_zero, map_one]
  map_mul' s t := by rw [toAdd_mul, slU_add, map_mul]

theorem pslU_apply (t : Multiplicative K) : pslU t = pslMk (slU t.toAdd) :=
  rfl

theorem pslU_injective : Function.Injective (pslU (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro t ht
  rw [MonoidHom.mem_ker, pslU_apply, pslMk, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at ht
  have h0 := eq_zero_of_slU_mem_center ht
  rw [Subgroup.mem_bot, ← ofAdd_toAdd t, h0, ofAdd_zero]

theorem pslD_conj_pslU (a : Kˣ) (t : K) :
    pslMk (slD a) * pslU (Multiplicative.ofAdd t) * (pslMk (slD a))⁻¹ =
      pslU (Multiplicative.ofAdd ((a : K) ^ 2 * t)) := by
  rw [pslU_apply, pslU_apply, toAdd_ofAdd, toAdd_ofAdd, ← map_mul, slD_mul_slU, map_mul,
    mul_inv_cancel_right]

end CFSG.SectionRank.OddCover

namespace CFSG.SectionRank.OddCover

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

variable {K : Type} [Field K] [Finite K]

theorem one_le_of_card_eq_pow {p f : ℕ} (hK : Nat.card K = p ^ f) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · have := Finite.one_lt_card (α := K)
    rw [hK, pow_zero] at this
    exact absurd this (lt_irrefl 1)
  · exact hf

theorem psl_two_cofactor {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    2 * (((p ^ f) ^ 2 - 1) / 2) = (p ^ f) ^ 2 - 1 ∧ ¬ p ∣ ((p ^ f) ^ 2 - 1) / 2 := by
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨k, hk⟩ := hodd
  have hq : (p ^ f) ^ 2 - 1 = 2 * (2 * k * k + 2 * k) := by
    rw [hk]
    have : (2 * k + 1) ^ 2 = 2 * (2 * k * k + 2 * k) + 1 := by ring
    omega
  refine ⟨by rw [hq, Nat.mul_div_cancel_left _ two_pos], fun hdvd => ?_⟩
  rw [hq, Nat.mul_div_cancel_left _ two_pos] at hdvd
  have h1 : p ∣ (p ^ f) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
  have h2 : p ∣ (p ^ f) ^ 2 - 1 := by rw [hq]; exact dvd_mul_of_dvd_right hdvd 2
  have h3 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos f)
  have := Nat.dvd_sub h1 h2
  rw [Nat.sub_sub_self h3] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem card_psl_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K) = p ^ f * (((p ^ f) ^ 2 - 1) / 2) := by
  have hf := one_le_of_card_eq_pow hK
  rw [CFSG.GorensteinWalter.psl2_card_formula K ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩, hK]
  obtain ⟨h2, -⟩ := psl_two_cofactor hp hp2 hf
  exact Nat.mul_div_assoc _ ⟨_, h2.symm⟩

theorem factorization_card_psl_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    (Nat.card (ProjectiveSpecialLinearGroup (Fin 2) K)).factorization p = f := by
  have hf := one_le_of_card_eq_pow hK
  obtain ⟨-, hndvd⟩ := psl_two_cofactor hp hp2 hf
  have hm0 : ((p ^ f) ^ 2 - 1) / 2 ≠ 0 := fun h => hndvd (h ▸ dvd_zero p)
  rw [card_psl_two hp hp2 hK, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0,
    Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]

omit [Finite K] in
theorem card_range_pslU : Nat.card (pslU (K := K)).range = Nat.card K := by
  rw [← Nat.card_congr (MonoidHom.ofInjective pslU_injective).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

@[expose] noncomputable def pslUSylow {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : Sylow p (ProjectiveSpecialLinearGroup (Fin 2) K) :=
  Sylow.ofCard (pslU (K := K)).range (by
    rw [card_range_pslU, hK, factorization_card_psl_two hp.out hp2 hK])

theorem coe_pslUSylow {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    (pslUSylow hp2 hK : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) K)) =
      (pslU (K := K)).range :=
  rfl

omit [Finite K] in
theorem multiplicative_pow_char_eq_one {p : ℕ} [CharP K p] (t : Multiplicative K) :
    t ^ p = 1 := by
  change Multiplicative.ofAdd (p • t.toAdd) = Multiplicative.ofAdd 0
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

omit [Finite K] in
theorem isElemAbelian_range_pslU {p : ℕ} [CharP K p] :
    IsElemAbelian p (pslU (K := K)).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨s, hs⟩ := a.2
    obtain ⟨t, ht⟩ := b.2
    apply Subtype.ext
    change (a : ProjectiveSpecialLinearGroup (Fin 2) K) * b = b * a
    rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨t, rfl⟩ := hy
    rw [← map_pow, multiplicative_pow_char_eq_one, map_one]

theorem psl_two_sylow_isCyclic {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hrp : r ≠ p)
    (R : Sylow r (ProjectiveSpecialLinearGroup (Fin 2) K)) :
    IsCyclic (R : Subgroup (ProjectiveSpecialLinearGroup (Fin 2) K)) := by
  have hr : r.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have hf := one_le_of_card_eq_pow hK
  by_cases h7 : 7 ≤ Nat.card K
  · refine CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK h7 r hr2 ?_ R
    rw [hK]
    exact Nat.Coprime.pow_right f ((Nat.coprime_primes hr hp).2 hrp)
  ·
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hq : p ^ f = p := by
      by_contra hne
      have h2 : 2 ≤ f := by
        by_contra h
        exact hne (by rw [show f = 1 by omega, pow_one])
      have : p ^ 2 ≤ p ^ f := Nat.pow_le_pow_right hp.pos h2
      have : 9 ≤ p ^ 2 := by nlinarith
      omega
    have hpq : p < 7 := by omega
    have hp35 : p = 3 ∨ p = 5 := by
      interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; norm_num at hp)
    refine CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd ?_ R
    rw [card_psl_two hp hp2 hK, hq]
    intro hdvd
    have hr3 : 3 ≤ r := by have := hr.two_le; omega
    rcases hp35 with rfl | rfl
    · norm_num at hdvd
      have hle : r ^ 2 ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
      have hr4 : r ≤ 3 := by nlinarith
      omega
    · norm_num at hdvd
      have hle : r ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
      have hr7 : r ≤ 7 := by nlinarith
      interval_cases r <;> omega

section Cover

variable {E : Type*} [Group E] [Finite E]

theorem sylow_two_eq_bot_of_odd {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G))
    [Fact (Nat.Prime 2)] (P : Sylow 2 G) : (P : Subgroup G) = ⊥ := by
  have h := Sylow.card_eq_multiplicity P
  rw [Nat.factorization_eq_zero_of_not_dvd (by rwa [← even_iff_two_dvd, Nat.not_even_iff_odd]),
    pow_zero] at h
  exact Subgroup.card_eq_one.1 h

theorem eq_three_of_pow_eq_nine {p f : ℕ} (hp : p.Prime) (h9 : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf : f ≠ 0 := by rintro rfl; simp at h9
  have hp3 : p = 3 := by
    have : p ∣ 3 ^ 2 := by rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]; exact dvd_pow_self p hf
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow this)
  subst hp3
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (h9.trans (by norm_num : (9 : ℕ) = 3 ^ 2))⟩

variable [Group.IsPerfect E]

theorem psl_two_sylow_kernel_eq_bot {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h9 : p ^ f ≠ 9) (π : E →* ProjectiveSpecialLinearGroup (Fin 2) K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (Cp : Sylow p π.ker) :
    (Cp : Subgroup π.ker) = ⊥ := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ p (pslUSylow hp2 hK)
  have hmap : (P : Subgroup E).map π = (pslU (K := K)).range := by
    rw [← Sylow.coe_mapSurjective hπ P, hP, coe_pslUSylow]
  have hlift : ∀ t : K, ∃ y ∈ (P : Subgroup E), π y = pslU (Multiplicative.ofAdd t) := by
    intro t
    have hmem : pslU (Multiplicative.ofAdd t) ∈ (P : Subgroup E).map π := hmap ▸ ⟨_, rfl⟩
    exact Subgroup.mem_map.1 hmem
  choose x hxP hx using hlift
  have hcen : ∀ e : E, π e = 1 → e ∈ Subgroup.center E := fun e he => hC he
  have hcomm : ∀ s t : K, π ⁅x s, x t⁆ = 1 := by
    intro s t
    rw [map_commutatorElement, hx, hx, commutatorElement_eq_one_iff_mul_comm]
    have h := congrArg pslU (mul_comm (Multiplicative.ofAdd s) (Multiplicative.ofAdd t))
    rwa [map_mul, map_mul] at h
  let b : K → K → Additive (Subgroup.center E) := fun s t =>
    Additive.ofMul ⟨⁅x s, x t⁆, hcen _ (hcomm s t)⟩
  have hb : ∀ s t, ((Additive.toMul (b s t) : Subgroup.center E) : E) = ⁅x s, x t⁆ :=
    fun _ _ => rfl
  have hbext : ∀ u v : Additive (Subgroup.center E),
      ((Additive.toMul u : Subgroup.center E) : E) = (Additive.toMul v : Subgroup.center E) →
        u = v := fun u v h => Additive.toMul.injective (Subtype.ext h)
  have hxadd : ∀ s s' : K, ∃ c ∈ Subgroup.center E, x (s + s') = x s * x s' * c := by
    intro s s'
    refine ⟨(x s * x s')⁻¹ * x (s + s'), hcen _ ?_, by group⟩
    rw [map_mul, map_inv, map_mul, hx, hx, hx, ofAdd_add, map_mul, inv_mul_cancel]
  have hadd₁ : ∀ s s' t, b (s + s') t = b s t + b s' t := by
    intro s s' t
    apply hbext
    rw [toMul_add, Subgroup.coe_mul, hb, hb, hb]
    obtain ⟨c, hc, hc'⟩ := hxadd s s'
    rw [hc', commutatorElement_mul_central_left hc,
      commutatorElement_mul_left_of_mem_center (hcen _ (hcomm s' t))]
  have hadd₂ : ∀ s t t', b s (t + t') = b s t + b s t' := by
    intro s t t'
    apply hbext
    rw [toMul_add, Subgroup.coe_mul, hb, hb, hb]
    obtain ⟨c, hc, hc'⟩ := hxadd t t'
    rw [hc', commutatorElement_mul_central_right hc,
      commutatorElement_mul_right_of_mem_center (hcen _ (hcomm s t'))]
  have halt : ∀ t, b t t = 0 := by
    intro t
    apply hbext
    rw [hb, toMul_zero, Subgroup.coe_one, commutatorElement_self]
  have hinv : ∀ a : K, a ≠ 0 → ∀ s t, b (a ^ 2 * s) (a ^ 2 * t) = b s t := by
    intro a ha s t
    obtain ⟨g, hg⟩ := hπ (pslMk (slD (Units.mk0 a ha)))
    have hconj : ∀ t : K, ∃ c ∈ Subgroup.center E, g * x t * g⁻¹ = x (a ^ 2 * t) * c := by
      intro t
      refine ⟨(x (a ^ 2 * t))⁻¹ * (g * x t * g⁻¹), hcen _ ?_, by group⟩
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hg, hx, hx, pslD_conj_pslU,
        Units.val_mk0, inv_mul_cancel]
    apply hbext
    rw [hb, hb]
    obtain ⟨c, hc, hcs⟩ := hconj s
    obtain ⟨d, hd, hdt⟩ := hconj t
    have hs' : x (a ^ 2 * s) = g * x s * g⁻¹ * c⁻¹ := by rw [hcs]; group
    have ht' : x (a ^ 2 * t) = g * x t * g⁻¹ * d⁻¹ := by rw [hdt]; group
    rw [hs', ht', commutatorElement_mul_central_left (Subgroup.inv_mem _ hc),
      commutatorElement_mul_central_right (Subgroup.inv_mem _ hd)]
    have hz := hcen _ (hcomm s t)
    calc ⁅g * x s * g⁻¹, g * x t * g⁻¹⁆ = g * ⁅x s, x t⁆ * g⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅x s, x t⁆ := by rw [Subgroup.mem_center_iff.1 hz g]; group
  have hb0 := square_invariant_alternating_eq_zero hp2 hK b hadd₁ hadd₂ halt hinv h9
  have hxx : ∀ s t, x s * x t = x t * x s := by
    intro s t
    have h := congrArg (fun u : Additive (Subgroup.center E) =>
      ((Additive.toMul u : Subgroup.center E) : E)) (hb0 s t)
    simp only [hb, toMul_zero, Subgroup.coe_one] at h
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  have hdecomp : ∀ y ∈ (P : Subgroup E), ∃ s, ∃ c ∈ Subgroup.center E, y = x s * c := by
    intro y hy
    obtain ⟨t, ht⟩ : π y ∈ (pslU (K := K)).range := hmap ▸ Subgroup.mem_map_of_mem π hy
    refine ⟨t.toAdd, (x t.toAdd)⁻¹ * y, hcen _ ?_, by group⟩
    rw [map_mul, map_inv, hx, ofAdd_toAdd, ht, inv_mul_cancel]
  refine sylow_kernel_eq_bot_of_commute π hC P (fun y hy y' hy' => ?_) Cp
  obtain ⟨s, c, hc, rfl⟩ := hdecomp y hy
  obtain ⟨t, d, hd, rfl⟩ := hdecomp y' hy'
  have hc' := Subgroup.mem_center_iff.1 hc
  have hd' := Subgroup.mem_center_iff.1 hd
  calc x s * c * (x t * d) = x s * (c * x t) * d := by group
    _ = x s * (x t * c) * d := by rw [hc' (x t)]
    _ = x s * x t * (c * d) := by group
    _ = x t * x s * (d * c) := by rw [hxx, hd' c]
    _ = x t * (x s * d) * c := by group
    _ = x t * (d * x s) * c := by rw [hd' (x s)]
    _ = x t * d * (x s * c) := by group

theorem psl_two_sylow_kernel_nine {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h9 : p ^ f = 9) (π : E →* ProjectiveSpecialLinearGroup (Fin 2) K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (Cp : Sylow p π.ker) :
    IsCyclic (Cp : Subgroup π.ker) ∧ Nat.card (Cp : Subgroup π.ker) ≤ p := by
  have := Fintype.ofFinite K
  have hchar : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hf2⟩ := eq_three_of_pow_eq_nine hp.out h9
  refine CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound π hπ hC
    Cp (pslUSylow hp2 hK) ?_ ?_
  · rw [coe_pslUSylow]
    exact isElemAbelian_range_pslU
  · rw [coe_pslUSylow, card_range_pslU, hK, hf2]

theorem psl_two_perfect_odd_cover_kernel {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (π : E →* ProjectiveSpecialLinearGroup (Fin 2) K)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) :
    (p ^ f ≠ 9 → π.ker = ⊥) ∧ (p ^ f = 9 → IsCyclic π.ker ∧ Nat.card π.ker ≤ 3) := by
  have hoff : ∀ r : ℕ, r.Prime → r ≠ p → ∀ [Fact r.Prime] (Cr : Sylow r π.ker),
      (Cr : Subgroup π.ker) = ⊥ := by
    intro r hr hrp _ Cr
    by_cases hr2 : r = 2
    · subst hr2
      exact sylow_two_eq_bot_of_odd hodd Cr
    · obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow r (ProjectiveSpecialLinearGroup (Fin 2) K)))
      exact CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hC Cr R
        (psl_two_sylow_isCyclic hp.out hp2 hK hr2 hrp R)
  refine ⟨fun h9 => ?_, fun h9 => ?_⟩
  · refine eq_bot_of_forall_sylow_eq_bot π.ker fun r hr _ Cr => ?_
    by_cases hrp : r = p
    · subst hrp
      exact psl_two_sylow_kernel_eq_bot hp2 hK h9 π hπ hC Cr
    · exact hoff r hr hrp Cr
  · obtain ⟨hp3, -⟩ := eq_three_of_pow_eq_nine hp.out h9
    have hpg : IsPGroup p π.ker := isPGroup_of_forall_sylow_eq_bot π.ker fun r hr hrp _ Cr =>
      hoff r hr hrp Cr
    obtain ⟨Cp⟩ := (inferInstance : Nonempty (Sylow p π.ker))
    obtain ⟨hcyc, hcard⟩ := psl_two_sylow_kernel_nine hp2 hK h9 π hπ hC Cp
    have htop : (Cp : Subgroup π.ker) = ⊤ := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
      rw [← Subgroup.card_eq_iff_eq_top, Sylow.card_eq_multiplicity, hk,
        Nat.Prime.factorization_pow hp.out, Finsupp.single_eq_same]
    let e : (Cp : Subgroup π.ker) ≃* π.ker :=
      (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    refine ⟨isCyclic_of_surjective e.toMonoidHom e.surjective, ?_⟩
    rw [← Nat.card_congr e.toEquiv, ← hp3]
    exact hcard

end Cover

section Model

@[expose] noncomputable def pslEquiv (K : Type) [Field K] :
    ProjectiveSpecialLinearGroup (Fin 2) K ≃* StatedProj (StatedSL 2 K) :=
  projectiveSpecialLinearGroupEquivStatedProj 2 K

omit [Finite K] in
theorem pslEquiv_pslMk (A : SpecialLinearGroup (Fin 2) K) :
    pslEquiv K (pslMk A) =
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 K A) : StatedProj (StatedSL 2 K)) :=
  rfl

@[expose] noncomputable def stU (K : Type) [Field K] :
    Multiplicative K →* StatedProj (StatedSL 2 K) :=
  (pslEquiv K).toMonoidHom.comp pslU

@[expose] noncomputable def stD (a : Kˣ) : StatedProj (StatedSL 2 K) :=
  pslEquiv K (pslMk (slD a))

omit [Finite K] in
theorem stU_apply (t : K) :
    stU K (Multiplicative.ofAdd t) =
      (QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 K (slU t)) :
        StatedProj (StatedSL 2 K)) :=
  rfl

omit [Finite K] in
theorem coe_specialLinearGroupEquivStatedSL_slU (t : K) :
    ((specialLinearGroupEquivStatedSL 2 K (slU t) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, t; 0, 1] :=
  rfl

omit [Finite K] in
theorem coe_specialLinearGroupEquivStatedSL_slD (a : Kˣ) :
    ((specialLinearGroupEquivStatedSL 2 K (slD a) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] :=
  rfl

omit [Finite K] in
theorem stD_def (a : Kˣ) : stD a = (QuotientGroup.mk (specialLinearGroupEquivStatedSL 2 K (slD a)) :
      StatedProj (StatedSL 2 K)) :=
  rfl

omit [Finite K] in
theorem det_eq_one_of_mem_statedSL {n : ℕ} {x : GL (Fin n) K} (hx : x ∈ StatedSL n K) :
    (x : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hx

omit [Finite K] in
theorem mem_statedScalars_sl_two_iff (x : StatedSL 2 K) :
    x ∈ (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) ↔
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 := by
  have hdet := det_eq_one_of_mem_statedSL x.2
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    have hcx : ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) (c : K) := by
      rw [← hc, GeneralLinearGroup.coe_scalar]
    rw [hcx, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    rcases mul_self_eq_one_iff.1 hdet with h | h
    · left; rw [hcx, h, map_one]
    · right; rw [hcx, h, map_neg, map_one]
  · rintro (h | h)
    · exact ⟨1, Units.ext (by rw [GeneralLinearGroup.coe_scalar, h, Units.val_one, map_one])⟩
    · exact ⟨-1, Units.ext (by rw [GeneralLinearGroup.coe_scalar, h, Units.val_neg, Units.val_one,
        map_neg, map_one])⟩

omit [Finite K] in
theorem card_statedScalars_sl_two {p : ℕ} [CharP K p] (hp2 : p ≠ 2) :
    Nat.card ((StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K)) = 2 := by
  rw [← map_center_eq_statedScalars, Subgroup.card_map_of_injective
    (specialLinearGroupEquivStatedSL 2 K).injective,
    Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
    Fintype.card_fin]
  have : NeZero (2 : ℕ) := ⟨two_ne_zero⟩
  exact (IsPrimitiveRoot.neg_one p hp2).card_rootsOfUnity

theorem odd_psl_two_sylow_data {p f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    (∀ x : StatedSL 2 K, x ∈ (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) ↔
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1) ∧
    Nat.card ((StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K)) = 2 ∧
    Nat.card (StatedProj (StatedSL 2 K)) = p ^ f * (((p ^ f) ^ 2 - 1) / 2) ∧
    Function.Injective (stU K) ∧
    (∃ U : Sylow p (StatedProj (StatedSL 2 K)), (U : Subgroup (StatedProj (StatedSL 2 K))) =
      (stU K).range ∧ IsElemAbelian p (U : Subgroup (StatedProj (StatedSL 2 K))) ∧
      Nat.card (U : Subgroup (StatedProj (StatedSL 2 K))) = p ^ f) ∧
    (∀ (a : Kˣ) (t : K), stD a * stU K (Multiplicative.ofAdd t) * (stD a)⁻¹ =
      stU K (Multiplicative.ofAdd ((a : K) ^ 2 * t))) ∧
    (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ [Fact r.Prime] (R : Sylow r (StatedProj (StatedSL 2 K))),
      IsCyclic (R : Subgroup (StatedProj (StatedSL 2 K)))) := by
  have := Fintype.ofFinite K
  have hchar : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  set e := pslEquiv K
  have hUmap : (stU K).range = (pslU (K := K)).range.map e.toMonoidHom := by
    rw [stU, MonoidHom.range_comp]
  refine ⟨mem_statedScalars_sl_two_iff, card_statedScalars_sl_two hp2, ?_,
    e.injective.comp pslU_injective, ?_, fun a t => ?_, fun r hr hr2 hrp _ R => ?_⟩
  · rw [← Nat.card_congr e.toEquiv, card_psl_two hp.out hp2 hK]
  · have hes : Function.Surjective e.toMonoidHom := e.surjective
    refine ⟨(pslUSylow hp2 hK).mapSurjective hes, ?_, ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective, coe_pslUSylow, hUmap]
    · rw [Sylow.coe_mapSurjective, coe_pslUSylow]
      exact isElemAbelian_map isElemAbelian_range_pslU _
    · rw [Sylow.coe_mapSurjective, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
        coe_pslUSylow, card_range_pslU, hK]
  · change e (pslMk (slD a)) * e (pslU (Multiplicative.ofAdd t)) * (e (pslMk (slD a)))⁻¹ =
      e (pslU (Multiplicative.ofAdd ((a : K) ^ 2 * t)))
    rw [← map_inv, ← map_mul, ← map_mul, pslD_conj_pslU]
  · have hes : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
    have hR := psl_two_sylow_isCyclic hp.out hp2 hK hr2 hrp (R.mapSurjective hes)
    rw [Sylow.coe_mapSurjective] at hR
    let e' := (R : Subgroup (StatedProj (StatedSL 2 K))).equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective
    exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

theorem odd_psl_two_perfect_odd_cover_kernel {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* StatedProj (StatedSL 2 K)) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    (p ^ f ≠ 9 → π.ker = ⊥) ∧ (p ^ f = 9 → IsCyclic π.ker ∧ Nat.card π.ker ≤ 3) := by
  set π' := (pslEquiv K).symm.toMonoidHom.comp π
  have hker : π'.ker = π.ker := by
    ext x
    simp [π']
  have h := psl_two_perfect_odd_cover_kernel hp2 hK π' ((pslEquiv K).symm.surjective.comp hπ)
    (hker ▸ hC) (hker ▸ hodd)
  rwa [hker] at h

end Model

section Catalog

theorem pRank_le_of_sylow_card_le {G : Type*} [Group G] [Finite G] {p k : ℕ} [hp : Fact p.Prime]
    (P : Sylow p G) (h : Nat.card (P : Subgroup G) ≤ p ^ k) :
    CFSG.Open.pRank p (⊤ : Subgroup G) ≤ k := by
  refine pRank_le (H := (⊤ : Subgroup G)) hp.out.one_lt fun E _ hE => ?_
  have hpg : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g g.2)⟩
  obtain ⟨Q, hEQ⟩ := hpg.exists_le_sylow
  calc Nat.card E ≤ Nat.card (Q : Subgroup G) := Subgroup.card_le_of_le hEQ
    _ = Nat.card (P : Subgroup G) := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ ≤ p ^ k := h

theorem ker_comp_mk'_center {L S : Type*} [Group L] [Group S] (θ : L ⧸ Subgroup.center L ≃* S) :
    (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = Subgroup.center L := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ θ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem isStronglyQuasithin_quotient_of_center_eq_bot {L : Type} [Group L] [Finite L]
    (hSQT : IsStronglyQuasithin L) (hbot : Subgroup.center L = ⊥) :
    IsStronglyQuasithin (L ⧸ Subgroup.center L) :=
  isStronglyQuasithin_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot) hSQT

theorem odd_linear_two_odd_cover_catalog_step {L : Type} [Group L] [Finite L] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hL : IsQuasisimple L) (hSQT : IsStronglyQuasithin L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (h : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 2 p f) :
    CatalogStepConclusion L ∧ (Subgroup.center L = ⊥ ∨ (p = 3 ∧ f = 2)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect L := hL.1
  obtain ⟨-, K, _, _, hK, ⟨θ⟩⟩ := h
  set π : L →* StatedProj (StatedSL 2 K) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)) with hπdef
  have hπ : Function.Surjective π := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := ker_comp_mk'_center θ
  obtain ⟨h1, h9⟩ := odd_psl_two_perfect_odd_cover_kernel hp2 hK π hπ hker.le (hker ▸ hodd)
  by_cases hq : p ^ f = 9
  · obtain ⟨hp3, hf2⟩ := eq_three_of_pow_eq_nine hp hq
    obtain ⟨-, hcard⟩ := h9 hq
    rw [hker] at hcard
    have hZ : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    refine ⟨catalogStepConclusion_of hSQT hZ ?_, Or.inr ⟨hp3, hf2⟩⟩
    rw [isStronglyQuasithin_iff]
    intro r hr hr2
    have : Fact r.Prime := ⟨hr⟩
    by_cases hr3 : r = 3
    · subst hr3
      subst hp3
      rw [pRank_top_eq_of_mulEquiv hr.one_lt θ]
      obtain ⟨-, -, -, -, ⟨U, -, -, hUcard⟩, -⟩ := odd_psl_two_sylow_data (K := K) hp2 hK
      exact pRank_le_of_sylow_card_le U (by rw [hUcard, hf2])
    · rw [pRank_quotient_eq (Subgroup.center L) (by
        rcases hZ with h' | h' <;> rw [h']
        · exact hr.one_lt.ne' ∘ Nat.dvd_one.1
        · exact fun hd => hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hd))]
      exact (isStronglyQuasithin_iff.1 hSQT) r hr hr2
  · have hbot : Subgroup.center L = ⊥ := hker ▸ h1 hq
    refine ⟨catalogStepConclusion_of hSQT (Or.inl ?_)
      (isStronglyQuasithin_quotient_of_center_eq_bot hSQT hbot), Or.inl hbot⟩
    rw [hbot, Subgroup.card_bot]

end Catalog

end CFSG.SectionRank.OddCover
