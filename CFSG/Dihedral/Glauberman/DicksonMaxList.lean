module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Glauberman.Dickson

open BenderSuzuki.MatrixGroups

universe u

section Orders

variable {F : Type u} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem psl2_pow_eq_one_of_mem_sylow (hF : Nat.card F = p ^ f)
    (P : Sylow p (PSL2MatrixGroup F)) {x : PSL2MatrixGroup F} (hx : x ∈ P) : x ^ p = 1 := by
  obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  have h : (e.symm ⟨x, hx⟩) ^ p = 1 := by
    rw [← ofAdd_toAdd (e.symm ⟨x, hx⟩), ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero,
      zero_mul, ofAdd_zero]
  have h' := congrArg (fun y => ((e y : P) : PSL2MatrixGroup F)) h
  simpa using h'

theorem psl2_card_dvd_of_isPGroup (hF : Nat.card F = p ^ f) {H : Subgroup (PSL2MatrixGroup F)}
    (hH : IsPGroup p H) : Nat.card H ∣ p ^ f := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  have hPcard : Nat.card (P : Subgroup (PSL2MatrixGroup F)) = p ^ f := by
    rw [← Nat.card_congr e.toEquiv]
    exact hF
  exact hPcard ▸ Subgroup.card_dvd_of_le hP

theorem psl2_orderOf_dvd (hF : Nat.card F = p ^ f) (x : PSL2MatrixGroup F) :
    orderOf x ∣ p ∨ orderOf x ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∨
      orderOf x ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 := by
  by_cases hx : x = 1
  · left
    rw [hx, orderOf_one]
    exact one_dvd p
  let P : Sylow p (PSL2MatrixGroup F) := default
  obtain ⟨U, S, -, hU, -, hS, hcover⟩ :=
    BenderSuzuki.External.huppert_II_8_5_a_psl2_cover hF P
  obtain ⟨T, ⟨hxT, hT⟩, -⟩ := hcover x hx
  have key : ∀ (A : Subgroup (PSL2MatrixGroup F)) (g : PSL2MatrixGroup F),
      x ∈ A.map (MulAut.conj g).toMonoidHom → ∃ y ∈ A, orderOf x = orderOf y := by
    rintro A g ⟨y, hy, rfl⟩
    exact ⟨y, hy, MulEquiv.orderOf_eq (MulAut.conj g) y⟩
  rcases hT with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · obtain ⟨y, hy, hxy⟩ := key _ g hxT
    left
    rw [hxy]
    exact orderOf_dvd_of_pow_eq_one (psl2_pow_eq_one_of_mem_sylow hF P hy)
  · obtain ⟨y, hy, hxy⟩ := key _ g hxT
    right; left
    rw [hxy, ← hU]
    exact Subgroup.orderOf_dvd_natCard U hy
  · obtain ⟨y, hy, hxy⟩ := key _ g hxT
    right; right
    rw [hxy, ← hS]
    exact Subgroup.orderOf_dvd_natCard S hy

theorem psl2_eq_one_of_commute (hF : Nat.card F = p ^ f) {c x : PSL2MatrixGroup F}
    (hcx : Commute c x) (hc : Nat.Coprime (orderOf c) p) (hxp : x ^ p = 1) (hx : x ≠ 1) :
    c = 1 := by
  have hp' := hp.out
  have hox : orderOf x = p := orderOf_eq_prime hxp hx
  have hmul : orderOf (c * x) = orderOf c * p := by
    rw [hcx.orderOf_mul_eq_mul_orderOf_of_coprime (hox ▸ hc), hox]
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hpq : p ∣ Nat.card F := hF ▸ dvd_pow_self p hf0
  have hq1 : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  have hpc : p ∣ orderOf (c * x) := hmul ▸ dvd_mul_left p (orderOf c)
  have hnot : ∀ n : ℕ, Nat.Coprime (Nat.card F) n → ¬ p ∣ n := by
    intro n hn hpn
    have h1 : p ∣ Nat.gcd (Nat.card F) n := Nat.dvd_gcd hpq hpn
    rw [hn.gcd_eq_one] at h1
    exact hp'.not_dvd_one h1
  rcases psl2_orderOf_dvd hF (c * x) with h | h | h
  · rw [hmul] at h
    have h1 : orderOf c * p ∣ 1 * p := by rwa [one_mul]
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (Nat.dvd_of_mul_dvd_mul_right hp'.pos h1))
  · exact (hnot _ (hq_coprime_split_order _ hq1) (hpc.trans h)).elim
  · exact (hnot _ (hq_coprime_nonsplit_order _ hq1) (hpc.trans h)).elim

end Orders

section List

variable {F : Type u} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

omit [Field F] [Finite F] hp in
theorem card_sub_one_div_eq (hF : Nat.card F = p ^ f) :
    (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 = (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1) := by
  rw [hF, Nat.gcd_comm]

omit [Field F] [Finite F] hp in
theorem card_add_one_div_eq (hF : Nat.card F = p ^ f) :
    (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 = (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) := by
  rw [hF, Nat.gcd_comm]

theorem two_dvd_half_of_odd {q : ℕ} (hq : Odd q) :
    2 ∣ (q + 1) / Nat.gcd 2 (q - 1) ∨ 2 ∣ (q - 1) / Nat.gcd 2 (q - 1) := by
  obtain ⟨j, rfl⟩ := hq
  have hg : Nat.gcd 2 (2 * j + 1 - 1) = 2 := by
    rw [show 2 * j + 1 - 1 = 2 * j by omega]
    exact Nat.gcd_eq_left (dvd_mul_right 2 j)
  rw [hg, show (2 * j + 1 + 1) / 2 = j + 1 by omega, show (2 * j + 1 - 1) / 2 = j by omega]
  rcases Nat.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
  · right
    exact ⟨i, by omega⟩
  · left
    exact ⟨i + 1, by omega⟩

theorem dickson_psl2_subgroup_list (hF : Nat.card F = p ^ f)
    (H : Subgroup (PSL2MatrixGroup F)) :
    (∃ m, m ≤ f ∧ Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∨
    (∃ z, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧
      Nat.card H = z ∧ IsCyclic H) ∨
    (∃ z, 2 ≤ z ∧
      (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧
      Nonempty (H ≃* DihedralGroup z)) ∨
    ((Odd p ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
    ((p ^ f) ^ 2 ≡ 1 [MOD 16] ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
    ((p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5]) ∧ Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ m t, 1 ≤ m ∧ m ≤ f ∧ t ∣ p ^ m - 1 ∧ t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1) ∧
      ∃ E C : Subgroup H, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ m ∧
        IsCyclic C ∧ Nat.card C = t ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
        (∀ c ∈ C, (∀ e ∈ E, c * e = e * c) → c = 1) ∧
        ∃ φ : C →* MulAut E, Function.Injective φ ∧ Nonempty (H ≃* E ⋊[φ] C)) ∨
    (∃ m, m ∣ f ∧ Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∨
    (∃ m, 2 * m ∣ f ∧ Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by
  classical
  have hp' := hp.out
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hsub := card_sub_one_div_eq hF
  have hadd := card_add_one_div_eq hF
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    hel | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz, hcard, ⟨e⟩⟩ | ⟨hA4, eA4⟩ | ⟨hS4, eS4⟩ | ⟨hA5, eA5⟩ |
      ⟨m, t, htm, htq, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, -, hmf, eL⟩ | ⟨m, -, hmf, eG⟩
  ·
    left
    have hdvd := psl2_card_dvd_of_isPGroup hF (IsElementaryAbelian.isPGroup p H)
    obtain ⟨m, hm, hmc⟩ := (Nat.dvd_prime_pow hp').1 hdvd
    exact ⟨m, hm, hmc, hel⟩
  ·
    right; left
    rw [hsub, hadd] at hz
    exact ⟨z, hz.symm, hcard, hcyc⟩
  ·
    rw [hsub, hadd] at hz
    by_cases hz2 : 2 ≤ z
    · right; right; left
      exact ⟨z, hz2, hz.symm, ⟨e⟩⟩
    have hz1 : z = 1 := by
      rcases Nat.lt_or_ge z 1 with h | h
      · have : z = 0 := by omega
        subst this
        exact absurd hcard (by simp [Nat.card_pos.ne'])
      · omega
    subst hz1
    have h2 : Nat.card H = 2 := by simpa using hcard
    have hcycH : IsCyclic H := isCyclic_of_prime_card (p := 2) h2
    by_cases hp2 : p = 2
    · subst hp2
      left
      refine ⟨1, Nat.one_le_iff_ne_zero.mpr hf0, by rw [h2, pow_one], ?_⟩
      exact
        { toIsMulCommutative := ⟨⟨fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b⟩⟩
          exponent_dvd_p := by
            have h3 := Group.exponent_dvd_nat_card (G := H)
            rwa [h2] at h3 }
    · right; left
      have hodd : Odd (p ^ f) := (hp'.odd_of_ne_two hp2).pow
      exact ⟨2, two_dvd_half_of_odd hodd, h2, hcycH⟩
  ·
    right; right; right; left
    refine ⟨?_, eA4⟩
    rcases hA4 with h | h
    · exact Or.inl (hp'.odd_of_ne_two h)
    · exact Or.inr h
  ·
    right; right; right; right; left
    refine ⟨?_, eS4⟩
    have h1 : 1 ≤ p ^ (2 * f) := Nat.one_le_pow _ _ hp'.pos
    rw [← pow_mul, mul_comm]
    exact ((Nat.modEq_iff_dvd' h1).mpr hS4).symm
  ·
    right; right; right; right; right; left
    refine ⟨?_, eA5⟩
    rcases hA5 with h | h
    · exact Or.inl h
    · right
      have h1 : 1 ≤ p ^ (2 * f) := Nat.one_le_pow _ _ hp'.pos
      rw [← pow_mul, mul_comm]
      exact ((Nat.modEq_iff_dvd' h1).mpr h).symm
  ·
    rw [Nat.gcd_comm] at htq
    by_cases hm0 : m = 0
    ·
      subst hm0
      right; left
      have hN1 : N = ⊥ := by
        rw [← Subgroup.card_eq_one]
        simpa using hNcard
      rw [hN1, bot_sup_eq] at hsup
      subst hsup
      refine ⟨t, Or.inr htq, ?_, ?_⟩
      · rw [← hCcard]
        exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
      · exact isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom Subgroup.topEquiv.surjective
    right; right; right; right; right; right; left
    have hmf : m ≤ f := by
      have hpg : IsPGroup p (N.map H.subtype) := by
        have := IsElementaryAbelian.isPGroup p N
        exact this.map _
      have hdvd := psl2_card_dvd_of_isPGroup hF hpg
      rw [Subgroup.card_map_of_injective H.subtype_injective, hNcard] at hdvd
      exact (Nat.pow_dvd_pow_iff_le_right hp'.one_lt).1 hdvd
    have hfaith : ∀ c ∈ C, (∀ e ∈ N, c * e = e * c) → c = 1 := by
      intro c hc hce
      have hNtriv : Nat.card N ≠ 1 := by
        rw [hNcard]
        exact (Nat.one_lt_pow hm0 hp'.one_lt).ne'
      obtain ⟨x, hxN, hx1⟩ : ∃ x ∈ N, x ≠ 1 := by
        by_contra hcon
        push Not at hcon
        apply hNtriv
        rw [Subgroup.card_eq_one, eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.mpr (hcon x hx)
      have hxp : x ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian x hxN
      have hcop : Nat.Coprime (orderOf (c : PSL2MatrixGroup F)) p := by
        have h1 : orderOf (c : PSL2MatrixGroup F) ∣ t := by
          rw [Subgroup.orderOf_coe, ← hCcard]
          exact Subgroup.orderOf_dvd_natCard C hc
        have h2 : Nat.Coprime (p ^ m - 1) p := by
          have h4 : 1 ≤ p ^ m := Nat.one_le_pow _ _ hp'.pos
          have h3 : Nat.Coprime (p ^ m) (p ^ m - 1) :=
            (Nat.coprime_self_sub_right h4).mpr (Nat.coprime_one_right _)
          exact Nat.Coprime.coprime_dvd_right (dvd_pow_self p hm0) h3.symm
        exact Nat.Coprime.coprime_dvd_left (h1.trans htm) h2
      have hcomm : Commute (c : PSL2MatrixGroup F) (x : PSL2MatrixGroup F) := by
        have := hce x hxN
        exact congrArg Subtype.val this
      have hxp' : (x : PSL2MatrixGroup F) ^ p = 1 := by
        rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one]
      have hx1' : (x : PSL2MatrixGroup F) ≠ 1 := by
        intro h
        exact hx1 (Subtype.ext h)
      exact Subtype.ext (psl2_eq_one_of_commute hF hcomm hcop hxp' hx1')
    have hcomp : N.IsComplement' C := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
    refine ⟨m, t, Nat.one_le_iff_ne_zero.mpr hm0, hmf, htm, htq, N, C, hN, hNel, hNcard, hCcyc,
      hCcard, hdisj, hsup, hfaith, _, ?_, ⟨(SemidirectProduct.mulEquivSubgroup hcomp).symm⟩⟩
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff] at hc
    simp only [Subgroup.coe_inclusion] at hc
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hfaith c c.2 (fun e he => (hc e he).symm))
  · right; right; right; right; right; right; right; left
    exact ⟨m, hmf, eL⟩
  · right; right; right; right; right; right; right; right
    exact ⟨m, hmf, eG⟩

end List

end CFSG.Glauberman.Dickson
