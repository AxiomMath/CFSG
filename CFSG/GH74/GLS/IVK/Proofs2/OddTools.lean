module

public import CFSG.Dihedral.Glauberman.DicksonMaxNode
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup
open scoped commutatorElement Pointwise

theorem eq_of_orderOf_two_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  classical
  have := Fintype.ofFinite G
  have hle := IsCyclic.card_pow_eq_one_le (α := G) (n := 2) (by norm_num)
  by_contra hne
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  have hsub : ({1, x, y} : Finset G) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [← hx]; exact pow_orderOf_eq_one _
    · rw [← hy]; exact pow_orderOf_eq_one _
  have hcard : ({1, x, y} : Finset G).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, x, y, hx1.symm, hy1.symm, hne, rfl⟩
  have h2 := Finset.card_le_card hsub
  omega

theorem commutator_mem_of_sup_eq_top {M : Type*} [Group M] (E C : Subgroup M) [E.Normal]
    (hC : IsCyclic C) (hsup : E ⊔ C = ⊤) (g h : M) : ⁅g, h⁆ ∈ E := by
  have hmem : ∀ x : M, ∃ c ∈ C, (x : M ⧸ E) = (c : M ⧸ E) := by
    intro x
    have hx : x ∈ (E : Set M) * (C : Set M) := by
      rw [← Subgroup.normal_mul, hsup]
      exact Set.mem_univ x
    obtain ⟨e, he, c, hc, rfl⟩ := hx
    refine ⟨c, hc, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e).mpr he, one_mul]
  obtain ⟨c₁, hc₁, h₁⟩ := hmem g
  obtain ⟨c₂, hc₂, h₂⟩ := hmem h
  have hcomm : c₁ * c₂ = c₂ * c₁ := by
    have := (IsCyclic.commGroup (α := C)).mul_comm ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩
    exact congrArg Subtype.val this
  have : QuotientGroup.mk' E ⁅g, h⁆ = 1 := by
    have e1 : QuotientGroup.mk' E g = QuotientGroup.mk' E c₁ := h₁
    have e2 : QuotientGroup.mk' E h = QuotientGroup.mk' E c₂ := h₂
    rw [map_commutatorElement, e1, e2, ← map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr hcomm, map_one]
  exact (QuotientGroup.eq_one_iff _).mp this

theorem eq_one_of_mem_elemAb_of_sq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M : Type*} [Group M]
    (E : Subgroup M) [hE : CFSG.IsElementaryAbelian p E] {a : M} (ha : a ∈ E) (ha2 : a * a = 1) :
    a = 1 := by
  have hp' := (Fact.out : p.Prime)
  have h1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) a ha
  obtain ⟨k, hk⟩ := hp'.odd_of_ne_two hp2
  have ha2' : a ^ 2 = 1 := by rw [pow_two]; exact ha2
  rw [hk, pow_succ, pow_mul, ha2', one_pow, one_mul] at h1
  exact h1



section PSL

open CFSG.Glauberman.Dickson.MaxNode CFSG.BenderSuzuki.MatrixGroups CFSG.PSL2Table

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem mul_self_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {x : G} (h : orderOf x = 2) :
    x * x = 1 := by
  have := pow_orderOf_eq_one x
  rw [h, pow_two] at this
  exact this

theorem not_klein_le_borel (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {M : Subgroup (PSL2MatrixGroup F)}
    {c : PSL2MatrixGroup F} (hM : M = (borel F).map (MulAut.conj c).toMonoidHom)
    {a b : PSL2MatrixGroup F} (ha : a ∈ M) (hb : b ∈ M) (hab : a ≠ b) (ha2 : orderOf a = 2)
    (hb2 : orderOf b = 2) (hcomm : a * b = b * a) : False := by
  obtain ⟨E, C, hEn, hEel, -, hC, -, -, hsup, -⟩ := borel_shape hF hp2 hM
  have := hEn
  have hsurj : ∀ q : ↥M ⧸ E, ∃ x : C, QuotientGroup.mk' E (x : ↥M) = q := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : m ∈ (E : Set ↥M) * (C : Set ↥M) := by
      rw [← Subgroup.normal_mul, hsup]
      exact Set.mem_univ m
    obtain ⟨e', he', c', hc', rfl⟩ := hx
    refine ⟨⟨c', hc'⟩, ?_⟩
    show ((c' : ↥M) : ↥M ⧸ E) = ((e' * c' : ↥M) : ↥M ⧸ E)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e').mpr he', one_mul]
  have hcyc : IsCyclic (↥M ⧸ E) :=
    isCyclic_of_surjective ((QuotientGroup.mk' E).comp C.subtype) (by
      intro q
      obtain ⟨x, hx⟩ := hsurj q
      exact ⟨x, hx⟩)
  have : Finite (↥M ⧸ E) := inferInstance
  set a' : ↥M := ⟨a, ha⟩
  set b' : ↥M := ⟨b, hb⟩
  have ha'2 : orderOf a' = 2 := (Subgroup.orderOf_mk a ha).trans ha2
  have hb'2 : orderOf b' = 2 := (Subgroup.orderOf_mk b hb).trans hb2
  have hcomm' : a' * b' = b' * a' := Subtype.ext hcomm
  have hq : ∀ x : ↥M, orderOf x = 2 → orderOf (QuotientGroup.mk x : ↥M ⧸ E) = 2 := by
    intro x hx
    have hx1 : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx
    have hne : (QuotientGroup.mk x : ↥M ⧸ E) ≠ 1 := by
      intro h
      have := eq_one_of_mem_elemAb_of_sq hp2 E ((QuotientGroup.eq_one_iff x).mp h) hx1
      rw [this, orderOf_one] at hx
      omega
    exact orderOf_eq_prime (by rw [sq, ← QuotientGroup.mk_mul, hx1]; rfl) hne
  have hEq := eq_of_orderOf_two_of_isCyclic (hq a' ha'2) (hq b' hb'2)
  have hmem : (a'⁻¹ * b') ∈ E := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hEq]
    simp
  have hsq : (a'⁻¹ * b') * (a'⁻¹ * b') = 1 := by
    have ha1 : a' * a' = 1 := mul_self_eq_one_of_orderOf_eq_two ha'2
    have hb1 : b' * b' = 1 := mul_self_eq_one_of_orderOf_eq_two hb'2
    have hinv : a'⁻¹ = a' := inv_eq_of_mul_eq_one_right ha1
    rw [hinv]
    calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
      _ = a' * (a' * b') * b' := by rw [← hcomm']
      _ = (a' * a') * (b' * b') := by group
      _ = 1 := by rw [ha1, hb1, one_mul]
  have h1 := eq_one_of_mem_elemAb_of_sq hp2 E hmem hsq
  have : a' = b' := by
    have h2 : a'⁻¹ * b' = 1 := h1
    exact inv_mul_eq_one.mp h2
  exact hab (congrArg Subtype.val this)

end PSL

section OddCases

open CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp CFSG.BenderSuzuki.MatrixGroups
  CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem even_mul_sq_sub_one {u : ℕ} (hu : Odd u) : Even (u * (u ^ 2 - 1)) := by
  obtain ⟨k, rfl⟩ := hu
  have h : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [h]
  exact Even.mul_left (Even.mul_right (by decide : Even 4) _) _

theorem even_half_mul_sq_sub_one {u : ℕ} (hu : Odd u) : Even (u * (u ^ 2 - 1) / 2) := by
  obtain ⟨k, rfl⟩ := hu
  have h : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega
  rw [h]
  have : (2 * k + 1) * (4 * (k * (k + 1))) / 2 = 2 * ((2 * k + 1) * (k * (k + 1))) := by
    have : (2 * k + 1) * (4 * (k * (k + 1))) = 2 * (2 * ((2 * k + 1) * (k * (k + 1)))) := by ring
    rw [this]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  rw [this]
  exact ⟨(2 * k + 1) * (k * (k + 1)), by ring⟩

theorem mem_of_pow_eq_one_of_normal_sylow {G : Type*} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : IsPGroup p N) (hcard : Nat.card N = p ^ m)
    (hfac : (Nat.card G).factorization p = m) {y : G} (hy : y ^ p = 1) : y ∈ N := by
  have hodv : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hy
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (by rwa [pow_one] : orderOf y ∣ p ^ 1)
  have hP : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  obtain ⟨P', hP'⟩ := hP.exists_le_sylow
  have hNP' : N ≤ P' := hN.le_sylow_of_normal P'
  have hcardP' : Nat.card P' = p ^ m := by rw [Sylow.card_eq_multiplicity, hfac]
  have hNeq : N = (P' : Subgroup G) := Subgroup.eq_of_le_of_card_ge hNP' (by rw [hcard, hcardP'])
  rw [hNeq]
  exact hP' (Subgroup.mem_zpowers y)

theorem dickson_odd (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (X : Subgroup (PSL2MatrixGroup F)) (hXodd : Odd (Nat.card X)) :
    (∃ m, m ≤ f ∧ Nat.card X = p ^ m ∧ IsElementaryAbelian p X) ∨
    (∃ z, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) ∧
      Nat.card X = z ∧ IsCyclic X) ∨
    (∃ m t, 1 ≤ m ∧ m ≤ f ∧ t ∣ p ^ m - 1 ∧ t ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1) ∧
      ∃ E C : Subgroup X, E.Normal ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ m ∧
        IsCyclic C ∧ Nat.card C = t ∧ Disjoint E C ∧ E ⊔ C = ⊤ ∧
        (∀ c ∈ C, (∀ e ∈ E, c * e = e * c) → c = 1)) := by
  have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  rcases dickson_psl2_subgroup_list hF X with
    h1 | h2 | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, hm1, hmf, htm, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, hfaith, -⟩ |
    ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exfalso
    have := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at this
    rw [this] at hXodd
    exact (Nat.not_even_iff_odd.mpr hXodd) ⟨z, by ring⟩
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_alternatingFour'] at hXodd
    exact absurd hXodd (by decide)
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_permFour] at hXodd
    exact absurd hXodd (by decide)
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_alternatingFive'] at hXodd
    exact absurd hXodd (by decide)
  · exact Or.inr (Or.inr ⟨m, t, hm1, hmf, htm, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup,
      hfaith⟩)
  · exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmf
      exact hf0 hmf
    rw [Nat.card_congr e.toEquiv, card_psl2_galoisField hp2 hm0, pow_mul' p 2 m] at hXodd
    exact (Nat.not_even_iff_odd.mpr hXodd) (even_half_mul_sq_sub_one (hpodd.pow))
  · exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hmf
      exact hf0 hmf
    rw [Nat.card_congr e.toEquiv] at hXodd
    have hq : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    rw [pgl2_card_formula, hq] at hXodd
    exact (Nat.not_even_iff_odd.mpr hXodd) (even_mul_sq_sub_one (hpodd.pow))

theorem odd_subgroup_cases (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (X : Subgroup (PSL2MatrixGroup F)) (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X)) :
    IsCyclic X ∨ ∃ E : Subgroup (PSL2MatrixGroup F), E ≠ ⊥ ∧ E ≤ X ∧ IsPGroup p E ∧
      ∀ g ∈ normalizer (X : Set (PSL2MatrixGroup F)), g ∈ normalizer (E : Set (PSL2MatrixGroup F)) := by
  rcases dickson_odd hF hp2 X hXodd with ⟨m, -, -, hel⟩ | ⟨z, -, -, hcyc⟩ |
    ⟨m, t, hm1, -, htm, -, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup, -⟩
  · right
    exact ⟨X, hX1, le_rfl, IsElementaryAbelian.isPGroup p X, fun g hg => hg⟩
  · exact Or.inl hcyc
  · right
    have := hN
    have hcomp : N.IsComplement' C :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj (by
        rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hXcard : Nat.card X = p ^ m * t := by
      rw [← hcomp.card_mul_card, hNcard, hCcard]
    have hm0 : m ≠ 0 := by omega
    have hcop : Nat.Coprime p t := by
      have h1 : Nat.Coprime p (p ^ m - 1) := by
        have h4 : 1 ≤ p ^ m := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
        have h3 : Nat.Coprime (p ^ m) (p ^ m - 1) :=
          (Nat.coprime_self_sub_right h4).mpr (Nat.coprime_one_right _)
        exact Nat.Coprime.coprime_dvd_left (dvd_pow_self p hm0) h3
      exact Nat.Coprime.coprime_dvd_right htm h1
    have hfac : (Nat.card X).factorization p = m := by
      rw [hXcard, Nat.factorization_mul (pow_ne_zero m (Fact.out : p.Prime).ne_zero) (by
        have := Nat.card_pos (α := C); omega), Finsupp.add_apply,
        Nat.Prime.factorization_pow (Fact.out : p.Prime)]
      have : t.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd
        (fun h => (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h) )
      simp [this]
    refine ⟨N.map X.subtype, ?_, ?_, ?_, ?_⟩
    · intro h
      have : N = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (x : PSL2MatrixGroup F) ∈ N.map X.subtype := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (Subtype.ext this)
      rw [this, Subgroup.card_bot] at hNcard
      have := Nat.one_lt_pow hm0 (Fact.out : p.Prime).one_lt
      omega
    · exact Subgroup.map_subtype_le N
    · exact (IsElementaryAbelian.isPGroup p N).map X.subtype
    · have hkey : ∀ g ∈ normalizer (X : Set (PSL2MatrixGroup F)), ∀ h ∈ N.map X.subtype,
          g * h * g⁻¹ ∈ N.map X.subtype := by
        intro g hg h hh
        obtain ⟨n, hn, rfl⟩ := hh
        have hgX : g * (n : PSL2MatrixGroup F) * g⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp hg _).mp n.2
        have hp1 : (n : ↥X) ^ p = 1 := by
          have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := N) n hn
          exact this
        have hpow : (g * (n : PSL2MatrixGroup F) * g⁻¹) ^ p = 1 := by
          rw [conj_pow, ← Subgroup.coe_pow, hp1, Subgroup.coe_one, mul_one, mul_inv_cancel]
        have := mem_of_pow_eq_one_of_normal_sylow (p := p) (m := m) N
          (IsElementaryAbelian.isPGroup p N) hNcard hfac
          (y := (⟨g * (n : PSL2MatrixGroup F) * g⁻¹, hgX⟩ : ↥X)) (Subtype.ext hpow)
        exact ⟨_, this, rfl⟩
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨hkey g hg h, fun hgh => ?_⟩
      have h1 := hkey g⁻¹ ((Subgroup.normalizer (X : Set (PSL2MatrixGroup F))).inv_mem hg) _ hgh
      have h2 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
      rwa [h2] at h1

end OddCases

end CFSG.GH74.GLS.IVK.Proofs2
