module

public import CFSG.Monster.B.Recog.GenericTransferExtremal
public import CFSG.Quasithin.Background.A1cTransfer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.SolomonWong

open MulAction CFSG.Monster.B.Recog.TransferExtremal CFSG.Quasithin

variable {G : Type*} [Group G]

open Classical in
theorem toAdd_transfer_sgn_eq {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) [M.FiniteIndex]
    {x : G} (hx : ∀ p : G ⧸ M, x • p ≠ p →
      p.out⁻¹ * x ^ Function.minimalPeriod (x • ·) p * p.out ∈ M₁) :
    Multiplicative.toAdd ((sgn M M₁ hM₁).transfer x) =
      (Nat.card {p : G ⧸ M // x • p = p ∧ p.out⁻¹ * x * p.out ∉ M₁} : ZMod 2) := by
  have : Fintype (Quotient (orbitRel (Subgroup.zpowers x) (G ⧸ M))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  have key : ∀ q : Quotient (orbitRel (Subgroup.zpowers x) (G ⧸ M)),
      Multiplicative.toAdd (sgn M M₁ hM₁
        ⟨q.out.out⁻¹ * x ^ Function.minimalPeriod (x • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem M x q.out⟩) =
      if x • q.out = q.out ∧ q.out.out⁻¹ * x * q.out.out ∉ M₁ then 1 else 0 := by
    intro q
    rw [toAdd_sgn]
    show (if q.out.out⁻¹ * x ^ Function.minimalPeriod (x • ·) q.out * q.out.out ∈ M₁
      then (0 : ZMod 2) else 1) = _
    by_cases hq : x • q.out = q.out
    · rw [minimalPeriod_eq_one_iff_fixedBy.2 hq, pow_one]
      by_cases hm : q.out.out⁻¹ * x * q.out.out ∈ M₁ <;> simp [hq, hm]
    · simp [hq, hx _ hq]
  rw [Fintype.sum_congr _ _ key, Finset.sum_boole]
  congr 1
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun q => ⟨q.1.out, q.2⟩
      invFun := fun p => ⟨Quotient.mk _ p.1, by rw [out_mk_of_smul_eq M p.2.1]; exact p.2⟩
      left_inv := fun q => Subtype.ext (Quotient.out_eq q.1)
      right_inv := fun p => Subtype.ext (out_mk_of_smul_eq M p.2.1) }

theorem transfer_sgn_eq_one {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) [M.FiniteIndex]
    {x : G} (hG : ∀ K : Subgroup G, K.index = 2 → x ∈ K) :
    (sgn M M₁ hM₁).transfer x = 1 := by
  have hidx : ((sgn M M₁ hM₁).transfer).ker.index ∣ 2 := by
    rw [Subgroup.index_ker]
    have h := Subgroup.card_subgroup_dvd_card ((sgn M M₁ hM₁).transfer).range
    rwa [Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2)), Fintype.card_multiplicative,
      ZMod.card] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h | h
  · rw [Subgroup.index_eq_one] at h
    have hmem : x ∈ ((sgn M M₁ hM₁).transfer).ker := by
      rw [h]; exact Subgroup.mem_top x
    exact hmem
  · exact hG _ h

theorem orderOf_conj_eq (c y : G) : orderOf (c⁻¹ * y * c) = orderOf y :=
  SemiconjBy.orderOf_eq c (by simp [SemiconjBy, mul_assoc])

theorem mul_mem_iff_of_relIndex_two {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) {u v : G}
    (hu : u ∈ M) (hv : v ∈ M) : u * v ∈ M₁ ↔ (u ∈ M₁ ↔ v ∈ M₁) := by
  have := Subgroup.mul_mem_iff_of_index_two (H := M₁.subgroupOf M) hM₁ (a := ⟨u, hu⟩)
    (b := ⟨v, hv⟩)
  simpa [Subgroup.mem_subgroupOf] using this

theorem mul_self_mem_of_relIndex_two {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) {u : G}
    (hu : u ∈ M) : u * u ∈ M₁ :=
  (mul_mem_iff_of_relIndex_two hM₁ hu hu).2 Iff.rfl

theorem conj_mul_mem_iff {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) {x c m : G} (hm : m ∈ M) :
    ((c * m)⁻¹ * x * (c * m) ∈ M ∧ (c * m)⁻¹ * x * (c * m) ∉ M₁) ↔
      (c⁻¹ * x * c ∈ M ∧ c⁻¹ * x * c ∉ M₁) := by
  have e : (c * m)⁻¹ * x * (c * m) = m⁻¹ * (c⁻¹ * x * c) * m := by group
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    have hy : c⁻¹ * x * c ∈ M := by
      have := M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
      simpa [mul_assoc] using this
    refine ⟨hy, fun hy1 => h2 ?_⟩
    rw [mul_mem_iff_of_relIndex_two hM₁ (M.mul_mem (M.inv_mem hm) hy) hm,
      mul_mem_iff_of_relIndex_two hM₁ (M.inv_mem hm) hy, inv_mem_iff]
    tauto
  · rintro ⟨h1, h2⟩
    refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm, fun h3 => h2 ?_⟩
    rw [mul_mem_iff_of_relIndex_two hM₁ (M.mul_mem (M.inv_mem hm) h1) hm,
      mul_mem_iff_of_relIndex_two hM₁ (M.inv_mem hm) h1, inv_mem_iff] at h3
    tauto

theorem fixed_bad_iff {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) (x c : G) :
    (x • (c : G ⧸ M) = c ∧ (c : G ⧸ M).out⁻¹ * x * (c : G ⧸ M).out ∉ M₁) ↔
      (c⁻¹ * x * c ∈ M ∧ c⁻¹ * x * c ∉ M₁) := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul M c
  have key := conj_mul_mem_iff hM₁ m.2 (x := x) (c := c)
  rw [smul_coe_eq_iff_conj_mem, hm]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : (c * m)⁻¹ * x * (c * m) ∈ M := by
      have e : (c * m)⁻¹ * x * (c * m) = (m : G)⁻¹ * (c⁻¹ * x * c) * m := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem m.2) h1) m.2
    exact key.1 ⟨h3, h2⟩
  · intro hh
    exact ⟨hh.1, (key.2 hh).2⟩

theorem even_card_fixed_bad [Finite G] {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) {x : G}
    (hG : ∀ K : Subgroup G, K.index = 2 → x ∈ K) (hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1)
    (hmin : ∀ y ∈ M, y ∉ M₁ → (∃ n : ℕ, y ^ 2 ^ n = 1) → orderOf x ≤ orderOf y) :
    Even (Nat.card {p : G ⧸ M // x • p = p ∧ p.out⁻¹ * x * p.out ∉ M₁}) := by
  have hfix : ∀ p : G ⧸ M, x • p ≠ p →
      p.out⁻¹ * x ^ Function.minimalPeriod (x • ·) p * p.out ∈ M₁ := by
    intro p hp
    have hmem := QuotientGroup.out_conj_pow_minimalPeriod_mem M x p
    by_contra hnot
    obtain ⟨n, hn⟩ := hx2
    have hkdvd : Function.minimalPeriod (x • ·) p ∣ orderOf x := by
      rw [← MulAction.period_eq_minimalPeriod, ← MulAction.pow_smul_eq_iff_period_dvd,
        pow_orderOf_eq_one, one_smul]
    have hk1 : Function.minimalPeriod (x • ·) p ≠ 1 := fun h =>
      hp (minimalPeriod_eq_one_iff_fixedBy.1 h)
    have hpos : 0 < orderOf x := orderOf_pos x
    have hk0 : Function.minimalPeriod (x • ·) p ≠ 0 := by
      rintro h
      rw [h, zero_dvd_iff] at hkdvd
      omega
    have hle := hmin _ hmem hnot ⟨n, (orderOf_dvd_iff_pow_eq_one).1 (by
      rw [orderOf_conj_eq]
      exact (orderOf_pow_dvd _).trans (orderOf_dvd_of_pow_eq_one hn))⟩
    rw [orderOf_conj_eq, orderOf_pow_of_dvd hk0 hkdvd] at hle
    have : orderOf x / Function.minimalPeriod (x • ·) p < orderOf x :=
      Nat.div_lt_self hpos (by omega)
    omega
  have hV := transfer_sgn_eq_one hM₁ hG
  have h := toAdd_transfer_sgn_eq hM₁ hfix
  rw [hV, toAdd_one] at h
  exact ZMod.natCast_eq_zero_iff_even.1 h.symm

theorem psi_mul {A : Subgroup G} (hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b) {x : G}
    (hxA : ∀ b ∈ A, x * b * x⁻¹ ∈ A) {b c : G} (hb : b ∈ A) (hc : c ∈ A) :
    (b * c)⁻¹ * x * (b * c) * x⁻¹ = (b⁻¹ * x * b * x⁻¹) * (c⁻¹ * x * c * x⁻¹) := by
  have hcomm : c⁻¹ * (b⁻¹ * (x * b * x⁻¹)) = (b⁻¹ * (x * b * x⁻¹)) * c⁻¹ :=
    hAc _ (A.inv_mem hc) _ (A.mul_mem (A.inv_mem hb) (hxA b hb))
  calc (b * c)⁻¹ * x * (b * c) * x⁻¹ = c⁻¹ * (b⁻¹ * (x * b * x⁻¹)) * (x * c * x⁻¹) := by group
    _ = (b⁻¹ * (x * b * x⁻¹)) * c⁻¹ * (x * c * x⁻¹) := by rw [hcomm]
    _ = (b⁻¹ * x * b * x⁻¹) * (c⁻¹ * x * c * x⁻¹) := by group

theorem psi_inv {A : Subgroup G} (hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b) {x : G}
    (hxA : ∀ b ∈ A, x * b * x⁻¹ ∈ A) {b : G} (hb : b ∈ A) :
    b⁻¹⁻¹ * x * b⁻¹ * x⁻¹ = (b⁻¹ * x * b * x⁻¹)⁻¹ := by
  have hcomm : b * (x * b⁻¹ * x⁻¹) = (x * b⁻¹ * x⁻¹) * b := hAc _ hb _ (hxA _ (A.inv_mem hb))
  calc b⁻¹⁻¹ * x * b⁻¹ * x⁻¹ = b * (x * b⁻¹ * x⁻¹) := by group
    _ = (x * b⁻¹ * x⁻¹) * b := hcomm
    _ = (b⁻¹ * x * b * x⁻¹)⁻¹ := by group

theorem conj_mul_bad_iff {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M)
    {x a : G} (hxa : a⁻¹ * x * a ∈ M) (hxa' : a⁻¹ * x * a ∉ M₁) (b : G) :
    ((b * a)⁻¹ * x * (b * a) ∈ M ∧ (b * a)⁻¹ * x * (b * a) ∉ M₁) ↔
      a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a ∈ M₁ := by
  have e : (b * a)⁻¹ * x * (b * a) = (a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a) * (a⁻¹ * x * a) := by
    group
  rw [e]
  constructor
  · rintro ⟨h1, h2⟩
    have hv : a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a ∈ M := by
      have := M.mul_mem h1 (M.inv_mem hxa)
      simpa [mul_assoc] using this
    rw [mul_mem_iff_of_relIndex_two hM₁ hv hxa] at h2
    tauto
  · intro hv
    refine ⟨M.mul_mem (hM₁M hv) hxa, ?_⟩
    rw [mul_mem_iff_of_relIndex_two hM₁ (hM₁M hv) hxa]
    tauto

theorem mul_comm_of_sq_eq_one {E : Subgroup G} (hE2 : ∀ e ∈ E, e ^ 2 = 1) {b c : G} (hb : b ∈ E)
    (hc : c ∈ E) : b * c = c * b := by
  have hinv : ∀ e ∈ E, e⁻¹ = e := fun e he =>
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hE2 e he)
  calc b * c = (b * c)⁻¹ := (hinv _ (E.mul_mem hb hc)).symm
    _ = c * b := by rw [mul_inv_rev, hinv b hb, hinv c hc]

theorem card_conjSubgroup (E : Subgroup G) (g : G) : Nat.card (conjSubgroup E g) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjSubgroup_sq {E : Subgroup G} (hE2 : ∀ e ∈ E, e ^ 2 = 1) (g : G) :
    ∀ y ∈ conjSubgroup E g, y ^ 2 = 1 := by
  intro y hy
  rw [mem_conjSubgroup_iff] at hy
  have h := hE2 _ hy
  rw [conj_pow] at h
  calc y ^ 2 = g⁻¹ * (g * y ^ 2 * g⁻¹) * g := by group
    _ = 1 := by rw [h]; group

theorem exists_singular_coset [Finite G] {M M₁ A : Subgroup G} {x : G}
    (hG : ∀ K : Subgroup G, K.index = 2 → x ∈ K) (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M)
    (hAM : A ≤ M) (hA2 : IsPGroup 2 A) (hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b)
    (hxA : ∀ b ∈ A, x * b * x⁻¹ ∈ A) (hNA : Subgroup.normalizer (A : Set G) ≤ M)
    (hsyl : ∀ g : G, conjSubgroup A g ≤ M → ∃ m ∈ M, conjSubgroup A g = conjSubgroup A m)
    (hxM : x ∈ M) (hxM₁ : x ∉ M₁) (hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1)
    (hmin : ∀ y ∈ M, y ∉ M₁ → (∃ n : ℕ, y ^ 2 ^ n = 1) → orderOf x ≤ orderOf y) :
    ∃ a : G, a ∉ M ∧ a⁻¹ * x * a ∈ M ∧ a⁻¹ * x * a ∉ M₁ ∧
      (∀ b ∈ A, a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a ∈ M₁ → a⁻¹ * b * a ∈ M) ∧
      ∃ b ∈ A, a⁻¹ * b * a ∉ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (G ⧸ M) := Fintype.ofFinite _
  let P : G ⧸ M → Prop := fun p => x • p = p ∧ p.out⁻¹ * x * p.out ∉ M₁
  let Fs : Finset (G ⧸ M) := Finset.univ.filter P
  have hFs : Even Fs.card := by
    have h : Fs.card = Nat.card {p // P p} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h]
    exact even_card_fixed_bad hM₁ hG hx2 hmin
  have : Fintype (Quotient (MulAction.orbitRel A (G ⧸ M))) := Fintype.ofFinite _
  let π : G ⧸ M → Quotient (MulAction.orbitRel A (G ⧸ M)) := Quotient.mk _
  have hsum : Fs.card = ∑ ω, (Fs.filter (fun p => π p = ω)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  let p₀ : G ⧸ M := ((1 : G) : G ⧸ M)
  have hπ0 : ∀ p : G ⧸ M, π p = π p₀ → p = p₀ := by
    intro p h
    obtain ⟨b, rfl⟩ := MulAction.orbitRel_apply.1 (Quotient.exact h)
    show b • p₀ = p₀
    rw [Subgroup.smul_def, smul_coe_eq_iff_conj_mem]
    simpa using hAM b.2
  have hP0 : P p₀ := (fixed_bad_iff hM₁ x 1).2 ⟨by simpa using hxM, by simpa using hxM₁⟩
  have hfib0 : (Fs.filter (fun p => π p = π p₀)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨p₀, ?_⟩
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fs]
    exact ⟨fun h => hπ0 p h.2, by rintro rfl; exact ⟨hP0, rfl⟩⟩
  obtain ⟨ω, hω0, hodd⟩ : ∃ ω, ω ≠ π p₀ ∧ Odd (Fs.filter (fun p => π p = ω)).card := by
    by_contra hcon
    push Not at hcon
    have hrest : Even (∑ ω ∈ Finset.univ.erase (π p₀), (Fs.filter (fun p => π p = ω)).card) :=
      Finset.even_sum _ fun ω hω => Nat.not_odd_iff_even.1 (hcon ω (Finset.ne_of_mem_erase hω))
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (π p₀)), hfib0] at hsum
    rw [hsum] at hFs
    exact (Nat.not_even_iff_odd.2 (Even.one_add hrest)) hFs
  obtain ⟨p₁, hp₁⟩ := Finset.card_pos.1 hodd.pos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fs] at hp₁
  obtain ⟨hPp₁, hp₁ω⟩ := hp₁
  set a := p₁.out with ha
  have hap : ((a : G) : G ⧸ M) = p₁ := QuotientGroup.out_eq' p₁
  have hxa : a⁻¹ * x * a ∈ M ∧ a⁻¹ * x * a ∉ M₁ := by
    rw [← fixed_bad_iff hM₁ x a, hap]
    exact hPp₁
  have haM : a ∉ M := by
    intro haM
    apply hω0
    rw [← hp₁ω, ← hap]
    congr 1
    exact QuotientGroup.eq.2 (by simpa using haM)
  let B : Subgroup G :=
    { carrier := {b | b ∈ A ∧ a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a ∈ M₁}
      mul_mem' := by
        rintro b c ⟨hb, hb'⟩ ⟨hc, hc'⟩
        refine ⟨A.mul_mem hb hc, ?_⟩
        rw [psi_mul hAc hxA hb hc]
        have e : a⁻¹ * ((b⁻¹ * x * b * x⁻¹) * (c⁻¹ * x * c * x⁻¹)) * a =
            (a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a) * (a⁻¹ * (c⁻¹ * x * c * x⁻¹) * a) := by group
        rw [e]
        exact M₁.mul_mem hb' hc'
      one_mem' := ⟨A.one_mem, by simp⟩
      inv_mem' := by
        rintro b ⟨hb, hb'⟩
        refine ⟨A.inv_mem hb, ?_⟩
        rw [psi_inv hAc hxA hb]
        have e : a⁻¹ * (b⁻¹ * x * b * x⁻¹)⁻¹ * a = (a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a)⁻¹ := by
          group
        rw [e]
        exact M₁.inv_mem hb' }
  have hmemB : ∀ b : G, b ∈ B ↔ b ∈ A ∧ a⁻¹ * (b⁻¹ * x * b * x⁻¹) * a ∈ M₁ := fun _ => Iff.rfl
  have hsmul : ∀ b : G, b • p₁ = ((b * a : G) : G ⧸ M) := by
    intro b
    rw [← hap, MulAction.Quotient.smul_coe, smul_eq_mul]
  have hfib : ((Fs.filter (fun p => π p = ω) : Finset (G ⧸ M)) : Set (G ⧸ M)) =
      MulAction.orbit B p₁ := by
    ext q
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Fs]
    constructor
    · rintro ⟨hPq, hqω⟩
      obtain ⟨⟨b, hb⟩, rfl⟩ :=
        MulAction.orbitRel_apply.1 (Quotient.exact (hqω.trans hp₁ω.symm))
      have hPb : P ((b * a : G) : G ⧸ M) := by
        rw [← hsmul]
        exact hPq
      have h1 := (fixed_bad_iff hM₁ x (b * a)).1 hPb
      exact ⟨⟨b, hb, (conj_mul_bad_iff hM₁ hM₁M hxa.1 hxa.2 b).1 h1⟩, rfl⟩
    · rintro ⟨⟨b, hb, hb'⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show P (b • p₁)
        rw [hsmul]
        exact (fixed_bad_iff hM₁ x (b * a)).2 ((conj_mul_bad_iff hM₁ hM₁M hxa.1 hxa.2 b).2 hb')
      · rw [← hp₁ω]
        exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨⟨b, hb⟩, rfl⟩)
  have hodd' : Odd (MulAction.stabilizer B p₁).index := by
    rw [MulAction.index_stabilizer, ← hfib, Set.ncard_coe_finset]
    exact hodd
  have hB2 : IsPGroup 2 B := hA2.to_le fun b hb => hb.1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hB2
  have hdvd := Subgroup.index_dvd_card (MulAction.stabilizer B p₁)
  rw [hk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    rcases j with _ | j
    · rfl
    · rw [hj, pow_succ] at hodd'
      exact absurd hodd' (Nat.not_odd_iff_even.2 (even_two.mul_left _))
  have htop : MulAction.stabilizer B p₁ = ⊤ := by
    rw [← Subgroup.index_eq_one, hj, hj0, pow_zero]
  refine ⟨a, haM, hxa.1, hxa.2, fun b hb hb' => ?_, ?_⟩
  · have hst : (⟨b, hb, hb'⟩ : B) ∈ MulAction.stabilizer B p₁ := by
      rw [htop]
      exact Subgroup.mem_top _
    have h1 : b • p₁ = p₁ := hst
    rw [← hap, smul_coe_eq_iff_conj_mem] at h1
    exact h1
  · by_contra hcon
    push Not at hcon
    have hle : conjSubgroup A a ≤ M := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have := hcon _ hy
      simpa [mul_assoc] using this
    obtain ⟨m, hm, hAm⟩ := hsyl a hle
    have hN : a * m⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, hAm,
        conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    apply haM
    have := M.mul_mem (hNA hN) hm
    simpa using this

section Algebra

variable {V : Type*} [CommGroup V] (σ : V →* V)

theorem psi_one_mul_self (b : V) :
    (b * σ b)⁻¹ * σ (b * σ b) = b⁻¹ * σ (σ b) := by
  simp only [map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem psi_mul_self_eq (b : V) (h4 : b ^ 4 = 1) :
    (b⁻¹ * σ b) * (b⁻¹ * σ b) = (b * σ b) * (b * σ b) := by
  have e : (b⁻¹ * σ b) * (b⁻¹ * σ b) = (b * σ b) * (b * σ b) * (b ^ 4)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
  rw [e, h4, inv_one, mul_one]

theorem psi_psi (b : V) :
    (b⁻¹ * σ b)⁻¹ * σ (b⁻¹ * σ b) = (b⁻¹ * σ (σ b)) * ((b⁻¹ * σ b) * (b⁻¹ * σ b))⁻¹ := by
  simp only [map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem psi_inv_mul (b c : V) :
    (b⁻¹ * c)⁻¹ * σ (b⁻¹ * c) = (b⁻¹ * σ b)⁻¹ * (c⁻¹ * σ c) := by
  simp only [map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem psi_two_comm (b : V) :
    (b⁻¹ * σ b)⁻¹ * σ (σ (b⁻¹ * σ b)) = (b⁻¹ * σ (σ b))⁻¹ * σ (b⁻¹ * σ (σ b)) := by
  simp only [map_mul, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {σ}

theorem exists_psi_mem_notMem {AK AT : Subgroup V}
    (hN2 : ∀ v, v⁻¹ * σ v ∈ AK → v ∈ AT)
    (hnil : ∀ v, ∃ n : ℕ, (fun w => w⁻¹ * σ w)^[n] v = 1) {v : V} (hv : v ∉ AT) :
    ∃ w ∈ AT, w ∉ AK := by
  classical
  have hex : ∃ n, (fun w => w⁻¹ * σ w)^[n] v ∈ AT := by
    obtain ⟨n, hn⟩ := hnil v
    exact ⟨n, hn ▸ AT.one_mem⟩
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact hv this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hlt : ¬ (fun w => w⁻¹ * σ w)^[m] v ∈ AT := Nat.find_min hex (by omega)
  have hspec := Nat.find_spec hex
  rw [hm, Function.iterate_succ_apply'] at hspec
  exact ⟨_, hspec, fun h => hlt (hN2 _ h)⟩

theorem exists_psi_two_mem_notMem {AK AT : Subgroup V}
    (hsq : ∀ u ∈ AT, u * u ∈ AK)
    (hprod : ∀ u ∈ AT, ∀ w ∈ AT, u ∉ AK → w ∉ AK → u⁻¹ * w ∈ AK)
    (hN2 : ∀ v, v⁻¹ * σ v ∈ AK → v ∈ AT)
    (hnil : ∀ v, ∃ n : ℕ, (fun w => w⁻¹ * σ w)^[n] v = 1) (h4 : ∀ v : V, v ^ 4 = 1)
    {v₁ v₂ : V} (hv₁ : v₁ ∉ AT) (hv₂ : v₂ ∉ AT) (hv₁₂ : v₁⁻¹ * v₂ ∉ AT) :
    ∃ v : V, v⁻¹ * σ (σ v) ∈ AT ∧ v⁻¹ * σ (σ v) ∉ AK := by
  classical
  obtain ⟨b₀, hb₀⟩ : ∃ b : V, b⁻¹ * σ (σ b) ∉ AK := by
    by_contra hcon
    push Not at hcon
    have hψT : ∀ b : V, b⁻¹ * σ b ∈ AT := by
      intro b
      have hu : b * σ b ∈ AT := hN2 _ (by rw [psi_one_mul_self]; exact hcon b)
      have hsqψ : (b⁻¹ * σ b) * (b⁻¹ * σ b) ∈ AK := by
        rw [psi_mul_self_eq σ b (h4 b)]
        exact hsq _ hu
      exact hN2 _ (by rw [psi_psi]; exact AK.mul_mem (hcon b) (AK.inv_mem hsqψ))
    have h1 : v₁⁻¹ * σ v₁ ∉ AK := fun h => hv₁ (hN2 _ h)
    have h2 : v₂⁻¹ * σ v₂ ∉ AK := fun h => hv₂ (hN2 _ h)
    exact hv₁₂ (hN2 _ (by rw [psi_inv_mul]; exact hprod _ (hψT v₁) _ (hψT v₂) h1 h2))
  have hex : ∃ n, ((fun w => w⁻¹ * σ w)^[n] b₀)⁻¹ * σ (σ ((fun w => w⁻¹ * σ w)^[n] b₀)) ∈ AK := by
    obtain ⟨n, hn⟩ := hnil b₀
    exact ⟨n, by rw [hn]; simp⟩
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact hb₀ this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hlt := Nat.find_min hex (show m < Nat.find hex by omega)
  have hspec := Nat.find_spec hex
  rw [hm, Function.iterate_succ_apply', psi_two_comm] at hspec
  exact ⟨_, hN2 _ hspec, hlt⟩

end Algebra

theorem exists_iterate_eq_one_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {S : Subgroup G}
    (hS : IsPGroup p S) {x : G} (hx : x ∈ S) {y : G} (hy : y ∈ S) :
    ∃ n : ℕ, (fun z => z⁻¹ * x * z * x⁻¹)^[n] y = 1 := by
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries S).1 hS.isNilpotent
  refine ⟨c, ?_⟩
  have hmem : ∀ n, (fun z => z⁻¹ * x * z * x⁻¹)^[n] y ∈ S.lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [Function.iterate_succ_apply', Subgroup.lowerCentralSeries_succ]
      have := Subgroup.commutator_mem_commutator (inv_mem ih) hx
      simpa [commutatorElement_def] using this
  have := hmem c
  rwa [hc, Subgroup.mem_bot] at this

theorem index_le_two_of_forall {H : Type*} [Group H] {K : Subgroup H}
    (h : ∀ v₁ v₂ : H, v₁ ∉ K → v₂ ∉ K → v₁⁻¹ * v₂ ∈ K) : K.index ≤ 2 := by
  classical
  let f : H ⧸ K → Bool := fun q => decide (q = ((1 : H) : H ⧸ K))
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with | H v₁ => ?_
    induction q₂ using QuotientGroup.induction_on with | H v₂ => ?_
    have e : ∀ v : H, ((v : H ⧸ K) = ((1 : H) : H ⧸ K)) ↔ v ∈ K := fun v => by
      rw [QuotientGroup.eq, mul_one, inv_mem_iff]
    simp only [f, decide_eq_decide, e] at hq
    rw [QuotientGroup.eq]
    by_cases h1 : v₁ ∈ K
    · exact K.mul_mem (K.inv_mem h1) (hq.1 h1)
    · exact h v₁ v₂ h1 (fun h2 => h1 (hq.2 h2))
  calc K.index = Nat.card (H ⧸ K) := rfl
    _ ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
    _ = 2 := by simp

theorem exists_conj_relIndex_le_two_of_min [Finite G] {M M₁ A S : Subgroup G} {x : G}
    (hG : ∀ K : Subgroup G, K.index = 2 → x ∈ K) (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M)
    (hS : IsPGroup 2 S) (hSM : S ≤ M) (hAS : A ≤ S) (hxS : x ∈ S)
    (hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b) (hA4 : ∀ b ∈ A, b ^ 4 = 1)
    (hxA : ∀ b ∈ A, x * b * x⁻¹ ∈ A) (hNA : Subgroup.normalizer (A : Set G) ≤ M)
    (hsyl : ∀ g : G, conjSubgroup A g ≤ M → ∃ m ∈ M, conjSubgroup A g = conjSubgroup A m)
    (hxM₁ : x ∉ M₁)
    (hmin : ∀ y ∈ M, y ∉ M₁ → (∃ n : ℕ, y ^ 2 ^ n = 1) → orderOf x ≤ orderOf y) :
    ∃ g : G, g ∉ M ∧ M.relIndex (conjSubgroup A g) ≤ 2 ∧ ¬ conjSubgroup A g ⊓ M ≤ M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hS ⟨x, hxS⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  obtain ⟨a, haM, hxa, hxa', hN2, b₀, hb₀, hb₀'⟩ := exists_singular_coset hG hM₁ hM₁M
    (hAS.trans hSM) (hS.to_le hAS) hAc hxA hNA hsyl (hSM hxS) hxM₁ hx2 hmin
  let _ : CommGroup A := { (inferInstance : Group A) with
    mul_comm := fun b c => Subtype.ext (hAc b b.2 c c.2) }
  let σ : A →* A :=
    { toFun := fun b => ⟨x * b * x⁻¹, hxA b b.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun b c => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let f : A →* G := (MulAut.conj a⁻¹).toMonoidHom.comp A.subtype
  have hf : ∀ b : A, f b = a⁻¹ * b * a := fun b => by simp [f]
  let AT : Subgroup A := M.comap f
  let AK : Subgroup A := M₁.comap f
  have hAT : ∀ b : A, b ∈ AT ↔ a⁻¹ * (b : G) * a ∈ M := fun b => by
    rw [Subgroup.mem_comap, hf]
  have hAK : ∀ b : A, b ∈ AK ↔ a⁻¹ * (b : G) * a ∈ M₁ := fun b => by
    rw [Subgroup.mem_comap, hf]
  have hψ : ∀ b : A, ((b⁻¹ * σ b : A) : G) = (b : G)⁻¹ * x * b * x⁻¹ := fun b => by
    show (b : G)⁻¹ * (x * b * x⁻¹) = _
    group
  have hN2' : ∀ b : A, b⁻¹ * σ b ∈ AK → b ∈ AT := fun b h => by
    rw [hAK, hψ] at h
    rw [hAT]
    exact hN2 b b.2 h
  have hnil : ∀ v : A, ∃ n : ℕ, (fun w => w⁻¹ * σ w)^[n] v = 1 := by
    intro v
    obtain ⟨n, hn⟩ := exists_iterate_eq_one_of_isPGroup hS hxS (hAS v.2)
    refine ⟨n, Subtype.ext ?_⟩
    have hcoe : ∀ (k : ℕ) (w : A), (((fun w => w⁻¹ * σ w)^[k] w : A) : G) =
        (fun z => z⁻¹ * x * z * x⁻¹)^[k] (w : G) := by
      intro k
      induction k with
      | zero => intro w; rfl
      | succ k ih =>
        intro w
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hψ]
    rw [hcoe, hn]
    rfl
  have hsq : ∀ u ∈ AT, u * u ∈ AK := fun u hu => by
    rw [hAT] at hu
    rw [hAK]
    have e : a⁻¹ * ((u * u : A) : G) * a = (a⁻¹ * u * a) * (a⁻¹ * u * a) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact mul_self_mem_of_relIndex_two hM₁ hu
  have hprod : ∀ u ∈ AT, ∀ w ∈ AT, u ∉ AK → w ∉ AK → u⁻¹ * w ∈ AK := by
    intro u hu w hw hu' hw'
    rw [hAT] at hu hw
    rw [hAK] at hu' hw' ⊢
    have e : a⁻¹ * ((u⁻¹ * w : A) : G) * a = (a⁻¹ * u * a)⁻¹ * (a⁻¹ * w * a) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, mul_mem_iff_of_relIndex_two hM₁ (M.inv_mem hu) hw, inv_mem_iff]
    tauto
  have h4 : ∀ v : A, v ^ 4 = 1 := fun v => Subtype.ext (by simpa using hA4 v v.2)
  obtain ⟨w, hwT, hwK⟩ := exists_psi_mem_notMem hN2' hnil
    (v := ⟨b₀, hb₀⟩) (by rw [hAT]; exact hb₀')
  rw [hAT] at hwT
  rw [hAK] at hwK
  refine ⟨a, haM, ?_, fun hle => hwK (hle (Subgroup.mem_inf.2 ⟨?_, hwT⟩))⟩
  ·
    have hidx : M.relIndex (conjSubgroup A a) = AT.index := by
      rw [Subgroup.index_comap]
      congr 1
      ext y
      simp [f, conjSubgroup]
    rw [hidx]
    refine index_le_two_of_forall fun v₁ v₂ hv₁ hv₂ => ?_
    by_contra hv₁₂
    obtain ⟨v, hvT, hvK⟩ :=
      exists_psi_two_mem_notMem hsq hprod hN2' hnil h4 hv₁ hv₂ hv₁₂
    rw [hAT] at hvT
    rw [hAK] at hvK
    have hcoe2 : ((v⁻¹ * σ (σ v) : A) : G) = (v : G)⁻¹ * (x * (x * v * x⁻¹) * x⁻¹) := rfl
    have hy : ((v : G) * a)⁻¹ * (x * x) * ((v : G) * a) =
        (a⁻¹ * ((v⁻¹ * σ (σ v) : A) : G) * a) * ((a⁻¹ * x * a) * (a⁻¹ * x * a)) := by
      rw [hcoe2]
      group
    have hyM : ((v : G) * a)⁻¹ * (x * x) * ((v : G) * a) ∈ M := by
      rw [hy]
      exact M.mul_mem hvT (M.mul_mem hxa hxa)
    have hyM₁ : ((v : G) * a)⁻¹ * (x * x) * ((v : G) * a) ∉ M₁ := by
      rw [hy]
      intro h
      apply hvK
      have := M₁.mul_mem h (M₁.inv_mem (mul_self_mem_of_relIndex_two hM₁ hxa))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨n, hn⟩ := hx2
    have hle := hmin _ hyM hyM₁ ⟨n, (orderOf_dvd_iff_pow_eq_one).1 (by
      rw [orderOf_conj_eq, ← sq]
      exact (orderOf_pow_dvd _).trans (orderOf_dvd_of_pow_eq_one hn))⟩
    rw [orderOf_conj_eq, ← sq] at hle
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hxM₁ (hk ▸ M₁.one_mem)
    have h2dvd : 2 ∣ orderOf x := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    rw [orderOf_pow_of_dvd two_ne_zero h2dvd] at hle
    have : orderOf x / 2 < orderOf x := Nat.div_lt_self (orderOf_pos x) one_lt_two
    omega
  · rw [mem_conjSubgroup_iff]
    have e : a * (a⁻¹ * (w : G) * a) * a⁻¹ = w := by group
    rw [e]
    exact w.2

theorem mem_of_sq_eq_one [Finite G] {M M₁ A : Subgroup G} (hG : ∀ K : Subgroup G, K.index ≠ 2)
    (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M) (hAM : A ≤ M) (hA2 : IsPGroup 2 A)
    (hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b) (hNA : Subgroup.normalizer (A : Set G) ≤ M)
    (hsyl : ∀ g : G, conjSubgroup A g ≤ M → ∃ m ∈ M, conjSubgroup A g = conjSubgroup A m)
    {e : G} (heA : e ∈ A) (he : e ^ 2 = 1) : e ∈ M₁ := by
  by_contra he₁
  have hord : orderOf e = 2 := orderOf_eq_prime he fun h => he₁ (h ▸ M₁.one_mem)
  obtain ⟨a, -, -, -, hN2, b, hb, hb'⟩ := exists_singular_coset (x := e)
    (fun K hK => absurd hK (hG K)) hM₁ hM₁M hAM hA2 hAc
    (fun b hb => A.mul_mem (A.mul_mem heA hb) (A.inv_mem heA)) hNA hsyl (hAM heA) he₁
    ⟨1, by simpa using he⟩ (fun y _ hy₁ _ => by
      have hy1 : y ≠ 1 := fun h => hy₁ (h ▸ M₁.one_mem)
      have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
      have h0 : 0 < orderOf y := orderOf_pos y
      omega)
  apply hb'
  apply hN2 b hb
  have e1 : b⁻¹ * e * b * e⁻¹ = 1 := by
    rw [mul_assoc b⁻¹, hAc e heA b hb, ← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel]
  rw [e1, mul_one, inv_mul_cancel]
  exact M₁.one_mem

theorem exists_conj_mem_sylow [Finite G] {M : Subgroup G} (P : Sylow 2 M) {y : G} (hy : y ∈ M)
    (hy2 : ∃ n : ℕ, y ^ 2 ^ n = 1) :
    ∃ m ∈ M, m * y * m⁻¹ ∈ (P : Subgroup M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hy2
  let z : M := ⟨y, hy⟩
  have hz : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨w, hw⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, Subgroup.coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    simp [z, hn]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Q P
  refine ⟨m, m.2, ⟨m * z * m⁻¹, ?_, rfl⟩⟩
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  exact ⟨z, hQ (Subgroup.mem_zpowers z), by simp [MulAut.conj_apply]⟩

theorem exists_min_order [Finite G] {M M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) (P : Sylow 2 M) :
    ∃ x ∈ (P : Subgroup M).map M.subtype, x ∉ M₁ ∧
      ∀ y ∈ M, y ∉ M₁ → (∃ n : ℕ, y ^ 2 ^ n = 1) → orderOf x ≤ orderOf y := by
  classical
  have hex : ∃ k, ∃ x ∈ (P : Subgroup M).map M.subtype, x ∉ M₁ ∧ orderOf x = k := by
    by_contra hcon
    push Not at hcon
    have hle : (P : Subgroup M) ≤ M₁.subgroupOf M := by
      intro s hs
      rw [Subgroup.mem_subgroupOf]
      by_contra h
      exact hcon _ s ⟨s, hs, rfl⟩ h rfl
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [show (M₁.subgroupOf M).index = 2 from hM₁] at hdvd
    exact P.not_dvd_index hdvd
  obtain ⟨x, hxS, hxM₁, hx⟩ := Nat.find_spec hex
  refine ⟨x, hxS, hxM₁, fun y hy hy₁ hy2 => ?_⟩
  obtain ⟨m, hm, hmy⟩ := exists_conj_mem_sylow P hy hy2
  have hconj : m * y * m⁻¹ ∉ M₁ := by
    intro h
    apply hy₁
    have e : y = m⁻¹ * (m * y * m⁻¹) * m := by group
    rw [e, mul_mem_iff_of_relIndex_two hM₁ (M.mul_mem (M.inv_mem hm) (M.mul_mem (M.mul_mem hm hy)
      (M.inv_mem hm))) hm, mul_mem_iff_of_relIndex_two hM₁ (M.inv_mem hm)
      (M.mul_mem (M.mul_mem hm hy) (M.inv_mem hm)), inv_mem_iff]
    tauto
  have hord : orderOf (m * y * m⁻¹) = orderOf y := by
    simpa using orderOf_conj_eq m⁻¹ y
  rw [hx, ← hord]
  exact Nat.find_min' hex ⟨_, hmy, hconj, rfl⟩

theorem index_ne_two_of_isSimpleGroup [Finite G] [IsSimpleGroup G] (hG2 : Nat.card G ≠ 2)
    (K : Subgroup G) : K.index ≠ 2 := by
  intro hK
  have := Subgroup.normal_of_index_eq_two hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · rw [h, Subgroup.index_bot] at hK
    exact hG2 hK
  · rw [h, Subgroup.index_top] at hK
    exact absurd hK (by norm_num)

theorem solomon_wong_one_of_index [Finite G] (hG : ∀ K : Subgroup G, K.index ≠ 2)
    {M M₁ A : Subgroup G} (P : Sylow 2 M) (hAS : A ≤ (P : Subgroup M).map M.subtype)
    (hAn : ∀ s ∈ (P : Subgroup M).map M.subtype, ∀ b ∈ A, s * b * s⁻¹ ∈ A)
    (hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b) (hA4 : ∀ b ∈ A, b ^ 4 = 1)
    (hNA : Subgroup.normalizer (A : Set G) ≤ M)
    (hsyl : ∀ g : G, conjSubgroup A g ≤ M → ∃ m ∈ M, conjSubgroup A g = conjSubgroup A m)
    (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M) :
    ∃ g : G, g ∉ M ∧ M.relIndex (conjSubgroup A g) ≤ 2 ∧ ¬ conjSubgroup A g ⊓ M ≤ M₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxS, hxM₁, hmin⟩ := exists_min_order hM₁ P
  exact exists_conj_relIndex_le_two_of_min (fun K hK => absurd hK (hG K)) hM₁ hM₁M
    (P.isPGroup'.map _) (Subgroup.map_subtype_le _) hAS hxS hAc hA4 (hAn x hxS) hNA hsyl hxM₁ hmin

theorem solomon_wong_two_of_index [Finite G] (hG : ∀ K : Subgroup G, K.index ≠ 2)
    {M M₁ A : Subgroup G} (P : Sylow 2 M) (hAS : A ≤ (P : Subgroup M).map M.subtype)
    (hAc : ∀ b ∈ A, ∀ c ∈ A, b * c = c * b) (hNA : Subgroup.normalizer (A : Set G) ≤ M)
    (hsyl : ∀ g : G, conjSubgroup A g ≤ M → ∃ m ∈ M, conjSubgroup A g = conjSubgroup A m)
    (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M) {e : G} (heA : e ∈ A) (he : e ^ 2 = 1) :
    e ∈ M₁ :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  mem_of_sq_eq_one hG hM₁ hM₁M (hAS.trans (Subgroup.map_subtype_le _))
    ((P.isPGroup'.map _).to_le hAS) hAc hNA hsyl heA he

theorem relIndex_ne_two_of_rank [Finite G] (hG : ∀ K : Subgroup G, K.index ≠ 2)
    {E : Subgroup G} (hE2 : ∀ e ∈ E, e ^ 2 = 1)
    (hsyl : ∀ g : G, conjSubgroup E g ≤ Subgroup.normalizer (E : Set G) →
      ∃ m ∈ Subgroup.normalizer (E : Set G), conjSubgroup E g = conjSubgroup E m)
    (hrank : ∀ M₁ : Subgroup G, M₁ ≤ Subgroup.normalizer (E : Set G) →
      M₁.relIndex (Subgroup.normalizer (E : Set G)) = 2 → E ≤ M₁ → ∀ B : Subgroup G,
        B ≤ Subgroup.normalizer (E : Set G) → (∀ b ∈ B, b ^ 2 = 1) → ¬ B ≤ M₁ →
          2 * Nat.card B < Nat.card E)
    {M₁ : Subgroup G} (hM₁N : M₁ ≤ Subgroup.normalizer (E : Set G)) :
    M₁.relIndex (Subgroup.normalizer (E : Set G)) ≠ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hM₁
  set N := Subgroup.normalizer (E : Set G)
  have hEc : ∀ b ∈ E, ∀ c ∈ E, b * c = c * b := fun _ hb _ hc => mul_comm_of_sq_eq_one hE2 hb hc
  have hEp : IsPGroup 2 (E.subgroupOf N) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 x.2)))⟩
  obtain ⟨P, hP⟩ := hEp.exists_le_sylow
  have hAS : E ≤ (P : Subgroup N).map N.subtype := fun e he =>
    ⟨⟨e, Subgroup.le_normalizer he⟩, hP (Subgroup.mem_subgroupOf.2 he), rfl⟩
  have hAn : ∀ s ∈ (P : Subgroup N).map N.subtype, ∀ b ∈ E, s * b * s⁻¹ ∈ E :=
    fun s hs b hb => (Subgroup.mem_normalizer_iff.1 (Subgroup.map_subtype_le _ hs) b).1 hb
  have hE4 : ∀ b ∈ E, b ^ 4 = 1 := fun b hb => by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hE2 b hb, one_pow]
  obtain ⟨g, -, hidx, hnle⟩ :=
    solomon_wong_one_of_index hG P hAS hAn hEc hE4 le_rfl hsyl hM₁ hM₁N
  have hEM₁ : E ≤ M₁ := fun e he =>
    solomon_wong_two_of_index hG P hAS hEc le_rfl hsyl hM₁ hM₁N he (hE2 e he)
  have h := hrank M₁ hM₁N hM₁ hEM₁ (conjSubgroup E g ⊓ N) inf_le_right
    (fun b hb => conjSubgroup_sq hE2 g b hb.1) hnle
  have hcard := Subgroup.relIndex_mul_card N (conjSubgroup E g)
  rw [card_conjSubgroup, inf_comm] at hcard
  have := Nat.mul_le_mul_right (Nat.card ↥(conjSubgroup E g ⊓ N)) hidx
  omega

end CFSG.EvenSmallLie.UnitarySix.SolomonWong
