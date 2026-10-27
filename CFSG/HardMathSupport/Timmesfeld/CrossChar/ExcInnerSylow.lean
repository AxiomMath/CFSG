module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.SeitzGeneration.ExcTorusE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE7One
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Six
public import CFSG.LieType.SeitzGeneration.ExcTorusE8One
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Six

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge Polynomial
open scoped Matrix

theorem not_dvd_of_dvd_720 {p x : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hx : x ∣ 720) : ¬ p ∣ x := by
  intro h
  have h1 : p ∣ (2 ^ 4 * 3 ^ 2) * 5 := by
    have : ((2 : ℕ) ^ 4 * 3 ^ 2) * 5 = 720 := by norm_num
    rw [this]
    exact h.trans hx
  have hq : ∀ q : ℕ, q.Prime → ∀ k, p ∣ q ^ k → p = q := fun q hq k hk =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hk)
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · have := hq 2 Nat.prime_two 4 h3
      omega
    · have := hq 3 Nat.prime_three 2 h3
      omega
  · have := hq 5 Nat.prime_five 1 (by rwa [pow_one])
    omega

theorem not_dvd_of_dvd_5040 {p x : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (hx : x ∣ 5040) :
    ¬ p ∣ x := by
  intro h
  have h1 : p ∣ 720 * 7 := by
    have : (720 : ℕ) * 7 = 5040 := by norm_num
    rw [this]
    exact h.trans hx
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
  · exact not_dvd_of_dvd_720 hp (by omega) (dvd_refl 720) h2
  · have := Nat.le_of_dvd (by norm_num) h2
    omega

theorem not_dvd_div_of_720 {p e : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) {D : List ℕ}
    (h : ∀ d ∈ D, e ∣ d → d / e ∣ 720) : ∀ d ∈ D, e ∣ d → ¬ p ∣ d / e :=
  fun d hd hed => not_dvd_of_dvd_720 hp h7 (h d hd hed)

theorem not_dvd_div_of_5040 {p e : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) {D : List ℕ}
    (h : ∀ d ∈ D, e ∣ d → d / e ∣ 5040) : ∀ d ∈ D, e ∣ d → ¬ p ∣ d / e :=
  fun d hd hed => not_dvd_of_dvd_5040 hp h11 (h d hd hed)

theorem not_dvd_of_blocks {p e : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) {ds : List ℕ}
    (h : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3, 4, 6]) : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d :=
  fun d hd hde => not_dvd_small hp (by omega) (h d hd hde)

theorem mul_comm_of_sylowTorus {G : Type*} [Group G] {p m : ℕ} (h : SylowTorus G p m)
    {P : Subgroup G} (hP : IsPGroup p P) {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    a * b = b * a := by
  obtain ⟨T, -, hT, hconj, -⟩ := h.exists_torus
  obtain ⟨g, hg⟩ := hconj P hP
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 (hg ha)
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 (hg hb)
  have hxy : x * y = y * x :=
    congrArg (fun z : T => (z : G)) (hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hxy]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

theorem eq_of_three_le_degCount_E6 {e : ℕ} (h : 3 ≤ degCount Tag.E6 e) :
    e = 1 ∨ e = 2 ∨ e = 3 := by
  have hle := le_thirty_of_degCount_pos (τ := Tag.E6) (e := e) (by simp) (by omega)
  interval_cases e <;> revert h <;> decide

theorem eq_of_three_le_degCount_E7 {e : ℕ} (h : 3 ≤ degCount Tag.E7 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6 := by
  have hle := le_thirty_of_degCount_pos (τ := Tag.E7) (e := e) (by simp) (by omega)
  interval_cases e <;> revert h <;> decide

theorem eq_of_three_le_degCount_E8 {e : ℕ} (h : 3 ≤ degCount Tag.E8 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have hle := le_thirty_of_degCount_pos (τ := Tag.E8) (e := e) (by simp) (by omega)
  interval_cases e <;> revert h <;> decide

theorem eq_of_three_le_degCountTw {e : ℕ} (h : 3 ≤ degCountTw e) : e = 1 ∨ e = 2 ∨ e = 6 := by
  have hle := le_sixty_of_degCountTw_pos (by omega : 0 < degCountTw e)
  interval_cases e <;> revert h <;> decide

section Blocks


theorem sylowTorus_of_blocks_of_three_lt {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : IsWeylMatrix τ M)
    (ds : List ℕ) {e : ℕ} (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hpow : M ^ e = 1) (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e)
    (hother : ∀ d ∈ ds, d ≠ e → ¬ p ∣ d)
    (hdeg : ∀ d ∈ degreesE τ, e ∣ d → ¬ p ∣ d / e)
    (hcount : ((degreesE τ).filter fun d => e ∣ d).length = ds.count e) :
    SylowTorus (adjointGroup τ K) p (ds.count e) := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have hn : ¬ p ∣ e := not_dvd_of_orderOf hp hpq he
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcard : ∀ d ∈ degreesE τ, 0 < d := by
    rcases hτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hR : ¬ (p : ℤ) ∣ (((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod).eval
      (Nat.card K : ℤ) := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [eval_list_prod, hpz.dvd_prod_iff]
    rintro ⟨a, ha, hpa⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    rw [List.mem_filter] at hd
    have hde : d ≠ e := by simpa using hd.2
    exact not_dvd_cyclotomic_eval_of_ne hp he hde (hother d hd.1 hde) hpa
  have hord : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      (p ^ (Nat.card K ^ e - 1).factorization p) ^ ds.count e := by
    rw [ordProj_card_adjointGroup_E (by rcases hτ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hp
      hp3 hpq, prod_ordProj_pow_sub_one hp (by omega) hpq hq2 he (degreesE τ)
      (fun d hd hed => ⟨(hcard d hd).ne', hdeg d hd hed⟩), hcount]
  exact sylowTorus_untwisted d hτ K hp hp3 hpq hM _ he0 hpow hn hchar' he hR hord

theorem sylowTorus_twistedE6_of_blocks_of_three_lt {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ ℓ ^ f)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    (ds : List ℕ) {n e e' : ℕ} (hchar : M.charpoly = (ds.map fun d => cyclotomic d ℤ).prod)
    (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hnd : n = e ∨ n ∈ [1, 2, 3, 4, 6])
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e)
    (he' : orderOf (((-((ℓ ^ f : ℕ) : ℤ) : ℤ)) : ZMod p) = e')
    (hΦ : ∀ x : ℤ, ((cyclotomic e' ℤ).eval (-x)).natAbs = ((cyclotomic e ℤ).eval x).natAbs)
    (hso : ∀ d ∈ ds, d ≠ e → d ∈ [1, 2, 3, 4, 6])
    (hdeg : ∀ d ∈ degreesE Tag.E6, e' ∣ d → ¬ p ∣ d / e')
    (hcount : ((degreesE Tag.E6).filter fun d => e' ∣ d).length = ds.count e) :
    SylowTorus (twistedE6RootGroup K σ) p (ds.count e) := by
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have h5 := five_le_of_three_lt hp hp3
  have hn : ¬ p ∣ n := by
    rcases hnd with rfl | hn
    · exact not_dvd_of_orderOf hp hpq he
    · exact not_dvd_small hp h5 hn
  have hchar' : M.charpoly = cyclotomic e ℤ ^ ds.count e *
      ((ds.filter fun d => d ≠ e).map fun d => cyclotomic d ℤ).prod := by
    rw [hchar, prod_cyclotomic_split e ds]
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  set Q : ℤ := -((ℓ ^ f : ℕ) : ℤ) with hQdef
  have hQ2 : 2 ≤ Q.natAbs := by simpa [hQdef] using hq2
  have hpQ : ¬ (p : ℤ) ∣ Q := fun h => hpq (Int.natCast_dvd_natCast.1 (by simpa [hQdef] using h))
  have he'0 : e' ≠ 0 := by
    have hQ0 : (Q : ZMod p) ≠ 0 := fun h => hpQ ((ZMod.intCast_zmod_eq_zero_iff_dvd Q p).1 h)
    have : Fact p.Prime := ⟨hp⟩
    intro h0
    have hdvd := he' ▸ ZMod.orderOf_dvd_card_sub_one hQ0
    rw [h0, zero_dvd_iff] at hdvd
    have := hp.one_lt
    omega
  have hord : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      (p ^ ((ℓ ^ f) ^ e - 1).factorization p) ^ ds.count e := by
    have hD : ∀ d ∈ degreesE Tag.E6, e' ∣ d → d ≠ 0 ∧ ¬ p ∣ d / e' := fun d hd hed =>
      ⟨by have : ∀ d ∈ degreesE Tag.E6, 0 < d := by decide
          exact (this d hd).ne', hdeg d hd hed⟩
    rw [ordProj_card_twistedE6 hℓ hf K hK σ hσ hp hp3 hpq,
      prod_ordProj_int_pow_sub_one hp (by omega) hQ2 hpQ he' (degreesE Tag.E6) hD, hcount,
      ← ordProj_cyclotomic_int_eval hp hQ2 he' he'0]
    have h1 := ordProj_cyclotomic_eval hp hq2 he he0
    have h2 : ((cyclotomic e' ℤ).eval Q).natAbs =
        ((cyclotomic e ℤ).eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
      have := hΦ ((ℓ ^ f : ℕ) : ℤ)
      simpa [hQdef] using this
    rw [h2, h1]
  have hR := not_dvd_cyclotomic_eval_of_mem_small hp h5 he ds hso
  exact sylowTorus_twistedE6 hℓ hf K hK σ hσ hp hp3 hpq v hv _ hn0 hpow hn hchar' he hR hord

end Blocks

section Adjoint


theorem exists_sylowTorus_E6 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card K)
    (hcnt : 3 ≤ degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p))) :
    ∃ m, SylowTorus (adjointGroup Tag.E6 K) p m := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have hp3 : 3 < p := by omega
  rcases eq_of_three_le_degCount_E6 hcnt with rfl | rfl | rfl
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E6 e6OneWord) [1, 1, 1, 1, 1, 1] e6One_charpoly e6One_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2] e6Two_charpoly e6Two_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3] e6Three_charpoly e6Three_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩

theorem exists_sylowTorus_E7 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card K)
    (hcnt : 3 ≤ degCount Tag.E7 (orderOf ((Nat.card K : ℕ) : ZMod p)))
    (hsmall : 11 ≤ p ∨ 3 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) :
    ∃ m, SylowTorus (adjointGroup Tag.E7 K) p m := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt hsmall
  have hp3 : 3 < p := by omega
  rcases eq_of_three_le_degCount_E7 hcnt with rfl | rfl | rfl | rfl
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E7 e7OneWord) [1, 1, 1, 1, 1, 1, 1] e7One_charpoly e7One_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_5040 hp (by omega) (by decide))
      (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E7 e7TwoWord) [2, 2, 2, 2, 2, 2, 2] e7Two_charpoly e7Two_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_5040 hp (by omega) (by decide))
      (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3] e7Three_charpoly e7Three_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6] e7Six_charpoly e7Six_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩

theorem exists_sylowTorus_E8 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h7 : 7 ≤ p) (hpq : ¬ p ∣ Nat.card K)
    (hcnt : 3 ≤ degCount Tag.E8 (orderOf ((Nat.card K : ℕ) : ZMod p)))
    (hsmall : 11 ≤ p ∨ 3 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) :
    ∃ m, SylowTorus (adjointGroup Tag.E8 K) p m := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt hsmall
  have hp3 : 3 < p := by omega
  rcases eq_of_three_le_degCount_E8 hcnt with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E8 e8OneWord) [1, 1, 1, 1, 1, 1, 1, 1] e8One_charpoly
      e8One_pow he (not_dvd_of_blocks hp h7 (by decide))
      (not_dvd_div_of_5040 hp (by omega) (by decide)) (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E8 e8TwoWord) [2, 2, 2, 2, 2, 2, 2, 2] e8Two_charpoly
      e8Two_pow he (not_dvd_of_blocks hp h7 (by decide))
      (not_dvd_div_of_5040 hp (by omega) (by decide)) (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E8 e8ThreeWord) [3, 3, 3, 3] e8Three_charpoly e8Three_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E8 e8FourWord) [4, 4, 4, 4] e8Four_charpoly e8Four_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩
  · exact ⟨_, sylowTorus_of_blocks_of_three_lt 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3 hpq
      (IsWeylMatrix.of_word Tag.E8 e8SixWord) [6, 6, 6, 6] e8Six_charpoly e8Six_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide))
      (by decide)⟩

theorem exists_sylowTorus_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (h7 : 7 ≤ p) (hpq : ¬ p ∣ ℓ ^ f)
    (hcnt : 3 ≤ degCountTw (orderOf (((ℓ ^ f : ℕ)) : ZMod p))) :
    ∃ m, SylowTorus (twistedE6RootGroup K σ) p m := by
  obtain ⟨e, he⟩ : ∃ e, orderOf (((ℓ ^ f : ℕ)) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have hp3 : 3 < p := by omega
  have he' := orderOf_neg_natCast_zmod hp (by omega) hpq he
  rcases eq_of_three_le_degCountTw hcnt with rfl | rfl | rfl
  · rw [show ennola 1 = 2 by decide] at he'
    have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
        toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
      rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
        Matrix.mulVec_mulVec]
    have hΦ : ∀ x : ℤ, ((cyclotomic 2 ℤ).eval (-x)).natAbs =
        ((cyclotomic 1 ℤ).eval x).natAbs := fun x => by
      rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
        show -x + 1 = -(x - 1) by ring, Int.natAbs_neg]
    exact ⟨_, sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
      [1, 1, 1, 1, 2, 2] twE6One_charpoly (by norm_num) twE6One_pow (Or.inr (by decide)) he he'
      hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)⟩
  · rw [show ennola 2 = 1 by decide] at he'
    have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) • x =
        toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
      rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
        Matrix.mulVec_mulVec]
    have hΦ : ∀ x : ℤ, ((cyclotomic 1 ℤ).eval (-x)).natAbs =
        ((cyclotomic 2 ℤ).eval x).natAbs := fun x => by
      rw [cyclotomic_two, cyclotomic_one, eval_add, eval_sub, eval_X, eval_one, eval_X, eval_one,
        show -x - 1 = -(x + 1) by ring, Int.natAbs_neg]
    exact ⟨_, sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
      [2, 2, 2, 2, 2, 2] twE6Two_charpoly (by norm_num) twE6Two_pow (Or.inr (by decide)) he he'
      hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)⟩
  · rw [show ennola 6 = 3 by decide] at he'
    have hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) • x =
        toMat TwistTag.E6.tag.rank twE6SixMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
      rw [wordProd_smul_eq_wordMat_mulVec, twE6Six_wordMat, toMat_lmul, permLattice_E6_eq,
        Matrix.mulVec_mulVec]
    have hΦ : ∀ x : ℤ, ((cyclotomic 3 ℤ).eval (-x)).natAbs =
        ((cyclotomic 6 ℤ).eval x).natAbs := fun x => by
      rw [cyclotomic_six_eq, cyclotomic_three_eq]
      simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
      congr 1
      ring
    exact ⟨_, sylowTorus_twistedE6_of_blocks_of_three_lt hℓ hf K hK σ hσ hp hp3 hpq _ hv
      [6, 6, 6] twE6Six_charpoly (by norm_num) twE6Six_pow (Or.inr (by decide)) he he'
      hΦ (by decide) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)⟩

end Adjoint

section Catalogue


theorem exists_sylowTorus_cat_E6 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p))) :
    ∃ m, SylowTorus (Cat ⟨.E6 q, hv⟩) p m := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt
  obtain ⟨m, hm⟩ := exists_sylowTorus_E6 K hp h7 hpK hcnt
  exact ⟨m, hm.of_mulEquiv e.symm⟩

theorem exists_sylowTorus_cat_E7 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)))
    (hsmall : 11 ≤ p ∨ 3 ≤ orderOf ((q.card : ℕ) : ZMod p)) :
    ∃ m, SylowTorus (Cat ⟨.E7 q, hv⟩) p m := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt hsmall
  obtain ⟨m, hm⟩ := exists_sylowTorus_E7 K hp h7 hpK hcnt hsmall
  exact ⟨m, hm.of_mulEquiv e.symm⟩

theorem exists_sylowTorus_cat_E8 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hpq : p ≠ q.p)
    (hcnt : 3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)))
    (hsmall : 11 ≤ p ∨ 3 ≤ orderOf ((q.card : ℕ) : ZMod p)) :
    ∃ m, SylowTorus (Cat ⟨.E8 q, hv⟩) p m := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at hcnt hsmall
  obtain ⟨m, hm⟩ := exists_sylowTorus_E8 K hp h7 hpK hcnt hsmall
  exact ⟨m, hm.of_mulEquiv e.symm⟩

theorem exists_sylowTorus_cat_twistedE6 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hpq : p ≠ q.p) (hcnt : 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p))) :
    ∃ m, SylowTorus (Cat ⟨.twistedE6 q, hv⟩) p m := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hpK : ¬ p ∣ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact not_dvd_card_of_ne hp hpq
  rw [TauCeti.PrimePower.card_def] at hcnt
  obtain ⟨m, hm⟩ := exists_sylowTorus_twistedE6 q.prime_p q.exponent_pos K hK σ hσ hp h7 hpK hcnt
  exact ⟨m, hm.of_mulEquiv e.symm⟩

end Catalogue

end CFSG.HardMathSupport.Timmesfeld.CrossChar
