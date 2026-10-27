module

public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.RankThree.PartTwo.Sec3.MinimalCommutatorTwoGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S3.KM

open CFSG.Open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem card_modEq_card_inf_centralizer [Finite G] {p : ℕ} [hp : Fact p.Prime] {x : G}
    (hx : x ^ p = 1) {Y : Subgroup G} (hxY : x ∈ normalizer (Y : Set G)) :
    Nat.card Y ≡ Nat.card (Y ⊓ centralizer ({x} : Set G) : Subgroup G) [MOD p] := by
  classical
  set R := zpowers x with hR
  have hRY : R ≤ normalizer (Y : Set G) := zpowers_le.mpr hxY
  let := Subgroup.conjMulDistribMulActionOfLeNormalizer R Y hRY
  have hRp : IsPGroup p R := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp
      (orderOf_dvd_of_pow_eq_one (show x ^ p ^ 1 = 1 by rw [pow_one]; exact hx))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hmod := hRp.card_modEq_card_fixedPoints Y
  have hsmul : ∀ (r : R) (y : Y), ((r • y : Y) : G) = (r : G) * y * (r : G)⁻¹ := fun r y =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit R Y hRY r y
  let e : MulAction.fixedPoints R Y ≃
      (Y ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    { toFun := fun y => ⟨((y : Y) : G), Subgroup.mem_inf.mpr ⟨(y : Y).2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := congrArg Subtype.val (y.2 ⟨x, Subgroup.mem_zpowers x⟩)
        rw [hsmul] at h1
        calc ((y : Y) : G) * x = x * (y : Y) * x⁻¹ * x := by rw [h1]
          _ = x * (y : Y) := by group⟩⟩
      invFun := fun z => ⟨⟨z, (Subgroup.mem_inf.mp z.2).1⟩, fun r => by
        apply Subtype.ext
        rw [hsmul]
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp r.2
        have hc : Commute x (z : G) :=
          (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp z.2).2).symm
        have hcj : Commute (x ^ j) (z : G) := hc.zpow_left j
        rw [← hj]
        change x ^ j * (z : G) * (x ^ j)⁻¹ = z
        rw [hcj.eq, mul_inv_cancel_right]⟩
      left_inv := fun y => rfl
      right_inv := fun z => rfl }
  rwa [Nat.card_congr e] at hmod

theorem le_centralizer_of_card_lt [Finite G] {p : ℕ} (hp : p.Prime) {x : G} (hx : x ^ p = 1)
    {Y : Subgroup G} (hxY : x ∈ normalizer (Y : Set G)) (hY : Nat.card Y < p) :
    Y ≤ centralizer ({x} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := card_modEq_card_inf_centralizer hx hxY
  have hle : Nat.card (Y ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ Nat.card Y :=
    Subgroup.card_le_of_le inf_le_left
  have heq : Nat.card Y = Nat.card (Y ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have h1 : Nat.card Y % p = Nat.card (Y ⊓ centralizer ({x} : Set G) : Subgroup G) % p := h
    rwa [Nat.mod_eq_of_lt hY, Nat.mod_eq_of_lt (lt_of_le_of_lt hle hY)] at h1
  have hinf : Y ⊓ centralizer ({x} : Set G) = Y :=
    Subgroup.eq_of_le_of_card_ge inf_le_left heq.le
  exact hinf ▸ inf_le_right

theorem card_modEq_one_of_inf_centralizer_eq_bot [Finite G] {p : ℕ} (hp : p.Prime) {x : G}
    (hx : x ^ p = 1) {Y : Subgroup G} (hxY : x ∈ normalizer (Y : Set G))
    (hfix : ∀ y ∈ Y, x * y = y * x → y = 1) : Nat.card Y ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have h := card_modEq_card_inf_centralizer hx hxY
  have h1 : Nat.card (Y ⊓ centralizer ({x} : Set G) : Subgroup G) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    exact hfix y (Subgroup.mem_inf.mp hy).1
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hy).2).symm
  rwa [h1] at h

structure Ctx [Finite G] (p : ℕ) (A T : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elem : IsElemAbelian p A
  two : IsPGroup 2 T
  norm : A ≤ normalizer (T : Set G)
  faithful : ∀ a ∈ A, (∀ t ∈ T, a * t = t * a) → a = 1
  card_ge : p ^ 3 ≤ Nat.card A
  rank : ∀ E : Subgroup G, E ≤ A → ∀ k : ℕ, k ≤ 2 → Nat.card E * p ^ k = Nat.card A →
    ∀ V : Subgroup G, V ≤ T ⊓ centralizer (E : Set G) → IsElemAbelian 2 V →
      Nat.card V ≤ 2 ^ (k + 1)

@[expose] def IsHyp (p : ℕ) (A H : Subgroup G) : Prop := H ≤ A ∧ Nat.card H * p = Nat.card A

section CtxLemmas

variable [Finite G] {p : ℕ} {A T : Subgroup G}

theorem Ctx.comm (c : Ctx p A T) {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a :=
  isElemAbelian_commute c.elem ha hb

theorem Ctx.pow_p (c : Ctx p A T) {a : G} (ha : a ∈ A) : a ^ p = 1 := c.elem.2 a ha

theorem Ctx.ne_bot (c : Ctx p A T) : A ≠ ⊥ := by
  intro h
  have h1 : Nat.card A = 1 := by rw [h]; simp
  have h2 := c.card_ge
  have h3 : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) c.prime.one_lt
  omega

theorem Ctx.rank0 (c : Ctx p A T) {V : Subgroup G} (hV : V ≤ T ⊓ centralizer (A : Set G))
    (hVe : IsElemAbelian 2 V) : Nat.card V ≤ 2 := by
  have := c.rank A le_rfl 0 (by norm_num) (by simp) V hV hVe
  simpa using this

theorem Ctx.rank1 (c : Ctx p A T) {H : Subgroup G} (hH : IsHyp p A H) {V : Subgroup G}
    (hV : V ≤ T ⊓ centralizer (H : Set G)) (hVe : IsElemAbelian 2 V) : Nat.card V ≤ 4 := by
  have := c.rank H hH.1 1 (by norm_num) (by simpa using hH.2) V hV hVe
  simpa using this

theorem Ctx.rank2 (c : Ctx p A T) {E : Subgroup G} (hE : E ≤ A)
    (hcard : Nat.card E * p ^ 2 = Nat.card A) {V : Subgroup G}
    (hV : V ≤ T ⊓ centralizer (E : Set G)) (hVe : IsElemAbelian 2 V) : Nat.card V ≤ 8 := by
  have := c.rank E hE 2 le_rfl hcard V hV hVe
  simpa using this

theorem Ctx.two_ne (c : Ctx p A T) {k : ℕ} : ¬ p ∣ 2 ^ k := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq c.prime Nat.prime_two).mp (c.prime.dvd_of_dvd_pow h)
  exact c.odd this

theorem Ctx.not_dvd_card (c : Ctx p A T) {Y : Subgroup G} (hY : IsPGroup 2 Y) :
    ¬ p ∣ Nat.card Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  rw [hk]
  exact c.two_ne

end CtxLemmas

section Hyperplanes

variable [Finite G] {p : ℕ} {A H : Subgroup G}

theorem IsHyp.exists_not_mem (hp : p.Prime) (h : IsHyp p A H) : ∃ b ∈ A, b ∉ H := by
  by_contra hcon
  push Not at hcon
  have hAH : A ≤ H := hcon
  have hHA : H = A := le_antisymm h.1 hAH
  have h2 := h.2
  rw [hHA] at h2
  have hpos : 0 < Nat.card A := Nat.card_pos
  have : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [h2, mul_one])
  exact hp.one_lt.ne' this

theorem IsHyp.sup_zpowers (hp : p.Prime) (h : IsHyp p A H) {b : G} (hb : b ∈ A) (hbH : b ∉ H) :
    H ⊔ zpowers b = A := by
  have hle : H ⊔ zpowers b ≤ A := sup_le h.1 (zpowers_le.2 hb)
  set K := H ⊔ zpowers b with hK
  have hHK : H ≤ K := le_sup_left
  have hbK : b ∈ K := (le_sup_right : zpowers b ≤ K) (mem_zpowers b)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHK
  have hdvd : Nat.card K ∣ Nat.card A := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hmp : m ∣ p := by
    obtain ⟨j, hj⟩ := hdvd
    have h1 : Nat.card H * p = Nat.card H * (m * j) := by
      rw [h.2, hj, hm]; ring
    have h2 : p = m * j := Nat.eq_of_mul_eq_mul_left hpos h1
    exact ⟨j, h2⟩
  rcases (Nat.dvd_prime hp).1 hmp with h1 | h1
  · exfalso
    rw [h1, mul_one] at hm
    have hKH : K = H := (Subgroup.eq_of_le_of_card_ge hHK hm.le).symm
    exact hbH (hKH ▸ hbK)
  · have hKA : Nat.card K = Nat.card A := by rw [hm, h1, h.2]
    exact Subgroup.eq_of_le_of_card_ge hle hKA.ge

theorem IsHyp.card_inf (hp : p.Prime) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {H₁ H₂ : Subgroup G}
    (h₁ : IsHyp p A H₁) (h₂ : IsHyp p A H₂) (hne : H₁ ≠ H₂) :
    Nat.card (H₁ ⊓ H₂ : Subgroup G) * p ^ 2 = Nat.card A := by
  have hnot : ∃ b ∈ H₂, b ∉ H₁ := by
    by_contra hcon
    push Not at hcon
    have h21 : H₂ ≤ H₁ := hcon
    have hc : Nat.card H₁ = Nat.card H₂ := by
      have h1 := h₁.2
      have h2 := h₂.2
      exact Nat.eq_of_mul_eq_mul_right hp.pos (by omega)
    exact hne (Subgroup.eq_of_le_of_card_ge h21 hc.le).symm
  obtain ⟨b, hb2, hb1⟩ := hnot
  have hsup : H₁ ⊔ H₂ = A := by
    have h1 := h₁.sup_zpowers hp (h₂.1 hb2) hb1
    refine le_antisymm (sup_le h₁.1 h₂.1) ?_
    rw [← h1]
    exact sup_le_sup_left (zpowers_le.2 hb2) _
  have hH₂ : H₂ ≤ normalizer (H₁ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    have hxA := h₂.1 hx
    constructor
    · intro hy
      have := hAc x hxA y (h₁.1 hy)
      rw [show x * y * x⁻¹ = y by rw [this]; group]
      exact hy
    · intro hy
      have h3 := hAc x⁻¹ (inv_mem hxA) _ (h₁.1 hy)
      have h4 : y = x * y * x⁻¹ := by
        have h5 : y * x⁻¹ = x * y * x⁻¹ * x⁻¹ := by
          calc y * x⁻¹ = x⁻¹ * (x * y * x⁻¹) := by group
            _ = x * y * x⁻¹ * x⁻¹ := h3
        exact mul_right_cancel h5
      rw [h4]
      exact hy
  have hprod := card_sup_mul_card_inf_of_le_normalizer hH₂
  rw [hsup] at hprod
  have hpos : 0 < Nat.card A := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc Nat.card A * (Nat.card (H₁ ⊓ H₂ : Subgroup G) * p ^ 2)
      = (Nat.card A * Nat.card (H₁ ⊓ H₂ : Subgroup G)) * p ^ 2 := by ring
    _ = (Nat.card H₁ * Nat.card H₂) * p ^ 2 := by rw [hprod]
    _ = (Nat.card H₁ * p) * (Nat.card H₂ * p) := by ring
    _ = Nat.card A * Nat.card A := by rw [h₁.2, h₂.2]

end Hyperplanes

section Generation

variable [Finite G] {p : ℕ}

open CFSG in
theorem le_iSup_isHyp (hp : p.Prime) {A X : Subgroup G} (hA : IsElemAbelian p A) (hA1 : A ≠ ⊥)
    (hAX : A ≤ normalizer (X : Set G)) (hX : ¬ p ∣ Nat.card X) :
    X ≤ ⨆ (H : Subgroup G) (_ : IsHyp p A H), X ⊓ centralizer (H : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hAcomm := hA.1
  have : IsElementaryAbelian p A :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hA.2 x x.2) }
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  refine (CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hAX hX).trans ?_
  refine iSup₂_le fun B hB => ?_
  have h1 : IsHyp p A (B.map A.subtype) := by
    refine ⟨Subgroup.map_subtype_le B, ?_⟩
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    have := B.card_mul_index
    rwa [hB] at this
  exact le_iSup₂_of_le (B.map A.subtype) h1 le_rfl

theorem le_of_forall_isHyp (hp : p.Prime) {A X Y : Subgroup G} (hA : IsElemAbelian p A)
    (hA1 : A ≠ ⊥) (hAX : A ≤ normalizer (X : Set G)) (hX : ¬ p ∣ Nat.card X)
    (hY : ∀ H : Subgroup G, IsHyp p A H → X ⊓ centralizer (H : Set G) ≤ Y) : X ≤ Y :=
  (le_iSup_isHyp hp hA hA1 hAX hX).trans (iSup₂_le fun H hH => hY H hH)

theorem mem_normalizer_of_conj_mem {K : Subgroup G} {g : G} (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    g ∈ normalizer (K : Set G) :=
  CFSG.RankThree.PartTwo.Sec3.mem_normalizer_of_forall_conj_mem h

theorem le_normalizer_inf_centralizer {A H X : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hHA : H ≤ A) (hAX : A ≤ normalizer (X : Set G)) :
    A ≤ normalizer ((X ⊓ centralizer (H : Set G) : Subgroup G) : Set G) := by
  intro a ha
  apply mem_normalizer_of_conj_mem
  intro y hy
  obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.1 hy
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hAX ha) y).1 hyX, ?_⟩
  rw [mem_centralizer_iff]
  intro h hh
  have c1 : Commute h a := hAc h (hHA hh) a ha
  have c2 : Commute h y := (mem_centralizer_iff.1 hyC) h hh
  exact ((c1.mul_right c2).mul_right c1.inv_right).eq

end Generation

section Omega

variable {Q : Subgroup G}

@[expose] def omega1 (Q : Subgroup G) (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : Subgroup G where
  carrier := {x | x ∈ Q ∧ x ^ 2 = 1}
  one_mem' := ⟨Q.one_mem, one_pow 2⟩
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨Q.mul_mem ha hb, ?_⟩
    rw [Commute.mul_pow (hQ a ha b hb) 2, ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    exact ⟨Q.inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩

theorem mem_omega1 (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {x : G} :
    x ∈ omega1 Q hQ ↔ x ∈ Q ∧ x ^ 2 = 1 := Iff.rfl

theorem omega1_le (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : omega1 Q hQ ≤ Q := fun _ hx => hx.1

theorem isElemAbelian_omega1 (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) :
    IsElemAbelian 2 (omega1 Q hQ) :=
  ⟨⟨⟨fun a b => Subtype.ext (hQ a a.2.1 b b.2.1)⟩⟩, fun x hx => hx.2⟩

theorem exists_elemAbelian_card_le [Finite G] (hQ : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) {z : G}
    (hsq : ∀ x ∈ Q, x ^ 2 = 1 ∨ x ^ 2 = z) :
    ∃ V : Subgroup G, V ≤ Q ∧ IsElemAbelian 2 V ∧ Nat.card Q ≤ 2 * Nat.card V := by
  classical
  refine ⟨omega1 Q hQ, omega1_le hQ, isElemAbelian_omega1 hQ, ?_⟩
  by_cases hx₀ : ∃ x₀ ∈ Q, x₀ ^ 2 ≠ 1
  · obtain ⟨x₀, hx₀Q, hx₀2⟩ := hx₀
    have hx₀z : x₀ ^ 2 = z := (hsq x₀ hx₀Q).resolve_left hx₀2
    let f : Q → omega1 Q hQ × Bool := fun x =>
      if hx : (x : G) ^ 2 = 1 then (⟨x, x.2, hx⟩, false)
      else (⟨x * x₀⁻¹, Q.mul_mem x.2 (Q.inv_mem hx₀Q), by
        have hxz : (x : G) ^ 2 = z := (hsq x x.2).resolve_left hx
        rw [Commute.mul_pow (hQ _ x.2 _ (Q.inv_mem hx₀Q)), inv_pow, hx₀z, hxz, mul_inv_cancel]⟩,
        true)
    have hinj : Function.Injective f := by
      intro x y hxy
      have h1 := congrArg Prod.fst hxy
      have h2 := congrArg Prod.snd hxy
      by_cases hx : (x : G) ^ 2 = 1 <;> by_cases hy : (y : G) ^ 2 = 1
      · apply Subtype.ext
        simpa [f, hx, hy] using congrArg (fun w : omega1 Q hQ => (w : G)) h1
      · simp [f, hx, hy] at h2
      · simp [f, hx, hy] at h2
      · apply Subtype.ext
        have := congrArg (fun w : omega1 Q hQ => (w : G)) h1
        simp only [f, hx, hy, dite_false] at this
        exact mul_right_cancel this
    have h := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
    omega
  · push Not at hx₀
    have : Q ≤ omega1 Q hQ := fun x hx => ⟨hx, hx₀ x hx⟩
    have := Subgroup.card_le_of_le this
    omega

theorem comm_zpowers (y : G) : ∀ a ∈ zpowers y, ∀ b ∈ zpowers y, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
  rw [← zpow_add, ← zpow_add, add_comm]

theorem le_normalizer_of_commuting [Finite G] {P Y : Subgroup G}
    (hPY : ∀ x ∈ P, ∀ y ∈ Y, x * y = y * x) : Y ≤ normalizer (P : Set G) := by
  intro y hy
  apply mem_normalizer_of_conj_mem
  intro x hx
  rw [show y * x * y⁻¹ = x by rw [← hPY x hx y hy]; group]
  exact hx

theorem mem_sup_of_commuting [Finite G] {P Y : Subgroup G}
    (hPY : ∀ x ∈ P, ∀ y ∈ Y, x * y = y * x) : ∀ u ∈ P ⊔ Y, ∃ a ∈ P, ∃ b ∈ Y, u = a * b := by
  have hmul : ((P ⊔ Y : Subgroup G) : Set G) = (P : Set G) * (Y : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P Y (by
      intro x hx
      apply mem_normalizer_of_conj_mem
      intro y hy
      rw [show x * y * x⁻¹ = y by rw [hPY x hx y hy]; group]
      exact hy)
  intro u hu
  have : u ∈ ((P ⊔ Y : Subgroup G) : Set G) := hu
  rw [hmul] at this
  obtain ⟨a, ha, b, hb, rfl⟩ := this
  exact ⟨a, ha, b, hb, rfl⟩

theorem comm_sup_of_commuting [Finite G] {P Y : Subgroup G}
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (hPY : ∀ x ∈ P, ∀ y ∈ Y, x * y = y * x) : ∀ x ∈ P ⊔ Y, ∀ y ∈ P ⊔ Y, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commuting hPY x hx
  obtain ⟨c, hc, d, hd, rfl⟩ := mem_sup_of_commuting hPY y hy
  have ac : Commute a c := hP a ha c hc
  have ad : Commute a d := hPY a ha d hd
  have bc : Commute b c := (hPY c hc b hb).symm
  have bd : Commute b d := hY b hb d hd
  exact ((ac.mul_right ad).mul_left (bc.mul_right bd)).eq

theorem exists_elemAbelian_of_commuting [Finite G] {P Y : Subgroup G} {z : G} (hz : z * z = 1)
    (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hY : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x)
    (hPY : ∀ x ∈ P, ∀ y ∈ Y, x * y = y * x) (hPs : ∀ x ∈ P, x ^ 2 = 1 ∨ x ^ 2 = z)
    (hYs : ∀ x ∈ Y, x ^ 2 = 1 ∨ x ^ 2 = z) {m : ℕ} (hm : Nat.card (P ⊓ Y : Subgroup G) ≤ m) :
    ∃ V : Subgroup G, V ≤ P ⊔ Y ∧ IsElemAbelian 2 V ∧
      Nat.card P * Nat.card Y ≤ 2 * m * Nat.card V := by
  have hQs : ∀ x ∈ P ⊔ Y, x ^ 2 = 1 ∨ x ^ 2 = z := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commuting hPY x hx
    rw [Commute.mul_pow (hPY a ha b hb) 2]
    rcases hPs a ha with h1 | h1 <;> rcases hYs b hb with h2 | h2 <;> rw [h1, h2]
    · left; simp
    · right; simp
    · right; simp
    · left; exact hz
  obtain ⟨V, hVQ, hVe, hVc⟩ := exists_elemAbelian_card_le (comm_sup_of_commuting hP hY hPY) hQs
  refine ⟨V, hVQ, hVe, ?_⟩
  have hprod := card_sup_mul_card_inf_of_le_normalizer (le_normalizer_of_commuting hPY)
  calc Nat.card P * Nat.card Y = Nat.card (P ⊔ Y : Subgroup G) * Nat.card (P ⊓ Y : Subgroup G) :=
        hprod.symm
    _ ≤ (2 * Nat.card V) * m := Nat.mul_le_mul hVc hm
    _ = 2 * m * Nat.card V := by ring

theorem isElemAbelian_sup_of_commuting [Finite G] {P Y : Subgroup G} (hP : IsElemAbelian 2 P)
    (hY : IsElemAbelian 2 Y) (hPY : ∀ x ∈ P, ∀ y ∈ Y, x * y = y * x) :
    IsElemAbelian 2 (P ⊔ Y) ∧
      Nat.card (P ⊔ Y : Subgroup G) * Nat.card (P ⊓ Y : Subgroup G) = Nat.card P * Nat.card Y := by
  have hc := comm_sup_of_commuting (fun x hx y hy => isElemAbelian_commute hP hx hy)
    (fun x hx y hy => isElemAbelian_commute hY hx hy) hPY
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, fun x hx => ?_⟩,
    card_sup_mul_card_inf_of_le_normalizer (le_normalizer_of_commuting hPY)⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commuting hPY x hx
  rw [Commute.mul_pow (hPY a ha b hb) 2, hP.2 a ha, hY.2 b hb, one_mul]

theorem commute_of_sup_zpowers {A H : Subgroup G} {b : G} (hsup : H ⊔ zpowers b = A) {y : G}
    (hH : ∀ h ∈ H, h * y = y * h) (hb : b * y = y * b) : ∀ a ∈ A, a * y = y * a := by
  intro a ha
  have hle : A ≤ centralizer ({y} : Set G) := by
    rw [← hsup]
    refine sup_le (fun h hh => ?_) (zpowers_le.2 ?_)
    · rw [mem_centralizer_singleton_iff]
      exact hH h hh
    · rw [mem_centralizer_singleton_iff]
      exact hb
  have := mem_centralizer_singleton_iff.1 (hle ha)
  exact this

@[expose] def zOmega (T : Subgroup G) : Subgroup G :=
  omega1 (T ⊓ centralizer (T : Set G)) (fun x hx y hy =>
    (mem_centralizer_iff.1 hx.2 y hy.1).symm)

theorem mem_zOmega {T : Subgroup G} {x : G} :
    x ∈ zOmega T ↔ x ∈ T ∧ (∀ t ∈ T, t * x = x * t) ∧ x ^ 2 = 1 := by
  unfold zOmega
  rw [mem_omega1]
  constructor
  · rintro ⟨⟨hxT, hxC⟩, hx2⟩
    exact ⟨hxT, fun t ht => mem_centralizer_iff.1 hxC t ht, hx2⟩
  · rintro ⟨hxT, hxC, hx2⟩
    exact ⟨⟨hxT, mem_centralizer_iff.2 hxC⟩, hx2⟩

theorem zOmega_le {T : Subgroup G} : zOmega T ≤ T := fun _ hx => (mem_zOmega.1 hx).1

theorem isElemAbelian_zOmega (T : Subgroup G) : IsElemAbelian 2 (zOmega T) :=
  isElemAbelian_omega1 _

theorem le_normalizer_zOmega [Finite G] {A T : Subgroup G} (hAT : A ≤ normalizer (T : Set G)) :
    A ≤ normalizer (zOmega T : Set G) := by
  intro a ha
  apply mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨hxT, hxC, hx2⟩ := mem_zOmega.1 hx
  refine mem_zOmega.2 ⟨(mem_normalizer_iff.1 (hAT ha) x).1 hxT, fun t ht => ?_, ?_⟩
  · have ht' : a⁻¹ * t * a ∈ T := by
      have := (mem_normalizer_iff.1 (hAT (inv_mem ha)) t).1 ht
      simpa using this
    have h1 := hxC _ ht'
    calc t * (a * x * a⁻¹) = a * ((a⁻¹ * t * a) * x) * a⁻¹ := by group
      _ = a * (x * (a⁻¹ * t * a)) * a⁻¹ := by rw [h1]
      _ = a * x * a⁻¹ * t := by group
  · have : (a * x * a⁻¹) ^ 2 = a * x ^ 2 * a⁻¹ := by
      rw [pow_two, pow_two]; group
    rw [this, hx2]; group

theorem zOmega_ne_bot {T : Subgroup G} [Finite G] (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    zOmega T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  have hcn := hT.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center T)
  have hzz : (z : T) ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hT.exists_orderOf_eq_pow (z : T)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hzz (orderOf_eq_one_iff.1 (by simpa using hk))
  set w : T := (z : T) ^ (2 ^ (k - 1)) with hw
  have hwo : orderOf w = 2 := by
    rw [hw, orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk]
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    exact Nat.mul_div_cancel_left 2 (by positivity)
  have hw1 : w ≠ 1 := by
    intro h; rw [h, orderOf_one] at hwo; omega
  have hw2 : w ^ 2 = 1 := by
    rw [← hwo]; exact pow_orderOf_eq_one w
  have hwc : ∀ t : T, t * w = w * t := by
    intro t
    have hzc : Commute t (z : T) := Subgroup.mem_center_iff.1 z.2 t
    rw [hw]
    exact (Commute.pow_right hzc _).eq
  intro hbot
  have hmem : (w : G) ∈ zOmega T := by
    refine mem_zOmega.2 ⟨w.2, fun t ht => ?_, ?_⟩
    · exact congrArg Subtype.val (hwc ⟨t, ht⟩)
    · exact congrArg Subtype.val hw2
  rw [hbot, mem_bot] at hmem
  exact hw1 (Subtype.ext hmem)

end Omega

theorem isElemAbelian_zpowers {x : G} (hx : x ^ 2 = 1) : IsElemAbelian 2 (zpowers x) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · apply Subtype.ext
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 b.2
    show (a : G) * b = b * a
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem eq_of_card_le_two [Finite G] {V : Subgroup G} (hV : Nat.card V ≤ 2) {x y : G} (hx : x ∈ V)
    (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hnt : Nontrivial V := ⟨⟨⟨x, hx⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have h1 : 1 < Nat.card V := Finite.one_lt_card_iff_nontrivial.2 hnt
  have h2 : Nat.card V = 2 := by omega
  obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : V)).1 h2
  have hx' : (⟨x, hx⟩ : V) = u := hu _ (fun h => hx1 (congrArg Subtype.val h))
  have hy' : (⟨y, hy⟩ : V) = u := hu _ (fun h => hy1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (hx'.trans hy'.symm)

theorem exists_mem_ne_one {K : Subgroup G} (h : K ≠ ⊥) : ∃ f ∈ K, f ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h (eq_bot_iff.2 fun x hx => mem_bot.2 (hcon x hx))

end CFSG.LocalAnalysis.GLTheoremA.S3.KM
