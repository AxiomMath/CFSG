module

public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.LocalAnalysis.ComponentInitial

section Fixed

variable {J A : Type*} [Group J] [Group A] [MulDistribMulAction J A]

theorem mem_fixedPointSubgroup_iff {K : Subgroup J} {a : A} :
    a ∈ CFSG.fixedPointSubgroup K A ↔ ∀ k ∈ K, k • a = a :=
  (FixedPoints.mem_subgroup K A a).trans ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

theorem smul_mem_fixedPointSubgroup {K : Subgroup J} {j : J}
    (hj : j ∈ normalizer (K : Set J)) {a : A} (ha : a ∈ CFSG.fixedPointSubgroup K A) :
    j • a ∈ CFSG.fixedPointSubgroup K A := by
  rw [mem_fixedPointSubgroup_iff] at ha ⊢
  intro k hk
  have hk' : j⁻¹ * k * j ∈ K := by
    have := (mem_normalizer_iff.mp (inv_mem hj) k).mp hk
    rwa [inv_inv] at this
  calc k • j • a = j • (j⁻¹ * k * j) • a := by rw [← mul_smul, ← mul_smul]; group
    _ = j • a := by rw [ha _ hk']

end Fixed

section Gomi

universe u v

variable {J : Type v} [Group J]

theorem commute_inv_mul_of_commutator_eq {A : Type*} [Group A] {x y w c : A}
    (hc : c ∈ center A) (h1 : x⁻¹ * y⁻¹ * x * y = c) (h2 : x⁻¹ * w⁻¹ * x * w = c) :
    x * (y⁻¹ * w) = y⁻¹ * w * x := by
  have hcg : ∀ g : A, g * c = c * g := fun g => (mem_center_iff.mp hc g)
  have e0 : y⁻¹ * x * y = x * c := by rw [← h1]; group
  have e1 : y * x * y⁻¹ = x * c⁻¹ := by
    have : x = y * x * y⁻¹ * c := by
      calc x = y * (y⁻¹ * x * y) * y⁻¹ := by group
        _ = y * (x * c) * y⁻¹ := by rw [e0]
        _ = y * x * (c * y⁻¹) := by group
        _ = y * x * (y⁻¹ * c) := by rw [hcg y⁻¹]
        _ = y * x * y⁻¹ * c := by group
    calc y * x * y⁻¹ = (y * x * y⁻¹ * c) * c⁻¹ := by group
      _ = x * c⁻¹ := by rw [← this]
  have e2 : x * w = w * x * c := by rw [← h2]; group
  calc x * (y⁻¹ * w) = y⁻¹ * (y * x * y⁻¹) * w := by group
    _ = y⁻¹ * (x * c⁻¹) * w := by rw [e1]
    _ = y⁻¹ * (x * w) * c⁻¹ := by
        have : c⁻¹ * w = w * c⁻¹ := by
          have := hcg w
          calc c⁻¹ * w = c⁻¹ * (w * c) * c⁻¹ := by group
            _ = c⁻¹ * (c * w) * c⁻¹ := by rw [this]
            _ = w * c⁻¹ := by group
        calc y⁻¹ * (x * c⁻¹) * w = y⁻¹ * x * (c⁻¹ * w) := by group
          _ = y⁻¹ * x * (w * c⁻¹) := by rw [this]
          _ = y⁻¹ * (x * w) * c⁻¹ := by group
    _ = y⁻¹ * w * x := by rw [e2]; group

variable {p : ℕ} [Fact p.Prime]

theorem commute_of_le_fixedPointSubgroup [Finite J] {A : Type*} [Group A] [Finite A]
    [MulDistribMulAction J A] (hA : IsPGroup p A) (hJ : ¬ p ∣ Nat.card J) {J₁ J₂ : Subgroup J}
    (hJ₁₂ : J₁ ≤ normalizer (J₂ : Set J))
    (hprod : ∀ a : A, ∃ x ∈ CFSG.fixedPointSubgroup J₁ A, ∃ y ∈ CFSG.fixedPointSubgroup J₂ A,
      a = x * y)
    (hinf : CFSG.fixedPointSubgroup J₁ A ⊓ CFSG.fixedPointSubgroup J₂ A = ⊥) {N : Subgroup A}
    (hNZ : N ≤ center A) (hNX : N ≤ CFSG.fixedPointSubgroup J₁ A)
    (hcomm : ∀ x ∈ CFSG.fixedPointSubgroup J₁ A, ∀ y ∈ CFSG.fixedPointSubgroup J₂ A,
      x⁻¹ * y⁻¹ * x * y ∈ N) :
    ∀ x ∈ CFSG.fixedPointSubgroup J₁ A, ∀ y ∈ CFSG.fixedPointSubgroup J₂ A, x * y = y * x := by
  set X := CFSG.fixedPointSubgroup J₁ A
  set Y := CFSG.fixedPointSubgroup J₂ A
  have hJ₁ : ¬ p ∣ Nat.card J₁ := fun h => hJ (h.trans (card_subgroup_dvd_card J₁))
  have hYinv : ∀ j ∈ J₁, ∀ y ∈ Y, j • y ∈ Y := fun j hj y hy =>
    smul_mem_fixedPointSubgroup (hJ₁₂ hj) hy
  have hgen : ∀ a : A, ∀ j ∈ J₁, ∃ y ∈ Y, a⁻¹ * (j • a) = y⁻¹ * (j • y) := by
    intro a j hj
    obtain ⟨x, hx, y, hy, rfl⟩ := hprod a
    refine ⟨y, hy, ?_⟩
    rw [smul_mul', (mem_fixedPointSubgroup_iff.mp hx) j hj]
    group
  have hDY : actionCommutator J₁ (⊤ : Subgroup A) ≤ Y := by
    refine (closure_le _).2 ?_
    rintro _ ⟨a, -, j, rfl⟩
    obtain ⟨y, hy, he⟩ := hgen a j j.2
    change a⁻¹ * ((j : J) • a) ∈ Y
    rw [he]
    exact Y.mul_mem (Y.inv_mem hy) (hYinv j j.2 y hy)
  have hYD : ∀ y ∈ Y, y ∈ actionCommutator J₁ (⊤ : Subgroup A) := by
    intro y hy
    obtain ⟨d, hd, c, hc, rfl⟩ :=
      (coprime_pgroup_commutator_factorization (A := J₁) Fact.out hA hJ₁).1 y
    have hcX : c ∈ X := mem_fixedPointSubgroup_iff.mpr fun k hk => hc ⟨k, hk⟩
    have hcY : c ∈ Y := by
      have := Y.mul_mem (Y.inv_mem (hDY hd)) hy
      rwa [inv_mul_cancel_left] at this
    have hc1 : c = 1 := by
      have : c ∈ X ⊓ Y := ⟨hcX, hcY⟩
      rwa [hinf, mem_bot] at this
    rwa [hc1, mul_one]
  intro x hx y hy
  have hxD : actionCommutator J₁ (⊤ : Subgroup A) ≤ centralizer ({x} : Set A) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨a, -, j, rfl⟩
    obtain ⟨y', hy', he⟩ := hgen a j j.2
    change a⁻¹ * ((j : J) • a) ∈ centralizer ({x} : Set A)
    rw [he, mem_centralizer_singleton_iff]
    have hc := hcomm x hx y' hy'
    have hcj : (j : J) • (x⁻¹ * y'⁻¹ * x * y') = x⁻¹ * y'⁻¹ * x * y' :=
      (mem_fixedPointSubgroup_iff.mp (hNX hc)) j j.2
    have hxj : (j : J) • x = x := (mem_fixedPointSubgroup_iff.mp hx) j j.2
    rw [smul_mul', smul_mul', smul_mul', smul_inv', smul_inv', hxj] at hcj
    exact (commute_inv_mul_of_commutator_eq (hNZ hc) rfl hcj).symm
  exact (mem_centralizer_singleton_iff.mp (hxD (hYD y hy))).symm

theorem le_fixedPointSubgroup_of_inf_eq_bot {A : Type*} [Group A] [MulDistribMulAction J A]
    {J₁ J₂ : Subgroup J} (hJ₁₂ : J₁ ≤ normalizer (J₂ : Set J))
    (hprod : ∀ a : A, ∃ x ∈ CFSG.fixedPointSubgroup J₁ A, ∃ y ∈ CFSG.fixedPointSubgroup J₂ A,
      a = x * y)
    (hinf : CFSG.fixedPointSubgroup J₁ A ⊓ CFSG.fixedPointSubgroup J₂ A = ⊥) {N : Subgroup A}
    (hN : ∀ j ∈ J₁, ∀ n ∈ N, j • n ∈ N) (hNY : N ⊓ CFSG.fixedPointSubgroup J₂ A = ⊥) :
    N ≤ CFSG.fixedPointSubgroup J₁ A := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hprod z
  have hyX : y ∈ CFSG.fixedPointSubgroup J₁ A := by
    rw [mem_fixedPointSubgroup_iff]
    intro j hj
    have hxj : j • x = x := (mem_fixedPointSubgroup_iff.mp hx) j hj
    have h1 : (x * y)⁻¹ * (j • (x * y)) = y⁻¹ * (j • y) := by
      rw [smul_mul', hxj]
      group
    have hmem : y⁻¹ * (j • y) ∈ N ⊓ CFSG.fixedPointSubgroup J₂ A := by
      refine ⟨h1 ▸ N.mul_mem (N.inv_mem hz) (hN j hj _ hz), ?_⟩
      exact (CFSG.fixedPointSubgroup J₂ A).mul_mem ((CFSG.fixedPointSubgroup J₂ A).inv_mem hy)
        (smul_mem_fixedPointSubgroup (hJ₁₂ hj) hy)
    rw [hNY, mem_bot] at hmem
    exact (inv_mul_eq_one.mp hmem).symm
  have hy1 : y = 1 := by
    have : y ∈ CFSG.fixedPointSubgroup J₁ A ⊓ CFSG.fixedPointSubgroup J₂ A := ⟨hyX, hy⟩
    rwa [hinf, mem_bot] at this
  rw [hy1, mul_one]
  exact hx

theorem commutator_mem_of_quotient [Finite J] {A : Type u} [Group A] [Finite A]
    [MulDistribMulAction J A]
    (hA : IsPGroup p A) (hJ : ¬ p ∣ Nat.card J) {J₁ J₂ : Subgroup J} (hsup : J₁ ⊔ J₂ = ⊤)
    (N : Subgroup A) [N.Normal] (hN : CFSG.IsInvariant J A N)
    (hprod : ∀ a : A, ∃ x ∈ CFSG.fixedPointSubgroup J₁ A, ∃ y ∈ CFSG.fixedPointSubgroup J₂ A,
      ∃ n ∈ N, a = x * y * n)
    (hinf : CFSG.fixedPointSubgroup J₁ A ⊓ CFSG.fixedPointSubgroup J₂ A ≤ N)
    (hT : letI : MulDistribMulAction J (A ⧸ N) := CFSG.quotientMulDistribMulAction N hN
      (∀ a : A ⧸ N, ∃ x ∈ CFSG.fixedPointSubgroup J₁ (A ⧸ N),
        ∃ y ∈ CFSG.fixedPointSubgroup J₂ (A ⧸ N), a = x * y) →
      CFSG.fixedPointSubgroup J₁ (A ⧸ N) ⊓ CFSG.fixedPointSubgroup J₂ (A ⧸ N) = ⊥ →
      ∀ x ∈ CFSG.fixedPointSubgroup J₁ (A ⧸ N), ∀ y ∈ CFSG.fixedPointSubgroup J₂ (A ⧸ N),
        x * y = y * x) :
    ∀ x ∈ CFSG.fixedPointSubgroup J₁ A, ∀ y ∈ CFSG.fixedPointSubgroup J₂ A,
      x⁻¹ * y⁻¹ * x * y ∈ N := by
  let : MulDistribMulAction J (A ⧸ N) := CFSG.quotientMulDistribMulAction N hN
  let : MulAction.QuotientAction J N := CFSG.quotientAction_of_isInvariant N hN
  have hmk : ∀ (j : J) (a : A), j • (a : A ⧸ N) = ((j • a : A) : A ⧸ N) := fun j a =>
    MulAction.Quotient.smul_coe (H := N) j a
  have hfixmk : ∀ {K : Subgroup J} {a : A}, a ∈ CFSG.fixedPointSubgroup K A →
      (a : A ⧸ N) ∈ CFSG.fixedPointSubgroup K (A ⧸ N) := by
    intro K a ha
    rw [mem_fixedPointSubgroup_iff] at ha ⊢
    intro k hk
    rw [hmk, ha k hk]
  have hprod' : ∀ a : A ⧸ N, ∃ x ∈ CFSG.fixedPointSubgroup J₁ (A ⧸ N),
      ∃ y ∈ CFSG.fixedPointSubgroup J₂ (A ⧸ N), a = x * y := by
    intro a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨x, hx, y, hy, n, hn, rfl⟩ := hprod a
    refine ⟨x, hfixmk hx, y, hfixmk hy, ?_⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  have hinf' : CFSG.fixedPointSubgroup J₁ (A ⧸ N) ⊓ CFSG.fixedPointSubgroup J₂ (A ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨ha₁, ha₂⟩
    have hfix : a ∈ CFSG.fixedPointSubgroup J (A ⧸ N) := by
      rw [CFSG.fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro j
      have hle : J₁ ⊔ J₂ ≤ MulAction.stabilizer J a :=
        sup_le (fun k hk => (mem_fixedPointSubgroup_iff.mp ha₁) k hk)
          (fun k hk => (mem_fixedPointSubgroup_iff.mp ha₂) k hk)
      rw [hsup] at hle
      exact hle (mem_top j)
    have hsolv : Group.IsSolvable A := by
      have := hA.isNilpotent
      infer_instance
    have hcop : Nat.Coprime (Nat.card J) (Nat.card A) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hA
      rw [hk]
      exact Nat.Coprime.pow_right _
        (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hJ))
    rw [CFSG.fixedPointSubgroup_quotient_eq_map_of_solvable_coprime (G := A) (A := J) hsolv hcop
      N hN] at hfix
    obtain ⟨c, hc, rfl⟩ := hfix
    have hcJ : ∀ (K : Subgroup J), c ∈ CFSG.fixedPointSubgroup K A := fun K =>
      mem_fixedPointSubgroup_iff.mpr fun k _ => (FixedPoints.mem_subgroup J A c).mp hc k
    rw [mem_bot]
    exact (QuotientGroup.eq_one_iff c).mpr (hinf ⟨hcJ J₁, hcJ J₂⟩)
  intro x hx y hy
  have h := (hT hprod' hinf' _ (hfixmk hx) _ (hfixmk hy)).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  simpa [mul_assoc] using h

theorem gomi_commute [Finite J] {A : Type u} [Group A] [Finite A] [MulDistribMulAction J A]
    (hA : IsPGroup p A) (hJ : ¬ p ∣ Nat.card J) {J₁ J₂ : Subgroup J} [J₁.Normal] [J₂.Normal]
    (hsup : J₁ ⊔ J₂ = ⊤)
    (hprod : ∀ a : A, ∃ x ∈ CFSG.fixedPointSubgroup J₁ A, ∃ y ∈ CFSG.fixedPointSubgroup J₂ A,
      a = x * y)
    (hinf : CFSG.fixedPointSubgroup J₁ A ⊓ CFSG.fixedPointSubgroup J₂ A = ⊥) :
    ∀ x ∈ CFSG.fixedPointSubgroup J₁ A, ∀ y ∈ CFSG.fixedPointSubgroup J₂ A, x * y = y * x := by
  have hJ₁₂ : J₁ ≤ normalizer (J₂ : Set J) := fun j _ => (normalizer_eq_top_iff.mpr ‹_›).ge
    (mem_top j)
  have hJ₂₁ : J₂ ≤ normalizer (J₁ : Set J) := fun j _ => (normalizer_eq_top_iff.mpr ‹_›).ge
    (mem_top j)
  let P : ℕ → Prop := fun n => ∀ (A : Type u) [Group A] [Finite A] [MulDistribMulAction J A],
    Nat.card A = n → IsPGroup p A →
    (∀ a : A, ∃ x ∈ CFSG.fixedPointSubgroup J₁ A, ∃ y ∈ CFSG.fixedPointSubgroup J₂ A,
      a = x * y) →
    CFSG.fixedPointSubgroup J₁ A ⊓ CFSG.fixedPointSubgroup J₂ A = ⊥ →
    ∀ x ∈ CFSG.fixedPointSubgroup J₁ A, ∀ y ∈ CFSG.fixedPointSubgroup J₂ A, x * y = y * x
  suffices hP : ∀ n, P n from hP _ A rfl hA hprod hinf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ hn hA hprod hinf
  set X := CFSG.fixedPointSubgroup J₁ A
  set Y := CFSG.fixedPointSubgroup J₂ A
  rcases subsingleton_or_nontrivial A with hA1 | hA1
  · intro x _ y _
    exact Subsingleton.elim _ _
  have hZinv : ∀ (j : J), ∀ z ∈ center A, j • z ∈ center A := by
    intro j z hz
    rw [mem_center_iff] at hz ⊢
    intro g
    have h1 := hz (j⁻¹ • g)
    calc g * j • z = j • ((j⁻¹ • g) * z) := by rw [smul_mul', smul_inv_smul]
      _ = j • (z * (j⁻¹ • g)) := by rw [h1]
      _ = j • z * g := by rw [smul_mul', smul_inv_smul]
  have hex : ∃ m, ∃ N : Subgroup A, N ≤ center A ∧ (∀ (j : J), ∀ z ∈ N, j • z ∈ N) ∧
      N ≠ ⊥ ∧ Nat.card N = m := by
    have : Nontrivial (center A) := hA.center_nontrivial
    exact ⟨_, center A, le_rfl, hZinv, (nontrivial_iff_ne_bot _).mp this, rfl⟩
  classical
  obtain ⟨N, hNZ, hNinv, hN1, hNcard⟩ := Nat.find_spec hex
  have hmin : ∀ N' : Subgroup A, N' ≤ center A → (∀ (j : J), ∀ z ∈ N', j • z ∈ N') →
      N' ≠ ⊥ → Nat.card N ≤ Nat.card N' := by
    intro N' h1 h2 h3
    rw [hNcard]
    exact Nat.find_min' hex ⟨N', h1, h2, h3, rfl⟩
  have hNn : N.Normal := ⟨fun z hz g => by
    rw [mem_center_iff.mp (hNZ hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hNinv' : CFSG.IsInvariant J A N := ⟨fun j z => ⟨fun hz => hNinv j z hz,
    fun hz => by simpa using hNinv j⁻¹ _ hz⟩⟩
  have hcomm : ∀ x ∈ X, ∀ y ∈ Y, x⁻¹ * y⁻¹ * x * y ∈ N := by
    refine commutator_mem_of_quotient hA hJ hsup N hNinv' (fun a => ?_) ?_ ?_
    · obtain ⟨x, hx, y, hy, rfl⟩ := hprod a
      exact ⟨x, hx, y, hy, 1, N.one_mem, by rw [mul_one]⟩
    · rw [hinf]
      exact bot_le
    · let : MulDistribMulAction J (A ⧸ N) := CFSG.quotientMulDistribMulAction N hNinv'
      have hlt : Nat.card (A ⧸ N) < n := by
        rw [← hn, card_eq_card_quotient_mul_card_subgroup N]
        have h1 : 1 < Nat.card N := (one_lt_card_iff_ne_bot N).mpr hN1
        have h0 : 0 < Nat.card (A ⧸ N) := Nat.card_pos
        nlinarith
      exact ih _ hlt (A ⧸ N) rfl (hA.to_quotient N)
  have hNYinv : ∀ (j : J), ∀ z ∈ N ⊓ Y, j • z ∈ N ⊓ Y := fun j z hz =>
    ⟨hNinv j z hz.1, smul_mem_fixedPointSubgroup ((normalizer_eq_top_iff.mpr ‹J₂.Normal›).ge
      (mem_top j)) hz.2⟩
  by_cases hNY : N ⊓ Y = ⊥
  · exact commute_of_le_fixedPointSubgroup hA hJ hJ₁₂ hprod hinf hNZ
      (le_fixedPointSubgroup_of_inf_eq_bot hJ₁₂ hprod hinf (fun j _ => hNinv j) hNY) hcomm
  · have hNYeq : N ⊓ Y = N := eq_of_le_of_card_ge inf_le_left
      (hmin _ (inf_le_left.trans hNZ) hNYinv hNY)
    have hNle : N ≤ Y := hNYeq ▸ inf_le_right
    have hprod' : ∀ a : A, ∃ y ∈ Y, ∃ x ∈ X, a = y * x := by
      intro a
      obtain ⟨x, hx, y, hy, h⟩ := hprod a⁻¹
      exact ⟨y⁻¹, Y.inv_mem hy, x⁻¹, X.inv_mem hx, by rw [← mul_inv_rev, ← h, inv_inv]⟩
    have hcomm' : ∀ y ∈ Y, ∀ x ∈ X, y⁻¹ * x⁻¹ * y * x ∈ N := by
      intro y hy x hx
      have := N.inv_mem (hcomm x hx y hy)
      simpa [mul_assoc] using this
    intro x hx y hy
    exact (commute_of_le_fixedPointSubgroup hA hJ hJ₂₁ hprod' (by rw [inf_comm]; exact hinf)
      hNZ hNle hcomm' y hy x hx).symm

theorem gomi_commutator_mem [Finite J] {A : Type u} [Group A] [Finite A] [MulDistribMulAction J A]
    (hA : IsPGroup p A) (hJ : ¬ p ∣ Nat.card J) {J₁ J₂ : Subgroup J} [J₁.Normal] [J₂.Normal]
    (hsup : J₁ ⊔ J₂ = ⊤) (N : Subgroup A) [N.Normal] (hN : CFSG.IsInvariant J A N)
    (hprod : ∀ a : A, ∃ x ∈ CFSG.fixedPointSubgroup J₁ A, ∃ y ∈ CFSG.fixedPointSubgroup J₂ A,
      ∃ n ∈ N, a = x * y * n)
    (hinf : CFSG.fixedPointSubgroup J₁ A ⊓ CFSG.fixedPointSubgroup J₂ A ≤ N) :
    ∀ x ∈ CFSG.fixedPointSubgroup J₁ A, ∀ y ∈ CFSG.fixedPointSubgroup J₂ A,
      x⁻¹ * y⁻¹ * x * y ∈ N := by
  let : MulDistribMulAction J (A ⧸ N) := CFSG.quotientMulDistribMulAction N hN
  exact commutator_mem_of_quotient hA hJ hsup N hN hprod hinf
    (gomi_commute (hA.to_quotient N) hJ hsup)

end Gomi

section Conj

variable {G : Type*} [Group G]

@[expose, reducible] def conjMulDistribMulAction {H A : Subgroup G}
    (hHA : H ≤ normalizer (A : Set G)) : MulDistribMulAction H A :=
  MulDistribMulAction.compHom A (inclusion hHA)

theorem conjMulDistribMulAction_smul {H A : Subgroup G} (hHA : H ≤ normalizer (A : Set G))
    (h : H) (a : A) :
    letI := conjMulDistribMulAction hHA
    ((h • a : A) : G) = h * a * (h : G)⁻¹ :=
  rfl

theorem mem_fixedPointSubgroup_conj_iff {H A K : Subgroup G} (hHA : H ≤ normalizer (A : Set G))
    (hKH : K ≤ H) (a : A) :
    letI := conjMulDistribMulAction hHA
    a ∈ CFSG.fixedPointSubgroup (K.subgroupOf H) A ↔ (a : G) ∈ centralizer (K : Set G) := by
  let := conjMulDistribMulAction hHA
  rw [mem_fixedPointSubgroup_iff, mem_centralizer_iff]
  constructor
  · intro h k hk
    have := congrArg Subtype.val (h ⟨k, hKH hk⟩ (mem_subgroupOf.mpr hk))
    rw [conjMulDistribMulAction_smul] at this
    calc k * a = k * a * k⁻¹ * k := by group
      _ = a * k := by rw [this]
  · intro h k hk
    apply Subtype.ext
    rw [conjMulDistribMulAction_smul, h _ (mem_subgroupOf.mp hk), mul_inv_cancel_right]

theorem gomi_commutator_mem_conj [Finite G] {p : ℕ} [Fact p.Prime] {A N J₁ J₂ : Subgroup G}
    (hA : IsPGroup p A) (hJ : ¬ p ∣ Nat.card (J₁ ⊔ J₂ : Subgroup G))
    (hJA : J₁ ⊔ J₂ ≤ normalizer (A : Set G)) (hJN : J₁ ⊔ J₂ ≤ normalizer (N : Set G))
    (hJ₁₂ : J₁ ≤ normalizer (J₂ : Set G)) (hJ₂₁ : J₂ ≤ normalizer (J₁ : Set G))
    (hNA : N ≤ A) (hAN : A ≤ normalizer (N : Set G))
    (hprod : ∀ a ∈ A, ∃ x ∈ A ⊓ centralizer (J₁ : Set G), ∃ y ∈ A ⊓ centralizer (J₂ : Set G),
      ∃ n ∈ N, a = x * y * n)
    (hinf : (A ⊓ centralizer (J₁ : Set G)) ⊓ (A ⊓ centralizer (J₂ : Set G)) ≤ N) :
    ∀ x ∈ A ⊓ centralizer (J₁ : Set G), ∀ y ∈ A ⊓ centralizer (J₂ : Set G),
      x⁻¹ * y⁻¹ * x * y ∈ N := by
  set H := J₁ ⊔ J₂
  let := conjMulDistribMulAction hJA
  have h₁ : J₁ ≤ H := le_sup_left
  have h₂ : J₂ ≤ H := le_sup_right
  have hK₁ : (J₁.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer h₁).mpr (sup_le le_normalizer hJ₂₁)
  have hK₂ : (J₂.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer h₂).mpr (sup_le hJ₁₂ le_normalizer)
  have hsup : J₁.subgroupOf H ⊔ J₂.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup h₁ h₂, subgroupOf_self]
  have hN' : (N.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hNA).mpr hAN
  have hNinv : CFSG.IsInvariant H A (N.subgroupOf A) := by
    refine ⟨fun h a => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, conjMulDistribMulAction_smul]
    exact mem_normalizer_iff.mp (hJN h.2) a
  have hfix : ∀ (K : Subgroup G), K ≤ H → ∀ a : A,
      a ∈ CFSG.fixedPointSubgroup (K.subgroupOf H) A ↔ (a : G) ∈ centralizer (K : Set G) :=
    fun K hK a => mem_fixedPointSubgroup_conj_iff hJA hK a
  have key := gomi_commutator_mem (J := H) (A := A) (hA := hA) hJ hsup (N.subgroupOf A) hNinv
    (fun a => ?_) ?_
  · intro x hx y hy
    have := key ⟨x, hx.1⟩ ((hfix _ h₁ _).mpr hx.2) ⟨y, hy.1⟩ ((hfix _ h₂ _).mpr hy.2)
    exact mem_subgroupOf.mp this
  · obtain ⟨x, hx, y, hy, n, hn, he⟩ := hprod a a.2
    exact ⟨⟨x, hx.1⟩, (hfix _ h₁ _).mpr hx.2, ⟨y, hy.1⟩, (hfix _ h₂ _).mpr hy.2,
      ⟨n, hNA hn⟩, mem_subgroupOf.mpr hn, Subtype.ext he⟩
  · rintro a ⟨ha₁, ha₂⟩
    exact mem_subgroupOf.mpr (hinf ⟨⟨a.2, (hfix _ h₁ _).mp ha₁⟩, ⟨a.2, (hfix _ h₂ _).mp ha₂⟩⟩)

theorem gomi_commute_conj [Finite G] {p : ℕ} [Fact p.Prime] {A J₁ J₂ : Subgroup G}
    (hA : IsPGroup p A) (hJ : ¬ p ∣ Nat.card (J₁ ⊔ J₂ : Subgroup G))
    (hJA : J₁ ⊔ J₂ ≤ normalizer (A : Set G))
    (hJ₁₂ : J₁ ≤ normalizer (J₂ : Set G)) (hJ₂₁ : J₂ ≤ normalizer (J₁ : Set G))
    (hprod : ∀ a ∈ A, ∃ x ∈ A ⊓ centralizer (J₁ : Set G), ∃ y ∈ A ⊓ centralizer (J₂ : Set G),
      a = x * y)
    (hinf : (A ⊓ centralizer (J₁ : Set G)) ⊓ (A ⊓ centralizer (J₂ : Set G)) = ⊥) :
    ∀ x ∈ A ⊓ centralizer (J₁ : Set G), ∀ y ∈ A ⊓ centralizer (J₂ : Set G), x * y = y * x := by
  intro x hx y hy
  have hbot : ∀ g : G, g ∈ normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact mem_top g
  have h := gomi_commutator_mem_conj (N := ⊥) hA hJ hJA (fun g _ => hbot g)
    hJ₁₂ hJ₂₁ bot_le (fun g _ => hbot g)
    (fun a ha => by
      obtain ⟨x, hx, y, hy, he⟩ := hprod a ha
      exact ⟨x, hx, y, hy, 1, one_mem _, by rw [mul_one, he]⟩) hinf.le x hx y hy
  rw [mem_bot] at h
  calc x * y = x * y * (x⁻¹ * y⁻¹ * x * y)⁻¹ := by rw [h, inv_one, mul_one]
    _ = y * x := by group

theorem yamada_central_product [Finite G] {p : ℕ} [Fact p.Prime] {A X : Subgroup G}
    (hA : IsPGroup p A) (hX : ¬ p ∣ Nat.card X) (hXA : X ≤ normalizer (A : Set G))
    (hn : A ≤ normalizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G)) :
    (∀ a ∈ A, ∃ d ∈ ⁅X, A⁆, ∃ c ∈ A ⊓ centralizer (X : Set G), a = d * c) ∧ ⁅X, A⁆ ≤ A ∧
      ⁅X, A⁆ ≤ centralizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  let := conjMulDistribMulAction hXA
  have hDle : actionCommutator X (⊤ : Subgroup A) ≤ (⁅X, A⁆).subgroupOf A := by
    refine (closure_le _).2 ?_
    rintro _ ⟨a, -, x, rfl⟩
    change ((a⁻¹ * (x • a) : A) : G) ∈ ⁅X, A⁆
    rw [coe_mul, conjMulDistribMulAction_smul, commutator_comm]
    have h := commutator_mem_commutator (a⁻¹ : A).2 x.2
    rw [commutatorElement_def] at h
    simpa [mul_assoc] using h
  have hfac := (coprime_pgroup_commutator_factorization (A := X) (Q := A) Fact.out hA hX).1
  refine ⟨fun a ha => ?_, ?_,
    CFSG.LocalAnalysis.EvenBN.Common.commutator_le_centralizer_of_le_normalizer hn⟩
  · obtain ⟨d, hd, c, hc, he⟩ := hfac ⟨a, ha⟩
    refine ⟨d, mem_subgroupOf.mp (hDle hd), c, ⟨c.2, ?_⟩, congrArg Subtype.val he⟩
    have hc' : c ∈ CFSG.fixedPointSubgroup ((X.subgroupOf X)) A := by
      rw [mem_fixedPointSubgroup_iff]
      intro k _
      exact (FixedPoints.mem_subgroup X A c).mp hc ⟨k, k.2⟩
    exact (mem_fixedPointSubgroup_conj_iff hXA le_rfl c).mp hc'
  · rw [commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    exact A.mul_mem ((mem_normalizer_iff.mp (hXA hx) a).mp ha) (A.inv_mem ha)

theorem le_centralizer_of_yamada [Finite G] {p : ℕ} [Fact p.Prime] {A X : Subgroup G}
    (hA : IsPGroup p A) (hX : ¬ p ∣ Nat.card X) (hXA : X ≤ normalizer (A : Set G))
    (hn : A ≤ normalizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G))
    (hab : ∀ c ∈ A ⊓ centralizer (X : Set G), ∀ c' ∈ A ⊓ centralizer (X : Set G),
      c * c' = c' * c) :
    A ≤ centralizer ((A ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hfac, -, hcen⟩ := yamada_central_product hA hX hXA hn
  intro a ha
  obtain ⟨d, hd, c, hc, rfl⟩ := hfac a ha
  refine mul_mem (hcen hd) ?_
  rw [mem_centralizer_iff]
  intro c' hc'
  exact hab c' hc' c hc

end Conj

end CFSG.LocalAnalysis.EvenBN.U4
