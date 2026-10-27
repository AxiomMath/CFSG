module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KMBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S3.KM

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec3 (squares)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Atom (p : ℕ) (A W : Subgroup G) (b : G) (S H : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  elem : IsElemAbelian p A
  two : IsPGroup 2 W
  hb : b ∈ A
  le : S ≤ W
  inv : A ≤ normalizer (S : Set G)
  perf : ⁅S, zpowers b⁆ = S
  ne : S ≠ ⊥
  min : ∀ V ≤ S, ⁅V, zpowers b⁆ = V → V ≠ ⊥ → V = S
  hyp : IsHyp p A H
  cent : ∀ s ∈ S, ∀ h ∈ H, h * s = s * h
  not_mem : b ∉ H

section Existence

variable {p : ℕ}

theorem isPGroup_zpowers {b : G} (hb : b ^ p = 1) : IsPGroup p (zpowers b) := fun g => ⟨1, by
  obtain ⟨i, hi⟩ := mem_zpowers_iff.1 g.2
  apply Subtype.ext
  change (g : G) ^ p ^ 1 = 1
  rw [pow_one, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]⟩

theorem le_normalizer_zpowers_of_comm {A : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {b : G} (hb : b ∈ A) : A ≤ normalizer ((zpowers b : Subgroup G) : Set G) := by
  intro a ha
  apply mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
  have : Commute a b := hAc a ha b hb
  rw [show a * b ^ i * a⁻¹ = b ^ i by
    rw [(this.zpow_right i).eq]; group]
  exact zpow_mem_zpowers b i

theorem commutator_mem_normalizer {A U V : Subgroup G} (hU : A ≤ normalizer (U : Set G))
    (hV : A ≤ normalizer (V : Set G)) : A ≤ normalizer ((⁅U, V⁆ : Subgroup G) : Set G) := by
  intro a ha
  apply mem_normalizer_of_conj_mem
  intro c hc
  exact CFSG.RankThree.PartTwo.Sec3.conj_mem_commutator (hU ha) (hV ha) hc

theorem exists_atom (hp : p.Prime) (hp2 : p ≠ 2) {A W : Subgroup G} (hA : IsElemAbelian p A)
    (hW2 : IsPGroup 2 W) (hAW : A ≤ normalizer (W : Set G)) {b : G} (hb : b ∈ A)
    (hWb : ∃ w ∈ W, b * w ≠ w * b) : ∃ S H : Subgroup G, Atom p A W b S H := by
  classical
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => isElemAbelian_commute hA ha hb
  have hA1 : A ≠ ⊥ := by
    intro h
    obtain ⟨w, -, hw⟩ := hWb
    have : b = 1 := by rw [h] at hb; exact (mem_bot.1 hb)
    exact hw (by rw [this]; simp)
  set X := zpowers b with hX
  have hXA : X ≤ A := zpowers_le.2 hb
  have hXp : IsPGroup p X := isPGroup_zpowers (hA.2 b hb)
  have hAX : A ≤ normalizer (X : Set G) := le_normalizer_zpowers_of_comm hAc hb
  have hcop : ∀ Y : Subgroup G, IsPGroup 2 Y → ¬ p ∣ Nat.card Y := by
    intro Y hY h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hY.exists_card_eq
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hidem : ∀ Y : Subgroup G, IsPGroup 2 Y → A ≤ normalizer (Y : Set G) →
      ⁅⁅Y, X⁆, X⁆ = ⁅Y, X⁆ := fun Y hY hAY =>
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp X Y hXp
      (hcop Y hY) (hXA.trans hAY)
  let P : Subgroup G → Prop := fun U =>
    U ≤ W ∧ A ≤ normalizer (U : Set G) ∧ ⁅U, X⁆ = U ∧ U ≠ ⊥
  have hP0 : P ⁅W, X⁆ := by
    refine ⟨le_normalizer_iff_commutator_le_left.mp (hXA.trans hAW), commutator_mem_normalizer hAW hAX,
      hidem W hW2 hAW, ?_⟩
    intro h
    obtain ⟨w, hw, hwb⟩ := hWb
    have h1 : ⁅w, b⁆ ∈ ⁅W, X⁆ := commutator_mem_commutator hw (mem_zpowers b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact hwb h1.symm
  obtain ⟨S, hS, hSmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min {U | P U} ⟨_, hP0⟩
  obtain ⟨hSW, hASn, hSX, hSne⟩ := hS
  have hS2 : IsPGroup 2 S := hW2.to_le hSW
  have hmin' : ∀ V : Subgroup G, P V → V ≤ S → V = S := fun V hV hVS => by
    by_contra hne
    exact hSmin V hV (lt_of_le_of_ne hVS hne)
  have hex : ∃ H : Subgroup G, IsHyp p A H ∧ ⁅S ⊓ centralizer (H : Set G), X⁆ ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hle : S ≤ centralizer (X : Set G) := by
      refine le_of_forall_isHyp hp hA hA1 hASn (hcop S hS2) (fun H hH => ?_)
      exact commutator_eq_bot_iff_le_centralizer.1 (hcon H hH)
    have h1 : ⁅S, X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 hle
    exact hSne (hSX ▸ h1)
  obtain ⟨H, hH, hHne⟩ := hex
  have hSH : S ≤ centralizer (H : Set G) := by
    set Y := S ⊓ centralizer (H : Set G) with hY
    have hAY : A ≤ normalizer (Y : Set G) := le_normalizer_inf_centralizer hAc hH.1 hASn
    have hY2 : IsPGroup 2 Y := hS2.to_le inf_le_left
    have hPU : P ⁅Y, X⁆ := by
      refine ⟨?_, commutator_mem_normalizer hAY hAX, hidem Y hY2 hAY, hHne⟩
      exact (le_normalizer_iff_commutator_le_left.mp (hXA.trans hAY)).trans
        (inf_le_left.trans hSW)
    have hle : ⁅Y, X⁆ ≤ S :=
      (le_normalizer_iff_commutator_le_left.mp (hXA.trans hAY)).trans inf_le_left
    have heq := hmin' _ hPU hle
    have : S ≤ Y := by
      rw [← heq]
      exact le_normalizer_iff_commutator_le_left.mp (hXA.trans hAY)
    exact this.trans inf_le_right
  have hcent : ∀ s ∈ S, ∀ h ∈ H, h * s = s * h := fun s hs h hh =>
    (mem_centralizer_iff.1 (hSH hs) h hh)
  have hbH : b ∉ H := by
    intro hbH
    have hle : S ≤ centralizer (X : Set G) := by
      intro s hs
      rw [mem_centralizer_iff]
      intro x hx
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hx
      have : Commute b s := (hcent s hs b hbH)
      exact ((this.zpow_left i).eq)
    exact hSne (hSX ▸ commutator_eq_bot_iff_le_centralizer.2 hle)
  refine ⟨S, H, ⟨hp, hp2, hA, hW2, hb, hSW, hASn, hSX, hSne, ?_, hH, hcent, hbH⟩⟩
  intro V hVS hVX hV1
  have hXV : X ≤ normalizer (V : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hVX.le
  have hHV : H ≤ normalizer (V : Set G) := by
    intro h hh
    apply mem_normalizer_of_conj_mem
    intro v hv
    have := hcent v (hVS hv) h hh
    rw [show h * v * h⁻¹ = v by rw [this]; group]
    exact hv
  have hAV : A ≤ normalizer (V : Set G) := by
    rw [← hH.sup_zpowers hp hb hbH]
    exact sup_le hHV hXV
  exact hmin' V ⟨hVS.trans hSW, hAV, hVX, hV1⟩ hVS

end Existence

section Consequences

variable {p : ℕ} {A W S H : Subgroup G} {b : G}

theorem Atom.pow_p (a : Atom p A W b S H) : b ^ p = 1 := a.elem.2 b a.hb

theorem Atom.isPGroup_S (a : Atom p A W b S H) : IsPGroup 2 S := a.two.to_le a.le

theorem Atom.isPGroup_X (a : Atom p A W b S H) : IsPGroup p (zpowers b) :=
  isPGroup_zpowers a.pow_p

theorem Atom.b_ne_one (a : Atom p A W b S H) : b ≠ 1 := by
  intro h
  apply a.ne
  have := a.perf
  rw [h, zpowers_one_eq_bot, commutator_bot_right] at this
  exact this.symm

theorem Atom.card_X (a : Atom p A W b S H) : Nat.card (zpowers b) = p := by
  have : Fact p.Prime := ⟨a.prime⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime a.pow_p a.b_ne_one

theorem Atom.le_normalizer_X (a : Atom p A W b S H) :
    zpowers b ≤ normalizer (S : Set G) :=
  (zpowers_le.2 a.hb).trans a.inv

theorem Atom.squares_central (a : Atom p A W b S H) {f : G} (hf : f ∈ squares S) {v : G}
    (hv : v ∈ S) : f * v = v * f :=
  CFSG.RankThree.PartTwo.Sec3.squares_commute a.prime a.odd a.isPGroup_X a.isPGroup_S
    a.le_normalizer_X a.perf a.ne a.min hf hv

theorem Atom.sq_squares (a : Atom p A W b S H) {f : G} (hf : f ∈ squares S) : f ^ 2 = 1 :=
  CFSG.RankThree.PartTwo.Sec3.sq_eq_one_of_mem_squares a.prime a.odd a.isPGroup_X a.isPGroup_S
    a.le_normalizer_X a.perf a.ne a.min hf

theorem Atom.sq_eq_one_of_comm (a : Atom p A W b S H)
    (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {u : G} (hu : u ∈ S) : u ^ 2 = 1 :=
  CFSG.RankThree.PartTwo.Sec3.sq_eq_one_of_commute a.prime a.odd a.isPGroup_X a.isPGroup_S
    a.le_normalizer_X a.perf a.ne a.min hc hu

theorem Atom.center_le_squares (a : Atom p A W b S H)
    (hnc : ¬ ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {z : G} (hz : z ∈ S)
    (hzc : ∀ v ∈ S, z * v = v * z) : z ∈ squares S :=
  CFSG.RankThree.PartTwo.Sec3.mem_squares_of_forall_commute a.prime a.odd rfl a.card_X
    a.isPGroup_X a.isPGroup_S a.le_normalizer_X a.perf a.min hnc hz hzc

theorem Atom.commutator_eq_squares (a : Atom p A W b S H) : ⁅S, S⁆ = squares S :=
  CFSG.RankThree.PartTwo.Sec3.commutator_eq_squares a.prime a.odd a.isPGroup_X a.isPGroup_S
    a.le_normalizer_X a.perf a.ne a.min

theorem Atom.squares_b (a : Atom p A W b S H) {f : G} (hf : f ∈ squares S) : b * f = f * b := by
  have h := CFSG.RankThree.PartTwo.Sec3.commutator_squares_eq_bot a.prime a.odd a.isPGroup_X
    a.isPGroup_S a.le_normalizer_X a.ne a.min
  have h1 : ⁅f, b⁆ ∈ ⁅squares S, zpowers b⁆ := commutator_mem_commutator hf (mem_zpowers b)
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem Atom.mem_squares_of_comm (a : Atom p A W b S H) {u : G} (hu : u ∈ S)
    (hbu : b * u = u * b) : u ∈ squares S := by
  refine CFSG.RankThree.PartTwo.Sec3.mem_squares_of_conj_mul_inv_mem a.prime a.odd rfl a.card_X
    a.isPGroup_S a.le_normalizer_X a.perf hu ?_
  rw [hbu, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem Atom.idem (a : Atom p A W b S H) {Y : Subgroup G} (hY : IsPGroup 2 Y)
    (hAY : A ≤ normalizer (Y : Set G)) : ⁅⁅Y, zpowers b⁆, zpowers b⁆ = ⁅Y, zpowers b⁆ := by
  have hcop : ¬ p ∣ Nat.card Y := by
    intro h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hY.exists_card_eq
    rw [hk] at h
    exact a.odd ((Nat.prime_dvd_prime_iff_eq a.prime Nat.prime_two).mp (a.prime.dvd_of_dvd_pow h))
  exact CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p a.prime _ Y
    a.isPGroup_X hcop ((zpowers_le.2 a.hb).trans hAY)

theorem Atom.squares_le (a : Atom p A W b S H) : squares S ≤ S :=
  CFSG.RankThree.PartTwo.Sec3.squares_le S

end Consequences

end CFSG.LocalAnalysis.GLTheoremA.S3.KM
