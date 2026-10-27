module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped Pointwise commutatorElement

namespace GMS43

variable {D : Type} [Group D]

theorem commutatorElement_mul_right_eq (e a b : D) :
    ⁅e, a * b⁆ = ⁅e, b⁆ * ⁅b * e * b⁻¹, a⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_eq_mul_inv_conj (x w : D) : ⁅x, w⁆ = x * (w * x * w⁻¹)⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mem_of_mem_normalizer {E : Subgroup D} {w : D}
    (hw : w ∈ normalizer (E : Set D)) {e : D} (he : e ∈ E) : ⁅e, w⁆ ∈ E := by
  rw [commutatorElement_eq_mul_inv_conj]
  exact mul_mem he (inv_mem ((mem_normalizer_iff.mp hw e).mp he))

theorem commutatorElement_mul_left_of_comm {E : Subgroup D}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {w : D} (hw : w ∈ normalizer (E : Set D))
    {e₁ e₂ : D} (h₁ : e₁ ∈ E) (h₂ : e₂ ∈ E) : ⁅e₁ * e₂, w⁆ = ⁅e₁, w⁆ * ⁅e₂, w⁆ := by
  have ha := inv_mem ((mem_normalizer_iff.mp hw e₁).mp h₁)
  have hb := inv_mem ((mem_normalizer_iff.mp hw e₂).mp h₂)
  have h1 : (w * (e₁ * e₂) * w⁻¹)⁻¹ = (w * e₂ * w⁻¹)⁻¹ * (w * e₁ * w⁻¹)⁻¹ := by group
  rw [commutatorElement_eq_mul_inv_conj, commutatorElement_eq_mul_inv_conj e₁,
    commutatorElement_eq_mul_inv_conj e₂, h1]
  set a := (w * e₁ * w⁻¹)⁻¹
  set b := (w * e₂ * w⁻¹)⁻¹
  have hab : b * a = a * b := hcomm b hb a ha
  have hya : e₂ * a = a * e₂ := hcomm _ h₂ a ha
  calc e₁ * e₂ * (b * a) = e₁ * e₂ * (a * b) := by rw [hab]
    _ = e₁ * (e₂ * a) * b := by simp only [mul_assoc]
    _ = e₁ * (a * e₂) * b := by rw [hya]
    _ = e₁ * a * (e₂ * b) := by simp only [mul_assoc]

private def commutatorHom (E : Subgroup D) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (w : D)
    (hw : w ∈ normalizer (E : Set D)) : E →* D where
  toFun v := ⁅(v : D), w⁆
  map_one' := commutatorElement_one_left w
  map_mul' x y := commutatorElement_mul_left_of_comm hcomm hw x.2 y.2

theorem mem_commutator_zpowers_iff_exists {E : Subgroup D}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {w : D} (hw : w ∈ normalizer (E : Set D))
    {x : D} : x ∈ ⁅E, zpowers w⁆ ↔ ∃ e ∈ E, ⁅e, w⁆ = x := by
  refine ⟨fun hx => ?_, fun ⟨e, he, hex⟩ => hex ▸ commutator_mem_commutator he (mem_zpowers w)⟩
  set R := (commutatorHom E hcomm w hw).range
  have hmemR : ∀ y, y ∈ R ↔ ∃ e ∈ E, ⁅e, w⁆ = y := fun y =>
    ⟨fun ⟨v, hv⟩ => ⟨v, v.2, hv⟩, fun ⟨e, he, hey⟩ => ⟨⟨e, he⟩, hey⟩⟩
  let K : Subgroup D :=
    { carrier := {z | z ∈ normalizer (E : Set D) ∧ ∀ e ∈ E, ⁅e, z⁆ ∈ R}
      one_mem' := ⟨one_mem _, fun e _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
      mul_mem' := by
        rintro z₁ z₂ ⟨hz₁, hR₁⟩ ⟨hz₂, hR₂⟩
        refine ⟨mul_mem hz₁ hz₂, fun e he => ?_⟩
        rw [commutatorElement_mul_right_eq]
        exact mul_mem (hR₂ e he) (hR₁ _ ((mem_normalizer_iff.mp hz₂ e).mp he))
      inv_mem' := by
        rintro z ⟨hz, hRz⟩
        refine ⟨inv_mem hz, fun e he => ?_⟩
        have hf : z⁻¹ * e⁻¹ * z ∈ E := by
          have := (mem_normalizer_iff.mp (inv_mem hz) e⁻¹).mp (inv_mem he)
          simpa only [inv_inv] using this
        have hc : e * (z⁻¹ * e⁻¹ * z) = (z⁻¹ * e⁻¹ * z) * e := hcomm e he _ hf
        have key : ⁅e, z⁻¹⁆ = ⁅z⁻¹ * e⁻¹ * z, z⁆ := by
          calc ⁅e, z⁻¹⁆ = e * (z⁻¹ * e⁻¹ * z) := by simp only [commutatorElement_def]; group
            _ = (z⁻¹ * e⁻¹ * z) * e := hc
            _ = ⁅z⁻¹ * e⁻¹ * z, z⁆ := by simp only [commutatorElement_def]; group
        rw [key]
        exact hRz _ hf }
  have hwK : w ∈ K := ⟨hw, fun e he => (hmemR _).mpr ⟨e, he, rfl⟩⟩
  have hle : ⁅E, zpowers w⁆ ≤ R := by
    rw [commutator_le]
    intro e he z hz
    exact (zpowers_le.mpr hwK hz).2 e he
  exact (hmemR x).mp (hle hx)

theorem commutator_zpowers_mul_subset {E : Subgroup D}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {a b : D}
    (ha : a ∈ normalizer (E : Set D)) (hb : b ∈ normalizer (E : Set D)) :
    ((⁅E, zpowers (a * b)⁆ : Subgroup D) : Set D) ⊆
      ((⁅E, zpowers b⁆ : Subgroup D) : Set D) * ((⁅E, zpowers a⁆ : Subgroup D) : Set D) := by
  intro x hx
  obtain ⟨e, he, rfl⟩ := (mem_commutator_zpowers_iff_exists hcomm (mul_mem ha hb)).mp hx
  rw [commutatorElement_mul_right_eq]
  exact Set.mul_mem_mul (commutator_mem_commutator he (mem_zpowers b))
    (commutator_mem_commutator ((mem_normalizer_iff.mp hb e).mp he) (mem_zpowers a))

theorem card_commutator_mul_le [Finite D] {E : Subgroup D}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {a b : D}
    (ha : a ∈ normalizer (E : Set D)) (hb : b ∈ normalizer (E : Set D)) :
    Nat.card (⁅E, zpowers (a * b)⁆ : Subgroup D) ≤
      Nat.card (⁅E, zpowers a⁆ : Subgroup D) * Nat.card (⁅E, zpowers b⁆ : Subgroup D) := by
  calc Nat.card (⁅E, zpowers (a * b)⁆ : Subgroup D)
      = Nat.card ((⁅E, zpowers (a * b)⁆ : Subgroup D) : Set D) := rfl
    _ ≤ Nat.card (((⁅E, zpowers b⁆ : Subgroup D) : Set D) *
          ((⁅E, zpowers a⁆ : Subgroup D) : Set D)) :=
        Nat.card_mono (Set.toFinite _) (commutator_zpowers_mul_subset hcomm ha hb)
    _ ≤ Nat.card ((⁅E, zpowers b⁆ : Subgroup D) : Set D) *
          Nat.card ((⁅E, zpowers a⁆ : Subgroup D) : Set D) := Set.natCard_mul_le
    _ = Nat.card (⁅E, zpowers a⁆ : Subgroup D) * Nat.card (⁅E, zpowers b⁆ : Subgroup D) :=
        Nat.mul_comm _ _

theorem commutatorElement_commutatorElement_eq_mul_self {E : Subgroup D}
    (hE : ∀ x ∈ E, x * x = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {c : D}
    (hc : c ∈ normalizer (E : Set D)) {e : D} (he : e ∈ E) :
    ⁅⁅e, c⁆, c⁆ = ⁅e, c * c⁆ := by
  have hs : c * e * c⁻¹ ∈ E := (mem_normalizer_iff.mp hc e).mp he
  have ht : c * (c * e * c⁻¹) * c⁻¹ ∈ E := (mem_normalizer_iff.mp hc _).mp hs
  have h1 : ⁅⁅e, c⁆, c⁆ =
      e * (c * e * c⁻¹)⁻¹ * (c * (c * e * c⁻¹) * c⁻¹) * (c * e * c⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have h2 : ⁅e, c * c⁆ = e * (c * (c * e * c⁻¹) * c⁻¹)⁻¹ := by
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  rw [h1, h2]
  generalize c * e * c⁻¹ = s at hs ht ⊢
  generalize c * s * c⁻¹ = t at ht ⊢
  rw [inv_eq_of_mul_eq_one_right (hE s hs), inv_eq_of_mul_eq_one_right (hE t ht),
    mul_assoc e s t, hcomm s hs t ht, ← mul_assoc, mul_assoc (e * t) s s, hE s hs, mul_one]

theorem commutatorElement_iterate_two_pow {E : Subgroup D}
    (hE : ∀ x ∈ E, x * x = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {a : D}
    (ha : a ∈ normalizer (E : Set D)) (n : ℕ) {e : D} (he : e ∈ E) :
    (fun x => ⁅x, a⁆)^[2 ^ n] e = ⁅e, a ^ 2 ^ n⁆ := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    have hmem : ⁅e, a ^ 2 ^ n⁆ ∈ E :=
      commutatorElement_mem_of_mem_normalizer (pow_mem ha _) he
    rw [pow_succ, mul_two, Function.iterate_add_apply, ih he, ih hmem, pow_add,
      commutatorElement_commutatorElement_eq_mul_self hE hcomm (pow_mem ha _) he]

theorem mem_chain_iff {M : Type*} [Group M] (N : M →* M) (C : ℕ → Subgroup M)
    (hC0 : C 0 = ⊤) (hCs : ∀ i, C (i + 1) = (C i).map N) (i : ℕ) (v : M) :
    v ∈ C i ↔ ∃ u, N^[i] u = v := by
  induction i generalizing v with
  | zero => simp [hC0]
  | succ i ih =>
    rw [hCs i, mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, rfl⟩ := (ih w).mp hw
      exact ⟨u, Function.iterate_succ_apply' _ _ _⟩
    · rintro ⟨u, rfl⟩
      exact ⟨N^[i] u, (ih _).mpr ⟨u, rfl⟩, (Function.iterate_succ_apply' _ _ _).symm⟩

theorem two_pow_mul_card_chain_le {M : Type*} [Group M] [Finite M] (N : M →* M) {K : ℕ}
    (hK : ∀ x, N^[K] x = 1) (C : ℕ → Subgroup M) (hC0 : C 0 = ⊤)
    (hCs : ∀ i, C (i + 1) = (C i).map N) (i : ℕ) (hne : C (i + 1) ≠ ⊥) :
    2 ^ i * Nat.card (C (i + 1)) ≤ Nat.card (C 1) := by
  have hmono : ∀ i, C (i + 1) ≤ C i := by
    intro i
    induction i with
    | zero => rw [hC0]; exact le_top
    | succ i ih =>
      calc C (i + 1 + 1) = (C (i + 1)).map N := hCs _
        _ ≤ (C i).map N := map_mono ih
        _ = C (i + 1) := (hCs i).symm
  have hanti : Antitone C := antitone_nat_of_succ_le hmono
  have hbot : ∀ j, K ≤ j → C j = ⊥ := by
    intro j hj
    refine eq_bot_iff.mpr (le_trans (hanti hj) fun v hv => ?_)
    obtain ⟨u, rfl⟩ := (mem_chain_iff N C hC0 hCs K v).mp hv
    rw [hK u]
    exact one_mem _
  have hconst : ∀ i, C (i + 1) = C i → ∀ j, C (i + j) = C i := by
    intro i h j
    induction j with
    | zero => rfl
    | succ j ih => rw [← add_assoc, hCs, ih, ← hCs, h]
  have hstrict : ∀ i, C i ≠ ⊥ → 2 * Nat.card (C (i + 1)) ≤ Nat.card (C i) := by
    intro i hi
    have hlt : C (i + 1) < C i := lt_of_le_of_ne (hmono i) fun h =>
      hi (by rw [← hconst i h K]; exact hbot _ (Nat.le_add_left K i))
    obtain ⟨m, hm⟩ := card_dvd_of_le (hmono i)
    have hlt' := card_lt_of_lt hlt
    have hpos : 0 < Nat.card (C i) := Nat.card_pos
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      omega
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hm
      omega
    calc 2 * Nat.card (C (i + 1)) = Nat.card (C (i + 1)) * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card (C (i + 1)) * m := Nat.mul_le_mul_left _ (by omega)
      _ = Nat.card (C i) := hm.symm
  induction i with
  | zero => simp
  | succ i ih =>
    have hne' : C (i + 1) ≠ ⊥ := fun h => hne (eq_bot_iff.mpr ((hmono (i + 1)).trans h.le))
    calc 2 ^ (i + 1) * Nat.card (C (i + 1 + 1))
        = 2 ^ i * (2 * Nat.card (C (i + 1 + 1))) := by rw [pow_succ, mul_assoc]
      _ ≤ 2 ^ i * Nat.card (C (i + 1)) := Nat.mul_le_mul_left _ (hstrict _ hne')
      _ ≤ Nat.card (C 1) := ih hne'

theorem two_pow_mul_card_commutator_pow_le [Finite D] {E : Subgroup D}
    (hE : ∀ x ∈ E, x * x = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {a : D}
    (ha : a ∈ normalizer (E : Set D)) (ha2 : IsPGroup 2 (zpowers a)) (n : ℕ)
    (hne : ⁅E, zpowers (a ^ 2 ^ n)⁆ ≠ ⊥) :
    2 ^ (2 ^ n - 1) * Nat.card (⁅E, zpowers (a ^ 2 ^ n)⁆ : Subgroup D) ≤
      Nat.card (⁅E, zpowers a⁆ : Subgroup D) := by
  let N : E →* E := (commutatorHom E hcomm a ha).codRestrict E
    (fun v => commutatorElement_mem_of_mem_normalizer ha v.2)
  have hN : ∀ v : E, (N v : D) = ⁅(v : D), a⁆ := fun v => rfl
  have hNit : ∀ j (v : E), ((N^[j] v : E) : D) = (fun x => ⁅x, a⁆)^[j] (v : D) := by
    intro j
    induction j with
    | zero => intro v; rfl
    | succ j ih =>
      intro v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hN, ih]
  obtain ⟨K, hK⟩ := ha2 ⟨a, mem_zpowers a⟩
  have haK : a ^ 2 ^ K = 1 := by
    have := congrArg Subtype.val hK
    simpa using this
  have hNK : ∀ v : E, N^[2 ^ K] v = 1 := fun v => Subtype.ext <| by
    have h := (hNit (2 ^ K) v).trans (commutatorElement_iterate_two_pow hE hcomm ha K v.2)
    rw [haK, commutatorElement_one_right] at h
    exact h
  obtain ⟨C, hC0, hCs⟩ : ∃ C : ℕ → Subgroup E, C 0 = ⊤ ∧ ∀ i, C (i + 1) = (C i).map N :=
    ⟨fun i => Nat.rec (motive := fun _ => Subgroup E) ⊤ (fun _ H => H.map N) i, rfl,
      fun _ => rfl⟩
  have hmapC : ∀ i x, x ∈ (C i).map E.subtype ↔ ∃ e ∈ E, (fun y => ⁅y, a⁆)^[i] e = x := by
    intro i x
    rw [mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨u, rfl⟩ := (mem_chain_iff N C hC0 hCs i v).mp hv
      exact ⟨u, u.2, (hNit i u).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨N^[i] ⟨e, he⟩, (mem_chain_iff N C hC0 hCs i _).mpr ⟨⟨e, he⟩, rfl⟩, hNit i _⟩
  have h1 : (C 1).map E.subtype = ⁅E, zpowers a⁆ := by
    ext x
    rw [hmapC, mem_commutator_zpowers_iff_exists hcomm ha]
    simp only [Function.iterate_one]
  have h2 : (C (2 ^ n)).map E.subtype = ⁅E, zpowers (a ^ 2 ^ n)⁆ := by
    ext x
    rw [hmapC, mem_commutator_zpowers_iff_exists hcomm (pow_mem ha _)]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, (commutatorElement_iterate_two_pow hE hcomm ha n he).symm⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, commutatorElement_iterate_two_pow hE hcomm ha n he⟩
  have hn1 : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
  have hne' : C (2 ^ n - 1 + 1) ≠ ⊥ := by
    rw [hn1]
    intro h
    exact hne (by rw [← h2, h, Subgroup.map_bot])
  have key := two_pow_mul_card_chain_le N hNK C hC0 hCs (2 ^ n - 1) hne'
  rw [hn1] at key
  rw [← h2, ← h1, card_map_of_injective E.subtype_injective,
    card_map_of_injective E.subtype_injective]
  exact key

theorem two_pow_mul_card_commutator_mul_pow_le [Finite D] {E : Subgroup D}
    (hE : ∀ x ∈ E, x * x = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {t y : D}
    (ht : t ∈ normalizer (E : Set D)) (hy : y ∈ normalizer (E : Set D))
    (h2 : IsPGroup 2 (zpowers (t * y))) (n : ℕ) (hne : ⁅E, zpowers ((t * y) ^ 2 ^ n)⁆ ≠ ⊥) :
    2 ^ (2 ^ n - 1) * Nat.card (⁅E, zpowers ((t * y) ^ 2 ^ n)⁆ : Subgroup D) ≤
      Nat.card (⁅E, zpowers t⁆ : Subgroup D) * Nat.card (⁅E, zpowers y⁆ : Subgroup D) :=
  (two_pow_mul_card_commutator_pow_le hE hcomm (mul_mem ht hy) h2 n hne).trans
    (card_commutator_mul_le hcomm ht hy)

end GMS43

end CFSG.SeitzReduction.RankOne
