module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Defs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSymplecticCentralProduct

public section

namespace CFSG.ComponentClassification.AS81.SuzB0

open Subgroup CFSG.Open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

@[expose] def bitVec (v : ℕ) : Fin 6 → ZMod 2 := fun i => if v.testBit i then 1 else 0

theorem bitVec_xor (v w : ℕ) : bitVec (v ^^^ w) = bitVec v + bitVec w := by
  funext i
  simp only [bitVec, Nat.testBit_xor, Pi.add_apply]
  cases v.testBit i <;> cases w.testBit i <;> decide

theorem bitVec_zero : bitVec 0 = 0 := by
  funext i
  simp [bitVec]

theorem xor_lt {v w : ℕ} (hv : v < 64) (hw : w < 64) : v ^^^ w < 64 :=
  Nat.xor_lt_two_pow (n := 6) hv hw

theorem bitVec_inj : ∀ v < 64, ∀ w < 64, bitVec v = bitVec w → v = w := by
  decide

theorem exists_bitVec (u : Fin 6 → ZMod 2) : ∃ v < 64, bitVec v = u := by
  have hinj : Function.Injective fun v : Fin 64 => bitVec v := fun v w h =>
    Fin.ext (bitVec_inj v v.2 w w.2 h)
  obtain ⟨v, hv⟩ := ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by simp [ZMod.card]⟩).2 u
  exact ⟨v, v.2, hv⟩

theorem gammaBit_lt (v w : ℕ) : gammaBit v w < 2 := Nat.mod_lt _ (by norm_num)

theorem gammaBit_self : ∀ v < 64, gammaBit v v = qMinusBit v := by
  decide

theorem qMinus_bitVec : ∀ v < 64, qMinus (bitVec v) = (qMinusBit v : ZMod 2) := by
  decide

theorem qMinusBit_lt (v : ℕ) : qMinusBit v < 2 := Nat.mod_lt _ (by norm_num)

theorem polar_nondegenerate :
    ∀ v < 64, v ≠ 0 → ∃ w < 64, (gammaBit v w + gammaBit w v) % 2 = 1 := by
  decide

theorem xor_xor_cancel (u v : ℕ) : u ^^^ (u ^^^ v) = v := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem exists_xor_lt : ∀ v < 64, v ≠ 0 → ∃ i < 6, 2 ^ i ^^^ v < v := by
  decide

variable {H : Type} [Group H]

structure Coord (t : H) (q : ℕ → H) : Prop where
  t_sq : t * t = 1
  t_ne : t ≠ 1
  comm : ∀ v < 64, q v * t = t * q v
  mul : ∀ v < 64, ∀ w < 64, q v * q w = q (v ^^^ w) * t ^ gammaBit v w
  inj : ∀ v < 64, ∀ w < 64, ∀ a < 2, ∀ b < 2, q v * t ^ a = q w * t ^ b → v = w ∧ a = b

namespace Coord

variable {t : H} {q : ℕ → H} (C : Coord t q)
include C

theorem t_pow_mod (n : ℕ) : t ^ n = t ^ (n % 2) := by
  have h2 : t ^ 2 = 1 := by rw [pow_two, C.t_sq]
  conv_lhs => rw [← Nat.div_add_mod n 2, pow_add, pow_mul, h2, one_pow, one_mul]

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right C.t_sq

theorem q_zero : q 0 = 1 := by
  have h := C.mul 0 (by norm_num) 0 (by norm_num)
  have h0 : gammaBit 0 0 = 0 := by decide
  rw [h0, pow_zero, mul_one, Nat.zero_xor] at h
  exact left_eq_mul.mp h.symm

theorem comm_pow {v : ℕ} (hv : v < 64) (a : ℕ) : q v * t ^ a = t ^ a * q v :=
  ((Commute.pow_right (C.comm v hv : Commute (q v) t) a)).eq

theorem mul_mul {v w : ℕ} (hv : v < 64) (hw : w < 64) (a b : ℕ) :
    q v * t ^ a * (q w * t ^ b) = q (v ^^^ w) * t ^ ((gammaBit v w + a + b) % 2) := by
  rw [← C.t_pow_mod, show q v * t ^ a * (q w * t ^ b) = q v * (t ^ a * q w) * t ^ b by group,
    ← C.comm_pow hw, show q v * (q w * t ^ a) * t ^ b = (q v * q w) * (t ^ a * t ^ b) by group,
    C.mul v hv w hw, ← pow_add, mul_assoc, ← pow_add, add_assoc]

theorem inv_eq {v : ℕ} (hv : v < 64) (a : ℕ) :
    (q v * t ^ a)⁻¹ = q v * t ^ ((gammaBit v v + a) % 2) := by
  rw [inv_eq_iff_mul_eq_one, C.mul_mul hv hv, Nat.xor_self, C.q_zero, one_mul]
  have h : (gammaBit v v + a + (gammaBit v v + a) % 2) % 2 = 0 := by omega
  rw [h, pow_zero]

def Q : Subgroup H where
  carrier := {x | ∃ v < 64, ∃ a < 2, x = q v * t ^ a}
  mul_mem' := by
    rintro _ _ ⟨v, hv, a, -, rfl⟩ ⟨w, hw, b, -, rfl⟩
    exact ⟨v ^^^ w, xor_lt hv hw, _, Nat.mod_lt _ (by norm_num), C.mul_mul hv hw a b⟩
  one_mem' := ⟨0, by norm_num, 0, by norm_num, by rw [C.q_zero, pow_zero, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨v, hv, a, -, rfl⟩
    exact ⟨v, hv, _, Nat.mod_lt _ (by norm_num), C.inv_eq hv a⟩

theorem mem_Q_iff {x : H} : x ∈ C.Q ↔ ∃ v < 64, ∃ a < 2, x = q v * t ^ a := Iff.rfl

theorem q_mem {v : ℕ} (hv : v < 64) : q v ∈ C.Q :=
  ⟨v, hv, 0, by norm_num, by rw [pow_zero, mul_one]⟩

theorem t_mem : t ∈ C.Q := ⟨0, by norm_num, 1, by norm_num, by rw [C.q_zero, one_mul, pow_one]⟩

theorem card_Q [Finite H] : Nat.card C.Q = 128 := by
  let f : Fin 64 × Fin 2 → C.Q := fun p =>
    ⟨q p.1 * t ^ (p.2 : ℕ), p.1.val, p.1.2, p.2.val, p.2.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, a⟩ ⟨w, b⟩ h
      have h' : q v * t ^ (a : ℕ) = q w * t ^ (b : ℕ) := congrArg Subtype.val h
      obtain ⟨h1, h2⟩ := C.inj v v.2 w w.2 a a.2 b b.2 h'
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · rintro ⟨x, v, hv, a, ha, rfl⟩
      exact ⟨(⟨v, hv⟩, ⟨a, ha⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin]

open Classical in
noncomputable def psi (x : H) : Fin 6 → ZMod 2 :=
  if h : ∃ v < 64, ∃ a < 2, x = q v * t ^ a then bitVec (Classical.choose h) else 0

theorem psi_eq {v : ℕ} (hv : v < 64) {a : ℕ} (ha : a < 2) : psi (t := t) (q := q) (q v * t ^ a) =
    bitVec v := by
  unfold psi
  split_ifs with h
  · obtain ⟨hw, b, hb, hwb⟩ := Classical.choose_spec h
    exact congrArg bitVec (C.inj v hv _ hw a ha b hb hwb).1.symm
  · exact absurd ⟨v, hv, a, ha, rfl⟩ h

theorem psi_mul {x y : H} (hx : x ∈ C.Q) (hy : y ∈ C.Q) :
    psi (t := t) (q := q) (x * y) = psi (t := t) (q := q) x + psi (t := t) (q := q) y := by
  obtain ⟨v, hv, a, ha, rfl⟩ := hx
  obtain ⟨w, hw, b, hb, rfl⟩ := hy
  rw [C.mul_mul hv hw, C.psi_eq (xor_lt hv hw) (Nat.mod_lt _ (by norm_num)), C.psi_eq hv ha,
    C.psi_eq hw hb, bitVec_xor]

theorem psi_surj (u : Fin 6 → ZMod 2) : ∃ x ∈ C.Q, psi (t := t) (q := q) x = u := by
  obtain ⟨v, hv, rfl⟩ := exists_bitVec u
  exact ⟨q v, C.q_mem hv, by rw [show q v = q v * t ^ 0 by rw [pow_zero, mul_one],
    C.psi_eq hv (by norm_num)]⟩

theorem psi_eq_zero_iff {x : H} (hx : x ∈ C.Q) :
    psi (t := t) (q := q) x = 0 ↔ x ∈ zpowers t := by
  obtain ⟨v, hv, a, ha, rfl⟩ := hx
  rw [C.psi_eq hv ha]
  constructor
  · intro h
    have hv0 : v = 0 := bitVec_inj v hv 0 (by norm_num) (h.trans bitVec_zero.symm)
    rw [hv0, C.q_zero, one_mul]
    exact pow_mem (mem_zpowers t) a
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have h1 := zpow_mod_orderOf t k
    rw [orderOf_eq_prime (by rw [pow_two]; exact C.t_sq) C.t_ne, Nat.cast_ofNat] at h1
    obtain ⟨n, hn, hkn⟩ : ∃ n < 2, t ^ n = q v * t ^ a := by
      rcases Int.emod_two_eq_zero_or_one k with h0 | h0
      · exact ⟨0, by norm_num, by rw [← hk, ← h1, h0, zpow_zero, pow_zero]⟩
      · exact ⟨1, by norm_num, by rw [← hk, ← h1, h0, zpow_one, pow_one]⟩
    have := C.inj 0 (by norm_num) v hv n hn a ha (by rw [C.q_zero, one_mul, hkn])
    rw [← this.1, bitVec_zero]

theorem mul_self_eq_one_iff {x : H} (hx : x ∈ C.Q) :
    x * x = 1 ↔ qMinus (psi (t := t) (q := q) x) = 0 := by
  obtain ⟨v, hv, a, ha, rfl⟩ := hx
  rw [C.psi_eq hv ha, qMinus_bitVec v hv, C.mul_mul hv hv, Nat.xor_self, C.q_zero, one_mul,
    ← C.t_pow_mod, gammaBit_self v hv]
  have h2a : qMinusBit v + a + a = qMinusBit v + 2 * a := by ring
  rw [h2a, pow_add, pow_mul, pow_two, C.t_sq, one_pow, mul_one]
  have hq := qMinusBit_lt v
  interval_cases h : qMinusBit v
  · simp
  · simp only [pow_one, Nat.cast_one, one_ne_zero, iff_false]
    exact C.t_ne

theorem mul_inv_eq {u : ℕ} (hu : u < 64) (m n : ℕ) :
    q u * t ^ m * (q u * t ^ n)⁻¹ = t ^ ((m + n) % 2) := by
  rw [mul_inv_rev, ← inv_pow, C.t_inv, ← C.t_pow_mod,
    show q u * t ^ m * (t ^ n * (q u)⁻¹) = q u * t ^ (m + n) * (q u)⁻¹ by rw [pow_add]; group,
    C.comm_pow hu, mul_inv_cancel_right]

theorem commutator_eq {v w : ℕ} (hv : v < 64) (hw : w < 64) (a b : ℕ) :
    q v * t ^ a * (q w * t ^ b) * (q v * t ^ a)⁻¹ * (q w * t ^ b)⁻¹ =
      t ^ ((gammaBit v w + gammaBit w v) % 2) := by
  have e : q v * t ^ a * (q w * t ^ b) * (q v * t ^ a)⁻¹ * (q w * t ^ b)⁻¹ =
      (q v * t ^ a * (q w * t ^ b)) * (q w * t ^ b * (q v * t ^ a))⁻¹ := by group
  rw [e, C.mul_mul hv hw, C.mul_mul hw hv, Nat.xor_comm w v, C.mul_inv_eq (xor_lt hv hw)]
  congr 1
  omega

theorem centerIn_Q : centerIn C.Q = zpowers t := by
  refine le_antisymm (fun x hx => ?_) (zpowers_le.mpr ⟨C.t_mem, mem_centralizer_iff.mpr ?_⟩)
  · obtain ⟨hxQ, hxc⟩ := mem_inf.mp hx
    obtain ⟨v, hv, a, ha, rfl⟩ := hxQ
    by_cases hv0 : v = 0
    · rw [hv0, C.q_zero, one_mul]
      exact pow_mem (mem_zpowers t) a
    · exfalso
      obtain ⟨w, hw, hvw⟩ := polar_nondegenerate v hv hv0
      have h1 := mem_centralizer_iff.mp hxc (q w * t ^ 0) ⟨w, hw, 0, by norm_num, rfl⟩
      have h2 := C.commutator_eq hv hw a 0
      rw [hvw, pow_one] at h2
      apply C.t_ne
      rw [← h2, ← h1]
      group
  · rintro _ ⟨v, hv, a, -, rfl⟩
    rw [mul_assoc, ← pow_succ, pow_succ', ← mul_assoc, C.comm v hv, mul_assoc]

theorem orderOf_t : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact C.t_sq) C.t_ne

theorem isPGroup_Q [Finite H] : IsPGroup 2 C.Q :=
  IsPGroup.of_card (n := 7) (by rw [C.card_Q]; norm_num)

theorem mul_self_eq {v : ℕ} (hv : v < 64) (a : ℕ) :
    q v * t ^ a * (q v * t ^ a) = t ^ qMinusBit v := by
  rw [C.mul_mul hv hv, Nat.xor_self, C.q_zero, one_mul, gammaBit_self v hv,
    C.t_pow_mod (qMinusBit v)]
  congr 1
  omega

theorem sq_mem_zpowers {x : H} (hx : x ∈ C.Q) : x ^ 2 ∈ zpowers t := by
  obtain ⟨v, hv, a, -, rfl⟩ := hx
  rw [pow_two, C.mul_self_eq hv]
  exact pow_mem (mem_zpowers t) _

theorem commutator_mem_zpowers {x y : H} (hx : x ∈ C.Q) (hy : y ∈ C.Q) : ⁅x, y⁆ ∈ zpowers t := by
  obtain ⟨v, hv, a, -, rfl⟩ := hx
  obtain ⟨w, hw, b, -, rfl⟩ := hy
  rw [commutatorElement_def, C.commutator_eq hv hw]
  exact pow_mem (mem_zpowers t) _

theorem forall_comm_iff {x : H} (hx : x ∈ C.Q) : (∀ y ∈ C.Q, x * y = y * x) ↔ x ∈ zpowers t := by
  rw [← C.centerIn_Q]
  constructor
  · exact fun h => mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr fun y hy => (h y hy).symm⟩
  · exact fun h y hy => (mem_centralizer_iff.mp (mem_inf.mp h).2 y hy).symm

theorem q_one_mul_q_two : q 1 * q 2 ≠ q 2 * q 1 := by
  intro h
  apply C.t_ne
  have e := C.commutator_eq (v := 1) (w := 2) (by norm_num) (by norm_num) 0 0
  rw [show (gammaBit 1 2 + gammaBit 2 1) % 2 = 1 by decide, pow_one] at e
  simp only [pow_zero, mul_one] at e
  rw [h] at e
  rw [← e]
  group

theorem isExtraspecialPGroup_Q [Finite H] :
    IsExtraspecialPGroup 2 ↥C.Q ∧ (center ↥C.Q).map C.Q.subtype = zpowers t :=
  LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_two_of_forall C.isPGroup_Q C.t_mem
    C.orderOf_t (fun _ hx => C.forall_comm_iff hx)
    (fun _ hx _ hy => C.commutator_mem_zpowers hx hy) (fun _ hx => C.sq_mem_zpowers hx)
    ⟨q 1, C.q_mem (by norm_num), q 2, C.q_mem (by norm_num), C.q_one_mul_q_two⟩

theorem not_exists_elemAbelian (hts : noTS3 = true) :
    ¬ ∃ U : Subgroup H, U ≤ C.Q ∧ IsElemAbelian 2 U ∧ Nat.card U = 16 := by
  classical
  rintro ⟨U, hUQ, hU, hU16⟩
  set Ψ : Finset ℕ := (Finset.range 64).filter fun v => ∃ a < 2, q v * t ^ a ∈ U with hΨ
  have hmemΨ : ∀ {v : ℕ}, v ∈ Ψ ↔ v < 64 ∧ ∃ a < 2, q v * t ^ a ∈ U := by
    intro v
    rw [hΨ, Finset.mem_filter, Finset.mem_range]
  have hxor : ∀ v ∈ Ψ, ∀ w ∈ Ψ, v ^^^ w ∈ Ψ := by
    intro v hv w hw
    obtain ⟨hv, a, -, hva⟩ := hmemΨ.mp hv
    obtain ⟨hw, b, -, hwb⟩ := hmemΨ.mp hw
    refine hmemΨ.mpr ⟨xor_lt hv hw, (gammaBit v w + a + b) % 2, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← C.mul_mul hv hw]
    exact U.mul_mem hva hwb
  have hsing : ∀ v ∈ Ψ, qMinusBit v = 0 := by
    intro v hv
    obtain ⟨hv, a, -, hva⟩ := hmemΨ.mp hv
    have h1 := hU.2 _ hva
    rw [pow_two, C.mul_self_eq hv] at h1
    have := qMinusBit_lt v
    interval_cases h : qMinusBit v
    · rfl
    · rw [pow_one] at h1
      exact absurd h1 C.t_ne
  have hcard : 8 ≤ Ψ.card := by
    have key : ∀ u : U, ∃ p : ℕ × ℕ, p ∈ Ψ ×ˢ Finset.range 2 ∧ (u : H) = q p.1 * t ^ p.2 := by
      intro u
      obtain ⟨v, hv, a, ha, hu⟩ := hUQ u.2
      exact ⟨(v, a), Finset.mem_product.mpr ⟨hmemΨ.mpr ⟨hv, a, ha, hu ▸ u.2⟩,
        Finset.mem_range.mpr ha⟩, hu⟩
    choose f hf using key
    let g : U → ↥(Ψ ×ˢ Finset.range 2) := fun u => ⟨f u, (hf u).1⟩
    have hg : Function.Injective g := fun u u' h => Subtype.ext (by
      rw [(hf u).2, (hf u').2, show f u = f u' from congrArg Subtype.val h])
    have h1 := Nat.card_le_card_of_injective g hg
    rw [hU16, Nat.card_eq_finsetCard, Finset.card_product, Finset.card_range] at h1
    omega
  have hlt : ∀ v ∈ Ψ, v < 64 := fun v hv => (hmemΨ.mp hv).1
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ Ψ, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (show Ψ ⊆ {0} from fun v hv =>
      Finset.mem_singleton.mpr (hcon v hv))
    rw [Finset.card_singleton] at this
    omega
  obtain ⟨b, hb, hb0, hba⟩ : ∃ b ∈ Ψ, b ≠ 0 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have := (Finset.card_le_card (show Ψ ⊆ {0, a} from fun v hv => by
      by_cases h0 : v = 0
      · simp [h0]
      · simp [hcon v hv h0])).trans Finset.card_le_two
    omega
  obtain ⟨c, hc, hc0, hca, hcb, hcab⟩ : ∃ c ∈ Ψ, c ≠ 0 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a ^^^ b := by
    by_contra hcon
    push Not at hcon
    have := (Finset.card_le_card (show Ψ ⊆ {0, a, b, a ^^^ b} from fun v hv => by
      by_cases h0 : v = 0
      · simp [h0]
      by_cases h1 : v = a
      · simp [h1]
      by_cases h2 : v = b
      · simp [h2]
      · simp [hcon v hv h0 h1 h2])).trans Finset.card_le_four
    omega
  have h := hts
  rw [noTS3, allBelow_eq_true] at h
  have h' := h a (hlt a ha)
  rw [allBelow_eq_true] at h'
  have h'' := h' b (hlt b hb)
  rw [allBelow_eq_true] at h''
  have h3 := h'' c (hlt c hc)
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_cons, List.any_nil, Bool.or_false] at h3
  rcases h3 with ((((((h3 | h3) | h3) | h3) | h3) | h3) | h3) | h3
  · exact ha0 h3
  · exact hb0 h3
  · exact hba h3
  · exact hc0 h3
  · exact hca h3
  · exact hcb h3
  · exact hcab h3
  · have hab := hxor a ha b hb
    have hac := hxor a ha c hc
    have hbc := hxor b hb c hc
    have habc := hxor _ hab c hc
    rcases h3 with h3 | h3 | h3 | h3 | h3 | h3 | h3
    · rw [hsing a ha] at h3; exact absurd h3 (by norm_num)
    · rw [hsing b hb] at h3; exact absurd h3 (by norm_num)
    · rw [hsing c hc] at h3; exact absurd h3 (by norm_num)
    · rw [hsing _ hab] at h3; exact absurd h3 (by norm_num)
    · rw [hsing _ hac] at h3; exact absurd h3 (by norm_num)
    · rw [hsing _ hbc] at h3; exact absurd h3 (by norm_num)
    · rw [hsing _ habc] at h3; exact absurd h3 (by norm_num)

theorem isQ8Cube [Finite H] (hts : noTS3 = true) : IsQ8Cube C.Q :=
  ⟨C.isExtraspecialPGroup_Q.1, by rw [C.card_Q]; norm_num, C.not_exists_elemAbelian hts⟩

theorem mem_normalizer [Finite H] {c : H} (hct : c * t = t * c)
    (hcq : ∀ i < 6, c * q (2 ^ i) * c⁻¹ ∈ C.Q) : c ∈ normalizer (C.Q : Set H) := by
  have hctk : ∀ k : ℕ, c * t ^ k * c⁻¹ = t ^ k := fun k => by
    rw [(Commute.pow_right (hct : Commute c t) k).eq, mul_inv_cancel_right]
  have hqv : ∀ v < 64, c * q v * c⁻¹ ∈ C.Q := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro hv
      by_cases hv0 : v = 0
      · rw [hv0, C.q_zero, mul_one, mul_inv_cancel]
        exact C.Q.one_mem
      obtain ⟨i, hi, hiv⟩ := exists_xor_lt v hv hv0
      have hi64 : 2 ^ i < 64 := by
        calc 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi
          _ = 64 := by norm_num
      have hw := C.mul (2 ^ i) hi64 _ (xor_lt hi64 hv)
      rw [xor_xor_cancel] at hw
      have e : q v = q (2 ^ i) * q (2 ^ i ^^^ v) * (t ^ gammaBit (2 ^ i) (2 ^ i ^^^ v))⁻¹ := by
        rw [hw, mul_inv_cancel_right]
      have e' : c * q v * c⁻¹ = (c * q (2 ^ i) * c⁻¹) * (c * q (2 ^ i ^^^ v) * c⁻¹) *
          (c * t ^ gammaBit (2 ^ i) (2 ^ i ^^^ v) * c⁻¹)⁻¹ := by
        rw [e]
        group
      rw [e', hctk]
      exact C.Q.mul_mem (C.Q.mul_mem (hcq i hi) (ih _ hiv (xor_lt hi64 hv)))
        (C.Q.inv_mem (pow_mem C.t_mem _))
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨v, hv, a, -, rfl⟩ := hx
  rw [show c * (q v * t ^ a) * c⁻¹ = (c * q v * c⁻¹) * (c * t ^ a * c⁻¹) by group, hctk]
  exact C.Q.mul_mem (hqv v hv) (pow_mem C.t_mem _)

end Coord

end CFSG.ComponentClassification.AS81.SuzB0
