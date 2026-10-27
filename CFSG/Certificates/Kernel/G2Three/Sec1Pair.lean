module

public import Certificates.Data.Kernel.G2Three.Sec1
public import CFSG.Certificates.Kernel.G2Three.Pack
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Codes
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import Mathlib

public section

set_option exponentiation.threshold 512

namespace CFSG.KC.G2Three.Sec1

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KD.G2Three CFSG.KD.G2Three.Sec1
  CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

@[expose] def OkP (x : ℕ) : Prop := Canon3 196 (x % 2 ^ 392) ∧ Canon3 196 (x / 2 ^ 392)

@[expose] def decP (x : ℕ) : Wm :=
  wdiag (mat3 14 196 (x % 2 ^ 392)) (mat3 14 196 (x / 2 ^ 392))

theorem consts_okP : consts3OK 14 5 196 LO RM CI ONE UP = true := by quickRfl

theorem split_mod {lo hi : ℕ} (h : lo < 2 ^ 392) : (lo + hi * 2 ^ 392) % 2 ^ 392 = lo := by
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

theorem split_div {lo hi : ℕ} (h : lo < 2 ^ 392) : (lo + hi * 2 ^ 392) / 2 ^ 392 = hi := by
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 392), Nat.div_eq_of_lt h, Nat.zero_add]

theorem lt_of_canon {X : ℕ} (h : Canon3 196 X) : X < 2 ^ 392 := h.1

theorem MUL_canon {a b : ℕ} (ha : Canon3 196 a) (hb : Canon3 196 b) :
    Canon3 196 (MUL a b) ∧ mat3 14 196 (MUL a b) = mat3 14 196 a * mat3 14 196 b :=
  mul3s_sound consts_okP ha hb

theorem MULP_eq (a b : ℕ) :
    MULP a b = MUL (a % 2 ^ 392) (b % 2 ^ 392) + MUL (a / 2 ^ 392) (b / 2 ^ 392) * 2 ^ 392 := by
  have hLP : LP = 2 ^ 392 - 1 := pow_sub_one_eq 392
  change MUL (a &&& LP) (b &&& LP) + MUL (a >>> 392) (b >>> 392) <<< 392 = _
  rw [hLP, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

theorem ONEP_eq : ONEP = ONE + ONE * 2 ^ 392 := by
  change ONE + ONE <<< 392 = _
  rw [Nat.shiftLeft_eq]

theorem okP_ONEP : OkP ONEP := by
  obtain ⟨h1, -⟩ := one3_sound consts_okP
  rw [OkP, ONEP_eq, split_mod (lt_of_canon h1), split_div (lt_of_canon h1)]
  exact ⟨h1, h1⟩

theorem decP_ONEP : decP ONEP = 1 := by
  obtain ⟨h1, h2⟩ := one3_sound consts_okP
  rw [decP, ONEP_eq, split_mod (lt_of_canon h1), split_div (lt_of_canon h1), h2, wdiag_one]

theorem okP_MULP {a b : ℕ} (ha : OkP a) (hb : OkP b) : OkP (MULP a b) := by
  have h1 := (MUL_canon ha.1 hb.1).1
  have h2 := (MUL_canon ha.2 hb.2).1
  rw [OkP, MULP_eq, split_mod (lt_of_canon h1), split_div (lt_of_canon h1)]
  exact ⟨h1, h2⟩

theorem decP_MULP {a b : ℕ} (ha : OkP a) (hb : OkP b) : decP (MULP a b) = decP a * decP b := by
  obtain ⟨h1, e1⟩ := MUL_canon ha.1 hb.1
  obtain ⟨-, e2⟩ := MUL_canon ha.2 hb.2
  rw [decP, decP, decP, MULP_eq, split_mod (lt_of_canon h1), split_div (lt_of_canon h1), e1, e2,
    wdiag_mul]

theorem decP_inj {a b : ℕ} (ha : OkP a) (hb : OkP b) (h : decP a = decP b) : a = b := by
  unfold decP wdiag at h
  obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.1 h
  have e1 := mat3_inj rfl ha.1 hb.1 h1
  have e2 := mat3_inj rfl ha.2 hb.2 h4
  rw [← Nat.mod_add_div a (2 ^ 392), ← Nat.mod_add_div b (2 ^ 392), e1, e2]

@[expose] def pkPc (c : List ℕ) : ℕ := pk (pcA c) + 2 ^ 392 * pk (pcB c)

theorem pkPc_parts {c : List ℕ} (hc : canonPc c = true) :
    pkPc c % 2 ^ 392 = pk (pcA c) ∧ pkPc c / 2 ^ 392 = pk (pcB c) := by
  obtain ⟨-, -, hA, -, -⟩ := canonPc_spec hc
  have hl : pk (pcA c) < 2 ^ 392 := pk_lt (canon14_iff.1 hA).1
  rw [pkPc, Nat.mul_comm]
  exact ⟨split_mod hl, split_div hl⟩

theorem okP_pkPc {c : List ℕ} (hc : canonPc c = true) : OkP (pkPc c) := by
  obtain ⟨-, -, hA, hB, -⟩ := canonPc_spec hc
  obtain ⟨e1, e2⟩ := pkPc_parts hc
  rw [OkP, e1, e2]
  exact ⟨pk_canon hA, pk_canon hB⟩

theorem decP_pkPc {c : List ℕ} (hc : canonPc c = true) (hf : pcFlag c = false) :
    decP (pkPc c) = decPc c := by
  obtain ⟨-, -, hA, hB, -⟩ := canonPc_spec hc
  obtain ⟨e1, e2⟩ := pkPc_parts hc
  rw [decP, e1, e2, mat3_pk_eq hA, mat3_pk_eq hB, decPc, hf]
  rfl

section Enc

variable {G : Type} [Group G] (ρ : G →* Wm)

@[expose] def Enc (x : ℕ) (g : G) : Prop := OkP x ∧ ρ g = decP x

theorem enc_one : Enc ρ ONEP 1 := ⟨okP_ONEP, by rw [map_one, decP_ONEP]⟩

theorem enc_mul {a b : ℕ} {g h : G} (ha : Enc ρ a g) (hb : Enc ρ b h) : Enc ρ (MULP a b) (g * h) :=
  ⟨okP_MULP ha.1 hb.1, by rw [map_mul, ha.2, hb.2, decP_MULP ha.1 hb.1]⟩

theorem enc_unique {ρ : G →* Wm} (hρ : Function.Injective ρ) {a : ℕ} {g h : G} (hg : Enc ρ a g)
    (hh : Enc ρ a h) : g = h :=
  hρ (hg.2.trans hh.2.symm)

theorem enc_inj {ρ : G →* Wm} {a b : ℕ} {g : G} (ha : Enc ρ a g) (hb : Enc ρ b g) : a = b :=
  decP_inj ha.1 hb.1 (ha.2.symm.trans hb.2)

theorem mul_eq_of_MULP {ρ : G →* Wm} (hρ : Function.Injective ρ) {a b c d : ℕ} {x y z w : G}
    (ha : Enc ρ a x) (hb : Enc ρ b y) (hc : Enc ρ c z) (hd : Enc ρ d w)
    (h : MULP a b = MULP c d) : x * y = z * w :=
  enc_unique hρ (enc_mul ρ ha hb) (by rw [h]; exact enc_mul ρ hc hd)

theorem mul_ne_of_MULP {ρ : G →* Wm} {a b c d : ℕ} {x y z w : G}
    (ha : Enc ρ a x) (hb : Enc ρ b y) (hc : Enc ρ c z) (hd : Enc ρ d w)
    (h : MULP a b ≠ MULP c d) : x * y ≠ z * w := fun e =>
  h (enc_inj (enc_mul ρ ha hb) (by rw [e]; exact enc_mul ρ hc hd))

end Enc

end CFSG.KC.G2Three.Sec1

end
