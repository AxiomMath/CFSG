module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowDef
public import CFSG.LocalAnalysis.OddStandard.AltStdSecSylowGam
public import Mathlib.Data.Nat.BitIndices
import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def BlockType : List ℕ → Type
  | [] => Empty
  | a :: l => (Fin a → Z2) ⊕ BlockType l

noncomputable instance instFintypeBlockType : (l : List ℕ) → Fintype (BlockType l)
  | [] => inferInstanceAs (Fintype Empty)
  | a :: l => haveI := instFintypeBlockType l;
      inferInstanceAs (Fintype ((Fin a → Z2) ⊕ BlockType l))

noncomputable instance instDecEqBlockType : (l : List ℕ) → DecidableEq (BlockType l)
  | [] => inferInstanceAs (DecidableEq Empty)
  | a :: l => haveI := instDecEqBlockType l;
      inferInstanceAs (DecidableEq ((Fin a → Z2) ⊕ BlockType l))

theorem card_BlockType : ∀ l : List ℕ, Fintype.card (BlockType l) = (l.map (fun a => 2 ^ a)).sum
  | [] => by
    show Fintype.card Empty = _
    simp
  | a :: l => by
    show Fintype.card ((Fin a → Z2) ⊕ BlockType l) = _
    rw [Fintype.card_sum, card_BlockType l]
    simp

noncomputable def embG : (l : List ℕ) → Gam l →* Equiv.Perm (BlockType l)
  | [] => 1
  | a :: l => (Equiv.Perm.sumCongrHom (Fin a → Z2) (BlockType l)).comp
      ((repW a).prodMap (embG l))

theorem embG_injective : ∀ l : List ℕ, Function.Injective (embG l)
  | [] => fun x y _ => Subsingleton.elim _ _
  | a :: l => by
    have h1 := repW_injective a
    have h2 := embG_injective l
    have h3 : Function.Injective ((repW a).prodMap (embG l)) := by
      intro x y hxy
      have := Prod.ext_iff.1 hxy
      exact Prod.ext (h1 this.1) (h2 this.2)
    exact Equiv.Perm.sumCongrHom_injective.comp h3

theorem sign_embG : ∀ (l : List ℕ) (γ : Gam l), Equiv.Perm.sign (embG l γ) = sgG l γ
  | [], γ => by
    have h1 : sgG [] γ = 1 := sgG_nil γ
    have h2 : embG [] γ = 1 := Equiv.ext fun x => nomatch (x : Empty)
    rw [h1, h2, map_one]
  | a :: l, ⟨x, γ⟩ => by
    show Equiv.Perm.sign (Equiv.Perm.sumCongr (repW a x) (embG l γ)) = sgG (a :: l) (Gam.cons x γ)
    rw [sgG_cons, Equiv.Perm.sign_sumCongr, sign_embG l γ, sgW_apply]

theorem card_Gam : ∀ l : List ℕ, Nat.card (Gam l) = 2 ^ (l.map (fun a => 2 ^ a - 1)).sum
  | [] => by
    show Nat.card PUnit = _
    simp
  | a :: l => by
    show Nat.card (W a × Gam l) = _
    rw [Nat.card_prod, card_W a, card_Gam l, List.map_cons, List.sum_cons, pow_add]

theorem digits_sum_eq_length (n : ℕ) : (Nat.digits 2 n).sum = n.bitIndices.length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
      · have hm : 0 < m := by omega
        rw [Nat.digits_def' (by norm_num) hn, List.sum_cons, Nat.bitIndices_two_mul,
          List.length_map]
        have := ih m (by omega)
        simp [this]
      · rw [Nat.digits_def' (by norm_num) hn, List.sum_cons, Nat.bitIndices_two_mul_add_one,
          List.length_cons, List.length_map]
        have := ih m (by omega)
        have h1 : (2 * m + 1) % 2 = 1 := by omega
        have h2 : (2 * m + 1) / 2 = m := by omega
        rw [h1, h2, this]
        omega

theorem sum_sub_one_bitIndices (n : ℕ) :
    (n.bitIndices.map (fun a => 2 ^ a - 1)).sum = n - n.bitIndices.length := by
  have h1 : ∀ l : List ℕ, (l.map (fun a => 2 ^ a - 1)).sum + l.length =
      (l.map (fun a => 2 ^ a)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      omega
  have h2 := h1 n.bitIndices
  rw [Nat.sum_map_two_pow_bitIndices] at h2
  omega

theorem card_Gam_bitIndices (n : ℕ) :
    Nat.card (Gam n.bitIndices) = 2 ^ ((Nat.factorial n).factorization 2) := by
  rw [card_Gam, sum_sub_one_bitIndices, Nat.factorization_def _ Nat.prime_two]
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [digits_sum_eq_length] at h
  simpa using h.symm

theorem card_roots_model {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n))) {Γ : Type*} [Group Γ]
    [Finite Γ] (σ : Γ →* ℤˣ) (ι : Γ →* Equiv.Perm (Fin n)) (hι : Function.Injective ι)
    (hsign : ∀ γ, Equiv.Perm.sign (ι γ) = σ γ) (hP : ∀ x, x ∈ P ↔ ∃ γ, ι γ = x) (ε : ℤˣ)
    (w : Equiv.Perm (Fin n)) (γw : Γ) (hγw : ι γw = w) :
    Nat.card {s : P // Equiv.Perm.sign (s : Equiv.Perm (Fin n)) = ε ∧
      (s : Equiv.Perm (Fin n)) ^ 2 = w} = rootCount σ ε γw := by
  unfold rootCount
  symm
  let F : {γ : Γ // σ γ = ε ∧ γ * γ = γw} →
      {s : P // Equiv.Perm.sign (s : Equiv.Perm (Fin n)) = ε ∧
        (s : Equiv.Perm (Fin n)) ^ 2 = w} := fun γ =>
    ⟨⟨ι γ.1, (hP _).2 ⟨γ.1, rfl⟩⟩, by
      show Equiv.Perm.sign (ι γ.1) = ε
      rw [hsign]
      exact γ.2.1, by
      show (ι γ.1) ^ 2 = w
      rw [← hγw, sq, ← map_mul, γ.2.2]⟩
  refine Nat.card_eq_of_bijective F ⟨?_, ?_⟩
  · intro a b hab
    have h1 : ι a.1 = ι b.1 := congrArg (fun s => ((s.1 : P) : Equiv.Perm (Fin n))) hab
    exact Subtype.ext (hι h1)
  · rintro ⟨⟨s, hs⟩, hs1, hs2⟩
    obtain ⟨γ, rfl⟩ := (hP s).1 hs
    have h1 : σ γ = ε := by rw [← hsign]; exact hs1
    have h2 : γ * γ = γw := by
      apply hι
      rw [map_mul, hγw, ← sq]
      exact hs2
    exact ⟨⟨γ, h1, h2⟩, rfl⟩

theorem exists_big_bitIndex (n : ℕ) (hn : 8 ≤ n) : ∃ a ∈ n.bitIndices, 3 ≤ a := by
  by_contra h
  push Not at h
  have : n < 2 ^ 3 := Nat.lt_pow_two_of_testBit n (fun i hi => by
    by_contra hb
    have hb' : n.testBit i = true := by simpa using hb
    have := h i (Nat.mem_bitIndices.2 hb')
    omega)
  omega

end CFSG.OddStandard.AltStdSec.SylowSn

namespace CFSG.OddStandard.AltStdSec

open CFSG.OddStandard.AltStdSec.SylowSn

theorem oddRootCount_of_le (n : ℕ) (hn : 8 ≤ n) : OddRootCount n := by
  classical
  intro P hP hmax y hyP hyc hys hy1 hy2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set l := n.bitIndices with hl
  have hcardB : Fintype.card (BlockType l) = n := by
    rw [card_BlockType, hl, Nat.sum_map_two_pow_bitIndices]
  let e : BlockType l ≃ Fin n := Fintype.equivFinOfCardEq hcardB
  let f : Gam l →* Equiv.Perm (Fin n) := (Equiv.permCongrHom e).toMonoidHom.comp (embG l)
  have hf : Function.Injective f := by
    intro a b hab
    exact embG_injective l ((Equiv.permCongrHom e).injective hab)
  have hfsign : ∀ γ, Equiv.Perm.sign (f γ) = sgG l γ := by
    intro γ
    show Equiv.Perm.sign (e.permCongr (embG l γ)) = _
    rw [Equiv.Perm.sign_permCongr, sign_embG]
  have hcard : Nat.card f.range = 2 ^ (Nat.card (Equiv.Perm (Fin n))).factorization 2 := by
    rw [Nat.card_perm, Nat.card_fin, ← card_Gam_bitIndices n,
      ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
  let M : Sylow 2 (Equiv.Perm (Fin n)) := Sylow.ofCard f.range hcard
  obtain ⟨S, hSP⟩ := hP.exists_le_sylow
  have hSP' : (S : Subgroup (Equiv.Perm (Fin n))) = P := hmax _ S.isPGroup' hSP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin n)) M S
  let ι : Gam l →* Equiv.Perm (Fin n) := (MulAut.conj g).toMonoidHom.comp f
  have hPmem : ∀ x, x ∈ P ↔ ∃ γ, ι γ = x := by
    intro x
    rw [← hSP', ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hs' : s ∈ f.range := by simpa [M] using hs
      obtain ⟨γ, rfl⟩ := hs'
      exact ⟨γ, rfl⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨f γ, by simp [M], rfl⟩
  have hιinj : Function.Injective ι := (MulAut.conj g).injective.comp hf
  have hιsign : ∀ γ, Equiv.Perm.sign (ι γ) = sgG l γ := by
    intro γ
    show Equiv.Perm.sign (g * f γ * g⁻¹) = _
    rw [map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign g) (Equiv.Perm.sign (f γ)),
      mul_assoc, mul_inv_cancel, mul_one, hfsign]
  obtain ⟨γy, hγy⟩ := (hPmem y).1 hyP
  have hy_cent : ∀ x : Gam l, x * γy = γy * x := by
    intro x
    apply hιinj
    rw [map_mul, map_mul, hγy]
    exact hyc (ι x) ((hPmem _).2 ⟨x, rfl⟩)
  have hy_sq : γy * γy = 1 := by
    apply hιinj
    rw [map_mul, hγy, map_one]
    exact hy2
  have hy_ne : γy ≠ 1 := by
    intro h
    apply hy1
    rw [← hγy, h, map_one]
  have hlt := strict_gam l (exists_big_bitIndex n hn) γy hy_cent hy_sq hy_ne
  rw [card_roots_model P (sgG l) ι hιinj hιsign hPmem (-1) y γy hγy,
    card_roots_model P (sgG l) ι hιinj hιsign hPmem (-1) 1 1 (map_one ι)]
  exact hlt

end CFSG.OddStandard.AltStdSec
