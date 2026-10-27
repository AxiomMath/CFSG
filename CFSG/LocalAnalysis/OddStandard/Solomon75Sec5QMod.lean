module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QPair
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFC

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Conj

variable {n : ℕ} {K : Type} [Group K]

@[expose] noncomputable def AhatData.CoverSetup.conj (C : AhatData.CoverSetup n K)
    (ν : Perm (Fin n)) : AhatData.CoverSetup n K where
  π := (MulAut.conjNormal ν : MulAut (alternatingGroup (Fin n))).toMonoidHom.comp C.π
  surj := (MulAut.conjNormal ν : MulAut (alternatingGroup (Fin n))).surjective.comp C.surj
  ker := by
    rw [← C.ker]
    ext x
    simp [MonoidHom.mem_ker]
  hX := C.hX

theorem AhatData.CoverSetup.conj_ρ (C : AhatData.CoverSetup n K) (ν : Perm (Fin n)) (x : K) :
    (C.conj ν).ρ x = ν * C.ρ x * ν⁻¹ := rfl

theorem AhatData.CoverSetup.Induces.conj {C : AhatData.CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (ν : Perm (Fin n)) :
    (C.conj ν).Induces α (ν * σ * ν⁻¹) :=
  ⟨fun x => by
    rw [C.conj_ρ, C.conj_ρ, h.map_ρ]
    group⟩

end Conj

section Model

variable {X : Type} [Group X] {n : ℕ} {A : Subgroup X}

@[expose] noncomputable def AhatModel.conjC (M : AhatModel X n A) (ν : Perm (Fin n)) :
    AhatModel X n A where
  K := M.K
  e := M.e
  C := M.C.conj ν

theorem AhatModel.conjC_perm (hn : 8 ≤ n) (M : AhatModel X n A) (ν : Perm (Fin n)) {c : X}
    (hc : c ∈ normalizer (A : Set X)) :
    (M.conjC ν).perm c hc = ν * M.perm c hc * ν⁻¹ :=
  (M.conjC ν).perm_eq_of_induces hn hc ((M.induces_perm hn c hc).conj ν)

theorem AhatModel.conjC_permX (hn : 8 ≤ n) (M : AhatModel X n A) (ν : Perm (Fin n)) (c : X) :
    (M.conjC ν).permX c = ν * M.permX c * ν⁻¹ := by
  by_cases hc : c ∈ normalizer (A : Set X)
  · rw [(M.conjC ν).permX_of_mem hc, M.permX_of_mem hc, M.conjC_perm hn ν hc]
  · simp [AhatModel.permX, hc]

end Model

section Counts

variable {n : ℕ}

theorem sign_conj_eq (ν σ : Perm (Fin n)) : sign (ν * σ * ν⁻¹) = sign σ := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm (sign ν) (sign σ), mul_assoc,
    Int.units_mul_self, mul_one]

theorem sign_of_involution {k : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (hk : σ.support.card = 2 * k) : sign σ = (-1) ^ k := by
  rw [Equiv.Perm.sign_of_cycleType, cycleType_eq_replicate_of_involution hσ hk]
  simp only [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  rw [show k * 2 + k = 2 * k + k by ring, pow_add, pow_mul]
  simp

theorem even_of_involution_sign {k : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (hk : σ.support.card = 2 * k) (hs : sign σ = 1) : Even k := by
  rw [sign_of_involution hσ hk] at hs
  exact (neg_one_pow_eq_one_iff_even (by decide)).1 hs

theorem six_le_transCount {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hn : 12 ≤ n)
    (hf : fixCount σ ≤ 3) (hs : sign σ = 1) : 6 ≤ transCount σ := by
  obtain ⟨k, hk⟩ := involution_support_even hσ
  have hev := even_of_involution_sign hσ hk hs
  have hsum := fixCount_add_support σ
  have htr : transCount σ = k := by
    unfold transCount
    rw [hk]
    omega
  rw [htr]
  obtain ⟨m, hm⟩ := hev
  omega

theorem support_card_eq_eight {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hn : 8 ≤ n) (hn' : n ≤ 11)
    (hf : fixCount σ ≤ 3) (ht : transCount σ ≠ 3) (hs : sign σ = 1) : σ.support.card = 8 := by
  obtain ⟨k, hk⟩ := involution_support_even hσ
  have hev := even_of_involution_sign hσ hk hs
  have hsum := fixCount_add_support σ
  have htr : transCount σ = k := by
    unfold transCount
    rw [hk]
    omega
  have ht' : k ≠ 3 := htr ▸ ht
  obtain ⟨m, hm⟩ := hev
  omega

end Counts

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

theorem conjModels (h : PairCtx X n z s A A' M M') (ν ν' : Perm (Fin n)) :
    PairCtx X n z s A A' (M.conjC ν) (M'.conjC ν') :=
  { h with
    hfix := by rw [M.conjC_permX h.hn, fixCount_conj]; exact h.hfix
    hfix' := by rw [M'.conjC_permX h.hn, fixCount_conj]; exact h.hfix'
    htr := by rw [M.conjC_permX h.hn, transCount_conj]; exact h.htr
    htr' := by rw [M'.conjC_permX h.hn, transCount_conj]; exact h.htr'
    hsgn := by rw [M.conjC_permX h.hn, sign_conj_eq]; exact h.hsgn
    hsgn' := by rw [M'.conjC_permX h.hn, sign_conj_eq]; exact h.hsgn' }

theorem sq_permX_s (h : PairCtx X n z s A A' M M') : M.permX s * M.permX s = 1 := by
  have hsN : s ∈ normalizer (A : Set X) := h.hNz h.s_mem_C
  rw [← M.permX_mul h.hn hsN hsN, h.sq_s, M.permX_one h.hn]

theorem sq_permX_z (h : PairCtx X n z s A A' M M') : M'.permX z * M'.permX z = 1 :=
  h.swap.sq_permX_s

theorem exists_sig0 [NeZero n] (h : PairCtx X n z s A A' M M') (hn11 : n ≤ 11) :
    ∃ (M₁ : AhatModel X n A) (M₁' : AhatModel X n A'), PairCtx X n z s A A' M₁ M₁' ∧
      M₁.permX s = sig0 n ∧ M₁'.permX z = sig0 n := by
  have hs8 := support_card_eq_eight h.sq_permX_s h.hn hn11 h.hfix h.htr h.hsgn
  have hz8 := support_card_eq_eight h.sq_permX_z h.hn hn11 h.hfix' h.htr' h.hsgn'
  obtain ⟨ν, hν⟩ := exists_conj_stdInv (n := n) (k := 4) (h := by have := h.hn; omega)
    h.sq_permX_s (by rw [hs8])
  obtain ⟨ν', hν'⟩ := exists_conj_stdInv (n := n) (k := 4) (h := by have := h.hn; omega)
    h.sq_permX_z (by rw [hz8])
  refine ⟨M.conjC ν, M'.conjC ν', h.conjModels ν ν', ?_, ?_⟩
  · rw [M.conjC_permX h.hn, hν, ← sig0_eq_stdInv n h.hn hn11]
  · rw [M'.conjC_permX h.hn, hν', ← sig0_eq_stdInv n h.hn hn11]

end PairCtx

end CFSG.OddStandard.Solomon75
