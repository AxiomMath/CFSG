module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma137
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop139
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a2
public import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaSmallPiGroup
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaFour

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped MatrixGroups

namespace Lemma137b

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff)

@[expose] def Input9_6OmegaTransv : Prop :=
  (∀ n : ℕ, 1 ≤ n →
    ∀ (t : GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2))
      (ht : t ∈ Subgroup.normalizer
        (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2)) : Set (GL (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)))),
      (∀ x, StatedQuadPlus (n + 1) (ZMod 2) (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
        StatedQuadPlus (n + 1) (ZMod 2) x) →
      IsTransvection t →
      (∀ a : ↥(StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))),
        MulAut.conj a ≠ (StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))).normalizerMonoidHom ⟨t, ht⟩) ∧
      Nonempty (↥(fixSub ((StatedOmega (StatedQuadPlus (n + 1) (ZMod 2))).normalizerMonoidHom
        ⟨t, ht⟩)) ≃* ↥(StatedSp n (ZMod 2)))) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∀ (t : GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2))
      (ht : t ∈ Subgroup.normalizer
        (StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1) :
          Set (GL (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2) (ZMod 2)))),
      (∀ x, StatedQuadMinus (n + 1) (ZMod 2) 1 1 (Matrix.mulVec (t : Matrix _ _ (ZMod 2)) x) =
        StatedQuadMinus (n + 1) (ZMod 2) 1 1 x) →
      IsTransvection t →
      (∀ a : ↥(StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)),
        MulAut.conj a ≠ (StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)).normalizerMonoidHom
          ⟨t, ht⟩) ∧
      Nonempty (↥(fixSub ((StatedOmega (StatedQuadMinus (n + 1) (ZMod 2) 1 1)).normalizerMonoidHom
        ⟨t, ht⟩)) ≃* ↥(StatedSp n (ZMod 2))))

@[expose] def Input3_3SpFacts : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (ε : Bool) (n : ℕ), 2 ≤ n → HasFixedPointFreeOrder ε n p →
    ∀ (C : Type) [Group C] [Finite C], Nonempty (C ≃* ↥(StatedSp n (ZMod 2))) →
      GLAPPrimeCore p C = ⊥ ∧ IsSimpleGroup ↥(commutator C) ∧ ¬ IsMulCommutative ↥(commutator C)

@[expose] def Input3_3OmegaUnique : Prop :=
  ∀ (ε ε' : Bool) (n n' : ℕ) (X : Type) [Group X] [Finite X],
    IsOmegaTwo ε (n + 1) X → IsOmegaTwo ε' (n' + 1) X → ε = ε' ∧ n = n'

@[expose] def Input3_3OmegaAlt : Prop :=
  ∀ (p k : ℕ), p.Prime → p ≠ 2 → ∀ (ε : Bool) (n : ℕ) (X : Type) [Group X] [Finite X],
    IsAltType (k * p + 2) X → IsOmegaTwo ε (n + 1) X →
      Nonempty (↥(StatedSp n (ZMod 2)) ≃* Equiv.Perm (Fin (k * p)))

theorem omegaFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ε : Bool}
    (hfp : HasFixedPointFreeOrder ε 1 p) {X : Type} [Group X] (hX : IsOmegaTwo ε 2 X) :
    p = 3 ∧ IsAltType 5 X := by
  cases ε with
  | true =>
    exact absurd hfp
      (CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2)
  | false =>
    refine ⟨CFSG.HardMathSupport.Timmesfeld.Proving.eq_three_of_hasFixedPointFreeOrder_minus_one
      hp hp2 hfp, ?_⟩
    obtain ⟨e⟩ := hX
    exact ⟨e.trans
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadMinus_two_mulEquiv_alt5⟩

section Alt

theorem eq_one_of_commute_alternatingGroup {n : ℕ} (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)}
    (h : ∀ a ∈ alternatingGroup (Fin n), σ * a = a * σ) : σ = 1 := by
  classical
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hne (Equiv.ext hcon)
  set j := σ i with hj
  obtain ⟨k, hk⟩ : ∃ k : Fin n, k ∉ ({i, j} : Finset (Fin n)) := by
    have hc : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have := Finset.card_le_two (a := i) (b := j)
      omega
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨e, he⟩
  obtain ⟨l, hl⟩ : ∃ l : Fin n, l ∉ ({i, j, k, σ k} : Finset (Fin n)) := by
    have hc : ({i, j, k, σ k} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]
      have h1 : ({i, j, k, σ k} : Finset (Fin n)).card ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine (Nat.succ_le_succ (Finset.card_insert_le _ _)).trans ?_
        refine (Nat.succ_le_succ (Nat.succ_le_succ (Finset.card_le_two))).trans ?_
        exact le_rfl
      omega
    obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    exact ⟨e, he⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
  obtain ⟨hki, hkj⟩ := hk
  obtain ⟨hli, hlj, hlk, hlσ⟩ := hl
  have hij : i ≠ j := fun h' => hi h'.symm
  set a : Equiv.Perm (Fin n) := Equiv.swap i k * Equiv.swap j l with ha
  have ha_mem : a ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, ha, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (Ne.symm hki),
      Equiv.Perm.sign_swap (Ne.symm hlj)]
    decide
  have hc := h a ha_mem
  have h1 : σ (a i) = a (σ i) := by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f i) hc
    simpa using this
  have hai : a i = k := by
    have e1 : Equiv.swap j l i = i := Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hli)
    rw [ha, Equiv.Perm.mul_apply, e1, Equiv.swap_apply_left]
  have haj : a j = l := by
    have e1 : Equiv.swap j l j = l := Equiv.swap_apply_left j l
    rw [ha, Equiv.Perm.mul_apply, e1, Equiv.swap_apply_of_ne_of_ne hli hlk]
  rw [hai, ← hj, haj] at h1
  exact hlσ h1.symm

theorem sign_eq_neg_one_of_isSwap {n : ℕ} {τ : Equiv.Perm (Fin n)} (hτ : τ.IsSwap) :
    Equiv.Perm.sign τ = -1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hτ
  exact Equiv.Perm.sign_swap hxy

theorem conj_ne_conjNormal {n : ℕ} (hn : 5 ≤ n) {τ : Equiv.Perm (Fin n)} (hτ : τ.IsSwap)
    (a : ↥(alternatingGroup (Fin n))) :
    MulAut.conj a ≠ MulAut.conjNormal (H := alternatingGroup (Fin n)) τ := by
  intro h
  have hcomm : ∀ x ∈ alternatingGroup (Fin n),
      ((a : Equiv.Perm (Fin n))⁻¹ * τ) * x = x * ((a : Equiv.Perm (Fin n))⁻¹ * τ) := by
    intro x hx
    have h1 := congrArg (fun f : MulAut ↥(alternatingGroup (Fin n)) =>
      ((f ⟨x, hx⟩ : ↥(alternatingGroup (Fin n))) : Equiv.Perm (Fin n))) h
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply] at h1
    have e : (a : Equiv.Perm (Fin n)) * x * (a : Equiv.Perm (Fin n))⁻¹ = τ * x * τ⁻¹ := h1
    calc (a : Equiv.Perm (Fin n))⁻¹ * τ * x
        = (a : Equiv.Perm (Fin n))⁻¹ * (τ * x * τ⁻¹) * τ := by group
      _ = (a : Equiv.Perm (Fin n))⁻¹ * ((a : Equiv.Perm (Fin n)) * x * (a : Equiv.Perm (Fin n))⁻¹) * τ := by
          rw [e]
      _ = x * ((a : Equiv.Perm (Fin n))⁻¹ * τ) := by group
  have h1 := eq_one_of_commute_alternatingGroup hn hcomm
  have h2 : τ = (a : Equiv.Perm (Fin n)) := (inv_mul_eq_one.1 h1).symm
  have h3 : Equiv.Perm.sign τ = 1 := by
    rw [h2]
    exact Equiv.Perm.mem_alternatingGroup.1 a.2
  rw [sign_eq_neg_one_of_isSwap hτ] at h3
  exact absurd h3 (by decide)

theorem pPrimeCore_perm_eq_bot {n p : ℕ} (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ≤ n) :
    GLAPPrimeCore p (Equiv.Perm (Fin n)) = ⊥ := by
  show CFSG.pPrimeCore p (Equiv.Perm (Fin n)) = ⊥
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hK hcop
  have hA : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hnormal : (K.subgroupOf (alternatingGroup (Fin n))).Normal := Subgroup.Normal.subgroupOf hK _
  haveI := hA
  haveI := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf (alternatingGroup (Fin n))) with hbot | htop
  · refine (Subgroup.eq_bot_iff_forall K).2 fun r hr => ?_
    refine eq_one_of_commute_alternatingGroup hn fun a ha => ?_
    have hc : r * a * r⁻¹ * a⁻¹ ∈ K := by
      have h1 : a * r⁻¹ * a⁻¹ ∈ K := hK.conj_mem _ (K.inv_mem hr) a
      have := K.mul_mem hr h1
      simpa [mul_assoc] using this
    have hcA : r * a * r⁻¹ * a⁻¹ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup] at ha ⊢
      simp [Equiv.Perm.sign_mul, ha, mul_comm]
    have hmem : (⟨r * a * r⁻¹ * a⁻¹, hcA⟩ : ↥(alternatingGroup (Fin n))) ∈
        K.subgroupOf (alternatingGroup (Fin n)) := hc
    rw [hbot, Subgroup.mem_bot] at hmem
    have hmem' : r * a * r⁻¹ * a⁻¹ = 1 := congrArg Subtype.val hmem
    have : r * a = a * r := by
      have := congrArg (fun z => z * a * r) hmem'
      simpa [mul_assoc] using this
    exact this
  · exfalso
    have hle : alternatingGroup (Fin n) ≤ K := by
      intro x hx
      have : (⟨x, hx⟩ : ↥(alternatingGroup (Fin n))) ∈ K.subgroupOf (alternatingGroup (Fin n)) := by
        rw [htop]; exact Subgroup.mem_top _
      exact this
    have hd : Nat.card (alternatingGroup (Fin n)) ∣ Nat.card K := Subgroup.card_dvd_of_le hle
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    have h2 : 2 * Nat.card (alternatingGroup (Fin n)) = Nat.factorial n := by
      rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
    have hpf : p ∣ Nat.factorial n := Nat.dvd_factorial hp.pos hpn
    rw [← h2] at hpf
    have hpA : p ∣ Nat.card (alternatingGroup (Fin n)) := by
      rcases (Nat.Prime.dvd_mul hp).1 hpf with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
      · exact h
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop (hpA.trans hd))

section AltCent

variable {r : ℕ}

abbrev Rest (a b : Fin (r + 2)) : Type := {x : Fin (r + 2) // x ≠ a ∧ x ≠ b}

theorem card_rest {a b : Fin (r + 2)} (hab : a ≠ b) : Fintype.card (Rest a b) = r := by
  classical
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : Fin (r + 2) => x ≠ a ∧ x ≠ b) = Finset.univ \ {a, b} := by
    ext x; simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hab]
  omega

noncomputable def corr (a b : Fin (r + 2)) (ρ : Equiv.Perm (Rest a b)) :
    Equiv.Perm (Fin (r + 2)) :=
  if Equiv.Perm.sign ρ = 1 then 1 else Equiv.swap a b

theorem ofSubtype_commute_swap (a b : Fin (r + 2)) (ρ : Equiv.Perm (Rest a b)) :
    Commute (Equiv.Perm.ofSubtype ρ) (Equiv.swap a b) := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : x ≠ a ∧ x ≠ b
  · right; exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2
  · left; exact Equiv.Perm.ofSubtype_apply_of_not_mem ρ hx

theorem commute_corr (a b : Fin (r + 2)) (ρ σ : Equiv.Perm (Rest a b)) :
    Commute (Equiv.Perm.ofSubtype σ) (corr a b ρ) := by
  unfold corr
  split_ifs
  · exact Commute.one_right _
  · exact ofSubtype_commute_swap a b σ

theorem corr_mul (a b : Fin (r + 2)) (ρ ρ' : Equiv.Perm (Rest a b)) :
    corr a b (ρ * ρ') = corr a b ρ * corr a b ρ' := by
  unfold corr
  rw [Equiv.Perm.sign_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ') with h' | h' <;>
    simp [h, h', Equiv.swap_mul_self]

theorem sign_corr (a b : Fin (r + 2)) (hab : a ≠ b) (ρ : Equiv.Perm (Rest a b)) :
    Equiv.Perm.sign (corr a b ρ) = Equiv.Perm.sign ρ := by
  unfold corr
  split_ifs with h
  · simp [h]
  · rw [Equiv.Perm.sign_swap hab]
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h' | h'
    · exact absurd h' h
    · exact h'.symm

noncomputable def psi (a b : Fin (r + 2)) :
    Equiv.Perm (Rest a b) →* Equiv.Perm (Fin (r + 2)) where
  toFun ρ := Equiv.Perm.ofSubtype ρ * corr a b ρ
  map_one' := by simp [corr]
  map_mul' ρ ρ' := by
    have hc := (commute_corr a b ρ ρ').symm.eq
    rw [map_mul, corr_mul]
    calc Equiv.Perm.ofSubtype ρ * Equiv.Perm.ofSubtype ρ' * (corr a b ρ * corr a b ρ')
        = Equiv.Perm.ofSubtype ρ * (Equiv.Perm.ofSubtype ρ' * corr a b ρ) * corr a b ρ' := by
          simp only [mul_assoc]
      _ = Equiv.Perm.ofSubtype ρ * (corr a b ρ * Equiv.Perm.ofSubtype ρ') * corr a b ρ' := by
          rw [hc]
      _ = (Equiv.Perm.ofSubtype ρ * corr a b ρ) * (Equiv.Perm.ofSubtype ρ' * corr a b ρ') := by
          simp only [mul_assoc]

theorem psi_apply_rest (a b : Fin (r + 2)) (ρ : Equiv.Perm (Rest a b)) (x : Rest a b) :
    psi a b ρ (x : Fin (r + 2)) = (ρ x : Fin (r + 2)) := by
  show Equiv.Perm.ofSubtype ρ (corr a b ρ x) = _
  have : corr a b ρ (x : Fin (r + 2)) = x := by
    unfold corr
    split_ifs
    · rfl
    · exact Equiv.swap_apply_of_ne_of_ne x.2.1 x.2.2
  rw [this, Equiv.Perm.ofSubtype_apply_coe]

theorem psi_injective (a b : Fin (r + 2)) : Function.Injective (psi a b) := by
  intro ρ ρ' h
  refine Equiv.ext fun x => Subtype.ext ?_
  have := congrArg (fun f : Equiv.Perm (Fin (r + 2)) => f (x : Fin (r + 2))) h
  simp only [psi_apply_rest] at this
  exact this

theorem sign_psi (a b : Fin (r + 2)) (hab : a ≠ b) (ρ : Equiv.Perm (Rest a b)) :
    Equiv.Perm.sign (psi a b ρ) = 1 := by
  show Equiv.Perm.sign (Equiv.Perm.ofSubtype ρ * corr a b ρ) = 1
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_ofSubtype, sign_corr a b hab]
  exact Int.units_mul_self _

theorem psi_commute (a b : Fin (r + 2)) (ρ : Equiv.Perm (Rest a b)) :
    Equiv.swap a b * psi a b ρ = psi a b ρ * Equiv.swap a b := by
  have h1 := (ofSubtype_commute_swap a b ρ).symm.eq
  have h2 : Equiv.swap a b * corr a b ρ = corr a b ρ * Equiv.swap a b := by
    unfold corr
    split_ifs <;> simp
  show Equiv.swap a b * (Equiv.Perm.ofSubtype ρ * corr a b ρ) =
    (Equiv.Perm.ofSubtype ρ * corr a b ρ) * Equiv.swap a b
  rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem mem_pair_of_commute {a b : Fin (r + 2)} (hab : a ≠ b) {σ : Equiv.Perm (Fin (r + 2))}
    (hσ : Equiv.swap a b * σ = σ * Equiv.swap a b) {x : Fin (r + 2)} (hx : x = a ∨ x = b) :
    σ x = a ∨ σ x = b := by
  have hA : Equiv.swap a b (σ a) = σ b := by
    have := congrArg (fun f : Equiv.Perm (Fin (r + 2)) => f a) hσ
    simpa using this
  have hB : Equiv.swap a b (σ b) = σ a := by
    have := congrArg (fun f : Equiv.Perm (Fin (r + 2)) => f b) hσ
    simpa using this
  by_contra hcon
  push Not at hcon
  rcases hx with rfl | rfl
  · have h1 : Equiv.swap x b (σ x) = σ x := Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2
    rw [h1] at hA
    exact hab (σ.injective hA)
  · have h1 : Equiv.swap a x (σ x) = σ x := Equiv.swap_apply_of_ne_of_ne hcon.1 hcon.2
    rw [h1] at hB
    exact hab (σ.injective hB).symm

theorem exists_psi_eq (a b : Fin (r + 2)) (hab : a ≠ b) {σ : Equiv.Perm (Fin (r + 2))}
    (hσA : Equiv.Perm.sign σ = 1) (hσ : Equiv.swap a b * σ = σ * Equiv.swap a b) :
    ∃ ρ : Equiv.Perm (Rest a b), psi a b ρ = σ := by
  have hσ' : Equiv.swap a b * σ⁻¹ = σ⁻¹ * Equiv.swap a b := by
    have := congrArg (fun f : Equiv.Perm (Fin (r + 2)) => σ⁻¹ * f * σ⁻¹) hσ
    simp only [mul_assoc, mul_inv_cancel, mul_one] at this
    simpa [mul_assoc] using this.symm
  have hpres : ∀ x, (x = a ∨ x = b) → (σ x = a ∨ σ x = b) := fun x hx => mem_pair_of_commute hab hσ hx
  have hpres' : ∀ x, (σ x = a ∨ σ x = b) → (x = a ∨ x = b) := by
    intro x hx
    have := mem_pair_of_commute hab hσ' hx
    simpa using this
  have hS : ∀ x, (x ≠ a ∧ x ≠ b) ↔ (σ x ≠ a ∧ σ x ≠ b) := by
    intro x
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hcon
      rw [not_and_or, not_not, not_not] at hcon
      rcases hpres' x hcon with h | h
      · exact h1 h
      · exact h2 h
    · rintro ⟨h1, h2⟩
      by_contra hcon
      rw [not_and_or, not_not, not_not] at hcon
      rcases hpres x hcon with h | h
      · exact h1 h
      · exact h2 h
  set ρ : Equiv.Perm (Rest a b) := σ.subtypePerm (fun x => (hS x).symm) with hρ
  refine ⟨ρ, ?_⟩
  have hsa : σ a = a ∨ σ a = b := hpres a (Or.inl rfl)
  have hsb : σ b = a ∨ σ b = b := hpres b (Or.inr rfl)
  rcases hsa with ha | ha
  ·
    have hb : σ b = b := by
      rcases hsb with hb | hb
      · exact absurd (σ.injective (hb.trans ha.symm)) hab.symm
      · exact hb
    have hσeq : σ = Equiv.Perm.ofSubtype ρ := by
      refine Equiv.ext fun x => ?_
      by_cases hx : x ≠ a ∧ x ≠ b
      · rw [Equiv.Perm.ofSubtype_apply_of_mem ρ hx]
        rfl
      · rw [Equiv.Perm.ofSubtype_apply_of_not_mem ρ hx]
        rw [not_and_or, not_not, not_not] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
    have hsr : Equiv.Perm.sign ρ = 1 := by
      rw [← Equiv.Perm.sign_ofSubtype, ← hσeq]
      exact hσA
    show Equiv.Perm.ofSubtype ρ * corr a b ρ = σ
    rw [hσeq]
    simp [corr, hsr]
  · have hb : σ b = a := by
      rcases hsb with hb | hb
      · exact hb
      · exact absurd (σ.injective (hb.trans ha.symm)) hab.symm
    have hσeq : σ = Equiv.Perm.ofSubtype ρ * Equiv.swap a b := by
      refine Equiv.ext fun x => ?_
      by_cases hx : x ≠ a ∧ x ≠ b
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hx.1 hx.2,
          Equiv.Perm.ofSubtype_apply_of_mem ρ hx]
        rfl
      · rw [not_and_or, not_not, not_not] at hx
        rw [Equiv.Perm.mul_apply]
        rcases hx with rfl | rfl
        · rw [Equiv.swap_apply_left, Equiv.Perm.ofSubtype_apply_of_not_mem ρ (by simp [hab.symm]), ha]
        · rw [Equiv.swap_apply_right, Equiv.Perm.ofSubtype_apply_of_not_mem ρ (by simp [hab]), hb]
    have hsr : Equiv.Perm.sign ρ = -1 := by
      have h1 := hσA
      rw [hσeq, Equiv.Perm.sign_mul, Equiv.Perm.sign_ofSubtype, Equiv.Perm.sign_swap hab] at h1
      rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h
      · rw [h] at h1; exact absurd h1 (by decide)
      · exact h
    have hne : ¬ Equiv.Perm.sign ρ = 1 := by rw [hsr]; decide
    show Equiv.Perm.ofSubtype ρ * corr a b ρ = σ
    rw [hσeq]
    simp [corr, hne]

theorem mem_fixSub_conjNormal {n : ℕ} {τ : Equiv.Perm (Fin n)} (x : ↥(alternatingGroup (Fin n))) :
    x ∈ fixSub (MulAut.conjNormal (H := alternatingGroup (Fin n)) τ) ↔
      τ * (x : Equiv.Perm (Fin n)) = (x : Equiv.Perm (Fin n)) * τ := by
  rw [mem_fixSub]
  constructor
  · intro h
    have := congrArg (fun y : ↥(alternatingGroup (Fin n)) => (y : Equiv.Perm (Fin n))) h
    simp only [MulAut.conjNormal_apply] at this
    calc τ * (x : Equiv.Perm (Fin n)) = (τ * (x : Equiv.Perm (Fin n)) * τ⁻¹) * τ := by group
      _ = (x : Equiv.Perm (Fin n)) * τ := by rw [this]
  · intro h
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    calc τ * (x : Equiv.Perm (Fin n)) * τ⁻¹ = ((x : Equiv.Perm (Fin n)) * τ) * τ⁻¹ := by rw [h]
      _ = x := by group

theorem alt_centralizer_equiv {τ : Equiv.Perm (Fin (r + 2))} (hτ : τ.IsSwap) :
    Nonempty (↥(fixSub (MulAut.conjNormal (H := alternatingGroup (Fin (r + 2))) τ)) ≃*
      Equiv.Perm (Fin r)) := by
  obtain ⟨a, b, hab, rfl⟩ := hτ
  let ψ₁ : Equiv.Perm (Rest a b) →* ↥(alternatingGroup (Fin (r + 2))) :=
    (psi a b).codRestrict (alternatingGroup (Fin (r + 2))) fun ρ =>
      Equiv.Perm.mem_alternatingGroup.2 (sign_psi a b hab ρ)
  let ψ₂ : Equiv.Perm (Rest a b) →* ↥(fixSub (MulAut.conjNormal
      (H := alternatingGroup (Fin (r + 2))) (Equiv.swap a b))) :=
    ψ₁.codRestrict _ fun ρ => (mem_fixSub_conjNormal _).2 (psi_commute a b ρ)
  have hbij : Function.Bijective ψ₂ := by
    constructor
    · intro ρ ρ' h
      apply psi_injective a b
      exact congrArg (fun y : ↥(fixSub (MulAut.conjNormal
        (H := alternatingGroup (Fin (r + 2))) (Equiv.swap a b))) =>
          (((y : ↥(alternatingGroup (Fin (r + 2)))) : Equiv.Perm (Fin (r + 2)))) ) h
    · rintro ⟨⟨σ, hσA⟩, hσ⟩
      obtain ⟨ρ, hρ⟩ := exists_psi_eq a b hab (Equiv.Perm.mem_alternatingGroup.1 hσA)
        ((mem_fixSub_conjNormal _).1 hσ)
      exact ⟨ρ, Subtype.ext (Subtype.ext hρ)⟩
  let e0 : Rest a b ≃ Fin r := Fintype.equivFinOfCardEq (card_rest hab)
  exact ⟨(MulEquiv.ofBijective ψ₂ hbij).symm.trans e0.permCongrHom⟩

end AltCent

end Alt

section ThmA

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_of_centralizes {p : ℕ} {M L T : Subgroup G} (hLM : L ≤ M) (hTM : T ≤ M)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hb : L ⊓ GLAPPrimeCoreOf p M ≤ T)
    {x : G} (hxL : x ∈ L)
    (hxc : (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨x, hLM hxL⟩ : ↥M)) ∈
      Subgroup.centralizer ((barX p M T : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    {t : G} (ht : t ∈ T) : x * t * x⁻¹ ∈ T := by
  have hcomm := (Subgroup.mem_centralizer_iff.1 hxc)
    (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨t, hTM ht⟩ : ↥M)) (Lemma137.mk_mem_barX' hTM ht)
  have hxM : x ∈ M := hLM hxL
  have htM : t ∈ M := hTM ht
  have hcM : x * t * x⁻¹ * t⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hxM htM) (M.inv_mem hxM)) (M.inv_mem htM)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M)
      ((⟨x, hxM⟩ : ↥M) * ⟨t, htM⟩ * (⟨x, hxM⟩ : ↥M)⁻¹ * (⟨t, htM⟩ : ↥M)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    set a := QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨x, hxM⟩ : ↥M)
    set b := QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨t, htM⟩ : ↥M)
    have hab : a * b = b * a := hcomm.symm
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [hab]
      _ = 1 := by group
  have h2 := (QuotientGroup.eq_one_iff _).1 h1
  have hcO : x * t * x⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf p M :=
    (mem_gLAPPrimeCoreOf_iff p M _).2 ⟨hcM, h2⟩
  have hcL : x * t * x⁻¹ * t⁻¹ ∈ L := by
    have h3 : t * x⁻¹ * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (hTL ht) x⁻¹).1 (L.inv_mem hxL)
    have : x * t * x⁻¹ * t⁻¹ = x * (t * x⁻¹ * t⁻¹) := by group
    rw [this]
    exact L.mul_mem hxL h3
  have hcT : x * t * x⁻¹ * t⁻¹ ∈ T := hb ⟨hcL, hcO⟩
  have := T.mul_mem hcT ht
  simpa [mul_assoc] using this

theorem le_pPrimeCoreOf_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Subgroup G}
    (hT2 : IsPGroup 2 ↥T) : T ≤ GLAPPrimeCoreOf p (Nof T) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine sec11_le_glaPPrimeCoreOf (H := Nof T) Subgroup.le_normalizer ?_ ?_
  · intro h hh n hn
    exact (Subgroup.mem_normalizer_iff.1 hh n).1 hn
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
    rw [hk]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem commutator_mem_inf {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) {x t : G}
    (hxL : x ∈ L) (hxN : x ∈ Nof T) (ht : t ∈ T) : t * x * t⁻¹ * x⁻¹ ∈ T ⊓ L := by
  refine ⟨?_, ?_⟩
  · have h1 : x * t⁻¹ * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hxN t⁻¹).1 (T.inv_mem ht)
    have : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
    rw [this]
    exact T.mul_mem ht h1
  · have h1 : t * x * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hTL ht) x).1 hxL
    exact L.mul_mem h1 (L.inv_mem hxL)

theorem barX_cent_equiv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L T : Subgroup G}
    (hLM : L ≤ M) (hTM : T ≤ M) (hT2 : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hb : L ⊓ GLAPPrimeCoreOf p M ≤ T) (hc : T ⊓ L ≤ GLAPPrimeCoreOf p M)
    (C₀ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M))
    (hC₀ : C₀ = barX p M L ⊓ Subgroup.centralizer ((barX p M T : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hO : GLAPPrimeCore p ↥C₀ = ⊥) :
    Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥C₀) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup G := Nof T with hN
  set J : Subgroup G := N ⊓ L with hJ
  have hJL : J ≤ L := inf_le_right
  have hJN : J ≤ N := inf_le_left
  have hJM : J ≤ M := hJL.trans hLM
  have hmem : ∀ j : ↥J, QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hJM j) ∈ C₀ := by
    intro j
    rw [hC₀]
    refine ⟨Lemma137.mk_mem_barX' hLM (hJL j.2), ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨t', ht', rfl⟩ := (mem_barX_iff p y).1 hy
    have hcO : (t' : G) * (j : G) * (t' : G)⁻¹ * (j : G)⁻¹ ∈ GLAPPrimeCoreOf p M :=
      hc (commutator_mem_inf hTL (hJL j.2) (hJN j.2) ht')
    obtain ⟨hcM, hcM'⟩ := (mem_gLAPPrimeCoreOf_iff p M _).1 hcO
    have e : (⟨(t' : G) * (j : G) * (t' : G)⁻¹ * (j : G)⁻¹, hcM⟩ : ↥M) =
        t' * Subgroup.inclusion hJM j * t'⁻¹ * (Subgroup.inclusion hJM j)⁻¹ := rfl
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M)
        (t' * Subgroup.inclusion hJM j * t'⁻¹ * (Subgroup.inclusion hJM j)⁻¹) = 1 := by
      rw [← e]
      exact (QuotientGroup.eq_one_iff _).2 hcM'
    simp only [map_mul, map_inv] at h1
    set a := QuotientGroup.mk' (GLAPPrimeCore p ↥M) t'
    set b := QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hJM j)
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  let h : ↥J →* ↥C₀ :=
    ((QuotientGroup.mk' (GLAPPrimeCore p ↥M)).comp (Subgroup.inclusion hJM)).codRestrict C₀ hmem
  have hsurj : Function.Surjective h := by
    rintro ⟨c, hcC⟩
    rw [hC₀] at hcC
    obtain ⟨hcL, hcZ⟩ := hcC
    obtain ⟨x, hxL, rfl⟩ := (mem_barX_iff p c).1 hcL
    have hxL' : (x : G) ∈ L := hxL
    have hxZ : (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨(x : G), hLM hxL'⟩ : ↥M)) ∈
        Subgroup.centralizer ((barX p M T : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) := hcZ
    have hxZ' : (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨((x⁻¹ : ↥M) : G), hLM (L.inv_mem hxL')⟩ : ↥M)) ∈
        Subgroup.centralizer ((barX p M T : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      have := (Subgroup.centralizer ((barX p M T : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
          Set (↥M ⧸ GLAPPrimeCore p ↥M))).inv_mem hxZ
      rw [← map_inv] at this
      exact this
    have hxN : (x : G) ∈ N := by
      refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
      · exact conj_mem_of_centralizes hLM hTM hTL hb hxL' hxZ hy
      · have := conj_mem_of_centralizes hLM hTM hTL hb (L.inv_mem hxL') hxZ' hy
        simpa [mul_assoc] using this
    refine ⟨⟨(x : G), hxN, hxL'⟩, ?_⟩
    apply Subtype.ext
    rfl
  let g : ↥J →* ↥(barX p N J) :=
    ((QuotientGroup.mk' (GLAPPrimeCore p ↥N)).comp (Subgroup.inclusion hJN)).codRestrict (barX p N J)
      fun j => Lemma137.mk_mem_barX' hJN j.2
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxJ, rfl⟩ := (mem_barX_iff p y).1 hy
    exact ⟨⟨(x : G), hxJ⟩, rfl⟩
  have hkerN : ∀ j : ↥J, j ∈ g.ker → (j : G) ∈ GLAPPrimeCoreOf p N := by
    intro j hj
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥N) (Subgroup.inclusion hJN j) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hj)
    exact (mem_gLAPPrimeCoreOf_iff p N _).2 ⟨hJN j.2, (QuotientGroup.eq_one_iff _).1 h1⟩
  have hker : g.ker = h.ker := by
    apply le_antisymm
    · intro j hj
      have hnorm : (g.ker.map h).Normal := Subgroup.Normal.map inferInstance h hsurj
      have hpR : ¬ p ∣ Nat.card g.ker := by
        have hle : g.ker.map J.subtype ≤ GLAPPrimeCoreOf p N := by
          rintro _ ⟨j', hj', rfl⟩
          exact hkerN j' hj'
        have hcard1 : Nat.card (g.ker.map J.subtype) = Nat.card g.ker :=
          Subgroup.card_map_of_injective J.subtype_injective
        intro hd
        apply not_dvd_card_glaPPrimeCoreOf hp N
        refine hd.trans ?_
        rw [← hcard1]
        exact Subgroup.card_dvd_of_le hle
      have hcop : Nat.Coprime p (Nat.card (g.ker.map h)) :=
        (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => hpR (hd.trans (Subgroup.card_map_dvd _ _))
      have hle2 : g.ker.map h ≤ GLAPPrimeCore p ↥C₀ :=
        CFSG.le_pPrimeCore_of_normal_coprime hnorm hcop
      rw [hO] at hle2
      have h3 := hle2 (Subgroup.mem_map_of_mem h hj)
      exact MonoidHom.mem_ker.2 (Subgroup.mem_bot.1 h3)
    · intro j hj
      have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (Subgroup.inclusion hJM j) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.1 hj)
      have hjO : (j : G) ∈ GLAPPrimeCoreOf p M :=
        (mem_gLAPPrimeCoreOf_iff p M _).2 ⟨hJM j.2, (QuotientGroup.eq_one_iff _).1 h1⟩
      have hjT : (j : G) ∈ T := hb ⟨hJL j.2, hjO⟩
      have hjN : (j : G) ∈ GLAPPrimeCoreOf p N := le_pPrimeCoreOf_normalizer hp hp2 hT2 hjT
      obtain ⟨hjN', hjN''⟩ := (mem_gLAPPrimeCoreOf_iff p N _).1 hjN
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).2 hjN''
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective g hgsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective h hsurj))⟩

theorem barX_derivedInf_eq {p : ℕ} {N J : Subgroup G} (hJN : J ≤ N)
    (hperf : ⁅⁅barX p N J, barX p N J⁆, ⁅barX p N J, barX p N J⁆⁆ = ⁅barX p N J, barX p N J⁆) :
    barX p N (derivedInf J) = ⁅barX p N J, barX p N J⁆ := by
  classical
  set S := ⁅barX p N J, barX p N J⁆ with hS
  have hQJ : ⁅J, J⁆ ≤ J := commutator_le_of_le' le_rfl le_rfl
  have hQ : barX p N ⁅J, J⁆ = S := barX_commutator p hJN hJN
  apply le_antisymm
  · have h1 : derivedInf J ≤ ⁅J, J⁆ := by
      refine (iInf_le _ 1).trans ?_
      rw [derivedSeries_one, Lemma137.map_commutator_subtype]
    calc barX p N (derivedInf J) ≤ barX p N ⁅J, J⁆ := barX_mono p h1
      _ = S := hQ
  ·
    have hex : ∃ n, ∃ H : Subgroup G, H ≤ ⁅J, J⁆ ∧ barX p N H = S ∧ Nat.card H = n :=
      ⟨_, ⁅J, J⁆, le_rfl, hQ, rfl⟩
    obtain ⟨H, hHQ, hHS, hHcard⟩ := Nat.find_spec hex
    have hHJ : H ≤ J := hHQ.trans hQJ
    have hHN : H ≤ N := hHJ.trans hJN
    have hperfH : ⁅H, H⁆ = H := by
      have h1 : ⁅H, H⁆ ≤ H := commutator_le_of_le' le_rfl le_rfl
      have h2 : barX p N ⁅H, H⁆ = S := by
        rw [barX_commutator p hHN hHN, hHS]
        exact hperf
      by_contra hne
      have hlt : Nat.card ↥⁅H, H⁆ < Nat.card ↥H :=
        lt_of_le_of_ne (Subgroup.card_le_of_le h1) fun h =>
          hne (Subgroup.eq_of_le_of_card_ge h1 h.ge)
      have hmin := Nat.find_min hex (m := Nat.card ↥⁅H, H⁆) (by rw [← hHcard]; exact hlt)
      exact hmin ⟨⁅H, H⁆, h1.trans hHQ, h2, rfl⟩
    have := Sec12a2.le_derivedInf_of_perfect hHJ hperfH
    calc S = barX p N H := hHS.symm
      _ ≤ barX p N (derivedInf J) := barX_mono p this

end ThmA

section CaseII

variable {Y : Type} [Group Y]

abbrev indAut (A : Subgroup Y) (y : Y) (hy : y ∈ Subgroup.normalizer (A : Set Y)) : MulAut ↥A :=
  A.normalizerMonoidHom ⟨y, hy⟩

theorem indAut_apply (A : Subgroup Y) (y : Y) (hy : y ∈ Subgroup.normalizer (A : Set Y)) (x : ↥A) :
    ((indAut A y hy x : ↥A) : Y) = y * x * y⁻¹ := rfl

theorem congr_conj {Λ : Type} [Group Λ] {A : Subgroup Y} (e : ↥A ≃* Λ) (a : ↥A) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem caseII_abstract (A W Tb : Subgroup Y) (hTW : Tb ≤ W)
    (hWN : W ≤ Subgroup.normalizer (A : Set Y))
    {Λ : Type} [Group Λ] (e : ↥A ≃* Λ) (g : MulAut Λ)
    (hInd : (inducedAutGroup W A).map (MulAut.congr e).toMonoidHom = Subgroup.zpowers g)
    (hcard : Nat.card (inducedAutGroup W A) = 2)
    (hout : ∀ a : Λ, MulAut.conj a ≠ g) (hZ : Subgroup.center ↥A = ⊥)
    (hnc : ¬ Tb ≤ Subgroup.centralizer (A : Set Y)) :
    Tb ⊓ A = ⊥ ∧ Nonempty (↥(A ⊓ Subgroup.centralizer (Tb : Set Y)) ≃* ↥(fixSub g)) := by
  have hord : orderOf g = 2 := by
    rw [← Nat.card_zpowers, ← hInd, Subgroup.card_map_of_injective (MulAut.congr e).injective, hcard]
  have hg2 : g ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h; rw [h, orderOf_one] at hord; exact absurd hord (by norm_num)
  have hmem : ∀ (y : Y) (hy : y ∈ Tb),
      MulAut.congr e (indAut A y (hWN (hTW hy))) ∈ Subgroup.zpowers g := by
    intro y hy
    rw [← hInd]
    exact ⟨_, ⟨⟨y, hWN (hTW hy)⟩, Subgroup.mem_subgroupOf.2 (hTW hy), rfl⟩, rfl⟩
  have hdich : ∀ (y : Y) (hy : y ∈ Tb), MulAut.congr e (indAut A y (hWN (hTW hy))) = 1 ∨
      MulAut.congr e (indAut A y (hWN (hTW hy))) = g := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hmem y hy)
    rw [← hk, ← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; simp [show ((2 : ℕ) : ℤ) = 2 from rfl, h]
    · right; simp [show ((2 : ℕ) : ℤ) = 2 from rfl, h]
  obtain ⟨y₀, hy₀T, hy₀⟩ : ∃ y ∈ Tb, y ∉ Subgroup.centralizer (A : Set Y) := by
    by_contra hcon
    push Not at hcon
    exact hnc (fun y hy => hcon y hy)
  obtain ⟨a₀, ha₀A, ha₀⟩ : ∃ a ∈ (A : Set Y), a * y₀ ≠ y₀ * a := by
    by_contra hcon
    push Not at hcon
    exact hy₀ (Subgroup.mem_centralizer_iff.2 hcon)
  have hnormy₀ := hWN (hTW hy₀T)
  have hind_ne : indAut A y₀ hnormy₀ ≠ 1 := by
    intro h
    have := congrArg (fun f : MulAut ↥A => ((f ⟨a₀, ha₀A⟩ : ↥A) : Y)) h
    simp only [indAut_apply, MulAut.one_apply] at this
    apply ha₀
    calc a₀ * y₀ = (y₀ * a₀ * y₀⁻¹) * y₀ := by rw [this]
      _ = y₀ * a₀ := by group
  have hg_y₀ : MulAut.congr e (indAut A y₀ hnormy₀) = g := by
    rcases hdich y₀ hy₀T with h | h
    · exfalso
      apply hind_ne
      exact (MulAut.congr e).injective (by rw [h, map_one])
    · exact h
  have hkey : ∀ x : ↥A, ((x : Y) ∈ Subgroup.centralizer (Tb : Set Y)) ↔ g (e x) = e x := by
    intro x
    constructor
    · intro hx
      have hc := Subgroup.mem_centralizer_iff.1 hx y₀ hy₀T
      have h1 : indAut A y₀ hnormy₀ x = x := by
        apply Subtype.ext
        rw [indAut_apply]
        calc y₀ * (x : Y) * y₀⁻¹ = ((x : Y) * y₀) * y₀⁻¹ := by rw [hc]
          _ = x := by group
      rw [← hg_y₀]
      show e (indAut A y₀ hnormy₀ (e.symm (e x))) = e x
      rw [e.symm_apply_apply, h1]
    · intro hx
      refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
      have hfix : MulAut.congr e (indAut A t (hWN (hTW ht))) (e x) = e x := by
        rcases hdich t ht with h | h
        · rw [h]; rfl
        · rw [h]; exact hx
      have h1 : indAut A t (hWN (hTW ht)) x = x := by
        have : e (indAut A t (hWN (hTW ht)) (e.symm (e x))) = e x := hfix
        rw [e.symm_apply_apply] at this
        exact e.injective this
      have h2 := congrArg (fun z : ↥A => (z : Y)) h1
      simp only [indAut_apply] at h2
      calc t * (x : Y) = (t * (x : Y) * t⁻¹) * t := by group
        _ = (x : Y) * t := by rw [h2]
  have hTA : Tb ⊓ A = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    obtain ⟨hyT, hyA⟩ := Subgroup.mem_inf.1 hy
    have hconj : indAut A y (hWN (hTW hyT)) = MulAut.conj (⟨y, hyA⟩ : ↥A) := by
      ext z; rfl
    rcases hdich y hyT with h | h
    · have h1 : indAut A y (hWN (hTW hyT)) = 1 :=
        (MulAut.congr e).injective (by rw [h, map_one])
      rw [hconj] at h1
      have hc : (⟨y, hyA⟩ : ↥A) ∈ Subgroup.center ↥A := by
        rw [Subgroup.mem_center_iff]
        intro z
        have h2 := congrArg (fun f : MulAut ↥A => ((f z : ↥A) : Y)) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        have h2' : y * (z : Y) * y⁻¹ = (z : Y) := h2
        apply Subtype.ext
        calc (z : Y) * y = (y * (z : Y) * y⁻¹) * y := by rw [h2']
          _ = y * z := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
    · exfalso
      rw [hconj, congr_conj] at h
      exact hout _ h
  refine ⟨hTA, ?_⟩
  let C₀ : Subgroup Y := A ⊓ Subgroup.centralizer (Tb : Set Y)
  have hC₀A : C₀ ≤ A := inf_le_left
  have hmap : (C₀.subgroupOf A).map e.toMonoidHom = fixSub g := by
    ext z
    rw [Subgroup.mem_map, mem_fixSub]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hkey x).1 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).2
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨(e.symm z).2, (hkey _).2 ?_⟩
      rw [e.apply_symm_apply]
      exact hz
  exact ⟨(Subgroup.subgroupOfEquivOfLe hC₀A).symm.trans
    ((Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hmap))⟩

end CaseII

structure GoodDer (C : Type) [Group C] : Prop where
  simple : IsSimpleGroup ↥(commutator C)
  nonab : ¬ IsMulCommutative ↥(commutator C)

theorem GoodDer.of_mulEquiv {C C' : Type} [Group C] [Group C'] (e : C ≃* C') (h : GoodDer C) :
    GoodDer C' := by
  obtain ⟨f⟩ := Lemma137.mulEquiv_commutator e
  refine ⟨f.isSimpleGroup_congr.1 h.simple, fun hc => h.nonab ⟨⟨fun a b => f.injective ?_⟩⟩⟩
  rw [map_mul, map_mul]
  exact hc.is_comm.comm _ _

theorem goodDer_of_simple {X : Type} [Group X] [IsSimpleGroup X] (hnc : ¬ IsMulCommutative X) :
    GoodDer X := by
  have hc : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exact absurd ((commutator_eq_bot_iff X).1 h) hnc
    · exact h
  have e : ↥(commutator X) ≃* X := (MulEquiv.subgroupCongr hc).trans Subgroup.topEquiv
  refine ⟨e.isSimpleGroup_congr.2 inferInstance, fun hcomm => hnc ⟨⟨fun a b => e.symm.injective ?_⟩⟩⟩
  rw [map_mul, map_mul]
  exact hcomm.is_comm.comm _ _

theorem goodDer_perm {n : ℕ} (hn : 5 ≤ n) : GoodDer (Equiv.Perm (Fin n)) := by
  have h5' : 5 ≤ Nat.card (Fin n) := by simpa using hn
  have hc : commutator (Equiv.Perm (Fin n)) = alternatingGroup (Fin n) :=
    alternatingGroup.commutator_perm_eq h5'
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5'
  have e : ↥(commutator (Equiv.Perm (Fin n))) ≃* ↥(alternatingGroup (Fin n)) :=
    MulEquiv.subgroupCongr hc
  refine ⟨e.isSimpleGroup_congr.2 inferInstance, fun hcomm => ?_⟩
  have h2 : IsMulCommutative ↥(alternatingGroup (Fin n)) :=
    ⟨⟨fun a b => e.symm.injective (by rw [map_mul, map_mul]; exact hcomm.is_comm.comm _ _)⟩⟩
  rw [alternatingGroup.isMulCommutative_iff_card_le_three] at h2
  simp at h2
  omega

theorem pPrimeCore_eq_bot_of_equiv {p : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : GLAPPrimeCore p Y = ⊥) : GLAPPrimeCore p X = ⊥ := by
  have := glaPPrimeCore_map_iso p e
  rw [h] at this
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 this

theorem alt_deg_unique {a b : ℕ} {X : Type} [Group X] (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hXa : IsAltType a X) (hXb : IsAltType b X) : a = b := by
  obtain ⟨ea⟩ := hXa
  obtain ⟨eb⟩ := hXb
  haveI : Nontrivial (Fin a) := Fin.nontrivial_iff_two_le.2 ha
  haveI : Nontrivial (Fin b) := Fin.nontrivial_iff_two_le.2 hb
  have h1 : Nat.card (alternatingGroup (Fin a)) = Nat.card (alternatingGroup (Fin b)) :=
    Nat.card_congr (ea.symm.trans eb).toEquiv
  have h2a := two_mul_nat_card_alternatingGroup (α := Fin a)
  have h2b := two_mul_nat_card_alternatingGroup (α := Fin b)
  rw [Nat.card_perm, Nat.card_fin] at h2a h2b
  have : Nat.factorial a = Nat.factorial b := by rw [← h2a, ← h2b, h1]
  exact (Nat.factorial_inj (by omega : 1 < a)).1 this

structure TypeData (p : ℕ) (X C : Type) [Group X] [Group C] : Prop where
  good : GoodDer C
  noP : GLAPPrimeCore p C = ⊥
  omega : ∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) X → Nonempty (C ≃* ↥(StatedSp n (ZMod 2)))
  alt : ∀ k : ℕ, IsAltType (k * p + 2) X → Nonempty (C ≃* Equiv.Perm (Fin (k * p)))

theorem typeData_of_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hAlt : Lemma118R.Input10_6AltRank)
    (hOmA : Input3_3OmegaAlt) {X : Type} [Group X] [Finite X]
    (hrank : 3 < p ∨ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {k : ℕ} (hk : 1 ≤ k)
    (hX : IsAltType (k * p + 2) X) {C : Type} [Group C]
    (hC : Nonempty (C ≃* Equiv.Perm (Fin (k * p)))) : TypeData p X C := by
  obtain ⟨eC⟩ := hC
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup X) = k := Prop139.pRank_top_alt hp hp2 hAlt hk hX
  have hk5 : 5 ≤ k * p := by
    rw [hrk] at hrank
    rcases hrank with h | h
    · have : p ≠ 4 := by rintro rfl; norm_num at hp
      have h5 : 5 ≤ p := by omega
      nlinarith
    · nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact GoodDer.of_mulEquiv eC.symm (goodDer_perm hk5)
  · exact pPrimeCore_eq_bot_of_equiv eC
      (pPrimeCore_perm_eq_bot hk5 hp hp2 (Nat.le_mul_of_pos_left p hk))
  · intro ε n hΩ
    obtain ⟨f⟩ := hOmA p k hp hp2 ε n X hX hΩ
    exact ⟨eC.trans f.symm⟩
  · intro k₂ hX₂
    have hab : k₂ * p + 2 = k * p + 2 := alt_deg_unique (by omega) (by omega) hX₂ hX
    have hkk : k₂ = k := by
      have : k₂ * p = k * p := by omega
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    subst hkk
    exact ⟨eC⟩

theorem typeData_of_beta {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hAlt : Lemma118R.Input10_6AltRank)
    (hSp : Input3_3SpFacts) (hOmU : Input3_3OmegaUnique) (hOmA : Input3_3OmegaAlt)
    {X : Type} [Group X] [Finite X] (hrank : 3 < p ∨ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {ε' : Bool} {n' : ℕ} (hn' : 1 ≤ n') (hfp : HasFixedPointFreeOrder ε' n' p)
    (hX : IsOmegaTwo ε' (n' + 1) X) {C : Type} [Group C] [Finite C]
    (hC : Nonempty (C ≃* ↥(StatedSp n' (ZMod 2)))) : TypeData p X C := by
  have hn2 : 2 ≤ n' := by
    by_contra hlt
    have h1 : n' = 1 := by omega
    subst h1
    obtain ⟨hp3, h5⟩ := omegaFour hp hp2 hfp hX
    subst hp3
    have h6 := Prop139.pRank_top_alt hp hp2 hAlt (k := 1) le_rfl h5
    rcases hrank with h | h
    · omega
    · omega
  obtain ⟨hnoP, hsimp, hncomm⟩ := hSp p hp hp2 ε' n' hn2 hfp C hC
  refine ⟨⟨hsimp, hncomm⟩, hnoP, ?_, ?_⟩
  · intro ε n hΩ
    obtain ⟨h1, h2⟩ := hOmU ε' ε n' n X hX hΩ
    subst h1
    subst h2
    exact hC
  · intro k hA
    obtain ⟨f⟩ := hOmA p k hp hp2 ε' n' X hA hX
    obtain ⟨eC⟩ := hC
    exact ⟨eC.trans f⟩

section CaseIIData

variable {G : Type} [Group G] [Finite G]

noncomputable def eXBar {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hLcomp : GLAPComponent p M L) (hbl : IsGLBlock M L) :
    (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(barX p M L) :=
  (QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two_of_block hp hp2 hLcomp hbl).symm).trans
    (quotEquivBarX hp hLcomp.1 hLcomp.2.1)

theorem pRank_top_X {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hLcomp : GLAPComponent p M L) (hbl : IsGLBlock M L) :
    CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = CFSG.Open.pRank p L := by
  haveI : Fact p.Prime := ⟨hp⟩
  let e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ GLAPPrimeCore p ↥L) :=
    QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two_of_block hp hp2 hLcomp hbl).symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e1]
  exact Prop139.pRank_top_barOf p L

theorem caseII_data {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M D L : Subgroup G}
    (hAlt : Lemma118R.Input10_6AltRank) (hOmT : Input9_6OmegaTransv) (hSp : Input3_3SpFacts)
    (hOmU : Input3_3OmegaUnique) (hOmA : Input3_3OmegaAlt)
    (hLcomp : GLAPComponent p M L) (hbl : IsGLBlock M L) (hrank : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L)
    (hNo7 : p = 3 → ¬ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 7)))
    (hiv : Prop95Alpha p M D L ∨ Prop95Beta p M D L ∨ Prop95Gamma p M D L) :
    ∃ (Λ : Type) (_ : Group Λ) (e : ↥(barX p M L) ≃* Λ) (g : MulAut Λ),
      (inducedAutGroup (barX p M (gammaD D)) (barX p M L)).map (MulAut.congr e).toMonoidHom =
        Subgroup.zpowers g ∧
      Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 2 ∧
      (∀ a : Λ, MulAut.conj a ≠ g) ∧
      TypeData p (↥L ⧸ CFSG.pCore 2 ↥L) ↥(fixSub g) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hrankX : 3 < p ∨ 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) := by
    rw [pRank_top_X hp hp2 hLcomp hbl]
    exact hrank
  let eX := eXBar hp hp2 hLcomp hbl
  rcases hiv with ⟨k, hk, hLM', e, τ, hτ, hcard, hAct, -⟩ | hβ | ⟨hp3', e, -, -, -⟩
  · refine ⟨_, inferInstance, e, MulAut.conjNormal τ, hAct, hcard,
      fun a => conj_ne_conjNormal (by nlinarith) hτ a, ?_⟩
    exact typeData_of_alt hp hp2 hAlt hOmA hrankX hk ⟨eX.trans e⟩ (alt_centralizer_equiv hτ)
  · obtain ⟨n', hn', hβ'⟩ := hβ
    rcases hβ' with ⟨hfp, hbw⟩ | ⟨hfp, hbw⟩
    · obtain ⟨hLM', e, hcard, ⟨t, ht, hQt, hTv, hAct⟩, -⟩ := hbw
      obtain ⟨hout, hSpIso⟩ := hOmT.1 n' hn' t ht hQt hTv
      haveI : Finite ↥(StatedOmega (StatedQuadPlus (n' + 1) (ZMod 2))) :=
        Finite.of_equiv _ e.toEquiv
      refine ⟨_, inferInstance, e, _, hAct, hcard, hout, ?_⟩
      exact typeData_of_beta hp hp2 hAlt hSp hOmU hOmA hrankX hn' hfp ⟨eX.trans e⟩ hSpIso
    · obtain ⟨hLM', e, hcard, ⟨t, ht, hQt, hTv, hAct⟩, -⟩ := hbw
      obtain ⟨hout, hSpIso⟩ := hOmT.2 n' hn' t ht hQt hTv
      haveI : Finite ↥(StatedOmega (StatedQuadMinus (n' + 1) (ZMod 2) 1 1)) :=
        Finite.of_equiv _ e.toEquiv
      refine ⟨_, inferInstance, e, _, hAct, hcard, hout, ?_⟩
      exact typeData_of_beta hp hp2 hAlt hSp hOmU hOmA hrankX hn' hfp ⟨eX.trans e⟩ hSpIso
  · exact absurd ⟨eX.trans e⟩ (hNo7 hp3')

end CaseIIData

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem pCoreTwo_le_of_isSubnormal {H K : Subgroup G} (h : IsSubnormal H K) :
    pCoreOf 2 H ≤ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction h with
  | refl H => exact le_rfl
  | @step H M K hHM hnorm _ ih =>
    refine le_trans ?_ ih
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
    exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hnorm).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H)

theorem inf_le_core_of_inf_eq_bot {p : ℕ} {M L T : Subgroup G} (hLM : L ≤ M) (hTM : T ≤ M)
    (h : barX p M T ⊓ barX p M L = ⊥) : T ⊓ L ≤ GLAPPrimeCoreOf p M := by
  intro x hx
  have hxM : x ∈ M := hLM hx.2
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨x, hxM⟩ : ↥M) ∈
      barX p M T ⊓ barX p M L :=
    ⟨Lemma137.mk_mem_barX' hTM hx.1, Lemma137.mk_mem_barX' hLM hx.2⟩
  rw [h, Subgroup.mem_bot] at h1
  exact (mem_gLAPPrimeCoreOf_iff p M x).2 ⟨hxM, (QuotientGroup.eq_one_iff _).1 h1⟩

theorem not_comm_of_simple_center_bot {X : Type} [Group X] [IsSimpleGroup X]
    (hZ : Subgroup.center X = ⊥) : ¬ IsMulCommutative X := by
  intro hc
  have h1 : Subgroup.center X = ⊤ := Subgroup.center_eq_top_iff.2 hc
  rw [hZ] at h1
  have : Subsingleton X := ⟨fun a b => by
    have ha : a ∈ (⊤ : Subgroup X) := Subgroup.mem_top a
    have hb : b ∈ (⊤ : Subgroup X) := Subgroup.mem_top b
    rw [← h1, Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  exact not_subsingleton X this

theorem concl_good {p : ℕ} {N J : Subgroup G} (hJN : J ≤ N) {C : Type} [Group C]
    (φ : ↥(barX p N J) ≃* C) (hC : GoodDer C) :
    barX p N (derivedInf J) = ⁅barX p N J, barX p N J⁆ ∧
      IsSimpleGroup ↥(barX p N (derivedInf J)) ∧ ¬ IsMulCommutative ↥(barX p N (derivedInf J)) := by
  set Jt := barX p N J with hJt
  have hG := GoodDer.of_mulEquiv φ.symm hC
  obtain ⟨f⟩ := Lemma137.eqv_commutator Jt
  have hS1 : IsSimpleGroup ↥⁅Jt, Jt⁆ := f.isSimpleGroup_congr.1 hG.simple
  have hS2 : ¬ IsMulCommutative ↥⁅Jt, Jt⁆ := fun hc =>
    hG.nonab ⟨⟨fun a b => f.injective (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _)⟩⟩
  have hperf : ⁅⁅Jt, Jt⁆, ⁅Jt, Jt⁆⁆ = ⁅Jt, Jt⁆ := by
    have hc : commutator ↥⁅Jt, Jt⁆ = ⊤ := by
      haveI := hS1
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥⁅Jt, Jt⁆) with h | h
      · exact absurd ((commutator_eq_bot_iff _).1 h) hS2
      · exact h
    rw [← Lemma137.map_commutator_subtype, hc, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK := barX_derivedInf_eq hJN hperf
  rw [hK]
  exact ⟨rfl, hS1, hS2⟩

theorem Iof_eq_iSup_summand (p : ℕ) (M D : Subgroup G) :
    Iof p M D = ⨆ x : {L0 : Subgroup G // Prop139.SummandOf p M D L0}, x.1 := by
  unfold Iof
  exact le_antisymm (iSup₂_le fun L0 h => le_iSup_of_le ⟨L0, h⟩ le_rfl)
    (iSup_le fun x => le_iSup₂_of_le x.1 x.2 le_rfl)

theorem istar_component' {p : ℕ} (hp : p.Prime) {M D L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) :
    ∃ g ∈ M, ∃ L0 : Subgroup G, Prop139.SummandOf p M D L0 ∧ L = GLBConj g L0 := by
  have hNM : Istar p M D ≤ M := istar_le_M p M D
  have hsubN : IsSubnormal (Istar p M D) M := istar_isSubnormal p M D
  have hLN : L ≤ Istar p M D := hL.1
  have hLM : L ≤ M := hLN.trans hNM
  have hsnL : IsSubnormal L M := isSubnormal_trans' hL.2.1 hsubN
  have hcompQ : IsComponentOf (barX p M L) ⊤ := by
    have e : ↥(barX p M L) ≃* ↥(barX p (Istar p M D) L) :=
      (quotEquivBarX hp hLM hsnL).symm.trans (quotEquivBarX hp hLN hL.2.1)
    refine ⟨le_top, ?_, ?_⟩
    · have := isSubnormal_barX p (C := M) hsnL
      rwa [barX_self] at this
    · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
        hL.2.2.1.2.2
  have hK_le : barX p M L ≤ ⨆ i : (↥M ⧸ GLAPPrimeCore p ↥M) × {L0 : Subgroup G // Prop139.SummandOf p M D L0},
      GLBConj i.1 (barX p M (i.2 : Subgroup G)) :=
    barX_le_iSup_conj_of (fun t : {L0 : Subgroup G // Prop139.SummandOf p M D L0} => t.1)
      (fun t => t.2.1.1) (Iof_eq_iSup_summand p M D) (Iof_le_M p M D) hLN
  have hcomp0 : ∀ t : {L0 : Subgroup G // Prop139.SummandOf p M D L0}, IsComponentOf (barX p M t.1) ⊤ :=
    fun t => t.2.1.2.2.1
  have hF : ∀ i : (↥M ⧸ GLAPPrimeCore p ↥M) × {L0 : Subgroup G // Prop139.SummandOf p M D L0},
      IsComponentOf (GLBConj i.1 (barX p M i.2.1)) ⊤ := fun i => isComponentOf_gLBConj (hcomp0 i.2) i.1
  obtain ⟨⟨y, ⟨L0, hL0⟩⟩, hFy⟩ := layer_mem hcompQ hF hK_le
  obtain ⟨⟨g, hg⟩, hgy⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥M) y
  subst hgy
  rw [← barX_gLBConj_eq p hg L0] at hFy
  have hL0M : GLBConj g L0 ≤ Istar p M D := by
    refine le_iSup₂_of_le (f := fun g (_ : g ∈ M) => GLBConj g (Iof p M D)) g hg ?_
    exact gLBConj_mono g (le_iSup₂_of_le (f := fun L (_ : Prop139.SummandOf p M D L) => L) L0 hL0 le_rfl)
  have hN2 : GLAPComponent p (Istar p M D) (GLBConj g L0) :=
    glaPComponent_of_le hp (glaPComponent_conj_mem hL0.1 hg) hL0M hNM
  have hbarN : barX p (Istar p M D) L = barX p (Istar p M D) (GLBConj g L0) := by
    have hJ : ∀ (K J : Subgroup G), K ≤ Istar p M D → J ≤ Istar p M D → K ≤ M → J ≤ M →
        barX p M K ≤ barX p M J → barX p (Istar p M D) K ≤ barX p (Istar p M D) J := by
      intro K J hKN hJN hKM hJM hle
      refine barX_le_of_forall hJN fun k hk => ?_
      obtain ⟨j, hj, hjk⟩ := exists_of_barX_le hle hk (hKM hk)
      refine ⟨j, hj, ?_⟩
      have hmem : j⁻¹ * k ∈ Istar p M D ⊓ GLAPPrimeCoreOf p M :=
        ⟨(Istar p M D).mul_mem ((Istar p M D).inv_mem (hJN hj)) (hKN hk), hjk⟩
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsubN] at hmem
      exact hmem
    have hL0M' : GLBConj g L0 ≤ M := hL0M.trans hNM
    exact le_antisymm (hJ L (GLBConj g L0) hLN hL0M hLM hL0M' hFy.symm.le)
      (hJ (GLBConj g L0) L hL0M hLN hL0M' hLM hFy.le)
  exact ⟨g, hg, L0, hL0, glaPComponent_unique hL hN2 hbarN⟩

end Assembly

end Lemma137b

open Lemma137b

theorem lemma137_ii_iii_of_inputs
    (h111 : Prop111Statement) (h1117 : Prop1117Statement) (h121 : Prop121_of_cexStatement)
    (h127 : Prop127_of_cexStatement) (hP95 : Prop95) (hL133 : Lemma133Statement)
    (hNo7 : Lemma137_noA7Statement) (hAlt : Lemma118R.Input10_6AltRank)
    (hOmT : Input9_6OmegaTransv) (hSp : Input3_3SpFacts) (hOmU : Input3_3OmegaUnique)
    (hOmA : Input3_3OmegaAlt) : Lemma137_ii_iiiStatement := by
  intro G _ _ m p B M E A D T h L hL hL1
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, L0, hL0, hLeq⟩ := istar_component' hp hL
  have hLcomp : GLAPComponent p M L := by
    rw [hLeq]
    exact glaPComponent_conj_mem hL0.1 hg
  have hLM : L ≤ M := hLcomp.1
  have hsn : IsSubnormal L M := hLcomp.2.1
  obtain ⟨⟨hbl, -, -⟩, -⟩ := (hL133 h).2 L hL
  have hPH := prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD
  obtain ⟨-, -, hcomp⟩ := hP95 G m p hS M D hPH
  obtain ⟨hnormW, hiv⟩ := hcomp L hLcomp
  have hPM : gammaStar p D ≤ M :=
    (prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h.toSec11 h.hD).2
  have hTM : T ≤ M := h.hT2.trans hPM
  have hT2 : IsPGroup 2 ↥T := (isPGroup_gammaStar p D).to_le h.hT2
  have hTW : barX p M T ≤ barX p M (gammaD D) :=
    barX_mono p (h.hT2.trans (gammaStar_le_gammaD p D))
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    intro t ht
    refine mem_normalizer_of_barX_normalizes hp le_rfl hLcomp (hTM ht)
      (Subgroup.le_normalizer (hTM ht)) ?_
    exact hnormW (hTW (Lemma137.mk_mem_barX' hTM ht))
  have hb : L ⊓ GLAPPrimeCoreOf p M ≤ T := by
    rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
    have h1 : GLAPPrimeCoreOf p L = pCoreOf 2 L := by
      unfold GLAPPrimeCoreOf pCoreOf
      rw [glaPPrimeCore_eq_pCore_two_of_block hp hp2 hLcomp hbl]
    rw [h1]
    exact (pCoreTwo_le_of_isSubnormal hsn).trans h.hT1
  have hZ : Subgroup.center ↥(barX p M L) = ⊥ :=
    Prop139.center_bot_of_mulEquiv (quotEquivBarX hp hLM hsn).symm
      (center_quotient_eq_bot_of_block hp hp2 hLcomp hbl)
  have hOLb : GLAPPrimeCore p ↥(barX p M L) = ⊥ :=
    pPrimeCore_eq_bot_of_equiv (quotEquivBarX hp hLM hsn).symm (glaPPrimeCore_quotient_eq_bot hp)
  let eX := eXBar hp hp2 hLcomp hbl
  have hJN : Nof T ⊓ L ≤ Nof T := inf_le_left
  by_cases hcen : barX p M T ≤ Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M))
  ·
    have hTLb : barX p M T ⊓ barX p M L = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
      obtain ⟨hyT, hyL⟩ := hy
      have hyc : (⟨y, hyL⟩ : ↥(barX p M L)) ∈ Subgroup.center ↥(barX p M L) := by
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hcen hyT) w w.2)
      rw [hZ, Subgroup.mem_bot] at hyc
      exact congrArg Subtype.val hyc
    have hc : T ⊓ L ≤ GLAPPrimeCoreOf p M := inf_le_core_of_inf_eq_bot hLM hTM hTLb
    have hC₀ : barX p M L = barX p M L ⊓ Subgroup.centralizer
        ((barX p M T : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      refine (inf_eq_left.2 fun x hx => Subgroup.mem_centralizer_iff.2 fun t ht => ?_).symm
      exact (Subgroup.mem_centralizer_iff.1 (hcen ht) x hx).symm
    obtain ⟨φ⟩ := barX_cent_equiv hp hp2 hLM hTM hT2 hTL hb hc (barX p M L) hC₀ hOLb
    haveI : IsSimpleGroup ↥(barX p M L) := eX.isSimpleGroup_congr.1 hbl.simple
    have hgood : GoodDer ↥(barX p M L) := goodDer_of_simple (not_comm_of_simple_center_bot hZ)
    obtain ⟨hK1, hK2, hK3⟩ := concl_good hJN φ hgood
    refine ⟨hK1, hK2, hK3, ?_, ?_⟩
    · intro ε n hX
      exact ⟨fun _ => IsOmegaTwo.of_mulEquiv (eX.trans φ.symm) hX, fun hn => absurd hcen hn⟩
    · intro k hX
      obtain ⟨f⟩ := hX
      exact ⟨fun _ => ⟨(φ.trans eX.symm).trans f⟩, fun hn => absurd hcen hn⟩
  ·
    have hiv' : Prop95Alpha p M D L ∨ Prop95Beta p M D L ∨ Prop95Gamma p M D L := by
      rcases hiv with hc | ⟨-, h'⟩
      · exact absurd (hTW.trans hc) hcen
      · exact h'
    obtain ⟨Λ, _, e, g, hInd, hcard, hout, hTD⟩ := caseII_data hp hp2 hAlt hOmT hSp hOmU hOmA
      hLcomp hbl hL1 (hNo7 h hL) hiv'
    obtain ⟨hTLb, ⟨ψ⟩⟩ := caseII_abstract (barX p M L) (barX p M (gammaD D)) (barX p M T) hTW hnormW
      e g hInd hcard hout hZ hcen
    have hc : T ⊓ L ≤ GLAPPrimeCoreOf p M := inf_le_core_of_inf_eq_bot hLM hTM hTLb
    have hO : GLAPPrimeCore p ↥(barX p M L ⊓ Subgroup.centralizer
        ((barX p M T : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) = ⊥ :=
      pPrimeCore_eq_bot_of_equiv ψ hTD.noP
    obtain ⟨φ⟩ := barX_cent_equiv hp hp2 hLM hTM hT2 hTL hb hc _ rfl hO
    obtain ⟨hK1, hK2, hK3⟩ := concl_good hJN (φ.trans ψ) hTD.good
    refine ⟨hK1, hK2, hK3, ?_, ?_⟩
    · intro ε n hX
      obtain ⟨f⟩ := hTD.omega ε n hX
      exact ⟨fun hc' => absurd hc' hcen, fun _ => ⟨(φ.trans ψ).trans f⟩⟩
    · intro k hX
      obtain ⟨f⟩ := hTD.alt k hX
      exact ⟨fun hc' => absurd hc' hcen, fun _ => ⟨(φ.trans ψ).trans f⟩⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
