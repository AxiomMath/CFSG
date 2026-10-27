module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.PlusIrr
public import CFSG.CGT.PushingUpLit.CGT6X.ExtNatIrr
public import CFSG.Quasithin.Background.A1cModuleAut

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG.Quasithin CFSG.Quasithin.XMod CFSG.CGT.PushingUpLit.CGT6
open CFSG.CGT.PushingUpLit.CGT6.TwoEight

namespace OmegaNorm

@[expose] def IsModelAct {P Sg M : Type*} [Group P] [Group M] (S : Subgroup (MulAut P))
    (ψ : P ≃* M) (act : Sg → M → M) : Prop :=
  (∀ g : Sg, ∃ s ∈ S, ∀ p, ψ (s p) = act g (ψ p)) ∧ (∀ s ∈ S, ∃ g : Sg, ∀ p, ψ (s p) = act g (ψ p))

section Transfer

variable {P : Type*} [CommGroup P] {Sg M : Type*} [CommGroup M]

theorem isIrrSec_of_isModelAct {S : Subgroup (MulAut P)} {ψ : P ≃* M} {act : Sg → M → M}
    (h : IsModelAct S ψ act)
    (hirr : ∀ J : Subgroup M, (∀ g : Sg, ∀ m ∈ J, act g m ∈ J) → J = ⊥ ∨ J = ⊤)
    (hnt : ∃ m : M, m ≠ 1) : IsIrrSec ↥S (⊥ : Subgroup P) ⊤ := by
  refine ⟨bot_lt_iff_ne_bot.mpr fun hbot => ?_, fun J hJ _ _ => ?_⟩
  · obtain ⟨m, hm⟩ := hnt
    have : ψ.symm m ∈ (⊥ : Subgroup P) := by rw [← hbot]; trivial
    exact hm (by simpa using this)
  have hJ' : ∀ g : Sg, ∀ m ∈ J.map ψ.toMonoidHom, act g m ∈ J.map ψ.toMonoidHom := by
    rintro g _ ⟨j, hj, rfl⟩
    obtain ⟨s, hs, hsg⟩ := h.1 g
    exact ⟨s j, hJ ⟨s, hs⟩ j hj, hsg j⟩
  rcases hirr _ hJ' with h1 | h1
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective J ψ.injective).mp h1
  · right
    refine eq_top_iff.mpr fun p _ => ?_
    have : ψ p ∈ J.map ψ.toMonoidHom := by rw [h1]; trivial
    obtain ⟨q, hq, hqp⟩ := this
    rwa [ψ.injective hqp] at hq

theorem le_card_eqvEnd_of_isModelAct [Finite P] {S : Subgroup (MulAut P)} {ψ : P ≃* M}
    {act : Sg → M → M} (h : IsModelAct S ψ act) {K : Type*} (sc : K → M →* M)
    (hsc : ∀ c g m, sc c (act g m) = act g (sc c m)) (hinj : Function.Injective sc) :
    Nat.card K ≤ Nat.card ↥(eqvEnd ↥S P) := by
  have hfin := finite_eqvEnd (A := ↥S) (P := P)
  let e : K → AddMonoid.End (Additive P) := fun c =>
    MonoidHom.toAdditive (ψ.symm.toMonoidHom.comp ((sc c).comp ψ.toMonoidHom))
  have he : ∀ c p, toMonoidEnd (e c) p = ψ.symm (sc c (ψ p)) := fun _ _ => rfl
  have hmem : ∀ c, e c ∈ eqvEnd ↥S P := by
    intro c
    rw [mem_eqvEnd_iff]
    intro a p
    obtain ⟨g, hg⟩ := h.2 a a.2
    change toMonoidEnd (e c) ((a : MulAut P) p) = (a : MulAut P) (toMonoidEnd (e c) p)
    rw [he, he, hg, hsc]
    apply ψ.injective
    rw [hg, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  refine Nat.card_le_card_of_injective (fun c => (⟨e c, hmem c⟩ : ↥(eqvEnd ↥S P))) ?_
  intro c c' hcc'
  apply hinj
  refine MonoidHom.ext fun m => ?_
  have h1 := congrArg (fun f : ↥(eqvEnd ↥S P) =>
    toMonoidEnd (f : AddMonoid.End (Additive P)) (ψ.symm m)) hcc'
  simp only [he, MulEquiv.apply_symm_apply] at h1
  exact ψ.symm.injective h1

end Transfer

@[expose] noncomputable def plusScalar (n : ℕ) (c : Fq n) :
    Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)) →*
      Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun m => c • m
      map_zero' := smul_zero c
      map_add' := smul_add c }

theorem plusScalar_act (n : ℕ) (c : Fq n) (g) (m : Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))) :
    plusScalar n c (omegaPlusAct n g m) = omegaPlusAct n g (plusScalar n c m) := by
  change Multiplicative.ofAdd (c • ((g.1 : Matrix (Fin 2) (Fin 2) (Fq n)) *
      Multiplicative.toAdd m * (g.2 : Matrix (Fin 2) (Fin 2) (Fq n)).transpose)) =
    Multiplicative.ofAdd ((g.1 : Matrix (Fin 2) (Fin 2) (Fq n)) * (c • Multiplicative.toAdd m) *
      (g.2 : Matrix (Fin 2) (Fin 2) (Fq n)).transpose)
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem plusScalar_injective (n : ℕ) : Function.Injective (plusScalar n) := by
  intro c c' h
  have h1 := congrArg (fun φ : Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)) →*
    Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)) =>
      Multiplicative.toAdd (φ (Multiplicative.ofAdd 1)) 0 0) h
  change (c • (1 : Matrix (Fin 2) (Fin 2) (Fq n))) 0 0 =
    (c' • (1 : Matrix (Fin 2) (Fin 2) (Fq n))) 0 0 at h1
  simpa using h1

theorem fz_smul_mem_hermSub (n : ℕ) (c : Fz n) {m : Matrix (Fin 2) (Fin 2) (Fq (2 * n))}
    (hm : m ∈ hermSub n) : (c : Fq (2 * n)) • m ∈ hermSub n := by
  intro i j
  have hc : frobHalf n (c : Fq (2 * n)) = c := sigR_Fz n c
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hm i j]
  unfold frobHalf at hc ⊢
  rw [mul_pow, hc]

@[expose] noncomputable def minusScalar (n : ℕ) (c : Fz n) :
    Multiplicative (hermSub n) →* Multiplicative (hermSub n) :=
  AddMonoidHom.toMultiplicative
    { toFun := fun m => ⟨(c : Fq (2 * n)) • m.1, fz_smul_mem_hermSub n c m.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun _ _ => Subtype.ext (smul_add _ _ _) }

theorem minusScalar_act (n : ℕ) [NeZero n] (c : Fz n) (A) (m : Multiplicative (hermSub n)) :
    minusScalar n c (omegaMinusAct n A m) = omegaMinusAct n A (minusScalar n c m) := by
  rw [omegaMinusAct_eq, omegaMinusAct_eq]
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change (c : Fq (2 * n)) • ((A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) *
      (Multiplicative.toAdd m).1 * cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) =
    (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * ((c : Fq (2 * n)) • (Multiplicative.toAdd m).1) *
      cstar n (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem one_mem_hermSub (n : ℕ) : (1 : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) ∈ hermSub n := by
  intro i j
  unfold frobHalf
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij), zero_pow (by positivity)]

theorem minusScalar_injective (n : ℕ) : Function.Injective (minusScalar n) := by
  intro c c' h
  have h1 := congrArg (fun φ : Multiplicative (hermSub n) →* Multiplicative (hermSub n) =>
    (Multiplicative.toAdd (φ (Multiplicative.ofAdd ⟨1, one_mem_hermSub n⟩))).1 0 0) h
  change ((c : Fq (2 * n)) • (1 : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) 0 0 =
    ((c' : Fq (2 * n)) • (1 : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) 0 0 at h1
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h1
  exact Subtype.ext h1

theorem minus_irreducible (n : ℕ) [NeZero n] (J : Subgroup (Multiplicative (hermSub n)))
    (hJ : ∀ A, ∀ m ∈ J, omegaMinusAct n A m ∈ J) : J = ⊥ ∨ J = ⊤ := by
  let e : Multiplicative (hermSub n) ≃* CGT6X.NMod n := AddEquiv.toMultiplicative (minusCoord n)
  have he : ∀ A m, e (omegaMinusAct n A m) = CGT6X.rhoW n A (e m) := by
    intro A m
    rw [omegaMinusAct_eq, CGT6X.rhoW_apply]
    exact (congrArg Multiplicative.ofAdd (minusHom_apply n A (Multiplicative.toAdd m))).symm
  have hJ' : ∀ A, ∀ m ∈ J.map e.toMonoidHom, CGT6X.rhoW n A m ∈ J.map e.toMonoidHom := by
    rintro A _ ⟨j, hj, rfl⟩
    exact ⟨_, hJ A j hj, he A j⟩
  rcases CGT6X.natModule_irreducible n _ hJ' with h | h
  · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective J e.injective).mp h)
  · right
    refine eq_top_iff.mpr fun m _ => ?_
    have : e m ∈ J.map e.toMonoidHom := by rw [h]; trivial
    obtain ⟨q, hq, hqm⟩ := this
    rwa [e.injective hqm] at hq

theorem omega_isIrrSec_card {P : Type*} [CommGroup P] [Finite P] {S : Subgroup (MulAut P)}
    {n : ℕ} (hn : n ≠ 0)
    (h : (∃ ψ : P ≃* Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)),
        IsModelAct S ψ (omegaPlusAct n)) ∨
      ∃ ψ : P ≃* Multiplicative (hermSub n), IsModelAct S ψ (omegaMinusAct n)) :
    IsIrrSec ↥S (⊥ : Subgroup P) ⊤ ∧ 2 ^ n ≤ Nat.card ↥(eqvEnd ↥S P) ∧
      Nat.card P = 2 ^ (4 * n) := by
  have : NeZero n := ⟨hn⟩
  rcases h with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩
  · have hcard : Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))) = 2 ^ (4 * n) := by
      have h1 : Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))) =
          Nat.card (Fin 2 → Fin 2 → Fq n) := Nat.card_congr Multiplicative.toAdd
      rw [h1, Nat.card_fun, Nat.card_fun, GaloisField.card 2 n hn,
        Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin, ← pow_mul, ← pow_mul]
      ring_nf
    refine ⟨isIrrSec_of_isModelAct hψ (natPlus_irreducible n) ⟨Multiplicative.ofAdd 1, ?_⟩, ?_,
      by rw [Nat.card_congr ψ.toEquiv, hcard]⟩
    · intro h1
      have h2 := congrArg
        (fun m : Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)) => Multiplicative.toAdd m 0 0) h1
      simp at h2
    · have := le_card_eqvEnd_of_isModelAct hψ (plusScalar n)
        (fun c g m => plusScalar_act n c g m) (plusScalar_injective n)
      rwa [GaloisField.card 2 n hn] at this
  · refine ⟨isIrrSec_of_isModelAct hψ (minus_irreducible n)
      ⟨Multiplicative.ofAdd ⟨1, one_mem_hermSub n⟩, ?_⟩, ?_, ?_⟩
    · intro h1
      have h2 := congrArg
        (fun m : Multiplicative (hermSub n) => (Multiplicative.toAdd m).1 0 0) h1
      simp at h2
    · have := le_card_eqvEnd_of_isModelAct hψ (minusScalar n)
        (fun c g m => minusScalar_act n c g m) (minusScalar_injective n)
      rwa [card_Fz] at this
    · rw [Nat.card_congr (ψ.toEquiv.trans (minusKappa n)), Nat.card_prod, Nat.card_prod, card_Fz,
        GaloisField.card 2 (2 * n) (by omega), ← pow_add, ← pow_add]
      congr 1
      ring

end OmegaNorm

end CFSG.CGT.PushingUpLit.ThmOne
