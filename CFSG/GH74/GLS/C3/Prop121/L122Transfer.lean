module

public import CFSG.GH74.GLS.C3.Prop121.L122Seven
public import CFSG.GH74.GLS.C3.Prop121.FnFacts

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2.Model

@[expose] def extP (e : Perm (Fin 7)) : Perm (Fin 8) := Equiv.Perm.decomposeFin.symm (0, e)

theorem extP_zero (e : Perm (Fin 7)) : extP e 0 = 0 := by
  simp [extP]

theorem extP_succ (e : Perm (Fin 7)) (j : Fin 7) : extP e j.succ = (e j).succ := by
  simp [extP]

theorem extP_mul (e f : Perm (Fin 7)) : extP (e * f) = extP e * extP f := by
  refine Equiv.ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [extP_zero]
  · simp [extP_succ, Perm.mul_apply]

theorem extP_one : extP 1 = 1 := by
  refine Equiv.ext fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [extP_zero]
  · simp [extP_succ]

theorem extP_inv (e : Perm (Fin 7)) : extP e⁻¹ = (extP e)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← extP_mul, mul_inv_cancel, extP_one])

theorem extP_inj : Function.Injective extP := by
  intro e f h
  refine Equiv.ext fun j => ?_
  have := congrArg (fun p : Perm (Fin 8) => p j.succ) h
  simp only [extP_succ] at this
  exact Fin.succ_injective _ this

theorem sign_extP (e : Perm (Fin 7)) : sign (extP e) = sign e := by
  simp [extP, Equiv.Perm.decomposeFin.symm_sign]

theorem card_support_extP (e : Perm (Fin 7)) : (extP e).support.card = e.support.card := by
  have : (extP e).support = e.support.map ⟨Fin.succ, Fin.succ_injective _⟩ := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [extP_zero]
    · simp [extP_succ, Equiv.Perm.mem_support]
  rw [this, Finset.card_map]

theorem exists_extP (σ : Perm (Fin 8)) (h0 : σ 0 = 0) :
    σ = extP (Equiv.Perm.decomposeFin σ).2 := by
  have h1 := Equiv.Perm.decomposeFin.symm_apply_apply σ
  have h2 : (Equiv.Perm.decomposeFin σ).1 = 0 := by
    have h3 : (Equiv.Perm.decomposeFin.symm ((Equiv.Perm.decomposeFin σ).1,
        (Equiv.Perm.decomposeFin σ).2)) 0 = σ 0 := by
      rw [Prod.mk.eta, h1]
    rw [Equiv.Perm.decomposeFin_symm_apply_zero, h0] at h3
    exact h3
  rw [extP]
  conv_lhs => rw [← h1]
  rw [show Equiv.Perm.decomposeFin σ = (0, (Equiv.Perm.decomposeFin σ).2) from Prod.ext h2 rfl]

theorem threeCycle_stab_seven {G : Type} [Group G] {K L : Subgroup G} (hKL : K ≤ L)
    (lam : ↥L ≃* alternatingGroup (Fin 8))
    (hstab : ∀ l : ↥L, (l : G) ∈ K ↔
      ((lam l : alternatingGroup (Fin 8)) : Perm (Fin 8)) 0 = 0)
    (hAut : ∀ α : MulAut (alternatingGroup (Fin 7)), ∃ π : Perm (Fin 7),
      ∀ a : alternatingGroup (Fin 7),
        ((α a : alternatingGroup (Fin 7)) : Perm (Fin 7)) = π * a * π⁻¹)
    (ε : ↥K ≃* alternatingGroup (Fin 7)) (k : ↥K)
    (hk : ((ε k : alternatingGroup (Fin 7)) : Perm (Fin 7)).IsThreeCycle) :
    ((lam (Subgroup.inclusion hKL k) : alternatingGroup (Fin 8)) : Perm (Fin 8)).IsThreeCycle := by
  classical
  let lk : ↥K → Perm (Fin 8) := fun k =>
    ((lam (Subgroup.inclusion hKL k) : alternatingGroup (Fin 8)) : Perm (Fin 8))
  have hlk0 : ∀ k, lk k 0 = 0 := fun k => (hstab (Subgroup.inclusion hKL k)).1 k.2
  let μ : ↥K → Perm (Fin 7) := fun k => (Equiv.Perm.decomposeFin (lk k)).2
  have hμ : ∀ k, extP (μ k) = lk k := fun k => (exists_extP (lk k) (hlk0 k)).symm
  have hlkmul : ∀ k k', lk (k * k') = lk k * lk k' := by
    intro k k'
    simp [lk]
  have hlk1 : lk 1 = 1 := by simp [lk]
  have hμmul : ∀ k k', μ (k * k') = μ k * μ k' := fun k k' =>
    extP_inj (by rw [extP_mul, hμ, hμ, hμ, hlkmul])
  have hμ1 : μ 1 = 1 := extP_inj (by rw [hμ, hlk1, extP_one])
  have hμsign : ∀ k, sign (μ k) = 1 := fun k => by
    rw [← sign_extP, hμ]
    exact mem_alternatingGroup.1 (lam _).2
  let μ' : ↥K →* alternatingGroup (Fin 7) :=
    { toFun := fun k => ⟨μ k, mem_alternatingGroup.2 (hμsign k)⟩
      map_one' := Subtype.ext hμ1
      map_mul' := fun a b => Subtype.ext (hμmul a b) }
  have hμinj : Function.Injective μ' := by
    intro a b h
    have h1 : μ a = μ b := congrArg Subtype.val h
    have h2 : lk a = lk b := by rw [← hμ, ← hμ, h1]
    have h3 : lam (Subgroup.inclusion hKL a) = lam (Subgroup.inclusion hKL b) := Subtype.ext h2
    exact Subgroup.inclusion_injective hKL (lam.injective h3)
  let φ : alternatingGroup (Fin 7) →* alternatingGroup (Fin 7) := μ'.comp ε.symm.toMonoidHom
  have hφinj : Function.Injective φ := hμinj.comp ε.symm.injective
  have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hφinj
  obtain ⟨π, hπ⟩ := hAut (MulEquiv.ofBijective φ hφbij)
  have h1 : μ k = π * ((ε k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * π⁻¹ := by
    have := hπ (ε k)
    simpa [φ, μ'] using this
  have h2 : lk k = extP π * extP ((ε k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * (extP π)⁻¹ := by
    rw [← hμ, h1, extP_mul, extP_mul, extP_inv]
  have h3 : (lk k).support.card = 3 := by
    rw [h2, Equiv.Perm.support_conj, Finset.card_map, card_support_extP]
    exact Equiv.Perm.IsThreeCycle.card_support hk
  exact card_support_eq_three_iff.1 h3

theorem aut_alt_seven (α : MulAut (alternatingGroup (Fin 7))) :
    ∃ π : Perm (Fin 7), ∀ a : alternatingGroup (Fin 7),
      ((α a : alternatingGroup (Fin 7)) : Perm (Fin 7)) = π * a * π⁻¹ := by
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)).2 α
  exact ⟨σ, fun a => by rw [← hσ]; exact MulAut.conjNormal_apply σ a⟩

theorem clause4_seven
    {G : Type} [Group G] [Finite G] (hC : pRank 2 G ≤ 4) {x : G}
    {K T Q S : Subgroup G} {a₀ : G} {t u g : G} (h : IsAConfig 7 x K T Q S a₀)
    (hS : Stage3Loc 7 x K Q t u g) {L : Subgroup G} (hKL : K ≤ L)
    (lam : ↥L ≃* alternatingGroup (Fin 8))
    (hstab : ∀ l : ↥L, (l : G) ∈ K ↔
      ((lam l : alternatingGroup (Fin 8)) : Perm (Fin 8)) 0 = 0) :
    ((lam ⟨g * t * g⁻¹, hKL hS.gt_K⟩ : alternatingGroup (Fin 8)) : Perm (Fin 8)).IsThreeCycle := by
  classical
  have hn : (7 : ℕ) = 5 ∨ (7 : ℕ) = 6 ∨ (7 : ℕ) = 7 := Or.inr (Or.inr rfl)
  have hG4 : pRank 2 G ≤ 4 := hC
  obtain ⟨ι, -, hι2⟩ := exists_coord hn hG4 h
  have hCQ := centralizer_Q_eq hn hG4 h (fnFacts 7 hn)
  have hKC : K ≤ centralizer ({x} : Set G) := h.K_le_C
  have hmem : g * t * g⁻¹ ∈ centralizer ({x} : Set G) := hKC hS.gt_K
  have h3 := lemma122_seven h hS ι hι2 hCQ hmem
  let lamK : ↥K →* alternatingGroup (Fin 7) :=
    ((MonoidHom.fst (Perm (Fin 7)) (Perm (Fin 4))).comp
      ((Fgrp 7).subtype.comp (ι.toMonoidHom.comp (Subgroup.inclusion hKC)))).codRestrict
      (alternatingGroup (Fin 7)) (fun k =>
        mem_alternatingGroup.2 ((K_iff hn h hι2 ⟨k, hKC k.2⟩).1 k.2).1)
  have hlamKinj : Function.Injective lamK := by
    intro k₁ k₂ hk
    have h1 : ι ⟨k₁, hKC k₁.2⟩ = ι ⟨k₂, hKC k₂.2⟩ := by
      apply Subtype.ext
      have e1 := ((K_iff hn h hι2 ⟨k₁, hKC k₁.2⟩).1 k₁.2).2
      have e2 := ((K_iff hn h hι2 ⟨k₂, hKC k₂.2⟩).1 k₂.2).2
      exact Prod.ext (congrArg Subtype.val hk) (e1.trans e2.symm)
    exact Subtype.ext (congrArg (fun z : ↥(centralizer ({x} : Set G)) => (z : G))
      (ι.injective h1))
  obtain ⟨eK⟩ := h.K_equiv_alt
  have hlamKbij : Function.Bijective lamK :=
    hlamKinj.bijective_of_nat_card_le (le_of_eq (Nat.card_congr eK.toEquiv.symm))
  let ε : ↥K ≃* alternatingGroup (Fin 7) := MulEquiv.ofBijective lamK hlamKbij
  have hε : ((ε ⟨g * t * g⁻¹, hS.gt_K⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((ι ⟨g * t * g⁻¹, hmem⟩ : Fgrp 7) : Amb 7).1 := rfl
  exact threeCycle_stab_seven hKL lam hstab aut_alt_seven ε ⟨g * t * g⁻¹, hS.gt_K⟩ (by rw [hε]; exact h3)

end CFSG.GH74.GLS.C3.Prop121
