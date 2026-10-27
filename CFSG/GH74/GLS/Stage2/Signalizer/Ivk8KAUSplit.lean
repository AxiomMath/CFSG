module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUDef
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUBlock

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.Burgoyne.PSL (commutator_eq_self_of_isQuasisimple
  signMat_mul_self)
open scoped commutatorElement

section Comp

theorem ka_all_of_components_fix_of_finite {G Y : Type} [Group G] [Group Y] [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (π : G →* Y) (hπ : Function.Surjective π) (φ : G →* G) {α : MulAut Y}
    (hφ : ∀ g, α (π g) = π (φ g)) {S : Subgroup G} (hfix0 : ∀ g ∈ S, φ g = g)
    (hnorm : ∀ h : G, π (φ h) = π h → ∀ g ∈ S, h * g * h⁻¹ ∈ S) (hperf : ⁅S, S⁆ = S)
    {ι : Type} [Finite ι] (Fq : ι → Subgroup G) (hq : ∀ i, IsQuasisimple (Fq i))
    (hle : ∀ i, Fq i ≤ S) (hsup : S ≤ ⨆ i, Fq i)
    (hFn : ∀ i, ∀ h ∈ S, ∀ g ∈ Fq i, h * g * h⁻¹ ∈ Fq i)
    (hfix : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P' : Subgroup (MulAut Y), IsPGroup p ↥P' →
      (∀ e ∈ P', e * α = α * e) → (∀ e ∈ P', ∀ r ∈ S.map π, e r = r) → IsCyclic ↥P')
    (hOut : ∀ x : MulAut Y, ⁅x, α⁆ ∈ innSub Y) : KAAll α := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  refine ka_all_of_components_fix hinj π hπ φ hφ hfix0 hnorm hperf (m := m)
    (fun i => Fq (e.symm i)) (fun i => hq _) (fun i => hle _) ?_ (fun i => hFn _) hfix hOut
  calc S ≤ ⨆ i, Fq i := hsup
    _ = ⨆ i : Fin m, Fq (e.symm i) := (Equiv.iSup_comp (g := Fq) e.symm).symm

end Comp

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

section Fix

include h in
theorem kaUS_two_ne_zero (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := h.prime.two_le
  exact hp2 (by omega)

include h in
theorem ka_u_block_fix [Finite K] (hp2 : p ≠ 2) (hn : 3 ≤ n) {J : Finset (Fin n)}
    (hJ : J.Nonempty) (hJc : J ≠ Finset.univ) (h5 : J.card = 2 ∨ J.card + 2 = n → 5 ≤ p ^ f) :
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ P' : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K))), IsPGroup r ↥P' →
        (∀ e ∈ P', ∀ x ∈ (uBlock p f K J ⊔ uBlock p f K Jᶜ).map
          (projH (StatedSU n (p ^ f) K)), e x = x) → IsCyclic ↥P' := by
  intro r hr hr2 P' hP' hfixP
  have hn1 : 1 ≤ n := by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  let T : ↥(kaUNormOne h) →* MulAut (StatedProj (StatedSU n (p ^ f) K)) :=
    (uConjAut h hn1).comp (kaUTor h J)
  have hle : P' ≤ T.range := by
    intro e he
    have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hr hr2 hP' he
    obtain ⟨E, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq e
    have hτm : τ ^ orderOf (uConjAut h hn1 E * uFieldAut h hn1 τ) = 1 :=
      fieldAut_pow_eq_one h hn hq (pow_orderOf_eq_one _)
    have hfixE : ∀ g ∈ uBlock p f K J ⊔ uBlock p f K Jᶜ,
        (uConjAut h hn1 E * uFieldAut h hn1 τ) (projH (StatedSU n (p ^ f) K) g) =
          projH (StatedSU n (p ^ f) K) g := fun g hg => hfixP _ he _ ⟨g, hg, rfl⟩
    have hblock_le : ∀ I : Finset (Fin n), (I = J ∨ I = Jᶜ) →
        uBlock p f K I ≤ uBlock p f K J ⊔ uBlock p f K Jᶜ := by
      intro I hI
      rcases hI with hI | hI
      · rw [hI]
        exact le_sup_left
      · rw [hI]
        exact le_sup_right
    obtain ⟨I0, hI0, h2I0⟩ := kaUS_exists_big hn J
    obtain ⟨v, η, i, hvI, hiso, hη, hvi⟩ := kaUS_exists_isotropic h h2I0
    have hτfix : ∀ c, h.bar c = c → τ c = c :=
      ka_u_sigma_fix h hn1 E τ hiso hη hvi fun g c _ hg =>
        hfixE g (hblock_le I0 hI0 (kaUS_mem_uBlock_of_transvection h hvI hg))
    have hτ1 : τ = 1 := eq_one_of_odd_of_fix h hodd hτm hτfix
    subst hτ1
    have hcomm : ∀ I : Finset (Fin n), (I = J ∨ I = Jᶜ) → 2 ≤ I.card → ∀ g ∈ uBlock p f K I,
        ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      intro I hI h2I g hg
      have hQ := kaUS_block_quasisimple h hp2 J h5 hI h2I
      have e1 := uSemilinear_eq_of_fix h hn1 (commutator_eq_self_of_isQuasisimple hQ)
        (fun g' hg' => hfixE g' (hblock_le I hI hg')) hg
      rw [map_one_ringEquiv] at e1
      have hDiD : (((E : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((((E : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
            rw [hDiD, Matrix.mul_one]
        _ = (((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (((E : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            simp only [Matrix.mul_assoc]
        _ = ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((E : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [e1]
    obtain ⟨a, d, ha, hd, hEeq⟩ := kaUS_eq_uDiagJ h hn hJ hJc E hcomm
    obtain ⟨u, hu⟩ := kaUS_conj_diag_eq h hn J a d ha hd
    refine ⟨u, ?_⟩
    show uConjAut h hn1 (kaUTor h J u) =
      uConjAut h hn1 E * uFieldAut h hn1 1
    rw [map_one, mul_one, hEeq, hu]
  have hcyc : IsCyclic ↥T.range :=
    isCyclic_of_surjective T.rangeRestrict T.rangeRestrict_surjective
  exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end Fix

section Main

theorem kaUSplit_thm : KAUSplit := by
  intro p f K _ _ h n hn hp2 J hJ hJc h5
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hn1 : 1 ≤ n := by omega
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have hnq : (n, p ^ f) ≠ (3, 2) := fun e => hq ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  have h2 : (2 : K) ≠ 0 := kaUS_two_ne_zero h hp2
  set S : Subgroup (StatedSU n (p ^ f) K) := uBlock p f K J ⊔ uBlock p f K Jᶜ with hS
  have hSfix : S ≤ MonoidHom.eqLocus (uLift h (uSign h J) 1)
      (MonoidHom.id (StatedSU n (p ^ f) K)) :=
    sup_le (fun g hg => kaUS_uLift_eq_of_mem h h2 J (Or.inl rfl) hg)
      (fun g hg => kaUS_uLift_eq_of_mem h h2 J (Or.inr rfl) hg)
  let ι : Type := {I : Finset (Fin n) // (I = J ∨ I = Jᶜ) ∧ 2 ≤ I.card}
  let Fq : ι → Subgroup (StatedSU n (p ^ f) K) := fun I => uBlock p f K I.1
  have hq' : ∀ i : ι, IsQuasisimple (Fq i) := fun i =>
    kaUS_block_quasisimple h hp2 J h5 i.2.1 i.2.2
  have hle : ∀ i : ι, Fq i ≤ S := by
    intro i
    rcases i.2.1 with hI | hI
    · show uBlock p f K i.1 ≤ S
      rw [hI]
      exact le_sup_left
    · show uBlock p f K i.1 ≤ S
      rw [hI]
      exact le_sup_right
  have hsup : S ≤ ⨆ i, Fq i := by
    refine sup_le ?_ ?_
    · by_cases hJ2 : 2 ≤ J.card
      · exact le_iSup_of_le (⟨J, Or.inl rfl, hJ2⟩ : ι) le_rfl
      · rw [kaUS_uBlock_eq_bot h (by omega)]
        exact bot_le
    · by_cases hJ2 : 2 ≤ Jᶜ.card
      · exact le_iSup_of_le (⟨Jᶜ, Or.inr rfl, hJ2⟩ : ι) le_rfl
      · rw [kaUS_uBlock_eq_bot h (by omega)]
        exact bot_le
  have hperf : ⁅S, S⁆ = S := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
    · refine hsup.trans (iSup_le fun i => ?_)
      calc Fq i = ⁅Fq i, Fq i⁆ := (commutator_eq_self_of_isQuasisimple (hq' i)).symm
        _ ≤ ⁅S, S⁆ := Subgroup.commutator_mono (hle i) (hle i)
  have hAA : ((uSign h J : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((uSign h J : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ((1 : K) ^ 2) • 1 := by
    rw [coe_uSign, signMat_mul_self, one_pow, one_smul]
  have hN1 : h.norm 1 = 1 ∨ h.norm 1 = -1 := Or.inl (by simp [UnitaryFieldData.norm])
  refine ka_all_of_components_fix_of_finite (ka_conj_inj_pu h.card_eq_sq hn hnq)
    (projH (StatedSU n (p ^ f) K)) projH_surjective (uLift h (uSign h J) 1) (fun g => ?_)
    (fun g hg => hSfix hg) (fun x hx g hg => kaUS_normalizes h h2 hn1 J hx hg) hperf Fq hq' hle hsup
    (fun i x hx g hg => kaUS_conj_mem_of_fix h h2 J i.2.1 (hSfix hx) hg)
    (fun r hr hr2 P' hP' _ hfixP => ka_u_block_fix h hp2 hn hJ hJc h5 r hr hr2 P' hP' hfixP)
    (fun x => ka_outCentral_pu h hn hq one_ne_zero hAA hN1 x)
  have := uLift_proj h hn1 (uSign h J) 1 g
  rwa [map_one, mul_one] at this

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
