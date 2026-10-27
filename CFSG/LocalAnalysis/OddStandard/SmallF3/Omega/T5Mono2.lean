module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono1
public import TauCeti.Data.Finset.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

@[expose] def monoG : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def monoD : Subgroup (Equiv.Perm (Fin 6)) :=
  alternatingGroup (Fin 6) ⊓ Subgroup.centralizer ({monoG} : Set (Equiv.Perm (Fin 6)))

private instance decidableMemMonoD : DecidablePred (· ∈ monoD) := fun σ =>
  decidable_of_iff'
    ((∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
        (if σ i < σ j then (1 : ℤˣ) else -1)) = 1 ∧ monoG * σ = σ * monoG)
    (by
      show (σ ∈ alternatingGroup (Fin 6) ⊓
        Subgroup.centralizer ({monoG} : Set (Equiv.Perm (Fin 6)))) ↔
        ((∏ j : Fin 6, ∏ i ∈ Finset.Iio j,
          (if σ i < σ j then (1 : ℤˣ) else -1)) = 1 ∧ monoG * σ = σ * monoG)
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_eq_prod_prod_Iio]
      simp only [Set.mem_singleton_iff, forall_eq])

private theorem monoG_eq_self_iff (i : Fin 6) : monoG i = i ↔ i = 4 ∨ i = 5 := by
  revert i
  decide

theorem monoD_card : Nat.card monoD = 8 := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype (fun σ : Equiv.Perm (Fin 6) => σ ∈ monoD)]
  decide

theorem monoD_cycle_mem :
    (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5 : Equiv.Perm (Fin 6)) ∈
      monoD := by
  decide

theorem monoD_orbits {J : Finset (Fin 6)} (h : ∀ σ ∈ monoD, J.map σ.toEmbedding = J) :
    J = ∅ ∨ J = {0, 1, 2, 3} ∨ J = {4, 5} ∨ J = Finset.univ := by
  have hr := h (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 *
    Equiv.swap 4 5 : Equiv.Perm (Fin 6)) monoD_cycle_mem
  have hcheck : ∀ J : Finset (Fin 6),
      J.map (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 *
        Equiv.swap 4 5 : Equiv.Perm (Fin 6)).toEmbedding = J →
        J = ∅ ∨ J = {0, 1, 2, 3} ∨ J = {4, 5} ∨ J = Finset.univ := by
    decide
  exact hcheck J hr

theorem monoD_map_orbit {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ monoD) :
    ({0, 1, 2, 3} : Finset (Fin 6)).map σ.toEmbedding = {0, 1, 2, 3} ∧
      ({4, 5} : Finset (Fin 6)).map σ.toEmbedding = {4, 5} := by
  have hcomm : monoG * σ = σ * monoG := by
    have h := hσ
    rw [monoD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at h
    exact h.2 monoG (Set.mem_singleton monoG)
  have happ : ∀ i : Fin 6, monoG (σ i) = σ (monoG i) := by
    intro i
    have h := congrFun (congrArg (fun e : Equiv.Perm (Fin 6) => (e : Fin 6 → Fin 6)) hcomm) i
    simpa only [Equiv.Perm.mul_apply] using h
  have hfix : ∀ i : Fin 6, monoG (σ i) = σ i ↔ i = 4 ∨ i = 5 := by
    intro i
    rw [happ i, Equiv.apply_eq_iff_eq σ, monoG_eq_self_iff]
  have hpre : ∀ i : Fin 6, σ.symm i = 4 ∨ σ.symm i = 5 ↔ i = 4 ∨ i = 5 := by
    intro i
    have h1 : (σ.symm i = 4 ∨ σ.symm i = 5) ↔ monoG i = i := by
      simpa using (hfix (σ.symm i)).symm
    exact h1.trans (monoG_eq_self_iff i)
  have hcompl : ∀ i : Fin 6,
      i ∈ ({0, 1, 2, 3} : Finset (Fin 6)) ↔ ¬ (i = 4 ∨ i = 5) := by
    decide
  constructor
  · ext i
    rw [Finset.mem_map_equiv, hcompl, hcompl]
    exact not_congr (hpre i)
  · ext i
    rw [Finset.mem_map_equiv]
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpre i

private theorem NFrame.permOrth_mul_signChange_basis {c : ZMod 3}
    (fr : NFrame Q (Fin 6) c) (σ : Equiv.Perm (Fin 6)) (J : Finset (Fin 6)) (i : Fin 6) :
    (((fr.permOrth σ * fr.signChange J : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i)) =
      (if i ∈ J then (-1 : ZMod 3) else 1) • fr.b (σ i) := by
  rw [Submonoid.coe_mul, LinearEquiv.mul_apply, fr.signChange_basis J i]
  by_cases hi : i ∈ J
  · rw [if_pos hi, map_neg, fr.permOrth_basis]
    simp [hi]
  · rw [if_neg hi, fr.permOrth_basis]
    simp [hi]

private theorem NFrame.eq_of_smul_basis_eq_smul_basis {c : ZMod 3} (fr : NFrame Q (Fin 6) c)
    {i j : Fin 6} {a d : ZMod 3} (ha : a ≠ 0)
    (h : a • fr.b i = d • fr.b j) : i = j := by
  by_contra hij
  have hc := congrArg (fun x : V => fr.b.repr x i) h
  simp [Module.Basis.repr_self, Finsupp.smul_apply, hij] at hc
  exact ha hc

private theorem NFrame.permOrth_symm_inv {c : ZMod 3} (fr : NFrame Q (Fin 6) c)
    (σ : Equiv.Perm (Fin 6)) :
    (fr.permOrth σ)⁻¹ = fr.permOrth σ.symm := by
  have hmul : σ * σ.symm = 1 := by
    ext i
    simp [Equiv.Perm.mul_apply]
  have h : fr.permOrth (σ * σ.symm) = fr.permOrth σ * fr.permOrth σ.symm :=
    fr.permOrth_mul σ σ.symm
  rw [hmul, fr.permOrth_one] at h
  exact inv_eq_of_mul_eq_one_right h.symm

private theorem NFrame.signChange_mul_permOrth {c : ZMod 3} (fr : NFrame Q (Fin 6) c)
    (σ : Equiv.Perm (Fin 6)) (J : Finset (Fin 6)) :
    fr.signChange J * fr.permOrth σ =
      fr.permOrth σ * fr.signChange (J.map σ.symm.toEmbedding) := by
  have hpinv : fr.permOrth σ.symm = (fr.permOrth σ)⁻¹ :=
    (fr.permOrth_symm_inv σ).symm
  have h := fr.permOrth_mul_signChange σ.symm J
  rw [hpinv] at h
  calc
    fr.signChange J * fr.permOrth σ
        = (fr.permOrth σ * (fr.permOrth σ)⁻¹) *
            (fr.signChange J * fr.permOrth σ) := by group
    _ = fr.permOrth σ * ((fr.permOrth σ)⁻¹ * fr.signChange J) * fr.permOrth σ := by
          group
    _ = fr.permOrth σ *
          (fr.signChange (J.map σ.symm.toEmbedding) * (fr.permOrth σ)⁻¹) *
            fr.permOrth σ := by rw [h]
    _ = fr.permOrth σ * fr.signChange (J.map σ.symm.toEmbedding) := by group

theorem t5_exists_monoP (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ∃ P : Subgroup (OGroup Q), P ≤ omegaGroup hQ ∧ Nat.card P = 2 ^ 8 ∧
      ∀ g, g ∈ P ↔ ∃ σ ∈ monoD, ∃ J : Finset (Fin 6), Even J.card ∧
        g = fr.permOrth σ * fr.signChange J := by
  let P : Subgroup (OGroup Q) :=
    { carrier := {g | ∃ σ ∈ monoD, ∃ J : Finset (Fin 6), Even J.card ∧
        g = fr.permOrth σ * fr.signChange J}
      one_mem' := by
        refine ⟨1, Subgroup.one_mem monoD, ∅, by simp, ?_⟩
        rw [fr.permOrth_one, fr.signChange_empty, one_mul]
      mul_mem' := by
        rintro a b ⟨σ, hσ, J, hJ, rfl⟩ ⟨τ, hτ, K, hK, rfl⟩
        refine ⟨σ * τ, Subgroup.mul_mem _ hσ hτ,
          symmDiff (J.map τ.symm.toEmbedding) K, ?_, ?_⟩
        · rw [Finset.even_card_symmDiff_iff, Finset.card_map]
          exact iff_of_true hJ hK
        · calc
            (fr.permOrth σ * fr.signChange J) * (fr.permOrth τ * fr.signChange K)
                = fr.permOrth σ * (fr.signChange J * fr.permOrth τ) *
                    fr.signChange K := by group
            _ = fr.permOrth σ *
                  (fr.permOrth τ * fr.signChange (J.map τ.symm.toEmbedding)) *
                    fr.signChange K := by rw [fr.signChange_mul_permOrth]
            _ = (fr.permOrth σ * fr.permOrth τ) *
                  (fr.signChange (J.map τ.symm.toEmbedding) * fr.signChange K) := by
                  group
            _ = fr.permOrth (σ * τ) *
                  fr.signChange (symmDiff (J.map τ.symm.toEmbedding) K) := by
                  rw [fr.permOrth_mul, fr.signChange_mul]
      inv_mem' := by
        rintro a ⟨σ, hσ, J, hJ, rfl⟩
        refine ⟨σ.symm, Subgroup.inv_mem _ hσ, J.map σ.toEmbedding, ?_, ?_⟩
        · rw [Finset.card_map]; exact hJ
        · rw [mul_inv_rev]
          have ht : (fr.signChange J)⁻¹ = fr.signChange J :=
            inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)
          have hp : (fr.permOrth σ)⁻¹ = fr.permOrth σ.symm :=
            fr.permOrth_symm_inv σ
          rw [ht, hp]
          exact fr.signChange_mul_permOrth σ.symm J }
  have hmem : ∀ g : OGroup Q, g ∈ P ↔ ∃ σ ∈ monoD, ∃ J : Finset (Fin 6),
      Even J.card ∧ g = fr.permOrth σ * fr.signChange J := fun _ => Iff.rfl
  refine ⟨P, ?_, ?_, hmem⟩
  · intro g hg
    obtain ⟨σ, hσ, J, hJ, rfl⟩ := (hmem g).mp hg
    exact Subgroup.mul_mem _ (fr.permOrth_mem_omegaGroup hQ (Subgroup.mem_inf.mp hσ).1)
      (fr.signChange_mem_omegaGroup hQ J hJ)
  · let E := {J : Finset (Fin 6) // Even J.card}
    let F : monoD × E → P := fun x =>
      ⟨fr.permOrth x.1.1 * fr.signChange x.2.1,
        (hmem _).mpr ⟨x.1.1, x.1.2, x.2.1, x.2.2, rfl⟩⟩
    have hinj : Function.Injective F := by
      rintro ⟨⟨σ, hσ⟩, ⟨J, hJ⟩⟩ ⟨⟨τ, hτ⟩, ⟨K, hK⟩⟩ h
      have hg : fr.permOrth σ * fr.signChange J =
          fr.permOrth τ * fr.signChange K := congrArg Subtype.val h
      have hστ : σ = τ := by
        apply Equiv.ext
        intro i
        exact fr.eq_of_smul_basis_eq_smul_basis
          (a := if i ∈ J then (-1 : ZMod 3) else 1)
          (d := if i ∈ K then (-1 : ZMod 3) else 1)
          (by split_ifs <;> decide)
          (by
            have hb := congrArg
              (fun g : OGroup Q => ((g : V ≃ₗ[ZMod 3] V) (fr.b i))) hg
            rwa [fr.permOrth_mul_signChange_basis σ J i,
              fr.permOrth_mul_signChange_basis τ K i] at hb)
      apply Prod.ext
      · exact Subtype.ext hστ
      · exact Subtype.ext (fr.signChange_injective (mul_left_cancel (by
          simpa only [hστ] using hg)))
    have hsurj : Function.Surjective F := by
      rintro ⟨g, hg⟩
      obtain ⟨σ, hσ, J, hJ, rfl⟩ := (hmem g).mp hg
      exact ⟨(⟨σ, hσ⟩, ⟨J, hJ⟩), Subtype.ext rfl⟩
    have hcard : Nat.card P = Nat.card (monoD × E) :=
      (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm
    have hE : Nat.card E = 32 := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_subtype (fun J : Finset (Fin 6) => Even J.card)]
      decide
    calc
      Nat.card P = Nat.card (monoD × E) := hcard
      _ = Nat.card monoD * Nat.card E := Nat.card_prod _ _
      _ = 8 * 32 := by rw [monoD_card, hE]
      _ = 2 ^ 8 := by norm_num

end CFSG.OddStandard.SmallF3.Omega
