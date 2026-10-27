module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Mono3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

@[expose] noncomputable def ffB0 (fr : NFrame Q (Fin 6) c) : Subgroup (OGroup Q) where
  carrier := {g | ∃ J : Finset (Fin 6), Even J.card ∧ g = fr.signChange J}
  one_mem' := ⟨∅, by simp, fr.signChange_empty.symm⟩
  mul_mem' := by
    rintro a b ⟨J, hJ, rfl⟩ ⟨K, hK, rfl⟩
    exact ⟨symmDiff J K, (Finset.even_card_symmDiff_iff J K).mpr (iff_of_true hJ hK),
      fr.signChange_mul J K⟩
  inv_mem' := by
    rintro a ⟨J, hJ, rfl⟩
    exact ⟨J, hJ, inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)⟩

theorem mem_ffB0_iff (fr : NFrame Q (Fin 6) c) {g : OGroup Q} :
    g ∈ ffB0 fr ↔ ∃ J : Finset (Fin 6), Even J.card ∧ g = fr.signChange J :=
  Iff.rfl

theorem signChange_mem_ffB0 (fr : NFrame Q (Fin 6) c) {J : Finset (Fin 6)} (hJ : Even J.card) :
    fr.signChange J ∈ ffB0 fr :=
  ⟨J, hJ, rfl⟩

theorem ffB0_card (fr : NFrame Q (Fin 6) c) : Nat.card (ffB0 fr) = 32 := by
  let E := {J : Finset (Fin 6) // Even J.card}
  let F : E → ffB0 fr := fun J => ⟨fr.signChange J.1, J.1, J.2, rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun J K h => Subtype.ext (fr.signChange_injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨g, J, hJ, rfl⟩
    exact ⟨⟨J, hJ⟩, rfl⟩
  have hE : Nat.card E = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype (fun J : Finset (Fin 6) => Even J.card)]
    decide
  rw [← Nat.card_congr (Equiv.ofBijective F hF), hE]

theorem ffB0_comm (fr : NFrame Q (Fin 6) c) {a b : OGroup Q} (ha : a ∈ ffB0 fr)
    (hb : b ∈ ffB0 fr) : a * b = b * a := by
  obtain ⟨J, -, rfl⟩ := ha
  obtain ⟨K, -, rfl⟩ := hb
  exact fr.signChange_comm J K

theorem ffB0_mul_self (fr : NFrame Q (Fin 6) c) {a : OGroup Q} (ha : a ∈ ffB0 fr) :
    a * a = 1 := by
  obtain ⟨J, -, rfl⟩ := ha
  exact fr.signChange_mul_self J

theorem piOrth_mem_ffB0 (fr : NFrame Q (Fin 6) c) : piOrth Q ∈ ffB0 fr := by
  refine ⟨Finset.univ, ?_, fr.piOrth_eq_signChange_univ⟩
  rw [Finset.card_univ, Fintype.card_fin]
  decide

@[expose] noncomputable def ffP0 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    Subgroup (OGroup Q) :=
  Classical.choose (t5_exists_monoP hQ fr)

theorem ffP0_le_omega (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ffP0 hQ fr ≤ omegaGroup hQ :=
  (Classical.choose_spec (t5_exists_monoP hQ fr)).1

theorem ffP0_card (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    Nat.card (ffP0 hQ fr) = 2 ^ 8 :=
  (Classical.choose_spec (t5_exists_monoP hQ fr)).2.1

theorem mem_ffP0_iff (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) {g : OGroup Q} :
    g ∈ ffP0 hQ fr ↔ ∃ σ ∈ monoD, ∃ J : Finset (Fin 6), Even J.card ∧
      g = fr.permOrth σ * fr.signChange J :=
  (Classical.choose_spec (t5_exists_monoP hQ fr)).2.2 g

theorem ffB0_le_ffP0 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    ffB0 fr ≤ ffP0 hQ fr := by
  rintro g ⟨J, hJ, rfl⟩
  refine (mem_ffP0_iff hQ fr).mpr ⟨1, Subgroup.one_mem _, J, hJ, ?_⟩
  rw [fr.permOrth_one, one_mul]

theorem ffMono_basis (fr : NFrame Q (Fin 6) c) (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6))
    (i : Fin 6) :
    (((fr.permOrth σ * fr.signChange K : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b i)) =
      (if i ∈ K then (-1 : ZMod 3) else 1) • fr.b (σ i) := by
  rw [Submonoid.coe_mul, LinearEquiv.mul_apply, fr.signChange_basis K i]
  by_cases hi : i ∈ K
  · rw [if_pos hi, map_neg, fr.permOrth_basis]
    simp [hi]
  · rw [if_neg hi, fr.permOrth_basis]
    simp [hi]

theorem ffMono_index_eq (fr : NFrame Q (Fin 6) c) {i j : Fin 6} {a d : ZMod 3} (ha : a ≠ 0)
    (h : a • fr.b i = d • fr.b j) : i = j := by
  by_contra hij
  have hc := congrArg (fun x : V => fr.b.repr x i) h
  simp [Module.Basis.repr_self, Finsupp.smul_apply, hij] at hc
  exact ha hc

theorem ffMono_unique (fr : NFrame Q (Fin 6) c) {σ τ : Equiv.Perm (Fin 6)}
    {J K : Finset (Fin 6)}
    (h : fr.permOrth σ * fr.signChange J = fr.permOrth τ * fr.signChange K) :
    σ = τ ∧ J = K := by
  have hστ : σ = τ := by
    apply Equiv.ext
    intro i
    refine ffMono_index_eq fr (a := if i ∈ J then (-1 : ZMod 3) else 1)
      (d := if i ∈ K then (-1 : ZMod 3) else 1) (by split_ifs <;> decide) ?_
    have hb := congrArg (fun g : OGroup Q => ((g : V ≃ₗ[ZMod 3] V) (fr.b i))) h
    rwa [ffMono_basis, ffMono_basis] at hb
  subst hστ
  exact ⟨rfl, fr.signChange_injective (mul_left_cancel h)⟩

theorem permOrth_inv (fr : NFrame Q (Fin 6) c) (σ : Equiv.Perm (Fin 6)) :
    (fr.permOrth σ)⁻¹ = fr.permOrth σ⁻¹ := by
  have h : fr.permOrth σ * fr.permOrth σ⁻¹ = 1 := by
    rw [← fr.permOrth_mul, mul_inv_cancel, fr.permOrth_one]
  exact inv_eq_of_mul_eq_one_right h

theorem ffMono_mul (fr : NFrame Q (Fin 6) c) (σ τ : Equiv.Perm (Fin 6)) (J K : Finset (Fin 6)) :
    (fr.permOrth σ * fr.signChange J) * (fr.permOrth τ * fr.signChange K) =
      fr.permOrth (σ * τ) * fr.signChange (symmDiff (J.map τ⁻¹.toEmbedding) K) := by
  have h1 : fr.signChange J * fr.permOrth τ =
      fr.permOrth τ * fr.signChange (J.map τ⁻¹.toEmbedding) := by
    have h := fr.permOrth_mul_signChange τ⁻¹ J
    rw [← permOrth_inv] at h
    calc fr.signChange J * fr.permOrth τ
        = fr.permOrth τ * ((fr.permOrth τ)⁻¹ * fr.signChange J) * fr.permOrth τ := by group
      _ = fr.permOrth τ * (fr.signChange (J.map τ⁻¹.toEmbedding) * (fr.permOrth τ)⁻¹) *
            fr.permOrth τ := by rw [h]
      _ = fr.permOrth τ * fr.signChange (J.map τ⁻¹.toEmbedding) := by group
  calc (fr.permOrth σ * fr.signChange J) * (fr.permOrth τ * fr.signChange K)
      = fr.permOrth σ * (fr.signChange J * fr.permOrth τ) * fr.signChange K := by group
    _ = fr.permOrth σ * (fr.permOrth τ * fr.signChange (J.map τ⁻¹.toEmbedding)) *
          fr.signChange K := by rw [h1]
    _ = (fr.permOrth σ * fr.permOrth τ) *
          (fr.signChange (J.map τ⁻¹.toEmbedding) * fr.signChange K) := by group
    _ = fr.permOrth (σ * τ) * fr.signChange (symmDiff (J.map τ⁻¹.toEmbedding) K) := by
          rw [fr.permOrth_mul, fr.signChange_mul]

theorem ffMono_conj_signChange (fr : NFrame Q (Fin 6) c) (σ : Equiv.Perm (Fin 6))
    (J K : Finset (Fin 6)) :
    (fr.permOrth σ * fr.signChange J) * fr.signChange K *
        (fr.permOrth σ * fr.signChange J)⁻¹ = fr.signChange (K.map σ.toEmbedding) := by
  have hJ : (fr.signChange J)⁻¹ = fr.signChange J :=
    inv_eq_of_mul_eq_one_right (fr.signChange_mul_self J)
  calc (fr.permOrth σ * fr.signChange J) * fr.signChange K *
        (fr.permOrth σ * fr.signChange J)⁻¹
      = fr.permOrth σ * (fr.signChange J * fr.signChange K * (fr.signChange J)⁻¹) *
          (fr.permOrth σ)⁻¹ := by group
    _ = fr.permOrth σ * fr.signChange K * (fr.permOrth σ)⁻¹ := by
          rw [fr.signChange_comm J K, mul_assoc (fr.signChange K), hJ,
            fr.signChange_mul_self J, mul_one]
    _ = fr.signChange (K.map σ.toEmbedding) := by
          rw [fr.permOrth_mul_signChange σ K, mul_assoc, mul_inv_cancel, mul_one]

end CFSG.OddStandard.SmallF3.Omega
