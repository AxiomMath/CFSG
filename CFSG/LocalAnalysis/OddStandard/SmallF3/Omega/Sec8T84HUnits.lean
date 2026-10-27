module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

private lemma ffK0_mul_mem {σ τ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffK0) (hτ : τ ∈ ffK0) :
    σ * τ ∈ ffK0 := by
  simp only [ffK0, Finset.mem_insert, Finset.mem_singleton] at hσ hτ
  rcases hσ with rfl | rfl | rfl | rfl <;>
    rcases hτ with rfl | rfl | rfl | rfl <;> decide

private lemma ffK0_mul_self {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffK0) : σ * σ = 1 := by
  simp only [ffK0, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> decide

private lemma ffK0_comm {σ τ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffK0) (hτ : τ ∈ ffK0) :
    σ * τ = τ * σ := by
  simp only [ffK0, Finset.mem_insert, Finset.mem_singleton] at hσ hτ
  rcases hσ with rfl | rfl | rfl | rfl <;>
    rcases hτ with rfl | rfl | rfl | rfl <;> decide

private lemma ffK0_map_ffF0 {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffK0) {J : Finset (Fin 6)}
    (hJ : J ∈ ffF0) : J.map σ.toEmbedding = J := by
  simp only [ffK0, Finset.mem_insert, Finset.mem_singleton] at hσ
  simp only [ffF0, Finset.mem_insert, Finset.mem_singleton] at hJ
  rcases hσ with rfl | rfl | rfl | rfl <;>
    rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ffF0_symmDiff_mem {J K : Finset (Fin 6)} (hJ : J ∈ ffF0) (hK : K ∈ ffF0) :
    symmDiff J K ∈ ffF0 := by
  simp only [ffF0, Finset.mem_insert, Finset.mem_singleton] at hJ hK
  rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ffF0_even {J : Finset (Fin 6)} (hJ : J ∈ ffF0) : Even J.card := by
  simp only [ffF0, Finset.mem_insert, Finset.mem_singleton] at hJ
  rcases hJ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ffK0_mem_monoD {σ : Equiv.Perm (Fin 6)} (hσ : σ ∈ ffK0) : σ ∈ monoD := by
  simp only [ffK0, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem monoD
  · exact ffInvolutions_mem_monoD.1
  · exact ffInvolutions_mem_monoD.2.1
  · exact ffInvolutions_mem_monoD.2.2.1

private lemma ffU2_mul_self {fr : NFrame Q (Fin 6) c} {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ffK0) {J : Finset (Fin 6)} (hJ : J ∈ ffF0) :
    (fr.permOrth σ * fr.signChange J) * (fr.permOrth σ * fr.signChange J) = 1 := by
  have h2 : σ * σ = 1 := ffK0_mul_self hσ
  have hinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right h2
  rw [ffMono_mul, h2, hinv, ffK0_map_ffF0 hσ hJ, symmDiff_self, Finset.bot_eq_empty,
    fr.permOrth_one, fr.signChange_empty, mul_one]

private lemma ffMono_inv_mul (fr : NFrame Q (Fin 6) c) (σ : Equiv.Perm (Fin 6))
    (J : Finset (Fin 6)) :
    (fr.permOrth σ * fr.signChange J)⁻¹ =
      fr.permOrth σ⁻¹ * fr.signChange (J.map σ.toEmbedding) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [ffMono_mul]
  have h2 : symmDiff (J.map (σ⁻¹)⁻¹.toEmbedding) (J.map σ.toEmbedding) = ∅ := by
    rw [inv_inv, symmDiff_self, Finset.bot_eq_empty]
  rw [mul_inv_cancel, fr.permOrth_one, h2, fr.signChange_empty, mul_one]

@[expose] noncomputable def hU2 (fr : NFrame Q (Fin 6) c) : Subgroup (OGroup Q) where
  carrier := {g | ∃ σ ∈ ffK0, ∃ J ∈ ffF0, g = fr.permOrth σ * fr.signChange J}
  one_mem' := by
    refine ⟨1, ?_, ∅, ?_, ?_⟩
    · decide
    · decide
    · rw [fr.permOrth_one, fr.signChange_empty, one_mul]
  mul_mem' := by
    rintro a b ⟨σ, hσ, J, hJ, rfl⟩ ⟨τ, hτ, K, hK, rfl⟩
    refine ⟨σ * τ, ffK0_mul_mem hσ hτ, symmDiff (J.map τ⁻¹.toEmbedding) K, ?_, ?_⟩
    · have hinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (ffK0_mul_self hτ)
      rw [hinv, ffK0_map_ffF0 hτ hJ]
      exact ffF0_symmDiff_mem hJ hK
    · rw [ffMono_mul]
  inv_mem' := by
    rintro a ⟨σ, hσ, J, hJ, rfl⟩
    exact ⟨σ, hσ, J, hJ, inv_eq_of_mul_eq_one_right (ffU2_mul_self hσ hJ)⟩

@[expose] noncomputable def hD1 (fr : NFrame Q (Fin 6) c) : Subgroup (OGroup Q) where
  carrier := {g | ∃ σ ∈ monoD, g = fr.permOrth σ}
  one_mem' := ⟨1, Subgroup.one_mem monoD, by rw [fr.permOrth_one]⟩
  mul_mem' := by
    rintro a b ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, Subgroup.mul_mem _ hσ hτ, by rw [fr.permOrth_mul]⟩
  inv_mem' := by
    rintro a ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, Subgroup.inv_mem _ hσ, permOrth_inv fr σ⟩

@[expose] def hF : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def hE4 : Finset (Finset (Fin 6)) := {∅, {3, 5}, {2, 5}, {2, 3}}

private lemma hF_mem_monoD : hF ∈ monoD := ffInvolutions_mem_monoD.2.2.2.1

private lemma hFH_mul_mem {σ τ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6))))
    (hτ : τ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6)))) :
    σ * τ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6))) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ hτ
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> decide

private lemma hFH_mul_self {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6)))) : σ * σ = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl <;> decide

private lemma hFH_map_hE4 {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6)))) {J : Finset (Fin 6)} (hJ : J ∈ hE4) :
    J.map σ.toEmbedding ∈ hE4 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  simp only [hE4, Finset.mem_insert, Finset.mem_singleton] at hJ
  rcases hσ with rfl | rfl <;> rcases hJ with rfl | rfl | rfl | rfl <;> decide

private lemma hFH_map_inv_hE4 {σ : Equiv.Perm (Fin 6)}
    (hσ : σ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6)))) {J : Finset (Fin 6)} (hJ : J ∈ hE4) :
    J.map σ⁻¹.toEmbedding ∈ hE4 := by
  rw [inv_eq_of_mul_eq_one_right (hFH_mul_self hσ)]
  exact hFH_map_hE4 hσ hJ

private lemma hE4_even {J : Finset (Fin 6)} (hJ : J ∈ hE4) : Even J.card := by
  simp only [hE4, Finset.mem_insert, Finset.mem_singleton] at hJ
  rcases hJ with rfl | rfl | rfl | rfl <;> decide

private lemma hE4_symmDiff_mem {J K : Finset (Fin 6)} (hJ : J ∈ hE4) (hK : K ∈ hE4) :
    symmDiff J K ∈ hE4 := by
  simp only [hE4, Finset.mem_insert, Finset.mem_singleton] at hJ hK
  rcases hJ with rfl | rfl | rfl | rfl <;>
    rcases hK with rfl | rfl | rfl | rfl <;> decide

@[expose] noncomputable def hD2 (fr : NFrame Q (Fin 6) c) : Subgroup (OGroup Q) where
  carrier := {g | ∃ σ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6))), ∃ J ∈ hE4,
    g = fr.permOrth σ * fr.signChange J}
  one_mem' := by
    refine ⟨1, ?_, ∅, ?_, ?_⟩
    · decide
    · decide
    · rw [fr.permOrth_one, fr.signChange_empty, one_mul]
  mul_mem' := by
    rintro a b ⟨σ, hσ, J, hJ, rfl⟩ ⟨τ, hτ, K, hK, rfl⟩
    refine ⟨σ * τ, hFH_mul_mem hσ hτ, symmDiff (J.map τ⁻¹.toEmbedding) K, ?_, ?_⟩
    · exact hE4_symmDiff_mem (hFH_map_inv_hE4 hτ hJ) hK
    · rw [ffMono_mul]
  inv_mem' := by
    rintro a ⟨σ, hσ, J, hJ, rfl⟩
    refine ⟨σ⁻¹, ?_, J.map σ.toEmbedding, ?_, ffMono_inv_mul fr σ J⟩
    · rw [inv_eq_of_mul_eq_one_right (hFH_mul_self hσ)]
      exact hσ
    · exact hFH_map_hE4 hσ hJ

theorem mem_hU2_iff (fr : NFrame Q (Fin 6) c) {g : OGroup Q} :
    g ∈ hU2 fr ↔ ∃ σ ∈ ffK0, ∃ J ∈ ffF0, g = fr.permOrth σ * fr.signChange J :=
  Iff.rfl

theorem mem_hD1_iff (fr : NFrame Q (Fin 6) c) {g : OGroup Q} :
    g ∈ hD1 fr ↔ ∃ σ ∈ monoD, g = fr.permOrth σ :=
  Iff.rfl

theorem mem_hD2_iff (fr : NFrame Q (Fin 6) c) {g : OGroup Q} :
    g ∈ hD2 fr ↔ ∃ σ ∈ ({1, hF} : Finset (Equiv.Perm (Fin 6))), ∃ J ∈ hE4,
      g = fr.permOrth σ * fr.signChange J :=
  Iff.rfl

theorem piOrth_mem_hU2 (fr : NFrame Q (Fin 6) c) : piOrth Q ∈ hU2 fr := by
  refine ⟨1, ?_, Finset.univ, ?_, ?_⟩
  · decide
  · decide
  · rw [fr.permOrth_one, one_mul, fr.piOrth_eq_signChange_univ]

theorem hU2_le_ffP0 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    hU2 fr ≤ ffP0 hQ fr := by
  rintro g ⟨σ, hσ, J, hJ, rfl⟩
  exact (mem_ffP0_iff hQ fr).mpr ⟨σ, ffK0_mem_monoD hσ, J, ffF0_even hJ, rfl⟩

theorem hD1_le_ffP0 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    hD1 fr ≤ ffP0 hQ fr := by
  rintro g ⟨σ, hσ, rfl⟩
  exact (mem_ffP0_iff hQ fr).mpr
    ⟨σ, hσ, ∅, by simp, by rw [fr.signChange_empty, mul_one]⟩

theorem hD2_le_ffP0 (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c) :
    hD2 fr ≤ ffP0 hQ fr := by
  rintro g ⟨σ, hσ, J, hJ, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl
  · exact (mem_ffP0_iff hQ fr).mpr
      ⟨1, Subgroup.one_mem monoD, J, hE4_even hJ, rfl⟩
  · exact (mem_ffP0_iff hQ fr).mpr
      ⟨hF, hF_mem_monoD, J, hE4_even hJ, rfl⟩

theorem hU2_card (fr : NFrame Q (Fin 6) c) : Nat.card (hU2 fr) = 32 := by
  let F : ↥(ffK0 ×ˢ ffF0) → hU2 fr := fun x =>
    ⟨fr.permOrth x.1.1 * fr.signChange x.1.2,
      ⟨x.1.1, (Finset.mem_product.mp x.2).1, x.1.2, (Finset.mem_product.mp x.2).2, rfl⟩⟩
  have hbij : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨σ, J⟩, hx⟩ ⟨⟨τ, K⟩, hy⟩ h
      have hg : fr.permOrth σ * fr.signChange J = fr.permOrth τ * fr.signChange K :=
        congrArg Subtype.val h
      obtain ⟨rfl, rfl⟩ := ffMono_unique fr hg
      exact Subtype.ext rfl
    · rintro ⟨g, hg⟩
      obtain ⟨σ, hσ, J, hJ, rfl⟩ := hg
      exact ⟨⟨(σ, J), Finset.mem_product.mpr ⟨hσ, hJ⟩⟩, Subtype.ext rfl⟩
  have hcard : Nat.card ↥(ffK0 ×ˢ ffF0) = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_product]
    have h4 : ffK0.card = 4 := by decide
    have h8 : ffF0.card = 8 := by decide
    rw [h4, h8]
  rw [← Nat.card_congr (Equiv.ofBijective F hbij)]
  exact hcard

theorem hU2_comm (fr : NFrame Q (Fin 6) c) {a b : OGroup Q} (ha : a ∈ hU2 fr) (hb : b ∈ hU2 fr) :
    a * b = b * a := by
  obtain ⟨σ, hσ, J, hJ, rfl⟩ := ha
  obtain ⟨τ, hτ, K, hK, rfl⟩ := hb
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right (ffK0_mul_self hσ)
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (ffK0_mul_self hτ)
  have hA : symmDiff (J.map τ⁻¹.toEmbedding) K = symmDiff (K.map σ⁻¹.toEmbedding) J := by
    rw [hτinv, hσinv, ffK0_map_ffF0 hτ hJ, ffK0_map_ffF0 hσ hK]
    exact symmDiff_comm J K
  rw [ffMono_mul, ffMono_mul, ffK0_comm hσ hτ, hA]

theorem hU2_mul_self (fr : NFrame Q (Fin 6) c) {a : OGroup Q} (ha : a ∈ hU2 fr) :
    a * a = 1 := by
  obtain ⟨σ, hσ, J, hJ, rfl⟩ := ha
  exact ffU2_mul_self hσ hJ

end CFSG.OddStandard.SmallF3.Omega
