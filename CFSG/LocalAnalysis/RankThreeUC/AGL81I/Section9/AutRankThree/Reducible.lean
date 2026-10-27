module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def natRep (Y : Subgroup (GL ι K)) : Representation K Y (ι → K) :=
  (Matrix.toLinAlgEquiv' : Matrix ι ι K ≃ₐ[K] _).toMonoidHom.comp
    ((Units.coeHom (Matrix ι ι K)).comp Y.subtype)

noncomputable def toGLFin {G W : Type} [Group G] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K G W) :
    G →* GL (Fin (Module.finrank K W)) K :=
  (Units.map (LinearMap.toMatrixAlgEquiv (Module.finBasis K W)).toMonoidHom).comp ρ.toHomUnits

private lemma eq_one_of_mem_ker_toGLFin {G W : Type} [Group G] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K G W) {g : G} (hg : g ∈ (toGLFin ρ).ker) :
    ρ g = 1 := by
  apply (LinearMap.toMatrixAlgEquiv (Module.finBasis K W)).injective
  rw [map_one]
  simpa [toGLFin] using congrArg Units.val hg

private lemma pow_ringChar_eq_one (U : Submodule K (ι → K)) (g : GL ι K)
    (h1 : ∀ u ∈ U, (g : Matrix ι ι K) *ᵥ u = u)
    (h2 : ∀ v, (g : Matrix ι ι K) *ᵥ v - v ∈ U) [Finite K] : g ^ ringChar K = 1 := by
  set N : Matrix ι ι K := (g : Matrix ι ι K) - 1
  have hN : ∀ v, N *ᵥ v = (g : Matrix ι ι K) *ᵥ v - v := fun v => by
    simp [N, Matrix.sub_mulVec]
  have hNN : N * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have := h1 _ (h2 v)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, map_zero, LinearMap.zero_apply,
      hN] at this ⊢
    rw [this, sub_self]
  have hp := CharP.char_is_prime K (ringChar K)
  have hNp : N ^ ringChar K = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp.two_le
    rw [hk, pow_add, sq, hNN, zero_mul]
  have := Fact.mk hp
  cases isEmpty_or_nonempty ι
  · exact Subsingleton.elim _ _
  ext1
  rw [Units.val_pow_eq_pow_val, Units.val_one, show (g : Matrix ι ι K) = 1 + N by simp [N],
    add_pow_char_of_commute (ringChar K) (Commute.one_left N), one_pow, hNp, add_zero]

private lemma isSolvable_range_toGLFin [Finite K]
    (hlow : ∀ d < Fintype.card ι, ∀ Y : Subgroup (GL (Fin d) K),
      Nat.Coprime 3 (Nat.card Y) → Group.IsSolvable Y)
    {Y : Subgroup (GL ι K)} (h3 : Nat.Coprime 3 (Nat.card Y)) {W : Type} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ρ : Representation K Y W)
    (hd : Module.finrank K W < Fintype.card ι) : Group.IsSolvable (toGLFin ρ).range :=
  hlow _ hd _ (Nat.Coprime.coprime_dvd_right (Subgroup.card_range_dvd _) h3)

noncomputable def redHom {Y : Subgroup (GL ι K)} (U : Submodule K (ι → K))
    (hle : ∀ g : Y, U ≤ U.comap (natRep Y g)) :
    Y →* (toGLFin ((natRep Y).subrepresentation U hle)).range ×
      (toGLFin ((natRep Y).quotient U hle)).range :=
  (toGLFin ((natRep Y).subrepresentation U hle)).rangeRestrict.prod
    (toGLFin ((natRep Y).quotient U hle)).rangeRestrict

theorem isPGroup_ker_redHom [Finite K] {Y : Subgroup (GL ι K)} (U : Submodule K (ι → K))
    (hle : ∀ g : Y, U ≤ U.comap (natRep Y g)) : IsPGroup (ringChar K) (redHom U hle).ker := by
  rintro ⟨⟨g, hgY⟩, hg⟩
  refine ⟨1, ?_⟩
  rw [redHom, MonoidHom.ker_prod, MonoidHom.ker_rangeRestrict, MonoidHom.ker_rangeRestrict,
    Subgroup.mem_inf] at hg
  have h₁ := eq_one_of_mem_ker_toGLFin _ hg.1
  have h₂ := eq_one_of_mem_ker_toGLFin _ hg.2
  have hU : ∀ u ∈ U, (g : Matrix ι ι K) *ᵥ u = u := fun u hu => by
    simpa [natRep] using congrArg Subtype.val (LinearMap.congr_fun h₁ ⟨u, hu⟩)
  have hQ : ∀ v, (g : Matrix ι ι K) *ᵥ v - v ∈ U := fun v =>
    (Submodule.Quotient.eq U).mp
      (by simpa [natRep] using LinearMap.congr_fun h₂ (Submodule.Quotient.mk v))
  rw [pow_one]
  exact Subtype.ext (Subtype.ext (by simpa using pow_ringChar_eq_one U g hU hQ))

theorem isSolvable_of_not_isIrreducibleOn {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hlow : ∀ d < Fintype.card ι, ∀ Y : Subgroup (GL (Fin d) K),
      Nat.Coprime 3 (Nat.card Y) → Group.IsSolvable Y)
    {Y : Subgroup (GL ι K)} (h3 : Nat.Coprime 3 (Nat.card Y)) (hred : ¬ IsIrreducibleOn Y) :
    Group.IsSolvable Y := by
  simp only [IsIrreducibleOn, not_forall, not_or] at hred
  obtain ⟨U, hU, hbot, htop⟩ := hred
  have hle : ∀ g : Y, U ≤ U.comap (natRep Y g) := fun g u hu => hU g g.2 u hu
  have hV : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  have hd₁ : Module.finrank K U < Fintype.card ι :=
    hV ▸ Submodule.finrank_lt htop
  have hd₂ : Module.finrank K ((ι → K) ⧸ U) < Fintype.card ι := by
    have := Submodule.finrank_quotient_add_finrank U
    have : 0 < Module.finrank K U :=
      Nat.pos_of_ne_zero fun h => hbot (Submodule.finrank_eq_zero.mp h)
    omega
  have := isSolvable_range_toGLFin hlow h3 ((natRep Y).subrepresentation U hle) hd₁
  have := isSolvable_range_toGLFin hlow h3 ((natRep Y).quotient U hle) hd₂
  have := Fact.mk (CharP.char_is_prime K (ringChar K))
  have := (isPGroup_ker_redHom U hle).isNilpotent
  exact Group.isSolvable_of_ker_le_range (redHom U hle).ker.subtype (redHom U hle) (by simp)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
