module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Steinberg.Adjoint.BaseChange

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem position_injective :
    Function.Injective (Label.position (τ := τ)) := by
  intro a b h
  by_contra hab
  rcases Label.precedes_or_precedes hab with h' | h'
  · exact absurd h (Label.position_lt_position h').ne
  · exact absurd h.symm (Label.position_lt_position h').ne

abbrev nLab (τ : Tag) : ℕ := Fintype.card (Label τ)

@[expose] def posEquiv (τ : Tag) : Label τ ≃ Fin (nLab τ) :=
  Equiv.ofBijective (fun a => ⟨a.position, a.position_lt_card⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h => position_injective (Fin.mk.inj h), by simp⟩)

theorem posEquiv_val
    (a : Label τ) : (posEquiv τ a).val = a.position :=
  rfl

theorem precedes_iff_posEquiv_lt (a b : Label τ) :
    a.Precedes b ↔ posEquiv τ a < posEquiv τ b := by
  rw [Fin.lt_def, posEquiv_val, posEquiv_val]
  refine ⟨Label.position_lt_position, fun h => ?_⟩
  have hab : a ≠ b := fun e => by rw [e] at h; exact lt_irrefl _ h
  rcases Label.precedes_or_precedes hab with h' | h'
  · exact h'
  · exact absurd (Label.position_lt_position h') (by omega)

variable (τ) (R : Type*) [CommRing R]

@[expose] def natBasis :
    Module.Basis (Fin (nLab τ)) R (RootModule τ R) :=
  Finsupp.basisSingleOne.reindex (posEquiv τ)

@[expose] def natMat :
    Module.End R (RootModule τ R) ≃ₐ[R] Matrix (Fin (nLab τ)) (Fin (nLab τ)) R :=
  LinearMap.toMatrixAlgEquiv (natBasis τ R)

variable {τ R}

theorem natMat_apply
    (A : Module.End R (RootModule τ R)) (i j : Fin (nLab τ)) :
    natMat τ R A i j = A (Finsupp.single ((posEquiv τ).symm j) 1) ((posEquiv τ).symm i) := by
  simp only [natMat, LinearMap.toMatrixAlgEquiv_apply, natBasis, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply, Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr,
    LinearEquiv.refl_apply]

theorem natMat_apply_posEquiv
    (A : Module.End R (RootModule τ R)) (a b : Label τ) :
    natMat τ R A (posEquiv τ a) (posEquiv τ b) = A (Finsupp.single b 1) a := by
  rw [natMat_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem natMat_of_baseChange {S : Type*} [CommRing S] {f : R →+* S}
    {A : Module.End R (RootModule τ R)} {B : Module.End S (RootModule τ S)}
    (h : BaseChange f A B) : natMat τ S B = f.mapMatrix (natMat τ R A) := by
  ext i j
  rw [natMat_apply, RingHom.mapMatrix_apply, Matrix.map_apply, natMat_apply, ← h]
  rfl

theorem natMat_posUnipotent
    {g : (Module.End R (RootModule τ R))ˣ} (hg : g ∈ posUnipotent τ R) :
    (∀ i, natMat τ R g i i = 1) ∧ ∀ i j, j < i → natMat τ R g i j = 0 := by
  have h := isUpperUnitriangular_of_mem (posUnipotent_le_posFiltration τ R hg)
  refine ⟨fun i => by rw [natMat_apply]; exact h.1 _, fun i j hji => ?_⟩
  rw [natMat_apply]
  refine h.2 _ _ ((precedes_iff_posEquiv_lt _ _).2 ?_)
  simpa using hji

theorem natMat_negUnipotent
    {g : (Module.End R (RootModule τ R))ˣ} (hg : g ∈ negUnipotent τ R) :
    (∀ i, natMat τ R g i i = 1) ∧ ∀ i j, i < j → natMat τ R g i j = 0 := by
  have h := isLowerUnitriangular_of_mem (negUnipotent_le_posFiltration τ R hg)
  refine ⟨fun i => by rw [natMat_apply]; exact h.1 _, fun i j hij => ?_⟩
  rw [natMat_apply]
  refine h.2 _ _ ((precedes_iff_posEquiv_lt _ _).2 ?_)
  simpa using hij

theorem torusGroup_apply_single
    {g : (Module.End R (RootModule τ R))ˣ} (hg : g ∈ torusGroup τ R)
    (b : Label τ) : ∃ c : Rˣ, (g : Module.End R (RootModule τ R)) (Finsupp.single b 1) =
      (c : R) • Finsupp.single b 1 := by
  have h := torusGroup_le_diagonalGroup hg
  rcases b with j | ⟨α, hα⟩
  · exact ⟨1, by rw [Units.val_one, one_smul]; exact h.1 j⟩
  · obtain ⟨c, hc⟩ := h.2 α hα
    refine ⟨c, ?_⟩
    have e : rootVec τ R α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 := by
      rw [rootVec, dite_eq_left hα]
    rw [← e]
    exact hc

theorem isUnit_natMat_torusGroup
    {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ torusGroup τ R) (i : Fin (nLab τ)) : IsUnit (natMat τ R g i i) := by
  obtain ⟨c, hc⟩ := torusGroup_apply_single hg ((posEquiv τ).symm i)
  rw [natMat_apply, hc, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  exact c.isUnit

theorem natMat_torusGroup
    {g : (Module.End R (RootModule τ R))ˣ} (hg : g ∈ torusGroup τ R)
    (i j : Fin (nLab τ)) (hij : i ≠ j) : natMat τ R g i j = 0 := by
  obtain ⟨c, hc⟩ := torusGroup_apply_single hg ((posEquiv τ).symm j)
  rw [natMat_apply, hc, Finsupp.smul_apply, Finsupp.single_eq_of_ne, smul_zero]
  exact fun e => hij ((posEquiv τ).symm.injective e)

@[expose] def IntegralIn
    (S : Subring R) (A : Module.End R (RootModule τ R)) : Prop :=
  ∀ i j, natMat τ R A i j ∈ S

theorem IntegralIn.mul
    {S : Subring R} {A B : Module.End R (RootModule τ R)}
    (hA : IntegralIn S A) (hB : IntegralIn S B) : IntegralIn S (A * B) := fun i j => by
  rw [map_mul, Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

theorem IntegralIn.one
    (S : Subring R) : IntegralIn (τ := τ) S 1 := fun i j => by
  rw [map_one, Matrix.one_apply]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem

theorem IntegralIn.list_prod {S : Subring R} :
    ∀ L : List (Module.End R (RootModule τ R)), (∀ A ∈ L, IntegralIn S A) →
      IntegralIn S L.prod
  | [], _ => by simpa using IntegralIn.one (τ := τ) S
  | A :: L, h => by
    rw [List.prod_cons]
    exact (h A List.mem_cons_self).mul
      (IntegralIn.list_prod L fun B hB => h B (List.mem_cons_of_mem _ hB))

theorem integralIn_of_baseChange
    (S : Subring R) {A : Module.End ℤ (RootModule τ ℤ)}
    {B : Module.End R (RootModule τ R)} (h : BaseChange (Int.castRingHom R) A B) :
    IntegralIn S B := fun i j => by
  rw [natMat_of_baseChange h, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact intCast_mem S _

end CFSG.TauCetiBridge.BigCell
