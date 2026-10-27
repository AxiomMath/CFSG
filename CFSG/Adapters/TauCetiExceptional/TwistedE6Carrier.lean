module

public import CFSG.Adapters.TauCetiExceptional.TwistedE6Block
public import CFSG.Adapters.TauCetiExceptional.TwistedEndgame

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell
open CFSG.TauCetiBridge.Minuscule

structure E6PushDown
    (L : Type) [Field L] where
  π : ↥(E6DoubledMinuscule.points L) →* ModGL .E6 L
  π_u : ∀ (i : Fin 6) (c : L),
    π (E6DoubledMinuscule.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd c)) =
      xUnit .E6 L i c
  π_v : ∀ (i : Fin 6) (c : L),
    π (E6DoubledMinuscule.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd c)) =
      yUnit .E6 L i c
  zeros : ∀ (z : ↥(E6DoubledMinuscule.points L))
    (P : MvPolynomial (Fin (nLab .E6) × Fin (nLab .E6)) ℤ), VanishesOnRat .E6 P →
      evalMat (natMat .E6 L (π z : Module.End L (RootModule .E6 L))) P = 0
  ker_iff : ∀ z : ↥(E6DoubledMinuscule.points L), π z = 1 ↔ ∀ i,
    (((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) * e6E L i =
      e6E L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L)) ∧
    (((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) * e6F L i =
      e6F L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L))

namespace E6PushDown

variable {L : Type} [Field L] (P : E6PushDown L)

abbrev u (i : Fin 6) (c : L) : ↥(E6DoubledMinuscule.points L) :=
  E6DoubledMinuscule.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd c)

abbrev v (i : Fin 6) (c : L) : ↥(E6DoubledMinuscule.points L) :=
  E6DoubledMinuscule.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd c)

theorem coe_u (i : Fin 6) (c : L) :
    (((u i c : ↥(E6DoubledMinuscule.points L)) : Matrix.GeneralLinearGroup (Fin 54) L) :
      Matrix (Fin 54) (Fin 54) L) = 1 + c • e6E L i := by
  rw [E6DoubledMinuscule.coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  rfl

theorem coe_v (i : Fin 6) (c : L) :
    (((v i c : ↥(E6DoubledMinuscule.points L)) : Matrix.GeneralLinearGroup (Fin 54) L) :
      Matrix (Fin 54) (Fin 54) L) = 1 + c • e6F L i := by
  rw [E6DoubledMinuscule.coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  rfl

theorem commute_of_commute_one_add {M E : Matrix (Fin 54) (Fin 54) L}
    (h : M * (1 + E) = (1 + E) * M) : M * E = E * M := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

theorem commute_diag_of {M : Matrix (Fin 54) (Fin 54) L}
    (h : ∀ i, M * e6E L i = e6E L i * M ∧ M * e6F L i = e6F L i * M) (i : Fin (Tag.rank .E6)) :
    M * Matrix.diagonal (fun a => (e6Wt a i : L)) =
      Matrix.diagonal (fun a => (e6Wt a i : L)) * M := by
  have h1 : M * (e6E L i * e6F L i) = e6E L i * e6F L i * M := by
    rw [← Matrix.mul_assoc, (h i).1, Matrix.mul_assoc, (h i).2, Matrix.mul_assoc]
  have h3 : M * (e6F L i * e6E L i) = e6F L i * e6E L i * M := by
    rw [← Matrix.mul_assoc, (h i).2, Matrix.mul_assoc, (h i).1, Matrix.mul_assoc]
  rw [← e6E_comm L i, Matrix.mul_sub, Matrix.sub_mul, h1, h3]

theorem mem_center_of_commute (h2 : (2 : L) ≠ 0) {z : ↥(E6DoubledMinuscule.points L)}
    (h : ∀ i, ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) *
        e6E L i = e6E L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) :
          Matrix (Fin 54) (Fin 54) L) ∧
      ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) * e6F L i =
        e6F L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L)) :
    z ∈ Subgroup.center ↥(E6DoubledMinuscule.points L) := by
  have hdiag : ∀ a b, a ≠ b →
      ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) a b = 0 :=
    fun a b hab => e6_isDiag_of_commute h2 (commute_diag_of h) hab
  rw [Subgroup.mem_center_iff]
  intro w
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact (commute_of_diag e6Blk hdiag
    (fun a b hab => e6_diag_eq_of_commute hdiag (fun i => (h i).1) (fun i => (h i).2) hab)
    (e6d_points_isBlockDiag L _ w.2)).symm

theorem π_eq_one_of_mem_center {z : ↥(E6DoubledMinuscule.points L)}
    (hz : z ∈ Subgroup.center ↥(E6DoubledMinuscule.points L)) : P.π z = 1 := by
  rw [P.ker_iff]
  intro i
  have hu := congrArg (fun w : ↥(E6DoubledMinuscule.points L) =>
    ((w : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L))
    (Subgroup.mem_center_iff.1 hz (u i 1))
  have hv := congrArg (fun w : ↥(E6DoubledMinuscule.points L) =>
    ((w : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L))
    (Subgroup.mem_center_iff.1 hz (v i 1))
  simp only [Subgroup.coe_mul, Units.val_mul] at hu hv
  rw [coe_u, one_smul] at hu
  rw [coe_v, one_smul] at hv
  exact ⟨commute_of_commute_one_add hu.symm, commute_of_commute_one_add hv.symm⟩

@[expose] def blockCarrier (h2 : (2 : L) ≠ 0) : BlockCarrier .E6 L 54 2 where
  C := E6DoubledMinuscule.points L
  π := P.π
  u := u
  v := v
  E := e6E L
  F := e6F L
  coe_u := coe_u
  coe_v := coe_v
  u_add i c d := by simp only [u, ofAdd_add, map_mul]
  v_add i c d := by simp only [v, ofAdd_add, map_mul]
  π_u i c := P.π_u i c
  π_v i c := P.π_v i c
  blk := e6Blk
  block z := e6d_points_isBlockDiag L _ z.2
  ker_diag z hz _ _ hab := e6_isDiag_of_commute h2 (commute_diag_of ((P.ker_iff z).1 hz)) hab
  ker_center z hz := mem_center_of_commute h2 ((P.ker_iff z).1 hz)
  wt := e6Wt
  wt_mem := e6Wt_mem
  comm := e6E_comm L
  comm_HE := e6E_commH L
  E_ne := e6E_ne_zero L
  cartan_off := cartan_E6_off
  excl := fun π' hc h => e6_excl π' hc h

end E6PushDown

end CFSG.TauCetiBridge.Twisted
