module

public import CFSG.Adapters.TauCetiExceptional.TwistedD4Block
public import CFSG.Adapters.TauCetiExceptional.TwistedEndgame

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti BigCell
open CFSG.TauCetiBridge.Minuscule

structure D4PushDown
    (L : Type) [Field L] where
  π : ↥(D4Tripled.points L) →* ModGL .D4 L
  π_u : ∀ (i : Fin 4) (c : L),
    π (D4Tripled.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd c)) = xUnit .D4 L (d4Node i) c
  π_v : ∀ (i : Fin 4) (c : L),
    π (D4Tripled.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd c)) = yUnit .D4 L (d4Node i) c
  zeros : ∀ (z : ↥(D4Tripled.points L)) (P : MvPolynomial (Fin (nLab .D4) × Fin (nLab .D4)) ℤ),
    VanishesOnRat .D4 P →
      evalMat (natMat .D4 L (π z : Module.End L (RootModule .D4 L))) P = 0
  ker_iff : ∀ z : ↥(D4Tripled.points L), π z = 1 ↔ ∀ i,
    (((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) * d4E L i =
      d4E L i * ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L)) ∧
    (((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) * d4F L i =
      d4F L i * ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L))

namespace D4PushDown

variable {L : Type} [Field L] (P : D4PushDown L)

abbrev u (i : Fin (Tag.rank .D4)) (c : L) : ↥(D4Tripled.points L) :=
  D4Tripled.rootSubgroupPoints (.inl (d4Node.symm i)) L (Multiplicative.ofAdd c)

abbrev v (i : Fin (Tag.rank .D4)) (c : L) : ↥(D4Tripled.points L) :=
  D4Tripled.rootSubgroupPoints (.inr (d4Node.symm i)) L (Multiplicative.ofAdd c)

theorem coe_u (i : Fin (Tag.rank .D4)) (c : L) :
    (((u i c : ↥(D4Tripled.points L)) : Matrix.GeneralLinearGroup (Fin 24) L) :
      Matrix (Fin 24) (Fin 24) L) = 1 + c • d4E L i := by
  rw [D4Tripled.coe_rootSubgroupPoints_inl, toAdd_ofAdd]
  rfl

theorem coe_v (i : Fin (Tag.rank .D4)) (c : L) :
    (((v i c : ↥(D4Tripled.points L)) : Matrix.GeneralLinearGroup (Fin 24) L) :
      Matrix (Fin 24) (Fin 24) L) = 1 + c • d4F L i := by
  rw [D4Tripled.coe_rootSubgroupPoints_inr, toAdd_ofAdd]
  rfl

theorem commute_of_commute_one_add {M E : Matrix (Fin 24) (Fin 24) L}
    (h : M * (1 + E) = (1 + E) * M) : M * E = E * M := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

theorem commute_diag_of {M : Matrix (Fin 24) (Fin 24) L}
    (h : ∀ i, M * d4E L i = d4E L i * M ∧ M * d4F L i = d4F L i * M) (i : Fin (Tag.rank .D4)) :
    M * Matrix.diagonal (fun a => (d4Wt a i : L)) =
      Matrix.diagonal (fun a => (d4Wt a i : L)) * M := by
  have h1 : M * (d4E L i * d4F L i) = d4E L i * d4F L i * M := by
    rw [← Matrix.mul_assoc, (h i).1, Matrix.mul_assoc, (h i).2, Matrix.mul_assoc]
  have h3 : M * (d4F L i * d4E L i) = d4F L i * d4E L i * M := by
    rw [← Matrix.mul_assoc, (h i).2, Matrix.mul_assoc, (h i).1, Matrix.mul_assoc]
  rw [← d4E_comm L i, Matrix.mul_sub, Matrix.sub_mul, h1, h3]

theorem mem_center_of_commute
    (h2 : (2 : L) ≠ 0) {z : ↥(D4Tripled.points L)}
    (h : ∀ i, ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) *
        d4E L i = d4E L i * ((z : Matrix.GeneralLinearGroup (Fin 24) L) :
          Matrix (Fin 24) (Fin 24) L) ∧
      ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) * d4F L i =
        d4F L i * ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L)) :
    z ∈ Subgroup.center ↥(D4Tripled.points L) := by
  have hdiag : ∀ a b, a ≠ b →
      ((z : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L) a b = 0 :=
    fun a b hab => d4_isDiag_of_commute h2 (commute_diag_of h) hab
  rw [Subgroup.mem_center_iff]
  intro w
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  exact (commute_of_diag d4Blk hdiag
    (fun a b hab => d4_diag_eq_of_commute hdiag (fun i => (h i).1) (fun i => (h i).2) hab)
    (d4_points_isBlockDiag L _ w.2)).symm

theorem π_eq_one_of_mem_center {z : ↥(D4Tripled.points L)}
    (hz : z ∈ Subgroup.center ↥(D4Tripled.points L)) : P.π z = 1 := by
  rw [P.ker_iff]
  intro i
  have hu := congrArg (fun w : ↥(D4Tripled.points L) =>
    ((w : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L))
    (Subgroup.mem_center_iff.1 hz (u i 1))
  have hv := congrArg (fun w : ↥(D4Tripled.points L) =>
    ((w : Matrix.GeneralLinearGroup (Fin 24) L) : Matrix (Fin 24) (Fin 24) L))
    (Subgroup.mem_center_iff.1 hz (v i 1))
  simp only [Subgroup.coe_mul, Units.val_mul, coe_u, coe_v, one_smul] at hu hv
  exact ⟨commute_of_commute_one_add hu.symm, commute_of_commute_one_add hv.symm⟩

@[expose] def blockCarrier
    (h2 : (2 : L) ≠ 0) : BlockCarrier .D4 L 24 3 where
  C := D4Tripled.points L
  π := P.π
  u := u
  v := v
  E := d4E L
  F := d4F L
  coe_u := coe_u
  coe_v := coe_v
  u_add i c d := by simp only [u, ofAdd_add, map_mul]
  v_add i c d := by simp only [v, ofAdd_add, map_mul]
  π_u i c := by rw [P.π_u, Equiv.apply_symm_apply]
  π_v i c := by rw [P.π_v, Equiv.apply_symm_apply]
  blk := d4Blk
  block z := d4_points_isBlockDiag L _ z.2
  ker_diag z hz _ _ hab := d4_isDiag_of_commute h2 (commute_diag_of ((P.ker_iff z).1 hz)) hab
  ker_center z hz := mem_center_of_commute h2 ((P.ker_iff z).1 hz)
  wt := d4Wt
  wt_mem := d4Wt_mem
  comm := d4E_comm L
  comm_HE := d4E_commH L
  E_ne := d4E_ne_zero L
  cartan_off := cartan_D4_off
  excl := d4_excl

end D4PushDown

end CFSG.TauCetiBridge.Twisted
