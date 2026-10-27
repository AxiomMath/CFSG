module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreLinMat
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.Open.PGLModelStated

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.OddCover CFSG.Quasithin

section Uni

variable {F : Type} [Field F] [Fintype F]

theorem diagHom_mem_statedSU {q m : ℕ} (hq0 : q ≠ 0) (t : Fin m → Fˣ) (h : ∏ i, t i = 1)
    (hq : ∀ i, (t i) ^ (q + 1) = 1) : diagHom m t ∈ StatedSU m q F := by
  rw [CFSG.PGLModel.statedSU_eq_closure_det]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, det_diagHom]
    have : (∏ i, (t i : F)) = ((∏ i, t i : Fˣ) : F) := by simp
    rw [this, h]
  · rw [coe_diagHom, Matrix.diagonal_map (by simp [hq0]), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hi := hq i
    rw [pow_succ] at hi
    have := congrArg Units.val hi
    simpa [Function.comp] using this

open scoped Classical in
theorem uniMat_ge4 {q r m : ℕ} [hr : Fact r.Prime] (hperm : PermBound r m) (hr2 : r ≠ 2)
    (hm : 4 ≤ m) (hF : Fintype.card F = q ^ 2) (hrq : r ∣ q + 1)
    (hconj : ∀ H : Subgroup (GL (Fin m) F), H ≤ StatedSU m q F → IsPGroup r H →
      ∃ g ∈ StatedGU m q F, ∀ x ∈ H,
        g * x * g⁻¹ ∈ (monEmb (unitsPPart F r).subtype m).range)
    (Z₀ : Subgroup ↥(StatedSU m q F)) [Z₀.Normal]
    (hZ₀ : Z₀ ≤ (StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)) :
    CFSG.Open.pRank r (⊤ : Subgroup (↥(StatedSU m q F) ⧸ Z₀)) =
      m - 1 - (if padicValNat r (Nat.card Z₀) =
          padicValNat r (Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F))) ∧
          padicValNat r (q + 1) ≤ padicValNat r m then 1 else 0) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : 0 < m := by omega
  have hq2 : 2 ≤ q := two_le_of_card_eq_sq hF
  have hacard : Nat.card (unitsPPart F r) = r ^ padicValNat r (q + 1) :=
    card_unitsPPart_of_dvd_add_one hr2 hF hrq
  have hF1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ha1 : 1 ≤ padicValNat r (q + 1) := one_le_padicValNat_of_dvd (by omega) hrq
  haveI : Nontrivial (unitsPPart F r) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hacard]
    exact Nat.one_lt_pow (by omega) hr.out.one_lt
  obtain ⟨f, hqf, hdata⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData F hF
  have hZsub : (Z₀.map (StatedSU m q F).subtype).subgroupOf (StatedSU m q F) = Z₀ :=
    Subgroup.comap_map_eq_self_of_injective (StatedSU m q F).subtype_injective Z₀
  haveI : ((Z₀.map (StatedSU m q F).subtype).subgroupOf (StatedSU m q F)).Normal := by
    rw [hZsub]
    infer_instance
  have hZG : Z₀.map (StatedSU m q F).subtype ≤ StatedSU m q F := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hZsc : Z₀.map (StatedSU m q F).subtype ≤ StatedScalars (Fin m) F := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hZ₀ hx)
  have hdiag : ∀ t : Fin m → unitsPPart F r, ∏ i, t i = 1 →
      diagHom m (fun i => (unitsPPart F r).subtype (t i)) ∈ StatedSU m q F := by
    intro t ht
    apply diagHom_mem_statedSU (by omega)
    · have := congrArg Subtype.val ht
      simpa using this
    · intro i
      exact pow_add_one_eq_one_of_mem_unitsPPart hr2 hF hrq (t i).2
  have hconj' : ∀ H : Subgroup (GL (Fin m) F), H ≤ StatedSU m q F → IsPGroup r H →
      ∃ g : GL (Fin m) F, (∀ x ∈ H, g * x * g⁻¹ ∈ StatedSU m q F) ∧
        ∀ x ∈ H, g * x * g⁻¹ ∈ (monEmb (unitsPPart F r).subtype m).range := by
    intro H hHU hH
    obtain ⟨g, hgU, hg⟩ := hconj H hHU hH
    refine ⟨g, fun x hx => ?_, hg⟩
    have hxGU : x ∈ StatedGU m q F :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
        (hHU hx)
    have hSL : g * x * g⁻¹ ∈ StatedSL m F :=
      conj_mem_statedSL g x (CFSG.Open.StatedAPI.statedSU_le_statedSL m q F (hHU hx))
    exact RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.mem_statedSU_of_mem_statedGU
      hdata hqf (Subgroup.mul_mem _ (Subgroup.mul_mem _ hgU hxGU) (Subgroup.inv_mem _ hgU))
      (CFSG.Open.StatedAPI.det_of_mem_statedSL hSL)
  have hcore := pRank_quot_core (F := F) (C := ↥(unitsPPart F r)) hperm hr2 hm
    (unitsPPart_isCyclic F r) (unitsPPart_isPGroup F r) (unitsPPart F r).subtype
    Subtype.val_injective (fun u hu => ⟨⟨u, hu⟩, rfl⟩)
    (monEmb (unitsPPart F r).subtype m) (monEmb_injective Subtype.val_injective m)
    (fun z => monEmb_monScalar (unitsPPart F r).subtype z)
    (fun x hx => monEmb_det_of_odd (unitsPPart F r).subtype x hx)
    (StatedSU m q F) (CFSG.Open.StatedAPI.statedSU_le_statedSL m q F) hdiag hconj'
    (Z₀.map (StatedSU m q F).subtype) hZG hZsc
  have hequiv := pRank_top_eq_of_mulEquiv (p := r) hr.out.one_lt
    (QuotientGroup.quotientMulEquivOfEq hZsub)
  rw [← hequiv, hcore]
  have hscR : (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F).range =
      StatedScalars (Fin m) F := rfl
  have hZle : Z₀.map (StatedSU m q F).subtype ≤
      (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F).range := hscR ▸ hZsc
  let Zu : Subgroup Fˣ := (Z₀.map (StatedSU m q F).subtype).comap
    (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F)
  let Du : Subgroup Fˣ := (StatedSU m q F).comap
    (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F)
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F) := scalarGL_injective hm1
  have hZu : Nat.card Zu = Nat.card Z₀ := by
    have h1 : Zu.map (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F) =
        Z₀.map (StatedSU m q F).subtype := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hZle
    rw [← Subgroup.card_map_of_injective hinj, h1,
      Subgroup.card_map_of_injective (StatedSU m q F).subtype_injective]
  have hDu : Nat.card Du =
      Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)) := by
    have h1 : Du.map (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F) =
        ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)).map
          (StatedSU m q F).subtype := by
      rw [Subgroup.map_comap_eq, Subgroup.subgroupOf_map_subtype, hscR, inf_comm]
    rw [← Subgroup.card_map_of_injective hinj, h1,
      Subgroup.card_map_of_injective (StatedSU m q F).subtype_injective]
  have hZD : Zu ≤ Du := fun u hu => hZG hu
  have hDm : ∀ u ∈ Du, u ^ m = 1 := fun u hu =>
    (scalar_mem_statedSL_iff u).1 (CFSG.Open.StatedAPI.statedSU_le_statedSL m q F hu)
  have hDμ : ∀ u ∈ unitsPPart F r, u ^ m = 1 → u ∈ Du := by
    intro u hu hum
    have hp : (ringChar F).Prime := (CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData F hF).elim
      fun _ h => h.2.prime
    have hK : Nat.card F = (ringChar F ^ f) ^ 2 := by
      rw [Nat.card_eq_fintype_card, hF, hqf]
    have := (CFSG.LinearGroups.scalar_mem_statedSU_iff hp hK hm1 u).2
      ⟨hum, hqf ▸ pow_add_one_eq_one_of_mem_unitsPPart hr2 hF hrq hu⟩
    rw [← hqf] at this
    exact this
  have hUa : padicValNat r (Nat.card Fˣ) = padicValNat r (q + 1) := by
    have h1 : r ^ padicValNat r (Fintype.card F - 1) = r ^ padicValNat r (q + 1) := by
      rw [← card_unitsPPart F r, hacard]
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
    exact Nat.pow_right_injective hr.out.two_le h1
  have hglue := sylow_le_iff_card (r := r) hm0 (unitsPPart F r) Zu Du hacard hUa hZD hDm hDμ
  have hD0 : 0 < Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)) :=
    Nat.card_pos
  have hZ0 : 0 < Nat.card Z₀ := Nat.card_pos
  have hZdvd : Nat.card Z₀ ∣
      Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)) :=
    Subgroup.card_dvd_of_le hZ₀
  have hiff : (∀ z : unitsPPart F r, Matrix.GeneralLinearGroup.scalar (Fin m)
        ((unitsPPart F r).subtype z) ∈ Z₀.map (StatedSU m q F).subtype) ↔
      (padicValNat r (Nat.card Z₀) =
          padicValNat r (Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F))) ∧
        padicValNat r (q + 1) ≤ padicValNat r m) := by
    have h1 : (∀ z : unitsPPart F r, Matrix.GeneralLinearGroup.scalar (Fin m)
        ((unitsPPart F r).subtype z) ∈ Z₀.map (StatedSU m q F).subtype) ↔
        unitsPPart F r ≤ Zu :=
      ⟨fun h u hu => h ⟨u, hu⟩, fun h z => h z.2⟩
    rw [h1, hglue, hZu, hDu, padicValNat_eq_iff_not_dvd_div hZ0 hD0 hZdvd]
  simp only [hiff]

end Uni

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
