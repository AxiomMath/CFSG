module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreGlue
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreUnits
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.OddCover

section Lin

variable {F : Type} [Field F] [Fintype F]

theorem diagHom_mem_statedSL {m : ℕ} (t : Fin m → Fˣ) (h : ∏ i, t i = 1) :
    diagHom m t ∈ StatedSL m F := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, det_diagHom]
  have : (∏ i, (t i : F)) = ((∏ i, t i : Fˣ) : F) := by simp
  rw [this, h]
  rfl

theorem conj_mem_statedSL {m : ℕ} (g x : GL (Fin m) F) (hx : x ∈ StatedSL m F) :
    g * x * g⁻¹ ∈ StatedSL m F := by
  rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det, MonoidHom.mem_ker] at hx ⊢
  rw [map_mul, map_mul, map_inv, hx, mul_one, mul_inv_cancel]

theorem padicValNat_eq_iff_not_dvd_div {r : ℕ} [hr : Fact r.Prime] {A B : ℕ} (hA : 0 < A)
    (hB : 0 < B) (hAB : A ∣ B) : padicValNat r A = padicValNat r B ↔ ¬ r ∣ B / A := by
  obtain ⟨n, rfl⟩ := hAB
  have hn : 0 < n := Nat.pos_of_mul_pos_left hB
  rw [Nat.mul_div_cancel_left _ hA, padicValNat.mul hA.ne' hn.ne']
  constructor
  · intro h hrn
    have : 0 < padicValNat r n := Nat.pos_of_ne_zero fun h0 => by
      rw [padicValNat.eq_zero_iff] at h0
      rcases h0 with h0 | h0 | h0
      · exact hr.out.one_lt.ne' h0
      · exact hn.ne' h0
      · exact h0 hrn
    omega
  · intro hrn
    have : padicValNat r n = 0 := by
      rw [padicValNat.eq_zero_iff]
      exact Or.inr (Or.inr hrn)
    omega

theorem scalar_mem_statedSL_iff {m : ℕ} (u : Fˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin m) u ∈ StatedSL m F ↔ u ^ m = 1 := by
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff, scalar_eq_diagHom_const, det_diagHom,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Units.val_pow_eq_pow_val]
  constructor
  · intro h
    exact Units.ext (by simpa using h)
  · intro h
    rw [h]
    rfl

open scoped Classical in
theorem linMat_ge4 {r m : ℕ} [hr : Fact r.Prime] (hperm : PermBound r m) (hr2 : r ≠ 2)
    (hm : 4 ≤ m) (hrF : r ∣ Fintype.card F - 1)
    (hconj : ∀ H : Subgroup (GL (Fin m) F), IsPGroup r H →
      ∃ g : GL (Fin m) F, ∀ x ∈ H, g * x * g⁻¹ ∈ (monEmb (unitsPPart F r).subtype m).range)
    (Z₀ : Subgroup ↥(StatedSL m F)) [Z₀.Normal]
    (hZ₀ : Z₀ ≤ (StatedScalars (Fin m) F).subgroupOf (StatedSL m F)) :
    CFSG.Open.pRank r (⊤ : Subgroup (↥(StatedSL m F) ⧸ Z₀)) =
      m - 1 - (if padicValNat r (Nat.card Z₀) =
          padicValNat r (Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F))) ∧
          padicValNat r (Fintype.card F - 1) ≤ padicValNat r m then 1 else 0) := by
  have hm1 : 1 ≤ m := by omega
  have hm0 : 0 < m := by omega
  have hacard : Nat.card (unitsPPart F r) = r ^ padicValNat r (Fintype.card F - 1) :=
    card_unitsPPart F r
  have hF1 : 0 < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have ha1 : 1 ≤ padicValNat r (Fintype.card F - 1) := one_le_padicValNat_of_dvd hF1.ne' hrF
  haveI : Nontrivial (unitsPPart F r) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hacard]
    exact Nat.one_lt_pow (by omega) hr.out.one_lt
  have hZsub : (Z₀.map (StatedSL m F).subtype).subgroupOf (StatedSL m F) = Z₀ :=
    Subgroup.comap_map_eq_self_of_injective (StatedSL m F).subtype_injective Z₀
  haveI : ((Z₀.map (StatedSL m F).subtype).subgroupOf (StatedSL m F)).Normal := by
    rw [hZsub]
    infer_instance
  have hZG : Z₀.map (StatedSL m F).subtype ≤ StatedSL m F := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hZsc : Z₀.map (StatedSL m F).subtype ≤ StatedScalars (Fin m) F := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hZ₀ hx)
  have hdiag : ∀ t : Fin m → unitsPPart F r, ∏ i, t i = 1 →
      diagHom m (fun i => (unitsPPart F r).subtype (t i)) ∈ StatedSL m F := by
    intro t ht
    apply diagHom_mem_statedSL
    have := congrArg Subtype.val ht
    simpa using this
  have hconj' : ∀ H : Subgroup (GL (Fin m) F), H ≤ StatedSL m F → IsPGroup r H →
      ∃ g : GL (Fin m) F, (∀ x ∈ H, g * x * g⁻¹ ∈ StatedSL m F) ∧
        ∀ x ∈ H, g * x * g⁻¹ ∈ (monEmb (unitsPPart F r).subtype m).range := by
    intro H hHG hH
    obtain ⟨g, hg⟩ := hconj H hH
    exact ⟨g, fun x hx => conj_mem_statedSL g x (hHG hx), hg⟩
  have hcore := pRank_quot_core (F := F) (C := ↥(unitsPPart F r)) hperm hr2 hm
    (unitsPPart_isCyclic F r) (unitsPPart_isPGroup F r) (unitsPPart F r).subtype
    Subtype.val_injective (fun u hu => ⟨⟨u, hu⟩, rfl⟩)
    (monEmb (unitsPPart F r).subtype m) (monEmb_injective Subtype.val_injective m)
    (fun z => monEmb_monScalar (unitsPPart F r).subtype z)
    (fun x hx => monEmb_det_of_odd (unitsPPart F r).subtype x hx)
    (StatedSL m F) le_rfl hdiag hconj' (Z₀.map (StatedSL m F).subtype) hZG hZsc
  have hequiv := pRank_top_eq_of_mulEquiv (p := r) hr.out.one_lt
    (QuotientGroup.quotientMulEquivOfEq hZsub)
  rw [← hequiv, hcore]
  have hscR : (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F).range =
      StatedScalars (Fin m) F := rfl
  have hZle : Z₀.map (StatedSL m F).subtype ≤
      (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F).range := hscR ▸ hZsc
  let Zu : Subgroup Fˣ := (Z₀.map (StatedSL m F).subtype).comap
    (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F)
  let Du : Subgroup Fˣ := (StatedSL m F).comap
    (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F)
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F) := scalarGL_injective hm1
  have hZu : Nat.card Zu = Nat.card Z₀ := by
    have h1 : Zu.map (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F) =
        Z₀.map (StatedSL m F).subtype := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hZle
    rw [← Subgroup.card_map_of_injective hinj, h1,
      Subgroup.card_map_of_injective (StatedSL m F).subtype_injective]
  have hDu : Nat.card Du =
      Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)) := by
    have h1 : Du.map (Matrix.GeneralLinearGroup.scalar (Fin m) : Fˣ →* GL (Fin m) F) =
        ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)).map (StatedSL m F).subtype := by
      rw [Subgroup.map_comap_eq, Subgroup.subgroupOf_map_subtype, hscR, inf_comm]
    rw [← Subgroup.card_map_of_injective hinj, h1,
      Subgroup.card_map_of_injective (StatedSL m F).subtype_injective]
  have hZD : Zu ≤ Du := fun u hu => hZG hu
  have hDm : ∀ u ∈ Du, u ^ m = 1 := fun u hu => (scalar_mem_statedSL_iff u).1 hu
  have hDμ : ∀ u ∈ unitsPPart F r, u ^ m = 1 → u ∈ Du := fun u _ hu =>
    (scalar_mem_statedSL_iff u).2 hu
  have hUa : padicValNat r (Nat.card Fˣ) = padicValNat r (Fintype.card F - 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hglue := sylow_le_iff_card (r := r) hm0 (unitsPPart F r) Zu Du hacard hUa hZD hDm hDμ
  have hD0 : 0 < Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)) := Nat.card_pos
  have hZ0 : 0 < Nat.card Z₀ := Nat.card_pos
  have hZdvd : Nat.card Z₀ ∣ Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F)) :=
    Subgroup.card_dvd_of_le hZ₀
  have hiff : (∀ z : unitsPPart F r, Matrix.GeneralLinearGroup.scalar (Fin m)
        ((unitsPPart F r).subtype z) ∈ Z₀.map (StatedSL m F).subtype) ↔
      (padicValNat r (Nat.card Z₀) =
          padicValNat r (Nat.card ((StatedScalars (Fin m) F).subgroupOf (StatedSL m F))) ∧
        padicValNat r (Fintype.card F - 1) ≤ padicValNat r m) := by
    have h1 : (∀ z : unitsPPart F r, Matrix.GeneralLinearGroup.scalar (Fin m)
        ((unitsPPart F r).subtype z) ∈ Z₀.map (StatedSL m F).subtype) ↔ unitsPPart F r ≤ Zu :=
      ⟨fun h u hu => h ⟨u, hu⟩, fun h z => h z.2⟩
    rw [h1, hglue, hZu, hDu, padicValNat_eq_iff_not_dvd_div hZ0 hD0 hZdvd]
  simp only [hiff]

end Lin

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
