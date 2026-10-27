module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenLinAlg
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenCentral
public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedScalars StatedProj)
open Matrix

noncomputable def natAction (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type) [Field F] :
    GL ι F →* ((ι → F) ≃ₗ[F] (ι → F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin (n := ι) (R := F)).toMonoidHom

theorem natAction_injective (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type) [Field F] :
    Function.Injective (natAction ι F) := by
  unfold natAction
  exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).injective.comp
    (Matrix.GeneralLinearGroup.toLin (n := ι) (R := F)).injective)

theorem scalars_subgroupOf_facts (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type) [Field F]
    [Finite F] (H : Subgroup (GL ι F)) :
    (StatedScalars ι F).subgroupOf H ≤ Subgroup.center ↥H ∧
      Nat.card ((StatedScalars ι F).subgroupOf H) ∣ Nat.card F - 1 := by
  constructor
  · intro z hz
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hz : (z : GL ι F) ∈ StatedScalars ι F)
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : GL ι F) * (z : GL ι F) = (z : GL ι F) * (y : GL ι F)
    rw [← hc]
    exact (Matrix.GeneralLinearGroup.scalar_commute c (y : GL ι F)).symm
  · let ψ : ((StatedScalars ι F).subgroupOf H) →* ↥(StatedScalars ι F) :=
      { toFun := fun x => ⟨(x : H).1, x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hψ : Function.Injective ψ := fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(StatedScalars ι F) => (z : GL ι F)) hab
    have h1 := Subgroup.card_dvd_of_injective ψ hψ
    have h2 : Nat.card ↥(StatedScalars ι F) ∣ Nat.card Fˣ :=
      Subgroup.card_range_dvd (Matrix.GeneralLinearGroup.scalar ι)
    rw [Nat.card_units] at h2
    exact h1.trans h2

theorem not_dvd_card_normalizer_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] [Finite F] [CharP F 2] (H : Subgroup (GL ι F)) {r : ℕ} (hr : r.Prime)
    (hd2 : 2 ≤ Fintype.card ι) (hdvd : r ∣ Nat.card F ^ Fintype.card ι - 1)
    (hmin : ∀ k : ℕ, 0 < k → k < Fintype.card ι → ¬ r ∣ Nat.card F ^ k - 1)
    (R : Subgroup (StatedProj H)) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set (StatedProj H))) := by
  intro hrN
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hZc, hZcard⟩ := scalars_subgroupOf_facts ι F H
  have hrZ : ¬ r ∣ Nat.card ((StatedScalars ι F).subgroupOf H) := fun h =>
    hmin 1 one_pos (by omega) (by simpa using h.trans hZcard)
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨g, R', hgord, hR'2, hR'1, hgR'⟩ :=
    exists_lift_normalizing ((StatedScalars ι F).subgroupOf H) hZc hr hrZ R hR2 hR1 hrN
  let ρ : ↥H →* ((ι → F) ≃ₗ[F] (ι → F)) := (natAction ι F).comp H.subtype
  have hρinj : Function.Injective ρ :=
    (natAction_injective ι F).comp H.subtype_injective
  have hfin : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
  have hgr : g ^ r = 1 := hgord ▸ pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hgord
    exact hr.one_lt.ne hgord
  have hρg1 : ρ g ≠ 1 := fun h => hg1 (hρinj (by rw [h, map_one]))
  have hρgr : ρ g ^ r = 1 := by rw [← map_pow, hgr, map_one]
  have hirr : ∀ W : Submodule F (ι → F), (∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    submodule_eq_bot_or_top_of_ppd hr (ρ g) hρgr hρg1 (by rwa [hfin]) (by
      intro k hk hk'
      exact hmin k hk (by rwa [hfin] at hk')) W hW
  have hnorm : ∀ x ∈ R'.map ρ, (ρ g)⁻¹ * x * ρ g ∈ R'.map ρ := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨g⁻¹ * y * g, ?_, by simp [map_mul, map_inv]⟩
    have := (hgR' (g⁻¹ * y * g)).2 (by
      have : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [this]
      exact hy)
    exact this
  have hbot := eq_bot_of_irreducible_normalizing (R'.map ρ) (hR'2.map ρ) (ρ g) hnorm hirr
  exact hR'1 ((Subgroup.map_eq_bot_iff_of_injective _ hρinj).1 hbot)

theorem card_normalizer_dvd_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite B]
    (e : A ≃* B) (R : Subgroup A) :
    Nat.card (Subgroup.normalizer (R : Set A)) ∣
      Nat.card (Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup B) : Set B)) := by
  have h := Subgroup.le_normalizer_map (H := R) e.toMonoidHom
  have h1 : Nat.card ((Subgroup.normalizer (R : Set A)).map e.toMonoidHom) =
      Nat.card (Subgroup.normalizer (R : Set A)) :=
    Subgroup.card_map_of_injective e.injective
  rw [← h1]
  exact Subgroup.card_dvd_of_le h

theorem not_dvd_card_normalizer_of_equiv {K : Type} [Group K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 2] {H : Subgroup (GL ι F)}
    (e : K ≃* StatedProj H) {r : ℕ} (hr : r.Prime) (hd2 : 2 ≤ Fintype.card ι)
    (hdvd : r ∣ Nat.card F ^ Fintype.card ι - 1)
    (hmin : ∀ k : ℕ, 0 < k → k < Fintype.card ι → ¬ r ∣ Nat.card F ^ k - 1)
    (R : Subgroup K) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) := by
  intro hrN
  refine not_dvd_card_normalizer_statedProj H hr hd2 hdvd hmin (R.map e.toMonoidHom)
    (hR2.map e.toMonoidHom)
    (fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h))
    (hrN.trans (card_normalizer_dvd_of_mulEquiv e R))

theorem padicValNat_add_lt_of_not_dvd {r a b c : ℕ} (hr : r.Prime) (ha : ¬ r ∣ a)
    (hb : ¬ r ∣ b) (hc : c ≠ 0) (hrc : r ∣ c) :
    padicValNat r a + padicValNat r b < padicValNat r c := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [padicValNat.eq_zero_of_not_dvd ha, padicValNat.eq_zero_of_not_dvd hb, zero_add]
  exact one_le_padicValNat_of_dvd hc hrc

theorem sub_one_mul_add_one {A : ℕ} (hA : 1 ≤ A) : (A - 1) * (A + 1) = A * A - 1 := by
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : (B + 1) * (B + 1) = B * (B + 1 + 1) + 1 := by ring
  omega

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
