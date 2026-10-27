module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenOLPSUEvenGeom
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open (StatedScalars StatedProj)
open CFSG.LieType.BorelTits (ReflForm)
open Matrix

@[expose] noncomputable def natActionOL (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type)
    [Field F] : GL ι F →* ((ι → F) ≃ₗ[F] (ι → F)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin (n := ι) (R := F)).toMonoidHom

theorem natActionOL_injective (ι : Type) [Fintype ι] [DecidableEq ι] (F : Type) [Field F] :
    Function.Injective (natActionOL ι F) := by
  unfold natActionOL
  exact ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F)).injective.comp
    (Matrix.GeneralLinearGroup.toLin (n := ι) (R := F)).injective)

theorem natActionOL_apply {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (A : GL ι F) (u : ι → F) : natActionOL ι F A u = (A : Matrix ι ι F) *ᵥ u := by
  simp [natActionOL]

theorem not_dvd_card_normalizer_statedProj_isometry {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Finite F] [CharP F 2] (H : Subgroup (GL ι F)) (β : ReflForm F (ι → F))
    (hH : ∀ A ∈ H, ∀ u v : ι → F,
      β.β ((A : Matrix ι ι F) *ᵥ u) ((A : Matrix ι ι F) *ᵥ v) = β.β u v)
    {r d : ℕ} (hr : r.Prime) (hd : 2 ≤ d) (hcard : Fintype.card ι = d + 1)
    (hdvd : r ∣ Nat.card F ^ d - 1)
    (hmin : ∀ k : ℕ, 0 < k → k < d → ¬ r ∣ Nat.card F ^ k - 1)
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
  let ρ : ↥H →* ((ι → F) ≃ₗ[F] (ι → F)) := (natActionOL ι F).comp H.subtype
  have hρinj : Function.Injective ρ :=
    (natActionOL_injective ι F).comp H.subtype_injective
  have hρapp : ∀ (y : ↥H) (u : ι → F), ρ y u = ((y : GL ι F) : Matrix ι ι F) *ᵥ u :=
    fun y u => natActionOL_apply (y : GL ι F) u
  have hfin : Module.finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
  have hgr : g ^ r = 1 := hgord ▸ pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hgord
    exact hr.one_lt.ne hgord
  have hρg1 : ρ g ≠ 1 := fun h => hg1 (hρinj (by rw [h, map_one]))
  have hρgr : ρ g ^ r = 1 := by rw [← map_pow, hgr, map_one]
  have hiso : ∀ y : ↥H, ∀ u v : ι → F, β.β (ρ y u) (ρ y v) = β.β u v := fun y u v => by
    rw [hρapp, hρapp]
    exact hH (y : GL ι F) y.2 u v
  have hRg : ∀ x : (ι → F) ≃ₗ[F] (ι → F),
      x ∈ R'.map ρ ↔ ρ g * x * (ρ g)⁻¹ ∈ R'.map ρ := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y * g⁻¹, (hgR' y).1 hy, by simp [map_mul, map_inv]⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨g⁻¹ * z * g, (hgR' _).2 (by
        have : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
        rw [this]
        exact hz), ?_⟩
      rw [map_mul, map_mul, map_inv, hzx]
      group
  have hbot := eq_bot_of_isometry_normalizing_ppd β hr hd (by rw [hfin]; exact hcard) hdvd hmin
    (ρ g) hρgr hρg1 (hiso g) (R'.map ρ) (hR'2.map ρ)
    (by
      rintro _ ⟨y, -, rfl⟩ u v
      exact hiso y u v)
    hRg
  exact hR'1 ((Subgroup.map_eq_bot_iff_of_injective _ hρinj).1 hbot)

theorem not_dvd_card_normalizer_of_equiv_isometry {K : Type} [Group K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] [Finite F] [CharP F 2] {H : Subgroup (GL ι F)}
    (e : K ≃* StatedProj H) (β : ReflForm F (ι → F))
    (hH : ∀ A ∈ H, ∀ u v : ι → F,
      β.β ((A : Matrix ι ι F) *ᵥ u) ((A : Matrix ι ι F) *ᵥ v) = β.β u v)
    {r d : ℕ} (hr : r.Prime) (hd : 2 ≤ d) (hcard : Fintype.card ι = d + 1)
    (hdvd : r ∣ Nat.card F ^ d - 1)
    (hmin : ∀ k : ℕ, 0 < k → k < d → ¬ r ∣ Nat.card F ^ k - 1)
    (R : Subgroup K) (hR2 : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ¬ r ∣ Nat.card (Subgroup.normalizer (R : Set K)) := by
  intro hrN
  refine not_dvd_card_normalizer_statedProj_isometry H β hH hr hd hcard hdvd hmin
    (R.map e.toMonoidHom) (hR2.map e.toMonoidHom)
    (fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h))
    (hrN.trans (card_normalizer_dvd_of_mulEquiv e R))

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
