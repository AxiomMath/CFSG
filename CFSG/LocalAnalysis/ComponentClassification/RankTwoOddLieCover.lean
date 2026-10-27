module

public import CFSG.ClassicalInvolution.ModelFacts.CentralLiftE6
import CFSG.ClassicalInvolution.SmallCases.UpgradeCover

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.Blueprint
open scoped MatrixGroups commutatorElement

theorem isFundTag_of_admissible {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hp2 : p ≠ 2) (hG : t ≠ .twistedG2) : IsFundTag t := by
  cases t <;> first
    | exact trivial
    | exact absurd rfl hG
    | (obtain ⟨-, -, -, h2, -⟩ := hadm; exact absurd h2 hp2)

theorem reeTitsModel_of_lieModel {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .twistedG2 n p f) : ReeTitsModel X .twistedG2 p f :=
  (CFSG.Blueprint.LieModel.reeTitsModel h (by decide)).2

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have : a ∈ center G := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem exists_ne_comm_quotient_center {B : Type*} [Group B] (hB : Open.IsQuasisimple B) :
    ∃ a b : B ⧸ center B, a * b ≠ b * a := by
  have : IsSimpleGroup (B ⧸ center B) := hB.2
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : B ⧸ center B)
  apply hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  have hxB : x ∈ commutator B := hB.1 ▸ Subgroup.mem_top x
  have hle : commutator B ≤ (QuotientGroup.mk' (center B)).ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      hcon (QuotientGroup.mk' _ g₁) (QuotientGroup.mk' _ g₂), mul_inv_cancel_right,
      mul_inv_cancel]
  exact MonoidHom.mem_ker.mp (hle hxB)

theorem commutatorElement_mul_center {G : Type*} [Group G] (a b : G) {z z' : G}
    (hz : z ∈ center G) (hz' : z' ∈ center G) : ⁅a * z, b * z'⁆ = ⁅a, b⁆ := by
  have hzc : ∀ w : G, w * z = z * w := Subgroup.mem_center_iff.mp hz
  have hz'c : ∀ w : G, w * z' = z' * w := Subgroup.mem_center_iff.mp hz'
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * z') * (a * z)⁻¹ * (b * z')⁻¹
      = a * (z * b) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [← hzc b]
    _ = a * b * (z * z') * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by group
    _ = a * b * (z' * z) * z⁻¹ * a⁻¹ * z'⁻¹ * b⁻¹ := by rw [← hzc z']
    _ = a * b * (z' * a⁻¹) * z'⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z') * z'⁻¹ * b⁻¹ := by rw [← hz'c a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem exists_surjective_of_lieModel {B : Type} [Group B] [Finite B] (hB : Open.IsQuasisimple B)
    (hZ : IsPGroup 2 (center B))
    {t : StatedLieTag} {n p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hFT : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e) (hL : LieModel (B ⧸ center B) t n p e) :
    ∃ φ : (modelUniv t n p e hp).K →* B,
      Function.Surjective φ ∧ φ.ker ≤ center (modelUniv t n p e hp).K := by
  have : IsSimpleGroup (B ⧸ center B) := hB.2
  have hna := exists_ne_comm_quotient_center hB
  obtain ⟨ψ, hψs, hψk⟩ :=
    Upgrade.lieModelCentralCover t n p e hp hp2 hFT hadm (B ⧸ center B) hL
  have hker : ψ.ker = center (modelUniv t n p e hp).K := by
    refine le_antisymm hψk fun k hk => ?_
    have hc : ψ k ∈ center (B ⧸ center B) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := hψs g
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hk) g]
    rw [center_eq_bot_of_simple hna, Subgroup.mem_bot] at hc
    exact hc
  obtain ⟨ψ', hψ'⟩ := ClassicalInvolution.ModelFacts.centralLift p hp2 t n e hp hFT hadm B
    (B ⧸ center B) hna (QuotientGroup.mk' _) ψ (QuotientGroup.mk'_surjective _) hψs ⟨hB.1⟩
    (by rwa [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']) hker
  refine ⟨ψ', ?_, ?_⟩
  ·
    have hdec : ∀ x : B, ∃ k, ∃ z ∈ center B, x = ψ' k * z := by
      intro x
      obtain ⟨k, hk⟩ := hψs (QuotientGroup.mk' _ x)
      have h1 : QuotientGroup.mk' (center B) (ψ' k) = QuotientGroup.mk' (center B) x := by
        rw [← hk, ← MonoidHom.comp_apply, hψ']
      refine ⟨k, (ψ' k)⁻¹ * x, ?_, by group⟩
      rw [← QuotientGroup.eq]
      exact h1
    have hle : commutator B ≤ ψ'.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨k, z, hz, rfl⟩ := hdec x
      obtain ⟨k', z', hz', rfl⟩ := hdec y
      exact ⟨⁅k, k'⁆, by rw [map_commutatorElement, commutatorElement_mul_center _ _ hz hz']⟩
    intro x
    have : x ∈ ψ'.range := hle (hB.1 ▸ Subgroup.mem_top x)
    exact this
  · intro k hk
    rw [← hker, MonoidHom.mem_ker, ← hψ', MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one]

theorem sl2_or_psl2_of_surjective {F : Type*} [Field F] {B : Type*} [Group B] (φ : SL(2, F) →* B)
    (hφs : Function.Surjective φ) (hφk : φ.ker ≤ center SL(2, F)) :
    Nonempty (B ≃* SL(2, F)) ∨ Nonempty (B ≃* PSL(2, F)) := by
  by_cases hk : φ.ker = ⊥
  · left
    exact ⟨(MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hk, hφs⟩).symm⟩
  · right
    have hkc : φ.ker = center SL(2, F) := by
      refine le_antisymm hφk fun x hx => ?_
      obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hk
      have hy1' : y ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
      rcases (mem_center_sl2_iff y).mp (hφk hy) with h1 | h1
      · exact absurd h1 hy1'
      · rcases (mem_center_sl2_iff x).mp hx with h2 | h2
        · rw [h2]; exact one_mem _
        · rw [h2, ← h1]; exact hy
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hkc).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)).symm⟩

end CFSG.ComponentClassification.RankTwoOddLie
