module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReducePSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftFourCover
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

namespace ToralReduce

variable {X : Type} [Group X] {K : Type} [Field K]

theorem center_eq_bot_of_not_dvd [Finite K] (hX : commutator X = ⊤) (h : ¬ 3 ∣ Nat.card K - 1)
    (h5 : 5 ≤ Nat.card K) (φ : X ⧸ Subgroup.center X ≃* projectiveSL 3 K) :
    Subgroup.center X = ⊥ := by
  let e : Matrix.SpecialLinearGroup (Fin (2 + 1)) K ≃* projectiveSL 3 K :=
    MulEquiv.ofBijective (proj 3 K) ⟨proj_injective_of_not_dvd h, proj_surjective 3 K⟩
  let π : X →* Matrix.SpecialLinearGroup (Fin (2 + 1)) K :=
    e.symm.toMonoidHom.comp (φ.toMonoidHom.comp (QuotientGroup.mk' _))
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center X := fun x => by
    change e.symm (φ (QuotientGroup.mk' _ x)) = 1 ↔ _
    rw [map_eq_one_iff _ e.symm.injective, map_eq_one_iff _ φ.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hcen : π.ker ≤ Subgroup.center X := fun x hx => (hker x).mp hx
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
    (m := 2) le_rfl h5 hπ hcen
  have hz : ∀ g, (σ (π g))⁻¹ * g ∈ Subgroup.center X := fun g =>
    hcen (by rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel])
  have hrange : σ.range = ⊤ := by
    rw [eq_top_iff, ← hX, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [show a = σ (π a) * ((σ (π a))⁻¹ * a) by group,
      show b = σ (π b) * ((σ (π b))⁻¹ * b) by group,
      ParabPrime.commutatorElement_mul_central (hz a) (hz b)]
    exact ⟨⁅π a, π b⁆, by rw [map_commutatorElement]⟩
  rw [eq_bot_iff]
  intro z hz'
  obtain ⟨s, rfl⟩ := hrange ▸ Subgroup.mem_top z
  have hs : s = 1 := by rw [← hσ s]; exact (hker _).mpr hz'
  rw [hs, map_one]
  exact Subgroup.one_mem _

theorem nonempty_mulEquiv_specialLinear
    [Finite X] [Finite K] (hX : commutator X = ⊤)
    (h : 3 ∣ Nat.card K - 1) (φ : X ⧸ Subgroup.center X ≃* projectiveSL 3 K)
    (hodd : Odd (Nat.card (Subgroup.center X))) (hz : Subgroup.center X ≠ ⊥) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 3) K ≃* X) := by
  by_cases h4 : Nat.card K = 4
  · have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 2 :=
      ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
        inferInstance, by rw [h4]; norm_num,
        ⟨(φ.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K).symm).trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)⟩⟩
    exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftFour.exists_mulEquiv_specialLinear_four h4
      hX hm φ hodd hz
  · exact CFSG.LocalAnalysis.RankThreeTheoremC.SL3Lift.exists_mulEquiv_specialLinear h h4 hX φ hz

theorem false_of_card_eq_of_three_dvd
    [Finite X] [Finite K] [CharP K 2] (hX : commutator X = ⊤)
    (hK4 : 4 ≤ Nat.card K) (φ : X ⧸ Subgroup.center X ≃* projectiveSL 3 K)
    (hodd : Odd (Nat.card (Subgroup.center X))) (h3 : 3 ∣ Nat.card (Subgroup.center X))
    {E : Subgroup X} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3) : False := by
  have hz : Subgroup.center X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h3
    omega
  by_cases hK3 : 3 ∣ Nat.card K - 1
  · obtain ⟨ψ⟩ := nonempty_mulEquiv_specialLinear hX hK3 φ hodd hz
    have hle := card_le_sq_of_commute (K := K) (P := E.map ψ.symm.toMonoidHom) Nat.prime_three
      (by norm_num) three_ne_zero_of_charTwo
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        change ψ.symm a * ψ.symm b = ψ.symm b * ψ.symm a
        rw [← map_mul, ← map_mul]
        congr 1
        exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
      (by
        rintro _ ⟨a, ha, rfl⟩
        change (ψ.symm a) ^ 3 = 1
        rw [← map_pow, hE.2 a ha, map_one])
    rw [Subgroup.card_map_of_injective ψ.symm.injective, hcard] at hle
    norm_num at hle
  · have h5 : 5 ≤ Nat.card K := by
      by_contra h5
      have : Nat.card K = 4 := by omega
      rw [this] at hK3
      exact hK3 (by norm_num)
    exact hz (center_eq_bot_of_not_dvd hX hK3 h5 φ)

end ToralReduce

end CFSG.AGLEmbedding
