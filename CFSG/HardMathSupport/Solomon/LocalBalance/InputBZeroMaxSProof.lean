module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58Main

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

theorem isKGroup_gLADelta {G : Type} [Group G] [Finite G] {m : ℕ} (hS : GLStanding G m 3)
    {D : Subgroup G} (hDne : D ≠ ⊥) : CFSG.Open.IsKGroup ↥(GLADelta 3 D) := by
  refine CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hS.kProper ?_
  intro hΔ
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDne
  have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
  have hle : GLADelta 3 D ≤ Subgroup.centralizer ({d} : Set G) :=
    (iInf₂_le d hdD).trans ((iInf_le _ hd1').trans (Subgroup.map_subtype_le _))
  rw [hΔ] at hle
  have hcen : d ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
  have hcn : (Subgroup.center G).Normal := inferInstance
  rcases hS.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h] at hcen
    exact hd1' (Subgroup.mem_bot.1 hcen)
  · obtain ⟨a, b, hab⟩ := hS.nonabelian
    apply hab
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem normalizer_commutator_of_normalizes {G : Type} [Group G] {T B : Subgroup G}
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) :
    B ≤ Subgroup.normalizer ((⁅T, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ b ∈ B, ∀ x ∈ (⁅T, B⁆ : Subgroup G), b * x * b⁻¹ ∈ (⁅T, B⁆ : Subgroup G) := by
    intro b hb x hx
    have hle : (⁅T, B⁆ : Subgroup G) ≤ (⁅T, B⁆ : Subgroup G).comap (MulAut.conj b).toMonoidHom := by
      refine Subgroup.commutator_le.2 fun t ht c hc => ?_
      show (MulAut.conj b) ⁅t, c⁆ ∈ (⁅T, B⁆ : Subgroup G)
      have : (MulAut.conj b) ⁅t, c⁆ = ⁅b * t * b⁻¹, b * c * b⁻¹⁆ := by
        simp [MulAut.conj_apply, commutatorElement_def]
        group
      rw [this]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.1 (hBT hb) t).1 ht)
        (B.mul_mem (B.mul_mem hb hc) (B.inv_mem hb))
    exact hle hx
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key b hb x, fun h => ?_⟩
  have := key b⁻¹ (B.inv_mem hb) _ h
  simpa [mul_assoc] using this

theorem inputBZeroMaxS_of_B0T (iB0 : Lemma27Ns.InputB0T) : InputBZeroMaxS := by
  intro G _ _ m hS B hB
  obtain ⟨hBmax, D, hDB, hD, -, hDev⟩ := hB
  have hDev' := hDev rfl
  have hBel : IsElemAbelian 3 B := hBmax.1
  have hDne : D ≠ ⊥ := by
    intro h
    have h1 := hD.2
    rw [h, Subgroup.card_bot] at h1
    have h2 : 1 < 3 ^ 2 := by norm_num
    omega
  have hBΔ : B ≤ Subgroup.normalizer (GLADelta 3 D : Set G) := le_normalizer_gLADelta hBel hDB
  have hcop : Nat.Coprime 3 (Nat.card (GLADelta 3 D)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta Nat.prime_three hDne
  obtain ⟨T, hTΔ, hT2, hBT, hTB⟩ :=
    iB0 G B (GLADelta 3 D) hBel hBΔ hcop (isKGroup_gLADelta hS hDne) hDev'
  have hTle : ⁅T, B⁆ ≤ T := commutator_le_of_normalizes le_rfl hBT
  exact ⟨D, ⟨hDB, hD.1, hD.2⟩, ⁅T, B⁆, hT2.to_le hTle, hTB, hTle.trans hTΔ,
    normalizer_commutator_of_normalizes hBT, commutator_double_of_two_three hBel hT2 hBT⟩

end CFSG.HardMathSupport.Solomon.LocalBalance
