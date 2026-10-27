module

public import CFSG.ClassicalInvolution.Asc77.AscT7DRSyl
public import CFSG.ClassicalInvolution.Asc77.AscT7CHyp
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Asc77.T7C2

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C25_20_coord : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ →
      Nat.card ↥(S : Subgroup G) = 4 * Nat.card ↥(R ⊔ R') →
        ∃ a b s t' : G, a ∈ R ∧ b ∈ R ∧ Subgroup.closure ({a, b} : Set G) = R ∧
          b * a * b⁻¹ = a⁻¹ ∧ (∃ k : ℤ, b * b = a ^ k) ∧ s ∈ (S : Subgroup G) ∧
          t' ∈ (S : Subgroup G) ∧ (∃ g : G, g * z * g⁻¹ = t') ∧ conjSub t' R = R' ∧
          Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G) ∧ s * s = 1 ∧
          s * t' = t' * s ∧ s * a * s⁻¹ = a⁻¹ ∧ s * b * s⁻¹ = b * a

namespace T7DR

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem sq_mul_sq_eq_one {a b : G} {k : ℤ} (hbab : b * a * b⁻¹ = a⁻¹) (hk : b * b = a ^ k) :
    (b * b) * (b * b) = 1 := by
  have h1 : b * (b * b) * b⁻¹ = b * b := by group
  have h2 : b * (b * b) * b⁻¹ = (b * b)⁻¹ := by
    rw [hk, ← conj_zpow, hbab, inv_zpow]
  exact eq_inv_iff_mul_eq_one.mp (h1.symm.trans h2)

theorem tf4_of_index_four [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ a b s t' : G}
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) (haR : a ∈ R) (hbR : b ∈ R)
    (hbab : b * a * b⁻¹ = a⁻¹) (hk : ∃ k : ℤ, b * b = a ^ k) (hs : s ∈ (S : Subgroup G))
    (ht' : t' ∈ (S : Subgroup G)) (hg : ∃ g : G, g * z * g⁻¹ = t') (hconj : conjSub t' R = R')
    (hSgen : Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G)) (hs2 : s * s = 1)
    (hst : s * t' = t' * s) (hsa : s * a * s⁻¹ = a⁻¹) (hsb : s * b * s⁻¹ = b * a) :
    TwoSubgroupsFourGenerated G := by
  have hsetting : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst0 : AscStand p f Ω K := hsetting.stand
  have hp : p ≠ 2 := hst0.odd
  have hΩ : HypOmegaMod p f Ω := hst0.hyp
  have hK : K ∈ Ω := hst0.mem
  have hK' : K' ∈ Ω := hsetting.hK'.1
  have hKK' : K' ≠ K := hsetting.hne
  have hz : IsUniqueInvolution K z := hsetting.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hsetting.hK'
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hyp.hR.1 hyp.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hyp.hR'.1 hyp.hR'.2.1
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hR'S : R' ≤ (S : Subgroup G) := hyp.hR'.2.2
  have hc : Commutes R R' := hΩ.commutes_of_twin_of_isPGroup hK hK' hKK'.symm hz hz' hRsyl.1
    hR'syl.1 (S.isPGroup'.to_le (sup_le hRS hR'S))
  obtain ⟨g, hg'⟩ := hg
  have ht2 : t' * t' = 1 := by
    rw [← hg']
    calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have ha'R' : t' * a * t'⁻¹ ∈ R' := by
    rw [← hconj]
    exact conj_mem_conjSub haR
  have hb'R' : t' * b * t'⁻¹ ∈ R' := by
    rw [← hconj]
    exact conj_mem_conjSub hbR
  obtain ⟨k, hk'⟩ := hk
  have hbb : (b * b) * (b * b) = 1 := sq_mul_sq_eq_one hbab hk'
  have hbbK : b * b ∈ K := hRsyl.1 (R.mul_mem hbR hbR)
  have h6 : t' * (b * b) * t'⁻¹ = b * b := by
    rcases hz.unique (b * b) hbbK hbb with h | h
    · rw [h]
      group
    · rw [h]
      have := hyp.hzS t' ht'
      calc t' * z * t'⁻¹ = z * t' * t'⁻¹ := by rw [this]
        _ = z := by group
  have haT : a ∈ (S : Subgroup G) := hRS haR
  have hbT : b ∈ (S : Subgroup G) := hRS hbR
  refine twoSubgroupsFourGenerated_of_sylow S fun H hH => ?_
  exact genLE_four_of_omega6_sub haT hbT hs ht' hSgen hbab ⟨k, hk'⟩ ht2 hs2
    hst hsa hsb (hc a haR _ ha'R') (hc a haR _ hb'R') (hc b hbR _ ha'R') (hc b hbR _ hb'R') h6 hH

end T7DR

theorem c25_21_of_sylow_coord (h20 : C25_20_coord p f) : C25_21 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp h4
  obtain ⟨a, b, s, t', haR, hbR, -, hbab, hk, hs, ht', hg, hconj, hSgen, hs2, hst, hsa, hsb⟩ :=
    h20 G Ω K K' W S R R' z t u₁ u₂ hyp h4
  exact Or.inr (T7DR.tf4_of_index_four hyp haR hbR hbab hk hs ht' hg hconj hSgen hs2 hst hsa hsb)

end CFSG.ClassicalInvolution.Asc77
