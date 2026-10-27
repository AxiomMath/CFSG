module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3T
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3D
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM3F
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1C2
public import CFSG.ClassicalInvolution.Q3.TL4Mdl264OB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3

open CFSG.Blueprint CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.TL4.OrthQ8 QuadraticMap
open scoped MatrixGroups

theorem false_of_sfHyp_induced {K V S : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group S] {Q : QuadraticForm K V} (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {A B : Subgroup S} {r : S} {x : MulAut S} (h : SFHyp A B r x) {g : V ≃ₗ[K] V}
    (hx : InducedBy θ g x) {μ c : K} (hμ : ∀ v, Q (g v) = μ * Q v) (hc : ∀ v, g (g v) = c • v) :
    False := by
  obtain ⟨F, hAF, -⟩ := exists_frame_of_quatTwinDatum hK hQ hn θ hθ hker h.quat
  subst hAF
  have h2 := two_ne_zero' hK
  have hneg1 := neg_one_mem_commutator (K := K) hK
  have hFg := commute_La_of_fix hK hQ (by omega) hker hx h.fixA
  obtain ⟨q, hq, rfl⟩ := h.twin
  rcases twin_cases hK hQ hn θ hθ hker h.quat rfl hq h.ne with hswap | ⟨F', hF', hneg⟩
  ·
    obtain ⟨w, hw, hw4, hxw⟩ := h.onB
    rw [hswap] at hw hxw
    obtain ⟨w₀, -, hw₀, hconj⟩ := exists_w₀_of_member hK hQ (by omega) hker hx
      (by rw [Frame.La_swap_neg_one]; exact hFg (-1) hneg1) hw hw4 hxw
    obtain ⟨hμ1, hc1⟩ := mu_eq_one_of_swap hK F hFg hw₀ hconj hμ hc
    have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by rw [hμ, hμ1, one_mul]
    have hg2 : ∀ v, g (g v) = -v := fun v => by rw [hc, hc1, neg_one_smul]
    rcases Nat.even_or_odd (Module.finrank K V) with heven | hodd
    · have hn8 : 8 ≤ Module.finrank K V := by
        obtain ⟨k, hk⟩ := heven
        omega
      obtain ⟨G, hGspan, hGcomm⟩ := exists_frame_commute_swap hK hQ hn8 hgO hg2
        fun v hv => Frame.map_mem_perp h2 (hFg (-1) hneg1) hv
      exact false_of_fixed_frame_perp hK hQ hn hker hx
        (G := G.swap) (by rw [← Frame.span_eq_swap_span]; exact hGspan)
        (fun b _ => hGcomm b) h.noNbr
    · exact false_of_odd_finrank hK hg2 hodd
  ·
    obtain ⟨w, hw, hw4, hxw⟩ := h.onB
    rw [hF'] at hw hxw
    obtain ⟨w₀, -, hw₀, hconj⟩ := exists_w₀_of_member hK hQ (by omega) hker hx
      (commute_La_neg_one_of_neg hneg (hFg (-1) hneg1)) hw hw4 hxw
    exact false_of_neg_frame hK hQ hn hker hx hneg hFg hw₀ hconj hμ hc h.noNbr

theorem false_of_sfHyp_orth {K V S : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group S] {Q : QuadraticForm K V} (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q))
    {A B : Subgroup S} {r : S} {x : MulAut S} (h : SFHyp A B r x) : False := by
  obtain ⟨β, g, μ, -, hμ, hg, ⟨c, hc⟩, hact⟩ :=
    exists_similarity_of_involutive hK hQ hn θ hθ hker x h.sq
  exact false_of_sfHyp_induced hK hQ hn hθ hker (h.map β) ⟨hg, hact⟩ hμ hc

theorem sigmaFixOm3_of_orthModel {K V S : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Group S] {Q : QuadraticForm K V} (hK : Nat.card K = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hn : 7 ≤ Module.finrank K V)
    {θ : ↥(orthDerived Q) →* S} (hθ : Function.Surjective θ)
    (hker : θ.ker = (scalars K V).subgroupOf (orthDerived Q)) : SigmaFixOm3 S :=
  sigmaFixOm3_of_forall_false fun _ _ _ _ h => false_of_sfHyp_orth hK hQ hn hθ hker h

theorem sigmaFixOm3_orthBad3 {S : Type} [Group S] {t : Assembly.LowTwoRank.StatedLieTag}
    {n : ℕ} (ht : OrthBad3 t n) (hS : LieModel S t n 3 1) : SigmaFixOm3 S := by
  obtain ⟨K, _, _, d, Q, θ, hK, hQ, hd, hθ, hker⟩ := O264.exists_orthModel ht hS
  exact sigmaFixOm3_of_orthModel (V := Fin d → K) hK hQ (by rwa [Module.finrank_fin_fun]) hθ hker

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.OM3
