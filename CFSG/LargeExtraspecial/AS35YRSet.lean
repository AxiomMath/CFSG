module

public import CFSG.LargeExtraspecial.AS35YRFrameE
public import CFSG.LargeExtraspecial.AS35YLSIrrA
public import CFSG.LargeExtraspecial.AS35TMain
public import CFSG.LargeExtraspecial.AS35YRFrameY

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.ClassicalGroups.Orthogonal AS35YR

theorem AS35YR.finite_linearEquiv_YR {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_frame_YR (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) :
    ∃ F : Frame S.q, commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.ell ∧
      ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.t := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  set τ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hτ
  have hA : IsTypeA S.q τ 2 := (S.fiveOne_two hS.sixFour hS.weak ht htM).1
  have hO : τ ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := (S.ρ ⟨_, htM⟩).2
  have hne : commSpace τ ≠ ⊥ := by
    intro h
    have := hA.2.2.2.1
    rw [h, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨a, haℓ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : Submodule.span (ZMod 2) {a} < commSpace τ := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr haℓ) fun h => ?_
    have h1 := finrank_span_singleton (K := ZMod 2) ha0
    rw [h, hA.2.2.2.1] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨b, hbℓ, hbn⟩ := IsConcreteLE.exists_of_lt hlt
  have hb0 : b ≠ 0 := fun h => hbn (h ▸ Submodule.zero_mem _)
  have hab : a ≠ b := fun h => hbn (h ▸ Submodule.mem_span_singleton_self a)
  have hspan := AS35YL.span_pair_eq_YL hA.2.2.2.1 haℓ hbℓ ha0 hb0 hab
  obtain ⟨F, rfl, rfl⟩ := exists_frame S.q_nondegenerate (hA.2.2.2.2 _ haℓ) (hA.2.2.2.2 _ hbℓ)
    (polar_commSpace_eq_zero hO hA.2.2.1 haℓ hbℓ) ha0 hb0 hab
  have hℓ : commSpace τ = F.ell := hspan.symm
  exact ⟨F, hℓ, F.eq_t_of_isTypeA S.q_nondegenerate hA hℓ⟩

theorem mem_LbarAsc_of_even_YR (hS : S.SixHyp) (hidx : Nat.card S.LbarAsc * 2 = Nat.card S.O)
    {x : S.O} (hx : Even (finrank (ZMod 2) (commSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt)))) :
    x ∈ S.LbarAsc := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have : Nontrivial S.Qt := by
    rw [← Module.finrank_pos_iff (R := ZMod 2), S.finrank_Qt_eq_two_mul_width]
    have := hS.three_le_width
    omega
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) := finite_linearEquiv_YR
  set Ω : Subgroup S.O := (omegaGroup S.q S.q_nondegenerate).subgroupOf S.O with hΩ
  have hle : S.LbarAsc ≤ Ω := by
    show closure S.DbarAsc ≤ Ω
    rw [closure_le]
    intro d hd
    have hdA := isTypeA_of_mem_DbarAsc_YL hS hd
    rw [SetLike.mem_coe, hΩ, mem_subgroupOf, mem_omegaGroup]
    exact ⟨d.2, by rw [hdA.2.2.2.1]; exact even_two⟩
  have hidxΩ : Ω.index = 2 := relIndex_omegaGroup S.q S.q_nondegenerate
  have hcardΩ : Nat.card Ω * 2 = Nat.card S.O := by
    have := Subgroup.card_mul_index Ω
    rwa [hidxΩ] at this
  have heq : S.LbarAsc = Ω := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    omega
  rw [heq, hΩ, mem_subgroupOf, mem_omegaGroup]
  exact ⟨x.2, hx⟩

variable (S) in
noncomputable abbrev PbarL_YR (g : G) : Subgroup (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  (S.PbarAsc g).map S.O.subtype

theorem card_PbarL_YR (hS : S.SixHyp) {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet)
    (htM : g * S.z * g⁻¹ ∈ S.M) : Nat.card (S.PbarL_YR g) = 2 ^ (2 * S.width - 3) := by
  rw [Subgroup.card_map_of_injective S.O.subtype_injective]
  exact (S14.asc512PbarStmt G S hS g ht htM).2.2.1

theorem conj_mem_PbarL_YR (hS : S.SixHyp) (hidx : Nat.card S.LbarAsc * 2 = Nat.card S.O)
    {g : G} (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (F : Frame S.q)
    (hFt : ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.t) {s : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup S.q)
    (heven : Even (finrank (ZMod 2) (commSpace s))) (hst : s * F.t = F.t * s) :
    ∀ p ∈ S.PbarL_YR g, s * p * s⁻¹ ∈ S.PbarL_YR g := by
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := S14.asc512PbarStmt G S hS g ht htM
  intro p hp
  obtain ⟨x, hx, rfl⟩ := hp
  have hsL : (⟨s, hs⟩ : S.O) ∈ S.LbarAsc := mem_LbarAsc_of_even_YR hS hidx heven
  have hst' : (⟨s, hs⟩ : S.O) * S.ρ ⟨_, htM⟩ = S.ρ ⟨_, htM⟩ * ⟨s, hs⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hFt]
    exact hst
  exact ⟨_, hnorm _ (LbarAsc_le_Mbar_YL hsL) hst' x hx, rfl⟩

theorem radHyp_YR (hS : S.SixHyp) (hidx : Nat.card S.LbarAsc * 2 = Nat.card S.O) {g : G}
    (ht : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) (F : Frame S.q)
    (hFℓ : commSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.ell)
    (hFt : ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = F.t) :
    F.RadHyp (S.PbarL_YR g) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨-, -, -, hcent, -, hcomm, hfix⟩ := S14.asc512PbarStmt G S hS g ht htM
  have hA : IsTypeA S.q ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 :=
    (S.fiveOne_two hS.sixFour hS.weak ht htM).1
  have hconj := fun (s : S.Qt ≃ₗ[ZMod 2] S.Qt) hs heven hst =>
    conj_mem_PbarL_YR (s := s) hS hidx ht htM F hFt hs heven hst
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, hcomm x hx F.a (hFℓ ▸ F.a_mem_ell), hcomm x hx F.b (hFℓ ▸ F.b_mem_ell), ?_⟩
    intro v ha hb
    have hv : v ∈ fixSpace ((S.ρ ⟨_, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate (S.ρ ⟨_, htM⟩).2 hA.2.2.1, hFℓ,
        OrthoF2.mem_orthogonal_iff_polar]
      intro u hu
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
      rw [polar_add_right, polar_smul_right, polar_smul_right, ha, hb]
      simp
    have := hfix x hx v hv
    rwa [hFℓ] at this
  · exact hconj F.s₁ F.s₁_mem (F.even_finrank_commSpace_s₁ S.q_nondegenerate)
      (F.s₁_comm S.q_nondegenerate)
  · exact hconj F.s₂ F.s₂_mem (F.even_finrank_commSpace_s₂ S.q_nondegenerate)
      (F.s₂_comm S.q_nondegenerate)
  · rintro _ ⟨x, hx, rfl⟩ hcen
    have hcen' : ∀ y ∈ S.PbarAsc g, x * y = y * x := by
      intro y hy
      exact Subtype.ext (hcen _ ⟨y, hy, rfl⟩)
    rcases hcent x hx hcen' with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
      exact hFt

end Setting

end CFSG.LargeExtraspecial
