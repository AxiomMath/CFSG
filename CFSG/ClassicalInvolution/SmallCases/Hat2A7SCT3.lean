module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8C261

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
namespace Core

section Pure

variable {G : Type} [Group G] [Finite G]

theorem eq_of_conj_mul_inv_mem_odd {P : Subgroup G} (hP : IsPGroup 2 ↥P) {u v : G} (hu : u ∈ P)
    (hv : v ∈ P) {O : Subgroup G} (hO : Odd (Nat.card ↥O)) (n : G)
    (h : n⁻¹ * (u * v⁻¹) * n ∈ O) : u = v := by
  refine eq_of_mul_inv_mem_odd hP hu hv (N := conjSub n O) ?_ ?_
  · rw [CFSG.ClassicalInvolution.Asc77.natCard_conjSub O n]
    exact hO
  · have := conj_mem_conjSub (n := n) h
    simpa [mul_assoc] using this

end Pure

section Cert

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


structure Core26 (Ω : Set (Subgroup G)) (K J : Subgroup G) (S : Sylow 2 G) (R T : Subgroup G)
    (z t : G) : Prop where
  rset : ∀ P ∈ RSet Ω, P ≤ (S : Subgroup G) → P = R ∨ P = T
  conj : ∀ n : G, (conjSub n K = K ∨ conjSub n J = K) →
    ∃ O : Subgroup G, Odd (Nat.card O) ∧ n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ O
  not_nbr : ∀ M ∈ Ω, 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G)) → M ≠ J → M ∉ omegaNbr Ω K

@[expose] def Core26All (Ω : Set (Subgroup G)) : Prop :=
  ∀ (K J : Subgroup G) (S : Sylow 2 G) (R T W : Subgroup G) (z t : G),
    Std8 Ω K J S R T W z t → Core26 Ω K J S R T z t

theorem eq_or_eq_of_mem_RSet_of_le (hs : Std8 Ω K J S R T W z t) (hC : Core26All Ω)
    {P : Subgroup G} (hP : P ∈ RSet Ω) (hPS : P ≤ (S : Subgroup G)) : P = R ∨ P = T :=
  (hC K J S R T W z t hs).rset P hP hPS

theorem conj_zt_mul_inv_mem_of_conj (hs : Std8 Ω K J S R T W z t) (hC : Core26All Ω) {n : G}
    (hn : conjSub n K = K ∨ conjSub n J = K) :
    ∃ O : Subgroup G, Odd (Nat.card O) ∧ n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ O :=
  (hC K J S R T W z t hs).conj n hn

theorem conj_zt_mul_inv_mem_oddCoreOf (hs : Std8 Ω K J S R T W z t) (hC : Core26All Ω) {y : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    ∃ O : Subgroup G, Odd (Nat.card O) ∧ y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ O := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hyN : y ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz hy
  exact conj_zt_mul_inv_mem_of_conj hs hC (Or.inl (mem_normalizer_iff_conjSub_eq.mp hyN))

theorem not_mem_omegaNbr_of_four_le (hs : Std8 Ω K J S R T W z t) (hC : Core26All Ω)
    {M : Subgroup G} (hM : M ∈ Ω) (h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G))) (hMJ : M ≠ J) :
    M ∉ omegaNbr Ω K :=
  (hC K J S R T W z t hs).not_nbr M hM h4 hMJ

theorem fix_or_swap (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) {s : G}
    (hsS : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s T = T) ∨ (conjSub s R = T ∧ conjSub s T = R) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT := R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hsS' : ∀ P ≤ (S : Subgroup G), conjSub s P ≤ (S : Subgroup G) := by
    intro P hP
    have := conjSub_mono (n := s) hP
    rwa [conjSub_eq_self_of_mem hsS] at this
  have hR' := eq_or_eq_of_mem_RSet_of_le hs hC (RSet.conj hcl hRΩ s) (hsS' R hRS)
  have hT' := eq_or_eq_of_mem_RSet_of_le hs hC (RSet.conj hcl hTΩ s) (hsS' T hTS)
  rcases hR' with hR' | hR'
  · left
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)).symm hRT
    · exact hT'
  · right
    refine ⟨hR', ?_⟩
    rcases hT' with hT' | hT'
    · exact hT'
    · exact absurd ((conjSub_inj s).mp (hT'.trans hR'.symm)) (Ne.symm hRT)

theorem conj_zt_of_mem_sylow (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * (z * t) * s⁻¹ = z * t := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hzt : z * t = t * z := Q3.Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hRsyl : IsSylow2In R K := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  rcases fix_or_swap hs hC hsS with ⟨hR', hT'⟩ | ⟨hR', hT'⟩
  · have hK' : conjSub s K = K := Q3.Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hK hRΩ hRK hR'
    have hJ' : conjSub s J = J := Q3.Q3CL.T8.conjSub_eq_of_conjSub_eq hΩ hJΩ hTΩ hTJ hT'
    have h1 := hs.hz.conj_eq hK'
    have h2 := hs.ht.conj_eq hJ'
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = z * t := by rw [h1, h2]
  · have hK' : conjSub s K = J := hΩ.eq_of_le_of_le (hcl s K hK) hJΩ hTsyl.2.1 (by omega)
      (hR' ▸ conjSub_mono (n := s) hRK) hTJ
    have hJ' : conjSub s J = K := hΩ.eq_of_le_of_le (hcl s J hJΩ) hK hRsyl.2.1 (by omega)
      (hT' ▸ conjSub_mono (n := s) hTJ) hRK
    have h1 : s * z * s⁻¹ = t := (hs.ht.eq (hK' ▸ hs.hz.conj s)).symm
    have h2 : s * t * s⁻¹ = z := (hs.hz.eq (hJ' ▸ hs.ht.conj s)).symm
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = t * z := by rw [h1, h2]
      _ = z * t := hzt.symm

end Cert

end Core
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
namespace Core
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem conj_zt_mul_inv_mem_of_orderFour (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) (hV : ExtraTrans Ω K J S z t)
    {n x : G} (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (n * (z * t) * n⁻¹) = (n * (z * t) * n⁻¹) * x) :
    ∃ O : Subgroup G, Odd (Nat.card O) ∧ n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ O := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hC hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨n', hn'c, hxn'⟩ := exists_conj_sylow_of_centralizes S haS hx2 hxc
  rw [← hn'c]
  have key : ∀ m : G, (conjSub m K = K ∨ conjSub m J = K) →
      m * (z * t) * m⁻¹ = n' * (z * t) * n'⁻¹ →
      ∃ O : Subgroup G, Odd (Nat.card O) ∧ n' * (z * t) * n'⁻¹ * (z * t)⁻¹ ∈ O := fun m hm hmc => by
    rw [← hmc]
    exact conj_zt_mul_inv_mem_of_conj hs hC hm
  set M : Subgroup G := conjSub n'⁻¹ K with hMdef
  have hMΩ : M ∈ Ω := hΩ.conjInvariant n'⁻¹ K hK
  have hKM : conjSub n' M = K := by rw [hMdef, conjSub_conjSub_inv]
  have hx'M : n'⁻¹ * x * n' ∈ M := by
    rw [hMdef, mem_conjSub_iff]
    have e : (n'⁻¹)⁻¹ * (n'⁻¹ * x * n') * n'⁻¹ = x := by group
    rw [e]
    exact hxK
  have hx'S : n'⁻¹ * x * n' ∈ (S : Subgroup G) := (mem_conjSub_iff.mp hxn')
  have hx'o : orderOf (n'⁻¹ * x * n') = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n'⁻¹) x
    rw [MulAut.conj_apply, hx4] at this
    simpa using this
  have h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G)) := by
    have hle : Subgroup.zpowers (n'⁻¹ * x * n') ≤ M ⊓ (S : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hx'M) (Subgroup.zpowers_le.mpr hx'S)
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hx'o] at this
  have hKS : K ⊓ (S : Subgroup G) = R :=
    hRsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hRK hRS)
  have hJS : J ⊓ (S : Subgroup G) = T :=
    hTsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hTJ hTS)
  by_cases hSyl : IsSylow2In (M ⊓ (S : Subgroup G)) M
  · have hMR : M ⊓ (S : Subgroup G) ∈ RSet Ω := mem_RSet_of_isSylow2In hMΩ hSyl
    rcases eq_or_eq_of_mem_RSet_of_le hs hC hMR inf_le_right with h | h
    · have hRM : R ≤ M := h ▸ inf_le_left
      have hMK : M = K :=
        hΩ.eq_of_le_of_le hMΩ hK hRsyl.2.1 (by omega) hRM hRK
      refine key n' (Or.inl ?_) rfl
      have h' := hKM
      rw [hMK] at h'
      exact h'
    · have hTM : T ≤ M := h ▸ inf_le_left
      have hMJ : M = J :=
        hΩ.eq_of_le_of_le hMΩ hJΩ hTsyl.2.1 (by omega) hTM hTJ
      refine key n' (Or.inr ?_) rfl
      have h' := hKM
      rw [hMJ] at h'
      exact h'
  · have hMK : M ≠ K := by
      intro h
      exact hSyl (by rw [h, hKS]; exact hRsyl)
    have hMJ : M ≠ J := by
      intro h
      exact hSyl (by rw [h, hJS]; exact hTsyl)
    obtain ⟨c₁, hc₁, hc₁K⟩ := hV M hMΩ h4 hMK hMJ
    have hc₁a : c₁ * (z * t) * c₁⁻¹ = z * t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc₁
      calc c₁ * (z * t) * c₁⁻¹ = ((z * t) * c₁) * c₁⁻¹ := by rw [this]
        _ = z * t := by group
    refine key (n' * c₁) ?_ ?_
    · rcases hc₁K with h | h
      · left
        rw [conjSub_mul, h, hKM]
      · right
        rw [conjSub_mul, h, hKM]
    · calc n' * c₁ * (z * t) * (n' * c₁)⁻¹ = n' * (c₁ * (z * t) * c₁⁻¹) * n'⁻¹ := by group
        _ = n' * (z * t) * n'⁻¹ := by rw [hc₁a]
end Cert
end Core
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
namespace Core
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_perm (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) {n' : G} {X : Subgroup G}
    (hXR : X ∈ RSet Ω) (hXS : X ≤ conjSub n' (S : Subgroup G)) :
    X = conjSub n' R ∨ X = conjSub n' T := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have h1 : conjSub n'⁻¹ X ∈ RSet Ω := RSet.conj hΩ.conjInvariant hXR n'⁻¹
  have h2 : conjSub n'⁻¹ X ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := n'⁻¹) hXS
    rwa [conjSub_inv_conjSub] at this
  rcases eq_or_eq_of_mem_RSet_of_le hs hC h1 h2 with h | h
  · left
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this
  · right
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this

theorem frame_conj_perm (hs : Std8 Ω K J S R T W z t)
    (hC : Core26All Ω) {n' q : G}
    (hq : q ∈ conjSub n' (S : Subgroup G)) :
    (conjSub q (conjSub n' R) = conjSub n' R ∧ conjSub q (conjSub n' T) = conjSub n' T) ∨
      (conjSub q (conjSub n' R) = conjSub n' T ∧ conjSub q (conjSub n' T) = conjSub n' R) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT : R ≠ T := R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hP : ∀ Y ≤ (S : Subgroup G), conjSub q (conjSub n' Y) ≤ conjSub n' (S : Subgroup G) := by
    intro Y hY
    have := conjSub_mono (n := q) (conjSub_mono (n := n') hY)
    rwa [conjSub_eq_self_of_mem hq] at this
  have hR1 := frame_perm hs hC (RSet.conj hcl (RSet.conj hcl hRΩ n') q) (hP R hRS)
  have hT1 := frame_perm hs hC (RSet.conj hcl (RSet.conj hcl hTΩ n') q) (hP T hTS)
  have hne : conjSub n' R ≠ conjSub n' T := fun h => hRT (conjSub_injective n' h)
  rcases hR1 with hR1 | hR1
  · left
    refine ⟨hR1, ?_⟩
    rcases hT1 with hT1 | hT1
    · exact absurd ((conjSub_injective q) (hT1.trans hR1.symm)) (Ne.symm hne)
    · exact hT1
  · right
    refine ⟨hR1, ?_⟩
    rcases hT1 with hT1 | hT1
    · exact hT1
    · exact absurd ((conjSub_injective q) (hT1.trans hR1.symm)) (Ne.symm hne)
end Cert
end Core
end T8R
end Asc77

end

end CFSG.ClassicalInvolution.Hat2A7S8
