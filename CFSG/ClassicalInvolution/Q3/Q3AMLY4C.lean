module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY4B

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3AM (nbrLayer exactCore3_le_nbrLayer nbrLayer_le_centralizer
  conj_mem_nbrLayer conj_mem_oddCoreOf_of_mem_self)
open scoped commutatorElement

section Frame


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_perm (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {n' : G} {X : Subgroup G}
    (hXR : X ∈ RSet Ω) (hXS : X ≤ conjSub n' (S : Subgroup G)) :
    X = conjSub n' R ∨ X = conjSub n' T := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have h1 : conjSub n'⁻¹ X ∈ RSet Ω := RSet.conj hΩ.conjInvariant hXR n'⁻¹
  have h2 : conjSub n'⁻¹ X ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := n'⁻¹) hXS
    rwa [conjSub_inv_conjSub] at this
  rcases eq_or_eq_of_mem_RSet_of_le hs hY h1 h2 with h | h
  · left
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this
  · right
    have := congrArg (conjSub n') h
    rwa [conjSub_conjSub_inv] at this

theorem frame_conj_perm (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {n' q : G}
    (hq : q ∈ conjSub n' (S : Subgroup G)) :
    (conjSub q (conjSub n' R) = conjSub n' R ∧ conjSub q (conjSub n' T) = conjSub n' T) ∨
      (conjSub q (conjSub n' R) = conjSub n' T ∧ conjSub q (conjSub n' T) = conjSub n' R) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hRT : R ≠ T := T8R.R_ne_T hs
  have hcl := hΩ.conjInvariant
  have hP : ∀ Y ≤ (S : Subgroup G), conjSub q (conjSub n' Y) ≤ conjSub n' (S : Subgroup G) := by
    intro Y hY
    have := conjSub_mono (n := q) (conjSub_mono (n := n') hY)
    rwa [conjSub_eq_self_of_mem hq] at this
  have hR1 := frame_perm hs hY (RSet.conj hcl (RSet.conj hcl hRΩ n') q) (hP R hRS)
  have hT1 := frame_perm hs hY (RSet.conj hcl (RSet.conj hcl hTΩ n') q) (hP T hTS)
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

theorem conj_zt_mul_inv_mem_of_conj (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z)) {n : G}
    (hn : conjSub n K = K ∨ conjSub n J = K) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  rcases hn with hn | hn
  · refine conj_zt_mul_inv_mem_oddCoreOf hs hY ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hs.hz.conj_eq hn
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [h1]
  · have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
    have hNΩ : conjSub n K ∈ Ω := hΩ.conjInvariant n K hK
    have hKN : K ∈ omegaNbr Ω (conjSub n K) := by
      have := omegaNbr_conj hΩ.conjInvariant hs.hJ n
      rwa [hn] at this
    have hN : conjSub n K ∈ omegaNbr Ω K :=
      Q3CL.T3.omegaNbr_symm (l6_2) hΩ hNΩ hK hKN
    have hy : IsUniqueInvolution (conjSub n K) (n * z * n⁻¹) := hs.hz.conj n
    have h1 := mul_inv_mem_oddCoreOf_nbr hs hY hN hy
    have hnt : n * t * n⁻¹ = z := by
      have := hs.ht.conj n
      rw [hn] at this
      exact (hs.hz.eq this).symm
    have e : n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * t⁻¹ := by
      calc n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) * (z * t)⁻¹ := by group
        _ = (n * z * n⁻¹) * z * (t⁻¹ * z⁻¹) := by rw [hnt]; group
        _ = (n * z * n⁻¹) * (z * t⁻¹ * z⁻¹) := by group
        _ = (n * z * n⁻¹) * t⁻¹ := by
          have : z * t⁻¹ * z⁻¹ = t⁻¹ := by
            have h2 : z * t⁻¹ = t⁻¹ * z := by
              have h3 : t * z = z * t := hzt.symm
              calc z * t⁻¹ = t⁻¹ * (t * z) * t⁻¹ := by group
                _ = t⁻¹ * (z * t) * t⁻¹ := by rw [h3]
                _ = t⁻¹ * z := by group
            rw [h2]; group
          rw [this]
    rw [e]
    exact h1

theorem conj_zt_mul_inv_mem_of_orderFour (hs : Std8 Ω K J S R T W z t)
    (hY : nbrLayer Ω K z = exactCore3 z J ⊔ oddCoreOf (nbrLayer Ω K z))
      (hV : T8R.ExtraTrans Ω K J S z t)
    {n x : G} (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (n * (z * t) * n⁻¹) = (n * (z * t) * n⁻¹) * x) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hTΩ
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hY hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨n', hn'c, hxn'⟩ := T8R.exists_conj_sylow_of_centralizes S haS hx2 hxc
  rw [← hn'c]
  have key : ∀ m : G, (conjSub m K = K ∨ conjSub m J = K) →
      m * (z * t) * m⁻¹ = n' * (z * t) * n'⁻¹ →
      n' * (z * t) * n'⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (nbrLayer Ω K z) := fun m hm hmc => by
    rw [← hmc]
    exact conj_zt_mul_inv_mem_of_conj hs hY hm
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
    rcases eq_or_eq_of_mem_RSet_of_le hs hY hMR inf_le_right with h | h
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

end Frame

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.LY4
