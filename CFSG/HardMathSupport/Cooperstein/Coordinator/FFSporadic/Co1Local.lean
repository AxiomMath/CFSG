module

public import CFSG.LargeExtraspecial.S45QOmegaMinus
public import CFSG.LargeExtraspecial.O62Normalizer
public import CFSG.LargeExtraspecial.S12DWSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

section Irreducible

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem eq_top_of_omega_invariant (hQ : Q.polarBilin.Nondegenerate)
    (h8 : finrank (ZMod 2) V = 8) (D : Submodule (ZMod 2) V)
    (hD : ∀ g ∈ omegaGroup Q hQ, ∀ v ∈ D, g v ∈ D) (hne : D ≠ ⊥) : D = ⊤ := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  by_contra hDtop
  obtain ⟨v, hvD, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u, huD⟩ : ∃ u, u ∉ D := by
    by_contra h
    push Not at h
    exact hDtop (eq_top_iff.2 fun x _ => h x)
  have hu0 : u ≠ 0 := fun h => huD (h ▸ D.zero_mem)
  have htrans : ∀ x ∈ D, x ≠ 0 → ∀ y : V, y ≠ 0 → Q y = Q x → y ∈ D := by
    intro x hx hx0 y hy0 hyx
    obtain ⟨g, hg, hgx⟩ := CFSG.LargeExtraspecial.O62.exists_mem_omegaGroup_apply_eq hQ
      (by omega) hx0 hy0 hyx.symm
    rw [← hgx]
    exact hD g hg x hx
  have hcard : Nat.card V = 4 ^ 4 := CFSG.LargeExtraspecial.S12DW.natCard_eq_four_pow (by omega)
  have hcount := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic Q
    (CFSG.LargeExtraspecial.S12DW.polar_eq_zero_imp hQ) hcard
  have hN0 := CFSG.LargeExtraspecial.S12DW.ncard_eq_zero_eq Q
  rw [hcard] at hN0
  norm_num at hcount hN0
  have hDdvd : Nat.card D ∣ 2 ^ 8 := by
    have h1 : Nat.card D ∣ Nat.card V := by
      have := AddSubgroup.card_addSubgroup_dvd_card D.toAddSubgroup
      exact this
    rwa [hcard, show (4 : ℕ) ^ 4 = 2 ^ 8 by norm_num] at h1
  obtain ⟨k, hk8, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hDdvd
  have hDset : (D : Set V).ncard = Nat.card D := (Nat.card_coe_set_eq (D : Set V)).symm
  have hQ01 : ∀ x : V, Q x = 0 ∨ Q x = 1 := fun x => by
    have : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    exact this _
  have hQ0 : Q 0 = 0 := QuadraticMap.map_zero Q
  rcases hQ01 v with hQv | hQv <;> rcases hQ01 u with hQu | hQu
  · exact huD (htrans v hvD hv0 u hu0 (by rw [hQu, hQv]))
  ·
    have hD0 : (D : Set V) = {x | Q x = 0} := by
      ext x
      constructor
      · intro hx
        by_contra hx'
        have hx1 : Q x = 1 := by
          rcases hQ01 x with h | h
          · exact absurd h hx'
          · exact h
        have hx0 : x ≠ 0 := fun h => hx' (h ▸ hQ0)
        exact huD (htrans x hx hx0 u hu0 (by rw [hQu, hx1]))
      · intro hx
        by_cases hx0 : x = 0
        · rw [hx0]; exact D.zero_mem
        · exact htrans v hvD hv0 x hx0 (by rw [hx, hQv])
    rw [hD0] at hDset
    rw [hN0, hk] at hDset
    have hk' : k ≤ 8 := hk8
    interval_cases k <;> omega
  ·
    have hD1 : (D : Set V) = insert 0 {x | Q x = 1} := by
      ext x
      constructor
      · intro hx
        by_cases hx0 : x = 0
        · exact Or.inl hx0
        · refine Or.inr ?_
          rcases hQ01 x with h | h
          · exact absurd (htrans x hx hx0 u hu0 (by rw [hQu, h])) huD
          · exact h
      · rintro (rfl | hx)
        · exact D.zero_mem
        · exact htrans v hvD hv0 x (fun h => by
          have h1 : Q x = 1 := hx
          rw [h, hQ0] at h1
          exact absurd h1 (by decide))
            (by rw [hx, hQv])
    rw [hD1, Set.ncard_insert_of_notMem (by simp [hQ0])] at hDset
    rw [hk] at hDset
    have hk' : k ≤ 8 := hk8
    interval_cases k <;> omega
  · exact huD (htrans v hvD hv0 u hu0 (by rw [hQu, hQv]))

end Irreducible

section Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem le_QG_or_eq_M (hΩ : S.Mbar.map S.O.subtype = CFSG.Open.timmesfeldOmega S.q)
    (h8 : finrank (ZMod 2) S.Qt = 8) {N : Subgroup G} (hNM : N ≤ S.M)
    (hnorm : ∀ c ∈ S.M, ∀ n ∈ N, c * n * c⁻¹ ∈ N) : N ≤ S.QG ∨ N = S.M := by
  have hΩ' : S.Mbar.map S.O.subtype = omegaGroup S.q S.q_nondegenerate := by
    rw [hΩ, CFSG.LargeExtraspecial.s12_timmesfeldOmega_eq S.q S.q_nondegenerate]
  have hsimpΩ : IsSimpleGroup (omegaGroup S.q S.q_nondegenerate) :=
    CFSG.LargeExtraspecial.S45Q.isSimpleGroup_omegaGroup_of_six_le S.q_nondegenerate (by omega)
  let eΩ : S.Mbar ≃* omegaGroup S.q S.q_nondegenerate :=
    (S.Mbar.equivMapOfInjective S.O.subtype S.O.subtype_injective).trans
      (MulEquiv.subgroupCongr hΩ')
  have : IsSimpleGroup (omegaGroup S.q S.q_nondegenerate) := hsimpΩ
  have : IsSimpleGroup S.Mbar := eΩ.isSimpleGroup
  let ρ' : S.M →* S.Mbar := S.ρ.rangeRestrict
  have hρ's : Function.Surjective ρ' := S.ρ.rangeRestrict_surjective
  have hρ' : ∀ m : S.M, ((ρ' m : S.Mbar) : S.O) = S.ρ m := fun _ => rfl
  have hker : ∀ m : S.M, ρ' m = 1 ↔ (m : G) ∈ S.QG := fun m => by
    rw [← S.ρ_eq_one_iff]
    constructor
    · intro h
      exact congrArg (fun x : S.Mbar => (x : S.O)) h
    · intro h
      exact Subtype.ext h
  set Nm : Subgroup S.M := N.subgroupOf S.M with hNm
  have hNmn : Nm.Normal := ⟨fun n hn c => hnorm c c.2 n hn⟩
  have hRn : (Nm.map ρ').Normal := hNmn.map ρ' hρ's
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Nm.map ρ') with hR | hR
  · left
    intro x hx
    have hxM : x ∈ S.M := hNM hx
    have : ρ' ⟨x, hxM⟩ ∈ Nm.map ρ' := ⟨⟨x, hxM⟩, hx, rfl⟩
    rw [hR, Subgroup.mem_bot] at this
    exact (hker ⟨x, hxM⟩).1 this
  · right
    set N0 : Subgroup G := N ⊓ S.QG with hN0
    set W : Submodule (ZMod 2) S.Qt := S.clSub N0 with hW
    have hsurj : ∀ m : S.M, ∃ n : S.M, (n : G) ∈ N ∧ ρ' n = ρ' m := by
      intro m
      have : ρ' m ∈ Nm.map ρ' := by rw [hR]; trivial
      obtain ⟨n, hn, hnm⟩ := this
      exact ⟨n, hn, hnm⟩
    have hWinv : ∀ g ∈ omegaGroup S.q S.q_nondegenerate, ∀ v ∈ W,
        ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt → S.Qt) v ∈ W := by
      intro g hg v hv
      rw [← hΩ'] at hg
      obtain ⟨γ, hγ, rfl⟩ := hg
      obtain ⟨m, rfl⟩ := hγ
      obtain ⟨x, hxN, hxQ, rfl⟩ := S.mem_clSub_iff.1 hv
      change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) ∈ W
      rw [S.ρ_cl m hxQ]
      exact S.cl_mem_clSub ⟨hnorm m m.2 x hxN.1, S.conj_mem_QG m.2 hxQ⟩ (S.conj_mem_QG m.2 hxQ)
    have hnormQ : ∀ x ∈ S.QG, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn =>
      hnorm x (S.QG_le_M hx) n hn
    have hcomm : ∀ n ∈ N, ∀ x ∈ S.QG, (n * x * n⁻¹ * x⁻¹) ∈ N0 := by
      intro n hn x hx
      refine ⟨?_, ?_⟩
      · have h1 : x * n⁻¹ * x⁻¹ ∈ N := hnormQ x hx n⁻¹ (N.inv_mem hn)
        have := N.mul_mem hn h1
        simpa [mul_assoc] using this
      · exact S.QG.mul_mem (S.conj_mem_QG (hNM hn) hx) (S.QG.inv_mem hx)
    have hWtop : W = ⊤ := by
      by_contra hWne
      have hWbot : W = ⊥ := by
        by_contra hb
        exact hWne (eq_top_of_omega_invariant S.q_nondegenerate h8 W hWinv hb)
      have hN1 : ∀ n : S.M, (n : G) ∈ N → ρ' n = 1 := by
        intro n hn
        have hρn : S.ρ n = 1 := by
          refine Subtype.ext (LinearEquiv.ext fun v => ?_)
          obtain ⟨x, hx, rfl⟩ := S.exists_cl v
          rw [S.ρ_cl n hx]
          have hc := hcomm n hn x hx
          have hcl0 : S.cl ((n : G) * x * (n : G)⁻¹ * x⁻¹) = 0 := by
            have := S.cl_mem_clSub hc (S.QG.mul_mem (S.conj_mem_QG n.2 hx) (S.QG.inv_mem hx))
            rw [hW] at hWbot
            rw [hWbot] at this
            exact (Submodule.mem_bot _).1 this
          have h2 := S.cl_mul (S.QG.mul_mem (S.conj_mem_QG n.2 hx) (S.QG.inv_mem hx)) hx
          rw [show (n : G) * x * (n : G)⁻¹ * x⁻¹ * x = (n : G) * x * (n : G)⁻¹ by group] at h2
          rw [h2, hcl0, zero_add]
          rfl
        exact Subtype.ext hρn
      obtain ⟨g, hg⟩ := exists_ne (1 : S.Mbar)
      have hgm : g ∈ Nm.map ρ' := by rw [hR]; trivial
      obtain ⟨n, hn, rfl⟩ := hgm
      exact hg (hN1 n hn)
    have hzN0 : S.z ∈ N0 := by
      obtain ⟨v, hv⟩ : ∃ v : S.Qt, v ≠ 0 := by
        have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
        exact exists_ne 0
      obtain ⟨w, hw⟩ : ∃ w, S.q.polarBilin v w ≠ 0 := by
        by_contra! hall
        exact hv (S.q_nondegenerate.1 _ hall)
      have hv' : v ∈ W := by rw [hWtop]; trivial
      have hw' : w ∈ W := by rw [hWtop]; trivial
      obtain ⟨x, hxN, hxQ, rfl⟩ := S.mem_clSub_iff.1 hv'
      obtain ⟨y, hyN, hyQ, rfl⟩ := S.mem_clSub_iff.1 hw'
      rw [polarBilin_apply_apply, Ne, S.polar_cl_eq_zero_iff hxQ hyQ] at hw
      have hcm : x * y * x⁻¹ * y⁻¹ = S.z := by
        rcases S.commutator_eq_one_or_z hxQ hyQ with h | h
        · exact absurd (by
            calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
              _ = y * x := by rw [h, one_mul]) hw
        · exact h
      rw [← hcm]
      exact N0.mul_mem (N0.mul_mem (N0.mul_mem hxN hyN) (N0.inv_mem hxN)) (N0.inv_mem hyN)
    have hQN : S.QG ≤ N := by
      intro q hq
      have : S.cl q ∈ W := by rw [hWtop]; trivial
      obtain ⟨x, hxN, hxQ, hxq⟩ := S.mem_clSub_iff.1 this
      rcases (S.cl_eq_cl_iff hxQ hq).1 hxq with h | h
      · rw [h]; exact hxN.1
      · rw [h]; exact N.mul_mem hxN.1 hzN0.1
    refine le_antisymm hNM fun m hm => ?_
    obtain ⟨n, hnN, hnm⟩ := hsurj ⟨m, hm⟩
    have h1 : ρ' (n⁻¹ * ⟨m, hm⟩) = 1 := by rw [map_mul, map_inv, hnm, inv_mul_cancel]
    have h2 : ((n⁻¹ * ⟨m, hm⟩ : S.M) : G) ∈ S.QG := (hker _).1 h1
    have h3 : ((n⁻¹ * ⟨m, hm⟩ : S.M) : G) ∈ N := hQN h2
    have : m = (n : G) * ((n⁻¹ * ⟨m, hm⟩ : S.M) : G) := by
      simp
    rw [this]
    exact N.mul_mem hnN h3

end Setting

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
