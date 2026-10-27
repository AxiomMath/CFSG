module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FBlocks

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.YP (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {y : G}
    (hy : ∃ g : G, y = g⁻¹ * t * g) (hyP : y ∈ P) (hyA : y ∉ A) :
    ∃ c : Option (Fin 7), y = sec4FD t φ x c := by
  have hyN : y ∈ normalizer (A : Set G) := hT.PM hyP
  rcases h.kcases hy hyN with ⟨p, hp⟩ | ⟨u, v, huv, hσ⟩
  · exact absurd (hp ▸ sec4MPt_mem_A h.data p) hyA
  · obtain ⟨a', c, c', hb⟩ := h.blocks hT u
    obtain ⟨hr, _⟩ := h.block_realizes hT hb
    have hswap : Equiv.swap u v = Equiv.swap u a' :=
      h.swap_overlap hT.P2 hyP (h.d_mem_P hT c) huv hb.1 hσ hr (Or.inl rfl)
    have hσ' : Sec4MRealizes t φ y (Equiv.swap u a') := hswap ▸ hσ
    have hn : ∃ n : ℕ, ((sec4FD t φ x c)⁻¹ * y) ^ (2 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := hT.P2 ⟨(sec4FD t φ x c)⁻¹ * y,
        P.mul_mem (P.inv_mem (h.d_mem_P hT c)) hyP⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    rcases h.fiber_two (h.d_conj c) hy (hT.PM (h.d_mem_P hT c)) hyN hb.1 hr hσ' hn with
      h1 | h1
    · exact ⟨c, h1⟩
    · refine ⟨c', ?_⟩
      rw [h1, h.block_kappa hT hb, ← mul_assoc, h.d_sq c, one_mul]

theorem Sec4FSetup.conjA_unique (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {g : G}
    (hg : CFSG.conjugate A g ≤ P) (hne : CFSG.conjugate A g ≠ A) :
    CFSG.conjugate A g = CFSG.conjugate A x := by
  have hA' : CFSG.conjugate A g =
      Subgroup.closure (Set.range (fun c : Option (Fin 7) => g⁻¹ * sec4MPt t φ c * g)) := by
    have hfun : (fun x : Option (Fin 7) =>
          (MulAut.conj g⁻¹).toMonoidHom (sec4MPt t φ x)) =
        (fun c : Option (Fin 7) => g⁻¹ * sec4MPt t φ c * g) := by
      funext c
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [h.A_eq_closure, CFSG.conjugate, MonoidHom.map_closure, ← Set.range_comp', hfun]
  have hle : CFSG.conjugate A g ≤ CFSG.conjugate A x := by
    rw [hA']
    refine (Subgroup.closure_le _).mpr ?_
    rintro e ⟨c, rfl⟩
    change g⁻¹ * sec4MPt t φ c * g ∈ CFSG.conjugate A x
    have he'A' : g⁻¹ * sec4MPt t φ c * g ∈ CFSG.conjugate A g :=
      (mem_conjugate_iff A g _).mpr (by
        rw [show g * (g⁻¹ * sec4MPt t φ c * g) * g⁻¹ = sec4MPt t φ c by group]
        exact sec4MPt_mem_A h.data c)
    have he'conj : ∃ k : G, g⁻¹ * sec4MPt t φ c * g = k⁻¹ * t * k := by
      obtain ⟨k, hk⟩ := (conj_iff_mem_conjClassIn_top (t := t)).mpr (h.pt_mem_conj c)
      exact ⟨k * g, by rw [hk]; group⟩
    have he'notA : g⁻¹ * sec4MPt t φ c * g ∉ A :=
      h.conjA_disjoint hT.PM hg hne he'A' he'conj
    obtain ⟨c', hc'⟩ := h.YP hT he'conj (hg he'A') he'notA
    rw [hc', mem_conjugate_iff]
    have hx : x * sec4FD t φ x c' * x⁻¹ = sec4MPt t φ c' := by rw [sec4FD]; group
    rw [hx]
    exact sec4MPt_mem_A h.data c'
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcardx : Nat.card (CFSG.conjugate A x) = Nat.card A := by
    simpa only [CFSG.conjugate] using
      (Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj x⁻¹).toMonoidHom)
        (MulAut.conj x⁻¹).injective)
  have hcardg : Nat.card (CFSG.conjugate A g) = Nat.card A := by
    simpa only [CFSG.conjugate] using
      (Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective)
  rw [hcardx, hcardg]

end CFSG.OddStandard.SmallF3.Omega
