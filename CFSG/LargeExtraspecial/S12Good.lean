module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

@[expose] def S12NoNormalTwo {X : Type*} [Group X] (H : Subgroup X) : Prop :=
  ∀ P : Subgroup X, P ≤ H → IsPGroup 2 P → H ≤ normalizer (P : Set X) → P = ⊥

theorem s12_le_normalizer_sup {X : Type*} [Group X] {H P₁ P₂ : Subgroup X}
    (h₁ : H ≤ normalizer (P₁ : Set X)) (h₂ : H ≤ normalizer (P₂ : Set X)) :
    H ≤ normalizer ((P₁ ⊔ P₂ : Subgroup X) : Set X) := by
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
  rw [mem_normalizer_iff_map_conj_eq.mp (h₁ hh), mem_normalizer_iff_map_conj_eq.mp (h₂ hh)]

theorem s12_mem_map_conj_iff {X : Type*} [Group X] {Q : Subgroup X} {k y : X} :
    y ∈ Q.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * y * k ∈ Q := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem S12NoNormalTwo.of_normal {X : Type*} [Group X] [Finite X] {K H : Subgroup X}
    (hK : S12NoNormalTwo K) (hHK : H ≤ K) (hN : K ≤ normalizer (H : Set X)) :
    S12NoNormalTwo H := by
  intro P hPH hP hHP
  set F : Set (Subgroup X) :=
    {Q | Q ≤ H ∧ IsPGroup 2 Q ∧ H ≤ normalizer (Q : Set X)} with hF
  have hPF : P ∈ F := ⟨hPH, hP, hHP⟩
  have hne : F.Nonempty := ⟨P, hPF⟩
  have hdir : DirectedOn (· ≤ ·) F := by
    rintro Q₁ ⟨h1H, h1p, h1N⟩ Q₂ ⟨h2H, h2p, h2N⟩
    refine ⟨Q₁ ⊔ Q₂, ⟨sup_le h1H h2H, ?_, s12_le_normalizer_sup h1N h2N⟩, le_sup_left,
      le_sup_right⟩
    exact IsPGroup.to_sup_of_normal_right' h1p h2p (le_trans h1H h2N)
  set O := sSup F with hO
  have hmemO : ∀ x, x ∈ O ↔ ∃ Q ∈ F, x ∈ Q := fun x => Subgroup.mem_sSup_of_directedOn hne hdir
  have hOH : O ≤ H := sSup_le fun Q hQ => hQ.1
  have hOp : IsPGroup 2 O := by
    intro x
    obtain ⟨Q, hQ, hxQ⟩ := (hmemO x).mp x.2
    obtain ⟨k, hk⟩ := hQ.2.1 ⟨x, hxQ⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hKO : K ≤ normalizer (O : Set X) := by
    intro k hk
    rw [mem_normalizer_iff]
    have hconj : ∀ {k : X}, k ∈ K → ∀ x ∈ O, k * x * k⁻¹ ∈ O := by
      intro k hk x hx
      obtain ⟨Q, ⟨hQH, hQp, hQN⟩, hxQ⟩ := (hmemO x).mp hx
      refine (hmemO _).mpr ⟨Q.map (MulAut.conj k).toMonoidHom, ⟨?_, ?_, ?_⟩, ⟨x, hxQ, rfl⟩⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (hN hk) y).mp (hQH hy)
      · exact hQp.map _
      · intro h hh
        have hk' : k⁻¹ * h * k ∈ H := by
          have := (mem_normalizer_iff.mp (hN (K.inv_mem hk)) h).mp hh
          simpa using this
        rw [mem_normalizer_iff]
        intro y
        rw [s12_mem_map_conj_iff, s12_mem_map_conj_iff]
        have e : k⁻¹ * (h * y * h⁻¹) * k =
            (k⁻¹ * h * k) * (k⁻¹ * y * k) * (k⁻¹ * h * k)⁻¹ := by group
        rw [e]
        exact mem_normalizer_iff.mp (hQN hk') _
    intro x
    constructor
    · exact hconj hk x
    · intro hx
      have := hconj (K.inv_mem hk) _ hx
      simpa [mul_assoc] using this
  have hO1 : O = ⊥ := hK O (hOH.trans hHK) hOp (hKO)
  have hPO : P ≤ O := le_sSup hPF
  rw [hO1] at hPO
  exact le_bot_iff.mp hPO

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem s12_noNormalTwo_Mbar : S12NoNormalTwo S.Mbar := by
  intro P hPM hP hMP
  have hnorm : (P.subgroupOf S.Mbar).Normal := by
    refine ⟨fun x hx m => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (hMP m.2) x).mp hx
  have hp : IsPGroup 2 (P.subgroupOf S.Mbar) := by
    intro x
    obtain ⟨k, hk⟩ := hP ⟨((x : S.Mbar) : S.O), mem_subgroupOf.mp x.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have hle : P.subgroupOf S.Mbar ≤ CFSG.pCore 2 S.Mbar := le_sSup ⟨hnorm, hp⟩
  rw [S.pCore_Mbar_eq_bot, le_bot_iff, subgroupOf_eq_bot] at hle
  exact disjoint_self.mp (hle.mono_right hPM)

end Setting

end CFSG.LargeExtraspecial
