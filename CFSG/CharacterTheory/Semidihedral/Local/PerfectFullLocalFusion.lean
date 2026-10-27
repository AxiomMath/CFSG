module

public import CFSG.CharacterTheory.Semidihedral.Local.PerfectFullLocalFusionSupport

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

universe u

theorem klein_four_normalizer_conj_transitive {G : Type u} [Group G] [Finite G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S)
    (V : Subgroup G) (hVS : V ≤ S) (hV : IsKleinFour V) {v w : G} (hv : v ∈ V) (hw : w ∈ V)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) :
    ∃ g ∈ Subgroup.normalizer (V : Set G), g * v * g⁻¹ = w := by
  classical
  obtain ⟨⟨e, he⟩, -, -, -⟩ := kleinFour_automorphism_action (V := V)
  let v' : {x : V // x ≠ 1} := ⟨⟨v, hv⟩, fun h => hv1 (congrArg Subtype.val h)⟩
  let w' : {x : V // x ≠ 1} := ⟨⟨w, hw⟩, fun h => hw1 (congrArg Subtype.val h)⟩
  have hφ : e.symm (Equiv.swap v' w') ⟨v, hv⟩ = ⟨w, hw⟩ := by
    have h := he (e.symm (Equiv.swap v' w')) v'
    rw [MulEquiv.apply_symm_apply, Equiv.swap_apply_left] at h
    exact h.symm
  have hrange := kleinFour_normalizer_image_eq_top hn S f V hVS hV
  obtain ⟨y, hy⟩ : e.symm (Equiv.swap v' w') ∈ V.normalizerMonoidHom.range := by
    rw [hrange]
    trivial
  refine ⟨y, y.2, ?_⟩
  have h := congrArg (fun ψ : MulAut V => ((ψ ⟨v, hv⟩ : V) : G)) hy
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  rw [h, hφ]

theorem perfect_semidihedral_full_local_fusion {G : Type u} [Group G] [Finite G]
    [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    (∀ V : Subgroup G, V ≤ S → IsKleinFour V →
      V.normalizerMonoidHom.range = ⊤ ∧ Nat.card V.normalizerMonoidHom.range = 6) ∧
    (∀ Q : Subgroup G, Q ≤ S → Nonempty (Q ≃* QuaternionGroup 2) →
      Q.normalizerMonoidHom.range = ⊤ ∧ Nat.card Q.normalizerMonoidHom.range = 24) ∧
    (∀ P : Subgroup G, P ≤ S → ∀ g : G, P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S →
      ∃ k : ℕ, ∃ c : SemidihedralFullFusionChain (S : Subgroup G) k,
        c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = P.map (MulAut.conj g⁻¹).toMonoidHom ∧
        ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g) ∧
    (∀ (k : ℕ) (c : SemidihedralFullFusionChain (S : Subgroup G) k), ∃ g : G,
      c.subgroups (Fin.last k) = (c.subgroups 0).map (MulAut.conj g⁻¹).toMonoidHom ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g) ∧
    (∀ V : Subgroup G, V ≤ S → IsKleinFour V →
      Nat.card (Subgroup.normalizer (V : Set G) ⧸
        CFSG.oddCore (Subgroup.normalizer (V : Set G))) = 24) ∧
    (∀ Q : Subgroup G, Q ≤ S → Nonempty (Q ≃* QuaternionGroup 2) →
      Nat.card (Subgroup.normalizer (Q : Set G) ⧸
        CFSG.oddCore (Subgroup.normalizer (Q : Set G))) = 48 ∧
      ∃ P : Sylow 2 (Subgroup.normalizer (Q : Set G)), Nat.card P = 16 ∧
        (n = 4 → Nonempty (P ≃* SemidihedralGroup 4)) ∧
        (5 ≤ n → Nonempty (P ≃* QuaternionGroup 4))) := by
  have hK6 : ∀ V : Subgroup G, V ≤ S → IsKleinFour V →
      V.normalizerMonoidHom.range = ⊤ ∧ Nat.card V.normalizerMonoidHom.range = 6 := by
    intro V hVS hV
    have h := kleinFour_normalizer_image_eq_top hn S f V hVS hV
    refine ⟨h, ?_⟩
    rw [h, Subgroup.card_top, (kleinFour_automorphism_action (V := V)).2.1]
  have hQ24 : ∀ Q : Subgroup G, Q ≤ S → Nonempty (Q ≃* QuaternionGroup 2) →
      Q.normalizerMonoidHom.range = ⊤ ∧ Nat.card Q.normalizerMonoidHom.range = 24 := by
    intro Q hQS hQ
    have h := quaternionEight_normalizer_image_eq_top hn S f Q hQS hQ
    refine ⟨h, ?_⟩
    rw [h, Subgroup.card_top, (quaternionEight_automorphism_action hQ).2.1]
  refine ⟨hK6, hQ24, ?_, ?_, ?_, ?_⟩
  · intro P hPS g hg
    obtain ⟨k, c, h0, hlast, hcomp⟩ := semidihedral_fusion_chain n hn S f P hPS g hg
    exact ⟨k, c.toFullFusionChain, h0, hlast, fun x => hcomp x⟩
  · intro k c
    have hreal : ∀ i, ∃ h : G, SemidihedralFusionStep (S : Subgroup G) (c.supports i) h ∧
        ∀ x : c.supports i, (c.automorphisms i x : G) = h⁻¹ * (x : G) * h := by
      intro i
      rcases c.permitted i with ⟨hT, s, hs, hα⟩ | hK | hQ
      · exact ⟨s, Or.inl ⟨hT, hs⟩, hα⟩
      · obtain ⟨y, hy⟩ : c.automorphisms i ∈ (c.supports i).normalizerMonoidHom.range := by
          rw [(hK6 _ (c.support_le i) hK).1]
          trivial
        refine ⟨(y : G)⁻¹, Or.inr (Or.inl ⟨hK, Subgroup.inv_mem _ y.2⟩), fun x => ?_⟩
        rw [← hy, Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
      · obtain ⟨y, hy⟩ : c.automorphisms i ∈ (c.supports i).normalizerMonoidHom.range := by
          rw [(hQ24 _ (c.support_le i) hQ).1]
          trivial
        refine ⟨(y : G)⁻¹, Or.inr (Or.inr ⟨hQ, Subgroup.inv_mem _ y.2⟩), fun x => ?_⟩
        rw [← hy, Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
    obtain ⟨g, hg, hgx⟩ := (c.toFusionChain hreal).exists_realizing_element
    exact ⟨g, hg, fun x => hgx x⟩
  · intro V hVS hV
    obtain ⟨-, -, -, -, -, -, -, hK, -⟩ :=
      four_and_quaternion_eight_local_normalizer_quotients n hn S f V hVS (Or.inl hV)
    obtain ⟨-, -, hS2, halt⟩ := hK hV
    rcases halt with ⟨heq, -⟩ | ⟨-, h24⟩
    · exfalso
      have h6 := (hK6 V hVS hV).2
      rw [heq, hS2] at h6
      norm_num at h6
    · exact h24
  · intro Q hQS hQ
    obtain ⟨hRsyl, -, -, -, -, -, -, -, hQ8⟩ :=
      four_and_quaternion_eight_local_normalizer_quotients n hn S f Q hQS (Or.inr hQ)
    obtain ⟨h16, hS8, halt, hSD, hQ16⟩ := hQ8 hQ
    refine ⟨?_, ?_⟩
    · rcases halt with ⟨heq, -⟩ | ⟨-, h48⟩
      · exfalso
        have h24 := (hQ24 Q hQS hQ).2
        rw [heq, hS8] at h24
        norm_num at h24
      · exact h48
    · obtain ⟨P, hP⟩ := hRsyl
      have eP : P ≃* ((S : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) :=
        (MulEquiv.subgroupCongr hP).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
      refine ⟨P, ?_, fun h4 => ?_, fun h5 => ?_⟩
      · rw [Nat.card_congr eP.toEquiv, h16]
      · obtain ⟨e⟩ := hSD h4
        exact ⟨eP.trans e⟩
      · obtain ⟨e⟩ := hQ16 h5
        exact ⟨eP.trans e⟩

end CFSG.Semidihedral.Local
