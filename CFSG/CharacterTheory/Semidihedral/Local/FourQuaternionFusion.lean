module

public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionFusionSupport
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphismsSupport

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem semidihedralFusionStep_forms_exclusive (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (T : Subgroup G) :
    (T = S → ¬ IsKleinFour T ∧ ¬ Nonempty (T ≃* QuaternionGroup 2)) ∧
      (IsKleinFour T → ¬ Nonempty (T ≃* QuaternionGroup 2)) := by
  have hcardS : Nat.card (S : Subgroup G) = 2 ^ n := by
    rw [← Nat.card_congr f.toEquiv, card n (by omega)]
  have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨fun hTS => ⟨fun hK => ?_, fun ⟨e⟩ => ?_⟩, fun hK ⟨e⟩ => ?_⟩
  · have h4 : Nat.card T = 4 := hK.card_four
    rw [hTS, hcardS] at h4
    omega
  · have h8 := card_of_equiv e
    rw [hTS, hcardS] at h8
    omega
  · have h4 : Nat.card T = 4 := hK.card_four
    have h8 := card_of_equiv e
    omega

theorem semidihedral_fusion_chain (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (P : Subgroup G) (hPS : P ≤ S) (g : G)
    (hg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S) :
    ∃ k : ℕ, ∃ c : SemidihedralFusionChain (S : Subgroup G) k,
      c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = P.map (MulAut.conj g⁻¹).toMonoidHom ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c₀, hc₀, hc₀g⟩ := CFSG.RankTwoShapes.alperin_centric_radical_fusion S hPS hg
  obtain ⟨z, hz, hzc⟩ := semidihedralFusionDecomposition_of_alperin n hn S f hc₀
  obtain ⟨k, c, hfirst, hlast, hcomp⟩ := hz.exists_chain hPS
  refine ⟨k, c, hfirst, ?_, fun x => ?_⟩
  · rw [hlast]
    exact map_conj_inv_eq_of_pointwise P fun x hx => (hzc x hx).trans (hc₀g x hx)
  · have hx : (x : G) ∈ P := hfirst ▸ x.2
    rw [hcomp x]
    exact (hzc x hx).trans (hc₀g x hx)

theorem fusion_generated_by_four_and_quaternion_eight_normalizers (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    (∀ P : Subgroup G, P ≤ S → ∀ g : G, P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S →
      ∃ k : ℕ, ∃ c : SemidihedralFusionChain (S : Subgroup G) k,
        c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = P.map (MulAut.conj g⁻¹).toMonoidHom ∧
        ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g) ∧
    (∀ T : Subgroup G, (T = S → ¬ IsKleinFour T ∧ ¬ Nonempty (T ≃* QuaternionGroup 2)) ∧
      (IsKleinFour T → ¬ Nonempty (T ≃* QuaternionGroup 2))) ∧
    (∀ c : SemidihedralFusionChain (S : Subgroup G) 0, ∀ x : c.subgroups 0,
      (c.composite x : G) = x) ∧
    (∀ (k : ℕ) (c : SemidihedralFusionChain (S : Subgroup G) k), ∃ g : G,
      c.subgroups (Fin.last k) = (c.subgroups 0).map (MulAut.conj g⁻¹).toMonoidHom ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g) :=
  ⟨fun P hPS g hg => semidihedral_fusion_chain n hn S f P hPS g hg,
    semidihedralFusionStep_forms_exclusive n hn S f,
    fun c x => c.composite_zero x, fun _ c => c.exists_realizing_element⟩

end CFSG.Semidihedral.Local
