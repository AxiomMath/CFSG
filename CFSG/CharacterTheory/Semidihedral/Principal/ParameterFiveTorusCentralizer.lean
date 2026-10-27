module

public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusCentralizerSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.ParameterFiveTorusNormalizer

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_parameter_five_trivial_core_three_torus_centralizer_quotient
    {G : Type}
    [Group G] [Finite G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (hN : N t = ⊥) :
    let s₀ : G := fS (s n)
    let V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let π : K →* K ⧸ CFSG.pPrimeCore 2 K := QuotientGroup.mk' (CFSG.pPrimeCore 2 K)
    (CFSG.pPrimeCore 2 K).map K.subtype = W ∧ (CFSG.pPrimeCore 2 H).map H.subtype = W ∧
      (((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 36 ∧ Nat.card H = 72) ∨
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 180 ∧ Nat.card H = 360)) ∧
        ¬ ((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 36 ∧ Nat.card H = 72) ∧
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 180 ∧ Nat.card H = 360))) ∧
      (∃ P : Sylow 2 (K ⧸ CFSG.pPrimeCore 2 K), (P : Subgroup _) = (V.subgroupOf K).map π) ∧
      (∀ tK : K, (tK : G) = t → (V.subgroupOf K).map π = Subgroup.centralizer {π tK}) ∧
      ∀ w ∈ W, w ≠ 1 → Nat.card (Subgroup.centralizer ({w} : Set G)) ≤ 180 := by
  intro s₀ V D W H K π
  obtain ⟨-, ht2, -, hsC, -, -⟩ := supplied_t_s_facts hn fS ht
  have hnode := perfect_parameter_five_trivial_core_three_torus_inversion_normalizer n hn S fS t
    ht hnonab hcentral hnc hmodel hN
  obtain ⟨-, -, -, hW3, ⟨hsup, hdisj, -⟩, hD, hCK, -, -, ⟨d, hd, -, -, -, hdW, -⟩, hVsyl, hKH,
    hinv, hMH, -, hKM, -⟩ := hnode
  have hV : IsKleinFour V := supplied_four_group_isKleinFour hn fS ht
  have htS : t ∈ (S : Subgroup G) := by
    rw [ht]
    exact Subgroup.pow_mem _ (fS (r n)).property _
  have hVS : V ≤ (S : Subgroup G) :=
    sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr (fS (s n)).property)
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    norm_num at ht2
  have hfus : ∀ v ∈ V, v ≠ 1 → ∃ g ∈ Subgroup.normalizer (V : Set G), g * t * g⁻¹ = v :=
    fun v hv hv1 =>
      CFSG.Semidihedral.Local.klein_four_normalizer_conj_transitive n hn S fS V hVS hV htV hv ht1
        hv1
  exact three_torus_centralizer_quotient_of_data V W rfl hV ht2 hW3 hsup hdisj hD hCK
    (Subgroup.mem_inf.mp hd).1 hdW hVsyl hKH hinv hMH hKM hfus

end CFSG.Semidihedral.Principal
