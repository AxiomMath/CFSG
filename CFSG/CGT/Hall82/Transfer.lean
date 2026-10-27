module

public import CFSG.CGT.Hall82.Fusion
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Transfer
public import CFSG.Quasithin.Background.I4Basic

public section

namespace CFSG.CGT.Hall82

theorem timmesfeld75_conjSubgroup_eq_quasithin {G : Type*} [Group G] (g : G)
    (T : Subgroup G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g T = CFSG.Quasithin.conjSubgroup T g⁻¹ := by
  ext x
  rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, CFSG.Quasithin.mem_conjSubgroup_iff]
  simp only [inv_inv]

end CFSG.CGT.Hall82

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec19
open CFSG.ComponentClassification.AS81 CFSG.ComponentClassification.AS81.Hexa

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G}

theorem index_ne_two (S : Setting G M L) (K : Subgroup G) : K.index ≠ 2 := by
  haveI : IsSimpleGroup G := S.simple
  exact CFSG.Quasithin.I4.index_ne_two_of_isSimpleGroup S.nonab K

theorem exists_sylow_le (S : Setting G M L) :
    ∃ P : Sylow 2 M,
      CFSG.Open.pCoreOf 2 M ≤ (P : Subgroup M).map M.subtype := by
  have hJp : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hJleM : CFSG.Open.pCoreOf 2 M ≤ M :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hsub : IsPGroup 2 ((CFSG.Open.pCoreOf 2 M).subgroupOf M) :=
    hJp.comap_subtype (K := M)
  obtain ⟨P, hP⟩ := hsub.exists_le_sylow
  refine ⟨P, ?_⟩
  intro j hj
  exact Subgroup.mem_map.mpr ⟨⟨j, hJleM hj⟩, hP hj, rfl⟩

theorem pow_four_eq_one_of_mem_pCoreOf (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW4 : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w ^ 4 = 1)
    {j : G} (hj : j ∈ CFSG.Open.pCoreOf 2 M) : j ^ 4 = 1 := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (S.exists_mul_of_mem_pCoreOf hF hc).mp hj
  have hcomm : Commute v w := S.commute_blockU_pCoreOf_centralizer hv hw
  rw [hcomm.mul_pow]
  have hv4 : v ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, S.blockU_sq hv, one_pow]
  rw [hv4, hW4 w hw, one_mul]

theorem exists_conj_eq_of_le (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    (hW1 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≠ ⊥) (g : G)
    (hg : CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g ≤ M) :
    ∃ m ∈ M, CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g =
      CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) m := by
  have hg' : CFSG.CGT.Timmesfeld75.conjSubgroup g⁻¹ (CFSG.Open.pCoreOf 2 M) ≤ M := by
    rwa [CFSG.CGT.Hall82.timmesfeld75_conjSubgroup_eq_quasithin, inv_inv]
  have hEq := (S.weaklyClosedIn_pCoreOf hF hc hW2 hWab hW1).2 g⁻¹ hg'
  rw [CFSG.CGT.Hall82.timmesfeld75_conjSubgroup_eq_quasithin, inv_inv] at hEq
  exact ⟨1, M.one_mem, by rwa [CFSG.Quasithin.conjSubgroup_one]⟩

theorem exists_conj (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    (hW1 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≠ ⊥)
    (hW4 : ∀ w ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), w ^ 4 = 1)
    {M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M) :
    ∃ g : G, g ∉ M ∧
      M.relIndex (CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g) ≤ 2 ∧
      ¬ CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g ⊓ M ≤ M₁ := by
  classical
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  obtain ⟨P, hP⟩ := S.exists_sylow_le
  have hAn : ∀ s ∈ (P : Subgroup M).map M.subtype, ∀ b ∈ J, s * b * s⁻¹ ∈ J := by
    intro s hs b hb
    exact S.conj_mem_pCoreOf (Subgroup.map_subtype_le (P : Subgroup M) hs) hb
  have hAc : ∀ b ∈ J, ∀ c ∈ J, b * c = c * b := by
    intro b hb c hc'
    exact S.commute_of_mem_pCoreOf hF hc hWab hb hc'
  have hA4 : ∀ b ∈ J, b ^ 4 = 1 := by
    intro b hb
    exact S.pow_four_eq_one_of_mem_pCoreOf hF hc hW4 hb
  have hNA : Subgroup.normalizer (J : Set G) ≤ M := by
    simpa [J] using le_of_eq S.normalizer_pCoreOf
  exact CFSG.EvenSmallLie.UnitarySix.SolomonWong.solomon_wong_one_of_index S.index_ne_two P hP
    hAn hAc hA4 hNA (S.exists_conj_eq_of_le hF hc hW2 hWab hW1) hM₁ hM₁M

theorem card_le_two_mul_card_inf (S : Setting G M L) {g : G}
    (h : M.relIndex (CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g) ≤ 2) :
    Nat.card (CFSG.Open.pCoreOf 2 M) ≤
      2 * Nat.card ↥(CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g ⊓ M) := by
  let X : Subgroup G := CFSG.Quasithin.conjSubgroup (CFSG.Open.pCoreOf 2 M) g
  have hrel := Subgroup.relIndex_mul_card (H := M) (K := X)
  have hX : Nat.card X = Nat.card (CFSG.Open.pCoreOf 2 M) :=
    CFSG.EvenSmallLie.UnitarySix.SolomonWong.card_conjSubgroup (CFSG.Open.pCoreOf 2 M) g
  calc Nat.card (CFSG.Open.pCoreOf 2 M) = Nat.card X := hX.symm
    _ = M.relIndex X * Nat.card ↥(M ⊓ X) := hrel.symm
    _ = M.relIndex X * Nat.card ↥(X ⊓ M) := by rw [inf_comm]
    _ ≤ 2 * Nat.card ↥(X ⊓ M) := Nat.mul_le_mul_right _ h

theorem mem_of_relIndex_eq_two (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hW2 : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ Subgroup.centralizer (L : Set G) →
      Q ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)))
    (hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
      ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a)
    (hW1 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)) ≠ ⊥)
    {M₁ : Subgroup G} (hM₁ : M₁.relIndex M = 2) (hM₁M : M₁ ≤ M)
    {e : G} (he : e ∈ CFSG.Open.pCoreOf 2 M) (he2 : e ^ 2 = 1) : e ∈ M₁ := by
  classical
  let J : Subgroup G := CFSG.Open.pCoreOf 2 M
  obtain ⟨P, hP⟩ := S.exists_sylow_le
  have hAc : ∀ b ∈ J, ∀ c ∈ J, b * c = c * b := by
    intro b hb c hc'
    exact S.commute_of_mem_pCoreOf hF hc hWab hb hc'
  have hNA : Subgroup.normalizer (J : Set G) ≤ M := by
    simpa [J] using le_of_eq S.normalizer_pCoreOf
  exact CFSG.EvenSmallLie.UnitarySix.SolomonWong.solomon_wong_two_of_index S.index_ne_two P hP
    hAc hNA (S.exists_conj_eq_of_le hF hc hW2 hWab hW1) hM₁ hM₁M he he2

theorem relIndex_M1 (S : Setting G M L)
    (hF : ModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep) :
    (S.M1 hc).relIndex M = 1 ∨ (S.M1 hc).relIndex M = 2 := by
  change ((S.M1 hc).subgroupOf M).index = 1 ∨ ((S.M1 hc).subgroupOf M).index = 2
  rcases (Nat.dvd_prime Nat.prime_two).mp (S.index_M1 hF hc) with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem M1_eq_of_relIndex (S : Setting G M L)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (h : (S.M1 hc).relIndex M = 1) : S.M1 hc = M :=
  le_antisymm (S.M1_le hc) (Subgroup.relIndex_eq_one.mp h)

end CFSG.CGT.Hall82.Setting
