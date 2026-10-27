module

public import CFSG.GroupTheory.PerfectSectionStability
import CFSG.GroupTheory.SectionLemmas
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ChiefSectionPGroup
import CFSG.GroupTheory.CentralizeSolvableOfPCores
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem commutator_le_of_forall_chief {G : Type*} [Group G] [Finite G] {J H P N₀ : Subgroup G}
    (hJ : Group.IsPerfect J) (hPs : Group.IsSolvable P) (hN₀P : N₀ ≤ P)
    (hPN₀ : P ≤ Subgroup.normalizer (N₀ : Set G)) (hJN₀ : J ≤ Subgroup.normalizer (N₀ : Set G))
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hHN₀ : H ≤ Subgroup.normalizer (N₀ : Set G))
    (hchief : ∀ N M : Subgroup G, N₀ ≤ N → N < M → M ≤ P →
      H ≤ Subgroup.normalizer (N : Set G) → H ≤ Subgroup.normalizer (M : Set G) →
      (∀ K : Subgroup G, N ≤ K → K ≤ M → H ≤ Subgroup.normalizer (K : Set G) →
        K = N ∨ K = M) →
      ⁅M, J⁆ ≤ N) :
    ⁅P, J⁆ ≤ N₀ := by
  classical
  let C : Subgroup G → Prop := fun Q =>
    Group.IsSolvable Q → N₀ ≤ Q → Q ≤ Subgroup.normalizer (N₀ : Set G) →
    H ≤ Subgroup.normalizer (Q : Set G) →
    (∀ N M : Subgroup G, N₀ ≤ N → N < M → M ≤ Q →
      H ≤ Subgroup.normalizer (N : Set G) → H ≤ Subgroup.normalizer (M : Set G) →
      (∀ K : Subgroup G, N ≤ K → K ≤ M → H ≤ Subgroup.normalizer (K : Set G) →
        K = N ∨ K = M) →
      ⁅M, J⁆ ≤ N) →
    ⁅Q, J⁆ ≤ N₀
  have key : ∀ Q, C Q := by
    intro Q
    refine WellFounded.induction (Finite.to_wellFoundedLT : WellFoundedLT (Subgroup G))
      (C := C) Q ?_
    intro P ih hPs hN₀P hPN₀ hHP hchief
    rcases eq_or_lt_of_le hN₀P with hEq | hlt
    ·
      subst hEq
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp hJN₀
    ·
      obtain ⟨N, hN₀N, hNlt, hHN, hmax⟩ :=
        exists_maximal_invariant_lt (H := H) hN₀P hlt hHN₀
      have hNleP : N ≤ P := hNlt.le
      have hPN : ⁅P, J⁆ ≤ N := hchief N P hN₀N hNlt le_rfl hHN hHP hmax
      have hNsolv : Group.IsSolvable N := by
        haveI : Group.IsSolvable ↥P := hPs
        exact Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hNleP).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hNleP).symm.injective
      have hNN₀ : ⁅N, J⁆ ≤ N₀ := by
        refine ih N hNlt hNsolv hN₀N (hNleP.trans hPN₀) hHN ?_
        intro N' M' hN₀N' hN'M' hM'N hHN' hHM' hmin'
        exact hchief N' M' hN₀N' hN'M' (hM'N.trans hNleP) hHN' hHM' hmin'
      exact commutator_le_of_isPerfect_of_le (V := P) (J := J) (T := N) (N := N₀)
        hJ hNsolv hN₀N
        (Subgroup.normal_subgroupOf_of_le_normalizer (N := N₀) (H := N)
          (hNleP.trans hPN₀))
        hNN₀ hPN
  exact key P hPs hN₀P hPN₀ hHP hchief

theorem commutator_le_of_chief_of_isPGroup {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] {H P N M : Subgroup G} (hP : IsPGroup r P) (hPH : P ≤ H)
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hNM : N < M) (hMP : M ≤ P)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hHM : H ≤ Subgroup.normalizer (M : Set G))
    (hmin : ∀ K : Subgroup G, N ≤ K → K ≤ M → H ≤ Subgroup.normalizer (K : Set G) →
      K = N ∨ K = M) :
    ⁅M, P⁆ ≤ N := by
  have hPM : P ≤ Subgroup.normalizer (M : Set G) := hPH.trans hHM
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := hPH.trans hHN
  have hKlt : ⁅M, P⁆ ⊔ N < M :=
    commutator_sup_lt_of_isPGroup hMP hP hPM hPN hNM.le hNM.ne
  have hHK : H ≤ Subgroup.normalizer ((⁅M, P⁆ ⊔ N : Subgroup G) : Set G) := by
    have hcomm : H ≤ Subgroup.normalizer (⁅M, P⁆ : Subgroup G) :=
      CFSG.GroupTheory.FT63ChII.le_normalizer_commutator hHM hHP
    exact (le_inf hcomm hHN).trans
      (Subgroup.inf_normalizer_le_normalizer_sup ⁅M, P⁆ N)
  rcases hmin (⁅M, P⁆ ⊔ N) le_sup_right hKlt.le hHK with h | h
  · exact h ▸ le_sup_left
  · exact absurd h hKlt.ne

theorem commutator_eq_bot_of_forall_chief_pCoreOf {G : Type*} [Group G] [Finite G]
    {J X Θ : Subgroup G} (hΘ : Group.IsSolvable Θ) (hJ : Group.IsPerfect J)
    (hJΘ : J ≤ Subgroup.normalizer (Θ : Set G)) (hXΘ : X ≤ Subgroup.normalizer (Θ : Set G))
    (h2 : CFSG.Open.pCoreOf 2 Θ = ⊥) (h3 : CFSG.Open.pCoreOf 3 Θ = ⊥)
    (hchief : ∀ r : ℕ, r.Prime → 5 ≤ r → ∀ N M : Subgroup G, N < M →
      M ≤ CFSG.Open.pCoreOf r Θ →
      CFSG.Open.pCoreOf r Θ ⊔ J ⊔ X ≤ Subgroup.normalizer (N : Set G) →
      CFSG.Open.pCoreOf r Θ ⊔ J ⊔ X ≤ Subgroup.normalizer (M : Set G) →
      (∀ K : Subgroup G, N ≤ K → K ≤ M →
        CFSG.Open.pCoreOf r Θ ⊔ J ⊔ X ≤ Subgroup.normalizer (K : Set G) → K = N ∨ K = M) →
      ⁅M, J⁆ ≤ N) :
    ⁅Θ, J⁆ = ⊥ := by
  classical
  have hJJ : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ
  have h : ∀ q : ℕ, q.Prime → ⁅J, CFSG.Open.pCoreOf q Θ⁆ = ⊥ := by
    intro q hq
    haveI : Fact q.Prime := ⟨hq⟩
    rcases eq_or_ne q 2 with hq2 | hq2
    · subst q
      rw [h2, Subgroup.commutator_bot_right]
    rcases eq_or_ne q 3 with hq3 | hq3
    · subst q
      rw [h3, Subgroup.commutator_bot_right]
    have hq5 : 5 ≤ q := by
      have h2q : 2 ≤ q := hq.two_le
      rcases hq.eq_two_or_odd' with h | hodd
      · omega
      · rcases hodd with ⟨k, hk⟩
        omega
    have hcoreJ : CFSG.Open.pCoreOf q Θ ⊔ J ⊔ X ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf q Θ : Set G) := by
      refine sup_le (sup_le Subgroup.le_normalizer ?_) ?_
      · exact hJΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := q) Θ)
      · exact hXΘ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := q) Θ)
    haveI : Group.IsNilpotent ↥(CFSG.Open.pCoreOf q Θ) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := q) Θ).isNilpotent
    have hsolv : Group.IsSolvable (CFSG.Open.pCoreOf q Θ) := IsNilpotent.to_isSolvable
    have hbotnorm : ∀ S : Subgroup G, S ≤ Subgroup.normalizer (⊥ : Subgroup G) := by
      intro S
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    have hcomm : ⁅CFSG.Open.pCoreOf q Θ, J⁆ ≤ ⊥ :=
      commutator_le_of_forall_chief (J := J)
        (H := CFSG.Open.pCoreOf q Θ ⊔ J ⊔ X)
        (P := CFSG.Open.pCoreOf q Θ) (N₀ := ⊥)
        hJ hsolv bot_le (hbotnorm _) (hbotnorm _) hcoreJ (hbotnorm _)
        (fun N M _ hNM hMP hHN hHM hmin' =>
          hchief q hq hq5 N M hNM hMP hHN hHM hmin')
    have hbot : ⁅CFSG.Open.pCoreOf q Θ, J⁆ = ⊥ := le_bot_iff.mp hcomm
    rw [Subgroup.commutator_comm]
    exact hbot
  have hmain : ⁅J, Θ⁆ = ⊥ :=
    commutator_eq_bot_of_forall_pCoreOf (J := J) (K := Θ) hΘ hJJ hJΘ h
  rw [Subgroup.commutator_comm]
  exact hmain

end CFSG.GroupTheory
