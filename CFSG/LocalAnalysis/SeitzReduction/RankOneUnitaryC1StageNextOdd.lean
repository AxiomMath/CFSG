module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageNextStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}
  (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

noncomputable def permM :
    (normalizer (U : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) →* Equiv.Perm K :=
  H.perm.comp (inclusion inf_le_left)

theorem range_inf_stabilizer_eq :
    H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K) = H.permM.range := by
  refine le_antisymm ?_ ?_
  · rintro σ ⟨⟨n, rfl⟩, hσ⟩
    have h0 : H.perm n 0 = 0 := hσ
    obtain ⟨x, hx, hxn⟩ := H.mem_U₁_mul_centralizer n h0
    have hxN : x ∈ normalizer (U : Set G) := le_normalizer (H.stage.U₁_le hx)
    have hm : x⁻¹ * (n : G) ∈ normalizer (U : Set G) ⊓ centralizer ({t} : Set G) :=
      mem_inf.mpr ⟨mul_mem (inv_mem hxN) n.2, hxn⟩
    refine ⟨⟨x⁻¹ * (n : G), hm⟩, ?_⟩
    have hx1 : H.perm ⟨x, hxN⟩ = 1 := H.perm_eq_one_of_mem_U ⟨x, hxN⟩ (H.stage.U₁_le hx)
    have e : (inclusion inf_le_left ⟨x⁻¹ * (n : G), hm⟩ : normalizer (U : Set G)) =
        (⟨x, hxN⟩ : normalizer (U : Set G))⁻¹ * n := Subtype.ext rfl
    show H.perm (inclusion inf_le_left ⟨x⁻¹ * (n : G), hm⟩) = H.perm n
    rw [e, map_mul, map_inv, hx1, inv_one, one_mul]
  · rintro σ ⟨m, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    show H.perm (inclusion inf_le_left m) 0 = 0
    exact H.perm_zero_of_mem_centralizer _ (mem_inf.mp m.2).2

theorem odd_card_range_inf_stabilizer :
    Odd (Nat.card ↥(H.perm.range ⊓ MulAction.stabilizer (Equiv.Perm K) (0 : K))) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [H.range_inf_stabilizer_eq, ← Subgroup.index_ker]
  set M : Subgroup G := normalizer (U : Set G) ⊓ centralizer ({t} : Set G) with hM
  have hTM : T ≤ M := le_inf (H.stage.T_le_U.trans le_normalizer) H.stage.start.le
  have hker : T.subgroupOf M ≤ H.permM.ker := by
    intro m hm
    rw [mem_subgroupOf] at hm
    rw [MonoidHom.mem_ker]
    exact H.perm_eq_one_of_mem_U _ (H.stage.T_le_U hm)
  have h1 : H.permM.ker.index ∣ T.relIndex M := index_dvd_of_le hker
  have h2 : T.relIndex M ∣ T.relIndex (centralizer ({t} : Set G)) :=
    ⟨M.relIndex (centralizer ({t} : Set G)),
      (relIndex_mul_relIndex T M (centralizer ({t} : Set G)) hTM inf_le_right).symm⟩
  obtain ⟨P, hP⟩ := H.stage.start.sylow
  have h3 : T.relIndex (centralizer ({t} : Set G)) =
      (P : Subgroup (centralizer ({t} : Set G))).index := by
    rw [hP]
    rfl
  have hcop := P.card_coprime_index
  have hPcard : Nat.card P = Nat.card T := by
    rw [hP]
    exact Nat.card_congr (subgroupOfEquivOfLe H.stage.start.le).toEquiv
  have hT2 : 2 ∣ Nat.card T := by
    rw [H.stage.T_eq, H.stage.start.card_szT₁_sup_of_card_sylow H.stage.card_sylow]
    exact dvd_mul_right _ _
  have hodd : Odd (P : Subgroup (centralizer ({t} : Set G))).index := by
    rw [Nat.odd_iff]
    by_contra h2i'
    have h2i : 2 ∣ (P : Subgroup (centralizer ({t} : Set G))).index :=
      Nat.dvd_of_mod_eq_zero (by omega)
    rw [hPcard] at hcop
    have h21 := Nat.dvd_gcd hT2 h2i
    rw [Nat.Coprime.gcd_eq_one hcop] at h21
    omega
  rw [h3] at h2
  exact Odd.of_dvd_nat hodd (h1.trans h2)

end U3C1Next

end CFSG.SeitzReduction.RankOne
