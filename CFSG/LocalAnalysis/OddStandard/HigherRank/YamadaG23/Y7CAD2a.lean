module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAP

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_D2_simple {R : Type} [Group R] (c : K7Abs ρ t J Q P M6 M7) {N : Subgroup Γ}
    (hN : N = Subgroup.normalClosure (J : Set Γ)) (hq : CFSG.IsQuasisimple ↥N)
    (hker : ∀ n m : Γ, ρ n = 1 → m ∈ N → n * m = m * n)
    (hZ : ∀ z ∈ N, (∀ n ∈ N, z * n = n * z) → ρ z = 1)
    (f : Γ →* R) (hf : ∀ g : Γ, f g = 1 ↔ ρ g = 1) :
    IsSimpleGroup ↥(N.map f) ∧ (¬ ∀ x y : ↥(N.map f), x * y = y * x) ∧
      2 ^ 6 ∣ Nat.card ↥(N.map f) ∧ 7 ∣ Nat.card ↥(N.map f) := by
  have hPN : P ≤ N := by rw [hN]; exact y7c_P_le_N c
  have hkerP : ∀ z : Γ, z ∈ P → f z = 1 → z = 1 := by
    intro z hzP hfz
    have hρ : ρ z = 1 := (hf z).mp hfz
    have hzNc : z ∈ Subgroup.normalClosure (J : Set Γ) := by
      rw [← hN]; exact hPN hzP
    have hzc : ∀ n ∈ Subgroup.normalClosure (J : Set Γ), z * n = n * z :=
      fun n hn => hker z n hρ (by simpa [hN] using hn)
    exact y7c_P_inf_center c hzP hzNc hzc
  have hinjP : Function.Injective (f.subgroupMap P) := by
    rw [← MonoidHom.ker_eq_bot_iff (f.subgroupMap P), Subgroup.ker_subgroupMap]
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_bot]
    exact ⟨fun hfz => Subtype.ext (by simpa using hkerP (x : Γ) x.2 hfz),
      fun hx => by rw [hx]; simp⟩
  have hcardP : Nat.card ↥(P.map f) = Nat.card ↥P :=
    (Nat.card_congr (Equiv.ofBijective (f.subgroupMap P)
      ⟨hinjP, f.subgroupMap_surjective P⟩)).symm
  have hdvdP : 2 ^ 6 ∣ Nat.card ↥(N.map f) := by
    have hP : Nat.card ↥(P.map f) = 2 ^ 6 := by rw [hcardP, c.P_card]
    exact hP ▸ Subgroup.card_dvd_of_le (Subgroup.map_mono hPN)
  have hJN : J ≤ N := by rw [hN]; exact Subgroup.le_normalClosure
  have hkerJ : ∀ z : Γ, z ∈ J → f z = 1 → z = 1 := by
    intro z hzJ hfz
    exact c.ρ_inj z hzJ ((hf z).mp hfz)
  have hinjJ : Function.Injective (f.subgroupMap J) := by
    rw [← MonoidHom.ker_eq_bot_iff (f.subgroupMap J), Subgroup.ker_subgroupMap]
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_bot]
    exact ⟨fun hfz => Subtype.ext (by simpa using hkerJ (x : Γ) x.2 hfz),
      fun hx => by rw [hx]; simp⟩
  have hcardJ : Nat.card ↥(J.map f) = Nat.card ↥J :=
    (Nat.card_congr (Equiv.ofBijective (f.subgroupMap J)
      ⟨hinjJ, f.subgroupMap_surjective J⟩)).symm
  have hdvdJ : 7 ∣ Nat.card ↥(N.map f) := by
    have hJ : Nat.card ↥(J.map f) = 168 := by rw [hcardJ, y7c_J_card c]
    have h7 : 7 ∣ Nat.card ↥(J.map f) := by rw [hJ]; norm_num
    exact h7.trans (Subgroup.card_dvd_of_le (Subgroup.map_mono hJN))
  have hker_eq : (f.subgroupMap N).ker = Subgroup.center ↥N := by
    rw [Subgroup.ker_subgroupMap]
    ext z
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hfz
      have hρ : ρ (z : Γ) = 1 := (hf (z : Γ)).mp hfz
      intro m
      exact Subtype.ext (by simpa using (hker (z : Γ) (m : Γ) hρ m.2).symm)
    · intro hc
      exact (hf (z : Γ)).mpr (hZ (z : Γ) z.2 fun g hg =>
        by simpa using (congrArg Subtype.val (hc ⟨g, hg⟩)).symm)
  let e : ↥N ⧸ Subgroup.center ↥N ≃* ↥(N.map f) :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap N)
        (f.subgroupMap_surjective N))
  have hs : IsSimpleGroup ↥(N.map f) := by
    haveI : IsSimpleGroup (↥N ⧸ Subgroup.center ↥N) := hq.2.1
    exact e.symm.isSimpleGroup
  have hna : ¬ ∀ x y : ↥(N.map f), x * y = y * x := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    intro hcomm
    exact hab (e.injective (by rw [map_mul, map_mul]; exact hcomm (e a) (e b)))
  exact ⟨hs, hna, hdvdP, hdvdJ⟩

end CFSG.OddStandard.HigherRank.YamadaG23
