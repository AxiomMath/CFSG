module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAJ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 K : Subgroup Γ}

theorem y7c_K_le_N (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) : K ≤ Subgroup.normalClosure (J : Set Γ) := by
  have hN : (Subgroup.normalClosure (J : Set Γ)).Normal := inferInstance
  rcases CFSG.LocalCores.component_normal_subgroup hK hN with h | h
  · exact h
  · exfalso
    have hKcent : K ≤ Subgroup.centralizer (Subgroup.normalClosure (J : Set Γ) : Set Γ) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hKtcent : conjSub t K ≤
        Subgroup.centralizer (Subgroup.normalClosure (J : Set Γ) : Set Γ) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      have hconj : (Subgroup.normalClosure (J : Set Γ)).map (MulAut.conj t).toMonoidHom =
          Subgroup.normalClosure (J : Set Γ) := y7c_conjSub_eq_of_normal t
      have hmap := congrArg (Subgroup.map (MulAut.conj t).toMonoidHom) h
      rw [Subgroup.map_commutator, hconj, Subgroup.map_bot] at hmap
      simpa only [conjSub] using hmap
    have hJcent : J ≤ Subgroup.centralizer (Subgroup.normalClosure (J : Set Γ) : Set Γ) :=
      hJK.trans (sup_le hKcent hKtcent)
    obtain ⟨a, ha, b, hb, hab⟩ := y7c_J_nonabelian c
    exact hab ((Subgroup.mem_centralizer_iff.mp (hJcent hb)) a
      (Subgroup.subset_normalClosure ha))

theorem y7c_N_eq_ncK (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) :
    Subgroup.normalClosure (J : Set Γ) = Subgroup.normalClosure (K : Set Γ) := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.normalClosure_le_normal ?_
    intro j hj
    have hKt : conjSub t K ≤ Subgroup.normalClosure (K : Set Γ) := by
      calc conjSub t K ≤ conjSub t (Subgroup.normalClosure (K : Set Γ)) :=
            y7c_conjSub_le Subgroup.le_normalClosure
        _ = Subgroup.normalClosure (K : Set Γ) := y7c_conjSub_eq_of_normal t
    exact (sup_le Subgroup.le_normalClosure hKt) (hJK hj)
  · exact Subgroup.normalClosure_le_normal (y7c_K_le_N c hK hJK)

theorem y7c_conjSub_K_le_N (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (g : Γ) : conjSub g K ≤ Subgroup.normalClosure (J : Set Γ) := by
  rw [y7c_N_eq_ncK c hK hJK]
  calc conjSub g K ≤ conjSub g (Subgroup.normalClosure (K : Set Γ)) :=
        y7c_conjSub_le Subgroup.le_normalClosure
    _ = Subgroup.normalClosure (K : Set Γ) := y7c_conjSub_eq_of_normal g

theorem y7c_ker_cent_N (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) {n : Γ} (hn : ρ n = 1) {m : Γ}
    (hm : m ∈ Subgroup.normalClosure (J : Set Γ)) : n * m = m * n := by
  rcases CFSG.LocalCores.component_normal_subgroup hK (MonoidHom.normal_ker ρ) with h | h
  · exfalso
    have hJker : J ≤ MonoidHom.ker ρ := by
      refine hJK.trans (sup_le h ?_)
      calc conjSub t K ≤ conjSub t (MonoidHom.ker ρ) := y7c_conjSub_le h
        _ = MonoidHom.ker ρ := y7c_conjSub_eq_of_normal t
    obtain ⟨a, ha, b, hb, hab⟩ := y7c_J_nonabelian c
    refine hab (by rw [c.ρ_inj a ha (MonoidHom.mem_ker.mp (hJker ha)),
      c.ρ_inj b hb (MonoidHom.mem_ker.mp (hJker hb))])
  · have hle : Subgroup.normalClosure (K : Set Γ) ≤
        Subgroup.centralizer (MonoidHom.ker ρ : Set Γ) :=
      Subgroup.normalClosure_le_normal (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
    have hm' : m ∈ Subgroup.normalClosure (K : Set Γ) := by
      rwa [← y7c_N_eq_ncK c hK hJK]
    exact Subgroup.mem_centralizer_iff.mp (hle hm') n (MonoidHom.mem_ker.mpr hn)

theorem y7c_N_eq_K_of_normal (c : K7Abs ρ t J Q P M6 M7) (hK : CFSG.IsComponent K)
    (hJK : J ≤ K ⊔ conjSub t K) (hnorm : ∀ g : Γ, conjSub g K = K) :
    Subgroup.normalClosure (J : Set Γ) = K := by
  rw [y7c_N_eq_ncK c hK hJK]
  haveI : K.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ ∈ conjSub g K := y7c_mul_mem_conjSub (g := g) hn
    rwa [hnorm g] at h1⟩
  exact Subgroup.normalClosure_eq_self K

end CFSG.OddStandard.HigherRank.YamadaG23
