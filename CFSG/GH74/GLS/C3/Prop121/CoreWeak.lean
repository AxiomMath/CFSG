module

public import CFSG.GH74.GLS.C3.Prop121.Final
public import CFSG.GH74.GLS.C3.Prop121.L122Transfer

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS

@[expose] def S_lemma123_core6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 → ∀ n ∈ ({5, 6, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfig n x K T Q S a →
      IsApproxTo G (alternatingGroup (Fin (n + 4))) →
        ∀ t u g : G, Stage3Loc n x K Q t u g →
          ∃ (L : Subgroup G) (lam : ↥L ≃* alternatingGroup (Fin (n + 1))),
            (∀ l ∈ L, l * t = t * l) ∧
            (∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) ∧
            (∀ i : ℤ, t ^ i ∈ L → t ^ i = 1) ∧
            (n = 6 → ∀ h : g * t * g⁻¹ ∈ L,
              ((lam ⟨g * t * g⁻¹, h⟩ : alternatingGroup (Fin (n + 1))) :
                Equiv.Perm (Fin (n + 1))).IsThreeCycle)

theorem s_lemma123_core_of_core6
    (hB : S_lemma123_core6) : S_lemma123_core := by
  intro G _ _ hC n hn x K T Q S a h hap t u g hS
  obtain ⟨L, lam₀, hLt, hC', hZ, hthree₀⟩ := hB G hC n hn x K T Q S a h hap t u g hS
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  by_cases h7 : n = 7
  · subst h7
    obtain ⟨eK⟩ := hS.K_alt
    have hKperf : K ≤ ⁅K, K⁆ := Coord.le_commutator_of_equiv (by norm_num) eK
    have hKL : K ≤ L :=
      Derive.le_of_perfect hKperf (fun k hk => (hS.t_comm_K k hk).symm) hLt hC'
    obtain ⟨lam, hstab⟩ := CosetIso.exists_stab_iso (by norm_num) hKL lam₀ eK
      (Coord.commutator_eq_top_of_equiv (by norm_num) lam₀)
    exact ⟨L, lam, hLt, hC', hZ, fun _ _ => clause4_seven hC h hS hKL lam hstab⟩
  · exact ⟨L, lam₀, hLt, hC', hZ, fun _ hgtL => hthree₀ (by omega) hgtL⟩

theorem s_prop121_cfg_of_core6
    (hB : S_lemma123_core6) : S_prop121_cfg :=
  s_prop121_cfg_of (s_lemma123_core_of_core6 hB)

end CFSG.GH74.GLS.C3.Prop121
