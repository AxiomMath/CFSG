module

public import CFSG.GH74.GLS.C3.Prop121.Moore
public import CFSG.GH74.GLS.C3.Layer3.Moore
public import CFSG.GH74.GLS.C3.Layers

public section

namespace CFSG.GH74.GLS.C3.Prop121

open CFSG.GH74.GLS CFSG.Sporadic.SchreierLemmas

theorem exists_subgroup_alt_of_threeLocal
    {G : Type} [Group G] {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    {x : G} {K Q : Subgroup G} {t u g : G} (hS : Stage3Loc n x K Q t u g)
    {L : Subgroup G} {Θ : ↥(L ⊔ Subgroup.zpowers u) ≃* Equiv.Perm (Fin (n + 1))}
    (hL : ThreeLocal n K t u g L Θ) :
    ∃ G₀ : Subgroup G, Nonempty (G₀ ≃* alternatingGroup (Fin (n + 4))) := by
  obtain ⟨y, hy, hne⟩ := exists_moore_of_threeLocal hn hS hL
  have hy' : IsMooreFamily (n + 4 - 2) y := by
    have e : n + 4 - 2 = n + 2 := by omega
    rw [e]; exact hy
  exact Layer3.exists_subgroup_alt_of_moore (by omega : 5 ≤ n + 4) y hy'
    ⟨1, ⟨le_rfl, by omega⟩, hne⟩

theorem s_prop121_cfg_of_parts
    (hA : S_stage3Loc) (hB : S_lemma123) : S_prop121_cfg := by
  intro G _ _ hC n hn hcfg hap
  obtain ⟨x, K, T, Q, S, a, hcfg⟩ := hcfg
  obtain ⟨t, u, g, hS⟩ := hA G hC n hn x K T Q S a hcfg hap
  obtain ⟨L, Θ, hL⟩ := hB G hC n hn x K T Q S a hcfg hap t u g hS
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  exact exists_subgroup_alt_of_threeLocal hn' hS hL

end CFSG.GH74.GLS.C3.Prop121
