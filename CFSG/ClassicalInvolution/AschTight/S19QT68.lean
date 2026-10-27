module

public import CFSG.ClassicalInvolution.AschTight.S19B93
public import CFSG.ClassicalInvolution.AschTight.S1916CSR

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem conj_z_eq_or (hd : Sec19DataT p f K z S W L t V) {g : G}
    (hg : ∀ x ∈ K ⊓ W, g⁻¹ * x * g ∈ (S : Subgroup G)) :
    g⁻¹ * z * g = z ∨ g⁻¹ * z * g = t ∨ g⁻¹ * z * g = t * z := by
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  have htb := ht.toTightBranch
  have hΩ := hypOmegaMod_of_tightD ht
  have hI := isUniqueInvolution_of_tight htb
  obtain ⟨η, S', hη, hinv, hWη, hηS⟩ := S1911.exists_eta hd0
  have hU : K ⊓ W ∈ USet (CoreAssembly.conjClass K) :=
    (hη.1 (S1911.inf_mem_eta hd0 hη hinv hWη hηS)).1
  have hU' := S19B.conjSub_mem_USet hΩ.conjInvariant hU g⁻¹
  have hU'S : conjSub g⁻¹ (K ⊓ W) ≤ (S : Subgroup G) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h := hg _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h
  obtain ⟨V₀, ⟨hV₀η, hor⟩, -⟩ := l6_8 p f ht.branch.odd ht.branch.five G _ hΩ S _ hU' hU'S η
    ⟨S', hη, hinv⟩ hηS
  have hzU : z ∈ K ⊓ W := ⟨hI.mem, (S1916.isUniqueInvolution_W_inf hd).mem.1⟩
  have hgzU : g⁻¹ * z * g ∈ conjSub g⁻¹ (K ⊓ W) := by
    have h := conj_mem_conjSub (n := g⁻¹) hzU
    rwa [inv_inv] at h
  have hIg : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
    have h := hI.conj g⁻¹
    rwa [inv_inv] at h
  have hKg : conjSub g⁻¹ K ∈ CoreAssembly.conjClass K :=
    hΩ.conjInvariant g⁻¹ K (CoreAssembly.mem_conjClass_self K)
  obtain ⟨J, hJ, hV₀J, hJu⟩ : ∃ J ∈ CoreAssembly.conjClass K, V₀ ≤ J ∧
      IsUniqueInvolution J (g⁻¹ * z * g) := by
    rcases hor with h | h
    · refine ⟨conjSub g⁻¹ K, hKg, ?_, hIg⟩
      rw [← h]
      exact conjSub_mono inf_le_left
    · obtain ⟨J, hJ, hRJ, -, -⟩ := mem_RSet_iff.mp h
      obtain ⟨j, hj⟩ := S1911.exists_isUniqueInvolution_member htb hJ
      have hgzJ : g⁻¹ * z * g ∈ J := hRJ (Subgroup.mem_sup_left hgzU)
      have hjz : g⁻¹ * z * g = j := (hj.unique _ hgzJ hIg.sq).resolve_left hIg.ne_one
      exact ⟨J, hJ, le_sup_right.trans hRJ, hjz ▸ hj⟩
  exact S1911.invol_eq_or hd hη hinv hWη hV₀η hJ hV₀J hJu

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q
