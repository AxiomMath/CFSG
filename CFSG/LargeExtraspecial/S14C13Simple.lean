module

public import CFSG.LargeExtraspecial.S14C13Frattini
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.Open

variable {Y : Type} [Group Y] {M : Subgroup Y}

theorem eq_top_of_centralizer_le [Finite Y] {M0 : Subgroup M} [M0.Normal] {t : Y}
    (htM : t ∈ M) {N : Subgroup Y}
    (hF : (timmesfeldFStar ↥(M ⊓ centralizer ({t} : Set Y))).map
      (M ⊓ centralizer ({t} : Set Y)).subtype = N)
    (hN2 : IsPGroup 2 N) (htN : t ∈ N) (ht1 : t ≠ 1)
    (hcen : ∀ y ∈ N, (∀ n ∈ N, y * n = n * y) → y = 1 ∨ y = t)
    (hCt : M ⊓ centralizer ({t} : Set Y) ≤ M0.map M.subtype) : M0 = ⊤ := by
  have hNK : N ≤ M ⊓ centralizer ({t} : Set Y) := by
    rw [← hF]
    exact map_subtype_le _
  have hmem : ∀ m : M, (m : Y) ∈ M0.map M.subtype → m ∈ M0 := fun m hm => by
    obtain ⟨m', hm', he⟩ := Subgroup.mem_map.mp hm
    rwa [show m = m' from Subtype.ext he.symm]
  set N' : Subgroup M := N.comap M.subtype
  have hN0 : N' ≤ M0 := fun n hn => hmem n (hCt (hNK hn))
  have hN2' : IsPGroup 2 N' := hN2.comap_of_injective M.subtype Subtype.val_injective
  have hcent := CFSG.Adapters.generalized_fitting_self_centralizing ↥(M ⊓ centralizer ({t} : Set Y))
  have hZ : ∀ x : M, x * ⟨t, htM⟩ = ⟨t, htM⟩ * x → (∀ n ∈ N', x * n = n * x) →
      x = 1 ∨ x = ⟨t, htM⟩ := by
    intro x hxt hxN
    have hxK : (x : Y) ∈ M ⊓ centralizer ({t} : Set Y) := Subgroup.mem_inf.mpr
      ⟨x.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxt)⟩
    have hxN' : ∀ n ∈ N, (x : Y) * n = n * x := fun n hn =>
      congrArg Subtype.val (hxN ⟨n, (Subgroup.mem_inf.mp (hNK hn)).1⟩ hn)
    have hxF : (⟨x, hxK⟩ : ↥(M ⊓ centralizer ({t} : Set Y))) ∈
        timmesfeldFStar ↥(M ⊓ centralizer ({t} : Set Y)) := by
      refine hcent (mem_centralizer_iff.mpr fun f hf => ?_)
      have hfN : ((f : ↥(M ⊓ centralizer ({t} : Set Y))) : Y) ∈ N := by
        rw [← hF]
        exact ⟨f, hf, rfl⟩
      exact Subtype.ext (hxN' _ hfN).symm
    have hxNN : (x : Y) ∈ N := by
      rw [← hF]
      exact ⟨_, hxF, rfl⟩
    rcases hcen _ hxNN hxN' with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have htop := centralizer_sup_eq_top (M0 := M0) (N := N')
    (fun h => ht1 (congrArg Subtype.val h)) (show (⟨t, htM⟩ : M) ∈ N' from htN) hN0 hN2' hZ
  have hle : centralizer ({(⟨t, htM⟩ : M)} : Set M) ≤ M0 := fun c hc =>
    hmem c (hCt (Subgroup.mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩))
  rw [eq_top_iff, ← htop]
  exact sup_le hle le_rfl

end CFSG.LargeExtraspecial.S14
