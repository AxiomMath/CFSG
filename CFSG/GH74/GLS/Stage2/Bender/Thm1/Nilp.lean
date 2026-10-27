module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.LayerLemma

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Nil

variable {G : Type} [Group G] [Finite G]

theorem isNilpotent_of_le_Fm {M L : Subgroup G} (h : L ≤ Fm M) : Group.IsNilpotent ↥L := by
  have : Group.IsNilpotent ↥(L.subgroupOf (Fm M)) := by
    have := Fm_nilpotent M
    infer_instance
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h)

theorem le_Op_of_isPGroup_of_le_Fm {r : ℕ} (hr : r.Prime) {M X : Subgroup G} (hX : IsPGroup r ↥X)
    (hXF : X ≤ Fm M) : X ≤ Op r M := by
  have : Fact r.Prime := ⟨hr⟩
  have hXM : X ≤ M := hXF.trans (Fm_le M)
  set F : Subgroup ↥M := fittingSubgroup ↥M with hF
  set Y : Subgroup ↥M := X.subgroupOf M with hY
  have hYF : Y ≤ F := by
    intro y hy
    obtain ⟨f, hf, hfy⟩ := hXF (Subgroup.mem_subgroupOf.mp hy)
    have : f = y := Subtype.ext hfy
    exact this ▸ hf
  have hYp : IsPGroup r ↥Y := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm
  have hYF' : IsPGroup r ↥(Y.subgroupOf F) := hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYF).symm
  obtain ⟨Q, hQ⟩ := hYF'.exists_le_sylow
  have hle := _root_.Sylow.map_le_pCore (inferInstance : F.Normal) fittingSubgroup_nilpotent r Q
  have hYc : Y ≤ pCore r ↥M := by
    intro y hy
    apply hle
    have : (⟨y, hYF hy⟩ : ↥F) ∈ Y.subgroupOf F := hy
    exact ⟨⟨y, hYF hy⟩, hQ this, rfl⟩
  intro x hx
  exact ⟨⟨x, hXM hx⟩, hYc (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem Op_le_Ep {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) (M : Subgroup G) :
    Op r M ≤ Ep s M := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact s.Prime := ⟨hs⟩
  have hOF : Op r M ≤ Fm M := Op_le_Fm r hr M
  set K : Subgroup ↥(Fm M) := (Op r M).subgroupOf (Fm M) with hK
  have hKn : K.Normal := ⟨fun x hx g => by
    rw [hK, Subgroup.mem_subgroupOf] at hx ⊢
    have hgM : ((g : ↥(Fm M)) : G) ∈ M := Fm_le M g.2
    have := (mem_normalizer_iff.mp (le_normalizer_Op r M hgM) (x : G)).mp hx
    simpa using this⟩
  have hcop : Nat.Coprime s (Nat.card ↥K) := by
    have h1 : Nat.card ↥K = Nat.card ↥(Op r M) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOF).toEquiv
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_Op r hr M)
    rw [h1, hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hs hr).mpr (Ne.symm hrs))
  have hKle : K ≤ pPrimeCore s ↥(Fm M) := le_sSup ⟨hKn, hcop⟩
  calc Op r M = K.map (Fm M).subtype := (Subgroup.map_subgroupOf_eq_of_le hOF).symm
    _ ≤ Ep s M := Subgroup.map_mono hKle

theorem le_of_forall_sylow_le {L K : Subgroup G} [Group.IsNilpotent ↥L]
    (h : ∀ s ∈ (Nat.card ↥L).primeFactors, ((default : Sylow s ↥L) : Subgroup ↥L).map L.subtype ≤ K) :
    L ≤ K := by
  have htop := Sylow.iSup_sylow_eq_top (G := ↥L)
  have hL : L = (⨆ s ∈ (Nat.card ↥L).primeFactors, ((default : Sylow s ↥L) : Subgroup ↥L)).map L.subtype := by
    rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  calc L = _ := hL
    _ ≤ K := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun s => ?_
      rw [Subgroup.map_iSup]
      exact iSup_le fun hs => h s hs

end Nil

end CFSG.GH74.GLS.Stage2.Bender.Thm1
