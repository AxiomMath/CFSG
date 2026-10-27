module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95AssemblyComp
public import CFSG.LocalAnalysis.GLTheoremB.Prop95AssemblyCentral

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open scoped commutatorElement

section Component

variable {G : Type} [Group G] [Finite G]

@[expose] def projQ (p : ℕ) (M : Subgroup G) (hle : CFSG.pCore 2 ↥M ≤ GLAPPrimeCore p ↥M) :
    Mt M →* (↥M ⧸ GLAPPrimeCore p ↥M) :=
  QuotientGroup.map (CFSG.pCore 2 ↥M) (GLAPPrimeCore p ↥M) (MonoidHom.id _) hle

theorem pCore_two_le_glaPPrimeCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (M : Subgroup G) :
    CFSG.pCore 2 ↥M ≤ GLAPPrimeCore p ↥M := by
  have h := pCoreOf_two_le_glaPPrimeCoreOf hp hp2 M
  unfold pCoreOf GLAPPrimeCoreOf at h
  exact (Subgroup.map_le_map_iff_of_injective M.subtype_injective).1 h

theorem isSubnormal_tl {M L : Subgroup G} (hL : L ≤ M) (hsn : CFSG.Open.IsSubnormal L M) :
    CFSG.Open.IsSubnormal (tl M L) ⊤ := by
  have h1 : (L.subgroupOf M).IsSubnormal := (CFSG.Open.IsSubnormal.iff_subgroupOf hL).1 hsn
  have h2 : CFSG.Open.IsSubnormal (L.subgroupOf M) ⊤ := CFSG.Open.IsSubnormal.top_iff.2 h1
  have h3 := CFSG.Open.IsSubnormal.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) h2
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3
  exact h3

theorem isComponentOf_tl {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M D L : Subgroup G}
    (hD : Prop95Hyp p M D) (hL : GLAPComponent p M L)
    (hn : barX p M (gammaD D) ≤ Subgroup.normalizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hQ : ⁅gammaD D, GLAPPrimeCoreOf p M⁆ ≤ pCoreOf 2 M) :
    IsComponentOf (tl M L) ⊤ := by
  have hLM : L ≤ M := hL.1
  have hperfL : ⁅L, L⁆ = L := glaPComponent_perfect hL
  have hperfT : ⁅tl M L, tl M L⁆ = tl M L := by
    rw [← tl_commutator hLM hLM, hperfL]
  have hcomm : ⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆ = ⊥ :=
    commutator_tl_L_glaPPrimeCore_eq_bot hp hD hL hn hnc hQ
  have hle := pCore_two_le_glaPPrimeCore hp hp2 M
  have hmem : ∀ x : ↥(tl M L), projQ p M hle (x : Mt M) ∈ barX p M L := by
    intro x
    have hx : (x : Mt M) ∈ (L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := x.2
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx
    have e : projQ p M hle (x : Mt M) = QuotientGroup.mk' (GLAPPrimeCore p ↥M) m := by
      rw [← hmx]
      rfl
    rw [e]
    exact Subgroup.mem_map.2 ⟨m, hm, rfl⟩
  let f0 : ↥(tl M L) →* ↥(barX p M L) :=
    ((projQ p M hle).comp (tl M L).subtype).codRestrict (barX p M L) hmem
  have hsurj : Function.Surjective f0 := by
    intro z
    have hz : (z : ↥M ⧸ GLAPPrimeCore p ↥M) ∈
        (L.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore p ↥M)) := z.2
    obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 hz
    have hmt : (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m : Mt M) ∈ tl M L :=
      Subgroup.mem_map.2 ⟨m, hm, rfl⟩
    refine ⟨⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) m, hmt⟩, Subtype.ext ?_⟩
    change projQ p M hle (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) = (z : ↥M ⧸ GLAPPrimeCore p ↥M)
    rw [← hmz]
    rfl
  have hker : ∀ x ∈ f0.ker, x ∈ Subgroup.center ↥(tl M L) := by
    intro x hx
    have hx1 : projQ p M hle (x : Mt M) = 1 := by
      have h1 : f0 x = 1 := MonoidHom.mem_ker.1 hx
      exact congrArg Subtype.val h1
    have hx' : (x : Mt M) ∈ (L.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := x.2
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.1 hx'
    have hmQ : m ∈ GLAPPrimeCore p ↥M := by
      rw [← hmx] at hx1
      exact (QuotientGroup.eq_one_iff m).1 hx1
    have hxQ : (x : Mt M) ∈ tl M (GLAPPrimeCoreOf p M) := by
      rw [← hmx]
      exact Subgroup.mem_map.2
        ⟨m, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, hmQ, rfl⟩), rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hmem' : ⁅(g : Mt M), (x : Mt M)⁆ ∈ ⁅tl M L, tl M (GLAPPrimeCoreOf p M)⁆ :=
      Subgroup.commutator_mem_commutator g.2 hxQ
    rw [hcomm, Subgroup.mem_bot] at hmem'
    exact commutatorElement_eq_one_iff_mul_comm.1 hmem'
  have hperf : commutator ↥(tl M L) = ⊤ := by
    have h := subgroupOf_commutator (le_refl (tl M L)) (le_refl (tl M L))
    rw [hperfT, Subgroup.subgroupOf_self] at h
    exact h.symm
  have hY : CFSG.Open.IsQuasisimple ↥(barX p M L) := hL.2.2.1.2.2
  have hquasi : CFSG.Open.IsQuasisimple ↥(tl M L) :=
    isQuasisimple_of_central_quotient hsurj hperf hker hY
  exact ⟨le_top, isSubnormal_tl hLM hL.2.1, hquasi⟩

end Component

end CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
