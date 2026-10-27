module

public import CFSG.GH74.Generic.S45.PerfWitSpec
public import CFSG.GH74.Generic.S45.LSporRows
public import CFSG.GH74.Generic.S45.LEvenBender
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.McLAut
public import Certificates.Certificate5148

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.GH74.Uniqueness.Bender CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem perfWit_of_all {rows : List ClassRow} {c n : ℕ} {W : PerfWit}
    (h : (rows.all fun r => r.centOrder != c || perfWitOK n r.centGens W) = true) :
    ∀ r ∈ rows, r.centOrder = c → perfWitOK n r.centGens W = true := by
  intro r hr hc
  have := List.all_eq_true.1 h r hr
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  rcases this with h1 | h1
  · exact absurd hc h1
  · exact h1

theorem perfWit_j3_2A :
    (j3Rows.all fun r => r.centOrder != 1920 || perfWitOK 6156 r.centGens j3PerfWit2A) = true :=
  Certificates.certificate5148.1

theorem perfWit_mcl_2A :
    (mclRows.all fun r => r.centOrder != 40320 || perfWitOK 275 r.centGens mclPerfWitIn) = true :=
  Certificates.certificate5148.2.1

theorem perfWit_mcl_outer :
    (mclRows.all fun r => r.centOrder != 7920 || perfWitOK 275 r.centGens mclPerfWitOut) = true :=
  Certificates.certificate5148.2.2.1

theorem perfWit_j2_2A :
    (j2Rows.all fun r => r.centOrder != 1920 || perfWitOK 315 r.centGens j2PerfWit2A) = true :=
  Certificates.certificate5148.2.2.2

theorem mcl_perfOrd4 :
    ∀ r ∈ mclRows, PerfOrd4 mclP (tp 275 r.rep) := by
  obtain ⟨-, -, -, hrows, -, -, hmap, -⟩ := mcl_involution_centralizers
  intro r hr
  obtain ⟨-, -, -, hCeq, -, -⟩ := hrows r hr
  have hco : r.centOrder = 40320 ∨ r.centOrder = 7920 := by
    have hm : (r.outer, r.classSize, r.centOrder) ∈
        List.map (fun r => (r.outer, r.classSize, r.centOrder)) mclRows := List.mem_map_of_mem hr
    rw [hmap] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases hco with h | h
  · exact perfOrd4_of_perfWit (by norm_num) (perfWit_of_all perfWit_mcl_2A r hr h) hCeq
  · exact perfOrd4_of_perfWit (by norm_num) (perfWit_of_all perfWit_mcl_outer r hr h) hCeq

theorem sporRow_mcl :
    SporRow .McL := by
  refine sporRow_of_perfect_order_four .McL fun S _ e α h2 h1 => ?_
  obtain ⟨eR, heR, -⟩ := mcl_full_automorphism_model
  obtain ⟨-, -, -, -, hcover, -⟩ := mcl_involution_centralizers
  refine exists_perfect_order_four_of_equiv (e.trans mclPermEquiv) eR heR
    (mclRows.map fun r => tp 275 r.rep) ?_ ?_ α h2 h1
  · intro t ht ho
    obtain ⟨r, hr, g, hg, hrt⟩ := hcover t ht ho
    exact ⟨tp 275 r.rep, List.mem_map_of_mem hr, g, hg, hrt⟩
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact mcl_perfOrd4 r' hr'

theorem j3_perfOrd4_1920 :
    ∀ r ∈ j3Rows, Nat.card ↥(j3P ⊓ Subgroup.centralizer ({tp 6156 r.rep} :
      Set (Equiv.Perm (Fin 6156)))) = 1920 → PerfOrd4 j3P (tp 6156 r.rep) := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  intro r hr hc
  obtain ⟨-, -, -, hCeq, hcard, -⟩ := hrows r hr
  have hco : r.centOrder = 1920 := hcard.symm.trans hc
  exact perfOrd4_of_perfWit (by norm_num) (perfWit_of_all perfWit_j3_2A r hr hco) hCeq

theorem sporRowCls_j3_1920 :
    SporRowCls .J3 1920 := by
  refine sporRowCls_of_perfect_order_four .J3 1920 fun S _ e α h2 h1 hcard => ?_
  obtain ⟨eR, heR, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, -, hcover, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have e' : S ≃* NativeSporadic.J3 := e
  refine exists_perfect_order_four_of_equiv_card 1920 (e'.trans j3PermEquiv) eR heR
    (j3Rows.map fun r => tp 6156 r.rep) ?_ ?_ α h2 h1 hcard
  · intro t ht ho
    obtain ⟨r, hr, g, hg, hrt⟩ := hcover t ht ho
    exact ⟨tp 6156 r.rep, List.mem_map_of_mem hr, g, hg, hrt⟩
  · intro r hr hc
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact j3_perfOrd4_1920 r' hr' hc

theorem j2_perfOrd4_1920 :
    ∀ r ∈ j2Rows, Nat.card ↥(j2P ⊓ Subgroup.centralizer ({tp 315 r.rep} :
      Set (Equiv.Perm (Fin 315)))) = 1920 → PerfOrd4 j2P (tp 315 r.rep) := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  intro r hr hc
  obtain ⟨-, -, -, hCeq, hcard, -⟩ := hrows r hr
  have hco : r.centOrder = 1920 := hcard.symm.trans hc
  exact perfOrd4_of_perfWit (by norm_num) (perfWit_of_all perfWit_j2_2A r hr hco) hCeq

theorem sporRowCls_j2_1920 :
    SporRowCls .J2 1920 := by
  refine sporRowCls_of_perfect_order_four .J2 1920 fun S _ e α h2 h1 hcard => ?_
  obtain ⟨eR, heR, -⟩ := ctuc_j2_full_automorphism_permutation_model
  obtain ⟨-, -, -, -, hcover, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have e' : S ≃* NativeSporadic.J2 := e
  refine exists_perfect_order_four_of_equiv_card 1920 (e'.trans j2PermEquiv) eR heR
    (j2Rows.map fun r => tp 315 r.rep) ?_ ?_ α h2 h1 hcard
  · intro t ht ho
    obtain ⟨r, hr, g, hg, hrt⟩ := hcover t ht ho
    exact ⟨tp 315 r.rep, List.mem_map_of_mem hr, g, hg, hrt⟩
  · intro r hr hc
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact j2_perfOrd4_1920 r' hr' hc

theorem j2_cover_row
    {K : Type} [Group K] [Finite K] {y : MulAut K} {L : Subgroup K}
    (hyp : Hyp1310 K y L) (e : K ⧸ Subgroup.center K ≃* NativeSporadic.J2) :
    Subgroup.center K ≠ ⊥ → ∀ k : K, y = MulAut.conj k →
      Nat.card (Subgroup.centralizer ({(QuotientGroup.mk k : K ⧸ Subgroup.center K)} :
        Set (K ⧸ Subgroup.center K))) = 1920 → False := by
  intro _ k hk hcard
  refine sporRowCls_j2_1920 K y L hyp ⟨e⟩ (MulAut.conj (QuotientGroup.mk k)) ?_ ?_
  · intro k'
    rw [hk, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  · rw [autFixed_conj_eq_centralizer]
    exact hcard

end CFSG.GH74.Generic.S45
