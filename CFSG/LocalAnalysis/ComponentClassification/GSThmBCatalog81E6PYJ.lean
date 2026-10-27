module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYT
public import CFSG.Sporadic.SmallOddCore.J2

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211Y

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211 P211X
open CFSG.Sporadic.SmallOddCore

theorem card_inf_centralizer_lt_of_rows {M : Type*} [Group M] {P R : Subgroup M} {ρ : Type*}
    (rows : List ρ) (rep : ρ → M) (cent : ρ → ℕ)
    (hcard : ∀ r ∈ rows, Nat.card ↥(P ⊓ centralizer ({rep r} : Set M)) = cent r)
    (hcover : ∀ t ∈ R, orderOf t = 2 → ∃ r ∈ rows, ∃ g ∈ P, t = g * rep r * g⁻¹)
    {N : ℕ} (hN : ∀ r ∈ rows, cent r < N) (τ : M) (hτ : τ ∈ R) (ho : orderOf τ = 2) :
    Nat.card ↥(P ⊓ centralizer ({τ} : Set M)) < N := by
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ hτ ho
  rw [inf_centralizer_conj P hg, card_map_of_injective (MulAut.conj g).injective, hcard r hr]
  exact hN r hr

theorem p211For_J2 :
    P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .J2 := by
  intro X _ _ hsimp hC ⟨e⟩ p f hp hp2 hf a J D _ _ _ _ hJt hJF hDJ hDsyl hbound b K hb hb1
    hKC hK hKt
  exfalso
  have e' : ↥(generalizedFitting X) ≃* Blueprint.NativeSporadic.J2 := e
  obtain ⟨-, -, -, hrows, hcover, -, hmap, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hN : ∀ r ∈ j2Rows, r.centOrder < 20160 := by
    intro r hr
    have hm := List.mem_map_of_mem (f := fun r : ClassRow => (r.outer, r.classSize, r.centOrder))
      hr
    rw [hmap] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
  have hlt := card_inf_centralizer_lt_of_rows j2Rows (fun r => tp 315 r.rep)
    (fun r => r.centOrder) (fun r hr => (hrows r hr).2.2.2.2.1) hcover hN
  refine p211_of_fixed_lt hC (outer_solvable_of_equiv e' Sporadic.Schreier.AT_J2_Schreier.2.2)
    (fun α hα2 hα1 => ?_) hp hp2 hf hb hb1 hKC hK hKt
  have hβ2 : MulAut.congr (e'.trans Sporadic.Schreier.j2PermEquiv) α *
      MulAut.congr (e'.trans Sporadic.Schreier.j2PermEquiv) α = 1 := by
    rw [← map_mul, hα2, map_one]
  have hβ1 : MulAut.congr (e'.trans Sporadic.Schreier.j2PermEquiv) α ≠ 1 := fun h =>
    hα1 ((MulAut.congr _).injective (h.trans (map_one _).symm))
  rw [← card_fixed_congr (e'.trans Sporadic.Schreier.j2PermEquiv) α]
  exact card_fixed_lt_of_autModel j2_autModel hlt _ hβ2 hβ1

end P211Y

end CFSG.ComponentClassification.GSThmB
