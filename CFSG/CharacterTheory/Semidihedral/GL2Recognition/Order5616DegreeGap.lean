module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.DegreeTwelveClassicalAction
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.UniqueDegreeTwelveValues

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal

theorem order5616_degree_gap_classical_recognition {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 5616) (hperf : commutator G = ⊤) (h12 : Nat.card (ConjClasses G) = 12)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) {t : G} (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)))
    (χ : G → ℂ) (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 12)
    (hgap : ∀ ψ ∈ CFSG.BlocksIrr G, ψ ≠ 1 → ψ ≠ χ → ∃ d : ℕ, 12 < d ∧ ψ 1 = d) :
    ∃ M : Subgroup G, Nonempty (M ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
      Nat.card (M ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = 12 ∧
      (M ⊔ Subgroup.centralizer ({t} : Set G)).index = 13 ∧
      (∀ g : G, (∀ x : G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G)), g • x = x) → g = 1) ∧
      MulAction.IsMultiplyPretransitive G (G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G))) 2 ∧
      fixedPointCount G (G ⧸ (M ⊔ Subgroup.centralizer ({t} : Set G))) = 1 + χ ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 3 1 := by
  have huniq : ∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 12 → ψ = χ := by
    intro ψ hψ hψ1
    by_contra hne
    have hψne1 : ψ ≠ 1 := fun h => by
      rw [h, Pi.one_apply] at hψ1
      norm_num at hψ1
    obtain ⟨d, hd, hdψ⟩ := hgap ψ hψ hψne1 hne
    rw [hψ1] at hdψ
    have : d = 12 := by exact_mod_cast hdψ.symm
    omega
  obtain ⟨-, hfaith, -, horders, x, y, hx, hy, -, -, h3cls, hx3, hy0, hv2, hv48, hv6, -⟩ :=
    unique_degree_twelve_character_value_production hG hperf h12 hinv ht hC χ hχ hχ1 huniq
  obtain ⟨-, -, -, -, -, -, hlocal⟩ :=
    twelve_classes_produce_exponent_three_centralizer_data hG hperf h12 hinv ht hC
  obtain ⟨φ⟩ := hC
  have hprof := GL2_three_element_profile_and_derived_subgroup
  dsimp only at hprof
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hH3, -⟩ := hprof
  obtain ⟨⟨g3, hg3⟩⟩ := Nat.card_pos_iff.mp (by rw [hH3]; norm_num :
    0 < Nat.card {g : GL (Fin 2) (ZMod 3) // orderOf g = 3}) |>.1
  set a : G := ((φ.symm g3 : Subgroup.centralizer ({t} : Set G)) : G) with hadef
  have haC : a ∈ Subgroup.centralizer ({t} : Set G) := (φ.symm g3).2
  have ha : orderOf a = 3 := by
    rw [hadef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hg3]
  obtain ⟨hCa, P, hPa, hP, hexp, -⟩ := hlocal a haC ha
  refine degree_twelve_character_produces_thirteen_point_classical_action hG t ht ⟨φ⟩ a haC ha
    hCa P hPa hP hexp χ hχ hχ1 hgap hfaith hv2 (fun g hg => ?_) (fun g hg => ?_) hv6
  · have hcls : ∀ u v : G, IsConj u v → χ u = χ v := by
      intro u v huv
      obtain ⟨V, _, _, _, ρ, -, hρχ⟩ := hχ
      obtain ⟨c, hc⟩ := isConj_iff.mp huv
      rw [← hc, ← hρχ]
      exact (Representation.char_conj ρ u c).symm
    rcases h3cls g hg with h | h
    · right
      rw [hcls g x h, hx3]
    · left
      rw [hcls g y h, hy0]
  · rcases hg with hg | hg | hg
    · exact hv48 g (Or.inl hg)
    · exact hv48 g (Or.inr hg)
    · exfalso
      have := horders g
      rw [hg] at this
      simp at this

end CFSG.Semidihedral.GL2Recognition
