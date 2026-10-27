module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Reduce
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndTypes

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Assembly

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem nontrivial_of_ne_bot {K : Subgroup (MulAut V)} (hK : K ≠ ⊥) : Nontrivial V := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply hK
  rw [eq_bot_iff]
  intro k _
  rw [Subgroup.mem_bot]
  ext v
  exact Subsingleton.elim _ _

theorem exists_diagMinInv [Nontrivial V] (K : Subgroup (MulAut V)) :
    ∃ W : Subgroup V, DiagMinInv K W := by
  classical
  have hne : (⊤ : Subgroup V) ≠ ⊥ := by
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro h
    obtain ⟨a, b, hab⟩ := exists_pair_ne V
    exact hab ((h a (Subgroup.mem_top a)).trans (h b (Subgroup.mem_top b)).symm)
  have hex : ∃ n : ℕ, ∃ W : Subgroup V, W ≠ ⊥ ∧ GInv K W ∧ Nat.card ↥W = n :=
    ⟨_, ⊤, hne, fun _ _ _ _ => Subgroup.mem_top _, rfl⟩
  obtain ⟨W, hW0, hWinv, hWn⟩ := Nat.find_spec hex
  refine ⟨W, hW0, hWinv, fun A hA hAW => ?_⟩
  by_cases hA0 : A = ⊥
  · exact Or.inl hA0
  · right
    have hle : Nat.card ↥W ≤ Nat.card ↥A := by
      rw [hWn]
      exact Nat.find_min' hex ⟨A, hA0, hA, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hAW hle

theorem diagFree_of_parts (hR : DiagReduction) (hI : DiagMod_irr) (hAlt : DiagMod_alt)
    (hMinus : DiagMod_minus) (hCore : DiagMod_core) (hNat : DiagMod_nat)
    (hCount : DiagMod_count) : DiagFree := by
  intro V _ _ hV G T Y cfg h9 hL hirr hno
  obtain ⟨K, K', t, h⟩ := hR V hV G T Y cfg h9 hL hirr hno
  have hLirr := hI V hV G T Y K K' t h
  let hP : DiagPair K K' Y t := { h.toDiagPre with irr := hLirr }
  have hKperf : Group.IsPerfect ↥K := ⟨h.quasi.1⟩
  have hK1 : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKperf
  have hKne : K ≠ ⊥ := by
    have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.quasi.2
    have : Nontrivial (↥K ⧸ Subgroup.center ↥K) := IsSimpleGroup.toNontrivial
    have : Nontrivial ↥K :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance
  rcases h.cls with hX | ⟨n, hn, hΩ⟩
  · rcases types_of_classX hV h.perfY h.centerY hX with ⟨f, hf, hYSL⟩ | ⟨m, hm, hmodd, hYAlt⟩
    · rcases natSection_of_classX hV h.perfY hX hf hYSL with hsl | ⟨-, halt⟩
      · have hco : DiagCoreOut K K' f := hCore V hV K K' Y t hP f hf hsl
        have : Nontrivial V := nontrivial_of_ne_bot hKne
        obtain ⟨W, hW⟩ := exists_diagMinInv (V := V) K
        obtain ⟨θ, hθ, k₀, hk₀, hdis, hsup⟩ := hco.split W hW
        have hK'perf : ⁅K', K'⁆ = K' := by
          rw [h.Kconj, ← Subgroup.map_commutator, hK1]
        have hcard : Nat.card ↥K' = Nat.card ↥K := by
          rw [h.Kconj]
          exact (Nat.card_congr
            (K.equivMapOfInjective _ (MulAut.conj t).injective).toEquiv).symm
        have hnat := hNat V hV K K' f hf h.comm hK'perf hcard θ W hθ k₀ hk₀ hdis hsup
        have hcount := hCount V hV K K' Y t hP f hf hsl hco
        apply cfg.nolift
        refine ⟨K ⊔ K', ?_⟩
        have hXG : K ⊔ K' ≤ G := h.L_eq ▸ conjClosure_le h.Y_le
        have hn : ((K ⊔ K').subgroupOf G).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hXG).mpr
            (h.L_eq ▸ le_normalizer_conjClosure)
        refine ⟨?_, hXG, hn.isSubnormal, Or.inr ⟨f, hf, Or.inl hnat, Or.inr ⟨hX, hYSL, hcount⟩⟩⟩
        intro y hy
        obtain ⟨k, hk, rfl⟩ := (h.Y_mem y).1 hy
        refine Subgroup.mul_mem_sup hk ?_
        rw [h.Kconj]
        exact Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply]⟩
      · exact hAlt V hV K K' Y t hP (Or.inl ⟨5, le_rfl, by decide, halt⟩)
    · exact hAlt V hV K K' Y t hP (Or.inr ⟨hX, m, hm, hmodd, hYAlt⟩)
  · exact hMinus V hV K K' Y t hP n hn hΩ

end Assembly

end CFSG.CGT.PushingUpLit.CGT6
