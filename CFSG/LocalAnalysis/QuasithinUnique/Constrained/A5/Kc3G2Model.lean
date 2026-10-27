module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2Chain

public section

namespace CFSG.QuasithinUnique.A5.Kc3G2

open CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem bt2_of_holds (K : Subgroup G) (h : CFSG.LieType.BorelTits.Holds ↥K 2) : BT2 K := by
  intro W hWK hW0 hW2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' : Subgroup ↥K := W.subgroupOf K with hW'
  have hW'W : W'.map K.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWK
  have hW'0 : W' ≠ ⊥ := by
    intro hbot
    apply hW0
    rw [← hW'W, hbot, Subgroup.map_bot]
  have hW'2 : IsPGroup 2 ↥W' := hW2.comap_subtype
  obtain ⟨S', P', hP'top, hNP', -, hWP', hSP'⟩ := h W' hW'0 hW'2
  refine ⟨(S' : Subgroup ↥K).map K.subtype, P'.map K.subtype, ?_, Subgroup.map_subtype_le _, ?_,
    ?_, ?_, ?_⟩
  · exact isSylowTwoOf_iff_isSylowOf.2 ⟨S', rfl⟩
  · intro hPK
    apply hP'top
    have h1 : (P'.map K.subtype).subgroupOf K = P' := by
      show (P'.map K.subtype).comap K.subtype = P'
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective P'
    rw [← h1]
    exact Subgroup.subgroupOf_eq_top.2 hPK.ge
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥K) ∈ Subgroup.normalizer (W' : Set ↥K) := by
      rw [hW', normalizer_subgroupOf_eq' hWK]
      exact Subgroup.mem_subgroupOf.2 hx
    exact ⟨⟨x, hx.1⟩, hNP' hxN, rfl⟩
  · rw [← hW'W]
    exact (Subgroup.map_mono hWP').trans
      (CFSG.LieType.BorelTits.map_pCoreOf_le (r := 2) K.subtype P')
  · exact Subgroup.map_mono (Subgroup.le_normalizer.trans hSP')

theorem dInf_eq_perfectCore' (M : Subgroup G) : dInf M = perfectCore M :=
  le_antisymm
    (le_perfectCore_of_perfect (dInf_le M) (Subgroup.isPerfect_iff.mp (dInf_isPerfect M)))
    (le_dInf_of_perfect (Subgroup.isPerfect_iff.mpr (perfectCore_perfect M)) (perfectCore_le M))

theorem lat2_of_lattice (K : Subgroup G)
    (h : ∀ U' : Subgroup ↥K, IsSylowTwoOf U' ⊤ → ∃ P' Q' : Fin 2 → Subgroup ↥K,
      ResidualOvergroupsAt ↥K U' P' ∧ ∀ j, ParabolicFacts (P' j) (Q' j)) : Lat2 K := by
  intro U P hU hUP hPK hPtop
  obtain ⟨P', Q', hlat, hPF⟩ := h _ (isSylowTwoOf_subgroupOf_top hU)
  obtain ⟨-, -, hmax, -, hC2, -⟩ := hlat
  have hP₁top : P.subgroupOf K ≠ ⊤ := fun h1 =>
    hPtop (le_antisymm hPK (Subgroup.subgroupOf_eq_top.1 h1))
  have hUP₁ : U.subgroupOf K ≤ P.subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hUP (Subgroup.mem_subgroupOf.1 hx))
  obtain ⟨M', hM'ge, hM'cov⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.2 hP₁top)
  obtain ⟨k, hk⟩ := (hmax M' (hUP₁.trans hM'ge)).1 hM'cov
  have hP₁k : P.subgroupOf K ≤ P' k := hk ▸ hM'ge
  refine ⟨(P' k).map K.subtype, (Q' k).map K.subtype,
    (hPF k).map K.subtype K.subtype_injective, ?_, Subgroup.map_subtype_le _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hPK hx⟩, hP₁k (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · intro M hUM hMP hMns
    have hMK : M ≤ K := hMP.trans hPK
    have hUM₁ : U.subgroupOf K ≤ M.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hUM (Subgroup.mem_subgroupOf.1 hx))
    have hM₁P : M.subgroupOf K ≤ P.subgroupOf K := fun x hx =>
      Subgroup.mem_subgroupOf.2 (hMP (Subgroup.mem_subgroupOf.1 hx))
    have hM₁top : M.subgroupOf K ≠ ⊤ := fun h1 => hP₁top (top_le_iff.1 (h1 ▸ hM₁P))
    have hM₁ns : ¬ Group.IsSolvable ↥(M.subgroupOf K) := by
      intro hs
      apply hMns
      let e : ↥M ≃* ↥(M.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hMK).symm
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    obtain ⟨j, hj, hd⟩ := hC2 _ hUM₁ hM₁top hM₁ns
    have hjk : k = j := (hj k).1 (hM₁P.trans hP₁k)
    subst hjk
    have e1 : (M.subgroupOf K).map K.subtype = M := Subgroup.map_subgroupOf_eq_of_le hMK
    rw [← e1, ← map_perfectCore, ← dInf_eq_perfectCore', hd, dInf_eq_perfectCore',
      map_perfectCore]

end CFSG.QuasithinUnique.A5.Kc3G2
