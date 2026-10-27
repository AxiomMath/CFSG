module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdExact
public import CFSG.ClassicalInvolution.Q3.TL4VtxDich
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Ex
public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

section Orbit

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {r n : ℕ}

omit [Finite Q] in
theorem tightCore_subgroupOf_orbGrp (h : TypeRFam r Φ) {K : Subgroup Q} (hK : K ∈ Φ) :
    tightCore (K.subgroupOf (Vtx.orbGrp Φ K)) = K.subgroupOf (Vtx.orbGrp Φ K) := by
  rw [tightCore_subgroupOf ((tightCore_le K).trans (Vtx.le_orbGrp K))]
  congr 1
  exact h.closure_twoElts hK

theorem not_tightEdgeless_orbGrp (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore Q = ⊥) (hn : Nat.card Q < n) {K M : Subgroup Q}
    (hK : K ∈ Φ) (hM : M ∈ omegaNbr Φ K) {g : Q} (hg : g ∈ omegaGen Φ)
    (hgM : conjSub g K = M) : ¬ TightEdgeless (K.subgroupOf (Vtx.orbGrp Φ K)) := by
  have hcl := h.hyp.conjInvariant
  have hKX : K ≤ Vtx.orbGrp Φ K := Vtx.le_orbGrp K
  obtain ⟨k, hk, e⟩ :=
    Vtx.exists_orbGrp_conj hcl hK (Vtx.commute_conj_of_not_conj h4 h hO hn hK) hg
  have hMX : M ≤ Vtx.orbGrp Φ K := by
    rw [← hgM, e]
    exact Vtx.conjSub_le_orbGrp K ⟨k, Vtx.orbGrp_le hcl hK hk⟩
  have hM' : M.subgroupOf (Vtx.orbGrp Φ K) ∈
      CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)) := by
    refine ⟨⟨k, hk⟩, ?_⟩
    show conjSub (⟨k, hk⟩ : ↥(Vtx.orbGrp Φ K)) (K.subgroupOf (Vtx.orbGrp Φ K)) =
      M.subgroupOf (Vtx.orbGrp Φ K)
    rw [conjSub_subgroupOf, ← e, hgM]
  obtain ⟨hMΦ, hne, T, hT, hTM, hTN⟩ := hM
  have hTsyl : IsSylow2In T M := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hMΦ hT hTM
  have hnbr : M.subgroupOf (Vtx.orbGrp Φ K) ∈
      omegaNbr (CoreAssembly.conjClass (K.subgroupOf (Vtx.orbGrp Φ K)))
        (K.subgroupOf (Vtx.orbGrp Φ K)) :=
    ⟨hM', subgroupOf_ne_of_ne hKX hMX hne, T.subgroupOf (Vtx.orbGrp Φ K),
      mem_RSet_of_isSylow2In hM' (hTsyl.subgroupOf hMX),
      fun x hx => Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hx)),
      fun x hx => (mem_normalizer_subgroupOf_iff hKX).mp (hTN (Subgroup.mem_subgroupOf.mp hx))⟩
  intro hE
  have hE' : Disconnected.DEdgeless
      (CoreAssembly.conjClass (tightCore (K.subgroupOf (Vtx.orbGrp Φ K)))) := hE
  rw [tightCore_subgroupOf_orbGrp h hK] at hE'
  exact hE' _ (CoreAssembly.mem_conjClass_self _) _ hM' (Or.inl hnbr)

end Orbit

section Cit3


theorem secIdent3_of {n : ℕ} (hS : SecIdentDatum3 n) (h4 : Thm4RBelow 3 n) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam 3 Φ →
      classicalInvolutionOddCore X = ⊥ → ∀ K ∈ Φ, ∀ z : X, ∀ hz : IsUniqueInvolution K z,
        ∃ S' : Sylow 2 ↥(K.subgroupOf (Vtx.orbGrp Φ K)),
          TightDatum (K.subgroupOf (Vtx.orbGrp Φ K)) S' ⟨z, Vtx.le_orbGrp K hz.mem⟩ ∧
          TightCls ↥(Vtx.orbGrp Φ K) (K.subgroupOf (Vtx.orbGrp Φ K)) S'
            ⟨z, Vtx.le_orbGrp K hz.mem⟩ ∧
          SecIdentOut3 ↥(Vtx.orbGrp Φ K) (K.subgroupOf (Vtx.orbGrp Φ K))
            ⟨z, Vtx.le_orbGrp K hz.mem⟩ := by
  intro X _ _ hn Φ h hO K hK z hz
  obtain ⟨S', hd, hc⟩ := Vtx.tightCls_orbGrp h4 h hO hn hK hz
  exact ⟨S', hd, hc, hS _ (lt_of_le_of_lt (Subgroup.card_le_card_group _) hn) _ S' _ hd hc⟩

variable {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)} {n : ℕ}

theorem isPGroup_of_mem_omegaNbr_conj (hS : SecIdentDatum3 n) (h4 : Thm4RBelow 3 n)
    (hE4 : SecIdE4OddCent) (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore Q = ⊥)
    (hn : Nat.card Q < n) {K M : Subgroup Q} (hK : K ∈ Φ) (hM : M ∈ omegaNbr Φ K) {g : Q}
    (hg : g ∈ omegaGen Φ) (hgM : conjSub g K = M) : IsPGroup 2 ↥K := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
  obtain ⟨S', hd, hc, hout⟩ := secIdent3_of hS h4 Q hn Φ h hO K hK z hz
  have h2 := isPGroup_core_of_secIdentOut3 hE4 hd hc hout
    (not_tightEdgeless_orbGrp h4 h hO hn hK hM hg hgM)
  rw [tightCore_subgroupOf_orbGrp h hK] at h2
  exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe (Vtx.le_orbGrp K))

theorem tightSecExactR_three_of (hS : SecIdentDatum3 n) (h4 : Thm4RBelow 3 n)
    (hE4 : SecIdE4OddCent) : TightSecExactR 3 n := by
  intro X _ _ hn Φ h hO hgen _ L hL M hM ⟨g, hg⟩
  refine oddCore_eq_bot_of_isPGroup
    (isPGroup_of_mem_omegaNbr_conj hS h4 hE4 h hO hn hL hM ?_ hg)
  rw [hgen]
  exact Subgroup.mem_top g

end Cit3

theorem tightLambdaCommR_of_exact {r n : ℕ} (hE : TightSecExactR r n) (h4 : Thm4RBelow r n) :
    TightLambdaCommR r n := by
  intro X _ _ hn Φ hΦ hO hgen hA L hL M hM
  by_cases hc : ∃ g : X, conjSub g L = M
  · obtain ⟨g, hg⟩ := hc
    have hLM : L ∈ omegaNbr Φ M := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ.hyp hL hM.1 hM
    exact commutes_of_exact hΦ hL hM (hE X hn Φ hΦ hO hgen hA L hL M hM ⟨g, hg⟩)
      (hE X hn Φ hΦ hO hgen hA M hM.1 L hLM ⟨g⁻¹, by rw [← hg, conjSub_inv_conjSub]⟩)
  · exact Vtx.commutes_of_not_conj h4 hΦ hO hn hL hM.1 fun ⟨g, _, hg⟩ => hc ⟨g, hg⟩

section Plus


theorem tightLambdaCommR_three_of_plus {n : ℕ} (hP : TightBelowRPlus 3 n) (hA : CIT3Below n)
    (h4 : Thm4RBelow 3 n) (hE4 : SecIdE4OddCent) : TightLambdaCommR 3 n :=
  tightLambdaCommR_of_exact (tightSecExactR_three_of (secIdentDatum3_of hP hA) h4 hE4) h4

end Plus

end CFSG.ClassicalInvolution.Q3.TL4
