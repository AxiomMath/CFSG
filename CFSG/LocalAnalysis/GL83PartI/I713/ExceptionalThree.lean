module

public import CFSG.GH74.Filter.Lie.TwistedE6Odd
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankSL2

public section

namespace GL83.I713

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg.Adjoint CFSG.GH74.Filter.Lie CFSG.SectionRank
  CFSG.LocalAnalysis.ComponentInitial

theorem four_le_pRank_three_of_untwistedModel_E6
    {S : Type} [Group S] [Finite S] {q : ℕ}
    (h : UntwistedChevalleyModel S .E6 q) : 4 ≤ pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
  have : Finite (AdjointQuotient .E6 K) := Finite.of_equiv S e.toEquiv
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact four_le_pRank_three_adjointQuotient_any (Or.inr (Or.inl rfl))

section TwistedOdd

set_option linter.unusedSectionVars false


noncomputable def sl2E6Prime {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    SL2 (ZMod p) →* adjointGroup TwistTag.E6.tag K :=
  ((simpleRootSL2 TwistTag.E6.tag K e6Fix).comp
    (Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl p) K))).codRestrict _
    fun _ => simpleRootSL2_mem_adjointGroup e6Fix _

noncomputable def sl2E6 {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (k : Fin 4) :
    SL2 (ZMod p) →* adjointGroup TwistTag.E6.tag K :=
  (MulAut.conj (nrep TwistTag.E6.tag K (e6w k))).toMonoidHom.comp (sl2E6Prime p)

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem sl2E6Prime_uSL (c : ZMod p) :
    sl2E6Prime (K := K) p (uSL c) = xElement e6Fix (ZMod.castHom (dvd_refl p) K c) := by
  apply Subtype.ext
  change simpleRootSL2 _ K e6Fix (Matrix.SpecialLinearGroup.map _ (uSL c)) = _
  rw [sl2_map_uSL, simpleRootSL2_uSL]
  rfl

theorem sl2E6Prime_WSL : sl2E6Prime (K := K) p WSL = weylElement TwistTag.E6.tag K e6Fix := by
  apply Subtype.ext
  change simpleRootSL2 _ K e6Fix (Matrix.SpecialLinearGroup.map _ WSL) = _
  rw [sl2_map_WSL, simpleRootSL2_WSL]
  rfl

theorem sl2E6Prime_mem_twistDerived (σ : K →+* K) (A : SL2 (ZMod p)) :
    sl2E6Prime p A ∈ twistDerived .E6 K σ := by
  have hu : ∀ c, sl2E6Prime (K := K) p (uSL c) ∈ twistDerived .E6 K σ := fun c => by
    rw [sl2E6Prime_uSL]
    exact e6_xElement_three_mem (ringHom_zmod_cast σ c)
  have hn : weylElement TwistTag.E6.tag K e6Fix ∈ twistFixed .E6 K σ := by
    rw [mem_twistFixed, twistC_weylElement, e6Fix_perm]
  have hv : ∀ c, sl2E6Prime (K := K) p (vSL c) ∈ twistDerived .E6 K σ := fun c => by
    rw [sl2_vSL_eq_conj, map_mul, map_mul, map_inv, sl2E6Prime_WSL]
    exact conj_mem_twistDerived hn (hu (-c))
  have hle : (⊤ : Subgroup (SL2 (ZMod p))) ≤
      (twistDerived .E6 K σ).comap (sl2E6Prime (K := K) p) := by
    rw [← sl2_closure_upper_lower]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hu c
    · exact hv c
  exact hle (Subgroup.mem_top A)

theorem sl2E6Prime_injective (hK : ringChar K ≠ 2) : Function.Injective (sl2E6Prime (K := K) p) :=
  fun _ _ h => sl2_map_injective (ZMod.castHom (dvd_refl p) K)
    (simpleRootSL2_injective hK e6Fix (congrArg Subtype.val h))

theorem sl2E6_mem_twistDerived (σ : K →+* K) (k : Fin 4) (A : SL2 (ZMod p)) :
    sl2E6 p k A ∈ twistDerived .E6 K σ :=
  conj_mem_twistDerived (nrep_mem_twistFixed' (e6w_fixed k)) (sl2E6Prime_mem_twistDerived σ A)

theorem sl2E6_injective (hK : ringChar K ≠ 2) (k : Fin 4) :
    Function.Injective (sl2E6 (K := K) p k) :=
  (MulAut.conj (nrep TwistTag.E6.tag K (e6w k))).injective.comp (sl2E6Prime_injective hK)

theorem sl2E6_mem_rootRankOneGroup (k : Fin 4) (hk : IsRoot TwistTag.E6.tag (e6Vec k))
    (A : SL2 (ZMod p)) :
    (sl2E6 (K := K) p k A).1 ∈ rootRankOneGroup TwistTag.E6.tag K (e6Vec k) := by
  set B := Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl p) K) A
  have h1 : simpleRootSL2 TwistTag.E6.tag K e6Fix B ∈ Subgroup.closure
      (Set.range (xUnit TwistTag.E6.tag K e6Fix) ∪ Set.range (yUnit TwistTag.E6.tag K e6Fix)) := by
    rw [← range_simpleRootSL2]
    exact ⟨B, rfl⟩
  have h2 := Subgroup.mem_map_of_mem
    (MulAut.conj (canonicalRep (coxeterSystem TwistTag.E6.tag) K (e6w k))).toMonoidHom h1
  rw [map_conj_canonicalRep_closure_xUnit_yUnit (e6w_smul k)] at h2
  rw [(exceptional_Lang_root_rank_one_torus_transport TwistTag.E6.tag K hk).1]
  exact h2

theorem sl2E6_commute {k l : Fin 3} (hkl : k ≠ l) (A B : SL2 (ZMod p)) :
    Commute (sl2E6 (K := K) p k.castSucc A) (sl2E6 (K := K) p l.castSucc B) := by
  obtain ⟨hβ, hγ, h0, hp, hm⟩ := stronglyOrthB_spec (e6Vec_stronglyOrth k l hkl)
  refine Subtype.ext ?_
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation TwistTag.E6.tag K hβ hγ h0
    hp hm _ (sl2E6_mem_rootRankOneGroup k.castSucc hβ A) _
    (sl2E6_mem_rootRankOneGroup l.castSucc hγ B)

theorem two_le_pRank_three_derivedQuotient_twistedE6_odd (hp2 : p ≠ 2) (σ : K →+* K)
    [Finite (commutator (twistFixed .E6 K σ) ⧸ Subgroup.center (commutator (twistFixed .E6 K σ)))] :
    2 ≤ pRank 3 (⊤ : Subgroup
      (commutator (twistFixed .E6 K σ) ⧸ Subgroup.center (commutator (twistFixed .E6 K σ)))) := by
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  choose ψ hψ using fun k : Fin 3 =>
    exists_hom_commutator (σ := σ) (sl2E6 (K := K) p k.castSucc)
      (sl2E6_mem_twistDerived σ k.castSucc)
  have hinj : ∀ k : Fin 3, Function.Injective (ψ k) := fun k A B h => by
    apply sl2E6_injective hK k.castSucc
    rw [← hψ k A, ← hψ k B, h]
  refine CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank.two_le_pRank_three_of_sl2_pair
    (QuotientGroup.mk' (Subgroup.center _)) (fun z hz => (QuotientGroup.eq_one_iff z).1 hz)
    (ψ 0) (ψ 1) (hinj 0) (hinj 1) fun s t => ?_
  have h1 := (sl2E6_commute (K := K) (p := p) (k := 0) (l := 1) (by decide) s t).eq
  rw [← hψ 0 s, ← hψ 1 t] at h1
  exact Subtype.ext (Subtype.ext h1)

end TwistedOdd

theorem two_le_pRank_three_of_twistedE6Model
    {S : Type} [Group S] [Finite S] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hm : TwistedChevalleyModel S .E6 (p ^ f)) : 2 ≤ pRank 3 (⊤ : Subgroup S) := by
  by_cases hp2 : p = 2
  · subst hp2
    exact (by norm_num : 2 ≤ 4).trans (four_le_pRank_three_of_twistedE6Model_two hf hm)
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨K, _, _, _, σ, -, -, -, -, -, ⟨e⟩⟩ := twistedModel_data hf hm
    let e' := e.trans (derivedCentralQuotientEquiv _ (twistedFixedGroupEquiv .E6 K σ))
    have : Finite (commutator (twistFixed .E6 K σ) ⧸
        Subgroup.center (commutator (twistFixed .E6 K σ))) := Finite.of_equiv S e'.toEquiv
    rw [pRank_top_eq_of_mulEquiv (by norm_num) e']
    exact two_le_pRank_three_derivedQuotient_twistedE6_odd hp2 σ

end GL83.I713
