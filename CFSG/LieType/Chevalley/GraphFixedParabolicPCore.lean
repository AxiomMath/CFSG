module

public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section PCore

variable {G : Type*} [Group G] (p : ℕ)

theorem le_pCore_map_subtype {P N : Subgroup G} (hNP : N ≤ P) (hN : (N.subgroupOf P).Normal)
    (hp : IsPGroup p N) : N ≤ (CFSG.pCore p P).map P.subtype := by
  have hle : N.subgroupOf P ≤ CFSG.pCore p P :=
    le_sSup ⟨hN, hp.comap_of_injective P.subtype Subtype.val_injective⟩
  exact fun x hx => ⟨⟨x, hNP hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem pCore_map_subtype_le [Fact p.Prime] {P C U : Subgroup G} (hUP : U ≤ P) (hPC : P ≤ C)
    (hU : IsPGroup p U) (hidx : ¬ p ∣ U.relIndex C) : (CFSG.pCore p P).map P.subtype ≤ U := by
  have hU' : IsPGroup p (U.subgroupOf P) := hU.comap_of_injective P.subtype Subtype.val_injective
  have hidx' : ¬ p ∣ (U.subgroupOf P).index := fun h =>
    hidx (h.trans ⟨P.relIndex C, (Subgroup.relIndex_mul_relIndex U P C hUP hPC).symm⟩)
  have hle := IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := p) (G := P))
    (hU'.toSylow hidx')
  rw [← Subgroup.map_subgroupOf_eq_of_le hUP]
  exact Subgroup.map_mono hle

end PCore

section Radical


theorem parabolicLevi_inf_posUnipotent_le {τ : Tag} {K : Type} [Field K] (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ⊓ posUnipotent τ K ≤ parabolicLeviUnipotent τ K J := by
  intro g hg
  obtain ⟨hgM, hgU⟩ := Subgroup.mem_inf.1 hg
  have hg' : g ∈ (posUnipotent τ K : Set (ModGL τ K)) := hgU
  rw [posUnipotent_eq_mul_parabolic J] at hg'
  obtain ⟨q, hq, v, hv, hqv⟩ := hg'
  have hgq : g = q * v := hqv.symm
  have hqM : q ∈ parabolicLevi τ K J := by
    have := mul_mem hgM (inv_mem (parabolicLeviUnipotent_le_parabolicLevi J hv))
    rwa [hgq, mul_inv_cancel_right] at this
  have hq1 : q ∈ parabolicRadical τ K J ⊓ parabolicLevi τ K J := Subgroup.mem_inf.2 ⟨hq, hqM⟩
  rw [parabolicRadical_inf_parabolicLevi, Subgroup.mem_bot] at hq1
  rw [hgq, hq1, one_mul]
  exact hv

theorem pCore_graphFixedParabolic_le_of_conj (t : TwistTag) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) {n : ModGL t.tag K}
    (hn : n ∈ graphFixedParabolic t K σ.toRingHom J)
    (hV : (parabolicLeviUnipotent t.tag K (t.orbitUnion J)).map (MulAut.conj n).toMonoidHom ≤
      negUnipotent t.tag K) :
    (CFSG.pCore (ringChar K) (graphFixedParabolic t K σ.toRingHom J)).map
        (graphFixedParabolic t K σ.toRingHom J).subtype ≤
      graphFixedParabolicRadical t K σ.toRingHom J := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have hσ : Function.Surjective σ.toRingHom := σ.surjective
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQN, hLP, hfac, -, -, -, -, hpg, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  have hPC : graphFixedParabolic t K σ.toRingHom J ≤ graphFixedRootGroup t K σ.toRingHom :=
    graphFixedParabolic_le t K σ.toRingHom J
  have hPΓ : graphFixedParabolic t K σ.toRingHom J ≤ twistedFixedGroup t K σ.toRingHom :=
    hPC.trans (graphFixedRootGroup_le t K σ.toRingHom)
  have hUP : graphFixedPosUnipotent t K σ.toRingHom ≤ graphFixedParabolic t K σ.toRingHom J :=
    graphFixedPosUnipotent_le_graphFixedRootBorel.trans
      (graphFixedRootBorel_le_graphFixedParabolic t K σ.toRingHom J)
  have hRU := pCore_map_subtype_le (ringChar K) hUP hPC
    ((isPGroup_posUnipotent (K := K) (ringChar K) t.tag).to_le inf_le_left)
    (not_dvd_index_graphFixedPosUnipotent (ringChar K) hσ)
  have hQR := le_pCore_map_subtype (ringChar K) hQP hQN (hpg (ringChar K))
  have hRnorm : ∀ y ∈ (CFSG.pCore (ringChar K) (graphFixedParabolic t K σ.toRingHom J)).map
      (graphFixedParabolic t K σ.toRingHom J).subtype,
      ∀ g ∈ graphFixedParabolic t K σ.toRingHom J, g * y * g⁻¹ ∈
        (CFSG.pCore (ringChar K) (graphFixedParabolic t K σ.toRingHom J)).map
          (graphFixedParabolic t K σ.toRingHom J).subtype := by
    rintro _ ⟨y, hy, rfl⟩ g hg
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, (CFSG.pCore_normal (p := ringChar K)
      (G := graphFixedParabolic t K σ.toRingHom J)).conj_mem y hy ⟨g, hg⟩, rfl⟩
  intro x hx
  have hxP : x ∈ graphFixedParabolic t K σ.toRingHom J := by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hxql⟩, -⟩ := hfac x hxP
  change x = q * l at hxql
  have hlR : l ∈ (CFSG.pCore (ringChar K) (graphFixedParabolic t K σ.toRingHom J)).map
      (graphFixedParabolic t K σ.toRingHom J).subtype := by
    have e : l = q⁻¹ * x := by rw [hxql, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem (hQR hq)) hx
  have hlV : l ∈ parabolicLeviUnipotent t.tag K (t.orbitUnion J) :=
    parabolicLevi_inf_posUnipotent_le _ (Subgroup.mem_inf.2
      ⟨(Subgroup.mem_inf.1 hl).1, (Subgroup.mem_inf.1 (hRU hlR)).1⟩)
  have h1 := hRU (hRnorm l hlR n hn)
  have h2 : n * l * n⁻¹ ∈ negUnipotent t.tag K := hV ⟨l, hlV, rfl⟩
  have h3 : n * l * n⁻¹ ∈ twistedFixedGroup t K σ.toRingHom :=
    mul_mem (mul_mem (hPΓ hn) (hPΓ (hLP hl))) (inv_mem (hPΓ hn))
  have h4 : n * l * n⁻¹ ∈ graphFixedPosUnipotent t K σ.toRingHom ⊓
      graphFixedNegUnipotent t K σ.toRingHom :=
    Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_inf.2 ⟨h2, h3⟩⟩
  rw [graphFixedPosUnipotent_inf_graphFixedNegUnipotent, Subgroup.mem_bot, conj_eq_one_iff] at h4
  rw [hxql, h4, mul_one]
  exact hq

theorem graphFixedParabolicRadical_le_pCore (t : TwistTag) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) :
    graphFixedParabolicRadical t K σ.toRingHom J ≤
      (CFSG.pCore (ringChar K) (graphFixedParabolic t K σ.toRingHom J)).map
        (graphFixedParabolic t K σ.toRingHom J).subtype := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQN, -, -, -, -, -, -, hpg, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
  exact le_pCore_map_subtype (ringChar K) hQP hQN (hpg (ringChar K))

@[expose] def foldedWordRep (t : TwistTag) (K : Type) [Field K] (l : List (Fin t.foldedTag.rank)) :
    ModGL t.tag K :=
  (l.map fun a => canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)).prod

theorem map_conj_foldedWordRep (t : TwistTag) (K : Type) [Field K]
    (l : List (Fin t.foldedTag.rank)) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    (rootSubgroup t.tag K α).map (MulAut.conj (foldedWordRep t K l)).toMonoidHom =
      rootSubgroup t.tag K ((l.map t.orbitReflection).prod • α) := by
  induction l with
  | nil =>
    ext g
    simp [foldedWordRep]
  | cons a l ih =>
    rw [foldedWordRep, List.map_cons, List.prod_cons, map_conj_mul, ← foldedWordRep, ih,
      (canonical_weyl_root_transport t.tag K).2.1 _ _ (IsRoot.smul hα _), List.map_cons,
      List.prod_cons, mul_smul]

theorem foldedWordRep_mem (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)
    {J : Set (Fin t.foldedTag.rank)} {l : List (Fin t.foldedTag.rank)} (hl : ∀ a ∈ l, a ∈ J) :
    foldedWordRep t K l ∈ graphFixedParabolic t K σ.toRingHom J := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, hl a ha, rfl⟩)

theorem pCore_graphFixedParabolic_le_of_word (t : TwistTag) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (J : Set (Fin t.foldedTag.rank)) (l : List (Fin t.foldedTag.rank))
    (hl : ∀ a ∈ l, a ∈ J)
    (hneg : ∀ α ∈ parabolicPosRoots t.tag (t.orbitUnion J),
      height ((l.map t.orbitReflection).prod • α) < 0) :
    (CFSG.pCore (ringChar K) (graphFixedParabolic t K σ.toRingHom J)).map
        (graphFixedParabolic t K σ.toRingHom J).subtype ≤
      graphFixedParabolicRadical t K σ.toRingHom J := by
  refine pCore_graphFixedParabolic_le_of_conj t K σ J (foldedWordRep_mem t K σ hl) ?_
  refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun α hα => ?_)
  rw [← Subgroup.map_le_iff_le_comap, map_conj_foldedWordRep t K l hα.1.1]
  exact le_iSup₂_of_le _ ⟨IsRoot.smul hα.1.1 _, hneg α hα⟩ le_rfl

end Radical

end CFSG.LieType.Chevalley
