module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Two
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Pumpdown

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup

theorem fourGroup_slTwo
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hID : Harris81Lemma35IdentFact) {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hcat : ¬ Blueprint.Catalog X) {W : Subgroup X} (hW2 : ∀ a ∈ W, a * a = 1)
    (hW4 : Nat.card W = 4) {z₁ z₂ : X} (hz₁W : z₁ ∈ W) (hz₂W : z₂ ∈ W) (hz₁1 : z₁ ≠ 1)
    (hz₂1 : z₂ ≠ 1) (hne : z₁ ≠ z₂) {L₁ L₂ : Subgroup X}
    (hL₁ : IsTwoComponentIn L₁ (centralizer (W : Set X)))
    (hL₂ : IsTwoComponentIn L₂ (centralizer (W : Set X))) (hz₁L : z₁ ∈ L₁) (hz₂L : z₂ ∈ L₂)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (h5 : 5 ≤ p ^ k)
    (hsl : IsSLTwoOver (p ^ k) (↥L₁ ⧸ pPrimeCore 2 ↥L₁)) :
    IsTwoComponentIn (GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})))
        (centralizer {z₁}) ∧
      L₁ ≤ GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})) ∧
      L₂ ≤ GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})) ∧
      IsMTypeSchur p ↥(GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁}))) ∧
      ∃ hz₂K : z₂ ∈ GSThmB.conjClosure L₁ (GSThmB.layerIn (centralizer {z₁})),
        (QuotientGroup.mk ⟨z₂, hz₂K⟩ : Bar (GSThmB.conjClosure L₁
          (GSThmB.layerIn (centralizer {z₁})))) ∉ center (Bar (GSThmB.conjClosure L₁
            (GSThmB.layerIn (centralizer {z₁})))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz₂n : z₂ ∉ zpowers z₁ := fun h =>
    (T23.eq_one_or_eq_of_mem_zpowers (hW2 z₁ hz₁W) h).elim hz₂1 hne.symm
  obtain ⟨hz₁2, hz₂2, hz₂M, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hz₁W hz₁1 hz₂W hz₂n
  have hL₁' : IsTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) := hCW ▸ hL₁
  have hL₂' : IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) := hCW ▸ hL₂
  set M := centralizer ({z₁} : Set X) with hMdef
  set z₂' : ↥M := ⟨z₂, hz₂M⟩
  have hz₂'2 : orderOf z₂' = 2 := by rw [Subgroup.orderOf_mk]; exact hz₂2
  have hM₁ : IsMTypeSchur p ↥L₁ := T23.isMTypeSchur_of_slTwo hGA hL₁.2.2.1 hp hp2 hk h5 hsl
  have hm₁ : ∃ k : ℕ, Blueprint.LieModel (↥L₁ ⧸ Open.fusionZStar ↥L₁) .PSL 2 p k := by
    obtain ⟨-, -, hQm, -⟩ := Lemma47.sl2_facts hp hp2 hk h5 hsl
    obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥L₁
    exact ⟨k, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hQm⟩
  obtain ⟨K₀, hK₀, hKeq, -⟩ := T23.exists_pumpup hz₂2 hz₂M hL₁'
  have hfix : K₀.map (MulAut.conj z₂').toMonoidHom = K₀ :=
    T23.map_conj_eq_of_mem_twoComponent hz₂'2 (T23.isTwoComponentIn_subgroupOf hz₂M hL₂') hz₂L
      hK₀
  have hKK₀ : GSThmB.conjClosure L₁ (GSThmB.layerIn M) = K₀.map M.subtype := by
    rw [hKeq, hfix, sup_idem]
  rw [hKK₀]
  have hKc : IsTwoComponentIn (K₀.map M.subtype) M := T23.isTwoComponentIn_map_subtype hK₀
  have hL₁K : L₁ ≤ K₀.map M.subtype := hKK₀ ▸ GSThmB.B5a.le_conjClosure L₁ _
  have hz₁K : z₁ ∈ K₀.map M.subtype := hL₁K hz₁L
  have hKM : IsMTypeSchur p ↥(K₀.map M.subtype) := by
    by_contra hKM
    exact T23.false_of_not_isMTypeSchur hGA hID hnonab hK hcat hW2 hW4 hz₁W hz₂W hz₁1 hz₂1 hne
      hL₁ hL₂ hz₁L hz₂L hp hp2 hM₁ hm₁ fun _ _ => by rw [hKK₀]; exact hKM
  have hKv : (K₀.map M.subtype).map (MulAut.conj z₂).toMonoidHom = K₀.map M.subtype := by
    have h := T23.map_subtype_map_conj K₀ z₂'
    rw [hfix] at h
    exact h.symm
  have hz₂N : z₂ ∈ normalizer ((K₀.map M.subtype : Subgroup X) : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hKv]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hKv] at hh
      obtain ⟨x, hx, hxe⟩ := hh
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe
      rw [← mul_left_cancel (mul_right_cancel hxe)]
      exact hx
  have ht2 : IsPGroup 2 (zpowers z₂) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz₂2, pow_one])
  have hfalse : barAction (K₀.map M.subtype) ⟨z₂, hz₂N⟩ = 1 → False := by
    intro htriv
    obtain ⟨hJ, ⟨eJ⟩⟩ := pumpdown hKc hz₂N ht2 htriv
    rw [← hCW] at hJ
    set J := centralizerResidual (K₀.map M.subtype) z₂
    have hL₁J : L₁ ≤ J := le_perfectResidual_map
      (le_inf hL₁K (hL₁'.1.trans inf_le_right)) hL₁.2.2.1
    have heq : L₁ = J := by
      obtain ⟨hL₁W, hL₁t⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hL₁
      obtain ⟨hJW, hJt⟩ := L219.isTwoComponentIn_iff_twoComponents.mp hJ
      have h1 := TwoComponentSubnormal.eq_of_le _ _ hL₁t hJt (fun x hx => hL₁J hx)
      rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hL₁W, inf_eq_left.mpr hJW] at h1
      exact h1
    obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hsl
    let e : ↥J ≃* ↥L₁ := MulEquiv.subgroupCongr heq.symm
    let eL : ↥J ⧸ pPrimeCore 2 ↥J ≃* ↥L₁ ⧸ pPrimeCore 2 ↥L₁ :=
      QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)
    exact false_of_intrinsic_slTwo hCI hnonab hcat hz₁2 hKc hz₁K hp hp2
      ⟨F, inferInstance, inferInstance, hF, ⟨(eJ.symm.trans eL).trans eF⟩⟩
  obtain ⟨K₂, hK₂, -, -, hL₂K₂⟩ := T23.exists_pumpup_of_mem hz₂2 hz₂M hL₂' hz₂L
  have hz₂K₂ : z₂' ∈ K₂ := (hL₂K₂.1 (show z₂' ∈ L₂.subgroupOf M from hz₂L)).1
  by_cases hK₂K : K₀ = K₂
  · subst hK₂K
    have hL₂K : L₂ ≤ K₀.map M.subtype := by
      intro x hx
      exact ⟨⟨x, hL₂'.1 hx |>.1⟩, (hL₂K₂.1 (show (⟨x, _⟩ : ↥M) ∈ L₂.subgroupOf M from hx)).1,
        rfl⟩
    have hz₂K : z₂ ∈ K₀.map M.subtype := hL₂K hz₂L
    refine ⟨hKc, hL₁K, hL₂K, hKM, hz₂K, fun hc => hfalse ?_⟩
    exact barAction_eq_one_of_mem_center (t := ⟨z₂, hz₂K⟩) hc hz₂N
  ·
    exfalso
    apply hfalse
    ext y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    rw [barAction_mk, MulAut.one_apply]
    obtain ⟨o, ho, hoeq⟩ := T23.commutator_mem_pPrimeCore hK₀ hK₂ hK₂K hz₂K₂ k
    refine (QuotientGroup.eq.mpr ?_).symm
    have : k⁻¹ * normalizerConj (K₀.map M.subtype) ⟨z₂, hz₂N⟩ k = o := by
      apply Subtype.ext
      rw [hoeq]
      rfl
    rw [this]
    exact ho

end CFSG.ComponentClassification.HarrisLit.T1
