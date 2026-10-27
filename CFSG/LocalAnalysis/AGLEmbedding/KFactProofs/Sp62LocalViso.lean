module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import Certificates.Certificate9442

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13 CFSG.Quasithin.G2U
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U42
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.GH74.Exceptional

theorem nonempty_mulEquiv_of_isPresentation {X V : Type*} [Group X] [Finite X] [Group V]
    [Finite V] {ι : Type} {g : ι → X} {R : Set (FreeGroup ι)} (hP : IsPresentation g R)
    {e : ι → V} (hrel : ∀ r ∈ R, FreeGroup.lift e r = 1)
    (hgen : Subgroup.closure (Set.range e) = ⊤) (hcard : Nat.card X ≤ Nat.card V) :
    Nonempty (X ≃* V) := by
  set π := FreeGroup.lift g with hπ
  set ρ := FreeGroup.lift e with hρ
  have hker : π.ker ≤ ρ.ker := by
    rw [hP.ker_lift]
    refine Subgroup.normalClosure_le_normal fun r hr => ?_
    exact hrel r hr
  let Φ : X →* V := (QuotientGroup.lift π.ker ρ hker).comp
    (QuotientGroup.quotientKerEquivOfSurjective π hP.lift_surjective).symm.toMonoidHom
  have hΦπ : ∀ w, Φ (π w) = ρ w := by
    intro w
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hP.lift_surjective).symm (π w) =
        (w : FreeGroup ι ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.lift π.ker ρ hker)
      ((QuotientGroup.quotientKerEquivOfSurjective π hP.lift_surjective).symm (π w)) = ρ w
    rw [h1]
    rfl
  have hsurj : Function.Surjective Φ := by
    intro v
    have hv : v ∈ ρ.range := by
      rw [hρ, FreeGroup.range_lift_eq_closure, hgen]
      exact Subgroup.mem_top v
    obtain ⟨w, rfl⟩ := hv
    exact ⟨π w, hΦπ w⟩
  exact ⟨(MulEquiv.ofBijective Φ (hsurj.bijective_of_nat_card_le hcard))⟩

theorem sp62_relators : chkRel = true :=
  Certificates.certificate9442

theorem genB_cA : genB cA = true := by
  have h := sp62_relators
  simp only [chkRel, Bool.and_eq_true] at h
  exact h.1.1.1

theorem genB_cB : genB cB = true := by
  have h := sp62_relators
  simp only [chkRel, Bool.and_eq_true] at h
  exact h.1.1.2

theorem commB_cA_cB : commB cA cB = false := by
  have h := sp62_relators
  simp only [chkRel, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

theorem rep_letter (l : ℕ × Bool) :
    Rep (if l.2 then img2 (elt cA) (elt cB) l.1 else (img2 (elt cA) (elt cB) l.1)⁻¹)
      (letterC l) := by
  obtain ⟨i, t⟩ := l
  by_cases hi : i = 0
  · subst hi
    cases t
    · exact rep_elt_inv genB_cA
    · exact rep_elt (genB_isoB genB_cA)
  · have h1 : img2 (elt cA) (elt cB) i = elt cB := by simp [img2, hi]
    cases t
    · have h2 : letterC (i, false) = invC cB := by simp [letterC, hi]
      simp only [Bool.false_eq_true, ↓reduceIte, h1, h2]
      exact rep_elt_inv genB_cB
    · have h2 : letterC (i, true) = cB := by simp [letterC, hi]
      simp only [↓reduceIte, h1, h2]
      exact rep_elt (genB_isoB genB_cB)

theorem rep_wordProd (w : List (ℕ × Bool)) :
    Rep (wordProd (img2 (elt cA) (elt cB)) w) (evalW w) := by
  induction w with
  | nil => exact Rep.one
  | cons l w ih =>
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    exact (rep_letter l).mul ih

theorem wordProd_relWords :
    ∀ w ∈ relWords, wordProd (img2 (elt cA) (elt cB)) w = 1 := by
  have h := sp62_relators
  simp only [chkRel, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  intro w hw
  exact (rep_wordProd w).eq_one_iff.2 (h.2 w hw)

theorem cA_mem_gensV : cA ∈ gensV := by simp [gensV]

theorem cB_mem_gensV : cB ∈ gensV := by simp [gensV]

@[expose] noncomputable def aV : V0 := ⟨elt cA, elt_mem_Hgen cA_mem_gensV⟩

@[expose] noncomputable def bV : V0 := ⟨elt cB, elt_mem_Hgen cB_mem_gensV⟩

theorem range_img2_V0 : Set.range (fun i : Fin 2 => img2 aV bV i.val) =
    (Subtype.val : V0 → H6) ⁻¹' genSet gensV := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : (i : ℕ) = 0
    · simp only [img2, hi, ↓reduceIte, Set.mem_preimage]
      exact ⟨cA, cA_mem_gensV, rfl⟩
    · simp only [img2, hi, ↓reduceIte, Set.mem_preimage]
      exact ⟨cB, cB_mem_gensV, rfl⟩
  · intro hx
    obtain ⟨c, hc, hxc⟩ := hx
    simp only [gensV, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨0, Subtype.ext hxc.symm⟩
    · exact ⟨1, Subtype.ext hxc.symm⟩

theorem closure_range_img2_V0 :
    Subgroup.closure (Set.range (fun i : Fin 2 => img2 aV bV i.val)) = ⊤ := by
  rw [range_img2_V0]
  exact Subgroup.closure_closure_coe_preimage

theorem lift_relators_V0 :
    ∀ r ∈ wordSet U42.rels, FreeGroup.lift (fun i : Fin 2 => img2 aV bV i.val) r = 1 := by
  intro r hr
  simp only [Set.mem_ofPred_eq, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [lift_mk_eq_wordProd]
  apply V0.subtype_injective
  rw [map_one]
  show ((wordProd (img2 aV bV) _ : V0) : H6) = 1
  rw [coe_wordProd]
  have himg : (fun i => ((img2 aV bV i : V0) : H6)) = img2 (elt cA) (elt cB) := by
    funext i
    by_cases hi : i = 0 <;> simp [img2, hi, aV, bV]
  rw [himg]
  refine wordProd_relWords _ ?_
  have hrel : relWords = U42.rels.map (List.map fun l : Fin 2 × Bool => (l.1.val, l.2)) := by
    decide
  rw [hrel]
  exact List.mem_map.2 ⟨w, hw, rfl⟩

theorem nonempty_PSp43_mulEquiv_V0 :
    Nonempty (PSp43 ≃* V0) :=
  nonempty_mulEquiv_of_isPresentation isPresentation_PSp43 lift_relators_V0
    closure_range_img2_V0 (by rw [card_PSp43, card_V0])

@[expose] def q2 : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, by norm_num⟩

theorem valid_u42 : (TauCeti.LieTypeIndex.twistedA 3 q2).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [q2]

@[expose] def u42Index : TauCeti.ValidLieTypeIndex := ⟨.twistedA 3 q2, valid_u42⟩

theorem isUFourTwoIndex_u42 : IsUFourTwoIndex u42Index := ⟨q2, rfl, rfl, rfl⟩

theorem lieModel_u42 : CFSG.Blueprint.LieModel (CatGroup u42Index) .PSU 4 2 1 :=
  Or.inl ⟨by decide, CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q2 valid_u42
    (MulEquiv.refl _)⟩

theorem isSimpleGroup_catGroup_u42 : IsSimpleGroup (CatGroup u42Index) :=
  CFSG.Quasithin.H13.F431.U42.isSimpleGroup_of_lieModel_PSU_four_two lieModel_u42

theorem nonempty_V0_mulEquiv_catGroup :
    Nonempty (V0 ≃* CatGroup u42Index) := by
  obtain ⟨e₁⟩ := nonempty_PSp43_mulEquiv_V0
  obtain ⟨e₂⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 lieModel_u42
  exact ⟨e₁.symm.trans e₂.symm⟩

theorem isSimpleGroup_V0 :
    IsSimpleGroup V0 := by
  obtain ⟨e⟩ := nonempty_V0_mulEquiv_catGroup
  have := isSimpleGroup_catGroup_u42
  exact e.isSimpleGroup

theorem V_iso_V0 :
    ∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V0 →* CatGroup d), IsUFourTwoIndex d ∧
      Function.Bijective ψ := by
  obtain ⟨e⟩ := nonempty_V0_mulEquiv_catGroup
  exact ⟨u42Index, e.toMonoidHom, isUFourTwoIndex_u42, e.bijective⟩

end CFSG.AGLEmbedding.KFactProofs.Sp62Local
