module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotThm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
open scoped commutatorElement

section Transport

variable {G G' : Type} [Group G] [Group G'] (e : G ≃* G')

abbrev famMap (Ω : Set (Subgroup G)) : Set (Subgroup G') :=
  (fun L : Subgroup G => L.map e.toMonoidHom) '' Ω

theorem map_symm_map_equiv (U : Subgroup G) :
    (U.map e.toMonoidHom).map e.symm.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem famMap_symm_famMap (Ω : Set (Subgroup G)) : famMap e.symm (famMap e Ω) = Ω := by
  ext L
  constructor
  · rintro ⟨_, ⟨M, hM, rfl⟩, rfl⟩
    show (M.map e.toMonoidHom).map e.symm.toMonoidHom ∈ Ω
    rwa [map_symm_map_equiv]
  · intro hL
    exact ⟨L.map e.toMonoidHom, ⟨L, hL, rfl⟩, map_symm_map_equiv e L⟩

variable {e}

theorem equiv_map_mem_RSet {Ω : Set (Subgroup G)} {R : Subgroup G} (hR : R ∈ RSet Ω) :
    R.map e.toMonoidHom ∈ RSet (famMap e Ω) := by
  obtain ⟨J, hJ, hRJ, hR2, hmax⟩ := mem_RSet_iff.mp hR
  refine mem_RSet_iff.mpr ⟨J.map e.toMonoidHom, ⟨J, hJ, rfl⟩, Subgroup.map_mono hRJ,
    hR2.map _, fun R' hR'J hR'2 hle => ?_⟩
  have h1 : R'.comap e.toMonoidHom ≤ J := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hR'J hx
    have : z = x := e.injective (by simpa using hzx)
    rwa [← this]
  have h2 : IsPGroup 2 (R'.comap e.toMonoidHom) := hR'2.comap_of_injective _ e.injective
  have h3 : R ≤ R'.comap e.toMonoidHom := fun x hx => hle (Subgroup.mem_map_of_mem _ hx)
  have h4 := hmax _ h1 h2 h3
  calc R' = (R'.comap e.toMonoidHom).map e.toMonoidHom :=
        (Subgroup.map_comap_eq_self_of_surjective e.surjective R').symm
    _ = R.map e.toMonoidHom := by rw [h4]

theorem equiv_map_mem_USet {Ω : Set (Subgroup G)} {U : Subgroup G} (hU : U ∈ USet Ω) :
    U.map e.toMonoidHom ∈ USet (famMap e Ω) := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  refine ⟨R.map e.toMonoidHom, equiv_map_mem_RSet hR, Subgroup.map_mono hUR, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U e.toMonoidHom e.injective)).mp hcyc
  · rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    exact hidx

theorem equiv_inDistinctMembers_map {Ω : Set (Subgroup G)} {η : Set (Subgroup G)}
    (h : InDistinctMembers Ω η) : InDistinctMembers (famMap e Ω) (famMap e η) := by
  rintro _ ⟨U, hU, rfl⟩ _ ⟨U', hU', rfl⟩ hne _ ⟨J, hJ, rfl⟩ ⟨h1, h2⟩
  have hne' : U ≠ U' := fun h' => hne (by rw [h'])
  refine h U hU U' hU' hne' J hJ ⟨?_, ?_⟩
  · have := Subgroup.map_mono (f := e.symm.toMonoidHom) h1
    rwa [map_symm_map_equiv, map_symm_map_equiv] at this
  · have := Subgroup.map_mono (f := e.symm.toMonoidHom) h2
    rwa [map_symm_map_equiv, map_symm_map_equiv] at this

theorem equiv_map_mem_etaSet {Ω : Set (Subgroup G)} {S : Subgroup G} {η : Set (Subgroup G)}
    (h : η ∈ etaSet Ω S) : famMap e η ∈ etaSet (famMap e Ω) (S.map e.toMonoidHom) := by
  have hinj : Function.Injective (fun U : Subgroup G => U.map e.toMonoidHom) :=
    Subgroup.map_injective e.injective
  refine ⟨?_, equiv_inDistinctMembers_map h.2.1, fun η' hη' hd => ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨equiv_map_mem_USet (h.1 hU).1, Subgroup.map_mono (h.1 hU).2⟩
  · set η'' : Set (Subgroup G) := famMap e.symm η' with hη''
    have hsub : η'' ⊆ {U | U ∈ USet Ω ∧ U ≤ S} := by
      rintro _ ⟨U, hU, rfl⟩
      refine ⟨?_, ?_⟩
      · have := equiv_map_mem_USet (e := e.symm) (hη' hU).1
        rwa [famMap_symm_famMap] at this
      · have := Subgroup.map_mono (f := e.symm.toMonoidHom) (hη' hU).2
        rwa [map_symm_map_equiv] at this
    have hd'' : InDistinctMembers Ω η'' := by
      have := equiv_inDistinctMembers_map (e := e.symm) hd
      rwa [famMap_symm_famMap] at this
    have hle := h.2.2 η'' hsub hd''
    have himg : famMap e η'' = η' := by
      have := famMap_symm_famMap e.symm η'
      simpa using this
    have h1 : η'.ncard = η''.ncard := by
      rw [← himg, Set.ncard_image_of_injective _ hinj]
    rw [Set.ncard_image_of_injective _ hinj, h1]
    exact hle

theorem equiv_map_mem_WSet [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}
    (hW : W ∈ WSet Ω) : W.map e.toMonoidHom ∈ WSet (famMap e Ω) := by
  obtain ⟨η, ⟨S, hS, hinv⟩, rfl⟩ := hW
  let S' : Sylow 2 G' := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS' : (S' : Subgroup G') = (S : Subgroup G).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  refine ⟨famMap e η, ⟨S', ?_, ?_⟩, ?_⟩
  · rw [hS']
    exact equiv_map_mem_etaSet hS
  · intro s hs U hU
    rw [hS'] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨U₀, hU₀, rfl⟩ := hU
    exact ⟨conjSub s₀ U₀, hinv s₀ hs₀ U₀ hU₀, AscQuot.map_conjSub e.toMonoidHom s₀ U₀⟩
  · simp only [Subgroup.map_iSup, iSup_image]

variable (e) in
theorem wSet_map_equiv [Finite G] [Finite G'] (Ω : Set (Subgroup G)) :
    WSet (famMap e Ω) = (fun W : Subgroup G => W.map e.toMonoidHom) '' WSet Ω := by
  ext W'
  constructor
  · intro hW'
    have h1 := equiv_map_mem_WSet (e := e.symm) hW'
    rw [famMap_symm_famMap] at h1
    refine ⟨_, h1, ?_⟩
    simpa using map_symm_map_equiv e.symm W'
  · rintro ⟨W, hW, rfl⟩
    exact equiv_map_mem_WSet hW

end Transport

section RowsEquiv

variable {X X' : Type} [Group X] [Group X']

theorem isL3E8_of_mulEquiv (e : X ≃* X') (h : IsL3E8 X) : IsL3E8 X' := by
  obtain ⟨E, hEn, hEab, hcard, ⟨q⟩⟩ := h
  haveI : (E.map e.toMonoidHom).Normal := hEn.map _ e.surjective
  have hEab' : IsElemAbelian 2 (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · rcases a with ⟨_, x₁, hx₁, rfl⟩
      rcases b with ⟨_, x₂, hx₂, rfl⟩
      apply Subtype.ext
      show e.toMonoidHom x₁ * e.toMonoidHom x₂ = e.toMonoidHom x₂ * e.toMonoidHom x₁
      rw [← map_mul, ← map_mul]
      congr 1
      have := hEab.1.1.comm ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
      simpa using congrArg Subtype.val this
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [← map_pow, hEab.2 x hx, map_one]
  refine ⟨E.map e.toMonoidHom, inferInstance, hEab', ?_, ⟨?_⟩⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  · exact (QuotientGroup.congr E (E.map e.toMonoidHom) e rfl).symm.trans q

variable {Y₁ Y₂ : Type} [Group Y₁] [Group Y₂] [Finite Y₁] [Finite Y₂]

theorem thm3RowW_of_equiv {Φ₁ : Set (Subgroup Y₁)} {Φ₂ : Set (Subgroup Y₂)} {P₁ : Subgroup Y₁}
    {P₂ : Subgroup Y₂} (e : SecQuot P₁ ≃* SecQuot P₂)
    (hF : oddQuotientFamily (restrictFamily Φ₂ P₂) =
      famMap e (oddQuotientFamily (restrictFamily Φ₁ P₁)))
    (h : Thm3RowW Φ₁ P₁) : Thm3RowW Φ₂ P₂ := by
  obtain ⟨W, hW, hWset, ⟨d⟩⟩ := h
  haveI := hW
  haveI : (W.map e.toMonoidHom).Normal := hW.map _ e.surjective
  refine ⟨W.map e.toMonoidHom, inferInstance, ?_, ⟨?_⟩⟩
  · rw [hF, wSet_map_equiv, hWset, Set.image_singleton]
  · exact (QuotientGroup.congr W (W.map e.toMonoidHom) e rfl).symm.trans d

theorem thm3RowsA_of_equiv {Φ₁ : Set (Subgroup Y₁)} {Φ₂ : Set (Subgroup Y₂)} {P₁ : Subgroup Y₁}
    {P₂ : Subgroup Y₂} (e : SecQuot P₁ ≃* SecQuot P₂)
    (hF : oddQuotientFamily (restrictFamily Φ₂ P₂) =
      famMap e (oddQuotientFamily (restrictFamily Φ₁ P₁)))
    (h : Thm3RowsA Φ₁ P₁) : Thm3RowsA Φ₂ P₂ := by
  rcases h with ⟨N, hN, hidx, hLie⟩ | hM | hL | hW
  · haveI := hN
    haveI : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
    refine Or.inl ⟨N.map e.toMonoidHom, inferInstance, ?_, ?_⟩
    · exact (Subgroup.index_map_equiv N e).trans hidx
    · exact CFSG.Blueprint.LieModel.of_mulEquiv
        (N.equivMapOfInjective e.toMonoidHom e.injective) hLie
  · obtain ⟨f⟩ : Nonempty (SecQuot P₁ ≃* CFSG.Blueprint.NativeSporadic.Carrier .M12) := hM
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl (isL3E8_of_mulEquiv e hL)))
  · exact Or.inr (Or.inr (Or.inr (thm3RowW_of_equiv e hF hW)))

theorem thm3RowsG_of_equiv {Φ₁ : Set (Subgroup Y₁)} {Φ₂ : Set (Subgroup Y₂)} {P₁ : Subgroup Y₁}
    {P₂ : Subgroup Y₂} (e : SecQuot P₁ ≃* SecQuot P₂)
    (hF : oddQuotientFamily (restrictFamily Φ₂ P₂) =
      famMap e (oddQuotientFamily (restrictFamily Φ₁ P₁)))
    (h : Thm3RowsG Φ₁ P₁) : Thm3RowsG Φ₂ P₂ := by
  rcases h with hG | hA
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hG)
  · exact Or.inr (thm3RowsA_of_equiv e hF hA)

end RowsEquiv

section OddCore

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

theorem map_oddCore_of_surjective (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    (classicalInvolutionOddCore A).map φ = classicalInvolutionOddCore B := by
  apply le_antisymm
  · apply le_sSup
    refine ⟨Subgroup.Normal.map inferInstance φ hφ, ?_⟩
    exact (CFSG.ComponentClassification.OddCore.odd_card A).of_dvd_nat
      (Subgroup.card_map_dvd _ φ)
  · have hPodd : Odd (Nat.card ((classicalInvolutionOddCore B).comap φ)) :=
      CFSG.Wreathed.CyclicOddScalarQuotient.comap_odd_card φ hφ hker _
        (CFSG.ComponentClassification.OddCore.odd_card B)
    have hPle : (classicalInvolutionOddCore B).comap φ ≤ classicalInvolutionOddCore A :=
      le_sSup ⟨Subgroup.Normal.comap inferInstance φ, hPodd⟩
    calc classicalInvolutionOddCore B
        = ((classicalInvolutionOddCore B).comap φ).map φ :=
          (Subgroup.map_comap_eq_self_of_surjective hφ _).symm
      _ ≤ (classicalInvolutionOddCore A).map φ := Subgroup.map_mono hPle

theorem comap_oddCore_of_surjective (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    (classicalInvolutionOddCore B).comap φ = classicalInvolutionOddCore A := by
  apply le_antisymm
  · exact le_sSup ⟨Subgroup.Normal.comap inferInstance φ,
      CFSG.Wreathed.CyclicOddScalarQuotient.comap_odd_card φ hφ hker _
        (CFSG.ComponentClassification.OddCore.odd_card B)⟩
  · intro a ha
    show φ a ∈ classicalInvolutionOddCore B
    rw [← map_oddCore_of_surjective φ hφ hker]
    exact Subgroup.mem_map_of_mem φ ha

theorem ker_mk_comp_eq_oddCore (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    ((QuotientGroup.mk' (classicalInvolutionOddCore B)).comp φ).ker =
      classicalInvolutionOddCore A := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_oddCore_of_surjective φ hφ hker]

@[expose] noncomputable def oddQuotEquivOfSurjective (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    A ⧸ classicalInvolutionOddCore A ≃* B ⧸ classicalInvolutionOddCore B :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk_comp_eq_oddCore φ hφ hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hφ))

theorem oddQuotEquivOfSurjective_comp (φ : A →* B) (hφ : Function.Surjective φ)
    (hker : Odd (Nat.card φ.ker)) :
    (oddQuotEquivOfSurjective φ hφ hker).toMonoidHom.comp
        (QuotientGroup.mk' (classicalInvolutionOddCore A)) =
      (QuotientGroup.mk' (classicalInvolutionOddCore B)).comp φ := by
  ext a
  rfl

end OddCore

section SecQuot

variable {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]

theorem odd_natCard_ker_quotRestrict (hN : Odd (Nat.card N)) (P : Subgroup Y) :
    Odd (Nat.card (AscQuot.quotRestrict P N).ker) := by
  have hker : (AscQuot.quotRestrict P N).ker = N.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff, AscQuot.quotRestrict_apply]
    exact QuotientGroup.eq_one_iff (x : Y)
  rw [hker]
  have hcard : Nat.card ↥(N.subgroupOf P) = Nat.card ↥(N ⊓ P) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [hcard]
  exact odd_natCard_inf hN P

@[expose] noncomputable def secQuotMapEquiv (hN : Odd (Nat.card N)) (P : Subgroup Y) :
    SecQuot P ≃* SecQuot (P.map (QuotientGroup.mk' N)) :=
  oddQuotEquivOfSurjective (AscQuot.quotRestrict P N) (AscQuot.quotRestrict_surjective P N)
    (odd_natCard_ker_quotRestrict hN P)

theorem map_quotRestrict_subgroupOf {P L : Subgroup Y} (hLP : L ≤ P) :
    (L.subgroupOf P).map (AscQuot.quotRestrict P N) =
      (L.map (QuotientGroup.mk' N)).subgroupOf (P.map (QuotientGroup.mk' N)) := by
  ext ⟨x, hx⟩
  constructor
  · rintro ⟨⟨l, hlP⟩, hl, hlx⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨l, Subgroup.mem_subgroupOf.mp hl, ?_⟩
    exact (AscQuot.quotRestrict_apply P N ⟨l, hlP⟩).symm.trans (congrArg Subtype.val hlx)
  · intro h
    rw [Subgroup.mem_subgroupOf] at h
    obtain ⟨l, hl, hlx⟩ := h
    refine ⟨⟨l, hLP hl⟩, Subgroup.mem_subgroupOf.mpr hl, Subtype.ext ?_⟩
    rw [AscQuot.quotRestrict_apply]
    exact hlx

theorem oddQuotientFamily_restrict_map (hN : Odd (Nat.card N)) {Φ : Set (Subgroup Y)}
    {P : Subgroup Y}
    (hP : ∀ L ∈ Φ, L.map (QuotientGroup.mk' N) ≤ P.map (QuotientGroup.mk' N) → L ≤ P) :
    oddQuotientFamily (restrictFamily (quotFamily Φ N) (P.map (QuotientGroup.mk' N))) =
      famMap (secQuotMapEquiv hN P) (oddQuotientFamily (restrictFamily Φ P)) := by
  have hcomp := oddQuotEquivOfSurjective_comp (AscQuot.quotRestrict P N)
    (AscQuot.quotRestrict_surjective P N) (odd_natCard_ker_quotRestrict hN P)
  have key : ∀ L : Subgroup Y, L ≤ P →
      ((L.subgroupOf P).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥P))).map
          (secQuotMapEquiv hN P).toMonoidHom =
        ((L.map (QuotientGroup.mk' N)).subgroupOf (P.map (QuotientGroup.mk' N))).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(P.map (QuotientGroup.mk' N)))) := by
    intro L hLP
    rw [Subgroup.map_map]
    unfold secQuotMapEquiv
    rw [hcomp, ← Subgroup.map_map, map_quotRestrict_subgroupOf hLP]
  ext M
  constructor
  · rintro ⟨_, ⟨L', hL', hL'P, rfl⟩, rfl⟩
    obtain ⟨L, hL, rfl⟩ := hL'
    have hLP := hP L hL hL'P
    exact ⟨_, ⟨L.subgroupOf P, ⟨L, hL, hLP, rfl⟩, rfl⟩, key L hLP⟩
  · rintro ⟨_, ⟨_, ⟨L, hL, hLP, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨L.map (QuotientGroup.mk' N), map_mem_quotFamily hL, Subgroup.map_mono hLP, rfl⟩,
      (key L hLP).symm⟩

theorem thm3RowsG_map_iff_of_le (hN : Odd (Nat.card N)) {Φ : Set (Subgroup Y)} {P : Subgroup Y}
    (hP : ∀ L ∈ Φ, L.map (QuotientGroup.mk' N) ≤ P.map (QuotientGroup.mk' N) → L ≤ P) :
    Thm3RowsG (quotFamily Φ N) (P.map (QuotientGroup.mk' N)) ↔ Thm3RowsG Φ P := by
  have hF := oddQuotientFamily_restrict_map hN hP
  constructor
  · intro h
    refine thm3RowsG_of_equiv (secQuotMapEquiv hN P).symm ?_ h
    rw [hF, famMap_symm_famMap]
  · exact thm3RowsG_of_equiv (secQuotMapEquiv hN P) hF

theorem le_of_map_le_of_le {H L : Subgroup Y} (hNH : N ≤ H)
    (h : L.map (QuotientGroup.mk' N) ≤ H.map (QuotientGroup.mk' N)) : L ≤ H := by
  have := Subgroup.map_le_iff_le_comap.mp h
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNH] at this

theorem thm3RowsG_map_iff (hN : Odd (Nat.card N)) (Φ : Set (Subgroup Y)) {H : Subgroup Y}
    (hNH : N ≤ H) :
    Thm3RowsG (quotFamily Φ N) (H.map (QuotientGroup.mk' N)) ↔ Thm3RowsG Φ H :=
  thm3RowsG_map_iff_of_le hN fun _ _ h => le_of_map_le_of_le hNH h

theorem thm3RowW_map_iff_of_le (hN : Odd (Nat.card N)) {Φ : Set (Subgroup Y)} {P : Subgroup Y}
    (hP : ∀ L ∈ Φ, L.map (QuotientGroup.mk' N) ≤ P.map (QuotientGroup.mk' N) → L ≤ P) :
    Thm3RowW (quotFamily Φ N) (P.map (QuotientGroup.mk' N)) ↔ Thm3RowW Φ P := by
  have hF := oddQuotientFamily_restrict_map hN hP
  constructor
  · intro h
    refine thm3RowW_of_equiv (secQuotMapEquiv hN P).symm ?_ h
    rw [hF, famMap_symm_famMap]
  · exact thm3RowW_of_equiv (secQuotMapEquiv hN P) hF

theorem thm3RowW_map_iff (hN : Odd (Nat.card N)) (Φ : Set (Subgroup Y)) {H : Subgroup Y}
    (hNH : N ≤ H) :
    Thm3RowW (quotFamily Φ N) (H.map (QuotientGroup.mk' N)) ↔ Thm3RowW Φ H :=
  thm3RowW_map_iff_of_le hN fun _ _ h => le_of_map_le_of_le hNH h

end SecQuot

section Members

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {N : Subgroup Y} [N.Normal]

theorem map_sup_mk (P : Subgroup Y) :
    (N ⊔ P).map (QuotientGroup.mk' N) = P.map (QuotientGroup.mk' N) := by
  rw [Subgroup.map_sup]
  have : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    exact (QuotientGroup.eq_one_iff n).mpr hn
  rw [this, bot_sup_eq]

theorem le_omegaGen_aStar_iff (hΦ : TypeRHyp Φ) (hN : Odd (Nat.card N)) {K : Subgroup Y}
    (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hC : aStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N)) =
        vStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N)) ∧
      ∀ L ∈ quotFamily Φ N, L ∉ vStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N)) →
        ∀ M ∈ vStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N)),
          ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M)
    {M : Subgroup Y} (hM : M ∈ Φ) : M ≤ N ⊔ omegaGen (aStar Φ K) ↔ M ∈ aStar Φ K := by
  refine ⟨fun hle => ?_, fun h => (le_omegaGen h).trans le_sup_right⟩
  by_contra hMA
  have hΩ : HypOmegaGen Φ := hΦ.hyp
  have hΦ' : HypOmegaGen (quotFamily Φ N) := TwinEdge.hypOmegaGen_quotFamily_odd hΩ hN
  obtain ⟨heq, hcomm⟩ := hC
  set Mb : Subgroup (Y ⧸ N) := M.map (QuotientGroup.mk' N) with hMbdef
  have hMbΦ : Mb ∈ quotFamily Φ N := map_mem_quotFamily hM
  have hMbV : Mb ∉ vStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N)) := by
    rw [← heq]
    exact fun h => hMA ((map_mem_aStar_iff hΩ hN hK hA hM).mp h)
  have hMbP : Mb ≤ omegaGen (aStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N))) := by
    rw [← omegaGen_aStar_map hΩ hN hK, ← map_sup_mk (N := N)]
    exact Subgroup.map_mono hle
  let C : Subgroup (Y ⧸ N) :=
    { carrier := {g | g ∈ Subgroup.normalizer (Mb : Set (Y ⧸ N)) ∧
        ∀ m ∈ Mb, ⁅g, m⁆ ∈ oddCoreOf Mb}
      mul_mem' := by
        rintro g h ⟨hgN, hg⟩ ⟨hhN, hh⟩
        refine ⟨Subgroup.mul_mem _ hgN hhN, fun m hm => ?_⟩
        have e : ⁅g * h, m⁆ = (g * ⁅h, m⁆ * g⁻¹) * ⁅g, m⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (oddCoreOf Mb).mul_mem (mem_normalizer_oddCoreOf_of_mem_normalizer hgN (hh m hm))
          (hg m hm)
      one_mem' := ⟨Subgroup.one_mem _, fun m _ => by
        rw [commutatorElement_def]
        simp only [one_mul, inv_one, mul_one, mul_inv_cancel]
        exact (oddCoreOf Mb).one_mem⟩
      inv_mem' := by
        rintro g ⟨hgN, hg⟩
        refine ⟨Subgroup.inv_mem _ hgN, fun m hm => ?_⟩
        have e : ⁅g⁻¹, m⁆ = g⁻¹ * (⁅g, m⁆)⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.inv_mem _ hgN)
          ((oddCoreOf Mb).inv_mem (hg m hm)) }
  have hQC : ∀ Q ∈ aStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N)), Q ≤ C := by
    intro Q hQ
    have hQV : Q ∈ vStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N)) := heq ▸ hQ
    have hc := hcomm Mb hMbΦ hMbV Q hQV
    have hQN : Q ≤ Subgroup.normalizer (Mb : Set (Y ⧸ N)) := by
      refine le_normalizer_of_commutator_le ?_
      rw [Subgroup.commutator_comm]
      exact hc.trans (inf_le_left.trans (oddCoreOf_le_self Mb))
    intro g hg
    refine ⟨hQN hg, fun m hm => ?_⟩
    rw [← commutatorElement_inv]
    exact (oddCoreOf Mb).inv_mem (hc (Subgroup.commutator_mem_commutator hm hg)).1
  have hPC : omegaGen (aStar (quotFamily Φ N) (K.map (QuotientGroup.mk' N))) ≤ C :=
    iSup₂_le hQC
  obtain ⟨-, R, hR, hRnc⟩ := hΦ'.omega1 Mb hMbΦ
  apply hRnc
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hbM : (b : Y ⧸ N) ∈ Mb := hR.1 b.2
  have haC : (a : Y ⧸ N) ∈ C := hPC (hMbP (hR.1 a.2))
  have h1 : ⁅(a : Y ⧸ N), (b : Y ⧸ N)⁆ ∈ oddCoreOf Mb := haC.2 _ hbM
  have h2 : ⁅(a : Y ⧸ N), (b : Y ⧸ N)⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem a.2 b.2) (R.inv_mem a.2)) (R.inv_mem b.2)
  have h3 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Mb) h1
    (hR.2.1.to_le (Subgroup.zpowers_le.mpr h2))
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

theorem thm3RowsG_omegaGen_aStar (hΦ : TypeRHyp Φ) (hN : Odd (Nat.card N)) {K : Subgroup Y}
    (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K)
    (hC : Thm3RConclG (quotFamily Φ N) (K.map (QuotientGroup.mk' N))) :
    Thm3RowsG Φ (omegaGen (aStar Φ K)) ∧ Thm3RowsG Φ (N ⊔ omegaGen (aStar Φ K)) := by
  have hΩ : HypOmegaGen Φ := hΦ.hyp
  have hrows := hC.2
  rw [← omegaGen_aStar_map hΩ hN hK] at hrows
  refine ⟨?_, ?_⟩
  · refine (thm3RowsG_map_iff_of_le hN ?_).mp hrows
    intro L hL h
    have hL' : L ≤ N ⊔ omegaGen (aStar Φ K) := by
      have := Subgroup.map_le_iff_le_comap.mp h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm] at this
    exact le_omegaGen ((le_omegaGen_aStar_iff hΦ hN hK hA hC.1 hL).mp hL')
  · rw [← map_sup_mk (N := N)] at hrows
    exact (thm3RowsG_map_iff hN Φ le_sup_left).mp hrows

theorem thm3RowsG_omegaGen_aStar_of_quot (hQ : Thm3RGroupQuotG Y) (hΦ : TypeRHyp Φ)
    {K : Subgroup Y} (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) :
    Thm3RowsG Φ (omegaGen (aStar Φ K)) ∧
      Thm3RowsG Φ (classicalInvolutionOddCore Y ⊔ omegaGen (aStar Φ K)) :=
  thm3RowsG_omegaGen_aStar hΦ (CFSG.ComponentClassification.OddCore.odd_card Y) hK hA
    (hQ Φ hΦ K hK hA)

end Members

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot
