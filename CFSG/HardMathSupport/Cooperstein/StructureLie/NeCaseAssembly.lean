module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseLevi
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseCore
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseSylow
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseBlock
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseRadical

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock IsTwoPrimeComponent barM Asc81bEightFour
  IsClassicalTwoOrG2)
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput (IsChevOver LeviStructure LeviModR
  CentralizerInRadical)
open CFSG.HardMathSupport.Cooperstein.Proving (mem_pCoreOf_iff)
open scoped commutatorElement

section Generic

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_of_commutator_le {A B R : Subgroup Γ} (hR : R ≤ A) (hc : ⁅A, B⁆ ≤ R) :
    B ≤ Subgroup.normalizer (A : Set Γ) := by
  have key : ∀ c ∈ B, ∀ a ∈ A, c * a * c⁻¹ ∈ A := by
    intro c hc' a ha
    have h1 : ⁅a, c⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hc'
    have h2 : ⁅c, a⁆ ∈ A := by
      have := hR (hc h1)
      have h3 : ⁅c, a⁆ = ⁅a, c⁆⁻¹ := (commutatorElement_inv a c).symm
      rw [h3]; exact A.inv_mem this
    have : c * a * c⁻¹ = ⁅c, a⁆ * a := by simp only [commutatorElement_def]; group
    rw [this]
    exact A.mul_mem h2 ha
  intro c hc'
  exact mem_normalizer_of_conj_mem_both (key c hc') (fun a ha => by
    simpa using key c⁻¹ (B.inv_mem hc') a ha)

end Generic

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem comm_mem_pCoreOf_neX1 (hA : Asc81bHyp X S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {y s : G} (hy : y ∈ neY S L) (hyN : y ∈ Subgroup.normalizer (S : Set G)) (hs : s ∈ S) :
    y * s * y⁻¹ * s⁻¹ ∈ pCoreOf 2 (neX1 S L) := by
  refine inf_le_pCoreOf_neX1 hA hSL ⟨?_, ?_⟩
  · have h1 : y * s * y⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hyN s).mp hs
    exact S.mul_mem h1 (S.inv_mem hs)
  · have h1 : s * y⁻¹ * s⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hSL hs) _).mp (L.inv_mem hy.1)
    have h2 := L.mul_mem hy.1 h1
    rwa [show y * (s * y⁻¹ * s⁻¹) = y * s * y⁻¹ * s⁻¹ by group] at h2

theorem isSolvable_neYh (hQ : pCoreOf 2 X ≤ S) (hLX : L ≤ X) (hQ2 : IsPGroup 2 (pCoreOf 2 X))
    {Dc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} [Group.IsSolvable ↥Dc] :
    Group.IsSolvable ↥(neYh X S L Dc) := by
  have hDhX : neYh X S L Dc ≤ X := (neYh_le_neY Dc).trans (inf_le_left.trans hLX)
  set g := barIncl X hDhX with hg
  have hrange : g.range ≤ Dc := by
    rintro _ ⟨y, rfl⟩
    exact barHom_mem_of_mem_neYh (x := Subgroup.inclusion hDhX y) y.2
  have : Group.IsSolvable ↥g.range :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hrange)
      (Subgroup.inclusion_injective hrange)
  have : Finite ↥(pCoreOf 2 X ⊓ neYh X S L Dc) := inferInstance
  have hN0 : IsPGroup 2 ↥(pCoreOf 2 X ⊓ neYh X S L Dc) := hQ2.to_le inf_le_left
  have : Group.IsNilpotent ↥(pCoreOf 2 X ⊓ neYh X S L Dc) := hN0.isNilpotent
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_right :
    pCoreOf 2 X ⊓ neYh X S L Dc ≤ neYh X S L Dc)) g.rangeRestrict ?_
  intro y hy
  rw [MonoidHom.ker_rangeRestrict, mem_ker_barIncl hDhX] at hy
  exact ⟨⟨(y : G), hy, y.2⟩, rfl⟩

theorem neY_le_sup_neYh (_hQ : pCoreOf 2 X ≤ S) (hLX : L ≤ X) {n : ℕ}
    {Dc : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} {Yc : Fin n → Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hsup : barM X (neY S L) = Dc ⊔ ⨆ i, Yc i) :
    neY S L ≤ neYh X S L Dc ⊔ ⨆ i, neYh X S L (Yc i) := by
  have hDc : Dc ≤ barM X (neY S L) := by rw [hsup]; exact le_sup_left
  have hYc : ∀ i, Yc i ≤ barM X (neY S L) := fun i => by
    rw [hsup]; exact le_sup_of_le_right (le_iSup Yc i)
  set T := neYh X S L Dc ⊔ ⨆ i, neYh X S L (Yc i) with hT
  have hTY : T ≤ neY S L :=
    sup_le (neYh_le_neY _) (iSup_le fun i => neYh_le_neY _)
  have hB : barM X (neY S L) ≤ barM X T := by
    rw [hsup]
    refine sup_le ((mem_barM_neYh hDc).trans (barM_mono le_sup_left)) (iSup_le fun i => ?_)
    exact (mem_barM_neYh (hYc i)).trans (barM_mono (le_sup_of_le_right
      (le_iSup (fun i => neYh X S L (Yc i)) i)))
  intro y hy
  have hyX : y ∈ X := hLX hy.1
  obtain ⟨x, hxT, hx⟩ := mem_barM_iff.mp (hB (barHom_mem_barM (X := X) (Y := neY S L)
    (x := ⟨y, hyX⟩) hy))
  have hxY : (x : G) ∈ neY S L := hTY hxT
  have h1 : barHom X (x⁻¹ * ⟨y, hyX⟩) = 1 := by rw [map_mul, map_inv, hx, inv_mul_cancel]
  have h2 : (x⁻¹ * ⟨y, hyX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff _).mp h1
  have hz : (((x⁻¹ * ⟨y, hyX⟩ : ↥X)) : G) ∈ neYh X S L Dc := by
    refine mem_neYh.mpr ⟨?_, x⁻¹ * ⟨y, hyX⟩, rfl, ?_⟩
    · have := (neY S L).mul_mem ((neY S L).inv_mem hxY) hy
      simpa using this
    · rw [h1]; exact Dc.one_mem
  have hyxz : y = (x : G) * (((x⁻¹ * ⟨y, hyX⟩ : ↥X)) : G) := by simp
  rw [hyxz]
  exact T.mul_mem hxT (Subgroup.mem_sup_left hz)

theorem neY_le_normalizer (h84 : Asc81bEightFour)
    (hbot : CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineBotCase)
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hcent : CentralizerInRadical (barM X L) (barM X (S ⊓ L)))
    (hlevi : LeviModR (barM X L) (barM X (S ⊓ L))) :
    ∀ y ∈ neY S L, y ∈ Subgroup.normalizer (S : Set G) := by
  classical
  obtain ⟨n, Yc, D, hRD, hDY, hDsolv, hYc, hcomm, hsup⟩ := hlevi
  have hQ : pCoreOf 2 X ≤ S := hA.twoCore_le
  have hSX : S ≤ X := hA.twoRadical.1
  have hLX : L ≤ X := hL.le
  have hX1X : neX1 S L ≤ X := (neX1_le_sup S L).trans (sup_le hLX hSX)
  have hBY : barM X (neY S L) = D ⊔ ⨆ i, Yc i := (barM_neY hQ hLX).trans hsup
  have hYcBY : ∀ i, Yc i ≤ barM X (neY S L) := fun i => by
    rw [hBY]; exact le_sup_of_le_right (le_iSup Yc i)
  have hDBY : D ≤ barM X (neY S L) := by rw [hBY]; exact le_sup_left
  have hNYc : ∀ i, barM X (neY S L) ≤ Subgroup.normalizer (Yc i : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    intro i
    rw [hBY]
    refine sup_le (hYc i).2.2.2 (iSup_le fun j => ?_)
    by_cases hij : j = i
    · subst hij; exact Subgroup.le_normalizer
    · refine le_normalizer_of_commutator_le (hYc i).1 ?_
      rw [Subgroup.commutator_comm]
      exact hcomm j i hij
  have hYhN : ∀ i, neYh X S L (Yc i) ≤ Subgroup.normalizer (S : Set G) := fun i =>
    yh_le_normalizer hbot hX hA hL hSL hcent (neYh_le_neY _)
      (normal_neYh_subgroupOf hLX (hNYc i))
      (isChevOver_neYh hQ hLX (hYcBY i) (hYc i).2.2.1)
  have hA1 := asc81bHyp_neX1 hA hL hSL
  have hY1n : ((neY S L).subgroupOf (neX1 S L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (neY_le_neX1 S L)).mpr
      (sup_le Subgroup.le_normalizer (le_normalizer_neY hSL))
  have hMn : (barM (neX1 S L) (neY S L)).Normal :=
    hY1n.map (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hH := CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' (X := neX1 S L) 2
  set E : Subgroup (↥(neX1 S L) ⧸ CFSG.pCore 2 ↥(neX1 S L)) :=
    ⨆ i, barM (neX1 S L) (neYh X S L (Yc i)) with hE
  set D' : Subgroup (↥(neX1 S L) ⧸ CFSG.pCore 2 ↥(neX1 S L)) :=
    barM (neX1 S L) (neYh X S L D) with hD'
  have hEconj : ∀ m ∈ barM (neX1 S L) (neY S L), ∀ t ∈ E, m * t * m⁻¹ ∈ E := by
    intro m hm t ht
    obtain ⟨y0, hy0, rfl⟩ := mem_barM_iff.mp hm
    have hmap : E.map (MulAut.conj (barHom (neX1 S L) y0)).toMonoidHom ≤ E := by
      rw [hE, Subgroup.map_iSup]
      refine iSup_mono fun i => ?_
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hu
      have h1 : (y0 : G) * (x : G) * (y0 : G)⁻¹ ∈ neYh X S L (Yc i) :=
        conj_mem_neYh hLX (hNYc i) hy0 hx
      have h2 := barHom_mem_barM (X := neX1 S L) (Y := neYh X S L (Yc i))
        (x := y0 * x * y0⁻¹) (by simpa using h1)
      simpa using h2
    exact hmap ⟨t, ht, rfl⟩
  have hDM : D' ≤ barM (neX1 S L) (neY S L) := barM_mono (neYh_le_neY D)
  have hDs : Group.IsSolvable ↥D' := by
    have : Group.IsSolvable ↥D := hDsolv
    have : Group.IsSolvable ↥(neYh X S L D) := isSolvable_neYh hQ hLX (pCoreOf_isPGroup 2 X)
    have hDhX1 : neYh X S L D ≤ neX1 S L := (neYh_le_neY D).trans (neY_le_neX1 S L)
    have hsurj := MonoidHom.rangeRestrict_surjective (barIncl (neX1 S L) hDhX1)
    have : Group.IsSolvable ↥(barIncl (neX1 S L) hDhX1).range :=
      Group.isSolvable_of_surjective hsurj
    rw [hD', ← range_barIncl hDhX1]
    infer_instance
  have hMED : barM (neX1 S L) (neY S L) ≤ E ⊔ D' := by
    have hYle := neY_le_sup_neYh hQ hLX hBY
    let W : Subgroup G := ((E ⊔ D').comap (barHom (neX1 S L))).map (neX1 S L).subtype
    have hW : ∀ {A : Subgroup G}, A ≤ neY S L → barM (neX1 S L) A ≤ E ⊔ D' → A ≤ W := by
      intro A hAY hA' y hy
      exact ⟨⟨y, neY_le_neX1 S L (hAY hy)⟩, hA' (barHom_mem_barM (X := neX1 S L) (Y := A)
        (x := ⟨y, neY_le_neX1 S L (hAY hy)⟩) hy), rfl⟩
    have hYW : neY S L ≤ W := by
      refine hYle.trans (sup_le (hW (neYh_le_neY D) le_sup_right) (iSup_le fun i => ?_))
      exact hW (neYh_le_neY _) (le_sup_of_le_left (le_iSup (fun i => barM (neX1 S L)
        (neYh X S L (Yc i))) i))
    intro γ hγ
    obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp hγ
    obtain ⟨x', hx', hxx'⟩ := hYW hx
    have : x' = x := Subtype.ext hxx'
    rwa [this] at hx'
  have hsc : ∀ s ∈ S, ∀ y ∈ neY S L, y * s * y⁻¹ * s⁻¹ ∈ pCoreOf 2 (neX1 S L) := by
    intro s hs y hy
    have hsX1 : s ∈ neX1 S L := le_neX1 S L hs
    have hyX1 : y ∈ neX1 S L := neY_le_neX1 S L hy
    set sb := barHom (neX1 S L) ⟨s, hsX1⟩ with hsb
    have hs2 : ∃ e : ℕ, sb ^ (2 ^ e) = 1 := by
      obtain ⟨e, he⟩ := hA.twoRadical.isPGroup ⟨s, hs⟩
      refine ⟨e, ?_⟩
      rw [hsb, ← map_pow]
      have : (⟨s, hsX1⟩ : ↥(neX1 S L)) ^ (2 ^ e) = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
      rw [this, map_one]
    obtain ⟨e, he⟩ := hs2
    have hEc : ∀ t ∈ E, sb * t = t * sb := by
      have hle : E ≤ Subgroup.centralizer ({sb} : Set _) := by
        refine iSup_le fun i => ?_
        intro t ht
        obtain ⟨x, hx, rfl⟩ := mem_barM_iff.mp ht
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh, hsb]
        refine barHom_comm_iff.mpr ?_
        have h1 := comm_mem_pCoreOf_neX1 hA hSL (neYh_le_neY _ hx) (hYhN i hx) hs
        have : (s : G) * (x : G) * (s : G)⁻¹ * (x : G)⁻¹ =
            ((x : G) * s * (x : G)⁻¹ * s⁻¹)⁻¹ := by group
        show (s : G) * (x : G) * (s : G)⁻¹ * (x : G)⁻¹ ∈ _
        rw [this]
        exact (pCoreOf 2 (neX1 S L)).inv_mem h1
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp (hle ht) sb rfl)
    have hOc : ∀ t ∈ barM (neX1 S L) (neY S L),
        t ∈ CFSG.pPrimeCore 2 (↥(neX1 S L) ⧸ CFSG.pCore 2 ↥(neX1 S L)) → sb * t = t * sb := by
      intro t _ ht
      exact Subgroup.mem_centralizer_iff.mp
        (centralizes_pPrimeCore_neX1 h84 hX hA hL hSL hcent ht) sb
        (barHom_mem_barM (X := neX1 S L) (Y := S) (x := ⟨s, hsX1⟩) hs)
    have hcm := core_commute hH (M := barM (neX1 S L) (neY S L)) (E := E) (D := D') hEconj hDM hDs
      hMED he hEc hOc (barHom (neX1 S L) ⟨y, hyX1⟩)
      (barHom_mem_barM (X := neX1 S L) (Y := neY S L) (x := ⟨y, hyX1⟩) hy)
    have h3 := (barHom_comm_iff (X := neX1 S L)).mp hcm.symm
    exact h3
  intro y hy
  refine mem_normalizer_of_conj_mem_both (fun s hs => ?_) (fun s hs => ?_)
  · have h1 := hA1.twoCore_le (hsc s hs y hy)
    have := S.mul_mem h1 hs
    simpa [mul_assoc] using this
  · have h1 := hA1.twoCore_le (hsc s hs y⁻¹ ((neY S L).inv_mem hy))
    have := S.mul_mem h1 hs
    simpa [mul_assoc] using this

theorem eightNineNeCase_of_bot
    (hbot : CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineBotCase)
    (hLevi : ∀ (Γ : Type) [Group Γ] [Finite Γ] (L R : Subgroup Γ), IsClassicalTwoOrG2 (↥L ⧸
        Subgroup.center ↥L) → R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set Γ)) → LeviStructure L
        R ∧ LeviModR L R)
    (hCent : ∀ (Γ : Type) [Group Γ] [Finite Γ] (L R : Subgroup Γ), IsClassicalTwoOrG2 (↥L ⧸
        Subgroup.center ↥L) → R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set Γ)) → L ⊓
        Subgroup.normalizer (R : Set Γ) ≠ L → CentralizerInRadical L R) :
    EightNineNeCase := by
  intro G _ _ X S L hX hA hL hc hne _hSyl
  have hSL := CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hTP := hL.toIsTwoPrimeComponent
  have hrad := barM_inf_eq_pCoreOf_normalizer hA hTP
  have hlevi := (hLevi _ (barM X L) (barM X (S ⊓ L)) hc hrad).2
  have hcent := hCent _ (barM X L) (barM X (S ⊓ L)) hc hrad
    (inf_normalizer_ne_of_ne_bot hA hL hne)
  exact normalizer_barM_le_of_forall hA.twoCore_le hL.le
    (neY_le_normalizer (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
        CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved) hbot hX hA
      hTP hSL hcent hlevi)

theorem eightNineNonParabolic_of_bot
    (h85 : CFSG.AGLEmbedding.Asc81bEightFive)
    (hbot : CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineBotCase)
    (hLevi : ∀ (Γ : Type) [Group Γ] [Finite Γ] (L R : Subgroup Γ), IsClassicalTwoOrG2 (↥L ⧸
        Subgroup.center ↥L) → R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set Γ)) → LeviStructure L
        R ∧ LeviModR L R)
    (hCent : ∀ (Γ : Type) [Group Γ] [Finite Γ] (L R : Subgroup Γ), IsClassicalTwoOrG2 (↥L ⧸
        Subgroup.center ↥L) → R = pCoreOf 2 (L ⊓ Subgroup.normalizer (R : Set Γ)) → L ⊓
        Subgroup.normalizer (R : Set Γ) ≠ L → CentralizerInRadical L R) :
    EightNineNonParabolic :=
  eightNineNonParabolic_of_split h85 hbot (eightNineNeCase_of_bot hbot hLevi hCent)

end CFSG.HardMathSupport.Cooperstein.StructureLie
