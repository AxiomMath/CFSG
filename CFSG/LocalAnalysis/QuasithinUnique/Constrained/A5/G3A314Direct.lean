module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314
public import CFSG.Quasithin.Background.A3Structure314Cases
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeFive
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs314
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.Quasithin.Background.KnownMultL2
public import CFSG.Quasithin.Vol2.Ch1List

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.Assembly.LowTwoRank

@[expose] def Rank2NoDelta5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L P : Subgroup G), IsRank2LieChar2 ↥L → IsMaxParabolic2 L P →
    ¬ IsDelta5Group ↥(perfectCore P)

@[expose] def MathieuNoDelta5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T B : Subgroup G),
    (IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥L) →
    IsSylowTwoOf T L → B ≤ L → T ≤ Subgroup.normalizer (B : Set G) → ¬ IsDelta5Group ↥B

structure Delta5Rows : Prop where
  rank2 : Rank2NoDelta5
  mathieu : MathieuNoDelta5
  j4 : A314J4NoDelta5

theorem not_isAlt_five_of_delta5 {X : Type} [Group X] [Finite X] (hD : IsDelta5Group X)
    (h : IsAlt 5 X) : False := by
  have h1 := A314.card_isAlt_five h
  have h2 := hD.card
  omega

theorem not_a312Case_of_delta5 {G : Type} [Group G] [Finite G] {T B L : Subgroup G}
    (hM : A314ModelFacts) (hR : Delta5Rows) (hD : IsDelta5Group ↥B) (hTL : IsSylowTwoOf T L)
    (hBL : B ≤ L) (hTB : T ≤ Subgroup.normalizer (B : Set G)) (hcase : A312Case B L) : False := by
  have hA : IsAlt 5 (↥B ⧸ CFSG.solvableRadical ↥B) := hD.isAlt_modRadical
  have hcard := hD.card
  have hPV4 : ∀ (V : Type) [Group V] [Finite V], IsE2 4 V → Group.IsSolvable V :=
    fun V _ _ h => A314.solvable_isE2 4 V h
  unfold A312Case at hcase
  rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  ·
    obtain ⟨-, hrk, P, hP, hBP⟩ := h
    subst hBP
    exact hR.rank2 G L P hrk hP hD
  ·
    obtain ⟨f, hf, -⟩ := h
    exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hf⟩))))) hA
  ·
    obtain ⟨hB3, -⟩ := h
    exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _) (Or.inl hB3) hA
  ·
    obtain ⟨hB4, -⟩ := h
    exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
      (Or.inr (Or.inl hB4)) hA
  ·
    obtain ⟨hB5 | hB3, -⟩ := h
    · exact not_isAlt_five_of_delta5 hD hB5
    · exact A314.excl_model_self hM (Or.inl hB3) hA
  ·
    rcases h with ⟨hB, -⟩ | ⟨hB, -⟩
    · exact A314.excl_alt_self (by norm_num) (by norm_num) hB hA
    · exact A314.excl_hat_self hB A314.hS_alt_six hA
  ·
    rcases h with ⟨p, hp, hp3, hBp, -⟩ | ⟨hB5, -⟩
    · obtain ⟨hs, hna, -⟩ := hM.2.2 p hp hp3 ↥B hBp
      exact not_isAlt_five_of_delta5 hD (A314.isAlt_of_simple hs hna hA)
    · exact not_isAlt_five_of_delta5 hD hB5
  ·
    rcases h with ⟨s, p, hp, hp3, hBp, -⟩ | ⟨hB, -⟩ | ⟨hB, -⟩
    · have hp5 : p = 5 := by
        let e : ↥B ⧸ (⊥ : Subgroup ↥B) ≃* ↥B := QuotientGroup.quotientBot
        exact A314.p_eq_five_of_sl2 (V := ⊥)
          (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _) hp hp3
          (IsSL2.of_mulEquiv e.symm hBp) hA
      subst hp5
      have := card_isSL2_five hBp
      omega
    · exact A314.excl_alt_self (by norm_num) (by norm_num) hB hA
    · exact A314.excl_hat_self hB A314.hS_alt_six hA
  ·
    obtain ⟨p, hp, hp3, hBext, -⟩ := h
    have hp5 : p = 5 := by
      obtain ⟨V, hVn, hV, hY⟩ := hBext
      exact A314.p_eq_five_of_sl2 (A314.solvable_of_isElemAbelianOfRank hV) hp hp3 hY hA
    subst hp5
    obtain ⟨V, hVn, hV, hY⟩ := hBext
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [card_of_isElemAbelianOfRank hV, card_isSL2_five hY, hcard] at h1
    omega
  ·
    exact A314.excl_alt_self (by norm_num) (by norm_num) h.1 hA
  ·
    rcases h with ⟨hB | hB, hL⟩ | ⟨hB | hB, hL⟩
    · exact hR.mathieu G L T B (Or.inl hL) hTL hBL hTB hD
    · exact A314.excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) hA
    · exact hR.mathieu G L T B (Or.inr (Or.inl hL)) hTL hBL hTB hD
    · exact A314.excl_hat_ext hB hPV4 (fun Y _ hY => hY) A314.hS_alt_six hA
  ·
    have hPV3 : ∀ (V : Type) [Group V] [Finite V], IsE2 3 V → Group.IsSolvable V :=
      fun V _ _ h => A314.solvable_isE2 3 V h
    obtain ⟨hB | hB | hB | hB | hB | hB | hB, hL⟩ := h
    · exact A314.excl_model_self hM (Or.inr (Or.inr (Or.inr (Or.inl hB)))) hA
    · exact A314.excl_model_self hM (Or.inr (Or.inr (Or.inl hB))) hA
    · exact A314.excl_alt_ext (n := 7) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) hA
    · exact A314.excl_model_ext hM hB hPV4 (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_model_ext hM hB hPV3 (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_alt_ext (n := 6) (by norm_num) (by norm_num) hB hPV4 (fun Y _ hY => hY) hA
    · exact hR.mathieu G L T B (Or.inr (Or.inr hL)) hTL hBL hTB hD
  ·
    obtain ⟨hB | hB | hB | hB, -⟩ := h
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_isE2 4 V h)
        (fun Y _ hY => Or.inr (Or.inl hY)) hA
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_isE2 6 V h)
        (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_of_isExtraspecial2 h)
        (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_hat_ext hB (fun V _ _ h => A314.solvable_isE2 6 V h) (fun Y _ hY => hY)
        A314.hS_alt_six hA
  ·
    exact not_isAlt_five_of_delta5 hD h.1
  ·
    obtain ⟨⟨V, hVn, hV, hY⟩, -⟩ := h
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
    rw [hV.2, A314.card_isAlt_five hY, hcard] at h1
    omega
  ·
    obtain ⟨hL, hB | hB | hB | hB | hB | hB⟩ := h
    · exact A314.excl_hat_ext hB (fun V _ _ h => A314.solvable_of_isExtraspecial2 h)
        (fun Y _ hY => hY) (A314.hS_m22 hM) hA
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_isE2 11 V h)
        (fun Y _ hY => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hY))))) hA
    · exact hR.j4 G L B T hL hTL hBL hTB hD
    · exact A314.excl_hat (V := CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _) hB A314.hS_alt_six hA
    · exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
        (Or.inr (Or.inl hB)) hA
    · exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
        (Or.inl hB) hA
  ·
    obtain ⟨hB | hB, -⟩ := h
    · obtain ⟨V, hVn, hV, hY⟩ := hB
      obtain ⟨Z, E, -, -, hE, -⟩ := hV
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
      rw [A314.card_isAlt_five hY, hcard] at h1
      have h2 : Nat.card E ≤ Nat.card V := Subgroup.card_le_card_group _
      rw [hE.2] at h2
      omega
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_of_isZ4Cubed h)
        (fun Y _ hY => Or.inl hY) hA
  ·
    obtain ⟨hB | hB, -⟩ := h
    · exact A314.excl_model_ext hM hB (fun V _ _ h => A314.solvable_of_isExtraspecial2 h)
        (fun Y _ hY => Or.inl hY) hA
    · exact A314.excl_hat_ext hB (fun V _ _ h => A314.solvable_isE2 6 V h) (fun Y _ hY => hY)
        A314.hS_alt_six hA
  ·
    obtain ⟨hB | hB, h11, -⟩ := h
    · have := hD.card_pCore
      rw [h11] at this
      omega
    · exact A314.excl_model_mod hM (CFSG.pCore 2 ↥B) (A314.solvable_pCore_two _)
        (Or.inl hB) hA

@[expose] def NoDelta5In (X : Type) [Group X] [Finite X] : Prop :=
  ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ →
    T ≤ Subgroup.normalizer (B : Set X) → ¬ IsDelta5Group ↥B

theorem noDelta5In_of_a312Case {X : Type} [Group X] [Finite X] (hM : A314ModelFacts)
    (hR : Delta5Rows)
    (hX : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ → A312Case B ⊤) :
    NoDelta5In X := by
  intro T hT B hB hne hTB hD
  exact not_a312Case_of_delta5 hM hR hD hT le_top hTB (hX T hT B hB hne)

section Reduction

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem subgroupOf_le_normalizer {N B Λ : Subgroup G} (h : N ≤ Subgroup.normalizer (B : Set G)) :
    N.subgroupOf Λ ≤ Subgroup.normalizer ((B.subgroupOf Λ : Subgroup ↥Λ) : Set ↥Λ) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hx' : (x : G) ∈ Subgroup.normalizer (B : Set G) := h (Subgroup.mem_subgroupOf.mp hx)
  have := Subgroup.mem_normalizer_iff.mp hx' (y : G)
  simpa using this

theorem a314A5Excluded_of_noDelta5 (hcore : A36CoreForSQTKCat) (h37 : A37ForSQTKCat)
    (h39 : A39ForSQTKCat)
    (hΔ : ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
      CFSG.SectionRank.IsSQTKCat X → CFSG.pCore 2 X = ⊥ → NoDelta5In X) :
    A314A5Excluded := by
  intro G _ _ C S L hC hS hO hOZ hLC hLs hLa hQU hZ hSN
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : SQTKHypCat (↥C ⧸ CFSG.pCore 2 ↥C) := SQTKHypCat.quotient_pCore ↥C hC
  have hD : IsDelta5Group ↥L := isDelta5Group_of_block hLa hZ hQU
  have hqL : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    hLs.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl hLa)
  have hNorm : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSN)
  have hB : L ∈ lFamily S :=
    C1GN.mem_cComp_of_short hLs hqL (A3.subnormal_of_normal le_sup_left hNorm)
  obtain ⟨Λ, hΛ, hLΛ⟩ := exists_cComp_ge_of_subgroup hS hLC hB (h37 _ hQ) (h39 _ hQ)
  have hΛC : Λ ≤ C := le_of_mem_cComp hΛ
  have hZΛ : pCoreOf 2 Λ ≤ centerOf Λ := by
    intro x hx
    have hxC : x ∈ pCoreOf 2 C := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hΛ) hx
    refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 Λ hx,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp (hOZ hxC) y (hΛC hy)
  have hUcard : Nat.card ↥(blockU L) = 2 ^ 4 := by
    rw [← hQU]
    have h1 : Nat.card ↥(blockQ L) = Nat.card ↥(CFSG.pCore 2 ↥L) := by
      unfold blockQ pCoreOf
      rw [Subgroup.card_map_of_injective L.subtype_injective]
    rw [h1, hD.card_pCore]
    norm_num
  have hUL : blockU L ≤ L := by
    rw [← hQU]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hUe : IsElemAbelian 2 (blockU L) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, hLs.2.2.1.2⟩
    have hc := Subgroup.mem_centralizer_iff.mp (hLs.2.2.1.1 a.2).2 b (hLs.2.2.1.1 b.2).1
    exact Subtype.ext hc.symm
  have hm : 1 < CFSG.Open.pRank 2 Λ :=
    lt_of_lt_of_le (by norm_num : 1 < 4)
      (CFSG.SectionRank.le_pRank (by norm_num) (hUL.trans hLΛ) hUe hUcard)
  have hcoreΛ : A36CoreCat (modO2Image C Λ) := hcore _ hQ _ (modO2Image_mem_cComp hΛ)
  have hΛq : CFSG.IsQuasisimple ↥Λ :=
    lemma_1_2_1_five_of_core CFSG.Quasithin.l2MultiplierFact hΛ hcoreΛ hZΛ hm
  have hΛbar : modO2Image C Λ ∈ cComp (⊤ : Subgroup (↥C ⧸ CFSG.pCore 2 ↥C)) :=
    modO2Image_mem_cComp hΛ
  have hΛbq : CFSG.IsQuasisimple ↥(modO2Image C Λ) := by
    obtain ⟨ψ, hψ, hker⟩ := exists_modO2_surjection hΛ
    have hKc : ψ.ker ≤ Subgroup.center ↥Λ := by
      rw [hker]
      intro x hx
      have hxG : (x : G) ∈ pCoreOf 2 Λ := (mem_pCore_iff_mem_pCoreOf x).mp hx
      have hxc := (hZΛ hxG).2
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (by simpa using (Subgroup.mem_centralizer_iff.mp hxc (g : G) g.2))
    exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective
      (A36A.isPerfect_of_mem_cComp hΛ) ψ hψ hKc).mp hΛq
  have hψinj := injective_modO2 hLC hOZ hZ hQU
  have hrange : ((QuotientGroup.mk' (CFSG.pCore 2 ↥C)).comp (Subgroup.inclusion hLC)).range =
      modO2Image C L := by
    unfold modO2Image
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  let e : ↥L ≃* ↥(modO2Image C L) :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hrange)
  have hDB : IsDelta5Group ↥(modO2Image C L) := hD.of_equiv e
  have hSbar := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥C)) (QuotientGroup.mk'_surjective _)
  have hBfam := modO2Image_mem_lFamily hS hLC hB
  have hBLbar : modO2Image C L ≤ modO2Image C Λ := Subgroup.map_mono (fun x hx => hLΛ hx)
  have hBne : modO2Image C L ≠ modO2Image C Λ := by
    intro h
    apply hDB.not_isQuasisimple
    rw [h]
    exact hΛbq
  obtain ⟨hT', hB'⟩ := A312.isSylowTwoOf_lFamily_subgroupOf hSbar hΛbar hBLbar hBfam
  have hΛ' : SQTKHypCat ↥(modO2Image C Λ) := hQ.of_subnormal (subnormal_of_mem_cComp hΛbar)
  have hne' : (modO2Image C L).subgroupOf (modO2Image C Λ) ≠ ⊤ := by
    intro h
    apply hBne
    refine le_antisymm hBLbar (fun x hx => ?_)
    have : (⟨x, hx⟩ : ↥(modO2Image C Λ)) ∈ (modO2Image C L).subgroupOf (modO2Image C Λ) := by
      rw [h]; exact Subgroup.mem_top _
    exact this
  have hTN : ((((S.subgroupOf C).map (QuotientGroup.mk' (CFSG.pCore 2 ↥C))) ⊓
        modO2Image C Λ).subgroupOf (modO2Image C Λ)) ≤
      Subgroup.normalizer (((modO2Image C L).subgroupOf (modO2Image C Λ) : Subgroup
        ↥(modO2Image C Λ)) : Set ↥(modO2Image C Λ)) :=
    subgroupOf_le_normalizer (inf_le_left.trans (map_normalizes hSN))
  have hD' : IsDelta5Group ↥((modO2Image C L).subgroupOf (modO2Image C Λ)) :=
    hDB.of_equiv (Subgroup.subgroupOfEquivOfLe hBLbar).symm
  exact hΔ ↥(modO2Image C Λ) hΛbq hΛ'.isSQTKCat hΛ'.o2 _ hT' _ hB' hne' hTN hD'

end Reduction

end CFSG.QuasithinUnique.A5.G3
