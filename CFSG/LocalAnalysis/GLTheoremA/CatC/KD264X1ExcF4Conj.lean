module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Red
public import CFSG.LocalAnalysis.StandardType.GGExcFrameNormIsoF4
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType
  CFSG.StandardType.TableBExc CFSG.StandardType.TableBExcTwoFusion CFSG.StandardType.TableBF4Two
  CFSG.StandardType.TableBF4TwoTB CFSG.Assembly Matrix

namespace X1F4Conj

theorem prod_map_rootReflection_smul {τ : Tag}
    (l : List (Fin τ.rank → ℤ)) (hl : ∀ β ∈ l, IsRoot τ β)
    (v : Fin τ.rank → ℤ) :
    (l.map rootReflection).prod • v = l.foldr (fun β u => u - corootPair β u • β) v := by
  induction l with
  | nil => simp
  | cons β l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih fun γ hγ => hl γ (List.mem_cons_of_mem _ hγ),
      rootReflection_smul (hl β List.mem_cons_self), List.foldr_cons]

theorem smul_eq_neg_of_forall_single {τ : Tag} {w : WeylGroup τ}
    (h : ∀ i, w • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1) (v : Fin τ.rank → ℤ) :
    w • v = -v := by
  have hlin : CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, ← smul_def, h i]
    simp
  rw [smul_def, hlin]
  simp

theorem frameF4_reflections_single : ∀ j : Fin Tag.F4.rank,
    (List.ofFn orthRoot).foldr (fun β u => u - corootPair β u • β)
      (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = -Pi.single j 1 := by
  decide +kernel

theorem frameF4_reflections
    (v : Fin Tag.F4.rank → ℤ) :
    (List.ofFn fun i : Fin 4 => rootReflection (orthRoot i)).prod • v = -v := by
  refine smul_eq_neg_of_forall_single (fun j => ?_) v
  have e : (List.ofFn fun i : Fin 4 => rootReflection (orthRoot i)) =
      (List.ofFn orthRoot).map rootReflection := by
    rw [List.map_ofFn]
    rfl
  rw [e, prod_map_rootReflection_smul _ (fun β hβ => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hβ
      exact isRoot_orthRoot i)]
  exact frameF4_reflections_single j

theorem nSL_one_mul_HSL_mul_inv {L : Type} [Field L] (t : Lˣ) :
    (nSL (1 : Lˣ) : SL2 L) * HSL t * (nSL (1 : Lˣ))⁻¹ = (HSL t)⁻¹ := by
  rw [nSL_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_WSL, coe_HSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_conj_eq_of_descent {C₁ C₂ : Type} [Group C₁] [Group C₂] [Finite C₁] [Finite C₂]
    {ι : C₁ →* C₂} (hι : Function.Injective ι) {G : C₂} {X V : Subgroup C₂} {T : Subgroup C₁}
    (hdesc : ∀ m ∈ X, ∃ m₀ : C₁, ι m₀ = G * m * G⁻¹) (hidx : ¬ 3 ∣ X.index)
    (hV : (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom = V)
    (hX : ∀ E' : Subgroup C₂, IsElemAbelian 3 E' → E' ≤ X → 3 ^ 4 ≤ Nat.card E' → E' = V)
    {E : Subgroup C₁} (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card E) :
    ∃ c : C₁, E = T.map (MulAut.conj c).toMonoidHom := by
  have hXj : X.map (MulAut.conj G).toMonoidHom ≤ ι.range := by
    rintro _ ⟨m, hmX, rfl⟩
    obtain ⟨m₀, hm₀⟩ := hdesc m hmX
    exact ⟨m₀, hm₀⟩
  have hYidx : ¬ 3 ∣ ((X.map (MulAut.conj G).toMonoidHom).comap ι).index := fun h =>
    hidx (h.trans (index_comap_dvd hι G hXj))
  obtain ⟨x, hx⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hYidx
    (TableB.isPGroup_of_isElemAbelian hE)
  have hE'X : ((E.map (MulAut.conj x).toMonoidHom).map ι).map (MulAut.conj G⁻¹).toMonoidHom ≤
      X := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    obtain ⟨m, hmX, hm⟩ := hx hb
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hm, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    have e : G⁻¹ * (G * m * G⁻¹) * G⁻¹⁻¹ = m := by group
    rw [e]
    exact hmX
  have hE' : IsElemAbelian 3
      (((E.map (MulAut.conj x).toMonoidHom).map ι).map (MulAut.conj G⁻¹).toMonoidHom) :=
    TableB.isElemAbelian_map (TableB.isElemAbelian_map (TableB.isElemAbelian_map hE _) _) _
  have hcardE' : 3 ^ 4 ≤
      Nat.card (((E.map (MulAut.conj x).toMonoidHom).map ι).map (MulAut.conj G⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj G⁻¹).injective,
      Subgroup.card_map_of_injective hι, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact hcard
  have h1 : (E.map (MulAut.conj x).toMonoidHom).map ι = T.map ι :=
    Subgroup.map_injective (f := (MulAut.conj G⁻¹).toMonoidHom) (MulAut.conj G⁻¹).injective
      ((hX _ hE' hE'X hcardE').trans hV.symm)
  have h2 : E.map (MulAut.conj x).toMonoidHom = T := Subgroup.map_injective hι h1
  refine ⟨x⁻¹, ?_⟩
  have hcc : ∀ g : C₁,
      (MulAut.conj x⁻¹).toMonoidHom ((MulAut.conj x).toMonoidHom g) = g := fun g => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  ext g
  constructor
  · intro hg
    have hg' : (MulAut.conj x).toMonoidHom g ∈ T := h2 ▸ ⟨g, hg, rfl⟩
    exact ⟨_, hg', hcc g⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨g, hg, rfl⟩ := h2 ▸ ht
    rw [hcc g]
    exact hg

theorem torusPow_F4_eq (L : Type) [Field L]
    (p : ℕ) :
    TableBF4.torusPow L p = TableBExc.torusPow .F4 L p :=
  Subgroup.ext fun _ => Iff.rfl

section Frame


theorem frameProdF4_mul {L : Type} [Field L] (A B : SL2 L) :
    ExcFrameIso.frameProdF4 L (A * B) =
      ExcFrameIso.frameProdF4 L A * ExcFrameIso.frameProdF4 L B := by
  rw [ExcFrameIso.frameProdF4, ExcFrameIso.frameProdF4, ExcFrameIso.frameProdF4,
    ← list_prod_ofFn_mul_of_ne]
  · simp only [map_mul]
  · intro i j hij
    exact commute_rho hij A B

theorem adjointMap_rho_F4 {L L' : Type} [Field L] [Field L'] [CharP L 2] (f : L →+* L')
    (i : Fin 4) (A : SL2 L) :
    TableBExcTwo.adjointMap .F4 f (rho L i A) = rho L' i (Matrix.SpecialLinearGroup.map f A) :=
  Subtype.ext (by
    rw [TableBExcTwo.coe_adjointMap, coe_rho, coe_rho]
    exact CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo f (isRoot_orthRoot i) A)

theorem adjointMap_frameProdF4 {L L' : Type} [Field L] [Field L'] [CharP L 2] (f : L →+* L')
    (A : SL2 L) :
    TableBExcTwo.adjointMap .F4 f (ExcFrameIso.frameProdF4 L A) =
      ExcFrameIso.frameProdF4 L' (Matrix.SpecialLinearGroup.map f A) := by
  rw [ExcFrameIso.frameProdF4, ExcFrameIso.frameProdF4, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => adjointMap_rho_F4 f i A))

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem adjointMap_frob_frameProdF4_nSL :
    TableBExcTwo.adjointMap .F4 (frobHom K)
        (ExcFrameIso.frameProdF4 (FiniteField.Extension K 2 2) (nSL 1)) =
      ExcFrameIso.frameProdF4 (FiniteField.Extension K 2 2) (nSL 1) := by
  rw [adjointMap_frameProdF4, map_nSL_one]

theorem adjointMap_frob_langEltF4 (hK : Nat.card K = 2) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hω : orderOf ω = 3) :
    TableBExcTwo.adjointMap .F4 (frobHom K) (ExcFrameIso.langEltF4 hω) =
      ExcFrameIso.langEltF4 hω * ExcFrameIso.frameProdF4 (FiniteField.Extension K 2 2) (nSL 1) := by
  rw [ExcFrameIso.langEltF4, adjointMap_frameProdF4,
    map_langP _ (frobHom K) (by rw [frobHom_apply, frob_eq_sq hK]), frameProdF4_mul]

theorem card_torusPow_F4 (hK : Nat.card K = 2) :
    Nat.card (TableBExc.torusPow .F4 (FiniteField.Extension K 2 2) 3) = 3 ^ 4 := by
  have h3 : 3 ∣ Nat.card (FiniteField.Extension K 2 2) - 1 := three_dvd_natCard_ext_sub_one hK
  have hfull : ∀ a : Fin Tag.F4.rank → (FiniteField.Extension K 2 2)ˣ,
      rootDiagUnit .F4 a ∈ torusGroup .F4 (FiniteField.Extension K 2 2) :=
    fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a
  exact TableBExc.card_torusPow_of_full hfull Nat.prime_three h3

theorem conj_tE_mem_torusPow (hK : Nat.card K = 2) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hωo : orderOf ω = 3) (u : Multiplicative (Fin 4 → ZMod 3)) :
    (ExcFrameIso.langEltF4 hωo)⁻¹ *
      TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)) (tE K u) *
        ExcFrameIso.langEltF4 hωo ∈ TableBExc.torusPow .F4 (FiniteField.Extension K 2 2) 3 := by
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hfull : ∀ a : Fin Tag.F4.rank → (FiniteField.Extension K 2 2)ˣ,
      rootDiagUnit .F4 a ∈ torusGroup .F4 (FiniteField.Extension K 2 2) :=
    fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a
  have hu := ExcFrameIso.adjointMap_tE_eqF4 hωo hω3 hfull (Multiplicative.toAdd u)
  rw [ofAdd_toAdd] at hu
  rw [hu]
  have e : (ExcFrameIso.langEltF4 hωo)⁻¹ * (ExcFrameIso.langEltF4 hωo *
      (⟨ExcFrames.frameDiag ω hω3 (ExcFrameIso.frameCoordHomF4 (Multiplicative.toAdd u)),
        ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ : adjointGroup .F4
          (FiniteField.Extension K 2 2)) * (ExcFrameIso.langEltF4 hωo)⁻¹) *
        ExcFrameIso.langEltF4 hωo = ⟨ExcFrames.frameDiag ω hω3
          (ExcFrameIso.frameCoordHomF4 (Multiplicative.toAdd u)),
        ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ := by group
  rw [e]
  exact ExcFrames.mem_torusPow_iff_coe.mpr (ExcFrames.frameDiag_mem hfull ω hω3 _)

theorem map_conj_range_tE_eq_torusPow (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hωo : orderOf ω = 3) :
    ((tE K).range.map
        (TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)))).map
      (MulAut.conj (ExcFrameIso.langEltF4 hωo)⁻¹).toMonoidHom =
      TableBExc.torusPow .F4 (FiniteField.Extension K 2 2) 3 := by
  haveI : Finite (adjointGroup .F4 (FiniteField.Extension K 2 2)) :=
    generated_group_finite .F4 _
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨_, ⟨y, ⟨u, rfl⟩, rfl⟩, rfl⟩
    exact conj_tE_mem_torusPow hK hωo u
  · rw [card_torusPow_F4 hK, Subgroup.card_map_of_injective (MulAut.conj _).injective,
      Subgroup.card_map_of_injective (TableBExcTwo.adjointMap_injective _), X1F4.card_range_tE]

theorem mem_torusPow_iff_exists (hK : Nat.card K = 2) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hωo : orderOf ω = 3) {x : adjointGroup .F4 (FiniteField.Extension K 2 2)} :
    x ∈ TableBExc.torusPow .F4 (FiniteField.Extension K 2 2) 3 ↔
      ∃ y ∈ (tE K).range, x = (ExcFrameIso.langEltF4 hωo)⁻¹ *
        TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)) y *
          ExcFrameIso.langEltF4 hωo := by
  rw [← map_conj_range_tE_eq_torusPow hK hωo]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by simp [MulAut.conj_apply]⟩

theorem frameProdF4_conj_torusPow (hK : Nat.card K = 2) {ω : (FiniteField.Extension K 2 2)ˣ}
    (hωo : orderOf ω = 3) {v : adjointGroup .F4 (FiniteField.Extension K 2 2)}
    (hv : v ∈ TableBExc.torusPow .F4 (FiniteField.Extension K 2 2) 3) :
    ExcFrameIso.frameProdF4 (FiniteField.Extension K 2 2) (nSL 1) * v *
      (ExcFrameIso.frameProdF4 (FiniteField.Extension K 2 2) (nSL 1))⁻¹ = v⁻¹ := by
  set L := FiniteField.Extension K 2 2
  obtain ⟨y, hy, rfl⟩ := (mem_torusPow_iff_exists hK hωo).1 hv
  rw [tE_range] at hy
  obtain ⟨f, rfl⟩ := hy
  set G := ExcFrameIso.langEltF4 hωo
  set ι := TableBExcTwo.adjointMap .F4 (algebraMap K L)
  set nF := ExcFrameIso.frameProdF4 L (nSL 1) with hnF
  set D : (Fin 4 → Multiplicative (ZMod 3)) →* adjointGroup .F4 L :=
    (MulAut.conj G⁻¹).toMonoidHom.comp (ι.comp (tD K)) with hD
  have hDf : ∀ g, D g = G⁻¹ * ι (tD K g) * G := fun g => by
    simp [hD, MulAut.conj_apply]
  have hDgen : ∀ (i : Fin 4) (a : Multiplicative (ZMod 3)),
      D (Pi.mulSingle i a) = rho L i (HSL ω) ^ (Multiplicative.toAdd a).val := by
    intro i a
    have hL1 : tD K (Pi.mulSingle i a) = tGen K i ^ (Multiplicative.toAdd a).val := by
      rw [tD, MonoidHom.noncommPiCoprod_mulSingle, tC_apply]
    have hρ : ι (tGen K i) = G * rho L i (HSL ω) * G⁻¹ :=
      (ExcFrameIso.langEltF4_conj_rho_HSL hωo i).symm
    rw [hDf, hL1, map_pow, hρ, conj_pow]
    group
  have hc : ∀ i : Fin 4, nF * rho L i (HSL ω) * nF⁻¹ = (rho L i (HSL ω))⁻¹ := fun i => by
    rw [hnF, ExcFrameIso.frameProdF4_conj_rho, nSL_one_mul_HSL_mul_inv, map_inv]
  have key : (MulAut.conj nF).toMonoidHom.comp D = D.comp invMonoidHom := by
    refine MonoidHom.pi_ext fun i a => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      invMonoidHom_apply, map_inv, hDgen]
    rw [← conj_pow, hc, inv_pow]
  have h := congrArg (fun φ => φ f) key
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    invMonoidHom_apply, map_inv] at h
  rw [← hDf]
  exact h

theorem exists_rho_nSL_mem_monomial_F4 {L : Type} [Field L] [CharP L 2] (i : Fin 4) :
    ∃ h : ((rho L i (nSL 1) : adjointGroup .F4 L) : ModGL .F4 L) ∈ monomialSubgroup .F4 L,
      weylQuotientHom .F4 L ⟨_, h⟩ = rootReflection (orthRoot i) :=
  ((CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .F4 L
    (isRoot_orthRoot i)).2.2.2.2.1 1).2.2

theorem exists_frameProdF4_nSL_mem_monomial {L : Type} [Field L] [CharP L 2] :
    ∃ h : ((ExcFrameIso.frameProdF4 L (nSL 1) : adjointGroup .F4 L) : ModGL .F4 L) ∈
        monomialSubgroup .F4 L,
      weylQuotientHom .F4 L ⟨_, h⟩ =
        (List.ofFn fun i : Fin 4 => rootReflection (orthRoot i)).prod := by
  choose hm hw using exists_rho_nSL_mem_monomial_F4 (L := L)
  set m : Fin 4 → monomialSubgroup .F4 L := fun i => ⟨_, hm i⟩
  have hcoe : ((ExcFrameIso.frameProdF4 L (nSL 1) : adjointGroup .F4 L) : ModGL .F4 L) =
      (((List.ofFn m).prod : monomialSubgroup .F4 L) : ModGL .F4 L) := by
    rw [ExcFrameIso.frameProdF4, SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod,
      List.map_ofFn, List.map_ofFn]
    rfl
  have hmem : ((ExcFrameIso.frameProdF4 L (nSL 1) : adjointGroup .F4 L) : ModGL .F4 L) ∈
      monomialSubgroup .F4 L := hcoe ▸ ((List.ofFn m).prod).2
  refine ⟨hmem, ?_⟩
  have he : (⟨_, hmem⟩ : monomialSubgroup .F4 L) = (List.ofFn m).prod := Subtype.ext hcoe
  rw [he, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => hw i))

theorem commute_frameProdF4_nSL_nWord (hK : Nat.card K = 2) (ω : List (Fin Tag.F4.rank)) :
    ExcFrameIso.frameProdF4 (FiniteField.Extension K 2 2) (nSL 1) *
        nWord .F4 (FiniteField.Extension K 2 2) ω =
      nWord .F4 (FiniteField.Extension K 2 2) ω *
        ExcFrameIso.frameProdF4 (FiniteField.Extension K 2 2) (nSL 1) := by
  set L := FiniteField.Extension K 2 2
  set n := ExcFrameIso.frameProdF4 L (nSL 1)
  obtain ⟨hnm, hnw⟩ := exists_frameProdF4_nSL_mem_monomial (L := L)
  have hm := coe_nWord_mem_monomialSubgroup (τ := .F4) (K := L) ω
  set c := n * nWord .F4 L ω * n⁻¹ * (nWord .F4 L ω)⁻¹ with hc
  have hcm : (c : ModGL .F4 L) ∈ monomialSubgroup .F4 L :=
    mul_mem (mul_mem (mul_mem hnm hm) (inv_mem hnm)) (inv_mem hm)
  have hce : (⟨c, hcm⟩ : monomialSubgroup .F4 L) =
      ⟨_, hnm⟩ * ⟨_, hm⟩ * (⟨_, hnm⟩ : monomialSubgroup .F4 L)⁻¹ *
        (⟨_, hm⟩ : monomialSubgroup .F4 L)⁻¹ :=
    rfl
  have hc1 : c = 1 := by
    refine Subtype.ext (eq_one_of_monomial_of_frob hK hcm ?_ ?_)
    · rw [hce, map_mul, map_mul, map_mul, map_inv, map_inv, hnw, weylQuotientHom_nWord,
        commute_of_smul_eq_neg frameF4_reflections]
      group
    · have h1 := adjointMap_frob_frameProdF4_nSL (K := K)
      have h2 := adjointMap_nWord (frobHom K) (τ := .F4) ω
      have h3 : TableBExcTwo.adjointMap .F4 (frobHom K) c = c := by
        rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, h1, h2]
      exact congrArg Subtype.val h3
  have : n * nWord .F4 L ω * n⁻¹ = nWord .F4 L ω := by
    rw [← mul_inv_eq_one]
    exact hc1
  calc n * nWord .F4 L ω = (n * nWord .F4 L ω * n⁻¹) * n := by group
    _ = nWord .F4 L ω * n := by rw [this]

theorem adjointMap_frob_conj_langEltF4 (hK : Nat.card K = 2)
    {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3)
    {m : adjointGroup .F4 (FiniteField.Extension K 2 2)}
    (hm : (m : ModGL .F4 (FiniteField.Extension K 2 2)) ∈
      monomialSubgroup .F4 (FiniteField.Extension K 2 2)) :
    TableBExcTwo.adjointMap .F4 (frobHom K)
        (ExcFrameIso.langEltF4 hω * m * (ExcFrameIso.langEltF4 hω)⁻¹) =
      ExcFrameIso.langEltF4 hω * m * (ExcFrameIso.langEltF4 hω)⁻¹ := by
  set L := FiniteField.Extension K 2 2
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := .F4) (K := L)
  obtain ⟨ω', hω'⟩ := (coxeterSystem .F4).wordProd_surjective (weylQuotientHom .F4 L ⟨_, hm⟩)
  set nW := nWord .F4 L ω'
  have hnWm := coe_nWord_mem_monomialSubgroup (τ := .F4) (K := L) ω'
  set h := m * nW⁻¹ with hh
  have hhT : (h : ModGL .F4 L) ∈ torusGroup .F4 L := by
    have h1 : (⟨_, hm⟩ * (⟨_, hnWm⟩ : monomialSubgroup .F4 L)⁻¹ : monomialSubgroup .F4 L) ∈
        (weylQuotientHom .F4 L).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, weylQuotientHom_nWord, ← hω', mul_inv_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨hφh, hh3⟩ := baseChangeGL_frob_of_mem_torusGroup hK hhT
  have hhV : h ∈ TableBExc.torusPow .F4 L 3 :=
    ⟨hhT, Subtype.ext (by rw [Subgroup.coe_pow]; exact hh3)⟩
  set nF := ExcFrameIso.frameProdF4 L (nSL 1)
  have e0 : nF * h * nF⁻¹ = h⁻¹ := frameProdF4_conj_torusPow hK hω hhV
  have e1 : nF * h⁻¹ * nF⁻¹ = h := by
    have : nF * h⁻¹ * nF⁻¹ = (nF * h * nF⁻¹)⁻¹ := by group
    rw [this, e0, inv_inv]
  have e2 : nF * nW * nF⁻¹ = nW := by
    rw [commute_frameProdF4_nSL_nWord hK ω', mul_inv_cancel_right]
  have hφm : TableBExcTwo.adjointMap .F4 (frobHom K) m = h⁻¹ * nW := by
    have hm' : m = h * nW := by rw [hh, inv_mul_cancel_right]
    rw [hm', map_mul, adjointMap_nWord]
    congr 1
    exact Subtype.ext (by rw [TableBExcTwo.coe_adjointMap, Subgroup.coe_inv]; exact hφh)
  calc TableBExcTwo.adjointMap .F4 (frobHom K)
        (ExcFrameIso.langEltF4 hω * m * (ExcFrameIso.langEltF4 hω)⁻¹)
      = (ExcFrameIso.langEltF4 hω * nF) * (h⁻¹ * nW) *
          (ExcFrameIso.langEltF4 hω * nF)⁻¹ := by
        rw [map_mul, map_mul, map_inv, adjointMap_frob_langEltF4 hK hω, hφm]
    _ = ExcFrameIso.langEltF4 hω * ((nF * h⁻¹ * nF⁻¹) * (nF * nW * nF⁻¹)) *
          (ExcFrameIso.langEltF4 hω)⁻¹ := by group
    _ = ExcFrameIso.langEltF4 hω * m * (ExcFrameIso.langEltF4 hω)⁻¹ := by
        rw [e1, e2, hh, inv_mul_cancel_right]

theorem exists_adjointMap_eq_of_frob_F4
    {g : adjointGroup .F4 (FiniteField.Extension K 2 2)}
    (hg : TableBExcTwo.adjointMap .F4 (frobHom K) g = g) :
    ∃ g₀ : adjointGroup .F4 K,
      TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)) g₀ = g := by
  set φ : FiniteField.Extension K 2 2 ≃+* FiniteField.Extension K 2 2 :=
    (FiniteField.Extension.frob K 2 2).toRingEquiv
  have hσg : baseChangeGL (frobHom K) (g : ModGL .F4 _) = g := congrArg Subtype.val hg
  have h1 : (g : ModGL .F4 _) ∈ entrywiseFixedGroup .F4 φ :=
    mem_entrywiseFixedGroup.2 ⟨g.2, by
      rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self]; exact hσg⟩
  rw [entrywiseFixedGroup_eq_fixedFieldImage_of_ringChar_two (Or.inr (Or.inl rfl))
    (ringChar.eq _ 2) φ, fixedFieldImage,
    map_adjointGroup_baseChangeGL_eq_of_range_eq (fixSubfield φ).subtype
      (algebraMap K (FiniteField.Extension K 2 2)) ?_] at h1
  · obtain ⟨g₀, hg₀, hg₀g⟩ := h1
    exact ⟨⟨g₀, hg₀⟩, Subtype.ext hg₀g⟩
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (CFSG.SeitzReduction.F4Pilot.frob_eq_self_iff (w : FiniteField.Extension K 2 2)).1 w.2
    · intro hz
      exact ⟨⟨z, (CFSG.SeitzReduction.F4Pilot.frob_eq_self_iff z).2 hz⟩, rfl⟩

end Frame

end X1F4Conj

section Main


theorem x1F4FrameConj_holds : X1F4FrameConj := by
  intro K _ _ _ hK E hE hcard
  have h3 : 3 ∣ Nat.card (FiniteField.Extension K 2 2) - 1 := three_dvd_natCard_ext_sub_one hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := FiniteField.Extension K 2 2)
    (p := 3) h3
  haveI : Finite (adjointGroup .F4 (FiniteField.Extension K 2 2)) := generated_group_finite .F4 _
  haveI : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  refine X1F4Conj.exists_conj_eq_of_descent (TableBExcTwo.adjointMap_injective _)
    (X := TableBF4.weylX (FiniteField.Extension K 2 2)) (fun m hm => ?_)
    (TableBF4.not_three_dvd_index_weylX h3) (X1F4Conj.map_conj_range_tE_eq_torusPow hK hωo)
    (fun E' hE' hEX hc => ?_) hE hcard.ge
  · exact X1F4Conj.exists_adjointMap_eq_of_frob_F4
      (X1F4Conj.adjointMap_frob_conj_langEltF4 hK hωo (TableBF4.mem_weylX.mp hm).1)
  · rw [← X1F4Conj.torusPow_F4_eq]
    exact TableBF4.eq_torusPow_of_le_weylX h3 hE' hEX hc

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
