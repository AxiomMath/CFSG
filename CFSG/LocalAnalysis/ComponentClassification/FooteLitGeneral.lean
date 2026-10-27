module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitPointed
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical
public import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankSmallSources
public import CFSG.LieType.CurtisTits.Conclusion
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def FooteCoreAt (H : Type) [Group H] : Prop :=
  ∀ a b : H, orderOf a = 2 → orderOf b = 2 → a * b = b * a →
    ∀ Y : Subgroup H, Y ≤ centralizer ({b} : Set H) →
    IsPComponent 2 (Y.subgroupOf (centralizer ({b} : Set H))) →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) ∨
    ⁅⁅oddCoreOfCentralizer a ⊓ centralizer ({b} : Set H),
        oddCoreOfCentralizer a ⊓ centralizer ({b} : Set H)⁆, Y⁆ ≤ oddCoreOfCentralizer b

@[expose] def FooteCoreHypothesis (G : Type) [Group G] : Prop :=
  ∀ H : Subgroup G, FooteCoreAt ↥H

variable {G : Type} [Group G]

@[expose] def FooteFamilyType (L : Subgroup G) : Prop :=
  Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7)) ∨
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
      Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p f

@[expose] def FooteConclusion (t : G) (L A : Subgroup G) : Prop :=
  Nonempty (A ⧸ pPrimeCore 2 A ≃* L ⧸ pPrimeCore 2 L) ∨
  (∃ K : Subgroup G, IsPComponent 2 K ∧ conjugate K t ≠ K ∧ A = K ⊔ conjugate K t) ∨
  ((Nonempty (A ⧸ pPrimeCore 2 A ≃* alternatingGroup (Fin 9)) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5))) ∨
    (Nonempty (A ⧸ pPrimeCore 2 A ≃* alternatingGroup (Fin 10)) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6))) ∨
    (Nonempty (A ⧸ pPrimeCore 2 A ≃* alternatingGroup (Fin 11)) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))) ∨
    (Nonempty (A ⧸ pPrimeCore 2 A ≃* Blueprint.NativeSporadic.J2) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5)))) ∨
  (IsSimpleGroup (A ⧸ pPrimeCore 2 A) ∧ IsEmpty (A ⧸ pPrimeCore 2 A ≃* L ⧸ pPrimeCore 2 L) ∧
    ((∃ P : Sylow 2 ↥((A ⊔ zpowers t) ⊓ coreActionKernel L),
        (P : Subgroup _) = (zpowers t).subgroupOf ((A ⊔ zpowers t) ⊓ coreActionKernel L)) ∨
      CFSG.pRank 2 ↥(A ⊓ coreActionKernel L) = 1)) ∨
  (IsSimpleGroup (A ⧸ pPrimeCore 2 A) ∧ Blueprint.OddLieType (A ⧸ pPrimeCore 2 A))

@[expose] def FooteGeneralStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Assembly.KProper Blueprint.Catalog G →
    FooteCoreHypothesis G →
    ∀ (t : G) (L : Subgroup G), IsTwoComponentAt t L → FootePointedMaximal t L →
      FooteFamilyType L → 2 ≤ CFSG.pRank 2 ↥L → FooteConclusion t L (conjClosure L (pLayer G 2))

theorem statedClassicalModel_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (h : Blueprint.LieModel X .PSL 2 p f) :
    Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem isSimpleGroup_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (hL : Blueprint.LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL

theorem isSimpleGroup_of_footeType {X : Type} [Group X] {L : Subgroup X} (h : FooteType L) :
    IsSimpleGroup (L ⧸ pPrimeCore 2 L) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨p, f, -, -, -, -, hL⟩
  · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
    exact e.isSimpleGroup
  · exact isSimpleGroup_of_lieModel_psl_two hL

theorem center_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases (center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hS
    exact hab (mem_center_iff.mp (h ▸ mem_top b) a)

theorem fusionZStar_eq_pPrimeCore {X : Type*} [Group X] (L : Subgroup X)
    [IsSimpleGroup (L ⧸ pPrimeCore 2 L)] (hna : ∃ a b : L ⧸ pPrimeCore 2 L, a * b ≠ b * a) :
    Open.fusionZStar L = pPrimeCore 2 L := by
  have hO := UnbalancingLocal.fusionOddCore_eq_pPrimeCore L
  have hZ : center (L ⧸ pPrimeCore 2 L) = ⊥ := center_eq_bot_of_isSimpleGroup hna
  let e : L ⧸ Open.fusionOddCore L ≃* L ⧸ pPrimeCore 2 L := QuotientGroup.quotientMulEquivOfEq hO
  ext g
  constructor
  · intro hg
    have h1 : (QuotientGroup.mk g : L ⧸ Open.fusionOddCore L) ∈ center _ := hg
    have h2 : e (QuotientGroup.mk g) ∈ center (L ⧸ pPrimeCore 2 L) := by
      refine mem_center_iff.mpr fun y => ?_
      obtain ⟨y', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp h1 y']
    rw [hZ, mem_bot] at h2
    have h3 : (QuotientGroup.mk g : L ⧸ pPrimeCore 2 L) = 1 := h2
    exact (QuotientGroup.eq_one_iff g).mp h3
  · intro hg
    have h1 : g ∈ Open.fusionOddCore L := hO ▸ hg
    show (QuotientGroup.mk g : L ⧸ Open.fusionOddCore L) ∈ center _
    rw [(QuotientGroup.eq_one_iff g).mpr h1]
    exact one_mem _

theorem footeFamilyType_of_footeType {X : Type} [Group X] {L : Subgroup X} (h : FooteType L)
    (hna : ∃ a b : L ⧸ pPrimeCore 2 L, a * b ≠ b * a) : FooteFamilyType L := by
  have : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := isSimpleGroup_of_footeType h
  let e : L ⧸ Open.fusionZStar L ≃* L ⧸ pPrimeCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_pPrimeCore L hna)
  unfold FooteFamilyType
  rcases h with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, h5, hL⟩
  · exact Or.inl ⟨e.trans e7⟩
  · exact Or.inr ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv e.symm hL⟩

theorem two_le_pRank_of_footeType {X : Type} [Group X] {L : Subgroup X} [Finite L]
    (hLq : IsQuasisimple (L ⧸ pPrimeCore 2 L)) (h : FooteType L) : 2 ≤ CFSG.pRank 2 ↥L := by
  let e : L ⧸ CFSG.oddCore L ≃* L ⧸ pPrimeCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two L)
  have hA : IsQuasisimple (L ⧸ CFSG.oddCore L) := LocalCores.isQuasisimple_of_mulEquiv e.symm hLq
  rcases h with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inr (Or.inl ⟨e.trans e7⟩))
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf,
        LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm
          (statedClassicalModel_of_lieModel_psl_two hL)⟩)

theorem exists_mul_ne_mul_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

theorem pRank_two_le_one_of_card_sylow_le {H : Type*} [Group H] [Finite H] (P : Sylow 2 H)
    (hP : Nat.card P ≤ 2) : CFSG.pRank 2 H ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have hpA : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨Q, hAQ⟩ := hpA.exists_le_sylow
  have hQ : Nat.card Q = Nat.card P := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h1 : 2 ^ r ≤ 2 ^ 1 := by
    rw [← hcard, pow_one]
    exact (Subgroup.card_le_of_le hAQ).trans (hQ.le.trans hP)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem pPrimeCore_two_eq_bot_of_isSimpleGroup {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] {x : S} (hx : orderOf x = 2) : pPrimeCore 2 S = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 S) with h | h
  · exact h
  · exfalso
    have hc := pPrimeCore_coprime_card (p := 2) (G := S)
    rw [h, Subgroup.card_top] at hc
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hc (hx ▸ orderOf_dvd_natCard x)

theorem pLayer_two_eq_top_of_isSimpleGroup {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {x : S} (hx : orderOf x = 2) : pLayer S 2 = ⊤ := by
  have hS := (LocalCores.isQuasisimple_of_isSimpleGroup hna).1
  have htop : IsComponent (⊤ : Subgroup S) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hS, Subgroup.IsSubnormal.top⟩
  have hsolv : Group.IsSolvable (pPrimeCore 2 S) := by
    rw [pPrimeCore_two_eq_bot_of_isSimpleGroup hx]
    infer_instance
  exact eq_top_iff.2 (le_sSup
    ((LocalAnalysis.ComponentInitial.solvable_prime_core_ordinary_components 2 Nat.prime_two
      hsolv).1 ⊤ htop))

theorem conjClosure_top_eq_normalClosure (Y : Subgroup G) :
    conjClosure Y ⊤ = normalClosure (Y : Set G) := by
  unfold conjClosure normalClosure
  congr 1
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, mem_top, exists_const,
    Group.mem_conjugatesOfSet_iff, isConj_iff]
  constructor
  · rintro ⟨e, hx⟩
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact ⟨y, hy, e⁻¹, by simp⟩
  · rintro ⟨y, hy, c, rfl⟩
    exact ⟨c⁻¹, mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩⟩

theorem conjClosure_top_eq_top [IsSimpleGroup G] {Y : Subgroup G} (hY : Y ≠ ⊥) :
    conjClosure Y ⊤ = ⊤ := by
  rw [conjClosure_top_eq_normalClosure]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure (Y : Set G)) with h | h
  · have hYle : Y ≤ normalClosure (Y : Set G) := fun y hy => subset_normalClosure hy
    exact absurd (eq_bot_iff.2 (hYle.trans h.le)) hY
  · exact h

theorem conjugate_bot (g : G) : conjugate (⊥ : Subgroup G) g = ⊥ :=
  Subgroup.map_bot _

theorem conjugate_top (g : G) : conjugate (⊤ : Subgroup G) g = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective

theorem nonempty_quotient_top_equiv {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {x : X}
    (hx : orderOf x = 2) :
    Nonempty ((⊤ : Subgroup X) ⧸ pPrimeCore 2 ↥(⊤ : Subgroup X) ≃* X) := by
  have : IsSimpleGroup ↥(⊤ : Subgroup X) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).isSimpleGroup
  have hx' : orderOf (⟨x, mem_top x⟩ : ↥(⊤ : Subgroup X)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hx
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (pPrimeCore_two_eq_bot_of_isSimpleGroup hx')).trans
    QuotientGroup.quotientBot).trans Subgroup.topEquiv⟩

theorem footeMaximalInput_of_general (hgen : FooteGeneralStatement)
    (hcore : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Assembly.KProper Blueprint.Catalog X → FooteCoreHypothesis X) :
    FooteMaximalInput := by
  intro X _ _ _ hna hK x hx L hLx hL hmax htype
  have hLq := isQuasisimple_quotient_of_isPComponent hLx hL
  have hLna := exists_mul_ne_mul_of_isQuasisimple hLq
  have hconc := hgen X hK (hcore X hna hK) x L ⟨hx, hLx, hL⟩ (hmax.pointed ⟨hx, hLx, hL⟩)
    (footeFamilyType_of_footeType htype hLna) (two_le_pRank_of_footeType hLq htype)
  have hLne : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨a, b, hab⟩ := hLna
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    rw [show a' = 1 from Subtype.ext ((Subgroup.mem_bot).1 a'.2),
      show b' = 1 from Subtype.ext ((Subgroup.mem_bot).1 b'.2)]
  have hA : conjClosure L (pLayer X 2) = ⊤ := by
    rw [pLayer_two_eq_top_of_isSimpleGroup hna hx, conjClosure_top_eq_top hLne]
  generalize conjClosure L (pLayer X 2) = A at hconc hA
  subst hA
  obtain ⟨eX⟩ := nonempty_quotient_top_equiv hx
  have hXq := LocalCores.isQuasisimple_of_isSimpleGroup hna
  rcases hconc with ⟨⟨e⟩⟩ | ⟨K, hK, hne, -⟩ | h3 | ⟨-, -, hP | hrank⟩ | ⟨-, hodd⟩
  ·
    exfalso
    have hcard : Nat.card X ≤ Nat.card (centralizer ({x} : Set X)) := by
      calc Nat.card X = Nat.card (L ⧸ pPrimeCore 2 L) := Nat.card_congr (eX.symm.trans e).toEquiv
        _ ≤ Nat.card L := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
        _ ≤ Nat.card (centralizer ({x} : Set X)) := Subgroup.card_le_of_le hLx
    have hxZ : x ∈ center X := by
      refine mem_center_iff.mpr fun g => ?_
      have hg : g ∈ centralizer ({x} : Set X) := by
        rw [Subgroup.eq_top_of_le_card _ hcard]; exact mem_top g
      exact mem_centralizer_singleton_iff.mp hg
    rw [hXq.2, mem_bot] at hxZ
    rw [hxZ, orderOf_one] at hx
    exact absurd hx (by norm_num)
  ·
    exfalso
    obtain ⟨-, -, hsub, -, -⟩ := hK
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hXq.1 hsub with h | h
    · exact hne (by rw [h, conjugate_top])
    · rw [hXq.2, le_bot_iff] at h
      exact hne (by rw [h, conjugate_bot])
  ·
    right; right
    rcases h3 with ⟨⟨e⟩, h⟩ | ⟨⟨e⟩, h⟩ | ⟨⟨e⟩, h⟩ | ⟨⟨e⟩, h⟩
    · exact Or.inl ⟨⟨eX.symm.trans e⟩, h⟩
    · exact Or.inr (Or.inl ⟨⟨eX.symm.trans e⟩, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨eX.symm.trans e⟩, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨eX.symm.trans e⟩, h⟩))
  ·
    right; left
    obtain ⟨P, hPx⟩ := hP
    have hxD : x ∈ (⊤ ⊔ zpowers x) ⊓ coreActionKernel L :=
      ⟨mem_sup_left (mem_top x), mem_coreActionKernel_of_le_centralizer hLx⟩
    have hPc : Nat.card P ≤ 2 := by
      rw [hPx, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hxD)).toEquiv,
        Nat.card_zpowers, hx]
    have hle := pRank_two_le_one_of_card_sylow_le P hPc
    rw [top_sup_eq, top_inf_eq] at hle
    exact le_antisymm hle (one_le_pRank_coreActionKernel hx hLx)
  ·
    right; left
    rwa [top_inf_eq] at hrank
  ·
    left
    exact (ClassicalInvolution.oddLieType_congr eX).1 hodd

end CFSG.ComponentClassification.FooteLit
