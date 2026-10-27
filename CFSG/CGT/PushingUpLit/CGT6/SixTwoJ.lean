module

public import CFSG.CGT.PushingUpLit.CGT6.SixTwoQ
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic
public import CFSG.CGT.PushingUpLit.EightOneRel
public import CFSG.Quasithin.Background.BlueprintB2Bridge
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.B2Thompson

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree CFSG.CGT.PushingUpLit.BHS
open CFSG.Quasithin CFSG.QuasithinUnique.GammaExtra
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V Y X : Subgroup G}

omit [Finite G] in
theorem isMax_iff_of_exists_le {H A₀ : Subgroup G} (hA₀H : A₀ ≤ H) (hA₀ : IsMaxElemAbelian ⊤ A₀)
    (A : Subgroup G) : IsMaxElemAbelian H A ↔ A ≤ H ∧ IsMaxElemAbelian ⊤ A := by
  constructor
  · intro hA
    refine ⟨hA.1, le_top, hA.2.1, fun B _ hB => ?_⟩
    exact (hA₀.2.2 B le_top hB).trans (hA.2.2 A₀ hA₀H hA₀.2.1)
  · rintro ⟨hAH, hA⟩
    exact ⟨hAH, hA.2.1, fun B _ hB => hA.2.2 B le_top hB⟩

omit [Finite G] in
theorem isMax_map_conj (a : G) {A : Subgroup G} (h : IsMaxElemAbelian ⊤ A) :
    IsMaxElemAbelian ⊤ (A.map (MulAut.conj a).toMonoidHom) := by
  have := isMaxElemAbelian_map_equiv (MulAut.conj a) h
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj a).surjective] at this

omit [Finite G] in
theorem isPGroup_two_of_isElemAbelian {A : Subgroup G} (h : CFSG.Open.IsElemAbelian 2 A) :
    IsPGroup 2 A := CFSG.Open.IsElemAbelian.isPGroup h

theorem commutator_le_oTwoIn_of_le_centralizer [V.Normal] {A : Subgroup G} (h : XCtx V Y X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hAC : A ≤ Subgroup.centralizer (V : Set G)) :
    ⁅A, X⁆ ≤ oTwoIn X := by
  refine le_trans ?_ h.inf_le_oTwoIn
  refine le_inf (Subgroup.le_normalizer_iff_commutator_le_right.mp hAX) ?_
  refine Subgroup.commutator_le.mpr fun a ha x hx => ?_
  have h1 : a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) := by group
  have hC : (Subgroup.centralizer (V : Set G)).Normal := inferInstance
  rw [commutatorElement_def, h1]
  exact (Subgroup.centralizer (V : Set G)).mul_mem (hAC ha)
    (hC.conj_mem _ ((Subgroup.centralizer (V : Set G)).inv_mem (hAC ha)) x)

theorem isMax_le_normalizer [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    {A : Subgroup G} (hA : IsMaxElemAbelian ⊤ A) : A ≤ Subgroup.normalizer (X : Set G) := by
  by_cases hAC : A ≤ Subgroup.centralizer (V : Set G)
  · exact hAC.trans h.hCX
  · refine hP1 A (isOffG_of_isMaxElemAbelian hV le_top ?_ hA hAC)
    rw [Subgroup.normalizer_eq_top V]

@[expose] def OffConj (V Y X : Subgroup G) : Prop :=
  ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G) →
    ¬ ⁅A, X⁆ ≤ oTwoIn X → ∃ x ∈ X, A.map (MulAut.conj x).toMonoidHom ≤
      Subgroup.normalizer (Y : Set G) ∧ ¬ ⁅A.map (MulAut.conj x).toMonoidHom, Y⁆ ≤ oTwoIn Y

omit [Finite G] in
theorem map_conj_one (A : Subgroup G) : A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hz
    exact ⟨z, hz, by simp⟩

omit [Finite G] in
theorem OffConj.of_eq {V X : Subgroup G} : OffConj V X X := fun A _ hAN hA =>
  ⟨1, X.one_mem, by rw [map_conj_one]; exact hAN, by rw [map_conj_one]; exact hA⟩

theorem caseI_X [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hXstar : ∀ K : Subgroup G, K ≤ X → (K.subgroupOf X).Normal → ¬ K ≤ oTwoIn X → K = X)
    {A : Subgroup G} (hA : IsMaxElemAbelian ⊤ A) (hAX : ¬ ⁅A, X⁆ ≤ oTwoIn X) :
    ⁅thompsonJ (⊤ : Subgroup G), X⁆ = X := by
  have hJN : thompsonJ (⊤ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) :=
    thompsonJ_le fun A' hA' => isMax_le_normalizer hV h hP1 hA'
  have hZX : ⁅thompsonJ (⊤ : Subgroup G), X⁆ ≤ X :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hJN
  have hn : (⁅thompsonJ (⊤ : Subgroup G), X⁆.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZX).mpr
      (Subgroup.normalizer_commutator_ge_right _ _)
  refine hXstar _ hZX hn fun hle => hAX ?_
  exact (Subgroup.commutator_mono (le_thompsonJ hA) le_rfl).trans hle

theorem caseI_Y [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hconj : OffConj V Y X)
    (hYstar : ∀ K : Subgroup G, K ≤ Y → (K.subgroupOf Y).Normal → ¬ K ≤ oTwoIn Y → K = Y)
    {A : Subgroup G} (hA : IsMaxElemAbelian ⊤ A) (hAX : ¬ ⁅A, X⁆ ≤ oTwoIn X) :
    ⁅thompsonJ (Subgroup.normalizer (Y : Set G)), Y⁆ = Y := by
  have hAN := isMax_le_normalizer hV h hP1 hA
  have hAC : ¬ A ≤ Subgroup.centralizer (V : Set G) := fun hAC =>
    hAX (commutator_le_oTwoIn_of_le_centralizer h hAN hAC)
  have hoff : IsOffG V A := isOffG_of_isMaxElemAbelian hV le_top
    (by rw [Subgroup.normalizer_eq_top V]) hA hAC
  obtain ⟨x, -, hxA, hxY⟩ := hconj A hoff hAN hAX
  have hA' := isMax_map_conj x hA
  have hA'M : IsMaxElemAbelian (Subgroup.normalizer (Y : Set G))
      (A.map (MulAut.conj x).toMonoidHom) :=
    (isMax_iff_of_exists_le hxA hA' _).mpr ⟨hxA, hA'⟩
  have hJN : thompsonJ (Subgroup.normalizer (Y : Set G)) ≤ Subgroup.normalizer (Y : Set G) :=
    thompsonJ_le_self _
  have hZY : ⁅thompsonJ (Subgroup.normalizer (Y : Set G)), Y⁆ ≤ Y :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hJN
  have hn : (⁅thompsonJ (Subgroup.normalizer (Y : Set G)), Y⁆.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZY).mpr
      (Subgroup.normalizer_commutator_ge_right _ _)
  refine hYstar _ hZY hn fun hle => hxY ?_
  exact (Subgroup.commutator_mono (le_thompsonJ hA'M) le_rfl).trans hle

theorem caseII_le [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hII : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X) :
    (∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → A ≤ centralizerModCore Y) ∧
      thompsonJ (Subgroup.normalizer (Y : Set G)) ≤ centralizerModCore Y := by
  have hA : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → A ≤ centralizerModCore Y := by
    intro A hA
    have hAX' : A ≤ centralizerModCore X := fun a ha =>
      ⟨isMax_le_normalizer hV h hP1 hA ha, fun x hx =>
        hII A hA (Subgroup.commutator_mem_commutator ha hx)⟩
    exact hAX'.trans h.hXY
  refine ⟨hA, ?_⟩
  obtain ⟨A₀, hA₀⟩ := Quasithin.exists_isMaxElemAbelian (⊤ : Subgroup G)
  refine thompsonJ_le fun A hAM => ?_
  have hA₀M : A₀ ≤ Subgroup.normalizer (Y : Set G) := fun g hg => (hA A₀ hA₀ hg).1
  exact hA A ((isMax_iff_of_exists_le hA₀M hA₀ A).mp hAM).2

theorem caseII_not_eq [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hII : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X)
    (hYn : ¬ Y ≤ oTwoIn Y) : ¬ Y = ⁅thompsonJ (Subgroup.normalizer (Y : Set G)), Y⁆ := by
  intro h1
  have hJ := (caseII_le hV h hP1 hII).2
  have : ⁅thompsonJ (Subgroup.normalizer (Y : Set G)), Y⁆ ≤ oTwoIn Y :=
    Subgroup.commutator_le.mpr fun j hj y hy => (hJ hj).2 y hy
  exact hYn (h1.le.trans this)

theorem jIn_eq_thompsonJ (K : Subgroup G) : jIn K = thompsonJ K :=
  CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ K

theorem exists_isMax_le_sylow [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hII : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y)) :
    ∃ A₀ : Subgroup G, A₀ ≤ R ∧ IsMaxElemAbelian ⊤ A₀ := by
  obtain ⟨A₁, hA₁⟩ := Quasithin.exists_isMaxElemAbelian (⊤ : Subgroup G)
  have hA₁C : A₁ ≤ centralizerModCore Y := (caseII_le hV h hP1 hII).1 A₁ hA₁
  obtain ⟨S, hS, hA₁S⟩ := Nine.exists_isSylowOf_ge (isPGroup_two_of_isElemAbelian hA₁.2.1) hA₁C
  obtain ⟨a, -, hRa⟩ := EightOneRel.exists_conjugate_eq_of_isSylowOf hR hS
  have hRS : R = S.map (MulAut.conj a⁻¹).toMonoidHom := by
    have := ThreeFromEight.conjugate_inv_eq_map S a⁻¹
    rw [inv_inv] at this
    rw [hRa, this]
  refine ⟨A₁.map (MulAut.conj a⁻¹).toMonoidHom, ?_, isMax_map_conj _ hA₁⟩
  rw [hRS]
  exact Subgroup.map_mono hA₁S

theorem caseII_normalizer [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hII : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y)) (hQR : pCore 2 G ≤ R) :
    X ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
  obtain ⟨A₀, hA₀R, hA₀⟩ := exists_isMax_le_sylow hV h hP1 hII hR
  have hmem := isMax_iff_of_exists_le hA₀R hA₀
  have hmap : ∀ x ∈ X, ∀ A : Subgroup G, IsMaxElemAbelian R A →
      IsMaxElemAbelian R (A.map (MulAut.conj x).toMonoidHom) := by
    intro x hx A hA
    obtain ⟨hAR, hAtop⟩ := (hmem A).mp hA
    refine (hmem _).mpr ⟨?_, isMax_map_conj x hAtop⟩
    rintro _ ⟨a, ha, rfl⟩
    have hxa : (MulAut.conj x).toMonoidHom a = ⁅x, a⁆ * a := by
      simp [commutatorElement_def]
    rw [hxa]
    refine R.mul_mem ?_ (hAR ha)
    have h1 : ⁅x, a⁆ ∈ ⁅A, X⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hx ha
    exact hQR (h.oTwoIn_le_pCore (hII A hAtop h1))
  have key : ∀ x ∈ X, (thompsonJ R).map (MulAut.conj x).toMonoidHom ≤ thompsonJ R := fun x hx =>
    Subgroup.map_le_iff_le_comap.mpr (thompsonJ_le fun A hA =>
      Subgroup.map_le_iff_le_comap.mp (le_thompsonJ (hmap x hx A hA)))
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact key x hx ⟨z, hz, rfl⟩
  · intro hz
    have := key x⁻¹ (X.inv_mem hx) ⟨_, hz, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem exists_sylow_pCore_le [V.Normal] (h : XCtx V Y X) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y))
    (h2 : Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
      (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal) :
    ∃ R' : Subgroup G, IsSylowOf 2 R' (centralizerModCore Y) ∧ pCore 2 G ≤ R' ∧
      Y ≤ Subgroup.normalizer ((jIn R' : Subgroup G) : Set G) ∧
      (Y.subgroupOf (Subgroup.normalizer ((jIn R' : Subgroup G) : Set G))).IsSubnormal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hQS⟩ := Nine.exists_isSylowOf_ge (pCore_isPGroup (p := 2) (G := G))
    h.hQY
  obtain ⟨a, haK, hSa⟩ := EightOneRel.exists_conjugate_eq_of_isSylowOf hS hR
  refine ⟨S, hS, hQS, ?_⟩
  have h2' : Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
      (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ⊓ ⊤)).IsSubnormal :=
    ⟨h2.1, (EightOneRel.isSubnormal_subgroupOf_inf_top_iff _ _).mpr h2.2⟩
  have := EightOneRel.sylowClause_conjugate (N := ⊤) (X := Y) (a := a) haK.1
    (Subgroup.mem_top a) h2'
  rw [EightOneRel.conjugate_jIn, ← hSa] at this
  exact ⟨this.1, (EightOneRel.isSubnormal_subgroupOf_inf_top_iff _ _).mp this.2⟩

theorem caseII_subnormal [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hII : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y))
    (h2 : Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
      (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal) :
    (Y.subgroupOf X).IsSubnormal := by
  obtain ⟨R', hR', hQR', hY', hs'⟩ := exists_sylow_pCore_le h hR h2
  have hXN : X ≤ Subgroup.normalizer ((jIn R' : Subgroup G) : Set G) := by
    rw [jIn_eq_thompsonJ]
    exact caseII_normalizer hV h hP1 hII hR' hQR'
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hXN hs'

omit [Finite G] in
theorem exists_normal_ne_top_of_isSubnormal {Γ : Type*} [Group Γ] {H : Subgroup Γ}
    (hH : H.IsSubnormal) (hne : H ≠ ⊤) : ∃ K : Subgroup Γ, K.Normal ∧ K ≠ ⊤ ∧ H ≤ K := by
  induction hH with
  | top => exact absurd rfl hne
  | step H K hHK hK hN ih =>
    by_cases hKtop : K = ⊤
    · subst hKtop
      have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).mp hN
      rw [top_le_iff, Subgroup.normalizer_eq_top_iff] at h1
      exact ⟨H, h1, hne, le_rfl⟩
    · obtain ⟨K', hK'n, hK'ne, hKK'⟩ := ih hKtop
      exact ⟨K', hK'n, hK'ne, hHK.trans hKK'⟩

theorem eq_of_isSubnormal [V.Normal] (h : XCtx V Y X)
    (hXstar : ∀ K : Subgroup G, K ≤ X → (K.subgroupOf X).Normal → ¬ K ≤ oTwoIn X → K = X)
    (hYn : ¬ Y ≤ oTwoIn Y) (hs : (Y.subgroupOf X).IsSubnormal) : Y = X := by
  by_contra hne
  have hne' : Y.subgroupOf X ≠ ⊤ := fun htop =>
    hne (le_antisymm h.hYX (Subgroup.subgroupOf_eq_top.mp htop))
  obtain ⟨K', hK'n, hK'ne, hYK'⟩ := exists_normal_ne_top_of_isSubnormal hs hne'
  set K : Subgroup G := K'.map X.subtype with hK
  have hKX : K ≤ X := Subgroup.map_subtype_le K'
  have hKsub : K.subgroupOf X = K' :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective K'
  have hKne : K ≠ X := fun hKX' => hK'ne (by
    rw [← hKsub, hKX']
    exact Subgroup.subgroupOf_self X)
  have hKo : K ≤ oTwoIn X := by
    by_contra hnot
    exact hKne (hXstar K hKX (by rw [hKsub]; exact hK'n) hnot)
  have hYK : Y ≤ K := by
    intro y hy
    have : (⟨y, h.hYX hy⟩ : X) ∈ K' := hYK' hy
    rw [hK]
    exact ⟨_, this, rfl⟩
  have hY2 : IsPGroup 2 Y := (ThreeFromEight.isPGroup_oTwoIn X).to_le (hYK.trans hKo)
  exact hYn (le_oTwoIn_of_isPGroup le_rfl hY2 Subgroup.le_normalizer)

theorem endgame_a [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hconj : OffConj V Y X)
    (hXstar : ∀ K : Subgroup G, K ≤ X → (K.subgroupOf X).Normal → ¬ K ≤ oTwoIn X → K = X)
    (hYstar : ∀ K : Subgroup G, K ≤ Y → (K.subgroupOf Y).Normal → ¬ K ≤ oTwoIn Y → K = Y)
    (hYn : ¬ Y ≤ oTwoIn Y) {R : Subgroup G} (hR : IsSylowOf 2 R (centralizerModCore Y))
    (h12 : Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ ∨
      (Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
        (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal)) :
    (Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ → X = ⁅jIn (⊤ : Subgroup G), X⁆) ∧
      (¬ Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ → Y = X) := by
  rw [jIn_eq_thompsonJ, jIn_eq_thompsonJ] at *
  by_cases hI : ∃ A : Subgroup G, IsMaxElemAbelian ⊤ A ∧ ¬ ⁅A, X⁆ ≤ oTwoIn X
  · obtain ⟨A, hA, hAX⟩ := hI
    refine ⟨fun _ => (caseI_X hV h hP1 hXstar hA hAX).symm, fun hn => ?_⟩
    exact absurd (caseI_Y hV h hP1 hconj hYstar hA hAX).symm hn
  · have hII : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X := fun A hA =>
      by_contra fun hn => hI ⟨A, hA, hn⟩
    have hn1 := caseII_not_eq hV h hP1 hII hYn
    refine ⟨fun h1 => absurd h1 hn1, fun _ => ?_⟩
    have h2 := h12.resolve_left hn1
    rw [← jIn_eq_thompsonJ] at h2
    exact eq_of_isSubnormal h hXstar hYn (caseII_subnormal hV h hP1 hII hR h2)

theorem endgame_b [V.Normal] (hV : CFSG.Open.IsElemAbelian 2 V) (h : XCtx V Y X)
    (hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G))
    (hII : ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → ⁅A, X⁆ ≤ oTwoIn X)
    (hYn : ¬ Y ≤ oTwoIn Y) (hns : ¬ (Y.subgroupOf X).IsSubnormal) {R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y))
    (h12 : Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ ∨
      (Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
        (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal)) :
    False := by
  have hn1 := caseII_not_eq hV h hP1 hII hYn
  rw [jIn_eq_thompsonJ] at h12
  exact hns (caseII_subnormal hV h hP1 hII hR (h12.resolve_left hn1))

omit [Finite G] in
theorem exists_isMax_not_le_of_eq (hYn : ¬ Y ≤ oTwoIn Y)
    (h1 : Y = ⁅thompsonJ (Subgroup.normalizer (Y : Set G)), Y⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian (Subgroup.normalizer (Y : Set G)) A ∧
      ¬ ⁅A, Y⁆ ≤ oTwoIn Y := by
  by_contra hall
  push Not at hall
  have hJ : thompsonJ (Subgroup.normalizer (Y : Set G)) ≤ centralizerModCore Y := by
    refine thompsonJ_le fun A hA => fun a ha => ⟨hA.1 ha, fun y hy => ?_⟩
    exact hall A hA (Subgroup.commutator_mem_commutator ha hy)
  have : ⁅thompsonJ (Subgroup.normalizer (Y : Set G)), Y⁆ ≤ oTwoIn Y :=
    Subgroup.commutator_le.mpr fun j hj y hy => (hJ hj).2 y hy
  exact hYn (h1.le.trans this)

theorem endgame_prime
    (hYstar : ∀ K : Subgroup G, K ≤ Y → (K.subgroupOf Y).Normal → ¬ K ≤ oTwoIn Y → K = Y)
    (hYn : ¬ Y ≤ oTwoIn Y)
    (hP : Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ →
      ∀ A : Subgroup G, IsMaxElemAbelian ⊤ A → A ≤ Subgroup.normalizer (Y : Set G))
    (h1 : Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆) :
    Y = ⁅jIn (⊤ : Subgroup G), Y⁆ := by
  have hP' := hP h1
  rw [jIn_eq_thompsonJ] at h1 ⊢
  obtain ⟨A', hA'M, hA'⟩ := exists_isMax_not_le_of_eq hYn h1
  obtain ⟨A₀, hA₀⟩ := Quasithin.exists_isMaxElemAbelian (⊤ : Subgroup G)
  have hA'top : IsMaxElemAbelian ⊤ A' :=
    ((isMax_iff_of_exists_le (hP' A₀ hA₀) hA₀ A').mp hA'M).2
  have hJN : thompsonJ (⊤ : Subgroup G) ≤ Subgroup.normalizer (Y : Set G) :=
    thompsonJ_le fun A hA => hP' A hA
  have hZY : ⁅thompsonJ (⊤ : Subgroup G), Y⁆ ≤ Y :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hJN
  have hn : (⁅thompsonJ (⊤ : Subgroup G), Y⁆.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZY).mpr
      (Subgroup.normalizer_commutator_ge_right _ _)
  refine (hYstar _ hZY hn fun hle => hA' ?_).symm
  exact (Subgroup.commutator_mono (le_thompsonJ hA'top) le_rfl).trans hle

end CFSG.CGT.PushingUpLit.CGT6
