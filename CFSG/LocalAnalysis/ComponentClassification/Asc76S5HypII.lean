module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Q
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Sub

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_normalIn {Γ : Type*} [Group Γ] {X Y : Subgroup Γ} (h : NormalIn X Y) :
    Y ≤ normalizer (X : Set Γ) :=
  (normal_subgroupOf_iff_le_normalizer h.1).mp h.2

omit [Finite G] in
theorem mem_normalizer_map_subtype_iff {M : Subgroup G} (X : Subgroup M) (m : M) :
    m ∈ normalizer (X : Set M) ↔
      (m : G) ∈ normalizer ((X.map M.subtype : Subgroup G) : Set G) := by
  have hX : (X.map M.subtype).subgroupOf M = X :=
    comap_map_eq_self_of_injective M.subtype_injective X
  have h := mem_normalizer_subgroupOf_iff (map_subtype_le X) m
  rwa [hX] at h

theorem twoPrimeLayerIn_eq_oddCoreIn_of_odd {Γ : Type} [Group Γ] [Finite Γ] {Q : Subgroup Γ}
    (h : Odd (Nat.card (twoPrimeLayerIn Q))) : twoPrimeLayerIn Q = oddCoreIn Q := by
  refine (twoPrimeLayerIn_eq_oddCoreIn_iff Q).mpr ?_
  set E := CFSG.layer (Q ⧸ CFSG.Assembly.oddCore Q)
  have hodd : Odd (Nat.card E) := by
    rw [card_twoPrimeLayerIn] at h
    exact h.of_dvd_nat (dvd_mul_left _ _)
  have : Group.IsSolvable E := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsPerfect E := CFSG.LocalCores.layer_isPerfect
  have hsub := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    (G := E)
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : E) = 1 := Subsingleton.elim _ _
  exact mem_bot.mpr (congrArg Subtype.val this)

theorem not_normalIn_twoPrimeLayerIn {A : Subgroup G} (hA : standardComponentIsStandard A)
    {g : G} (hg : g ∉ normalizer (A : Set G)) :
    let M := normalizer (A : Set G)
    let P := (rightConjugate (centralizer (A : Set G)) g ⊓ M).subgroupOf M
    twoPrimeLayerIn P ≠ oddCoreIn P →
      ¬ NormalIn (twoPrimeLayerIn P) (twoPrimeLayerIn (⊤ : Subgroup M)) := by
  intro M P hne hN
  have hq : Open.IsQuasisimple A := hA.1
  have hAA : ⁅A, A⁆ = A := commutator_self_of_isQuasisimple hq
  set K := centralizer (A : Set G) with hKdef
  have hK : TightlyEmbedded K := tightlyEmbedded_centralizer hA
  have hgK : g ∉ normalizer (K : Set G) := by rwa [normalizer_centralizer_eq hA]
  set L₀ := (twoPrimeLayerIn P).map M.subtype with hL₀
  set L := (twoPrimeLayerIn (⊤ : Subgroup M)).map M.subtype with hL
  have hL₀P : L₀ ≤ rightConjugate K g ⊓ M := by
    refine (map_mono (twoPrimeLayerIn_le P)).trans ?_
    rw [subgroupOf_map_subtype]
    exact inf_le_left
  have hL₀A : L₀ ≤ normalizer (A : Set G) := hL₀P.trans inf_le_right
  have hL₀L : L₀ ≤ L := map_mono hN.1
  have hLL₀ : L ≤ normalizer (L₀ : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    exact (mem_normalizer_map_subtype_iff _ l).mp (le_normalizer_of_normalIn hN hl)
  have hAL : A ≤ normalizer (L : Set G) := fun a ha =>
    (mem_normalizer_map_subtype_iff _ ⟨a, le_normalizer ha⟩).mp
      (le_normalizer_twoPrimeLayerIn ⊤ (mem_top _))
  have hcomm : ⁅L₀, A⁆ ≠ ⊥ := by
    intro hc
    have hL₀K : L₀ ≤ K := (commutator_eq_bot_iff_le_centralizer).mp hc
    have hle : L₀ ≤ K ⊓ rightConjugate K g := le_inf hL₀K (hL₀P.trans inf_le_left)
    have hodd := (hK.2 g hgK).of_dvd_nat (card_dvd_of_le hle)
    rw [hL₀, card_map_of_injective M.subtype_injective] at hodd
    exact hne (twoPrimeLayerIn_eq_oddCoreIn_of_odd hodd)
  have hAL₀ : ¬ A ≤ L₀ := by
    intro h
    have hAK : A ≤ centralizer (rightConjugate A g : Set G) := by
      rw [← AschbacherTheorem3.rightConjugate_centralizer]
      exact h.trans (hL₀P.trans inf_le_left)
    exact commutator_rightConjugate_ne_bot hA g ((commutator_eq_bot_iff_le_centralizer).mpr hAK)
  have hAinf : A ≤ normalizer ((A ⊓ L : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_inf (le_normalizer ha) (hAL ha)
  rcases le_centerOf_or_eq_of_le_normalizer hq inf_le_left hAinf with hZ | hEq
  · apply hcomm
    refine commutator_eq_bot_of_commutator_commutator_eq_bot hAA ?_
    rw [commutator_eq_bot_iff_le_centralizer]
    exact (Sec5.commutator_le_inf hL₀L hL₀A hAL).trans (hZ.trans inf_le_right)
  · have hAL' : A ≤ L := by rw [← hEq]; exact inf_le_right
    have hAN : A ≤ normalizer (L₀ : Set G) := hAL'.trans hLL₀
    have hAinf' : A ≤ normalizer ((L₀ ⊓ A : Subgroup G) : Set G) := fun a ha =>
      mem_normalizer_inf (hAN ha) (le_normalizer ha)
    rcases le_centerOf_or_eq_of_le_normalizer hq inf_le_right hAinf' with hZ' | hEq'
    · exact hcomm (commutator_eq_bot_of_inf_le_centerOf hq hL₀A hAN (hZ'.trans inf_le_right))
    · exact hAL₀ (by rw [← hEq']; exact inf_le_left)

omit [Finite G] in
theorem isMulCommutative_subgroupOf {T : Subgroup G} (M : Subgroup G) (hTc : IsMulCommutative T) :
    IsMulCommutative (T.subgroupOf M) := by
  refine ⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩
  have h := congrArg Subtype.val (hTc.is_comm.comm ⟨((x : M) : G), x.2⟩ ⟨((y : M) : G), y.2⟩)
  simpa using h

omit [Finite G] in
theorem omegaOne_subgroupOf {T : Subgroup G} (M : Subgroup G) (hTc : IsMulCommutative T) :
    omegaOne (T.subgroupOf M) = (omegaOne T).subgroupOf M := by
  ext x
  rw [mem_omegaOne_iff (isMulCommutative_subgroupOf M hTc), mem_subgroupOf, mem_subgroupOf,
    mem_omegaOne_iff hTc]
  refine and_congr_right fun _ => ?_
  rw [← Subtype.val_inj (a := x ^ 2)]
  simp

omit [Finite G] in
theorem le_normalizer_of_normal {Γ : Type*} [Group Γ] {B : Subgroup Γ} (hB : B.Normal)
    (Q : Subgroup Γ) : Q ≤ normalizer (B : Set Γ) := by
  intro q _
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => hB.conj_mem y hy q
  · intro hy
    have := hB.conj_mem _ hy q⁻¹
    simpa [mul_assoc] using this

omit [Finite G] in
theorem gammaOneOn_subgroupOf_le (A U M : Subgroup G) :
    gammaOneOn (U.subgroupOf M) (A.subgroupOf M) ≤ (gammaOneOn U A).subgroupOf M := by
  refine iSup_le fun V' => iSup_le fun hVU => iSup_le fun hV1 => ?_
  intro x hx
  rw [mem_subgroupOf]
  set V := V'.map M.subtype
  have hVU' : V ≤ U := by
    rintro _ ⟨v, hv, rfl⟩
    exact mem_subgroupOf.mp (hVU hv)
  have hV1' : V ≠ ⊥ := fun h => hV1 ((map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
  have hle : A ⊓ normalizer (V : Set G) ≤ gammaOneOn U A :=
    le_iSup_of_le V (le_iSup_of_le hVU' (le_iSup_of_le hV1' le_rfl))
  exact hle ⟨mem_subgroupOf.mp hx.1, (mem_normalizer_map_subtype_iff V' x).mp hx.2⟩

theorem omegaOne_le_sup_centralizer (h75 : Asc75Theorem4) {A T : Subgroup G}
    (hA : standardComponentIsStandard A) (hII : Asc76HypII A) {g : G}
    (hg : g ∉ normalizer (A : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)))
    (hT1 : T ≠ ⊥) (hTc : IsMulCommutative T) (hU4 : 4 ≤ Nat.card (omegaOne T)) :
    omegaOne T ≤ A ⊔ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  set M := normalizer (A : Set G) with hMdef
  set P := rightConjugate K g ⊓ M with hPdef
  have hKg : TightlyEmbedded (rightConjugate K g) :=
    tightlyEmbedded_rightConjugate (tightlyEmbedded_centralizer hA) g
  have hPeven : Even (Nat.card P) := even_iff_two_dvd.mpr
    ((even_card_of_isPGroup hT.isPGroup hT1).two_dvd.trans (card_dvd_of_le hT.le))
  have hP' : TightlyEmbedded (P.subgroupOf M) :=
    tightlyEmbedded_inf_subgroupOf_of_tightlyEmbedded hKg hPeven
  have hTM : T ≤ M := hT.le.trans inf_le_right
  have hT' : IsSylowOf 2 (T.subgroupOf M) (P.subgroupOf M) :=
    (isSylowOf_subgroupOf_iff hTM inf_le_right).mpr hT
  have hTc' : IsMulCommutative (T.subgroupOf M) := isMulCommutative_subgroupOf M hTc
  have hT1' : T.subgroupOf M ≠ ⊥ := by
    intro h
    apply hT1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hTM hx⟩ : M) ∈ T.subgroupOf M := hx
    rw [h, mem_bot] at this
    exact mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨Q', -, hUQ', hnil', hQTE'⟩ := exists_twoNilpotent_tightlyEmbedded h75 hP' hT' hTc' hT1'
    (not_normalIn_twoPrimeLayerIn hA hg)
  set A' := A.subgroupOf M with hA'def
  have hA'n : A'.Normal := Subgroup.normal_in_normalizer
  have hUeq : omegaOne (T.subgroupOf M) = (omegaOne T).subgroupOf M := omegaOne_subgroupOf M hTc
  have hUM : omegaOne T ≤ M := (omegaOne_le T).trans hTM
  have hgam : ¬ A' ≤ gammaOneOn (omegaOne (T.subgroupOf M)) A' := by
    intro hle
    have hnot := not_le_gammaOneOn hA g ((omegaOne_le T).trans (hT.le.trans inf_le_left))
      (hT.isPGroup.to_le (omegaOne_le T))
      (not_le_normalizer_rightConjugate hA hg hT.isPGroup hT1 hT.le)
    apply hnot
    intro a ha
    have h1 : (⟨a, le_normalizer ha⟩ : M) ∈ gammaOneOn (omegaOne (T.subgroupOf M)) A' := hle ha
    rw [hUeq] at h1
    exact mem_subgroupOf.mp (gammaOneOn_subgroupOf_le A (omegaOne T) M h1)
  have hUe : IsElemAbelian 2 (omegaOne (T.subgroupOf M)) :=
    ⟨isMulCommutative_of_le (omegaOne_le _) hTc', fun x hx =>
      ((mem_omegaOne_iff hTc').mp hx).2⟩
  have hU4' : 4 ≤ Nat.card (omegaOne (T.subgroupOf M)) := by
    rw [hUeq, card_subgroupOf hUM]
    exact hU4
  have hTE'' : TightlyEmbedded (Q'.subgroupOf (Q' ⊔ A')) :=
    tightlyEmbedded_subgroupOf hQTE' le_sup_left
  have hII' := hII.2 M A' Q' (omegaOne (T.subgroupOf M)) ⟨subgroupOfEquivOfLe le_normalizer⟩
    (le_normalizer_of_normal hA'n Q') hUQ' hgam hUe hU4' hnil' hTE''
  intro u hu
  have hu' : (⟨u, hUM hu⟩ : M) ∈ omegaOne (T.subgroupOf M) := by
    rw [hUeq]
    exact hu
  have h := hII' hu'
  have hmap : (A' ⊔ centralizer (A' : Set M)).map M.subtype ≤ A ⊔ K := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rw [hA'def, subgroupOf_map_subtype]
      exact inf_le_left
    · rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      intro a ha
      have h1 := mem_centralizer_iff.mp hx ⟨a, le_normalizer ha⟩ ha
      exact congrArg Subtype.val h1
  exact hmap ⟨_, h, rfl⟩

end CFSG.ComponentClassification.Asc76.Sec5
