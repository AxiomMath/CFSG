module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentClauses
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SylowIntersectionControl.GomiParabolicSwapConj
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer
import CFSG.Quasithin.Background.C124Perf

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ABGLocalTools

private theorem centralizer_bot_subgroup {G : Type} [Group G] :
    Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset]
  intro x hx
  have hx' : x = 1 := by simpa using hx
  rw [hx']
  exact mem_center_iff.mpr fun y => by simp

private theorem subgroupOf_inf_eq {G : Type} [Group G] {H K N : Subgroup G} :
    (H ⊓ K).subgroupOf N = H.subgroupOf N ⊓ K.subgroupOf N :=
  Subgroup.comap_inf H K N.subtype

private noncomputable def gomiChevQuotientCenterEquiv {G : Type} [Group G]
    {A Γ : Subgroup G} (hAΓ : A ≤ Γ) :
    ↥(A.subgroupOf Γ) ⧸ center ↥(A.subgroupOf Γ) ≃* ↥A ⧸ center ↥A :=
  QuotientGroup.congr (Subgroup.center ↥(A.subgroupOf Γ)) (Subgroup.center ↥A)
    (Subgroup.subgroupOfEquivOfLe hAΓ) (Subgroup.map_center_eq _)

private theorem not_gomiException_subgroupOf {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hAΓ : A ≤ Γ)
    (hexc : ¬ (IsGomiL2 (↥A ⧸ center ↥A) ∨ IsGomiU3 (↥A ⧸ center ↥A) ∨
      IsGomiSz (↥A ⧸ center ↥A))) :
    ¬ (IsGomiL2 (↥(A.subgroupOf Γ) ⧸ center ↥(A.subgroupOf Γ)) ∨
      IsGomiU3 (↥(A.subgroupOf Γ) ⧸ center ↥(A.subgroupOf Γ)) ∨
      IsGomiSz (↥(A.subgroupOf Γ) ⧸ center ↥(A.subgroupOf Γ))) := by
  intro h
  apply hexc
  have e := gomiChevQuotientCenterEquiv hAΓ
  rcases h with h | h | h
  · exact Or.inl (h.of_mulEquiv e)
  · exact Or.inr (Or.inl (h.of_mulEquiv e))
  · exact Or.inr (Or.inr (h.of_mulEquiv e))

private theorem pCoreOf_subgroupOf_eq_bot {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hAΓ : A ≤ Γ) (hpc : CFSG.pCore 2 ↥A = ⊥) :
    pCoreOf 2 (A.subgroupOf Γ) = ⊥ := by
  have e := Subgroup.subgroupOfEquivOfLe hAΓ
  have h1 : CFSG.pCore 2 ↥(A.subgroupOf Γ) = ⊥ := by
    rw [← CFSG.pCore_map_iso 2 e.symm, hpc, Subgroup.map_bot]
  simp only [pCoreOf, h1, Subgroup.map_bot]

private theorem exists_sylow_not_swap_subgroupOf {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G))
    (hswap : (IsGomiL3 (↥A ⧸ center ↥A) ∨ IsGomiSp4 (↥A ⧸ center ↥A)) →
      ∃ T : Subgroup G, IsSylowTwoOf T (normalizer (A : Set G)) ∧ ¬ IsGomiParabolicSwap T A)
    (e : ↥(A.subgroupOf Γ) ⧸ center ↥(A.subgroupOf Γ) ≃* ↥A ⧸ center ↥A) :
    (IsGomiL3 (↥(A.subgroupOf Γ) ⧸ center ↥(A.subgroupOf Γ)) ∨
      IsGomiSp4 (↥(A.subgroupOf Γ) ⧸ center ↥(A.subgroupOf Γ))) →
      ∃ T : Sylow 2 ↥Γ, ¬ IsGomiParabolicSwap (T : Subgroup ↥Γ) (A.subgroupOf Γ) := by
  subst hΓ
  intro h
  have h' : IsGomiL3 (↥A ⧸ center ↥A) ∨ IsGomiSp4 (↥A ⧸ center ↥A) :=
    h.imp (fun h3 => h3.of_mulEquiv e) (fun h4 => h4.of_mulEquiv e)
  obtain ⟨T, hT, hTnot⟩ := hswap h'
  have hTle : T ≤ normalizer (A : Set G) := hT.1
  have hTpg : IsPGroup 2 (T.subgroupOf (normalizer (A : Set G))) := hT.2.1.comap_subtype
  refine ⟨hTpg.toSylow hT.2.2, fun hswap' => hTnot ?_⟩
  refine IsGomiParabolicSwap.of_subgroupOf hTle le_normalizer ?_
  simpa only [IsPGroup.toSylow_coe] using hswap'

private theorem isPIsolatedOver_subgroupOf_normalizer {G : Type} [Group G] [Finite G]
    {A I Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G))
    (hIA : I ≤ normalizer (A : Set G))
    (hiso : IsPIsolatedOver 2 (normalizer (I : Set G) ⊓ (A ⊔ I)) I) :
    IsPIsolatedOver 2
      (normalizer (I.subgroupOf Γ : Set ↥Γ) ⊓ (A ⊔ I).subgroupOf Γ)
      (I.subgroupOf Γ) := by
  subst hΓ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (isPIsolatedOver_subgroupOf_iff (H := I)
    (K := normalizer (I : Set G) ⊓ (A ⊔ I)) (K' := normalizer (A : Set G))
    hIA (inf_le_right.trans (sup_le le_normalizer hIA))).mpr hiso
  rw [subgroupOf_inf_eq, Subgroup.subgroupOf_normalizer_eq hIA] at h1
  exact h1

private theorem gomiChevCore_bot_case (hIso : GomiChevIsolated) {G : Type} [Group G] [Finite G]
    {A I : Subgroup G} (hA : IsGomiChevTwo ↥A)
    (hexc : ¬ (IsGomiL2 (↥A ⧸ center ↥A) ∨ IsGomiU3 (↥A ⧸ center ↥A) ∨
      IsGomiSz (↥A ⧸ center ↥A)))
    (_hI : IsPGroup 2 I)
    (hiso : IsPIsolatedOver 2 (normalizer (I : Set G) ⊓ (A ⊔ I)) I)
    (hIbot : I = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : IsPIsolatedOver 2 (A ⊓ centralizer ((⊥ : Subgroup G) : Set G)) ⊥ := by
    have h1 := hiso
    rw [hIbot] at h1
    rw [Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))] at h1
    rw [centralizer_bot_subgroup]
    simpa only [top_inf_eq, sup_bot_eq, inf_top_eq] using h1
  rcases hIso G A ⊥ hA (by simp [IsPGroup]) (by simp) hbot with h | ⟨-, hforall⟩
  · exact hexc h
  · obtain ⟨U, hU⟩ := exists_isSylowOf 2 A
    obtain ⟨a, ha, P, -, -, hnotin⟩ := hforall U hU bot_le
    rw [mem_bot] at ha
    exact hnotin (by rw [ha]; exact one_mem _)

private theorem core_data_of_gomiChevCore {G : Type} [Group G] [Finite G]
    (hCore : GomiChevCore) {A I Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G))
    (hA : IsGomiChevTwo ↥A)
    (hexc : ¬ (IsGomiL2 (↥A ⧸ center ↥A) ∨ IsGomiU3 (↥A ⧸ center ↥A) ∨
      IsGomiSz (↥A ⧸ center ↥A)))
    (hswap : (IsGomiL3 (↥A ⧸ center ↥A) ∨ IsGomiSp4 (↥A ⧸ center ↥A)) →
      ∃ T : Subgroup G, IsSylowTwoOf T (normalizer (A : Set G)) ∧ ¬ IsGomiParabolicSwap T A)
    (hIA : I ≤ normalizer (A : Set G)) (hI : IsPGroup 2 I)
    (hiso : IsPIsolatedOver 2 (normalizer (I : Set G) ⊓ (A ⊔ I)) I)
    (hIbot : I ≠ ⊥) :
    ∃ Y' : Subgroup ↥Γ, Y' ≠ ⊤ ∧ Odd Y'.index ∧
      (∃ K' : Subgroup ↥Γ, I.subgroupOf Γ ≤ K' ∧
        K' ≤ normalizer (I.subgroupOf Γ : Set ↥Γ) ⊓ (A ⊔ I).subgroupOf Γ ∧
        (K'.subgroupOf
          (normalizer (I.subgroupOf Γ : Set ↥Γ) ⊓ (A ⊔ I).subgroupOf Γ)).IsSubnormal ∧
        2 ∣ (I.subgroupOf Γ).relIndex K' ∧ K' ≤ Y') ∧
      (A.subgroupOf Γ) ⊓ normalizer ((Y' ⊓ A.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) =
        Y' ⊓ A.subgroupOf Γ ∧
      twoResidual ((Y' ⊓ A.subgroupOf Γ) ⊓
        centralizer (pCoreOf 2 (Y' ⊓ A.subgroupOf Γ) : Set ↥Γ)) ≤
        (A.subgroupOf Γ) ⊓ centralizer ((A.subgroupOf Γ) : Set ↥Γ) := by
  subst hΓ
  have hL'X' : A.subgroupOf (normalizer (A : Set G)) ≤
      (A ⊔ I).subgroupOf (normalizer (A : Set G)) :=
    Subgroup.subgroupOf_mono _ le_sup_left
  have hH'X' : I.subgroupOf (normalizer (A : Set G)) ≤
      (A ⊔ I).subgroupOf (normalizer (A : Set G)) :=
    Subgroup.subgroupOf_mono _ le_sup_right
  have hH'pg : IsPGroup 2 (I.subgroupOf (normalizer (A : Set G))) := hI.comap_subtype
  have hH'ne : I.subgroupOf (normalizer (A : Set G)) ≠ ⊥ := by
    intro h
    exact hIbot (by
      have h2 := congrArg (Subgroup.map (normalizer (A : Set G)).subtype) h
      rwa [Subgroup.map_subgroupOf_eq_of_le hIA, Subgroup.map_bot] at h2)
  have hH'iso := isPIsolatedOver_subgroupOf_normalizer rfl hIA hiso
  refine hCore ↥(normalizer (A : Set G))
    (A.subgroupOf (normalizer (A : Set G)))
    ((A ⊔ I).subgroupOf (normalizer (A : Set G)))
    (I.subgroupOf (normalizer (A : Set G))) ?_ ?_ ?_ ?_ hL'X' hH'ne hH'pg hH'X' hH'iso
  · infer_instance
  · exact hA.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_normalizer).symm
  · exact not_gomiException_subgroupOf le_normalizer hexc
  · exact exists_sylow_not_swap_subgroupOf rfl hswap
      (gomiChevQuotientCenterEquiv le_normalizer)

private theorem le_normalizer_inf_subgroupOf {G : Type} [Group G]
    {A Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G)) {Y : Subgroup ↥Γ}
    [(A.subgroupOf Γ).Normal] :
    Y ≤ normalizer (Y ⊓ A.subgroupOf Γ : Subgroup ↥Γ) := by
  subst hΓ
  exact (le_inf le_normalizer Subgroup.le_normalizer_of_normal).trans
    (Subgroup.inf_normalizer_le_normalizer_inf (H := Y) (K := A.subgroupOf _))

private theorem core_map_inf_le_A {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G)) (Y : Subgroup ↥Γ) :
    (Y ⊓ A.subgroupOf Γ).map Γ.subtype ≤ A := by
  subst hΓ
  exact (Subgroup.map_mono inf_le_right).trans_eq
    (Subgroup.map_subgroupOf_eq_of_le le_normalizer)

private theorem core_map_inf_ne_A {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G)) (hA : IsGomiChevTwo ↥A)
    {Y : Subgroup ↥Γ}
    (hNY : (A.subgroupOf Γ) ⊓ normalizer ((Y ⊓ A.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) =
      Y ⊓ A.subgroupOf Γ)
    (hres : twoResidual ((Y ⊓ A.subgroupOf Γ) ⊓
        centralizer (pCoreOf 2 (Y ⊓ A.subgroupOf Γ) : Set ↥Γ)) ≤
      (A.subgroupOf Γ) ⊓ centralizer ((A.subgroupOf Γ) : Set ↥Γ)) :
    (Y ⊓ A.subgroupOf Γ).map Γ.subtype ≠ A := by
  subst hΓ
  intro hQ
  have hL'le : A.subgroupOf (normalizer (A : Set G)) ≤ Y := by
    have h1 : (Y ⊓ A.subgroupOf (normalizer (A : Set G))).map
          (normalizer (A : Set G)).subtype =
        (A.subgroupOf (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype := by
      rw [hQ, Subgroup.map_subgroupOf_eq_of_le le_normalizer]
    exact inf_eq_right.mp
      (Subgroup.map_injective (normalizer (A : Set G)).subtype_injective h1)
  have hpCore : pCoreOf 2 (A.subgroupOf (normalizer (A : Set G))) = ⊥ :=
    pCoreOf_subgroupOf_eq_bot le_normalizer hA.2.1
  have hres' : twoResidual (A.subgroupOf (normalizer (A : Set G))) ≤
      centralizer ((A.subgroupOf (normalizer (A : Set G))) :
        Set ↥(normalizer (A : Set G))) := by
    have h := hres
    rw [inf_eq_right.mpr hL'le, hpCore, centralizer_bot_subgroup, inf_top_eq] at h
    exact h.trans inf_le_right
  have hperf : twoResidual (A.subgroupOf (normalizer (A : Set G))) =
      A.subgroupOf (normalizer (A : Set G)) :=
    CFSG.Quasithin.C124.twoResidual_eq_self_of_perfect'
      (Subgroup.isPerfect_iff.mp (CFSG.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe le_normalizer) hA.1).1)
  have hcomm : A.subgroupOf (normalizer (A : Set G)) ≤
      centralizer ((A.subgroupOf (normalizer (A : Set G))) :
        Set ↥(normalizer (A : Set G))) := hperf.ge.trans hres'
  have hcommut : ∀ x y : ↥(A.subgroupOf (normalizer (A : Set G))), x * y = y * x := by
    intro x y
    exact Subtype.ext (mem_centralizer_iff.mp (hcomm x.2) (y : ↥(normalizer (A : Set G)))
      y.2).symm
  have : Subsingleton (↥(A.subgroupOf (normalizer (A : Set G))) ⧸
      center ↥(A.subgroupOf (normalizer (A : Set G)))) := by
    rw [QuotientGroup.subsingleton_iff]
    exact eq_top_iff.mpr fun x _ => mem_center_iff.mpr fun y => (hcommut x y).symm
  obtain ⟨a, b, hab⟩ := (CFSG.IsQuasisimple.of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe le_normalizer) hA.1).2.2
  exact hab (Subsingleton.elim _ _)

private theorem core_inf_normalizer_le {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G)) (Y : Subgroup ↥Γ)
    (hNY : (A.subgroupOf Γ) ⊓ normalizer ((Y ⊓ A.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) =
      Y ⊓ A.subgroupOf Γ) :
    A ⊓ normalizer (((Y ⊓ A.subgroupOf Γ).map Γ.subtype : Subgroup G) : Set G) ≤
      (Y ⊓ A.subgroupOf Γ).map Γ.subtype := by
  subst hΓ
  rintro a ⟨haA, haN⟩
  set a' : ↥(normalizer (A : Set G)) := ⟨a, le_normalizer haA⟩ with ha'def
  have hmem : a' ∈ (A.subgroupOf (normalizer (A : Set G))) ⊓
      normalizer ((Y ⊓ A.subgroupOf (normalizer (A : Set G)) : Subgroup _) : Set _) := by
    refine ⟨mem_subgroupOf.mpr haA, Subgroup.mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩⟩
    · intro hx
      have hxQ : (x : G) ∈ (Y ⊓ A.subgroupOf (normalizer (A : Set G))).map
          (normalizer (A : Set G)).subtype := ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hzG⟩ := (Subgroup.mem_normalizer_iff.mp haN (x : G)).mp hxQ
      have heq : a' * x * a'⁻¹ = z := Subtype.ext (by simpa [ha'def] using hzG.symm)
      rw [heq]
      exact hz
    · intro hx
      have hxQ : (a' * x * a'⁻¹ : G) ∈ (Y ⊓ A.subgroupOf (normalizer (A : Set G))).map
          (normalizer (A : Set G)).subtype := ⟨a' * x * a'⁻¹, hx, rfl⟩
      have hxQ' : (x : G) ∈ (Y ⊓ A.subgroupOf (normalizer (A : Set G))).map
          (normalizer (A : Set G)).subtype := by
        have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem haN) (a' * x * a'⁻¹ : G)).mp hxQ
        simpa [ha'def, mul_assoc] using h2
      obtain ⟨z, hz, hzG⟩ := hxQ'
      have hzx : z = x := Subtype.ext hzG
      rw [← hzx]
      exact hz
  rw [hNY] at hmem
  exact ⟨a', hmem, rfl⟩

private theorem exists_sylow_le_normalizer_map {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G))
    {Y : Subgroup ↥Γ} (hYodd : Odd Y.index) [(A.subgroupOf Γ).Normal] :
    ∃ T : Subgroup G, IsSylowTwoOf T Γ ∧
      T ≤ normalizer (((Y ⊓ A.subgroupOf Γ).map Γ.subtype : Subgroup G) : Set G) := by
  subst hΓ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T', hT'⟩ := exists_isSylowOf 2 Y
  have hT'iff := isSylowOf_iff.mp hT'
  have hrel : Odd (T'.relIndex Y) :=
    Nat.not_even_iff_odd.mp fun he => hT'iff.2.2 (even_iff_two_dvd.mp he)
  have hT'odd : Odd T'.index := by
    rw [← Subgroup.relIndex_mul_index (IsSylowOf.le hT')]
    exact hrel.mul hYodd
  have hYnorm : Y ≤ normalizer (Y ⊓ A.subgroupOf (normalizer (A : Set G)) : Subgroup _) :=
    le_normalizer_inf_subgroupOf rfl
  refine ⟨T'.map (normalizer (A : Set G)).subtype, ?_, ?_⟩
  · refine ⟨Subgroup.map_subtype_le _, (IsSylowOf.isPGroup hT').map _, ?_⟩
    show ¬ 2 ∣ ((T'.map (normalizer (A : Set G)).subtype).comap
      (normalizer (A : Set G)).subtype).index
    rw [Subgroup.comap_map_eq_self_of_injective (normalizer (A : Set G)).subtype_injective T']
    exact fun h => (Nat.not_even_iff_odd.mpr hT'odd) (even_iff_two_dvd.mpr h)
  · exact (Subgroup.map_mono ((IsSylowOf.le hT').trans hYnorm)).trans
      (Subgroup.le_normalizer_map _)

private theorem core_I_le_normalizer_map {G : Type} [Group G] [Finite G]
    {A I Γ : Subgroup G} (hIΓ : I ≤ Γ)
    (Y K : Subgroup ↥Γ) (hHK : I.subgroupOf Γ ≤ K) (hKY : K ≤ Y)
    (hYnorm : Y ≤ normalizer (Y ⊓ A.subgroupOf Γ : Subgroup ↥Γ)) :
    I ≤ normalizer (((Y ⊓ A.subgroupOf Γ).map Γ.subtype : Subgroup G) : Set G) := by
  calc I = (I.subgroupOf Γ).map Γ.subtype := (Subgroup.map_subgroupOf_eq_of_le hIΓ).symm
    _ ≤ Y.map Γ.subtype := Subgroup.map_mono (hHK.trans hKY)
    _ ≤ (normalizer (Y ⊓ A.subgroupOf Γ)).map Γ.subtype := Subgroup.map_mono hYnorm
    _ ≤ normalizer ((Y ⊓ A.subgroupOf Γ).map Γ.subtype) :=
        Subgroup.le_normalizer_map (H := Y ⊓ A.subgroupOf Γ) Γ.subtype

private theorem core_mem_of_sq_mem {G : Type} [Group G] [Finite G]
    {A I Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G)) (hIΓ : I ≤ Γ)
    {Y' K' : Subgroup ↥Γ}
    (hHK' : I.subgroupOf Γ ≤ K')
    (hK'le : K' ≤ normalizer (I.subgroupOf Γ : Set ↥Γ) ⊓ (A ⊔ I).subgroupOf Γ)
    (hK'sub : (K'.subgroupOf
      (normalizer (I.subgroupOf Γ : Set ↥Γ) ⊓ (A ⊔ I).subgroupOf Γ)).IsSubnormal)
    (hK'2 : 2 ∣ (I.subgroupOf Γ).relIndex K') (hK'Y' : K' ≤ Y')
    (hH'pg : IsPGroup 2 (I.subgroupOf Γ))
    (hH'iso : IsPIsolatedOver 2
      (normalizer (I.subgroupOf Γ : Set ↥Γ) ⊓ (A ⊔ I).subgroupOf Γ) (I.subgroupOf Γ)) :
    ∀ d ∈ A ⊓ normalizer (I : Set G), d ^ 2 ∈ I → d ∈ (Y' ⊓ A.subgroupOf Γ).map Γ.subtype := by
  subst hΓ
  intro d hd hd2
  obtain ⟨hdA, hdN⟩ := hd
  set d' : ↥(normalizer (A : Set G)) := ⟨d, le_normalizer hdA⟩ with hd'def
  have hd'K : d' ∈ normalizer (I.subgroupOf (normalizer (A : Set G)) : Set _) ⊓
      (A ⊔ I).subgroupOf (normalizer (A : Set G)) := by
    refine ⟨Subgroup.mem_normalizer_iff.mpr fun x => ⟨?_, ?_⟩,
      mem_subgroupOf.mpr (Subgroup.mem_sup_left hdA)⟩
    · intro hx
      rw [mem_subgroupOf] at hx ⊢
      simpa [hd'def] using (Subgroup.mem_normalizer_iff.mp hdN (x : G)).mp hx
    · intro hx
      rw [mem_subgroupOf] at hx ⊢
      simpa [hd'def] using (Subgroup.mem_normalizer_iff.mp hdN (x : G)).mpr hx
  have hd'2 : d' ^ 2 ∈ I.subgroupOf (normalizer (A : Set G)) := by
    rw [mem_subgroupOf]
    simpa [hd'def] using hd2
  have hmem := hH'iso.mem_of_isSubnormal_over hH'pg
    (le_inf le_normalizer (Subgroup.subgroupOf_mono _ le_sup_right)) inf_le_left
    hHK' hK'le hK'sub hK'2 hd'K hd'2
  exact ⟨d', ⟨hK'Y' hmem, mem_subgroupOf.mpr hdA⟩, rfl⟩

private theorem core_twoResidual_le {G : Type} [Group G] [Finite G]
    {A Γ : Subgroup G} (hΓ : Γ = normalizer (A : Set G)) {Y : Subgroup ↥Γ}
    (hres : twoResidual ((Y ⊓ A.subgroupOf Γ) ⊓
        centralizer (pCoreOf 2 (Y ⊓ A.subgroupOf Γ) : Set ↥Γ)) ≤
      (A.subgroupOf Γ) ⊓ centralizer ((A.subgroupOf Γ) : Set ↥Γ)) :
    twoResidual (((Y ⊓ A.subgroupOf Γ).map Γ.subtype) ⊓
        centralizer (pCoreOf 2 ((Y ⊓ A.subgroupOf Γ).map Γ.subtype) : Set G)) ≤
      A ⊓ centralizer (A : Set G) := by
  subst hΓ
  rw [twoResidual_inf_centralizer_map (normalizer (A : Set G)).subtype_injective
    (Y ⊓ A.subgroupOf (normalizer (A : Set G)))]
  refine (Subgroup.map_mono hres).trans ?_
  refine (Subgroup.map_inf_le _ _ _).trans ?_
  rw [Subgroup.map_subgroupOf_eq_of_le le_normalizer]
  refine inf_le_inf_left A ?_
  have h := Subgroup.map_centralizer_le_centralizer_image
    (A.subgroupOf (normalizer (A : Set G)) : Set ↥(normalizer (A : Set G)))
    (normalizer (A : Set G)).subtype
  rw [← Subgroup.coe_map (normalizer (A : Set G)).subtype
    (A.subgroupOf (normalizer (A : Set G))),
    Subgroup.map_subgroupOf_eq_of_le le_normalizer] at h
  exact h

theorem exists_core_of_gomiChevCore (hIso : GomiChevIsolated) (hCore : GomiChevCore)
    {G : Type} [Group G] [Finite G] {A I : Subgroup G} (hA : IsGomiChevTwo ↥A)
    (hexc : ¬ (IsGomiL2 (↥A ⧸ center ↥A) ∨ IsGomiU3 (↥A ⧸ center ↥A) ∨
      IsGomiSz (↥A ⧸ center ↥A)))
    (hswap : (IsGomiL3 (↥A ⧸ center ↥A) ∨ IsGomiSp4 (↥A ⧸ center ↥A)) →
      ∃ T : Subgroup G, IsSylowTwoOf T (normalizer (A : Set G)) ∧ ¬ IsGomiParabolicSwap T A)
    (hIA : I ≤ normalizer (A : Set G)) (hI : IsPGroup 2 I)
    (hiso : IsPIsolatedOver 2 (normalizer (I : Set G) ⊓ (A ⊔ I)) I) :
    ∃ Q : Subgroup G, Q ≤ A ∧ Q ≠ A ∧ A ⊓ normalizer (Q : Set G) ≤ Q ∧
      (∃ T : Subgroup G, IsSylowTwoOf T (normalizer (A : Set G)) ∧
        T ≤ normalizer (Q : Set G)) ∧
      I ≤ normalizer (Q : Set G) ∧ (∀ d ∈ A ⊓ normalizer (I : Set G), d ^ 2 ∈ I → d ∈ Q) ∧
      twoResidual (Q ⊓ centralizer (pCoreOf 2 Q : Set G)) ≤ A ⊓ centralizer (A : Set G) := by
  classical
  by_cases hIbot : I = ⊥
  · exact (gomiChevCore_bot_case hIso hA hexc hI hiso hIbot).elim
  · let Γ : Subgroup G := normalizer (A : Set G)
    obtain ⟨Y', hY'ne, hY'odd, ⟨K', hHK', hK'le, hK'sub, hK'2, hK'Y'⟩, hNY', hres'⟩ :=
      core_data_of_gomiChevCore hCore rfl hA hexc hswap hIA hI hiso hIbot
    have hH'pg : IsPGroup 2 (I.subgroupOf Γ) := hI.comap_subtype
    have hH'iso := isPIsolatedOver_subgroupOf_normalizer rfl hIA hiso
    exact ⟨(Y' ⊓ A.subgroupOf Γ).map Γ.subtype,
      core_map_inf_le_A rfl Y',
      core_map_inf_ne_A rfl hA hNY' hres',
      core_inf_normalizer_le rfl Y' hNY',
      exists_sylow_le_normalizer_map rfl hY'odd,
      core_I_le_normalizer_map hIA Y' K' hHK' hK'Y' (le_normalizer_inf_subgroupOf rfl),
      core_mem_of_sq_mem rfl hIA hHK' hK'le hK'sub hK'2 hK'Y' hH'pg hH'iso,
      core_twoResidual_le rfl hres'⟩

end CFSG.GroupTheory

end
