module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace CFSG.AGLEmbedding

namespace AscEightFive

open AscEightFour

section SylowProduct

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem isSylowTwoOf_map {Δ : Type*} [Group Δ] {B L : Subgroup Γ} (hB : IsSylowTwoOf B L)
    (π : Γ →* Δ) : IsSylowTwoOf (B.map π) (L.map π) := by
  refine ⟨Subgroup.map_mono hB.1, hB.2.1.map π, ?_⟩
  let ρ : ↥L →* ↥(L.map π) := π.subgroupMap L
  have hρ : Function.Surjective ρ := π.subgroupMap_surjective L
  have heq : (B.subgroupOf L).map ρ ≤ (B.map π).subgroupOf (L.map π) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have h1 : ((B.map π).subgroupOf (L.map π)).index ∣ (B.subgroupOf L).index :=
    (Subgroup.index_dvd_of_le heq).trans (Subgroup.index_map_dvd _ hρ)
  exact fun hd => hB.2.2 (hd.trans h1)

omit [Finite Γ] in
theorem isSylowTwoOf_of_le {P T L : Subgroup Γ} (hP : IsSylowTwoOf P L) (hPT : P ≤ T) (hTL : T ≤ L)
    (hT : IsPGroup 2 T) : IsSylowTwoOf T L := by
  refine ⟨hTL, hT, fun hd => hP.2.2 (hd.trans ?_)⟩
  exact Subgroup.index_dvd_of_le (fun x hx => hPT hx)

omit [Finite Γ] in
theorem isSylowTwoOf_sup_of_commute {A B PA PB : Subgroup Γ} (hA : IsSylowTwoOf PA A)
    (hB : IsSylowTwoOf PB B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsSylowTwoOf (PA ⊔ PB) (A ⊔ B) := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  let φ : ↥A × ↥B →* Γ := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hφ : ∀ x, φ x ∈ A ⊔ B := fun x =>
    (A ⊔ B).mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
  let ψ : ↥A × ↥B →* ↥(A ⊔ B) := φ.codRestrict (A ⊔ B) hφ
  have hψ : Function.Surjective ψ := by
    have hNA : A ≤ Subgroup.normalizer (B : Set Γ) := fun a ha =>
      Subgroup.mem_normalizer_iff.mpr fun b => by
        constructor
        · intro hb; rw [hc a ha b hb, mul_assoc, mul_inv_cancel, mul_one]; exact hb
        · intro hb
          have h := hc a ha (a * b * a⁻¹) hb
          have : b = a * b * a⁻¹ := by
            calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
              _ = a⁻¹ * (a * (a * b * a⁻¹)) * a⁻¹ * a := by rw [h]; group
              _ = a * b * a⁻¹ := by group
          rw [this]; exact hb
    rintro ⟨y, hy⟩
    have hy' : y ∈ ((A ⊔ B : Subgroup Γ) : Set Γ) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hNA] at hy'
    obtain ⟨a, ha, b, hb, rfl⟩ := hy'
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hPAB : PA ⊔ PB ≤ A ⊔ B := sup_le_sup hA.1 hB.1
  have h2 : IsPGroup 2 ↥(PA ⊔ PB) := by
    refine IsPGroup.to_sup_of_normal_right' hA.2.1 hB.2.1 ?_
    intro a ha
    refine Subgroup.mem_normalizer_iff.mpr fun b => ?_
    constructor
    · intro hb; rw [hc a (hA.1 ha) b (hB.1 hb), mul_assoc, mul_inv_cancel, mul_one]; exact hb
    · intro hb
      have h := hc a (hA.1 ha) (a * b * a⁻¹) (hB.1 hb)
      have : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
          _ = a⁻¹ * (a * (a * b * a⁻¹)) * a⁻¹ * a := by rw [h]; group
          _ = a * b * a⁻¹ := by group
      rw [this]; exact hb
  refine ⟨hPAB, h2, fun hd => ?_⟩
  have hmap : ((PA.subgroupOf A).prod (PB.subgroupOf B)).map ψ ≤
      (PA ⊔ PB).subgroupOf (A ⊔ B) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (PA ⊔ PB).mul_mem (Subgroup.mem_sup_left hx.1) (Subgroup.mem_sup_right hx.2)
  have h1 : ((PA ⊔ PB).subgroupOf (A ⊔ B)).index ∣
      (PA.subgroupOf A).index * (PB.subgroupOf B).index := by
    rw [← Subgroup.index_prod]
    exact (Subgroup.index_dvd_of_le hmap).trans (Subgroup.index_map_dvd _ hψ)
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp (hd.trans h1) with h | h
  · exact hA.2.2 h
  · exact hB.2.2 h


omit [Finite Γ] in
theorem isSylowTwoOf_inf_iSup {T : Subgroup Γ} (hT : IsPGroup 2 T) (𝒪 : Finset (Subgroup Γ))
    (hsyl : ∀ A ∈ 𝒪, IsSylowTwoOf (T ⊓ A) A)
    (hcomm : ∀ A ∈ 𝒪, ∀ B ∈ 𝒪, A ≠ B → ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsSylowTwoOf (T ⊓ ⨆ A ∈ 𝒪, A) (⨆ A ∈ 𝒪, A) := by
  classical
  induction 𝒪 using Finset.induction_on with
  | empty =>
    have hbot : (⨆ A ∈ (∅ : Finset (Subgroup Γ)), A) = ⊥ := by simp
    rw [hbot, inf_bot_eq]
    refine ⟨le_rfl, IsPGroup.of_bot, ?_⟩
    rw [Subgroup.index_eq_one.mpr (Subsingleton.elim _ _)]
    norm_num
  | insert a s ha ih =>
    rw [Finset.iSup_insert]
    have ih' := ih (fun A hA => hsyl A (Finset.mem_insert_of_mem hA))
      (fun A hA B hB hne =>
        hcomm A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) hne)
    have hle : (⨆ A ∈ s, A) ≤ Subgroup.centralizer (a : Set Γ) := by
      refine iSup₂_le fun A hA z hz => Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      exact hcomm a (Finset.mem_insert_self a s) A (Finset.mem_insert_of_mem hA)
        (fun h => ha (h ▸ hA)) w hw z hz
    have hca : ∀ x ∈ a, ∀ y ∈ ⨆ A ∈ s, A, x * y = y * x := fun x hx y hy =>
      Subgroup.mem_centralizer_iff.mp (hle hy) x hx
    have h2 := isSylowTwoOf_sup_of_commute (hsyl a (Finset.mem_insert_self a s)) ih' hca
    exact isSylowTwoOf_of_le h2
      (sup_le (inf_le_inf_left T le_sup_left) (inf_le_inf_left T le_sup_right)) inf_le_right
      (hT.to_le inf_le_left)

end SylowProduct

section Generic

variable {G : Type} [Group G]






theorem charTwo_of_le {X S H : Subgroup G} (hyp : Asc81bHyp X S) (hQH : pCoreOf 2 X ≤ H)
    (hHX : H ≤ X) : CharTwo H := by
  have hQn : ((pCoreOf 2 X).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr
      (hHX.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X))
  have hQle : pCoreOf 2 X ≤ pCoreOf 2 H :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ hQH hQn
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 X)
  rintro g ⟨hgH, hgC⟩
  exact hQle (hyp.charTwo ⟨hHX hgH,
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQle) hgC⟩)

theorem isSylowTwoOf_subgroupOf {A B X : Subgroup G} (h : IsSylowTwoOf A B) (hBX : B ≤ X) :
    IsSylowTwoOf (A.subgroupOf X) (B.subgroupOf X) := by
  refine ⟨fun x hx => h.1 hx, h.2.1.comap_subtype, ?_⟩
  have : ((A.subgroupOf X).subgroupOf (B.subgroupOf X)).index = (A.subgroupOf B).index :=
    Subgroup.relIndex_subgroupOf hBX
  rw [this]
  exact h.2.2

end Generic

section EightFiveSylow

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

@[expose] noncomputable def orbitFS (X S L : Subgroup G) :
    Finset (Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  classical
  have : Fintype ↥(barM X S) := Fintype.ofFinite _
  exact (Finset.univ : Finset ↥(barM X S)).image fun t : ↥(barM X S) =>
    (barM X L).map (MulAut.conj t.1).toMonoidHom

theorem mem_orbitFS {A : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} :
    A ∈ orbitFS X S L ↔ ∃ t ∈ barM X S, A = (barM X L).map (MulAut.conj t).toMonoidHom := by
  classical
  unfold orbitFS
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, -, ht⟩
    exact ⟨t, t.2, ht.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, @Finset.mem_univ _ (Fintype.ofFinite _) _, rfl⟩

@[expose] noncomputable def dBar (X S L : Subgroup G) : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
  ⨆ A ∈ orbitFS X S L, A

theorem le_dBar_of_mem {A : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hA : A ∈ orbitFS X S L) :
    A ≤ dBar X S L :=
  le_iSup₂_of_le A hA le_rfl

theorem barM_le_dBar : barM X L ≤ dBar X S L := by
  refine le_dBar_of_mem (mem_orbitFS.mpr ⟨1, one_mem _, ?_⟩)
  ext x
  simp


theorem isComponentOf_of_mem_orbitFS (hL : IsTwoPrimeComponent X L)
    {A : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hA : A ∈ orbitFS X S L) : IsComponentOf A ⊤ := by
  obtain ⟨t, -, rfl⟩ := mem_orbitFS.mp hA
  exact (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj t) _).mpr hL.component

theorem commute_of_mem_orbitFS (hL : IsTwoPrimeComponent X L)
    {A B : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)} (hA : A ∈ orbitFS X S L) (hB : B ∈ orbitFS X S L)
    (hne : A ≠ B) : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne A B
    (isComponentOf_of_mem_orbitFS hL hA) (isComponentOf_of_mem_orbitFS hL hB) hne
  intro a ha b hb
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
  exact (Subgroup.mem_centralizer_iff.mp this b hb).symm

theorem isSylowTwoOf_barM_inf (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsSylowTwoOf (barM X S ⊓ barM X L) (barM X L) := by
  have h1 := isSylowTwoOf_map (isSylowTwoOf_subgroupOf hsyl hL.le)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  refine isSylowTwoOf_of_le h1 ?_ inf_le_right
    ((AscEightFour.barM_isPGroup hyp.twoRadical.isPGroup).to_le inf_le_left)
  exact le_inf (Subgroup.map_mono fun x hx => hx.1) (Subgroup.map_mono fun x hx => hx.2)

theorem isSylowTwoOf_of_mem_orbitFS (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) {A : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)}
    (hA : A ∈ orbitFS X S L) : IsSylowTwoOf (barM X S ⊓ A) A := by
  obtain ⟨t, ht, rfl⟩ := mem_orbitFS.mp hA
  have h1 := isSylowTwoOf_map (isSylowTwoOf_barM_inf hyp hL hsyl) (MulAut.conj t).toMonoidHom
  refine isSylowTwoOf_of_le h1 ?_ inf_le_right
    ((AscEightFour.barM_isPGroup hyp.twoRadical.isPGroup).to_le inf_le_left)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ⟨x, hx.2, rfl⟩⟩
  change t * x * t⁻¹ ∈ barM X S
  exact (barM X S).mul_mem ((barM X S).mul_mem ht hx.1) ((barM X S).inv_mem ht)

theorem isSylowTwoOf_dBar (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) :
    IsSylowTwoOf (barM X S ⊓ dBar X S L) (dBar X S L) :=
  isSylowTwoOf_inf_iSup (AscEightFour.barM_isPGroup hyp.twoRadical.isPGroup) (orbitFS X S L)
    (fun _ hA => isSylowTwoOf_of_mem_orbitFS hyp hL hsyl hA)
    (fun _ hA _ hB hne => commute_of_mem_orbitFS hL hA hB hne)

theorem barM_le_normalizer_dBar :
    barM X S ≤ Subgroup.normalizer (dBar X S L : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
  apply le_normalizer_of_forall_map_conj_le
  intro g hg
  unfold dBar
  rw [Subgroup.map_iSup]
  refine iSup_le fun A => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hA => ?_
  obtain ⟨t, ht, rfl⟩ := mem_orbitFS.mp hA
  refine le_dBar_of_mem (mem_orbitFS.mpr ⟨g * t, (barM X S).mul_mem hg ht, ?_⟩)
  rw [map_conj_mul_eq]

@[expose] noncomputable def hBar (X S L : Subgroup G) : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X) :=
  dBar X S L ⊔ barM X S

theorem isSylowTwoOf_hBar (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsSylowTwoOf (barM X S) (hBar X S L) := by
  have hN := barM_le_normalizer_dBar (X := X) (S := S) (L := L)
  have hD := isSylowTwoOf_dBar hyp hL hsyl
  refine isSylowTwoOf_of_forall_normalizer_le le_sup_right
    (AscEightFour.barM_isPGroup hyp.twoRadical.isPGroup) ?_
  intro U hUH hU2 hSU _ u hu
  have hu' : u ∈ ((barM X S ⊔ dBar X S L : Subgroup _) : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
    rw [sup_comm]; exact hUH hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hu'
  obtain ⟨s, hs, d, hd, rfl⟩ := hu'
  have hdU : d ∈ U := by
    have := U.mul_mem (U.inv_mem (hSU hs)) hu
    simpa using this
  have heq := isSylowTwoOf_eq_of_le hD (inf_le_right : U ⊓ dBar X S L ≤ dBar X S L)
    (hU2.to_le inf_le_left) (inf_le_inf_right _ hSU)
  have hdS : d ∈ barM X S ⊓ dBar X S L := heq ▸ ⟨hdU, hd⟩
  exact (barM X S).mul_mem hs hdS.1

@[expose] noncomputable def hGrp5 (X S L : Subgroup G) : Subgroup G :=
  ((hBar X S L).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map X.subtype

theorem hGrp5_le : hGrp5 X S L ≤ X := Subgroup.map_subtype_le _

theorem mem_hGrp5 {x : ↥X} :
    (x : G) ∈ hGrp5 X S L ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥X) x ∈ hBar X S L := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain rfl : y = x := Subtype.ext hyx
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

theorem le_hGrp5_of_barM_le {Y : Subgroup G} (hYX : Y ≤ X) (h : barM X Y ≤ hBar X S L) :
    Y ≤ hGrp5 X S L := fun y hy =>
  (mem_hGrp5 (x := ⟨y, hYX hy⟩)).mpr (h ⟨⟨y, hYX hy⟩, hy, rfl⟩)

theorem barM_le_of_le_hGrp5 {Y : Subgroup G} (h : Y ≤ hGrp5 X S L) : barM X Y ≤ hBar X S L := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_hGrp5 (x := x)).mp (h hx)

theorem twoCore_le_hGrp5 : pCoreOf 2 X ≤ hGrp5 X S L := by
  rintro _ ⟨y, hy, rfl⟩
  refine (mem_hGrp5 (x := y)).mpr ?_
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) y = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff y).mpr hy
  rw [h1]
  exact one_mem _

theorem isSylowTwoOf_hGrp5 (hyp : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hsyl : IsSylowTwoOf (S ⊓ L) L) : IsSylowTwoOf S (hGrp5 X S L) := by
  have hSX := hyp.twoRadical.1
  have hQS := hyp.twoCore_le
  have hSH : S ≤ hGrp5 X S L :=
    le_hGrp5_of_barM_le hSX le_sup_right
  refine isSylowTwoOf_of_forall_normalizer_le hSH hyp.twoRadical.isPGroup ?_
  intro U hUH hU2 hSU _ u hu
  have hUX : U ≤ X := hUH.trans hGrp5_le
  have hUeq := isSylowTwoOf_eq_of_le (isSylowTwoOf_hBar hyp hL hsyl) (barM_le_of_le_hGrp5 hUH)
    (AscEightFour.barM_isPGroup hU2) (Subgroup.map_mono fun x hx => hSU hx)
  have hxu : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨u, hUX hu⟩ ∈ barM X S :=
    hUeq ▸ ⟨⟨u, hUX hu⟩, hu, rfl⟩
  have h2 : (⟨u, hUX hu⟩ : ↥X) ∈ S.subgroupOf X ⊔ CFSG.pCore 2 ↥X := by
    rw [← comap_barM]; exact hxu
  have h3 : CFSG.pCore 2 ↥X ≤ S.subgroupOf X := by
    intro y hy
    exact hQS ⟨y, hy, rfl⟩
  rw [sup_eq_left.mpr h3] at h2
  exact h2

end EightFiveSylow

end AscEightFive

end CFSG.AGLEmbedding
