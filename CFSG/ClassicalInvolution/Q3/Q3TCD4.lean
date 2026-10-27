module

public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3EXDef
public import CFSG.ClassicalInvolution.Q3.Q3NGStar
public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TC

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.RouteD.NonClassical (le_centralizer_of_commutes)


theorem modelTwinClass_of_layer_family3 {G : Type} [Group G] [Finite G] {ι : Type}
    {Ω : Set (Subgroup G)} {x : G} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {j : ι} {t : StatedLieTag} {n : ℕ}
    (hk : D.kind j = CompData.model t n) (hft : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {a : ℕ} (T : Fin a → Subgroup G)
    (hTx : ∀ k, T k ∈ centralizingMembers Ω {x})
    (hTj : ∀ k, locImg Ω x (T k) ≤ (D.hom j).range) (hinj : Function.Injective T)
    (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, ∀ k l,
      (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
    ModelTwinClass 3 t n 1 a := by
  have hsc : FundamentalSingleClass t (modelUniv t n 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three (modelFacts_isFundTag hft) hadm
      hG2 hD4
  have hpc : PowCop3 (D.kind j) := hk ▸ powCop3_model hft hadm hG2 hD4
  have hsc' : ∀ R ∈ (D.kind j).fund, ∀ R' ∈ (D.kind j).fund, ∃ g, R' = conjSub g R := by
    rw [hk]
    exact hsc
  choose R hR using fun k =>
    exists_corr_left3 hΩ hex hP1 hO3 D (⟨hTx k, hTj k⟩ : T k ∈ compMembers3 Ω x D j)
  have main : ∃ F : Fin a → Subgroup (D.kind j).G, (∀ k, F k ∈ (D.kind j).fund) ∧
      Function.Injective F ∧ (∀ k l, k ≠ l → Commutes (F k) (F l)) ∧
      ∀ k l, ∀ S ∈ (D.kind j).fund, (S = F k ∨ Commutes S (F k)) ↔
        (S = F l ∨ Commutes S (F l)) := by
    refine ⟨R, fun k => (hR k).2.1, ?_, ?_, ?_⟩
    · intro k l hkl
      exact hinj (corr_unique_right3 hΩ hex hP1 hO3 (hR k) (hkl ▸ hR l))
    · intro k l hkl
      exact (corr_commutes3 hΩ hex hP1 hO3 hpc (hR k) (hR l)).mp (hcomm k l hkl)
    · intro k l S hS
      obtain ⟨N, hN⟩ := exists_corr_right3 hΩ D hsc' hS
      have key : ∀ m, (S = R m ∨ Commutes S (R m)) ↔ (N = T m ∨ Commutes N (T m)) := by
        intro m
        constructor
        · rintro (h | h)
          · left
            exact corr_unique_right3 hΩ hex hP1 hO3 (h ▸ hN) (hR m)
          · right
            exact (corr_commutes3 hΩ hex hP1 hO3 hpc hN (hR m)).mpr h
        · rintro (h | h)
          · left
            exact corr_unique_left3 hpc (h ▸ hN) (hR m)
          · right
            exact (corr_commutes3 hΩ hex hP1 hO3 hpc hN (hR m)).mp h
      rw [key k, key l]
      exact htwin N hN.1 k l
  generalize D.kind j = c at main hk
  subst hk
  exact main



theorem exists_d4_component_of_twin_product3 (hTw : MFTwin3) (h3 : OddThreeFreeInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (hR : RouteD3Setup K z)
    {T₁ : Subgroup G} (hT₁ : T₁ ∈ centralizingMembers (conjClass3 K) {z}) (hT₁K : T₁ ≠ K)
    (hT₁comm : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T₁ → Commutes T₁ N)
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z}) (hK₂K : K₂ ≠ K)
    (hK₂T : K₂ ≠ T₁) {w : G} (hw : IsClassicalMember3 K₂ w) (hzw : z ≠ w)
    (hP1x : LocalOddCentral (conjClass3 K) {z * w})
    (hO3x : LocalOddThreeFree3 (conjClass3 K) (z * w))
    (hlink : LinkedAtProduct (conjClass3 K) K z w) :
    ∃ (ι : Type) (_ : Finite ι)
      (D : LieSystemData3 ι (locQuot (conjClass3 K) (z * w)) (locFamily (conjClass3 K) (z * w)))
      (c : ι), D.kind c = CompData.model .POmegaPlus 4 ∧ Commutes K K₂ ∧
      K ∈ compMembers3 (conjClass3 K) (z * w) D c ∧
      K₂ ∈ compMembers3 (conjClass3 K) (z * w) D c ∧
      T₁ ∈ compMembers3 (conjClass3 K) (z * w) D c ∧
      ∀ N ∈ centralizingMembers (conjClass3 K) {z * w}, N ≠ K → ¬ Commutes K N →
        N ∈ compMembers3 (conjClass3 K) (z * w) D c := by
  classical
  obtain ⟨hex, -⟩ := hR.setup
  have hΩ := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := fun L hL => by
    obtain ⟨g, hg⟩ := hL
    exact ⟨g, hg.symm⟩
  have hz := hR.cls
  have hcen := center_eq_bot hnab
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hKΩ, isSubnormal_le hz.subnormal⟩
  have hK₂w : K₂ ∈ centralizingMembers (conjClass3 K) {w} :=
    ⟨hK₂.1, isSubnormal_le hw.subnormal⟩
  have cpz : ∀ {L : Subgroup G}, L ∈ centralizingMembers (conjClass3 K) {z} →
      Commutes K L ∨ L = K := fun hL => cp_at_member3 h3 hnab hR hKΩ hz hL
  have cpw : ∀ {L : Subgroup G}, L ∈ centralizingMembers (conjClass3 K) {w} →
      Commutes K₂ L ∨ L = K₂ := fun hL => cp_at_member3 h3 hnab hR hK₂.1 hw hL
  have hKK₂ : Commutes K K₂ := (cpz hK₂).resolve_right hK₂K
  obtain ⟨t₁, ht₁⟩ := hΩ.classical T₁ hT₁.1
  have hΩt : centralizingMembers (conjClass3 K) {t₁} = centralizingMembers (conjClass3 K) {z} :=
    centralizingMembers_eq_of_twin3 hΩ hz ht₁ (hsingle T₁ hT₁.1) hT₁ hT₁comm
  have hx_nc : ¬ ({z * w} : Set G) ⊆ Subgroup.center G := by
    intro h
    have h1 : z * w ∈ Subgroup.center G := h rfl
    rw [hcen, Subgroup.mem_bot] at h1
    apply hzw
    rw [eq_inv_of_mul_eq_one_left h1]
    exact inv_eq_of_mul_eq_one_right (mul_self_of_isClassicalMember3 hw)
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {z * w} hx_nc
  have hcent_x : ∀ {N : Subgroup G}, N ∈ conjClass3 K → N ≤ Subgroup.centralizer ({z} : Set G) →
      N ≤ Subgroup.centralizer ({w} : Set G) →
        N ∈ centralizingMembers (conjClass3 K) {z * w} :=
    fun hN h1 h2 => ⟨hN, fun n hn => mem_centralizer_mul (h1 hn) (h2 hn)⟩
  have hKx : K ∈ centralizingMembers (conjClass3 K) {z * w} :=
    hcent_x hKΩ (isSubnormal_le hz.subnormal) (le_centralizer_of_commutes hKK₂ hw.mem)
  have hK₂x : K₂ ∈ centralizingMembers (conjClass3 K) {z * w} :=
    hcent_x hK₂.1 hK₂.2 (isSubnormal_le hw.subnormal)
  have hT₁x : T₁ ∈ centralizingMembers (conjClass3 K) {z * w} :=
    hcent_x hT₁.1 hT₁.2 (le_centralizer_of_commutes (hT₁comm K₂ hK₂ hK₂T) hw.mem)
  have hCzw : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass3 K) {z * w} →
      (N ≤ Subgroup.centralizer ({z} : Set G) ↔ N ≤ Subgroup.centralizer ({w} : Set G)) := by
    intro N hN
    exact ⟨fun h n hn => mem_centralizer_right_of_mul (hN.2 hn) (h hn),
      fun h n hn => mem_centralizer_left_of_mul (hN.2 hn) (h hn)⟩
  have hPK : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass3 K) {z * w} →
      ((N = K ∨ Commutes N K) ↔ N ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro N hN
    constructor
    · rintro (rfl | h)
      · exact isSubnormal_le hz.subnormal
      · exact le_centralizer_of_commutes h hz.mem
    · intro h
      rcases cpz ⟨hN.1, h⟩ with h' | h'
      · exact Or.inr (Commutes.symm h')
      · exact Or.inl h'
  have hPK₂ : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass3 K) {z * w} →
      ((N = K₂ ∨ Commutes N K₂) ↔ N ≤ Subgroup.centralizer ({w} : Set G)) := by
    intro N hN
    constructor
    · rintro (rfl | h)
      · exact isSubnormal_le hw.subnormal
      · exact le_centralizer_of_commutes h hw.mem
    · intro h
      rcases cpw ⟨hN.1, h⟩ with h' | h'
      · exact Or.inr (Commutes.symm h')
      · exact Or.inl h'
  have hPT : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass3 K) {z * w} →
      ((N = T₁ ∨ Commutes N T₁) ↔ N ≤ Subgroup.centralizer ({z} : Set G)) := by
    intro N hN
    constructor
    · rintro (rfl | h)
      · exact hT₁.2
      · have hmem : N ∈ centralizingMembers (conjClass3 K) {t₁} :=
          ⟨hN.1, le_centralizer_of_commutes h ht₁.mem⟩
        rw [hΩt] at hmem
        exact hmem.2
    · intro h
      by_cases hNT : N = T₁
      · exact Or.inl hNT
      · exact Or.inr (Commutes.symm (hT₁comm N ⟨hN.1, h⟩ hNT))
  obtain ⟨N₀, hN₀x, hN₀K, hN₀nc⟩ := hlink
  have hN₀z : ¬ N₀ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro h
    rcases (hPK hN₀x).mpr h with h' | h'
    · exact hN₀K h'
    · exact hN₀nc (Commutes.symm h')
  obtain ⟨i₀, hKi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
  obtain ⟨j₀, hN₀j⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N₀, hN₀x, rfl⟩)
  have hij : i₀ = j₀ :=
    eq_of_not_commutes3 hΩ hex hP1x hO3x D ⟨hKx, hKi⟩ ⟨hN₀x, hN₀j⟩ hN₀nc
  subst hij
  obtain ⟨b, hKb⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₂, hK₂x, rfl⟩)
  have hb : b = i₀ := by
    by_contra hb
    have hc : Commutes N₀ K₂ :=
      commutes_of_ne_comp3 hΩ hex hP1x hO3x D (Ne.symm hb) ⟨hN₀x, hN₀j⟩ ⟨hK₂x, hKb⟩
    exact hN₀z ((hCzw hN₀x).mpr (le_centralizer_of_commutes hc hw.mem))
  subst hb
  obtain ⟨c, hTc⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨T₁, hT₁x, rfl⟩)
  have hc : c = b := by
    by_contra hc
    have hcm : Commutes N₀ T₁ :=
      commutes_of_ne_comp3 hΩ hex hP1x hO3x D (Ne.symm hc) ⟨hN₀x, hN₀j⟩ ⟨hT₁x, hTc⟩
    exact hN₀z ((hPT hN₀x).mp (Or.inr hcm))
  subst hc
  have hKc : K ∈ compMembers3 (conjClass3 K) (z * w) D c := ⟨hKx, hKi⟩
  have hK₂c : K₂ ∈ compMembers3 (conjClass3 K) (z * w) D c := ⟨hK₂x, hKb⟩
  have hT₁c : T₁ ∈ compMembers3 (conjClass3 K) (z * w) D c := ⟨hT₁x, hTc⟩
  have hN₀c : N₀ ∈ compMembers3 (conjClass3 K) (z * w) D c := ⟨hN₀x, hN₀j⟩
  have hnA1 : ¬ IsA1Comp3 D c := fun hA =>
    hN₀K (eq_of_mem_compMembers_a13 hΩ hex hP1x hO3x hA hN₀c hKc)
  rcases kind_cases_of_not_a1 D hnA1 with ⟨t, n, hft, hadm, hk⟩ | hk
  swap
  · exact absurd hKK₂ (not_commutes_of_m11_comp3 hΩ hex hP1x hO3x hk hKc hK₂c)
  have hexc : t ≠ .G2 ∧ t ≠ .trialityD4 := by
    refine ⟨fun ht => ?_, fun ht => ?_⟩
    · exact hzw (eq_involution_of_commuting_in_g2d43 hΩ hex hP1x hO3x D (Or.inl ht) hadm hk hT₁c
        hKc hK₂c ht₁ hz hw (hT₁comm K hKz hT₁K.symm) (hT₁comm K₂ hK₂ hK₂T))
    · exact hzw (eq_involution_of_commuting_in_g2d43 hΩ hex hP1x hO3x D (Or.inr ht) hadm hk hT₁c
        hKc hK₂c ht₁ hz hw (hT₁comm K hKz hT₁K.symm) (hT₁comm K₂ hK₂ hK₂T))
  have hTk : ∀ N ∈ centralizingMembers (conjClass3 K) {z * w}, ∀ k : Fin 3,
      (N = ![K, K₂, T₁] k ∨ Commutes N (![K, K₂, T₁] k)) ↔
        N ≤ Subgroup.centralizer ({z} : Set G) := by
    intro N hN k
    fin_cases k
    · exact hPK hN
    · exact (hPK₂ hN).trans (hCzw hN).symm
    · exact hPT hN
  have hTx : ∀ k : Fin 3, ![K, K₂, T₁] k ∈ centralizingMembers (conjClass3 K) {z * w} := by
    intro k
    fin_cases k
    · exact hKx
    · exact hK₂x
    · exact hT₁x
  have hTj : ∀ k : Fin 3, locImg (conjClass3 K) (z * w) (![K, K₂, T₁] k) ≤ (D.hom c).range := by
    intro k
    fin_cases k
    · exact hKi
    · exact hKb
    · exact hTc
  have hinj : Function.Injective ![K, K₂, T₁] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; simp_all)
  have hcomm : ∀ k l : Fin 3, k ≠ l → Commutes (![K, K₂, T₁] k) (![K, K₂, T₁] l) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact hKK₂
      | exact Commutes.symm hKK₂
      | exact Commutes.symm (hT₁comm K hKz hT₁K.symm)
      | exact hT₁comm K hKz hT₁K.symm
      | exact Commutes.symm (hT₁comm K₂ hK₂ hK₂T)
      | exact hT₁comm K₂ hK₂ hK₂T
  have hmtc : ModelTwinClass 3 t n 1 3 :=
    modelTwinClass_of_layer_family3 hΩ hex hP1x hO3x D hk hft hadm hexc.1 hexc.2 ![K, K₂, T₁] hTx
      hTj hinj hcomm fun N hN k l => (hTk N hN k).trans (hTk N hN l).symm
  rcases hTw t n 3 hft hexc.1 hexc.2 hadm (not_psl_two_of_admissible3 hadm) (by norm_num) hmtc
    with h | ⟨rfl, rfl, -⟩
  · exact absurd (Asc77.ShapeTable.le_two h) (by norm_num)
  refine ⟨ι, hι, D, c, hk, hKK₂, hKc, hK₂c, hT₁c, ?_⟩
  intro N hN hNK hnc
  obtain ⟨j', hj'⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  have hcj : c = j' := eq_of_not_commutes3 hΩ hex hP1x hO3x D hKc ⟨hN, hj'⟩ hnc
  subst hcj
  exact ⟨hN, hj'⟩

end CFSG.ClassicalInvolution.Q3.Q3TC
