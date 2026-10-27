module

public import CFSG.ClassicalInvolution.Q3.Q3T8AF01
import CFSG.ClassicalInvolution.Asc77.AscT8T12Eng
public import CFSG.ClassicalInvolution.Q3.Q3NHMain
public import CFSG.ClassicalInvolution.Q3.Q3T8N03

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3T8.AF
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem xMem_of_omegaNbr (hΩ : HypOmegaMod Ω) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {K J : Subgroup G} {z t : G} (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K)
    (ht : IsUniqueInvolution J t) : T8.XMem Ω z J := by
  have hcomm : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ ht
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := hJ
  have hsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  refine ⟨hJΩ, ?_, T, hsyl, fun r hr => ?_⟩
  · exact T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hJΩ (hnt _ hJΩ) ht
      (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  · have h := T3.le_centralizer_of_le_normalizer' hz hTN hr
    exact Subgroup.mem_centralizer_singleton_iff.mp h

theorem mem_tqMembers3_of_omegaNbr (hΩ : HypOmegaMod Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K J : Subgroup G} {z t : G}
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) :
    J ∈ Q3NL.tqMembers3 Ω z :=
  (xMem_of_omegaNbr hΩ hnt hz hJ ht).mem_tqMembers3 hΩ hz.sq

end Basic

section Frame


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isClassicalMember3_of_uniqueInvolution (hΩu : HypOmegaModU (.sl2 3 1) Ω)
    {M : Subgroup G} {x : G} (hM : M ∈ Ω) (hx : IsUniqueInvolution M x) :
    Q3.IsClassicalMember3 M x := by
  obtain ⟨w, hw⟩ := hΩu.classical M hM
  have hwt : w = x := (hw.isUniqueInvolution_sl2).eq hx
  subst hwt
  exact hw.toQ3 (by norm_num)

theorem fuzzyFrame3_of_adj (hΩ : HypOmegaMod Ω) (hΩu : HypOmegaModU (.sl2 3 1) Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K J A : Subgroup G} {z t u : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hu : IsUniqueInvolution A u) (hKJ : J ∈ omegaNbr Ω K) (hKA : A ∈ omegaNbr Ω K)
    (hJA : A ∈ omegaNbr Ω J) (hind : u ∉ Subgroup.closure ({z, t} : Set G)) :
    Q3NL.FuzzyFrame3 Ω (Subgroup.closure ({z, t, u} : Set G)) := by
  have hJΩ : J ∈ Ω := hKJ.1
  have hAΩ : A ∈ Ω := hKA.1
  have hJK : K ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm l6_2 hΩ hK hJΩ hKJ
  have hAK : K ∈ omegaNbr Ω A := Q3CL.T3.omegaNbr_symm l6_2 hΩ hK hAΩ hKA
  have hAJ : J ∈ omegaNbr Ω A := Q3CL.T3.omegaNbr_symm l6_2 hΩ hJΩ hAΩ hJA
  have hc01 : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hKJ ht
  have hc02 : z * u = u * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hKA hu
  have hc12 : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJA hu
  have hne1 : z ≠ t := fun h => by
    have : IsUniqueInvolution J z := h ▸ ht
    exact hKJ.2.1 (hnt K hK J ⟨hJΩ, z, hz, this⟩)
  have hcl : ∀ {M : Subgroup G} {x : G}, M ∈ Ω → IsUniqueInvolution M x →
      Q3.IsClassicalMember3 M x := fun hM hx => isClassicalMember3_of_uniqueInvolution hΩu hM hx
  have hself : ∀ {M : Subgroup G} {x : G}, M ∈ Ω → IsUniqueInvolution M x →
      x ∈ trivialOnQuot M := fun hM hx =>
    mem_trivialOnQuot_of_centralizes fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp
        (isSubnormal_le (hcl hM hx).subnormal hy)).symm
  have hcross : ∀ {M N : Subgroup G} {x y : G}, N ∈ omegaNbr Ω M → IsUniqueInvolution M x →
      IsUniqueInvolution N y → x ∈ trivialOnQuot N := fun hN hx hy =>
    (xMem_of_omegaNbr hΩ hnt hx hN hy).trivialOnQuot3 hΩ hx.sq
  have hrange : Set.range ![z, t, u] = ({z, t, u} : Set G) := by
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have htriv : ∀ i : Fin 3, Subgroup.closure ({z, t, u} : Set G) ≤
      trivialOnQuot (![K, J, A] i) := by
    intro i
    rw [Subgroup.closure_le]
    intro y hy
    fin_cases i
    · rcases hy with rfl | rfl | rfl
      · exact hself hK hz
      · exact hcross hJK ht hz
      · exact hcross hAK hu hz
    · rcases hy with rfl | rfl | rfl
      · exact hcross hKJ hz ht
      · exact hself hJΩ ht
      · exact hcross hAJ hu ht
    · rcases hy with rfl | rfl | rfl
      · exact hcross hKA hz hu
      · exact hcross hJA ht hu
      · exact hself hAΩ hu
  refine ⟨![K, J, A], ![z, t, u], fun i => ?_, ?_,
    T8T.isElemAbelian_closure_three hz.sq ht.sq hu.sq hc01 hc02 hc12,
    T8T.natCard_closure_three hz.sq ht.sq hu.sq hc01 hc02 hc12 hz.ne_one ht.ne_one hne1
      hu.ne_one hind, htriv⟩
  · fin_cases i
    · exact ⟨hK, hcl hK hz⟩
    · exact ⟨hJΩ, hcl hJΩ ht⟩
    · exact ⟨hAΩ, hcl hAΩ hu⟩
  · rw [hrange]

end Frame

section Lift


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_adjacent (hΩ : HypOmegaMod Ω) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {K J A : Subgroup G} {z tJ tA : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hJ : J ∈ omegaNbr Ω K) (hA : A ∈ omegaNbr Ω K) (htJ : IsUniqueInvolution J tJ)
    (htA : IsUniqueInvolution A tA)
    (hcomm : ∀ r ∈ Q3NL.exactCore3 z J, ⁅r, tA⁆ ∈ oddCoreOf (Q3NL.exactLayer3 Ω z)) :
    ∃ o ∈ oddCoreOf (Q3NL.exactLayer3 Ω z), conjSub o A ∈ omegaNbr Ω K ∧
      IsUniqueInvolution (conjSub o A) (o * tA * o⁻¹) ∧
      (conjSub o A = J ∨ (conjSub o A ∈ omegaNbr Ω J ∧ J ∈ omegaNbr Ω (conjSub o A))) := by
  set Y : Subgroup G := Q3NL.exactLayer3 Ω z with hY
  set O : Subgroup G := oddCoreOf Y with hO
  have hJΩ : J ∈ Ω := hJ.1
  have hAΩ : A ∈ Ω := hA.1
  have hodd : Odd (Nat.card O) := oddCoreOf_odd_natCard Y
  have hOY : O ≤ Y := oddCoreOf_le_self Y
  have hYn : ∀ y ∈ Y, ∀ o ∈ O, y * o * y⁻¹ ∈ O := fun y hy o ho =>
    T7R.conj_mem_oddCoreOf hy ho
  have hJt : J ∈ Q3NL.tqMembers3 Ω z := mem_tqMembers3_of_omegaNbr hΩ hnt hz hJ htJ
  have hAt : A ∈ Q3NL.tqMembers3 Ω z := mem_tqMembers3_of_omegaNbr hΩ hnt hz hA htA
  obtain ⟨-, -, R, hR, hRz⟩ := xMem_of_omegaNbr hΩ hnt hz hJ htJ
  have hRcz : R ≤ Subgroup.centralizer ({z} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hRz r hr)
  have hRY : R ≤ Y := fun r hr =>
    Q3NL.exactCore3_le_exactLayer3 hJt ⟨hR.1 hr, hRcz hr⟩
  have htAY : tA ∈ Y := Q3NL.exactCore3_le_exactLayer3 hAt
    ⟨htA.mem, Subgroup.mem_centralizer_singleton_iff.mpr
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hA htA).symm⟩
  have hrt : ∀ r ∈ R, tA⁻¹ * (r * tA * r⁻¹) ∈ O := by
    intro r hr
    have hc : ⁅r, tA⁆ ∈ O := hcomm r ⟨hR.1 hr, hRcz hr⟩
    have h1 := hYn tA⁻¹ (Y.inv_mem htAY) _ hc
    rw [commutatorElement_def] at h1
    convert h1 using 1
    group
  obtain ⟨o, hoO, hfix⟩ := exists_fixed_conj_of_isPGroup htA.sq hodd hR.2.1
    (fun r hr o ho => hYn r (hRY hr) o ho) hrt
  have hoz : o ∈ Subgroup.centralizer ({z} : Set G) :=
    Q3NL.exactLayer3_le_centralizer Ω z (hOY hoO)
  have hoN : o ∈ Subgroup.normalizer (K : Set G) :=
    T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK (hnt K hK) hz hoz
  have hoK : conjSub o K = K := mem_normalizer_iff_conjSub_eq.mp hoN
  have hA'K : conjSub o A ∈ omegaNbr Ω K := by
    have := omegaNbr_conj hΩ.conjInvariant hA o
    rwa [hoK] at this
  have hA'Ω : conjSub o A ∈ Ω := hΩ.conjInvariant o A hAΩ
  refine ⟨o, hoO, hA'K, htA.conj o, ?_⟩
  by_cases hAJ : conjSub o A = J
  · exact Or.inl hAJ
  · right
    have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hJΩ hR
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRset
    have hRc : R ≤ Subgroup.centralizer ({o * tA * o⁻¹} : Set G) := fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        have := hfix r hr
        calc r * (o * tA * o⁻¹) = (r * (o * tA * o⁻¹) * r⁻¹) * r := by group
          _ = (o * tA * o⁻¹) * r := by rw [this])
    have hRN : R ≤ Subgroup.normalizer (conjSub o A : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hA'Ω hJΩ hAJ (htA.conj o) hR.1 hR.2.1
        (by omega) hRc
    have hJA' : J ∈ omegaNbr Ω (conjSub o A) := ⟨hJΩ, Ne.symm hAJ, R, hRset, hR.1, hRN⟩
    exact ⟨Q3CL.T3.omegaNbr_symm l6_2 hΩ hA'Ω hJΩ hJA', hJA'⟩

end Lift

section Alpha


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem alpha_of_triangle [IsSimpleGroup G] {K₀ : Subgroup G} (hs : Q3.Disc3.AscStand3 Ω K₀)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K J A : Subgroup G} {z t u : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t)
    (hu : IsUniqueInvolution A u) (hKJ : J ∈ omegaNbr Ω K) (hKA : A ∈ omegaNbr Ω K)
    (hJA : A ∈ omegaNbr Ω J) (hind : u ∉ Subgroup.closure ({z, t} : Set G)) :
    (∀ F : Subgroup G, F ≤ Subgroup.closure ({z, t, u} : Set G) → IsElemAbelian2 F 2 →
        alphaOf F = alphaOf (Subgroup.closure ({t, z} : Set G))) ∧
      ∀ b ∈ Subgroup.closure ({z, t, u} : Set G),
        oddCoreOf (Subgroup.centralizer ({b} : Set G)) ≤
          Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩu : HypOmegaModU (.sl2 3 1) Ω := hs.hyp
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩu
  have hfr := fuzzyFrame3_of_adj hΩ hΩu hnt hK hz ht hu hKJ hKA hJA hind
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    obtain ⟨a, -, hac⟩ := IsConcreteLE.not_le_iff_exists.mp
      (isClassicalMember3_of_uniqueInvolution hΩu hK hz).not_le_center
    rw [Subgroup.mem_center_iff] at hac
    push Not at hac
    obtain ⟨b, hb⟩ := hac
    exact ⟨b, a, hb⟩
  have hHyp : Hyp51 (Subgroup.closure ({z, t, u} : Set G)) :=
    Q3NH.hyp51_of_fuzzyFrame (Q3T7.inClass3_of_stand3 hs) (Q3T7.cit3Below_of_stand3 hs) hnab hfr
  have hc01 : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hKJ ht
  have hc02 : z * u = u * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hKA hu
  have hc12 : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ ht hJA hu
  have hzt' : t ≠ z := fun h => by
    have : IsUniqueInvolution J z := h ▸ ht
    exact hKJ.2.1 (hnt K hK J ⟨hKJ.1, z, hz, this⟩)
  have hDB : Subgroup.closure ({t, z} : Set G) ≤ Subgroup.closure ({z, t, u} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    rcases hy with rfl | rfl <;> simp
  have hD : IsElemAbelian2 (Subgroup.closure ({t, z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair ht.sq hz.sq ht.ne_one hz.ne_one hzt' hc01.symm
  have h3 := (lemma54_odd_and_eq hHyp hDB hD).2
  refine ⟨h3, fun b hb => ?_⟩
  exact T8T.oddCoreOf_centralizer_le_normalizer hHyp.1 hHyp.2.1 hb h3

end Alpha

section Transfer


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem closure_pair_mul_left {z t : G} (hz : z * z = 1) :
    Subgroup.closure ({z * t, z} : Set G) = Subgroup.closure ({t, z} : Set G) := by
  exact CFSG.ClassicalInvolution.Asc77.T8T.closure_pair_mul_leftE hz

theorem oddCore_le_normalizer_alpha [IsSimpleGroup G] {K₀ : Subgroup G}
    (hs : Q3.Disc3.AscStand3 Ω K₀) (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M)
    {K A B : Subgroup G} {z tA tB : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hA : A ∈ omegaNbr Ω K) (hB : B ∈ omegaNbr Ω K) (htA : IsUniqueInvolution A tA)
    (htB : IsUniqueInvolution B tB) (hAB : B ∈ omegaNbr Ω A)
    (hind : tB ∉ Subgroup.closure ({z, tA} : Set G)) :
    oddCoreOf (Q3NL.exactLayer3 Ω z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  obtain ⟨-, hnorm⟩ := alpha_of_triangle hs hnt hK hz htA htB hA hB hAB hind
  have hzB : z ∈ Subgroup.closure ({z, tA, tB} : Set G) := Subgroup.subset_closure (by simp)
  exact (T8T.oddCoreOf_layerJoin_le_oddCoreOf_centralizer hΩ z).trans (hnorm z hzB)

theorem alphaOf_eq_of_comm [IsSimpleGroup G] {K₀ : Subgroup G} (hs : Q3.Disc3.AscStand3 Ω K₀)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {K J A : Subgroup G} {z tJ tA : G}
    (hK : K ∈ Ω) (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K)
    (hA : A ∈ omegaNbr Ω K) (htJ : IsUniqueInvolution J tJ) (htA : IsUniqueInvolution A tA)
    (hOn : oddCoreOf (Q3NL.exactLayer3 Ω z) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({tA, z} : Set G)) : Set G))
    (hcomm : ∀ r ∈ Q3NL.exactCore3 z J, ⁅r, tA⁆ ∈ oddCoreOf (Q3NL.exactLayer3 Ω z)) :
    alphaOf (Subgroup.closure ({tJ, z} : Set G)) =
      alphaOf (Subgroup.closure ({tA, z} : Set G)) := by
  have hΩ : HypOmegaMod Ω := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hs.hyp
  obtain ⟨o, hoO, hA'K, hA'inv, hcase⟩ := exists_conj_adjacent hΩ hnt hK hz hJ hA htJ htA hcomm
  have hoN : conjSub o (alphaOf (Subgroup.closure ({tA, z} : Set G))) =
      alphaOf (Subgroup.closure ({tA, z} : Set G)) := mem_normalizer_iff_conjSub_eq.mp (hOn hoO)
  have hoz : o * z * o⁻¹ = z := by
    have : o ∈ Subgroup.centralizer ({z} : Set G) :=
      Q3NL.exactLayer3_le_centralizer Ω z (oddCoreOf_le_self _ hoO)
    have h := Subgroup.mem_centralizer_singleton_iff.mp this
    rw [mul_inv_eq_iff_eq_mul]
    exact h
  have hαA' : alphaOf (Subgroup.closure ({o * tA * o⁻¹, z} : Set G)) =
      alphaOf (Subgroup.closure ({tA, z} : Set G)) := by
    have h1 : Subgroup.closure ({o * tA * o⁻¹, z} : Set G) =
        conjSub o (Subgroup.closure ({tA, z} : Set G)) := by
      rw [conjSub_closure_pair, hoz]
    rw [h1, alphaOf_conjSub]
    exact hoN
  have hA'Ω : conjSub o A ∈ Ω := hΩ.conjInvariant o A hA.1
  rcases hcase with hAJ | ⟨hA'J, hJA'⟩
  · have : tJ = o * tA * o⁻¹ := htJ.eq (hAJ ▸ hA'inv)
    rw [this]
    exact hαA'
  · have hzt : z * tJ = tJ * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hJ htJ
    have hzt'' : z * (o * tA * o⁻¹) = (o * tA * o⁻¹) * z :=
      Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hz hA'K hA'inv
    by_cases hdeg : o * tA * o⁻¹ ∈ Subgroup.closure ({z, tJ} : Set G)
    · rcases T3CII.closure_pair_cases hz.sq htJ.sq hzt hdeg with h | h | h | h
      · exact absurd h hA'inv.ne_one
      · exact absurd (hnt K hK _ ⟨hA'Ω, z, hz, h ▸ hA'inv⟩) hA'K.2.1
      · exact absurd (hnt J hJ.1 _ ⟨hA'Ω, tJ, htJ, h ▸ hA'inv⟩) hA'J.2.1
      · rw [← hαA', h, closure_pair_mul_left hz.sq]
    · obtain ⟨hbal, -⟩ := alpha_of_triangle hs hnt hK hz htJ hA'inv hJ hA'K hA'J hdeg
      have hle : Subgroup.closure ({o * tA * o⁻¹, z} : Set G) ≤
          Subgroup.closure ({z, tJ, o * tA * o⁻¹} : Set G) := by
        apply Subgroup.closure_mono
        intro y hy
        rcases hy with rfl | rfl <;> simp
      have hne : o * tA * o⁻¹ ≠ z := fun h => by
        exact hA'K.2.1 (hnt K hK _ ⟨hA'Ω, z, hz, h ▸ hA'inv⟩)
      have hab : IsElemAbelian2 (Subgroup.closure ({o * tA * o⁻¹, z} : Set G)) 2 :=
        T7A.isElemAbelian2_closure_pair hA'inv.sq hz.sq hA'inv.ne_one hz.ne_one hne hzt''.symm
      rw [← hαA', hbal _ hle hab]

end Transfer

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
