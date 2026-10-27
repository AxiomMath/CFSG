module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Tools46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46R3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsFieldW

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoIn_of_le_of_sylow {S H : Subgroup G}
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (hSH : S ≤ H) : IsSylowTwoIn S H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, rfl⟩ := hSyl
  exact isSylowTwoIn_of_not_dvd hSH P.isPGroup' fun hd =>
    P.not_dvd_index (hd.trans (relIndex_dvd_index_of_le hSH))

omit [Finite G] in
theorem mem_normalizer_of_wGroup_eq {W A : Subgroup G} {g : G} (hA : wGroup A = W)
    (hAg : wGroup (A.map (MulAut.conj g⁻¹).toMonoidHom) = W) : g ∈ normalizer (W : Set G) := by
  rw [wGroup_map_conj, hA] at hAg
  have h := inv_mem (mem_normalizer_iff_map_conj_eq.mpr hAg)
  rwa [inv_inv] at h

theorem isAbelianTwoOfRank_of_eight {E : Subgroup G} (hE : IsEightGroup E) :
    IsAbelianTwoOfRank 3 E :=
  ⟨hE.1.isPGroup, hE.1.1, le_pRank_of_isElemTwo le_rfl hE.1 (k := 3) (by rw [hE.2]; norm_num)⟩

theorem wGroup_eq_of_eight_le (hConn : L34EightsConnectedFact) (hU : L34UnbalancingUnitaryStep)
    (hC : L34UnitaryCentralizerFact) {a x : G} {J S W : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hexp : Monoid.exponent ↥(S ⊓ zStarIn J) = 4)
    (hnc : ¬ IsCyclic ↥(S ⊓ zStarIn J))
    (hWx : wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {E : Subgroup G} (hEJ : E ≤ J)
    (hE8 : IsEightGroup E) : wGroup E = W := by
  obtain ⟨hbase, hU3, hL34, -, hS, -, hxS⟩ := id hset
  have hGW : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hbase.2.2.2.2.2.1
  have hJ : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hU3.2.2.2.1 hU3.2.2.2.2.1
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [inf_assoc, inf_of_le_right (show zStarIn J ≤ J from map_subtype_le _)]
  have hxP : x ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    inf_mem_normalizer (le_normalizer hxS) (hS.1 hxS)
  obtain ⟨-, h8, -, -, -, hel, -, -⟩ := hC G J (S ⊓ J) x hJ hL34 (hU G a x J hU3 hL34) hP hxP
  have hR : IsEightGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) := ⟨hel (by rwa [hZP]), h8⟩
  have hz4 : ∃ z ∈ S ⊓ J ⊓ zStarIn J, z * z ≠ 1 := by
    rw [hZP]
    exact exists_sq_ne_one_of_exponent_eq_four hexp
  exact wGroup_eq_of_le_of_connected hGW hP hWx (le_normalizer.trans hNJ) (fun F hF hF8 =>
    hConn G J (S ⊓ J) hJ hL34 hP (by rwa [hZP]) hz4 _ F inf_le_left hF hR hF8) hEJ hE8

theorem exists_eight_le_centralizer (hSqC : L34SquareCenterFact)
    (hWit : L34OuterWitnessFact) {J S : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hS : IsSylowTwoIn S (normalizer (J : Set G)))
    (hnc : ¬ IsCyclic ↥(S ⊓ zStarIn J)) {V₀ : Subgroup G} (hV₀Z : V₀ ≤ S ⊓ zStarIn J)
    (hV₀ : IsElemTwo V₀) (hV₀4 : Nat.card V₀ = 4) {t : G} (htS : t ∈ S) (htt : t * t = 1)
    (htV : ∀ v ∈ V₀, v * t = t * v) :
    ∃ E : Subgroup G, V₀ ≤ E ∧ E ≤ S ⊓ J ⊓ centralizer ({t} : Set G) ∧ IsEightGroup E := by
  have hP : IsSylowTwoIn (S ⊓ J) J := isSylowTwoIn_inf hS
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hzK : ∀ {z : G}, z ∈ zStarIn J → z ∈ coreActionKernel J := fun hz => by
    have h : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
    rw [h] at hz
    exact (mem_inf.mp hz).2
  obtain ⟨e, heP, hee, het, heV⟩ : ∃ e ∈ S ⊓ J, e * e = 1 ∧ e * t = t * e ∧ e ∉ V₀ := by
    by_cases htK : t ∈ withKernel J
    · obtain ⟨F, hF, hFe, hF8⟩ := exists_isElemTwo_of_three_le_pRank
        (three_le_pRank_centralizer_of_mem_withKernel hSqC hJ hL hS hnc htS htK htt)
      by_contra hno
      push Not at hno
      have hFV : F ≤ V₀ := fun y hy => by
        obtain ⟨hyP, hyt⟩ := mem_inf.mp (hF hy)
        exact hno y hyP (hFe.2 y hy) (mem_centralizer_singleton_iff.mp hyt)
      have h1 := card_le_of_le hFV
      omega
    · obtain ⟨w, hwP, hww, hwt, hwZ⟩ := hWit G J (S ⊓ J) t hJ hL hP (hS.1 htS)
        (inf_mem_normalizer (le_normalizer htS) (hS.1 htS)) htt htK
      exact ⟨w, hwP, hww, hwt, fun h => hwZ (mem_inf.mp (hV₀Z h)).2⟩
  have heV₀ : ∀ v ∈ V₀, v * e = e * v := fun v hv =>
    mul_comm_of_mem_coreActionKernel hS2 (mem_inf.mp (hV₀Z hv)).1 (hzK (mem_inf.mp (hV₀Z hv)).2)
      (mem_inf.mp heP).1 (mem_inf.mp heP).2
  obtain ⟨hE, hEc⟩ := isElemTwo_sup_zpowers hV₀ hee heV heV₀
  refine ⟨V₀ ⊔ zpowers e, le_sup_left, sup_le (fun v hv => ?_) (zpowers_le.mpr ?_),
    ⟨hE, by rw [hEc, hV₀4]⟩⟩
  · obtain ⟨hvS, hvZ⟩ := mem_inf.mp (hV₀Z hv)
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hvS, map_subtype_le _ hvZ⟩,
      mem_centralizer_singleton_iff.mpr (htV v hv)⟩
  · exact mem_inf.mpr ⟨heP, mem_centralizer_singleton_iff.mpr het⟩

theorem wGroup_eq_of_centralizes (hGW : GWTwoBalanced G) {J S W V₀ : Subgroup G}
    (hWE : ∀ E : Subgroup G, E ≤ J → IsEightGroup E → wGroup E = W)
    (hT : ∀ t ∈ S, t * t = 1 → (∀ v ∈ V₀, v * t = t * v) →
      ∃ E : Subgroup G, V₀ ≤ E ∧ E ≤ S ⊓ J ⊓ centralizer ({t} : Set G) ∧ IsEightGroup E)
    (hV₀ : IsElemTwo V₀) (hV₀4 : Nat.card V₀ = 4) {A : Subgroup G} (hAS : A ≤ S)
    (hA : IsAbelianTwoOfRank 3 A) (hAV : ∀ y ∈ A, ∀ v ∈ V₀, v * y = y * v) : wGroup A = W := by
  obtain ⟨F₀, hF₀A, hF₀, hF₀8⟩ := exists_isElemTwo_eight hA
  obtain ⟨t, htF₀, htV⟩ : ∃ t ∈ F₀, t ∉ V₀ := by
    by_contra hno
    push Not at hno
    have h1 := card_le_of_le (show F₀ ≤ V₀ from hno)
    omega
  have htt : t * t = 1 := hF₀.2 t htF₀
  have htA : t ∈ A := hF₀A htF₀
  obtain ⟨hF, hFc⟩ := isElemTwo_sup_zpowers hV₀ htt htV fun v hv => hAV t htA v hv
  have hF8 : IsEightGroup (V₀ ⊔ zpowers t) := ⟨hF, by rw [hFc, hV₀4]⟩
  obtain ⟨E, hVE, hES, hE8⟩ := hT t (hAS htA) htt fun v hv => hAV t htA v hv
  have hAF : ∀ y ∈ A, ∀ z ∈ V₀ ⊔ zpowers t, y * z = z * y := by
    intro y hy z hz
    have hle : V₀ ⊔ zpowers t ≤ centralizer ({y} : Set G) := sup_le
      (fun v hv => mem_centralizer_singleton_iff.mpr (hAV y hy v hv))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hA.2.1 t htA y hy)))
    exact (mem_centralizer_singleton_iff.mp (hle hz)).symm
  have hFE : ∀ z ∈ V₀ ⊔ zpowers t, ∀ e ∈ E, z * e = e * z := by
    intro z hz e he
    have hle : V₀ ⊔ zpowers t ≤ centralizer ({e} : Set G) := sup_le
      (fun v hv => mem_centralizer_singleton_iff.mpr (hE8.1.1 v (hVE hv) e he))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (mem_inf.mp (hES he)).2).symm))
    exact mem_centralizer_singleton_iff.mp (hle hz)
  rw [wGroup_eq_of_commute hGW hA (isAbelianTwoOfRank_of_eight hF8) hAF,
    wGroup_eq_of_commute hGW (isAbelianTwoOfRank_of_eight hF8) (isAbelianTwoOfRank_of_eight hE8)
      hFE]
  exact hWE E ((hES.trans inf_le_left).trans inf_le_right) hE8

theorem exists_eight_le_inf_centralizer {A : Subgroup G} (hA : IsElemTwo A)
    (h16 : Nat.card A = 16) {a f : G} (hff : f * f = 1) (hAa : ∀ s ∈ A, s * a = a * s)
    (hAf : ∀ s ∈ A, s * f * s⁻¹ = f ∨ s * f * s⁻¹ = a * f) :
    ∃ X : Subgroup G, X ≤ A ⊓ centralizer ({f} : Set G) ∧ IsEightGroup X := by
  have hc : ∀ s ∈ A, (s * f * s⁻¹ * f = 1) ∨ (s * f * s⁻¹ * f = a) := fun s hs => by
    rcases hAf s hs with h | h
    · left; rw [h, hff]
    · right; rw [h, mul_assoc, hff, mul_one]
  have hca : ∀ s ∈ A, ∀ y : G, y = 1 ∨ y = a →
      (s * f * s⁻¹ * f) * y = y * (s * f * s⁻¹ * f) := by
    intro s hs y hy
    rcases hy with rfl | rfl
    · group
    · rcases hc s hs with h | h <;> rw [h]; group
  let c : ↥A →* G :=
    { toFun := fun s => (s : G) * f * (s : G)⁻¹ * f
      map_one' := by simp [hff]
      map_mul' := fun s t => by
        show (s : G) * t * f * ((s : G) * t)⁻¹ * f =
          ((s : G) * f * (s : G)⁻¹ * f) * ((t : G) * f * (t : G)⁻¹ * f)
        have e1 : (s : G) * t * f * ((s : G) * t)⁻¹ * f =
            (s : G) * ((t : G) * f * (t : G)⁻¹) * (s : G)⁻¹ * f := by group
        rw [e1]
        rcases hAf t t.2 with h | h
        · rw [h, hff, mul_one]
        · have e2 : (s : G) * (a * f) * (s : G)⁻¹ * f =
              a * ((s : G) * f * (s : G)⁻¹ * f) := by
            rw [← mul_assoc (s : G) a f, hAa s s.2]; group
          rw [h, e2, show a * f * f = a by rw [mul_assoc, hff, mul_one]]
          exact (hca s s.2 a (Or.inr rfl)).symm }
  have hker : ∀ s : ↥A, s ∈ c.ker ↔ (s : G) * f = f * s := fun s => by
    rw [MonoidHom.mem_ker]
    show (s : G) * f * (s : G)⁻¹ * f = 1 ↔ _
    constructor
    · intro h
      calc (s : G) * f = (s : G) * f * (s : G)⁻¹ * f * f * s := by
            rw [mul_assoc _ f f, hff]; group
        _ = f * s := by rw [h]; group
    · intro h
      rw [h, mul_inv_cancel_right, hff]
  have hrange : Nat.card c.range ≤ 2 := by
    have hsub : (c.range : Set G) ⊆ ({1, a} : Set G) := by
      rintro _ ⟨s, rfl⟩
      rcases hc s s.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Nat.card c.range = Nat.card (c.range : Set G) := rfl
      _ ≤ Nat.card ({1, a} : Set G) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hcard : 8 ≤ Nat.card c.ker := by
    have h1 := c.ker.card_mul_index
    rw [Subgroup.index_ker, h16] at h1
    have h2 : Nat.card c.range ≠ 0 := Nat.card_pos.ne'
    by_contra h
    push Not at h
    have : Nat.card c.ker * Nat.card c.range ≤ 7 * 2 :=
      Nat.mul_le_mul (by omega) hrange
    omega
  set X₀ : Subgroup G := c.ker.map A.subtype with hX₀
  have hX₀A : X₀ ≤ A ⊓ centralizer ({f} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_inf.mpr ⟨s.2, mem_centralizer_singleton_iff.mpr ((hker s).mp hs)⟩
  have hX₀c : Nat.card X₀ = Nat.card c.ker := by
    rw [hX₀, card_map_of_injective A.subtype_injective]
  have hX₀e : IsElemTwo X₀ := hA.mono (hX₀A.trans inf_le_left)
  obtain ⟨X, hXX₀, hX8⟩ := exists_le_card_eight hX₀e.isPGroup (by rw [hX₀c]; exact hcard)
  exact ⟨X, hXX₀.trans hX₀A, hX₀e.mono hXX₀, hX8⟩

theorem wGroup_eq_of_sixteen (hGW : GWTwoBalanced G) {S W : Subgroup G} {a f : G}
    (hW : ∀ B : Subgroup G, B ≤ S → IsAbelianTwoOfRank 3 B →
      (∀ y ∈ B, ∀ v ∈ zpowers a ⊔ zpowers f, v * y = y * v) → wGroup B = W)
    (hSa : ∀ s ∈ S, s * a = a * s) (hff : f * f = 1)
    (hSf : ∀ s ∈ S, s * f * s⁻¹ = f ∨ s * f * s⁻¹ = a * f) {A : Subgroup G} (hAS : A ≤ S)
    (hA : IsElemTwo A) (h16 : Nat.card A = 16) : wGroup A = W := by
  obtain ⟨X, hXA, hX8⟩ := exists_eight_le_inf_centralizer hA h16 hff
    (fun s hs => hSa s (hAS hs)) (fun s hs => hSf s (hAS hs))
  have hXV : ∀ y ∈ X, ∀ v ∈ zpowers a ⊔ zpowers f, v * y = y * v := by
    intro y hy v hv
    have hle : zpowers a ⊔ zpowers f ≤ centralizer ({y} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (hSa y (hAS (mem_inf.mp (hXA hy)).1)).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp (mem_inf.mp (hXA hy)).2).symm))
    exact mem_centralizer_singleton_iff.mp (hle hv)
  rw [wGroup_eq_of_le_eight hGW hA (hXA.trans inf_le_left) hX8.2]
  exact hW X ((hXA.trans inf_le_left).trans hAS) (isAbelianTwoOfRank_of_eight hX8) hXV

end CFSG.ComponentClassification.GrSLit.GrS4
