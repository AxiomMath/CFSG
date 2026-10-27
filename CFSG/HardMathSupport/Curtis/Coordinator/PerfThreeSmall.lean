module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchGlue
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIVOut
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoUThree
import CFSG.HardMathSupport.Curtis.Coordinator.ToralThreeReduce
import CFSG.HardMathSupport.Curtis.Proving.NineDvdCentralizer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertA5Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even6Inputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Equiv CFSG.AGLEmbedding CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
  CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private def NineAvoid (S : Type) [Group S] : Prop :=
  9 ∣ Nat.card S ∧ ∀ (T : Sylow 2 S) (J : Subgroup S), (T : Subgroup S) ≤ J → J ≠ ⊤ →
    ¬ 9 ∣ Nat.card J

private def NormalizerMax (S : Type) [Group S] : Prop :=
  ∀ (T : Sylow 2 S) (J : Subgroup S), Subgroup.normalizer ((T : Subgroup S) : Set S) ≤ J →
    J ≠ ⊤ → J ≤ Subgroup.normalizer ((T : Subgroup S) : Set S)

private theorem map_ne_top {S S' : Type} [Group S] [Group S'] [Finite S] (φ : S ≃* S')
    {J : Subgroup S} (hJ : J ≠ ⊤) : J.map φ.toMonoidHom ≠ ⊤ := by
  intro htop
  apply hJ
  refine Subgroup.eq_top_of_card_eq J ?_
  have h2 : Nat.card (J.map φ.toMonoidHom) = Nat.card S' := by
    rw [htop, Subgroup.card_top]
  rw [Subgroup.card_map_of_injective φ.injective] at h2
  rw [h2]
  exact Nat.card_congr φ.toEquiv.symm

private theorem NineAvoid.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Sylow 2 S)
    (h9 : 9 ∣ Nat.card S)
    (h : ∀ J : Subgroup S, (T₀ : Subgroup S) ≤ J → J ≠ ⊤ → ¬ 9 ∣ Nat.card J) : NineAvoid S := by
  refine ⟨h9, fun T J hTJ hJ => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S T T₀
  set φ : S ≃* S := MulAut.conj g with hφ
  have hT : (T₀ : Subgroup S) = (T : Subgroup S).map φ.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have := h (J.map φ.toMonoidHom) (hT ▸ Subgroup.map_mono hTJ) (map_ne_top φ hJ)
  rwa [Subgroup.card_map_of_injective φ.injective] at this

private theorem NineAvoid.of_mulEquiv {S S' : Type} [Group S] [Group S'] [Finite S] (e : S ≃* S')
    (h : NineAvoid S) : NineAvoid S' := by
  have : Finite S' := Finite.of_equiv S e.toEquiv
  refine ⟨?_, fun T' J' hTJ hJ' => ?_⟩
  · rw [← Nat.card_congr e.toEquiv]
    exact h.1
  · set T : Sylow 2 S := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T'
    have hT : (T : Subgroup S) = (T' : Subgroup S').map e.symm.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    have := h.2 T (J'.map e.symm.toMonoidHom) (hT ▸ Subgroup.map_mono hTJ)
      (map_ne_top e.symm hJ')
    rwa [Subgroup.card_map_of_injective e.symm.injective] at this

private theorem NormalizerMax.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Sylow 2 S)
    (h : ∀ J : Subgroup S, Subgroup.normalizer ((T₀ : Subgroup S) : Set S) ≤ J → J ≠ ⊤ →
      J ≤ Subgroup.normalizer ((T₀ : Subgroup S) : Set S)) : NormalizerMax S := by
  intro T J hNJ hJ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S T T₀
  set φ : S ≃* S := MulAut.conj g with hφ
  have hT : (T₀ : Subgroup S) = (T : Subgroup S).map φ.toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hN : Subgroup.normalizer ((T₀ : Subgroup S) : Set S) =
      (Subgroup.normalizer ((T : Subgroup S) : Set S)).map φ.toMonoidHom := by
    rw [hT]
    exact (Subgroup.map_equiv_normalizer_eq _ φ).symm
  have h1 := h (J.map φ.toMonoidHom) (by rw [hN]; exact Subgroup.map_mono hNJ) (map_ne_top φ hJ)
  rw [hN] at h1
  exact (Subgroup.map_le_map_iff_of_injective φ.injective).1 h1

private theorem NormalizerMax.of_mulEquiv {S S' : Type} [Group S] [Group S'] [Finite S]
    (e : S ≃* S') (h : NormalizerMax S) : NormalizerMax S' := by
  have : Finite S' := Finite.of_equiv S e.toEquiv
  intro T' J' hNJ hJ'
  set T : Sylow 2 S := Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective T'
  have hT : (T : Subgroup S) = (T' : Subgroup S').map e.symm.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hN : Subgroup.normalizer ((T : Subgroup S) : Set S) =
      (Subgroup.normalizer ((T' : Subgroup S') : Set S')).map e.symm.toMonoidHom := by
    rw [hT]
    exact (Subgroup.map_equiv_normalizer_eq _ e.symm).symm
  have h1 := h T (J'.map e.symm.toMonoidHom) (by rw [hN]; exact Subgroup.map_mono hNJ)
    (map_ne_top e.symm hJ')
  rw [hN] at h1
  exact (Subgroup.map_le_map_iff_of_injective e.symm.injective).1 h1

private theorem latCert_data {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A) (hc : c.check RN.enc = true) :
    (∀ Y : Subgroup ↥A, (Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A ≤ Y →
      Nat.card Y ∈ c.sizes) ∧ Nat.card ↥A = c.msize ∧
    Nat.card ((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A) = c.sizes.headD 0 := by
  subst hM
  have hcl := c.closedOK_of_check hc
  have hszOK := c.sizesOK_of_check hc
  refine ⟨fun Y hY => ?_, c.card_m (rawIsEnc n) hcl hszOK, ?_⟩
  · obtain ⟨L, -, hLM, hYL, hL⟩ := c.overgroup_cases (rawIsEnc n) hc Y hY
    rw [hYL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
    exact hL
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv,
      c.card_t (rawIsEnc n) hcl hszOK]

private theorem not_two_dvd_index_of_isSylowTwoOf {S : Type} [Group S] {T : Subgroup S}
    (h : IsSylowTwoOf T ⊤) : ¬ 2 ∣ T.index := by
  have h2 := h.2.2
  rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h2

private theorem nineAvoid_alt_six :
    NineAvoid ↥(alternatingGroup (Fin 6)) := by
  obtain ⟨hmem, hcardA, -⟩ := latCert_data Even6.cert Even6.closure_mGens Even6.D_le
    Even6.cert_check
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := Even6.isSylow_D
  refine NineAvoid.of_sylow (hs.2.1.toSylow (not_two_dvd_index_of_isSylowTwoOf hs))
    (by rw [hcardA]; decide) fun J hJ hne => ?_
  have hJ' := hmem J hJ
  have h360 : Nat.card J ≠ Nat.card ↥(alternatingGroup (Fin 6)) := fun h =>
    hne (Subgroup.eq_top_of_card_eq J h)
  rw [hcardA] at h360
  change Nat.card J ∈ ([8, 24, 24, 360] : List ℕ) at hJ'
  change Nat.card J ≠ 360 at h360
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ'
  omega

private theorem nineAvoid_u33 :
    NineAvoid ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup := by
  obtain ⟨hmem, hcardA, -⟩ := latCert_data CertU33.cert CertU33.closure_mGens CertU33.D_le
    CertU33.cert_check
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := CertU33.isSylow_D
  refine NineAvoid.of_sylow (hs.2.1.toSylow (not_two_dvd_index_of_isSylowTwoOf hs))
    (by rw [hcardA]; decide) fun J hJ hne => ?_
  have hJ' := hmem J hJ
  have h360 : Nat.card J ≠ Nat.card ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup := fun h =>
    hne (Subgroup.eq_top_of_card_eq J h)
  rw [hcardA] at h360
  change Nat.card J ∈ ([32, 96, 96, 6048] : List ℕ) at hJ'
  change Nat.card J ≠ 6048 at h360
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJ'
  omega

private theorem normalizerMax_alt_five :
    NormalizerMax ↥(alternatingGroup (Fin 5)) := by
  obtain ⟨hmem, hcardA, hcardT⟩ := latCert_data CertA5.cert CertA5.closure_mGens CertA5.D_le
    CertA5.cert_check
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := CertA5.isSylow_D
  refine NormalizerMax.of_sylow (hs.2.1.toSylow (not_two_dvd_index_of_isSylowTwoOf hs))
    fun J hNJ hne => ?_
  set T₀ : Subgroup ↥(alternatingGroup (Fin 5)) :=
    CertA5.D.subgroupOf (alternatingGroup (Fin 5)) with hT₀
  change Subgroup.normalizer (T₀ : Set _) ≤ J at hNJ
  change J ≤ Subgroup.normalizer (T₀ : Set _)
  set N := Subgroup.normalizer (T₀ : Set ↥(alternatingGroup (Fin 5))) with hN
  have hT₀N : T₀ ≤ N := Subgroup.le_normalizer
  have hcT : Nat.card T₀ = 4 := hcardT
  have hJc := hmem J (hT₀N.trans hNJ)
  have hNc := hmem N hT₀N
  change Nat.card J ∈ ([4, 12, 60] : List ℕ) at hJc
  change Nat.card N ∈ ([4, 12, 60] : List ℕ) at hNc
  have h60 : Nat.card J ≠ Nat.card ↥(alternatingGroup (Fin 5)) := fun h =>
    hne (Subgroup.eq_top_of_card_eq J h)
  rw [hcardA] at h60
  change Nat.card J ≠ 60 at h60
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hJc hNc
  have hle := Subgroup.card_le_of_le hNJ
  set t₁ : Perm (Fin 5) := permOf 5 [[1, 2], [3, 4]] with ht₁
  set t₂ : Perm (Fin 5) := permOf 5 [[1, 3], [2, 4]] with ht₂
  set x : Perm (Fin 5) := permOf 5 [[2, 3, 4]] with hx
  have hxA : x ∈ alternatingGroup (Fin 5) := Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have h1 : x * t₁ * x⁻¹ = t₂ := by decide
  have h2 : x * t₂ * x⁻¹ = t₁ * t₂ := by decide
  have h3 : x⁻¹ * t₁ * x = t₁ * t₂ := by decide
  have h4 : x⁻¹ * t₂ * x = t₁ := by decide
  have hD1 : t₁ ∈ CertA5.D := Subgroup.subset_closure (by simp [CertA5.tGens, ht₁])
  have hD2 : t₂ ∈ CertA5.D := Subgroup.subset_closure (by simp [CertA5.tGens, ht₂])
  have hfw : ∀ y ∈ CertA5.D, x * y * x⁻¹ ∈ CertA5.D := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      simp only [CertA5.tGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl
      · rw [h1]; exact hD2
      · rw [h2]; exact Subgroup.mul_mem _ hD1 hD2
    | one => simp
    | mul a b _ _ ha hb =>
      have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  have hbw : ∀ y ∈ CertA5.D, x⁻¹ * y * x ∈ CertA5.D := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      simp only [CertA5.tGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl
      · rw [h3]; exact Subgroup.mul_mem _ hD1 hD2
      · rw [h4]; exact hD1
    | one => simp
    | mul a b _ _ ha hb =>
      have : x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
      rw [this]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      have : x⁻¹ * a⁻¹ * x = (x⁻¹ * a * x)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ ha
  have hxN : x ∈ Subgroup.normalizer (CertA5.D : Set (Perm (Fin 5))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfw y, fun hy => ?_⟩
    have := hbw _ hy
    simpa [mul_assoc] using this
  have hDle : CertA5.D ≤ (alternatingGroup (Fin 5)).subtype.range := by
    rw [Subgroup.range_subtype]
    exact CertA5.D_le
  have hx'N : (⟨x, hxA⟩ : ↥(alternatingGroup (Fin 5))) ∈ N := by
    have : (⟨x, hxA⟩ : ↥(alternatingGroup (Fin 5))) ∈
        (Subgroup.normalizer (CertA5.D : Set (Perm (Fin 5)))).comap
          (alternatingGroup (Fin 5)).subtype := hxN
    rw [Subgroup.comap_normalizer_eq_of_le_range hDle] at this
    exact this
  have hx'T : (⟨x, hxA⟩ : ↥(alternatingGroup (Fin 5))) ∉ T₀ := by
    intro hxT
    have h4' : (⟨⟨x, hxA⟩, hxT⟩ : T₀) ^ Nat.card T₀ = 1 := pow_card_eq_one'
    rw [hcT] at h4'
    have h4'' : (x : Perm (Fin 5)) ^ 4 = 1 := by
      have := congrArg (fun z : T₀ => ((z : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5))) h4'
      simpa using this
    have h3'' : (x : Perm (Fin 5)) ^ 3 = 1 := by decide
    have hx1 : x = 1 := by
      calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4'', h3'']; simp
    exact absurd hx1 (by decide)
  have hNT : N ≠ T₀ := fun h => hx'T (h ▸ hx'N)
  have hN4 : Nat.card N ≠ 4 := fun h =>
    hNT (Subgroup.eq_of_le_of_card_ge hT₀N (by rw [h, hcT])).symm
  have hNJc : Nat.card J = Nat.card N := by omega
  exact (Subgroup.eq_of_le_of_card_ge hNJ hNJc.le).ge

private theorem exists_mul_of_mem_sup {Y : Type} [Group Y] {L : Subgroup Y} {u : Y}
    (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y)) :
    ∃ l ∈ L, ∃ c ∈ Subgroup.centralizer (L : Set Y), u = l * c := by
  have hCN : L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) :=
    CFSG.AGLEmbedding.ToralCensus.le_normalizer_centralizer L
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at hu
  obtain ⟨l, hl, c, hc, rfl⟩ := hu
  exact ⟨l, hl, c, hc, rfl⟩

private theorem exists_sylow_of_compParab {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hP : CompParab L J) :
    ∃ T : Subgroup Y, IsSylowTwoOf T L ∧ L ⊓ Subgroup.normalizer (T : Set Y) ≤ J := by
  obtain ⟨T, hT, hTJ⟩ := hP.parab.2
  exact ⟨T, hT, hTJ⟩

private theorem sylow_subgroupOf {Y : Type} [Group Y] {L T : Subgroup Y} (hT : IsSylowTwoOf T L) :
    IsPGroup 2 (T.subgroupOf L) ∧ ¬ 2 ∣ (T.subgroupOf L).index :=
  ⟨hT.2.1.comap_of_injective L.subtype L.subtype_injective, hT.2.2⟩

private theorem false_of_nineAvoid {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {u : Y}
    (hH : FixPerfThreeHyp L J u) (hu : u ∈ L ⊔ Subgroup.centralizer (L : Set Y))
    (hZ : Subgroup.center ↥L = ⊥) {S : Type} [Group S] [Finite S] (e : ↥L ≃* S)
    (hS : NineAvoid S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup hu
  have hlc : Commute l c := (Subgroup.mem_centralizer_iff.mp hc) l hl
  have hu3 := hH.pow
  have hl3 : l ^ 3 = 1 := by
    have h1 : l ^ 3 * c ^ 3 = 1 := by rw [← hlc.mul_pow]; exact hu3
    have hcen : (⟨l ^ 3, Subgroup.pow_mem _ hl 3⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hc3 : c ^ 3 ∈ Subgroup.centralizer (L : Set Y) := Subgroup.pow_mem _ hc 3
      have hl3c : l ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
      apply Subtype.ext
      change (g : Y) * l ^ 3 = l ^ 3 * g
      rw [hl3c]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hc3)) g g.2
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hl1 : l ≠ 1 := by
    rintro rfl
    have h1 := hH.not_mem
    rw [one_mul] at h1
    exact h1 hc
  set l' : ↥L := ⟨l, hl⟩
  have hl'3 : orderOf l' = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using hl3)
    · intro h
      exact hl1 (congrArg Subtype.val h)
  have h9L : 9 ∣ Nat.card ↥L := by
    rw [Nat.card_congr e.toEquiv]
    exact hS.1
  have hC9 := CFSG.HardMathSupport.Curtis.Proving.nine_dvd_card_centralizer_of_orderOf_eq_three
    h9L hl'3
  obtain ⟨T, hT, hTJ⟩ := exists_sylow_of_compParab hH.parab
  have hJL : J ≤ L := hH.parab.parab.1
  have hmap : Subgroup.centralizer ({l'} : Set ↥L) ≤ J.subgroupOf L := by
    intro x hx
    refine hH.fix x x.2 ?_
    have hxl : x * l' = l' * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hxl' : (x : Y) * l = l * x := congrArg Subtype.val hxl
    have hxc : (x : Y) * c = c * x := (Subgroup.mem_centralizer_iff.mp hc) x x.2
    change l * c * (x : Y) * (l * c)⁻¹ = x
    calc l * c * (x : Y) * (l * c)⁻¹
        = l * (c * x) * c⁻¹ * l⁻¹ := by group
      _ = l * (x * c) * c⁻¹ * l⁻¹ := by rw [hxc]
      _ = (l * x) * l⁻¹ := by group
      _ = (x * l) * l⁻¹ := by rw [hxl']
      _ = x := by group
  have h9J : 9 ∣ Nat.card (J.subgroupOf L) := hC9.trans (Subgroup.card_dvd_of_le hmap)
  obtain ⟨hT2, hTi⟩ := sylow_subgroupOf hT
  have hTJ' : T.subgroupOf L ≤ J.subgroupOf L := by
    intro t ht
    exact hTJ ⟨t.2, Subgroup.le_normalizer ht⟩
  have hJne : J.subgroupOf L ≠ ⊤ := by
    intro h
    exact hH.parab.ne_top (le_antisymm hJL (Subgroup.subgroupOf_eq_top.1 h))
  have : Finite ↥L := inferInstance
  exact (NineAvoid.of_mulEquiv e.symm hS).2 (hT2.toSylow hTi) _ hTJ' hJne h9J

private theorem false_of_normalizerMax {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} {u : Y}
    (hH : FixPerfThreeHyp L J u) {S : Type} [Group S] [Finite S] (e : ↥L ≃* S)
    (hS : NormalizerMax S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTJ⟩ := exists_sylow_of_compParab hH.parab
  have hJL : J ≤ L := hH.parab.parab.1
  obtain ⟨hT2, hTi⟩ := sylow_subgroupOf hT
  have hTr : T ≤ L.subtype.range := by rw [Subgroup.range_subtype]; exact hT.1
  have hNJ' : Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) ≤ J.subgroupOf L := by
    rw [Subgroup.subgroupOf, ← Subgroup.comap_normalizer_eq_of_le_range hTr]
    intro x hx
    exact hTJ ⟨x.2, hx⟩
  have hJne : J.subgroupOf L ≠ ⊤ := by
    intro h
    exact hH.parab.ne_top (le_antisymm hJL (Subgroup.subgroupOf_eq_top.1 h))
  have hle := (NormalizerMax.of_mulEquiv e.symm hS) (hT2.toSylow hTi) _ hNJ' hJne
  apply hH.parab.ne_borel T hT
  refine le_antisymm (fun j hj => ⟨hJL hj, ?_⟩) hTJ
  have hj' : (⟨j, hJL hj⟩ : ↥L) ∈ Subgroup.normalizer ((T.subgroupOf L : Subgroup ↥L) : Set ↥L) :=
    hle hj
  rw [Subgroup.subgroupOf, ← Subgroup.comap_normalizer_eq_of_le_range hTr] at hj'
  exact hj'

private theorem not_three_dvd_card_outer_of_small {X : Type} [Group X] [Group.IsPerfect X]
    [Nontrivial (X ⧸ Subgroup.center X)] (hS : IsSmallTwoOrG2 (X ⧸ Subgroup.center X)) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
  · exact not_three_dvd_card_outer_of_center_alt e
  · have hc := statedClassicalModel_psl_two_seven ⟨q, hq7, hdq⟩ e
    exact fun h3 => not_three_dvd_card_outer_of_psl_seven hc
      (h3.trans (card_outer_dvd_card_outer_centerQuotient X))
  · obtain ⟨dd, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨hp, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_three hq3
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hf] at h
    have hout := card_outer_eq_two_of_model_psu_three_three h
    intro h3
    have h32 := h3.trans (card_outer_dvd_card_outer_centerQuotient X)
    rw [hout] at h32
    omega

theorem fixPerfThreeSmall
    (hZ : OddCenterRest) : FixPerfThreeSmall := by
  intro Y _ _ L J u hH hS
  have hcomp := hH.parab.comp
  have hodd := hH.parab.odd
  have hq : CFSG.Open.IsQuasisimple ↥L := hcomp.2.2
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  have : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
  have hinner : u ∈ L ⊔ Subgroup.centralizer (L : Set Y) :=
    mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three
      (not_three_dvd_card_outer_of_small hS) hH.norm (by rw [pow_one]; exact hH.pow)
  refine ⟨hinner, ?_⟩
  rcases hZ Y L hcomp hodd (Or.inr (Or.inr (Or.inr (Or.inr hS)))) with hZ1 | ⟨hZ3, ⟨e6⟩⟩
  · have hZbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ1
    have eZ : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot
    rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
    · rcases hn with rfl | rfl | rfl
      · exact (false_of_normalizerMax hH (eZ.symm.trans e) normalizerMax_alt_five).elim
      · exact (false_of_nineAvoid hH hinner hZbot (eZ.symm.trans e) nineAvoid_alt_six).elim
      · exact Or.inr (Or.inr ⟨e⟩)
    · exact Or.inl ⟨d, ⟨q, hq7, hdq⟩, ⟨e⟩⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      obtain ⟨hp, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_three hq3
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hp, hf] at h
      obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
      exact (false_of_nineAvoid hH hinner hZbot (eZ.symm.trans eU) nineAvoid_u33).elim
  · exact Or.inr (Or.inl ⟨hZ3, ⟨e6⟩⟩)

end CFSG.HardMathSupport.Curtis.Coordinator
