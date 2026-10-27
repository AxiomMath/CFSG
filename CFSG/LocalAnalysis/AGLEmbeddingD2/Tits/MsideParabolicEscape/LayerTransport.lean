module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.GNSettingM
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerAutImageProved

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.RankThreeCoreUniqueness.Helpers

theorem gnSetting_of_core {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hK : CFSG.Open.IsKProper G) (hMtop : M ≠ ⊤) (hchar : CharTwo M) (hT : IsSylowTwoOf T M)
    (hX : ∀ Y : Subgroup G, Y ≤ M → IsSubnormal Y M → InClassXBlock Y → False) :
    GNSetting ↥M (T.subgroupOf M) :=
  S3AmalgamBound.gnSetting_of_subgroup hK hMtop hchar hT hX

theorem map_normalizer_subtype {G : Type} [Group G] (M : Subgroup G) (C' : Subgroup ↥M) :
    (Subgroup.normalizer (C' : Set ↥M)).map M.subtype =
      Subgroup.normalizer ((C'.map M.subtype : Subgroup G) : Set G) ⊓ M := by
  ext g
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨?_, n.2⟩
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨n * c * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn c).mp hc, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      have h1 : (n⁻¹ * c * n) ∈ C' := by
        refine (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * c * n)).mpr ?_
        have e : n * (n⁻¹ * c * n) * n⁻¹ = c := by group
        rw [e]; exact hc
      refine ⟨n⁻¹ * c * n, h1, ?_⟩
      have hcx' : ((c : ↥M) : G) = (n : G) * x * (n : G)⁻¹ := hcx
      show ((n⁻¹ * c * n : ↥M) : G) = x
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcx']
      group
  · rintro ⟨hgN, hgM⟩
    refine ⟨⟨g, hgM⟩, ?_, rfl⟩
    refine Subgroup.mem_normalizer_iff.mpr ?_
    intro c
    have key := Subgroup.mem_normalizer_iff.mp hgN (c : G)
    constructor
    · intro hc
      have : g * (c : G) * g⁻¹ ∈ C'.map M.subtype := key.mp ⟨c, hc, rfl⟩
      obtain ⟨c2, hc2, hc2e⟩ := this
      have : (⟨g, hgM⟩ : ↥M) * c * ⟨g, hgM⟩⁻¹ = c2 := Subtype.ext (by simpa using hc2e.symm)
      rw [this]; exact hc2
    · intro hc
      have : g * (c : G) * g⁻¹ ∈ C'.map M.subtype := ⟨_, hc, by simp⟩
      obtain ⟨c1, hc1, hc1e⟩ := key.mpr this
      have : c1 = c := Subtype.ext hc1e
      rw [← this]; exact hc1

theorem characteristic_map_equiv' {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {H : Subgroup A}
    (h : H.Characteristic) : (H.map φ.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq] at h ⊢
  intro ψ
  have hσ := h (φ.trans (ψ.trans φ.symm))
  calc (H.map φ.toMonoidHom).map ψ.toMonoidHom = H.map ((φ.trans ψ).toMonoidHom) := by
        rw [Subgroup.map_map]; rfl
    _ = (H.map (φ.trans (ψ.trans φ.symm)).toMonoidHom).map φ.toMonoidHom := by
        rw [Subgroup.map_map]; congr 1; ext x; simp
    _ = H.map φ.toMonoidHom := by rw [hσ]


theorem characteristic_subgroupOf_map {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)
    {C' : Subgroup ↥M} (hC'T : C' ≤ T.subgroupOf M)
    (h : (C'.subgroupOf (T.subgroupOf M)).Characteristic) :
    ((C'.map M.subtype).subgroupOf T).Characteristic := by
  let ι : ↥(T.subgroupOf M) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTM
  have hc := characteristic_map_equiv' ι h
  have heq : (C'.subgroupOf (T.subgroupOf M)).map ι.toMonoidHom =
      (C'.map M.subtype).subgroupOf T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
    · rintro ⟨c, hc', hcx⟩
      have hcT : c ∈ T.subgroupOf M := hC'T hc'
      refine ⟨⟨c, hcT⟩, hc', Subtype.ext ?_⟩
      exact hcx
  rwa [heq] at hc

theorem gnLocal_of_core {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hT : IsSylowTwoOf T M)
    (h1 : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.normalizer (C : Set G) ⊓ M))
    (h2 : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      ∀ U : Subgroup G, U ≤ Subgroup.normalizer (C : Set G) ⊓ M → IsPGroup 3 U →
        ¬ IsCyclic U → IsElemAbelian 3 U ∧ Nat.card U = 9 ∧
          ∀ x ∈ U, x ≠ 1 → ∀ y ∈ U, y ≠ 1 →
            ∃ n ∈ M ⊓ Subgroup.normalizer (U : Set G), n * x * n⁻¹ = y) :
    GNLocal (T.subgroupOf M) := by
  have hTM : T ≤ M := hT.1
  have hT'map : (T.subgroupOf M).map M.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hTM]
  have hC1 : ∀ C' : Subgroup ↥M, C' ≠ ⊥ → C' ≤ T.subgroupOf M →
      (C'.subgroupOf (T.subgroupOf M)).Characteristic →
      (C'.map M.subtype ≠ ⊥ ∧ C'.map M.subtype ≤ T ∧
        ((C'.map M.subtype).subgroupOf T).Characteristic) := by
    intro C' hC'1 hC'T hch
    refine ⟨?_, ?_, characteristic_subgroupOf_map hTM hC'T hch⟩
    · intro h
      exact hC'1 ((Subgroup.map_eq_bot_iff_of_injective C' M.subtype_injective).mp h)
    · rw [← hT'map]; exact Subgroup.map_mono hC'T
  refine ⟨fun C' hC'1 hC'T hch => ?_, fun C' hC'1 hC'T hch U' hU'N hU'p hU'c => ?_⟩
  · obtain ⟨hne, hle, hchar⟩ := hC1 C' hC'1 hC'T hch
    have hsolv := h1 _ hne hle hchar
    rw [← map_normalizer_subtype] at hsolv
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm hsolv
  · obtain ⟨hne, hle, hchar⟩ := hC1 C' hC'1 hC'T hch
    have hUN : U'.map M.subtype ≤ Subgroup.normalizer ((C'.map M.subtype : Subgroup G) : Set G) ⊓ M := by
      rw [← map_normalizer_subtype]; exact Subgroup.map_mono hU'N
    have hUp : IsPGroup 3 (U'.map M.subtype) := hU'p.map _
    have hUc : ¬ IsCyclic (U'.map M.subtype) := fun hc =>
      hU'c ((Subgroup.equivMapOfInjective U' M.subtype M.subtype_injective).isCyclic.mpr hc)
    obtain ⟨hel, hcard, htr⟩ := h2 _ hne hle hchar _ hUN hUp hUc
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have := hel.1.is_comm.comm
          (⟨((a : ↥M) : G), Subgroup.mem_map_of_mem _ a.2⟩ : U'.map M.subtype)
          (⟨((b : ↥M) : G), Subgroup.mem_map_of_mem _ b.2⟩ : U'.map M.subtype)
        exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val this))
      · have := hel.2 (x : G) (Subgroup.mem_map_of_mem _ hx)
        exact Subtype.ext (by simpa using this)
    · rw [← Subgroup.card_map_of_injective M.subtype_injective]; exact hcard
    · intro x hx y hy hx1 hy1
      obtain ⟨n, ⟨hnM, hnN⟩, hnxy⟩ := htr (x : G) ⟨x, hx, rfl⟩ (fun h => hx1 (Subtype.ext h))
        (y : G) ⟨y, hy, rfl⟩ (fun h => hy1 (Subtype.ext h))
      have hnU : (⟨n, hnM⟩ : ↥M) ∈ Subgroup.normalizer (U' : Set ↥M) := by
        have : n ∈ (Subgroup.normalizer (U' : Set ↥M)).map M.subtype := by
          rw [map_normalizer_subtype]; exact ⟨hnN, hnM⟩
        obtain ⟨m, hm, hmn⟩ := this
        have : m = ⟨n, hnM⟩ := Subtype.ext hmn
        rwa [← this]
      exact ⟨⟨n, hnM⟩, hnU, Subtype.ext (by simpa using hnxy)⟩

theorem exists_isRankTwoLayer_of_quotient {G : Type} [Group G] [Finite G] {M : Subgroup G}
    {K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 3)} (hKn : K.Normal)
    (hKs : IsSimpleGroup ↥K) (hKc : ¬ IsMulCommutative ↥K) (hKt : IsRankTwoLayerType ↥K) :
    ∃ L : Subgroup G, IsRankTwoLayer M L := by
  have hD : (GLBPrimeCore 3 M).subgroupOf M = primeComplementCore (G := ↥M) 3 :=
    glbPrimeCore_subgroupOf 3 M
  let ε : (↥M ⧸ (GLBPrimeCore 3 M).subgroupOf M) ≃* (↥M ⧸ primeComplementCore (G := ↥M) 3) :=
    QuotientGroup.quotientMulEquivOfEq hD
  set K' : Subgroup (↥M ⧸ (GLBPrimeCore 3 M).subgroupOf M) := K.map ε.symm.toMonoidHom with hK'
  haveI hK'n : K'.Normal := Subgroup.Normal.map hKn _ ε.symm.surjective
  let eK : ↥K ≃* ↥K' := Subgroup.equivMapOfInjective K ε.symm.toMonoidHom ε.symm.injective
  set π : ↥M →* ↥M ⧸ (GLBPrimeCore 3 M).subgroupOf M :=
    QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) with hπ
  set L₀ : Subgroup ↥M := K'.comap π with hL₀def
  refine ⟨L₀.map M.subtype, ?_⟩
  have hL₀ : (L₀.map M.subtype).subgroupOf M = L₀ :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective L₀
  have hstar : starImg M (L₀.map M.subtype) = K' := by
    unfold starImg
    rw [hL₀]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K'
  haveI : IsSimpleGroup ↥K := hKs
  have hK's : IsSimpleGroup ↥K' := MulEquiv.isSimpleGroup eK.symm
  have hK'c : ¬ IsMulCommutative ↥K' := by
    intro hc
    apply hKc
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hc.is_comm.comm (eK a) (eK b)
    exact eK.injective (by rw [map_mul, map_mul]; exact this)
  have hK't : IsRankTwoLayerType ↥K' := S3AmalgamBound.isRankTwoLayerType_of_equiv eK hKt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · intro g hg
    refine ⟨⟨g, glbPrimeCore_le 3 M hg⟩, ?_, rfl⟩
    show π ⟨g, glbPrimeCore_le 3 M hg⟩ ∈ K'
    have : π ⟨g, glbPrimeCore_le 3 M hg⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hg)
    rw [this]; exact K'.one_mem
  · rw [hL₀]; exact Subgroup.normal_comap _
  · rw [hstar]; exact hK's
  · rw [hstar]; exact hK'c
  · rw [hstar]; exact hK't

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
