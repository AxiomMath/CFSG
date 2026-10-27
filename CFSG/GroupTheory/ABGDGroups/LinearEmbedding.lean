module

public import CFSG.GroupTheory.ABGDGroups.LinearDecomposition
public import CFSG.GroupTheory.ABGDGroups.LinearSemidihedral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalPSL2ToPGammaL2Apply
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.CharacterTheory.Semidihedral.AlternatingSevenExclusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower HasDihedralSylowTwo
  pGammaL2PSLRange pGammaL2PGLRange mem_pGammaL2PSLRange_iff pgl2FieldAut)
open scoped commutatorElement

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm

theorem odd_card_oddCore (G : Type*) [Group G] [Finite G] : Odd (Nat.card (CFSG.oddCore G)) := by
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem oddCore_eq_bot_of_normal {H : Type*} [Group H] [Finite H] (hO : CFSG.oddCore H = ⊥)
    (K : Subgroup H) [K.Normal] : CFSG.oddCore K = ⊥ := by
  rw [oddCore_eq_pPrimeCore_two] at hO ⊢
  have hN : ((CFSG.pPrimeCore 2 K).map K.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (CFSG.pPrimeCore 2 K).map K.subtype ≤ CFSG.pPrimeCore 2 H := by
    refine le_sSup ⟨hN, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at hle

section Dihedral

variable {H : Type} [Group H] [Finite H]

theorem aSeven_or_exists_normal_psl2
    (hDih : HasDihedralSylowTwo H)
    (hNC : ¬ HasNormalPComplement 2 H) (hO : CFSG.oddCore H = ⊥) :
    Nonempty (H ≃* alternatingGroup (Fin 7)) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), IsOddPrimePower (Nat.card F) ∧
        ∃ N : Subgroup H, N.Normal ∧ Nonempty (N ≃* PSL2 F) ∧
          Subgroup.centralizer (N : Set H) = ⊥ := by
  have hO2 : CFSG.pPrimeCore 2 H = ⊥ := (oddCore_eq_pPrimeCore_two H) ▸ hO
  let qE : (H ⧸ CFSG.pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (G := H) hO2).trans (QuotientGroup.quotientBot (G := H))
  rcases CFSG.GorensteinWalter.gorensteinWalter H hDih with
    ⟨_, hQ⟩ | ⟨_, ⟨e7⟩⟩ | ⟨_, K, hK, L', hL'n, -, hL'model⟩
  · exfalso
    apply hNC
    have hH2 : IsPGroup 2 H := hQ.of_equiv qE
    exact ⟨⊥, inferInstance, by simp, hH2.of_equiv (QuotientGroup.quotientBot (G := H)).symm⟩
  · exact Or.inl ⟨qE.symm.trans e7⟩
  · right
    set N := L'.map qE.toMonoidHom
    have hNn : N.Normal := hL'n.map _ qE.surjective
    let eN : L' ≃* N := L'.equivMapOfInjective _ qE.injective
    obtain ⟨F, _, _, hF, M, hMn, ⟨eM⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
        IsOddPrimePower (Nat.card F) ∧ ∃ M : Subgroup H, M.Normal ∧ Nonempty (M ≃* PSL2 F) := by
      rcases hL'model with he | he
      · obtain ⟨e⟩ := he
        exact ⟨K, inferInstance, inferInstance, hK, N, hNn, ⟨eN.symm.trans e⟩⟩
      · obtain ⟨e⟩ := he
        by_cases h3 : Nat.card K = 3
        · have : Fintype K := Fintype.ofFinite K
          let eK : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three
            (by simpa [Nat.card_eq_fintype_card] using h3)
          obtain ⟨M, hMn, -, ⟨eM⟩⟩ :=
            CFSG.GorensteinWalter.exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three N hNn
              ((eN.symm.trans e).trans (CFSG.GorensteinWalter.pgl2RingEquiv eK).symm)
          exact ⟨ZMod 3, inferInstance, inferInstance,
            ⟨3, 1, Nat.prime_three, by decide, le_rfl, by simp⟩, M, hMn, ⟨eM⟩⟩
        · have hodd : Odd (Nat.card K) := by
            obtain ⟨p, f, -, hpodd, -, hq⟩ := hK
            rw [hq]
            exact hpodd.pow
          have hone : 1 < Nat.card K := Finite.one_lt_card
          have hgt : 3 < Nat.card K := by
            obtain ⟨k, hk⟩ := hodd
            omega
          obtain ⟨M, hMn, -, hM⟩ :=
            CFSG.GorensteinWalter.exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three
              N hNn K hK hgt (eN.symm.trans e)
          exact ⟨K, inferInstance, inferInstance, hK, M, hMn, hM⟩
    refine ⟨F, inferInstance, inferInstance, hF, M, hMn, ⟨eM⟩, ?_⟩
    exact
      CFSG.GorensteinWalter.centralizer_eq_bot_of_normal_centerless_dihedral_of_pPrimeCore_eq_bot
        hDih hO2 M hMn
        (CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv eM
          (CFSG.GorensteinWalter.psl2_center_eq_bot F))
        (CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eM
          (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF))

end Dihedral

section Embedding

variable {F : Type} [Field F] [Finite F]

theorem inf_pGLRange_eq_or_eq (hF : IsOddPrimePower (Nat.card F)) {A : Subgroup (PGammaL2 F)}
    (hA : pGammaL2PSLRange F ≤ A) :
    A ⊓ pGammaL2PGLRange F = pGammaL2PSLRange F ∨
      A ⊓ pGammaL2PGLRange F = pGammaL2PGLRange F := by
  have h1 : pGammaL2PSLRange F ≤ A ⊓ pGammaL2PGLRange F := le_inf hA pGammaL2PSLRange_le_pGLRange
  have h := Subgroup.relIndex_mul_relIndex _ _ _ h1 inf_le_right
  rw [CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F hF] at h
  have hdvd : (pGammaL2PSLRange F).relIndex (A ⊓ pGammaL2PGLRange F) ∣ 2 := ⟨_, h.symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h') h1)
  · right
    rw [h'] at h
    exact le_antisymm inf_le_right (Subgroup.relIndex_eq_one.mp (by omega))

omit [Finite F] in
theorem relIndex_inf_pGLRange (A : Subgroup (PGammaL2 F)) :
    (A ⊓ pGammaL2PGLRange F).relIndex A =
      Nat.card (CFSG.GorensteinWalter.pGammaL2FieldProjection F A).range := by
  rw [Subgroup.inf_relIndex_left, relIndex_pGLRange_eq_card_map,
    CFSG.GorensteinWalter.pGammaL2FieldProjection, MonoidHom.range_comp, Subgroup.range_subtype]

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem exists_embedding_of_normal_psl2 (hF : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {N : Subgroup H} [N.Normal] (e : N ≃* PSL2 F)
    (hC : Subgroup.centralizer (N : Set H) = ⊥) :
    ∃ ι : H →* PGammaL2 F, Function.Injective ι ∧ pGammaL2PSLRange F ≤ ι.range ∧
      linearCore ι = N := by
  have hF' := hF
  obtain ⟨p, f, hp, -, -, hKcard⟩ := hF'
  have : Fact p.Prime := ⟨hp⟩
  have hsurj := CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective F hKcard hF hcard
  set ι := CFSG.GorensteinWalter.normalPSL2ToPGammaL2 N F hF hcard e hsurj
  have hι : Function.Injective ι :=
    CFSG.GorensteinWalter.normalPSL2ToPGammaL2_injective N F hF hcard e hC hsurj
  have happly : ∀ n : N, ι n = SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n)) :=
    CFSG.GorensteinWalter.normalPSL2ToPGammaL2_apply_subtype N F hF hcard e hsurj
  refine ⟨ι, hι, CFSG.GorensteinWalter.normalPSL2ToPGammaL2_range_contains_psl N F hF hcard e
    hsurj, ?_⟩
  ext x
  constructor
  · intro hx
    change ι x ∈ pGammaL2PSLRange F at hx
    rw [mem_pGammaL2PSLRange_iff] at hx
    obtain ⟨y, hy⟩ := hx
    have h1 := happly (e.symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    have : x = (e.symm y : H) := hι (hy.symm.trans h1.symm)
    rw [this]
    exact (e.symm y).property
  · intro hx
    change ι x ∈ pGammaL2PSLRange F
    rw [show x = ((⟨x, hx⟩ : N) : H) from rfl, happly, mem_pGammaL2PSLRange_iff]
    exact ⟨_, rfl⟩

theorem nonempty_mulEquiv_psl2_three_or_pgl2_three (h3 : Nat.card F = 3) {N : Subgroup H}
    [N.Normal] (e : N ≃* PSL2 F) (hC : Subgroup.centralizer (N : Set H) = ⊥) :
    Nonempty (H ≃* PSL2 (ZMod 3)) ∨ Nonempty (H ≃* PGL2 (ZMod 3)) := by
  have : Fintype F := Fintype.ofFinite F
  let eK : ZMod 3 ≃+* F :=
    ZMod.ringEquivOfPrime F Nat.prime_three (by simpa [Nat.card_eq_fintype_card] using h3)
  let eN3 : N ≃* PSL2 (ZMod 3) := e.trans (CFSG.GorensteinWalter.psl2RingEquiv eK).symm
  obtain ⟨φ, hφ⟩ := CFSG.GorensteinWalter.quotient_centralizer_mulAut_embedding N
  let q : H ≃* H ⧸ Subgroup.centralizer (N : Set H) :=
    ((QuotientGroup.quotientMulEquivOfEq (G := H) hC).trans
      (QuotientGroup.quotientBot (G := H))).symm
  let ψ : H →* MulAut N := φ.comp q.toMonoidHom
  have hψ : Function.Injective ψ := hφ.comp q.injective
  let eNA4 : N ≃* alternatingGroup (Fin 4) :=
    eN3.trans CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup
  let eAut : Equiv.Perm (Fin 4) ≃* MulAut (alternatingGroup (Fin 4)) :=
    MulEquiv.ofBijective _ GroupTheory.AutAlternating.aut_alternatingGroup_four_bijective_conj
  have hNcard : Nat.card N = 12 :=
    (Nat.card_congr eN3.toEquiv).trans CFSG.GorensteinWalter.nat_card_psl2_zmod3
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hAutcard : Nat.card (MulAut N) = 24 := by
    rw [Nat.card_congr (MulAut.congr eNA4).toEquiv, ← Nat.card_congr eAut.toEquiv, hPermCard]
  have hle : Nat.card H ≤ 24 := (Nat.card_le_card_of_injective ψ hψ).trans_eq hAutcard
  obtain ⟨k, hk⟩ := N.card_subgroup_dvd_card
  rw [hNcard] at hk
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd hk (by simp [Nat.card_pos.ne'])
    · exact h
  rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
  · left
    have htop : N = ⊤ := Subgroup.eq_top_of_card_eq N (by rw [hNcard, hk])
    exact ⟨((Subgroup.topEquiv (G := H)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans eN3⟩
  · right
    have hbij : Function.Bijective ψ :=
      (Nat.bijective_iff_injective_and_card ψ).mpr ⟨hψ, by rw [hk, hAutcard]⟩
    exact ⟨(((MulEquiv.ofBijective ψ hbij).trans (MulAut.congr eNA4)).trans eAut.symm).trans
      CFSG.GorensteinWalter.pgl2_three_equiv_perm.symm⟩

theorem aSeven_or_embedding_of_hasDihedralSylowTwo
    (hDih : HasDihedralSylowTwo H)
    (hNC : ¬ HasNormalPComplement 2 H) (hO : CFSG.oddCore H = ⊥) :
    Nonempty (H ≃* alternatingGroup (Fin 7)) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F), IsOddPrimePower (Nat.card F) ∧
        ∃ (ι : H →* PGammaL2 F) (M : Subgroup (PGammaL2 F)), Function.Injective ι ∧
          (M = pGammaL2PSLRange F ∨ M = pGammaL2PGLRange F) ∧ M ≤ ι.range ∧
            Odd (M.relIndex ι.range) := by
  rcases aSeven_or_exists_normal_psl2 hDih hNC hO with h7 | ⟨F, _, _, hF, N, hNn, ⟨e⟩, hC⟩
  · exact Or.inl h7
  right
  have := hNn
  by_cases h3 : Nat.card F = 3
  · have h3' : IsOddPrimePower (Nat.card (ZMod 3)) :=
      ⟨3, 1, Nat.prime_three, by decide, le_rfl, by simp⟩
    refine ⟨ZMod 3, inferInstance, inferInstance, h3', ?_⟩
    rcases nonempty_mulEquiv_psl2_three_or_pgl2_three h3 e hC with heH | heH
    · obtain ⟨eH⟩ := heH
      set ι := ((SemidirectProduct.inl : PGL2 (ZMod 3) →* PGammaL2 (ZMod 3)).comp
          Matrix.ProjectiveSpecialLinearGroup.toPGL).comp eH.toMonoidHom
      have hr : ι.range = pGammaL2PSLRange (ZMod 3) := by
        ext x
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨eH a, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨eH.symm y, by simp [ι]⟩
      refine ⟨ι, pGammaL2PSLRange (ZMod 3), ?_, Or.inl rfl, hr.ge, ?_⟩
      · exact (SemidirectProduct.inl_injective.comp
          Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).comp eH.injective
      · rw [hr, Subgroup.relIndex_self]
        exact odd_one
    · obtain ⟨eH⟩ := heH
      set ι := (SemidirectProduct.inl : PGL2 (ZMod 3) →* PGammaL2 (ZMod 3)).comp eH.toMonoidHom
      have hr : ι.range = pGammaL2PGLRange (ZMod 3) := by
        ext x
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨eH a, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ⟨eH.symm y, by simp [ι]⟩
      refine ⟨ι, pGammaL2PGLRange (ZMod 3), ?_, Or.inr rfl, hr.ge, ?_⟩
      · exact SemidirectProduct.inl_injective.comp eH.injective
      · rw [hr, Subgroup.relIndex_self]
        exact odd_one
  · have hodd : Odd (Nat.card F) := by
      obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
      rw [hq]
      exact hpodd.pow
    have hone : 1 < Nat.card F := Finite.one_lt_card
    have hgt : 3 < Nat.card F := by
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨ι, hι, hPSL, -⟩ := exists_embedding_of_normal_psl2 hF hgt e hC
    refine ⟨F, inferInstance, inferInstance, hF, ι, ι.range ⊓ pGammaL2PGLRange F, hι,
      inf_pGLRange_eq_or_eq hF hPSL, inf_le_left, ?_⟩
    rw [relIndex_inf_pGLRange]
    let eR : H ≃* ι.range := MulEquiv.ofBijective ι.rangeRestrict
      ⟨fun a b hab => hι (congrArg Subtype.val hab), ι.rangeRestrict_surjective⟩
    exact CFSG.GorensteinWalter.pGammaL2_field_projection_range_odd_of_dihedral F hF hgt
      ι.range hPSL (CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv eR.symm hDih)

end Embedding

theorem IsLinearDecomposition.hasDihedralSylowTwo {H : Type} [Group H] [Finite H] {F : Type}
    [Field F] [Finite F] {ι : H →* PGammaL2 F} {L E : Subgroup H} {S : Sylow 2 H}
    (hd : IsLinearDecomposition ι L E S)
    (hL : L.map ι = pGammaL2PSLRange F ∨ L.map ι = pGammaL2PGLRange F) :
    HasDihedralSylowTwo H := by
  have hLd : HasDihedralSylowTwo L := by
    let eL := L.equivMapOfInjective ι hd.injective
    rcases hL with h | h
    · exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv
        ((eL.trans (MulEquiv.subgroupCongr h)).trans
          (CFSG.GorensteinWalter.pGammaL2PSLRangeEquiv F).symm)
        (CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hd.isOddPrimePower_card)
    · exact CFSG.GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv
        ((eL.trans (MulEquiv.subgroupCongr h)).trans
          (CFSG.GorensteinWalter.pGammaL2PGLRangeEquiv F).symm)
        (CFSG.GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hd.isOddPrimePower_card)
  intro P
  have hPL := hd.sylow_le P
  obtain ⟨m, hm, ⟨e⟩⟩ := hLd (P.subtype hPL)
  exact ⟨m, hm, ⟨((Subgroup.subgroupOfEquivOfLe hPL).symm.trans
    (MulEquiv.subgroupCongr (Sylow.coe_subtype P hPL).symm)).trans e⟩⟩

theorem IsLinearDecomposition.map_eq_pGLStar_of_hasSemidihedralSylow {H : Type} [Group H]
    [Finite H] {F : Type} [Field F] [Finite F] {ι : H →* PGammaL2 F} {L E : Subgroup H}
    {S : Sylow 2 H} (hd : IsLinearDecomposition ι L E S) {n : ℕ}
    (hn : HasSemidihedralSylow H n) : L.map ι = pGammaL2PGLStar F := by
  rcases hd.map_eq with h | h | h
  · exact absurd (hd.hasDihedralSylowTwo (Or.inl h))
      (not_hasDihedralSylowTwo_of_hasSemidihedralSylow hn)
  · exact absurd (hd.hasDihedralSylowTwo (Or.inr h))
      (not_hasDihedralSylowTwo_of_hasSemidihedralSylow hn)
  · exact h

theorem isKleinFour_map_of_injective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) {V : Subgroup G} (hV : IsKleinFour V) : IsKleinFour (V.map f) :=
  ⟨by rw [← Nat.card_congr (V.equivMapOfInjective f hf).toEquiv]; exact hV.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv (V.equivMapOfInjective f hf)]; exact hV.exponent_two⟩

theorem exists_kleinFour_le_pGammaL2PSLRange {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) :
    ∃ V : Subgroup (PGammaL2 F), IsKleinFour V ∧ V ≤ pGammaL2PSLRange F ∧
      ∀ σ : F ≃+* F, ∀ v ∈ V, SemidirectProduct.inr σ * v = v * SemidirectProduct.inr σ := by
  obtain ⟨p, f, hp, hpodd, -, hcard⟩ := hF
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  set i : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  set j : PGL2 (ZMod p) →* PGL2 F := Matrix.ProjGenLinGroup.map i
  have hj : Function.Injective j := CFSG.Semidihedral.FixedFieldCentralizer.pgl_map_injective i
  have hp' : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p, 1, hp, hpodd, le_rfl, by simp⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (PSL2 (ZMod p))) := inferInstance
  obtain ⟨m, hm, ⟨eP⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model (ZMod p) hp' P
  obtain ⟨V₀, -, hV₀⟩ := CFSG.GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (P : Subgroup (PSL2 (ZMod p))) hm eP
  set φ : PSL2 (ZMod p) →* PGammaL2 F :=
    ((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp j).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hφ : Function.Injective φ := (SemidirectProduct.inl_injective.comp hj).comp
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hfix : ∀ σ : F ≃+* F, ∀ g : PGL2 (ZMod p), pgl2FieldAut F σ (j g) = j g := by
    intro σ g
    induction g using Matrix.ProjGenLinGroup.induction_on with
    | mk A =>
      rw [Matrix.ProjGenLinGroup.map_mk, CFSG.GorensteinWalter.pgl2FieldAut_apply]
      change CFSG.GorensteinWalter.pgl2RingEquiv σ
        (QuotientGroup.mk' _ (Matrix.GeneralLinearGroup.map i A)) = _
      rw [CFSG.GorensteinWalter.pgl2RingEquiv_mk]
      congr 1
      ext a b
      simp only [Matrix.GeneralLinearGroup.map_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact DFunLike.congr_fun (RingHom.ext_zmod (σ.toRingHom.comp i) i) _
  refine ⟨V₀.map φ, isKleinFour_map_of_injective hφ hV₀, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    induction y using QuotientGroup.induction_on with
    | H S =>
      rw [mem_pGammaL2PSLRange_iff]
      refine ⟨(Matrix.SpecialLinearGroup.map i S : Matrix.SpecialLinearGroup (Fin 2) F), ?_⟩
      simp only [φ, MonoidHom.comp_apply, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, j,
        Matrix.ProjGenLinGroup.map_mk]
      congr 2
      ext a b
      rfl
  · rintro σ _ ⟨y, -, rfl⟩
    have h := SemidirectProduct.inl_aut (φ := pgl2FieldAut F) σ
      (j (Matrix.ProjectiveSpecialLinearGroup.toPGL y))
    rw [hfix] at h
    change SemidirectProduct.inr σ * SemidirectProduct.inl (j _) =
      SemidirectProduct.inl (j _) * SemidirectProduct.inr σ
    calc (SemidirectProduct.inr σ : PGammaL2 F) *
          SemidirectProduct.inl (j (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) =
        SemidirectProduct.inr σ *
          SemidirectProduct.inl (j (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) *
          SemidirectProduct.inr σ⁻¹ * SemidirectProduct.inr σ := by rw [map_inv]; group
      _ = _ := by rw [← h]

section Semidihedral

variable {H : Type} [Group H] [Finite H]

theorem not_hasNormalPComplement_of_noIndexTwo {K : Type*} [Group K] [Finite K]
    (hK : ∀ M : Subgroup K, M.index ≠ 2) (h2 : 2 ∣ Nat.card K) :
    ¬ HasNormalPComplement 2 K := by
  rintro ⟨N, hNn, hNodd, hN2⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hidx : N.index = 1 := by rw [Subgroup.index_eq_card, hk, pow_zero]
    rw [Subgroup.index_eq_one] at hidx
    rw [hidx, Subgroup.card_top] at hNodd
    exact absurd (Nat.Coprime.coprime_dvd_right h2 hNodd) (by norm_num)
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := K ⧸ N) 2 (n := k - 1)
    (by rw [hk]; exact Nat.pow_dvd_pow 2 (Nat.sub_le k 1))
  have hQidx : Q.index = 2 := by
    have h := Q.index_mul_card
    rw [hQ, hk] at h
    have hk' : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
    rw [hk'] at h
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  apply hK (Q.comap (QuotientGroup.mk' N))
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), hQidx]

omit [Finite H] in
theorem false_of_hasSemidihedralSylow_of_aSeven {n : ℕ} (hSD : HasSemidihedralSylow H n)
    {K : Subgroup H} [K.Normal] (hK2 : K.index = 2) (e7 : K ≃* alternatingGroup (Fin 7)) :
    False := by
  obtain ⟨h, hh⟩ := exists_orderOf_eq_eight_of_hasSemidihedralSylow hSD
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  let eAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective c
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
        (by norm_num))
  let χ : H →* Equiv.Perm (Fin 7) :=
    eAut.symm.toMonoidHom.comp ((MulAut.congr e7).toMonoidHom.comp (MulAut.conjNormal (H := K)))
  have hχK : ∀ x : K, χ x = ((e7 x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
    intro x
    apply eAut.injective
    simp only [χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    change MulAut.congr e7 (MulAut.conjNormal (x : H)) =
      MulAut.conjNormal ((e7 x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
    rw [MulAut.conjNormal_val, MulAut.conjNormal_val]
    ext y
    simp [MulAut.congr, MulAut.conj_apply]
  have h4K : h ^ 4 ∈ K := by
    have := Subgroup.sq_mem_of_index_two hK2 (h ^ 2)
    rwa [← pow_mul] at this
  have h4 : h ^ 4 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hh] at this
    norm_num at this
  have hχ4 : χ h ^ 4 ≠ 1 := by
    rw [← map_pow, show h ^ 4 = ((⟨h ^ 4, h4K⟩ : K) : H) from rfl, hχK]
    intro h1
    apply h4
    have h2 : (e7 ⟨h ^ 4, h4K⟩ : alternatingGroup (Fin 7)) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    exact congrArg Subtype.val h2
  have hχ8 : χ h ^ 8 = 1 := by rw [← map_pow, ← hh, pow_orderOf_eq_one, map_one]
  have hord : orderOf (χ h) = 8 :=
    orderOf_eq_prime_pow (p := 2) (n := 2) (by norm_num; exact hχ4) (by norm_num; exact hχ8)
  exact CFSG.Semidihedral.AlternatingSevenExclusion.symmetric_seven_no_order_eight _ hord

theorem exists_embedding_of_hasSemidihedralSylow
    (hO : CFSG.oddCore H = ⊥) {K : Subgroup H}
    (hK : IsDGroupData K) {n : ℕ} (hSD : HasSemidihedralSylow H n)
    (hKD : HasDihedralSylowTwo K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), IsOddPrimePower (Nat.card F) ∧
      ∃ ι : H →* PGammaL2 F, Function.Injective ι ∧ pGammaL2PGLStar F ≤ ι.range ∧
        Odd ((pGammaL2PGLStar F).relIndex ι.range) := by
  have hKn := hK.normal
  have hK2 := hK.index_eq_two
  have hOK := oddCore_eq_bot_of_normal hO K
  have h2K : 2 ∣ Nat.card K := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
    obtain ⟨m, -, ⟨e⟩⟩ := hKD P
    have hP : Nat.card (P : Subgroup K) = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    exact (Dvd.intro _ hP.symm).trans (Subgroup.card_subgroup_dvd_card _)
  have hKNC := not_hasNormalPComplement_of_noIndexTwo hK.noIndexTwo h2K
  rcases aSeven_or_embedding_of_hasDihedralSylowTwo hKD hKNC hOK with h7 |
      ⟨F, _, _, hF, ιK, MK, hιK, hMK, hMKle, hMKodd⟩
  · obtain ⟨e7⟩ := h7
    exact (false_of_hasSemidihedralSylow_of_aSeven hSD hK2 e7).elim
  have hMKpsl : MK = pGammaL2PSLRange F := by
    rcases hMK with h | h
    · exact h
    · exfalso
      set φ := (pGammaL2DetClass F hF).comp ιK
      have hsurj : Function.Surjective φ := by
        intro c
        obtain ⟨g, rfl⟩ := CFSG.Semidihedral.SemilinearOuterQuotient.pglDet_surjective F c
        obtain ⟨k, hk⟩ : SemidirectProduct.inl g ∈ ιK.range := hMKle (h ▸ ⟨g, rfl⟩)
        exact ⟨k, by simp [φ, hk, pGammaL2DetClass_apply]⟩
      apply hK.noIndexTwo φ.ker
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
        CFSG.Semidihedral.SemilinearOuterQuotient.squareClass_card_two F hF]
  subst hMKpsl
  set L₀ := linearCore ιK
  have hL₀idx : Odd L₀.index := by
    change Odd ((pGammaL2PSLRange F).comap ιK).index
    rw [Subgroup.index_comap]
    exact hMKodd
  have hL₀map : L₀.map ιK = pGammaL2PSLRange F := by
    change ((pGammaL2PSLRange F).comap ιK).map ιK = _
    rw [Subgroup.map_comap_eq_self hMKle]
  let eL₀ : L₀ ≃* PSL2 F := ((L₀.equivMapOfInjective ιK hιK).trans
    (MulEquiv.subgroupCongr hL₀map)).trans (CFSG.GorensteinWalter.pGammaL2PSLRangeEquiv F).symm
  have hcard : 3 < Nat.card F := by
    have hodd : Odd (Nat.card F) := by
      obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
      rw [hq]
      exact hpodd.pow
    have hone : 1 < Nat.card F := Finite.one_lt_card
    by_contra h3
    have h3' : Nat.card F = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hL₀card : Nat.card L₀ = 12 := by
      rw [Nat.card_congr eL₀.toEquiv, CFSG.GorensteinWalter.psl2_card_formula F hF, h3']
      norm_num
    have hHcard : Nat.card H = 24 * L₀.index := by
      rw [← K.card_mul_index, hK2, ← L₀.card_mul_index, hL₀card]
      ring
    obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
    obtain ⟨f⟩ := hSD.2 S
    have hS : Nat.card (S : Subgroup H) = 2 ^ n := by
      rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by have := hSD.1; omega)]
    have h16 : 16 ∣ Nat.card H := by
      have h1 : 2 ^ 4 ∣ 2 ^ n := Nat.pow_dvd_pow 2 hSD.1
      rw [← hS] at h1
      exact h1.trans (Subgroup.card_subgroup_dvd_card _)
    rw [hHcard] at h16
    obtain ⟨c, hc⟩ := h16
    obtain ⟨k, hk⟩ := hL₀idx
    omega
  have hL₀comm : L₀ = commutator K := by
    apply le_antisymm
    · have := CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three F hcard
      have : Group.IsPerfect L₀ :=
        Group.IsPerfect.ofSurjective (f := eL₀.symm.toMonoidHom) eL₀.symm.surjective
      rw [← Subgroup.commutator_eq_self (H := L₀), commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    · rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      change ιK ⁅x, y⁆ ∈ pGammaL2PSLRange F
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact commutator_mem_pGammaL2PSLRange hF _ _
  have hL₀char : L₀.Characteristic := by
    rw [hL₀comm]
    infer_instance
  set N := L₀.map K.subtype
  have hNn : N.Normal := ConjAct.normal_of_characteristic_of_normal
  let eN : N ≃* PSL2 F := (L₀.equivMapOfInjective K.subtype K.subtype_injective).symm.trans eL₀
  have hNidx : N.index = 2 * L₀.index := by
    rw [Subgroup.index_map_subtype, hK2, mul_comm]
  obtain ⟨V, hVN, hV⟩ : ∃ V : Subgroup H, V ≤ N ∧ IsKleinFour V := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 (PSL2 F)) := inferInstance
    obtain ⟨m, hm, ⟨eP⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hF P
    obtain ⟨V₁, -, hV₁⟩ := CFSG.GorensteinWalter.exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
      (P : Subgroup (PSL2 F)) hm eP
    refine ⟨(V₁.map eN.symm.toMonoidHom).map N.subtype, Subgroup.map_subtype_le _, ?_⟩
    exact isKleinFour_map_of_injective N.subtype_injective
      (isKleinFour_map_of_injective eN.symm.injective hV₁)
  have hCK : Subgroup.centralizer (N : Set H) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcC, hcK⟩
    have hcent : ιK ⟨c, hcK⟩ ∈
        Subgroup.centralizer (pGammaL2PSLRange F : Set (PGammaL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨l, rfl⟩ := hMKle hz
      have hl : l ∈ L₀ := hz
      have hcomm := (Subgroup.mem_centralizer_iff.mp hcC) (l : H) ⟨l, hl, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ιK (Subtype.ext hcomm)
    rw [CFSG.GorensteinWalter.pGammaL2_pslRange_centralizer_eq_bot F hF hcard,
      Subgroup.mem_bot] at hcent
    have h1 : (⟨c, hcK⟩ : K) = 1 := hιK (hcent.trans (map_one ιK).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  have hC : Subgroup.centralizer (N : Set H) = ⊥ := by
    by_contra hCne
    obtain ⟨⟨t, htC⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have htK : t ∉ K := fun h => by
      have : t ∈ Subgroup.centralizer (N : Set H) ⊓ K := ⟨htC, h⟩
      rw [hCK, Subgroup.mem_bot] at this
      exact ht1' this
    have ht2 : t ^ 2 = 1 := by
      have : t ^ 2 ∈ Subgroup.centralizer (N : Set H) ⊓ K :=
        ⟨Subgroup.pow_mem _ htC 2, Subgroup.sq_mem_of_index_two hK2 t⟩
      rwa [hCK, Subgroup.mem_bot] at this
    exact false_of_hasSemidihedralSylow_of_kleinFour hSD hV ht2
      (fun h => htK (Subgroup.map_subtype_le L₀ (hVN h)))
      (fun v hv => Subgroup.mem_centralizer_iff.mp htC v (hVN hv))
  obtain ⟨ι, hι, hPSL, hcore⟩ := exists_embedding_of_normal_psl2 hF hcard eN hC
  set A := ι.range
  have hPSLidx : (pGammaL2PSLRange F).relIndex A = 2 * L₀.index := by
    rw [← Subgroup.index_comap, ← hNidx]
    exact congrArg Subgroup.index hcore
  have hlin : A ⊓ pGammaL2PGLRange F = pGammaL2PSLRange F := by
    rcases inf_pGLRange_eq_or_eq hF hPSL with h | h
    · exact h
    · exfalso
      have hPGLle : pGammaL2PGLRange F ≤ A := by rw [← h]; exact inf_le_left
      have hPGLodd : Odd ((pGammaL2PGLRange F).relIndex A) := by
        have e := Subgroup.relIndex_mul_relIndex _ _ _ pGammaL2PSLRange_le_pGLRange hPGLle
        rw [CFSG.GorensteinWalter.pGammaL2_psl_range_relIndex_pgl_eq_two F hF, hPSLidx] at e
        rw [show (pGammaL2PGLRange F).relIndex A = L₀.index by omega]
        exact hL₀idx
      obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
      obtain ⟨ι', E, hd, hmap⟩ := exists_isLinearDecomposition_of_embedding hF hι
        (Or.inr (Or.inl rfl)) hPGLle hPGLodd S
      exact not_hasDihedralSylowTwo_of_hasSemidihedralSylow hSD
        (hd.hasDihedralSylowTwo (Or.inr hmap))
  have hρ : Nat.card (A.map (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F))) =
      2 * L₀.index := by
    rw [← relIndex_pGLRange_eq_card_map, ← Subgroup.inf_relIndex_left, hlin, hPSLidx]
  obtain ⟨⟨σ, hσA⟩, hσ⟩ := exists_prime_orderOf_dvd_card' (G := A.map
    (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F))) 2 (by rw [hρ]; exact dvd_mul_right _ _)
  rw [Subgroup.orderOf_mk] at hσ
  obtain ⟨a, haA, rfl⟩ := hσA
  rw [SemidirectProduct.rightHom_eq_right] at hσ
  have hσ2 : a.right ^ 2 = 1 := by
    have h := pow_orderOf_eq_one a.right
    rwa [hσ] at h
  have hσ1 : a.right ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    norm_num at hσ
  have haL : a.left ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    intro haL
    have hinl : SemidirectProduct.inl a.left ∈ A := by
      apply hPSL
      rw [mem_pGammaL2PSLRange_iff]
      obtain ⟨y, hy⟩ := haL
      exact ⟨y, by rw [hy]⟩
    have hinr : SemidirectProduct.inr a.right ∈ A := by
      have h : SemidirectProduct.inr a.right = (SemidirectProduct.inl a.left)⁻¹ * a := by
        rw [eq_inv_mul_iff_mul_eq, SemidirectProduct.inl_left_mul_inr_right]
      rw [h]
      exact A.mul_mem (A.inv_mem hinl) haA
    obtain ⟨W, hW, hWPSL, hWcomm⟩ := exists_kleinFour_le_pGammaL2PSLRange hF
    obtain ⟨t, ht⟩ := hinr
    have hWA : W ≤ A := hWPSL.trans hPSL
    have hWH : IsKleinFour (W.comap ι) := by
      have e := (W.comap ι).equivMapOfInjective ι hι
      rw [Subgroup.map_comap_eq_self hWA] at e
      exact ⟨by rw [Nat.card_congr e.toEquiv]; exact hW.card_four,
        by rw [Monoid.exponent_eq_of_mulEquiv e]; exact hW.exponent_two⟩
    refine false_of_hasSemidihedralSylow_of_kleinFour hSD hWH (t := t) ?_ ?_ ?_
    · apply hι
      rw [map_pow, ht, ← map_pow, hσ2, map_one, map_one]
    · intro htW
      have h1 : ι t ∈ pGammaL2PGLRange F :=
        pGammaL2PSLRange_le_pGLRange (hWPSL htW)
      rw [ht, pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
        SemidirectProduct.rightHom_inr] at h1
      exact hσ1 h1
    · intro v hv
      apply hι
      rw [map_mul, map_mul, ht]
      exact (hWcomm a.right (ι v) hv).symm
  have haS : a ∈ pGammaL2PGLStar F :=
    ⟨hσ2, ⟨fun h => absurd h haL, fun h => absurd h hσ1⟩⟩
  have hle : pGammaL2PGLStar F ≤ A := by
    intro x hx
    by_cases hx1 : x.right = 1
    · have hxP : x ∈ pGammaL2PGLRange F := by
        rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
          SemidirectProduct.rightHom_eq_right, hx1]
      apply hPSL
      rw [← pGLStar_inf_pGLRange]
      exact ⟨hx, hxP⟩
    · have hxa : x.right = a.right := ringEquiv_eq_of_sq_eq_one hx.1 hσ2 hx1 hσ1
      have hxaP : x * a⁻¹ ∈ pGammaL2PGLRange F := by
        rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
          map_mul, map_inv, SemidirectProduct.rightHom_eq_right, hxa, mul_inv_cancel]
      have hxa' : x * a⁻¹ ∈ pGammaL2PSLRange F := by
        rw [← pGLStar_inf_pGLRange]
        exact ⟨(pGammaL2PGLStar F).mul_mem hx ((pGammaL2PGLStar F).inv_mem haS), hxaP⟩
      have h := A.mul_mem (hPSL hxa') haA
      rwa [inv_mul_cancel_right] at h
  refine ⟨F, inferInstance, inferInstance, hF, ι, hι, hle, ?_⟩
  have hs : (pGammaL2PSLRange F).relIndex (pGammaL2PGLStar F) = 2 := by
    have h1 := relIndex_pGammaL2PSLRange_pGLStar_le_two (F := F)
    have h2 := relIndex_ne_zero_of_finite (pGammaL2PSLRange F) (pGammaL2PGLStar F)
    have h3 : (pGammaL2PSLRange F).relIndex (pGammaL2PGLStar F) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      intro h
      exact haL (by
        have := (pGammaL2PSLRange_le_pGLRange (h haS))
        rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
          SemidirectProduct.rightHom_eq_right] at this
        exact absurd this hσ1)
    omega
  have e := Subgroup.relIndex_mul_relIndex _ _ _ pGammaL2PSLRange_le_pGLStar hle
  rw [hs, hPSLidx] at e
  rw [show (pGammaL2PGLStar F).relIndex A = L₀.index by omega]
  exact hL₀idx

theorem aSeven_or_linearDecomposition
    (hH : IsDGroup H) (hO : CFSG.oddCore H = ⊥)
    (hW : ¬ ∃ n, HasWreathedSylow H n) :
    Nonempty (H ≃* alternatingGroup (Fin 7)) ∨
      ∀ S : Sylow 2 H, ∃ (F : Type) (_ : Field F) (_ : Finite F) (ι : H →* PGammaL2 F)
        (L E : Subgroup H), IsLinearDecomposition ι L E S := by
  rcases hH with ⟨hDih, hNC⟩ | ⟨K, hK⟩
  · rcases aSeven_or_embedding_of_hasDihedralSylowTwo hDih hNC hO with h7 |
        ⟨F, _, _, hF, ι, M, hι, hM, hMle, hodd⟩
    · exact Or.inl h7
    · right
      intro S
      have hM' : IsStandardLayer M := by
        rcases hM with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      obtain ⟨ι', E, hd, -⟩ := exists_isLinearDecomposition_of_embedding hF hι hM' hMle hodd S
      exact ⟨F, inferInstance, inferInstance, ι', _, E, hd⟩
  · rcases hK.sylow with ⟨n, hSD, hKD⟩ | ⟨n, hWn, -⟩
    · right
      intro S
      obtain ⟨F, _, _, hF, ι, hι, hle, hodd⟩ :=
        exists_embedding_of_hasSemidihedralSylow hO hK hSD hKD
      obtain ⟨ι', E, hd, -⟩ := exists_isLinearDecomposition_of_embedding hF hι
        (Or.inr (Or.inr rfl)) hle hodd S
      exact ⟨F, inferInstance, inferInstance, ι', _, E, hd⟩
    · exact absurd ⟨n, hWn⟩ hW

end Semidihedral

end CFSG.ABGDGroups
