module

public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.CGT.PushingUp.ResidualTwo
public import CFSG.GH74.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.AGLEmbedding.NoXBlock

open CFSG.QuasithinUnique CFSG.RankThree.PartOne
open scoped commutatorElement

variable {G : Type} [Group G]

theorem blockQ_eq_oTwoIn (L : Subgroup G) : blockQ L = CGT.PushingUpLit.oTwoIn L := by
  rw [blockQ, CFSG.Open.pCoreOf, CGT.PushingUpLit.oTwoIn_eq_map]

theorem blockU_eq_lit (L : Subgroup G) :
    QuasithinUnique.blockU L = CGT.PushingUpLit.blockU L := by
  rw [QuasithinUnique.blockU, CGT.PushingUpLit.blockU, blockQ_eq_oTwoIn]

theorem blockZ_eq_lit (L : Subgroup G) :
    QuasithinUnique.blockZ L = CGT.PushingUpLit.blockZ L := by
  rw [QuasithinUnique.blockZ, CGT.PushingUpLit.blockZ, blockU_eq_lit]

theorem blockQ_eq_map (L : Subgroup G) : blockQ L = (CFSG.pCore 2 ↥L).map L.subtype := by
  rw [blockQ_eq_oTwoIn, CGT.PushingUpLit.oTwoIn_eq_map]

theorem map_shortU_eq_blockU (L : Subgroup G) :
    (shortU ↥L).map L.subtype = QuasithinUnique.blockU L := by
  rw [blockU_eq_lit, CGT.PushingUpLit.map_shortU_subtype]

theorem map_shortC_eq_blockZ (L : Subgroup G) :
    (shortC ↥L).map L.subtype = QuasithinUnique.blockZ L := by
  rw [blockZ_eq_lit, CGT.PushingUpLit.map_shortC_subtype]

@[expose] noncomputable def shortUEquiv (L : Subgroup G) :
    ↥(shortU ↥L) ≃* ↥(QuasithinUnique.blockU L) :=
  (Subgroup.equivMapOfInjective (shortU ↥L) L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_shortU_eq_blockU L))

theorem coe_shortUEquiv (L : Subgroup G) (u : ↥(shortU ↥L)) :
    ((shortUEquiv L u : ↥(QuasithinUnique.blockU L)) : G) = ((u : ↥L) : G) := rfl

theorem shortUEquiv_mem_blockZ_iff (L : Subgroup G) (u : ↥(shortU ↥L)) :
    ((shortUEquiv L u : ↥(QuasithinUnique.blockU L)) : G) ∈ QuasithinUnique.blockZ L ↔
      (u : ↥L) ∈ shortC ↥L := by
  rw [coe_shortUEquiv, ← map_shortC_eq_blockZ]
  exact Subgroup.mem_map_iff_mem L.subtype_injective

section Field

variable {F K : Type} [Field F] [Field K]

@[expose] def slTwoEquiv (e : F ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (by
      ext A i j
      exact e.symm_apply_apply _)
    (by
      ext A i j
      exact e.apply_symm_apply _)

@[expose] def vecTwoEquiv (e : F ≃+* K) :
    Multiplicative (Fin 2 → F) ≃* Multiplicative (Fin 2 → K) :=
  (AddEquiv.piCongrRight fun _ : Fin 2 => e.toAddEquiv).toMultiplicative

theorem toAdd_vecTwoEquiv (e : F ≃+* K) (v : Multiplicative (Fin 2 → F)) (i : Fin 2) :
    Multiplicative.toAdd (vecTwoEquiv e v) i = e (Multiplicative.toAdd v i) := rfl

theorem toAdd_vecTwoEquiv_mulVec (e : F ≃+* K) (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Multiplicative (Fin 2 → F)) :
    Multiplicative.toAdd (vecTwoEquiv e (Multiplicative.ofAdd
      ((A : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd v)))) =
      ((slTwoEquiv e A : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (Multiplicative.toAdd (vecTwoEquiv e v)) := by
  funext i
  rw [toAdd_vecTwoEquiv]
  exact RingHom.map_mulVec e.toRingHom (A : Matrix (Fin 2) (Fin 2) F) (Multiplicative.toAdd v) i

end Field

theorem isNaturalSLTwoModule_of_isLin2Type {L : Subgroup G} {n : ℕ} (hn : n ≠ 0)
    (h : IsLin2Type L n) : IsNaturalSLTwoModule ↥L n := by
  obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  let _ : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcardK : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n hn
  let e : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (hcard.trans hcardK.symm)
  let α' : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (slTwoEquiv e).toMonoidHom.comp α
  have hpc : CFSG.pCore 2 ↥L = α'.ker := by
    rw [← hαk]
    ext x
    simp only [α', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  let φ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective α' ((slTwoEquiv e).surjective.comp hαs))
  refine ⟨φ, (vecTwoEquiv e).toMonoidHom.comp (β.comp (shortUEquiv L).toMonoidHom),
    (vecTwoEquiv e).surjective.comp (hβs.comp (shortUEquiv L).surjective), ?_, ?_⟩
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf,
      shortUEquiv_mem_blockZ_iff]
  · intro l u hu hu'
    have hcoe : ((shortUEquiv L ⟨l * u * l⁻¹, hu'⟩ : ↥(QuasithinUnique.blockU L)) : G) =
        (l : G) * ((shortUEquiv L ⟨u, hu⟩ : ↥(QuasithinUnique.blockU L)) : G) * (l : G)⁻¹ := rfl
    have key := hβe l (shortUEquiv L ⟨u, hu⟩) (shortUEquiv L ⟨l * u * l⁻¹, hu'⟩) hcoe
    apply Multiplicative.toAdd.injective
    exact (congrArg (fun w => Multiplicative.toAdd (vecTwoEquiv e (Multiplicative.ofAdd w)))
      key).trans (toAdd_vecTwoEquiv_mulVec e (α l) _)

theorem isNaturalAltModule_of_isAltType {L : Subgroup G} {m : ℕ}
    (h : IsAltType L (2 * m + 1)) : IsNaturalAltModule ↥L m := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := h
  have hpc : CFSG.pCore 2 ↥L = α.ker := hαk.symm
  let φ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin (2 * m + 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  let ψ : ↥(shortU ↥L) →* Multiplicative (Fin (2 * m + 1) → ZMod 2) :=
    (evenWeight (2 * m + 1)).subtype.toMultiplicative.comp (β.comp (shortUEquiv L).toMonoidHom)
  have hψ : ∀ u, Multiplicative.toAdd (ψ u) =
      ((Multiplicative.toAdd (β (shortUEquiv L u)) : evenWeight (2 * m + 1)) :
        Fin (2 * m + 1) → ZMod 2) := fun u => rfl
  refine ⟨φ, ψ, fun u => ?_, fun v hv => ?_, ?_, ?_⟩
  · rw [hψ]
    exact (Multiplicative.toAdd (β (shortUEquiv L u))).2
  · obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd ⟨v, hv⟩)
    obtain ⟨u, rfl⟩ := (shortUEquiv L).surjective w
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    rw [hψ, hw]
    rfl
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ u = 1 ↔ β (shortUEquiv L u) = 1 := by
      constructor
      · intro h
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        rw [← hψ, h]
        rfl
      · intro h
        apply Multiplicative.toAdd.injective
        rw [hψ, h]
        rfl
    rw [h1, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, shortUEquiv_mem_blockZ_iff]
  · intro l u hu hu'
    have hcoe : ((shortUEquiv L ⟨l * u * l⁻¹, hu'⟩ : ↥(QuasithinUnique.blockU L)) : G) =
        (l : G) * ((shortUEquiv L ⟨u, hu⟩ : ↥(QuasithinUnique.blockU L)) : G) * (l : G)⁻¹ := rfl
    have key := hβe l (shortUEquiv L ⟨u, hu⟩) (shortUEquiv L ⟨l * u * l⁻¹, hu'⟩) hcoe
    apply Multiplicative.toAdd.injective
    funext i
    exact key i

variable [Finite G]

theorem isShortGroup_of_isShort2 {L : Subgroup G} (hL : IsShort2 L) : IsShortGroup ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hres, hchar, ⟨hUQ, -⟩, htype, hlt, hirr⟩ := hL
  have hQ := blockQ_eq_map L
  have hU := map_shortU_eq_blockU L
  have hC := map_shortC_eq_blockZ L
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥L 2).mp fun c hc => ?_
    have hc' : (c : G) ∈ L ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 L : Set G) := by
      refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro r hr
      have hr' : r ∈ (CFSG.pCore 2 ↥L).map L.subtype := by rw [← hQ]; exact hr
      obtain ⟨r0, hr0, rfl⟩ := hr'
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc r0 hr0)
    have h1 : (c : G) ∈ (CFSG.pCore 2 ↥L).map L.subtype := by rw [← hQ]; exact hchar hc'
    obtain ⟨c0, hc0, hcc⟩ := h1
    rwa [← Subtype.ext hcc]
  · refine CGT.PushingUpLit.oResidualTwo_eq_top_iff.2 fun N hN hpow => ?_
    exact hres N ((CGT.PushingUpLit.isPGroup_two_quotient_iff N).2 hpow)
  · rcases htype with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; exact Nat.prime_three)
  · refine CGT.PushingUpLit.shortU_le_center_iff.2 fun u hu => ?_
    have hu' : (u : G) ∈ QuasithinUnique.blockU L := by
      rw [← hU]; exact Subgroup.mem_map_of_mem _ hu
    have hu2 := hUQ hu'
    have hmem : (u : G) ∈ (CFSG.pCore 2 ↥L).map L.subtype := by rw [← hQ]; exact hu2.1
    obtain ⟨u0, hu0, hu0e⟩ := hmem
    refine ⟨by rwa [← Subtype.ext hu0e], fun r hr => Subtype.ext ?_⟩
    have hr' : (r : G) ∈ blockQ L := by rw [hQ]; exact Subgroup.mem_map_of_mem _ hr
    exact (Subgroup.mem_centralizer_iff.mp hu2.2 r hr').symm
  · rw [← Subgroup.map_lt_map_iff_of_injective L.subtype_injective, hU, hC]
    exact hlt
  · intro N hN hNU hCN
    have hNU' : N.map L.subtype ≤ QuasithinUnique.blockU L := by
      rw [← hU]; exact Subgroup.map_mono hNU
    have hCN' : QuasithinUnique.blockZ L ≤ N.map L.subtype := by
      rw [← hC]; exact Subgroup.map_mono hCN
    have hLN : L ≤ Subgroup.normalizer (N.map L.subtype : Set G) := by
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨k, hk⟩ * n * ⟨k, hk⟩⁻¹, hN.conj_mem n hn _, rfl⟩
      · rintro ⟨n, hn, hne⟩
        have hx : x ∈ L := by
          have h1 : k * x * k⁻¹ ∈ L := hne ▸ n.2
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem hk) h1) hk
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have h2 := hN.conj_mem n hn ⟨k, hk⟩⁻¹
        have e : (⟨k, hk⟩⁻¹ * n * (⟨k, hk⟩⁻¹)⁻¹ : ↥L) = ⟨x, hx⟩ := by
          have hn' : (n : G) = k * x * k⁻¹ := hne
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, hn']
          group
        rwa [e] at h2
    rcases hirr _ hCN' hNU' hLN with h | h
    · left
      apply Subgroup.map_injective L.subtype_injective
      rw [h, hC]
    · right
      apply Subgroup.map_injective L.subtype_injective
      rw [h, hU]

theorem inClassX_of_inClassXBlock {L : Subgroup G} (h : InClassXBlock L) : InClassX ↥L := by
  obtain ⟨hshort, ⟨n, hn, hlin⟩ | ⟨n, hn, halt⟩⟩ := h
  · exact ⟨isShortGroup_of_isShort2 hshort,
      Or.inr ⟨n, hn, isNaturalSLTwoModule_of_isLin2Type (by omega) hlin⟩⟩
  · exact ⟨isShortGroup_of_isShort2 hshort, Or.inl ⟨n, hn, isNaturalAltModule_of_isAltType halt⟩⟩

theorem card_specialLinearGroup_galoisField_two_one :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 :=
  CFSG.CGT.PushingUp.card_specialLinear_two_galoisField_one

theorem not_isPerfect_of_card_eq_six {Q : Type*} [Group Q] (h : Nat.card Q = 6) :
    ¬ Group.IsPerfect Q := by
  intro hperf
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [h]; norm_num)
  have hN : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hN, h] at this
    omega
  have hle : commutator Q ≤ Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ⁅a, b⁆ = a * b * (a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [key, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  have htop : Subgroup.zpowers x = ⊤ := top_le_iff.mp (hperf.commutator_eq_top ▸ hle)
  have hcard := congrArg (fun H : Subgroup Q => Nat.card H) htop
  simp only [Subgroup.card_top, hN, h] at hcard
  omega

theorem not_isNaturalSLTwoModule_one {X : Type} [Group X] [Finite X] (hX : IsShortGroup X) :
    ¬ IsNaturalSLTwoModule X 1 := by
  rintro ⟨φ, -⟩
  have hcard : Nat.card (X ⧸ CFSG.pCore 2 X) = 6 :=
    (Nat.card_congr φ.toEquiv).trans card_specialLinearGroup_galoisField_two_one
  rcases hX.quotient_type with hq | hq
  · exact not_isPerfect_of_card_eq_six hcard hq.1
  · rw [hcard] at hq
    exact absurd hq (by decide)

theorem not_isLin2Type_one {L : Subgroup G} (hL : IsShort2 L) : ¬ IsLin2Type L 1 := fun h =>
  not_isNaturalSLTwoModule_one (isShortGroup_of_isShort2 hL)
    (isNaturalSLTwoModule_of_isLin2Type one_ne_zero h)

omit [Finite G] in
theorem isMaximalTwoLocal_of_glb {M : Subgroup G} (hM : CFSG.Open.GLBIsMaxTwoLocal M) :
    CFSG.IsMaximalTwoLocal M :=
  ⟨hM.1, fun H hlt hH => hlt.ne (hM.2 H hH hlt.le).symm⟩

omit [Finite G] in
theorem isSubnormal_subgroupOf_of_open {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

omit [Finite G] in
theorem assembly_isCharTwoType_of_open (h : CFSG.Open.IsCharTwoType G) :
    CFSG.Assembly.IsCharTwoType G :=
  h

theorem open_evenRank_eq : CFSG.Open.evenRank G = CFSG.Assembly.evenRank G := rfl

theorem sectionalTwoRankLE_four_of_eq {X : Type*} [Group X]
    (h : CFSG.GH74.sectionalTwoRank X = 4) : CFSG.GH74.SectionalTwoRankLE X 4 := by
  rw [CFSG.GH74.sectionalTwoRank] at h
  have hmem := Nat.sInf_mem (Nat.nonempty_of_pos_sInf (s := {r | CFSG.GH74.SectionalTwoRankLE X r})
    (by omega))
  rw [h] at hmem
  exact hmem

end CFSG.AGLEmbedding.NoXBlock
