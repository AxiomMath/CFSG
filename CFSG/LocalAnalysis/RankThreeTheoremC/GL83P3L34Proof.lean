module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34R1Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6Point
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5MComp
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDiag
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedComponentStructure
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFusion
import CFSG.LocalAnalysis.RankFourTheoremC.PPointEndgameAux
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.Walter.W67.W1Basic
import CFSG.RankThree.PartOne.D4RC.Burnside
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTwoGroupAssembly
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Borel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Graph
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34OuterProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34TwoSigProved

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace GL83P3L34Aux

theorem normalizer_of_lwc {x : G} {Q : Subgroup G} (h : LineWeaklyClosed x Q)
    {g : G} (hg : g * x * g⁻¹ ∈ Q) : g ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hg
  exact mem_normalizer_iff_map_conj_eq.mpr (h g hle)

theorem fusion [Fact (Nat.Prime 3)] {P : Sylow 3 G} {x : G} (hx3 : x ^ 3 = 1)
    (hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G))
    (hwc : LineWeaklyClosed x (P : Subgroup G)) {a g : G} (haP : a ∈ (P : Subgroup G))
    (hb : g * a * g⁻¹ ∈ (P : Subgroup G)) :
    ∃ n ∈ normalizer ((zpowers x : Subgroup G) : Set G), g * a * g⁻¹ = n * a * n⁻¹ := by
  set b : G := g * a * g⁻¹ with hbdef
  set y : G := g * x * g⁻¹ with hydef
  have hxa : a * x = x * a := mem_centralizer_singleton_iff.mp (hPC haP)
  have hxb : b * x = x * b := mem_centralizer_singleton_iff.mp (hPC hb)
  have hyb : b * y = y * b := by
    calc b * y = g * (a * x) * g⁻¹ := by simp only [hbdef, hydef]; group
      _ = g * (x * a) * g⁻¹ := by rw [hxa]
      _ = y * b := by simp only [hbdef, hydef]; group
  set C : Subgroup G := centralizer ({b} : Set G) with hC
  have hxC : x ∈ C := mem_centralizer_singleton_iff.mpr hxb.symm
  have hyC : y ∈ C := mem_centralizer_singleton_iff.mpr hyb.symm
  have hxp : IsPGroup 3 (zpowers x) :=
    elementary_isPGroup 3 _ (CFSG.AGLEmbedding.isElemAbelian_zpowers hx3)
  have hy3 : y ^ 3 = 1 := by simp only [hydef]; rw [conj_pow, hx3]; simp
  have hyp : IsPGroup 3 (zpowers y) :=
    elementary_isPGroup 3 _ (CFSG.AGLEmbedding.isElemAbelian_zpowers hy3)
  obtain ⟨Q₁, hQ₁⟩ := (hxp.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := (hyp.comap_subtype (K := C)).exists_le_sylow
  set R₁ : Subgroup G := (Q₁ : Subgroup C).map C.subtype with hR₁
  set R₂ : Subgroup G := (Q₂ : Subgroup C).map C.subtype with hR₂
  have hR₁syl : IsSylowOf 3 R₁ C := ⟨Q₁, rfl⟩
  have hR₂syl : IsSylowOf 3 R₂ C := ⟨Q₂, rfl⟩
  have hxR₁ : x ∈ R₁ := ⟨⟨x, hxC⟩, hQ₁ (mem_zpowers x), rfl⟩
  have hyR₂ : y ∈ R₂ := ⟨⟨y, hyC⟩, hQ₂ (mem_zpowers y), rfl⟩
  obtain ⟨k, hkC, hk⟩ := hR₁syl.exists_mem_conj hR₂syl
  have hky : k⁻¹ * y * k ∈ R₁ := (hk y).mp hyR₂
  obtain ⟨S, hS⟩ := hR₁syl.isPGroup.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P S
  have key : ∀ z : G, z ∈ (S : Subgroup G) ↔ h⁻¹ * z * h ∈ (P : Subgroup G) := by
    intro z
    rw [← hh]
    change z ∈ MulAut.conj h • (P : Subgroup G) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  have hxS : x ∈ (S : Subgroup G) := hS hxR₁
  have hkyS : k⁻¹ * y * k ∈ (S : Subgroup G) := hS hky
  have hh1 : h⁻¹ ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    refine normalizer_of_lwc hwc ?_
    rw [inv_inv]
    exact (key x).mp hxS
  have hh2 : h⁻¹ * k⁻¹ * g ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    refine normalizer_of_lwc hwc ?_
    have e : (h⁻¹ * k⁻¹ * g) * x * (h⁻¹ * k⁻¹ * g)⁻¹ = h⁻¹ * (k⁻¹ * y * k) * h := by
      simp only [hydef]
      group
    rw [e]
    exact (key _).mp hkyS
  have hn : k⁻¹ * g ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    have hh1' : h ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
      simpa using Subgroup.inv_mem _ hh1
    have e : h * (h⁻¹ * k⁻¹ * g) = k⁻¹ * g := by group
    rw [← e]
    exact Subgroup.mul_mem _ hh1' hh2
  refine ⟨k⁻¹ * g, hn, ?_⟩
  have hkb : k⁻¹ * b = b * k⁻¹ := mem_centralizer_singleton_iff.mp (Subgroup.inv_mem _ hkC)
  calc b = k⁻¹ * b * k := by rw [hkb]; group
    _ = k⁻¹ * g * a * (k⁻¹ * g)⁻¹ := by rw [hbdef]; group

theorem strongClosed (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    (h34 : L34Prop34 3 P J x) :
    ∀ a ∈ (P : Subgroup G) ⊓ J, ∀ g : G, g * a * g⁻¹ ∈ (P : Subgroup G) →
      g * a * g⁻¹ ∈ (P : Subgroup G) ⊓ J := by
  intro a ha g hg
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPC, hEel, -, -, hwc⟩ := h34
  have hAE : (P : Subgroup G) ⊓ J ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x := le_sup_left
  have ha3 : a ^ 3 = 1 := hEel.2 a (hAE ha)
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, mul_inv_cancel]
    exact one_mem _
  obtain ⟨u', hu', hun⟩ := fusion hx3 hPC hwc ha.1 hg
  set u : G := u'⁻¹ with hudef
  have hu : u ∈ normalizer ((zpowers x : Subgroup G) : Set G) := Subgroup.inv_mem _ hu'
  have hbu : g * a * g⁻¹ = u⁻¹ * a * u := by rw [hun, hudef]; simp
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hJ.le_centralizer
  have hux : u * x * u⁻¹ ∈ zpowers x := (mem_normalizer_iff.mp hu x).mp (mem_zpowers x)
  have hnC : ∀ c ∈ C, u⁻¹ * c * u ∈ C := by
    intro c hc
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hux
    have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc
    have hcy : c * (u * x * u⁻¹) = (u * x * u⁻¹) * c := by
      rw [← hk]
      have : Commute c x := hcx
      exact (Commute.zpow_right this k).eq
    refine mem_centralizer_singleton_iff.mpr ?_
    calc u⁻¹ * c * u * x = u⁻¹ * (c * (u * x * u⁻¹)) * u := by group
      _ = u⁻¹ * ((u * x * u⁻¹) * c) * u := by rw [hcy]
      _ = x * (u⁻¹ * c * u) := by group
  have hCmap : C.map (MulAut.conj u⁻¹).toMonoidHom = C := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨c, hc, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hnC c hc
    · rw [Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective]
  set ψ : C ≃* C := ((MulAut.conj u⁻¹).subgroupMap C).trans (MulEquiv.subgroupCongr hCmap)
    with hψ
  have hψval : ∀ c : C, (ψ c : G) = u⁻¹ * c * u := fun c => by
    show ((MulAut.conj u⁻¹).subgroupMap C c : G) = u⁻¹ * c * u
    rw [MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply, inv_inv]
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOψ : O.map ψ.toMonoidHom = O :=
    Subgroup.characteristic_iff_map_eq.mp (primeComplementCore_characteristic 3) ψ
  set ψb : C ⧸ O ≃* C ⧸ O := QuotientGroup.congr O O ψ hOψ with hψb
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  have hψbπ : ∀ c, ψb (π c) = π (ψ c) := fun c => QuotientGroup.congr_mk' O O ψ hOψ c
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  have hLn : L.Normal := r1sBar_normal_l34 hJ
  set L' : Subgroup (C ⧸ O) := L.map ψb.toMonoidHom with hL'
  have hL'n : L'.Normal := hLn.map ψb.toMonoidHom ψb.surjective
  have haC : a ∈ C := hJC ha.2
  have hbC : u⁻¹ * a * u ∈ C := hnC a haC
  have hbL' : π ⟨u⁻¹ * a * u, hbC⟩ ∈ L' := by
    refine ⟨π ⟨a, haC⟩, ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha.2, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, hψbπ]
    congr 1
    exact Subtype.ext (hψval _)
  have haπ : π ⟨a, haC⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨a, haC⟩ : C) ∈ O := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : orderOf (⟨a, haC⟩ : C) ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨⟨a, haC⟩, h2⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    have h4 : orderOf (⟨a, haC⟩ : C) ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ha3)
    have h5 : orderOf (⟨a, haC⟩ : C) = 1 :=
      Nat.eq_one_of_dvd_coprimes (primeComplementCore_coprime 3) h4 h3
    apply ha1
    have := orderOf_eq_one_iff.mp h5
    exact congrArg Subtype.val this
  have haL : π ⟨a, haC⟩ ∈ L := ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.mpr ha.2, rfl⟩
  have hLL' : L' = L := by
    have hcard : Nat.card L' = Nat.card L := Subgroup.card_map_of_injective ψb.injective
    have := hLn
    have := hL'n
    have hsimple := l34cm_isSimpleGroup hJ
    have hN : ((L' ⊓ L).subgroupOf L).Normal := inferInstance
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L' ⊓ L).subgroupOf L) with h | h
    · exfalso
      have hdis : Disjoint L' L := by
        rw [Subgroup.disjoint_def]
        intro z hz1 hz2
        have hz : (⟨z, hz2⟩ : L) ∈ (L' ⊓ L).subgroupOf L :=
          Subgroup.mem_subgroupOf.mpr ⟨hz1, hz2⟩
        rw [h] at hz
        exact congrArg Subtype.val (Subgroup.mem_bot.mp hz)
      have hL'C : L' ≤ reducedCentralizerOfJ x J := by
        intro w hw
        rw [r1s_reducedCentralizerOfJ_eq, mem_centralizer_iff]
        intro v hv
        exact (Subgroup.commute_of_normal_of_disjoint L' L hL'n hLn hdis w v hw hv).eq.symm
      have hcyc := l34_reducedCentralizer_isCyclic hS hU0 hK1 hK2 hp hM hgen hJ
      let _ : CommGroup ↥(reducedCentralizerOfJ x J) := hcyc.commGroup
      have hLc : ∀ w ∈ L, ∀ v ∈ L, w * v = v * w := by
        intro w hw v hv
        apply ψb.injective
        rw [map_mul, map_mul]
        have hw' : ψb w ∈ reducedCentralizerOfJ x J := hL'C ⟨w, hw, rfl⟩
        have hv' : ψb v ∈ reducedCentralizerOfJ x J := hL'C ⟨v, hv, rfl⟩
        exact congrArg Subtype.val
          (mul_comm (⟨_, hw'⟩ : ↥(reducedCentralizerOfJ x J)) ⟨_, hv'⟩)
      have hper := r1sBar_perfect_l34 hJ
      have htop : _root_.commutator ↥L = ⊤ := Group.isPerfect_def.mp hper
      have hbot : _root_.commutator ↥L = ⊥ := by
        rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro w _
        rw [mem_centralizer_iff]
        intro v _
        exact Subtype.ext (hLc _ v.2 _ w.2)
      have h1 : (⟨π ⟨a, haC⟩, haL⟩ : L) ∈ _root_.commutator ↥L := by
        rw [htop]
        exact Subgroup.mem_top _
      rw [hbot, Subgroup.mem_bot] at h1
      exact haπ (congrArg Subtype.val h1)
    · have hle : L ≤ L' := fun z hz => by
        have hz' : (⟨z, hz⟩ : L) ∈ (L' ⊓ L).subgroupOf L := by
          rw [h]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hz').1
      exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hbL : π ⟨u⁻¹ * a * u, hbC⟩ ∈ L := by rw [← hLL']; exact hbL'
  have hb3 : (u⁻¹ * a * u) ^ 3 = 1 := by
    rw [show u⁻¹ * a * u = u⁻¹ * a * u⁻¹⁻¹ by rw [inv_inv], conj_pow, ha3, mul_one,
      mul_inv_cancel]
  have hbJ : u⁻¹ * a * u ∈ J := r1s_mem_of_mk_mem_l34 hJ hbC hb3 hbL
  refine ⟨hg, ?_⟩
  rw [hbu]
  exact hbJ

theorem exists_conj_le_of_isPGroup {P : Sylow 3 G} {O K₁ : Subgroup G}
    (hPO : (P : Subgroup G) ≤ normalizer (O : Set G)) (hK₁p : IsPGroup 3 K₁)
    (hK₁W : K₁ ≤ (P : Subgroup G) ⊔ O) :
    ∃ o ∈ O, ∀ y ∈ K₁, o * y * o⁻¹ ∈ (P : Subgroup G) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hPsylW : IsSylowOf 3 (P : Subgroup G) ((P : Subgroup G) ⊔ O) :=
    isSylowOf_iff.mpr ⟨le_sup_left, P.isPGroup', fun hdvd => P.not_dvd_index
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))⟩
  set W : Subgroup G := (P : Subgroup G) ⊔ O
  obtain ⟨Q, hQ⟩ := (hK₁p.comap_subtype (K := W)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup W).map W.subtype
  have hTsyl : IsSylowOf 3 T W := ⟨Q, rfl⟩
  have hK₁T : K₁ ≤ T := fun y hy => ⟨⟨y, hK₁W hy⟩, hQ hy, rfl⟩
  obtain ⟨k, hkW, hk⟩ := hTsyl.exists_mem_conj hPsylW
  have hkmul : k ∈ ((P : Subgroup G) : Set G) * (O : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (P : Subgroup G) O hPO]
    exact hkW
  obtain ⟨p, hpP, o, hoO, rfl⟩ := hkmul
  refine ⟨o, hoO, fun y hy => ?_⟩
  have h1 : (p * o)⁻¹ * (p * o * y * (p * o)⁻¹) * (p * o) ∈ T := by
    rw [show (p * o)⁻¹ * (p * o * y * (p * o)⁻¹) * (p * o) = y by group]
    exact hK₁T hy
  have h2 : p * o * y * (p * o)⁻¹ ∈ (P : Subgroup G) := (hk _).mpr h1
  have h3 : o * y * o⁻¹ = p⁻¹ * (p * o * y * (p * o)⁻¹) * p := by group
  rw [h3]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hpP) h2) hpP

theorem normalizer_of_conj {P : Sylow 3 G} {M K₀ : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hK₀P : K₀ ≤ (P : Subgroup G)) (hK₀p : IsPGroup 3 K₀)
    (hconj : ∀ m ∈ M, ∀ q ∈ K₀, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M)
    (hSC : ∀ a ∈ K₀, ∀ g : G, g * a * g⁻¹ ∈ (P : Subgroup G) → g * a * g⁻¹ ∈ K₀) :
    M ≤ normalizer ((K₀ ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G) := by
  have hMO : M ≤ normalizer (GLBPrimeCore 3 M : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M
  have hK₀M : K₀ ≤ M := hK₀P.trans hPM
  have hPO : (P : Subgroup G) ≤ normalizer (GLBPrimeCore 3 M : Set G) := hPM.trans hMO
  have hstar : ∀ m ∈ M, ∀ a ∈ K₀, m * a * m⁻¹ ∈ K₀ ⊔ GLBPrimeCore 3 M := by
    intro m hm a ha
    set O : Subgroup G := GLBPrimeCore 3 M
    set K₁ : Subgroup G := K₀.map (MulAut.conj m).toMonoidHom
    have hK₁W : K₁ ≤ (P : Subgroup G) ⊔ O := by
      rintro _ ⟨k, hk, rfl⟩
      exact hconj m hm k hk
    have hK₁p : IsPGroup 3 K₁ := hK₀p.map (MulAut.conj m).toMonoidHom
    obtain ⟨o, hoO, hoy⟩ := exists_conj_le_of_isPGroup hPO hK₁p hK₁W
    have hg : (o * m) * a * (o * m)⁻¹ ∈ K₀ := by
      refine hSC a ha (o * m) ?_
      have h1 := hoy (m * a * m⁻¹) ⟨a, ha, rfl⟩
      rw [show (o * m) * a * (o * m)⁻¹ = o * (m * a * m⁻¹) * o⁻¹ by group]
      exact h1
    obtain ⟨a', ha'K, ha'eq⟩ : ∃ a' ∈ K₀, a' = (o * m) * a * (o * m)⁻¹ := ⟨_, hg, rfl⟩
    have hmam : m * a * m⁻¹ = o⁻¹ * a' * o := by
      rw [ha'eq]
      group
    have h4 : a'⁻¹ * o⁻¹ * a' ∈ O := by
      have := (mem_normalizer_iff.mp (hMO (hK₀M (K₀.inv_mem ha'K))) o⁻¹).mp (O.inv_mem hoO)
      simpa using this
    have h5 : o⁻¹ * a' * o = a' * (a'⁻¹ * o⁻¹ * a') * o := by group
    rw [hmam, h5]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_sup_left ha'K) (mem_sup_right h4))
      (mem_sup_right hoO)
  have hmap : ∀ m ∈ M, ∀ y ∈ K₀ ⊔ GLBPrimeCore 3 M, m * y * m⁻¹ ∈ K₀ ⊔ GLBPrimeCore 3 M := by
    intro m hm y hy
    have hle : (K₀ ⊔ GLBPrimeCore 3 M).map (MulAut.conj m).toMonoidHom ≤
        K₀ ⊔ GLBPrimeCore 3 M := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨k, hk, rfl⟩
        exact hstar m hm k hk
      · rintro _ ⟨o', ho', rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hMO hm) o').mp ho')
    exact hle ⟨y, hy, rfl⟩
  intro m hm
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hmap m hm y hy, fun hy => ?_⟩
  have h1 := hmap m⁻¹ (M.inv_mem hm) _ hy
  have e : m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y := by group
  rwa [e] at h1

theorem point_facts (hS : Setting G) (hU0 : FullCoreLocal G) (hK2 : KFactL34Three)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J)
    (hDel : IsElemAbelian 3 ((P : Subgroup G) ⊓ J))
    (hDcard : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2) :
    GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M ∧
      M ⊓ centralizer ({x} : Set G) ≤
        normalizer ((((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 (centralizer ({x} : Set G)) :
          Subgroup G) : Set G) := by
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hOxM : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M :=
    (glbPrimeCore_le_pPrimeCoreIn 3 _).trans (pPrimeCoreIn_centralizer_le hS hp hM hgen.2.2.2.ge)
  refine ⟨hOxM, ?_⟩
  obtain ⟨Sbar, hSbar, hsh⟩ := exists_genericShadow3 hS hU0 hp rfl hM hgen
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hJ.le_centralizer
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  set π : C →* C ⧸ O := QuotientGroup.mk' O with hπ
  set Q' : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQ'
  have hQ'p : IsPGroup 3 Q' := (P.isPGroup'.to_le inf_le_left).comap_subtype
  set L : Subgroup (C ⧸ O) := r1sBar x J with hL
  have hLn : L.Normal := r1sBar_normal_l34 hJ
  set D' : Subgroup C := ((P : Subgroup G) ⊓ J).subgroupOf C with hD'
  have hD'Q : D' ≤ Q' := fun a ha =>
    Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp ha).1, hJC (Subgroup.mem_subgroupOf.mp ha).2⟩
  have hD'p : IsPGroup 3 D' := hQ'p.to_le hD'Q
  set Db : Subgroup (C ⧸ O) := D'.map π with hDb
  set Γ : Subgroup (C ⧸ O) := ((C ⊓ M).subgroupOf C).map π with hΓdef
  have hSylJ : IsSylowOf 3 ((P : Subgroup G) ⊓ J) J := by
    have h := hgen.2.2.1.inf_of_le_normalizer hJC hJ.centralizer_le
    have hPJ : ((P : Subgroup G) ⊓ C) ⊓ J = (P : Subgroup G) ⊓ J := by
      rw [inf_assoc, inf_eq_right.mpr hJC]
    rwa [hPJ] at h
  obtain ⟨TJ, hTJ⟩ := hSylJ
  set S : Sylow 3 ↥L := TJ.mapSurjective (r1sHom_surjective x hJC) with hS'
  have hSmap : (S : Subgroup ↥L).map L.subtype = Db := by
    rw [hS', Sylow.coe_mapSurjective, Subgroup.map_map, hDb, hD', ← hTJ]
    have h1 : ((TJ : Subgroup ↥J).map J.subtype).subgroupOf C =
        (TJ : Subgroup ↥J).map (Subgroup.inclusion hJC) := by
      ext c
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨j, hj, hjc⟩
        exact ⟨j, hj, Subtype.ext hjc⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
    rw [h1, Subgroup.map_map]
    rfl
  have hDbL : Db ≤ L := by
    rw [← hSmap]
    exact Subgroup.map_subtype_le _
  have hDbS : Db ≤ (Sbar : Subgroup (C ⧸ O)) := by
    rw [hSbar]
    exact Subgroup.map_mono fun a ha => Subgroup.mem_subgroupOf.mpr
      ⟨(Subgroup.mem_subgroupOf.mp ha).1, a.2⟩
  have hDbcard : Nat.card Db = 3 ^ 2 := by
    rw [hDb, CFSG.AGLEmbedding.card_map_mk_of_isPGroup Nat.prime_three O hOcop hD'p,
      hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hJC)).toEquiv, hDcard]
  have hDbel : IsElemAbelian 3 Db := by
    have hcomm := hDel.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨a', ha', ha'π⟩ := a.2
      obtain ⟨b', hb', hb'π⟩ := b.2
      apply Subtype.ext
      show (a : C ⧸ O) * b = b * a
      rw [← ha'π, ← hb'π, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (setLike_mul_comm (Subgroup.mem_subgroupOf.mp ha')
        (Subgroup.mem_subgroupOf.mp hb')))
    · obtain ⟨z', hz', rfl⟩ := hz
      rw [← map_pow]
      have : z' ^ 3 = 1 :=
        Subtype.ext (by simpa using hDel.2 (z' : G) (Subgroup.mem_subgroupOf.mp hz'))
      rw [this, map_one]
  have hDb2 : 2 ≤ CFSG.Open.pRank 3 Db :=
    le_pRank_of_elemAbelian_card (p := 3) (k := 2) le_rfl hDbel hDbcard
  have hNΓ : normalizer (Db : Set (C ⧸ O)) ≤ Γ := hsh.normalizer_le Db hDbS hDb2
  have hLΓ : ¬ L ≤ Γ := by
    intro hle
    apply hJ.not_le
    intro j hj
    have hjL : π ⟨j, hJC hj⟩ ∈ L := ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
    obtain ⟨c, hc, hcπ⟩ := hle hjL
    have hco : c⁻¹ * ⟨j, hJC hj⟩ ∈ O := QuotientGroup.eq.mp hcπ
    have hOx : ((c⁻¹ * ⟨j, hJC hj⟩ : C) : G) ∈ GLBPrimeCore 3 C :=
      (CFSG.AGLEmbedding.mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mp hco
    have hcM : (c : G) ∈ M := (Subgroup.mem_subgroupOf.mp hc).2
    have e : j = (c : G) * ((c⁻¹ * ⟨j, hJC hj⟩ : C) : G) := by
      change j = (c : G) * ((c : G)⁻¹ * j)
      group
    rw [e]
    exact M.mul_mem hcM (hOxM hOx)
  have hmaxS := (hK2 ↥L (r1sBar_isL34 hJ) S).2.2.1 (Γ.comap L.subtype) (by
    intro n hn
    have h1 := Subgroup.le_normalizer_map L.subtype ⟨n, hn, rfl⟩
    rw [hSmap] at h1
    exact hNΓ h1)
  have hΓL : ∀ g ∈ Γ, ∀ hgL : g ∈ L,
      (⟨g, hgL⟩ : ↥L) ∈ normalizer ((S : Subgroup ↥L) : Set ↥L) := by
    intro g hg hgL
    rcases hmaxS with h | h
    · have : (⟨g, hgL⟩ : ↥L) ∈ Γ.comap L.subtype := hg
      rwa [h] at this
    · exfalso
      apply hLΓ
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ Γ.comap L.subtype := by rw [h]; exact Subgroup.mem_top _
      exact this
  have hSsyl : IsSylowOf 3 (S : Subgroup ↥L) ⊤ := by
    refine isSylowOf_iff.mpr ⟨le_top, S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  have hΓS : ∀ g ∈ Γ, ∀ s ∈ Db, g * s * g⁻¹ ∈ Db := by
    intro g hg s hs
    have hsΓ : s ∈ Γ := hNΓ (Subgroup.le_normalizer hs)
    have hgsΓ : g * s * g⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hg hsΓ) (Γ.inv_mem hg)
    have hgsL : g * s * g⁻¹ ∈ L := hLn.conj_mem s (hDbL hs) g
    have hnorm := hΓL _ hgsΓ hgsL
    have hDbp : IsPGroup 3 Db := elementary_isPGroup 3 Db hDbel
    obtain ⟨k, hk⟩ := hDbp ⟨s, hs⟩
    have hk' : s ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have hk3 : (⟨g * s * g⁻¹, hgsL⟩ : ↥L) ^ 3 ^ k = 1 :=
      Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        change (g * s * g⁻¹) ^ 3 ^ k = 1
        rw [conj_pow, hk', mul_one, mul_inv_cancel])
    have hmemS := a6l43_mem_of_normalizer_sylow hSsyl (Subgroup.mem_top _) hnorm hk3
    rw [← hSmap]
    exact ⟨_, hmemS, rfl⟩
  have hOxn : ∀ c ∈ C, ∀ o ∈ GLBPrimeCore 3 C, c * o * c⁻¹ ∈ GLBPrimeCore 3 C :=
    fun c hc o ho => (mem_normalizer_iff.mp
      (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 C hc) o).mp ho
  have hDOx : ∀ c ∈ M ⊓ C, ∀ d ∈ (P : Subgroup G) ⊓ J,
      c * d * c⁻¹ ∈ ((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 C := by
    intro c hc d hd
    have hcC : c ∈ C := hc.2
    have hdC : d ∈ C := hJC hd.2
    set cC : C := ⟨c, hcC⟩ with hcC'
    set dC : C := ⟨d, hdC⟩ with hdC'
    have hcΓ : π cC ∈ Γ := ⟨cC, Subgroup.mem_subgroupOf.mpr ⟨hcC, hc.1⟩, rfl⟩
    have hdSL : π dC ∈ Db := ⟨dC, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    have h1 := hΓS _ hcΓ _ hdSL
    obtain ⟨d', hd', hd'π⟩ := h1
    have hd'π' : π d' = π (cC * dC * cC⁻¹) := by
      rw [hd'π, map_mul, map_mul, map_inv]
    have hco : d'⁻¹ * (cC * dC * cC⁻¹) ∈ O := QuotientGroup.eq.mp hd'π'
    have hOx : ((d'⁻¹ * (cC * dC * cC⁻¹) : C) : G) ∈ GLBPrimeCore 3 C :=
      (CFSG.AGLEmbedding.mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mp hco
    have hd'D : (d' : G) ∈ (P : Subgroup G) ⊓ J := Subgroup.mem_subgroupOf.mp hd'
    have hprod : (d' : G) * ((d'⁻¹ * (cC * dC * cC⁻¹) : C) : G) = c * d * c⁻¹ := by
      change (d' : G) * ((d' : G)⁻¹ * (c * d * c⁻¹)) = c * d * c⁻¹
      exact mul_inv_cancel_left _ _
    rw [← hprod]
    exact Subgroup.mul_mem_sup hd'D hOx
  refine Subgroup.le_normalizer_iff.mpr fun c hc k hk => ?_
  have hmap : (((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 C).map (MulAut.conj c).toMonoidHom ≤
      ((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 C := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨d, hd, rfl⟩
      exact hDOx c hc d hd
    · rintro _ ⟨o, ho, rfl⟩
      exact Subgroup.mem_sup_right (hOxn c hc.2 o ho)
  exact hmap ⟨k, hk, rfl⟩

section Quotient

open CFSG.LocalAnalysis.RankFourTheoremC

theorem pCore_map_le_pCore_of_isSubnormal {H : Type*} [Group H] (p : ℕ) {K : Subgroup H}
    (hK : K.IsSubnormal) : (CFSG.pCore p K).map K.subtype ≤ CFSG.pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ normalizer (X : Set H) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using CFSG.Walter.conj_mem_map_of_characteristic (hYN y.2) hl
      · exact ((CFSG.pCore_isPGroup (p := p) (G := X)).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hK with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => CFSG.Walter.conj_mem_map_of_characteristic ?_ hl⟩,
      (CFSG.pCore_isPGroup (p := p) (G := (⊤ : Subgroup H))).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

structure Hyp (Y : Type) [Group Y] [Finite Y] (x : Y) : Prop where
  core_eq_bot : primeComplementCore (G := Y) 3 = ⊥
  catalog : CatalogSimpleSections Y
  omega : ∀ R : Sylow 3 Y, ∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y),
    a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a
  rank : ∀ R : Sylow 3 Y, ∀ B : Subgroup Y, B ≤ (R : Subgroup Y) → IsElemAbelian 3 B →
    Nat.card B ≤ 3 ^ 3
  center_eq_bot : ∀ K : Subgroup Y, IsComponentOf K ⊤ → center K = ⊥
  ne_one : x ≠ 1
  pow_eq_one : x ^ 3 = 1
  weakClosed : ∀ Q : Sylow 3 Y, x ∈ (Q : Subgroup Y) → ∀ g : Y,
    (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup Y) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

namespace Hyp

variable {Y : Type} [Group Y] [Finite Y] {x : Y} {K : Subgroup Y}

theorem le_centralizer_of_mem (h : Hyp Y x) {Q : Sylow 3 Y} (hxQ : x ∈ (Q : Subgroup Y)) :
    (Q : Subgroup Y) ≤ centralizer ({x} : Set Y) := by
  intro q hq
  have hle : (zpowers x).map (MulAut.conj q).toMonoidHom ≤ (Q : Subgroup Y) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hq hxQ) (Subgroup.inv_mem _ hq)
  have h1 : q * x * q⁻¹ ∈ zpowers x := by
    have := h.weakClosed Q hxQ q hle
    rw [← this, MonoidHom.map_zpowers]
    exact mem_zpowers _
  obtain ⟨m, hm⟩ := Q.isPGroup' ⟨q, hq⟩
  have hqm : q ^ (3 ^ m) = 1 := congrArg Subtype.val hm
  have := p34_conj_eq_of_pow h.ne_one h.pow_eq_one hqm h1
  exact mem_centralizer_singleton_iff.mpr (by
    calc q * x = q * x * q⁻¹ * q := by group
      _ = x * q := by rw [this])

theorem exists_order_three (h : Hyp Y x) (hK : IsComponentOf K ⊤) :
    ∃ t ∈ K, orderOf t = 3 ∧ t ∉ centralizer (K : Set Y) := by
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow 3 Y))
  obtain ⟨t, htRK, hto, htC⟩ :=
    exists_mem_sylow_inf_component Nat.prime_three (by norm_num) h.core_eq_bot R hK
  exact ⟨t, htRK.2, hto, htC⟩

theorem mem_normalizer_of_pow_three (h : Hyp Y x) (hK : IsComponentOf K ⊤) {y : Y}
    (hy : y ^ 3 = 1) : y ∈ normalizer (K : Set Y) := by
  classical
  by_contra hyK
  obtain ⟨t, htK, hto, htC⟩ := h.exists_order_three hK
  have ht3 : t ^ 3 = 1 := hto ▸ pow_orderOf_eq_one t
  set f : ℕ → Subgroup Y := fun i => K.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (y ^ i)) K).mpr hK
  have key : ∀ i j : ℕ, i < j → j < 3 → f i ≠ f j := by
    intro i j hij hj hfij
    apply hyK
    refine mem_normalizer_of_pow_mem Nat.prime_three hy (m := j - i) ?_ ?_
    · exact (Nat.coprime_of_lt_prime (by omega) (by omega) Nat.prime_three).symm
    · rw [mem_normalizer_iff_map_conj_eq]
      have h1 : f j = (f (j - i)).map (MulAut.conj (y ^ i)).toMonoidHom := by
        simp only [hf]
        rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
          Nat.add_sub_cancel' hij.le]
      rw [h1] at hfij
      exact (map_injective (MulAut.conj (y ^ i)).injective hfij).symm
  have hKK : ∀ i j : Fin 3, i ≠ j → f i.val ≤ centralizer (f j.val : Set Y) := by
    intro i j hij
    have hne : f i.val ≠ f j.val := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h' | h'
      · exact key _ _ h' j.2
      · exact (key _ _ h' i.2).symm
    exact commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hfK _) (hfK _) hne)
  set tt : ℕ → Y := fun i => y ^ i * t * (y ^ i)⁻¹ with htt
  have htt_succ : ∀ n, y * tt n * y⁻¹ = tt (n + 1) := by
    intro n
    simp only [htt, pow_succ']
    group
  have htt_mod : ∀ n, tt (n % 3) = tt n := by
    intro n
    simp only [htt]
    rw [← pow_eq_pow_mod n hy]
  have htp : ∀ i : Fin 3, tt i.val ^ 3 = 1 := by
    intro i
    simp only [htt]
    rw [conj_pow, ht3]
    simp
  have htKi : ∀ i : Fin 3, tt i.val ∈ f i.val := fun i => ⟨t, htK, rfl⟩
  have htCi : ∀ i : Fin 3, tt i.val ∉ centralizer (f i.val : Set Y) := by
    intro i hi
    apply htC
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := mem_centralizer_iff.mp hi (y ^ i.val * k * (y ^ i.val)⁻¹) ⟨k, hk, rfl⟩
    have h2 : y ^ i.val * (k * t) * (y ^ i.val)⁻¹ = y ^ i.val * (t * k) * (y ^ i.val)⁻¹ := by
      calc y ^ i.val * (k * t) * (y ^ i.val)⁻¹
          = (y ^ i.val * k * (y ^ i.val)⁻¹) * tt i.val := by simp only [htt]; group
        _ = tt i.val * (y ^ i.val * k * (y ^ i.val)⁻¹) := h1
        _ = y ^ i.val * (t * k) * (y ^ i.val)⁻¹ := by simp only [htt]; group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨hE, -⟩ := isElemAbelian_iSup_zpowers (Y := Y) Nat.prime_three
    (fun i : Fin 3 => f i.val) (fun i : Fin 3 => tt i.val) htp htKi htCi hKK Finset.univ
  set B : Subgroup Y := ⨆ i ∈ (Finset.univ : Finset (Fin 3)), zpowers (tt i.val) with hB
  have hval : ∀ i : Fin 3, ((i + 1 : Fin 3) : ℕ) = (i.val + 1) % 3 := by
    intro i
    fin_cases i <;> rfl
  have hyB : y ∈ normalizer (B : Set Y) := by
    refine mem_normalizer_of_map_conj_le ?_
    simp only [hB, Subgroup.map_iSup]
    refine iSup₂_le fun i _ => ?_
    rw [MonoidHom.map_zpowers]
    have hs : (MulAut.conj y).toMonoidHom (tt i.val) = tt ((i + 1 : Fin 3) : ℕ) := by
      rw [hval, htt_mod]
      exact htt_succ i.val
    rw [hs]
    exact le_iSup₂ (f := fun (j : Fin 3) (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      zpowers (tt j.val)) (i + 1) (Finset.mem_univ _)
  have hBp : IsPGroup 3 B := elementary_isPGroup 3 B hE
  have hyp : IsPGroup 3 (zpowers y) := elementary_isPGroup 3 _ (CFSG.Open.isElemAbelian_zpowers hy)
  have hsup : IsPGroup 3 (zpowers y ⊔ B : Subgroup Y) :=
    hyp.to_sup_of_normal_right' hBp (zpowers_le.mpr hyB)
  obtain ⟨Q, hQ⟩ := hsup.exists_le_sylow
  have hyQ : y ∈ (Q : Subgroup Y) := hQ (mem_sup_left (mem_zpowers y))
  have ht0 : tt 0 = t := by simp [htt]
  have htQ : t ∈ (Q : Subgroup Y) := by
    refine hQ (mem_sup_right ?_)
    rw [← ht0]
    exact le_iSup₂ (f := fun (j : Fin 3) (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      zpowers (tt j.val)) (0 : Fin 3) (Finset.mem_univ _) (mem_zpowers _)
  have hcomm : y * t = t * y := h.omega Q y hyQ t htQ hy (hto ▸ pow_orderOf_eq_one t)
  have ht1 : tt 1 = t := by
    have : tt 1 = y * t * y⁻¹ := by simp [htt]
    rw [this, hcomm]
    group
  have ht1f : t ∈ f 1 := ht1 ▸ htKi 1
  have hf0 : f 0 = K := by
    have h1 : (MulAut.conj (y ^ 0)).toMonoidHom = MonoidHom.id Y := by
      ext g
      simp
    simp only [hf, h1, Subgroup.map_id]
  apply htC
  have := hKK 1 0 (by decide) ht1f
  simpa only [Fin.val_zero, hf0] using this

theorem mem_normalizer_of_mem (h : Hyp Y x) (hK : IsComponentOf K ⊤) (hxK : x ∈ K) {s : Y}
    (hs : s * x * s⁻¹ = x) : s ∈ normalizer (K : Set Y) := by
  by_contra hsK
  have hK' : IsComponentOf (K.map (MulAut.conj s).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj s) K).mpr hK
  have hne : K.map (MulAut.conj s).toMonoidHom ≠ K := fun h' =>
    hsK (mem_normalizer_iff_map_conj_eq.mpr h')
  have hC : K.map (MulAut.conj s).toMonoidHom ≤ centralizer (K : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK' hK hne)
  exact h.ne_one (GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer (h.center_eq_bot K hK) hxK
    (hC ⟨x, hxK, hs⟩))

theorem centralizes_of_le_centralizer (h : Hyp Y x) {Z O : Subgroup Y}
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZN : ∀ z ∈ Z, z ∈ normalizer (K : Set Y))
    (hO3 : ¬ 3 ∣ Nat.card O) (hZC : Z ≤ centralizer ({x} : Set Y))
    (hCO : centralizer ({x} : Set Y) ≤ normalizer (O : Set Y))
    (hCZO : centralizer ({x} : Set Y) ≤ normalizer ((Z ⊔ O : Subgroup Y) : Set Y))
    (hK : IsComponentOf K ⊤) (hKC : K ≤ centralizer ({x} : Set Y)) :
    Z ≤ centralizer (K : Set Y) := by
  set L : Subgroup Y := Z ⊔ O with hL
  have hZO : Z ≤ normalizer (O : Set Y) := fun z hz => hCO (hZC hz)
  have hLset : (L : Set Y) = (Z : Set Y) * (O : Set Y) :=
    coe_mul_of_left_le_normalizer_right Z O hZO
  have hZ := h.center_eq_bot K hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  obtain ⟨t, htK, hto, -⟩ := h.exists_order_three hK
  have h3K : 3 ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨t, htK⟩ : K)
    rwa [Subgroup.orderOf_mk, hto] at this
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b * a⁻¹ * b⁻¹ ∈ O := by
    intro a ha b hb
    rw [← SetLike.mem_coe, hLset] at ha hb
    obtain ⟨z₁, hz₁, o₁, ho₁, rfl⟩ := ha
    obtain ⟨z₂, hz₂, o₂, ho₂, rfl⟩ := hb
    have hzz : z₁ * z₂ = z₂ * z₁ := hZab z₁ hz₁ z₂ hz₂
    have ho₁' : z₂⁻¹ * o₁ * z₂ ∈ O := by
      have := (mem_normalizer_iff.mp (hZO (Z.inv_mem hz₂)) o₁).mp ho₁
      simpa using this
    have ho₂' : z₁⁻¹ * o₂ * z₁ ∈ O := by
      have := (mem_normalizer_iff.mp (hZO (Z.inv_mem hz₁)) o₂).mp ho₂
      simpa using this
    have e1 : (z₁ * o₁) * (z₂ * o₂) = (z₁ * z₂) * ((z₂⁻¹ * o₁ * z₂) * o₂) := by group
    have e2 : (z₂ * o₂) * (z₁ * o₁) = (z₁ * z₂) * ((z₁⁻¹ * o₂ * z₁) * o₁) := by
      calc (z₂ * o₂) * (z₁ * o₁) = (z₂ * z₁) * ((z₁⁻¹ * o₂ * z₁) * o₁) := by group
        _ = (z₁ * z₂) * ((z₁⁻¹ * o₂ * z₁) * o₁) := by rw [hzz]
    have e3 : z₁ * o₁ * (z₂ * o₂) * (z₁ * o₁)⁻¹ * (z₂ * o₂)⁻¹ =
        ((z₁ * o₁) * (z₂ * o₂)) * ((z₂ * o₂) * (z₁ * o₁))⁻¹ := by group
    have e4 : (z₁ * z₂) * ((z₂⁻¹ * o₁ * z₂) * o₂) * ((z₁ * z₂) * ((z₁⁻¹ * o₂ * z₁) * o₁))⁻¹ =
        (z₁ * z₂) * (((z₂⁻¹ * o₁ * z₂) * o₂) * ((z₁⁻¹ * o₂ * z₁) * o₁)⁻¹) * (z₁ * z₂)⁻¹ := by
      group
    rw [e3, e1, e2, e4]
    exact (mem_normalizer_iff.mp (hZO (Z.mul_mem hz₁ hz₂)) _).mp
      (O.mul_mem (O.mul_mem ho₁' ho₂) (O.inv_mem (O.mul_mem ho₂' ho₁)))
  have hKL : ¬ K ≤ L := by
    intro hKL
    have hperf : (⊤ : Subgroup K) ≤ O.subgroupOf K := by
      rw [← hK.2.2.1]
      show ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [mem_subgroupOf, commutatorElement_def]
      exact hcomm _ (hKL g₁.2) _ (hKL g₂.2)
    have hKO : K ≤ O := fun k hk => hperf (mem_top (⟨k, hk⟩ : K))
    exact hO3 (h3K.trans (Subgroup.card_dvd_of_le hKO))
  have hnorm : ((K ⊓ L).subgroupOf K).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
    exact (mem_normalizer_iff.mp (hCZO (hKC g.2)) n).mp hn.2⟩
  have hbot : (K ⊓ L).subgroupOf K = ⊥ := by
    have := hsimple
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ L).subgroupOf K) with h1 | h1
    · exact h1
    · exfalso
      apply hKL
      intro k hk
      have : (⟨k, hk⟩ : K) ∈ (K ⊓ L).subgroupOf K := by
        rw [h1]
        exact mem_top _
      exact (mem_subgroupOf.mp this).2
  intro z hz
  rw [mem_centralizer_iff]
  intro k hk
  have hcK : z * k * z⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((mem_normalizer_iff.mp (hZN z hz) k).mp hk) (K.inv_mem hk)
  have hcL : z * k * z⁻¹ * k⁻¹ ∈ L := by
    have h1 := (mem_normalizer_iff.mp (hCZO (hKC hk)) z⁻¹).mp (mem_sup_left (Z.inv_mem hz))
    have h2 : z * k * z⁻¹ * k⁻¹ = z * (k * z⁻¹ * k⁻¹) := by group
    rw [h2]
    exact L.mul_mem (mem_sup_left hz) h1
  have h3 : (⟨z * k * z⁻¹ * k⁻¹, hcK⟩ : K) ∈ (K ⊓ L).subgroupOf K := mem_subgroupOf.mpr ⟨hcK, hcL⟩
  rw [hbot, mem_bot] at h3
  have h4 : z * k * z⁻¹ * k⁻¹ = 1 := congrArg Subtype.val h3
  exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := z) (g₂ := k)).mp h4).symm

theorem conj_mem_zpowers_of_mem_pCore (h : Hyp Y x) (hxF : x ∈ CFSG.pCore 3 Y) (y : Y) :
    y * x * y⁻¹ ∈ zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxp : IsPGroup 3 (zpowers x) :=
    elementary_isPGroup 3 _ (CFSG.AGLEmbedding.isElemAbelian_zpowers h.pow_eq_one)
  obtain ⟨R, hR⟩ := hxp.exists_le_sylow
  have hxR : x ∈ (R : Subgroup Y) := hR (mem_zpowers x)
  have hyF : y * x * y⁻¹ ∈ CFSG.pCore 3 Y := (CFSG.pCore_normal (p := 3) (G := Y)).conj_mem x hxF y
  have hyR : y * x * y⁻¹ ∈ (R : Subgroup Y) := CFSG.pCore_isPGroup.le_sylow_of_normal R hyF
  have hle : (zpowers x).map (MulAut.conj y).toMonoidHom ≤ (R : Subgroup Y) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact hyR
  have := h.weakClosed R hxR y hle
  rw [← this, MonoidHom.map_zpowers]
  exact mem_zpowers _

end Hyp

structure Data (Y : Type) [Group Y] [Finite Y] (x : Y) (Z : Subgroup Y) (S : Set Y)
    (O : Subgroup Y) : Prop where
  hyp : Hyp Y x
  isElemAbelian : IsElemAbelian 3 Z
  card_eq : Nat.card Z = 3 ^ 2
  x_not_mem : x ∉ Z
  le_centralizer : Z ≤ centralizer ({x} : Set Y)
  centralizes : ∀ s ∈ S, s * x * s⁻¹ = x
  normalizes : ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ ∈ Z
  irreducible : ∀ D : Subgroup Y, D ≤ Z → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) → D = ⊥ ∨ D = Z
  coprime : ¬ 3 ∣ Nat.card O
  O_le_centralizer : O ≤ centralizer ({x} : Set Y)
  normalizes_O : centralizer ({x} : Set Y) ≤ normalizer (O : Set Y)
  normalizes_ZO : centralizer ({x} : Set Y) ≤ normalizer ((Z ⊔ O : Subgroup Y) : Set Y)

namespace Data

variable {Y : Type} [Group Y] [Finite Y] {x : Y} {Z : Subgroup Y} {S : Set Y} {O : Subgroup Y}

theorem eq_one_of_fixed (d : Data Y x Z S O) {z : Y} (hz : z ∈ Z)
    (hfix : ∀ s ∈ S, s * z * s⁻¹ = z) : z = 1 := by
  by_contra hz1
  have hz3 : z ^ 3 = 1 := d.isElemAbelian.2 z hz
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hDZ : zpowers z ≤ Z := zpowers_le.mpr hz
  have hDS : ∀ s ∈ S, ∀ w ∈ zpowers z, s * w * s⁻¹ ∈ zpowers z := by
    intro s hs w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    rw [← conj_zpow, hfix s hs]
    exact zpow_mem_zpowers _ k
  rcases d.irreducible _ hDZ hDS with h | h
  · exact hz1 (by simpa using h)
  · have hc : Nat.card (zpowers z) = Nat.card Z := by rw [h]
    rw [Nat.card_zpowers, hzo, d.card_eq] at hc
    omega

theorem le_normalizer_zpowers (d : Data Y x Z S O) :
    Z ≤ normalizer ((zpowers x : Subgroup Y) : Set Y) := by
  intro z hz
  have hzx : z * x * z⁻¹ = x := by
    have := mem_centralizer_singleton_iff.mp (d.le_centralizer hz)
    calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [this]
      _ = x := by group
  refine mem_normalizer_of_map_conj_le ?_
  rw [MonoidHom.map_zpowers]
  simp [hzx]

theorem mem_E_iff (d : Data Y x Z S O) {e : Y} (he : e ∈ Z ⊔ zpowers x) :
    ∃ z ∈ Z, ∃ w ∈ zpowers x, e = z * w := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Z (zpowers x)
    d.le_normalizer_zpowers] at he
  obtain ⟨z, hz, w, hw, rfl⟩ := he
  exact ⟨z, hz, w, hw, rfl⟩

theorem centralizes_zpowers (d : Data Y x Z S O) {s : Y} (hs : s ∈ S) {w : Y}
    (hw : w ∈ zpowers x) : s * w * s⁻¹ = w := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  rw [← conj_zpow, d.centralizes s hs]

theorem normalizes_E (d : Data Y x Z S O) {s : Y} (hs : s ∈ S) {e : Y}
    (he : e ∈ Z ⊔ zpowers x) : s * e * s⁻¹ ∈ Z ⊔ zpowers x := by
  obtain ⟨z, hz, w, hw, rfl⟩ := d.mem_E_iff he
  have : s * (z * w) * s⁻¹ = (s * z * s⁻¹) * w := by
    calc s * (z * w) * s⁻¹ = (s * z * s⁻¹) * (s * w * s⁻¹) := by group
      _ = (s * z * s⁻¹) * w := by rw [d.centralizes_zpowers hs hw]
  rw [this]
  exact Subgroup.mul_mem _ (mem_sup_left (d.normalizes s hs z hz)) (mem_sup_right hw)

theorem le_zpowers_of_inf_eq_bot (d : Data Y x Z S O) {D : Subgroup Y}
    (hDE : D ≤ Z ⊔ zpowers x) (hDS : ∀ s ∈ S, ∀ e ∈ D, s * e * s⁻¹ ∈ D) (hDZ : D ⊓ Z = ⊥) :
    D ≤ zpowers x := by
  intro e he
  obtain ⟨z, hz, w, hw, rfl⟩ := d.mem_E_iff (hDE he)
  have hfix : ∀ s ∈ S, s * z * s⁻¹ = z := by
    intro s hs
    have h1 : s * (z * w) * s⁻¹ * (z * w)⁻¹ ∈ D := D.mul_mem (hDS s hs _ he) (D.inv_mem he)
    have h2 : s * (z * w) * s⁻¹ * (z * w)⁻¹ = (s * z * s⁻¹) * z⁻¹ := by
      calc s * (z * w) * s⁻¹ * (z * w)⁻¹
          = (s * z * s⁻¹) * (s * w * s⁻¹) * w⁻¹ * z⁻¹ := by group
        _ = (s * z * s⁻¹) * w * w⁻¹ * z⁻¹ := by rw [d.centralizes_zpowers hs hw]
        _ = (s * z * s⁻¹) * z⁻¹ := by group
    have h3 : (s * z * s⁻¹) * z⁻¹ ∈ Z := Z.mul_mem (d.normalizes s hs z hz) (Z.inv_mem hz)
    rw [h2] at h1
    have h4 : (s * z * s⁻¹) * z⁻¹ ∈ D ⊓ Z := ⟨h1, h3⟩
    rw [hDZ, mem_bot] at h4
    exact mul_inv_eq_one.mp h4
  rw [d.eq_one_of_fixed hz hfix, one_mul]
  exact hw

theorem inf_eq_bot_or_eq (d : Data Y x Z S O) {D : Subgroup Y}
    (hDS : ∀ s ∈ S, ∀ e ∈ D, s * e * s⁻¹ ∈ D) : D ⊓ Z = ⊥ ∨ D ⊓ Z = Z :=
  d.irreducible (D ⊓ Z) inf_le_right fun s hs e he =>
    ⟨hDS s hs e he.1, d.normalizes s hs e he.2⟩

theorem eq_bot_of_not_mem (d : Data Y x Z S O) {D : Subgroup Y} (hDE : D ≤ Z ⊔ zpowers x)
    (hDS : ∀ s ∈ S, ∀ e ∈ D, s * e * s⁻¹ ∈ D) (hxD : x ∉ D) (hZD : ¬ Z ≤ D) : D = ⊥ := by
  have hDZ : D ⊓ Z = ⊥ := by
    rcases d.inf_eq_bot_or_eq hDS with h | h
    · exact h
    · exact absurd (fun z hz => (h.ge hz).1) hZD
  have hDx := d.le_zpowers_of_inf_eq_bot hDE hDS hDZ
  rw [eq_bot_iff]
  intro e he
  have hex := hDx he
  by_contra he1
  have he1' : e ≠ 1 := fun h => he1 (h ▸ one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime d.hyp.pow_eq_one d.hyp.ne_one
  have : zpowers e = zpowers x :=
    zpowers_eq_of_mem_zpowers_of_orderOf_eq_three hxo hex he1'
  exact hxD (zpowers_le.mpr he (this ▸ mem_zpowers x))

theorem le_pCore_of_mem_pCore (d : Data Y x Z S O) (hxF : x ∈ CFSG.pCore 3 Y) :
    Z ≤ CFSG.pCore 3 Y := by
  have hY := d.hyp
  have hconj : ∀ y : Y, y * x * y⁻¹ ∈ zpowers x := hY.conj_mem_zpowers_of_mem_pCore hxF
  set N : Subgroup Y := centralizer ({x} : Set Y) with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g⁻¹ * x * g ∈ zpowers x := by simpa using hconj g⁻¹
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    have hnx : n * x = x * n := mem_centralizer_singleton_iff.mp hn
    have hnxk : n * x ^ k = x ^ k * n := (Commute.zpow_right (show Commute n x from hnx) k).eq
    refine mem_centralizer_singleton_iff.mpr ?_
    calc g * n * g⁻¹ * x = g * (n * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (n * x ^ k) * g⁻¹ := by rw [hk]
      _ = g * (x ^ k * n) * g⁻¹ := by rw [hnxk]
      _ = g * ((g⁻¹ * x * g) * n) * g⁻¹ := by rw [hk]
      _ = x * (g * n * g⁻¹) := by group
  have hNsub : N.IsSubnormal := hNn.isSubnormal
  have hOn : (O.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer d.O_le_centralizer).mpr d.normalizes_O
  have hOsub : O.IsSubnormal := Subgroup.IsSubnormal.step O N d.O_le_centralizer hNsub hOn
  have hOle : O ≤ primeComplementCore (G := Y) 3 :=
    le_primeComplementCore_three_of_subnormal hOsub
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr d.coprime)
  have hObot : O = ⊥ := by
    rw [hY.core_eq_bot] at hOle
    exact le_bot_iff.mp hOle
  have hZn : (Z.subgroupOf N).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer d.le_centralizer).mpr fun n hn => ?_
    have := d.normalizes_ZO hn
    rwa [hObot, sup_bot_eq] at this
  have hZsub : Z.IsSubnormal := Subgroup.IsSubnormal.step Z N d.le_centralizer hNsub hZn
  have hZ3 : IsPGroup 3 Z := elementary_isPGroup 3 Z d.isElemAbelian
  have hmap := pCore_map_le_pCore_of_isSubnormal 3 hZsub
  intro z hz
  refine hmap ⟨⟨z, hz⟩, ?_, rfl⟩
  have hZtop : (⊤ : Subgroup ↥Z) ≤ CFSG.pCore 3 ↥Z :=
    le_sSup ⟨inferInstance, hZ3.of_equiv Subgroup.topEquiv.symm⟩
  exact hZtop (Subgroup.mem_top _)

theorem exists_central_order_three {F : Subgroup Y} (hF3 : IsPGroup 3 F) (hF : F ≠ ⊥) :
    ∃ v ∈ F, v ≠ 1 ∧ v ^ 3 = 1 ∧ ∀ f ∈ F, v * f = f * v := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial ↥F := (Subgroup.nontrivial_iff_ne_bot F).mpr hF
  haveI : Nontrivial ↥(Subgroup.center ↥F) := hF3.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥F))
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hF3 (c : ↥F)
  have hc1' : (c : ↥F) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hk1 : k ≠ 0 := by
    rintro rfl
    exact hc1' (orderOf_eq_one_iff.mp (by simpa using hk))
  have hdvd : 3 ^ (k - 1) ∣ orderOf (c : ↥F) := by
    rw [hk]
    exact pow_dvd_pow 3 (Nat.sub_le k 1)
  have hord : orderOf ((c : ↥F) ^ 3 ^ (k - 1)) = 3 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) hdvd, hk]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk1
    simp [pow_succ]
  have hv1 : (c : ↥F) ^ 3 ^ (k - 1) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    omega
  refine ⟨((c : ↥F) ^ 3 ^ (k - 1) : ↥F), (c ^ 3 ^ (k - 1) : ↥F).2, fun h => hv1 (Subtype.ext h),
    ?_, ?_⟩
  · have := pow_orderOf_eq_one ((c : ↥F) ^ 3 ^ (k - 1))
    rw [hord] at this
    exact congrArg Subtype.val this
  · intro f hf
    have hcc : ((c : ↥F) ^ 3 ^ (k - 1)) * ⟨f, hf⟩ = ⟨f, hf⟩ * ((c : ↥F) ^ 3 ^ (k - 1)) :=
      (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ c.2 _) ⟨f, hf⟩).symm
    exact congrArg Subtype.val hcc

theorem isElemAbelian_E (d : Data Y x Z S O) : IsElemAbelian 3 (Z ⊔ zpowers x) := by
  refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3
    d.isElemAbelian (CFSG.AGLEmbedding.isElemAbelian_zpowers d.hyp.pow_eq_one) ?_
  intro z hz
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have hzx : z * x = x * z := mem_centralizer_singleton_iff.mp (d.le_centralizer hz)
  exact ((Commute.zpow_right (show Commute z x from hzx) k).eq).symm

theorem card_E (d : Data Y x Z S O) : Nat.card ↥(Z ⊔ zpowers x) = 3 ^ 3 := by
  have hx3 := d.hyp.pow_eq_one
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three Z hx3 d.x_not_mem
    (fun z hz => mem_centralizer_singleton_iff.mp (d.le_centralizer hz)), d.card_eq]
  norm_num

theorem mem_E_of_pow_three (d : Data Y x Z S O) {R : Sylow 3 Y}
    (hER : Z ⊔ zpowers x ≤ (R : Subgroup Y)) {v : Y} (hvR : v ∈ (R : Subgroup Y))
    (hv3 : v ^ 3 = 1) : v ∈ Z ⊔ zpowers x := by
  by_contra hvE
  have hcomm : ∀ e ∈ Z ⊔ zpowers x, e * v = v * e := fun e he =>
    d.hyp.omega R e (hER he) v hvR (d.isElemAbelian_E.2 e he) hv3
  have hEv : IsElemAbelian 3 (Z ⊔ zpowers x ⊔ zpowers v) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 d.isElemAbelian_E
      (CFSG.AGLEmbedding.isElemAbelian_zpowers hv3)
      (fun e he => mem_centralizer_iff.mpr fun w hw => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        exact ((Commute.zpow_right (show Commute e v from hcomm e he) k).eq).symm)
  have hle : Z ⊔ zpowers x ⊔ zpowers v ≤ (R : Subgroup Y) :=
    sup_le hER (zpowers_le.mpr hvR)
  have h1 := d.hyp.rank R _ hle hEv
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three _ hv3 hvE hcomm,
    d.card_E] at h1
  omega

theorem exists_component_not_centralized (d : Data Y x Z S O) (hZ : ¬ Z ≤ CFSG.pCore 3 Y) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ ¬ Z ≤ centralizer (K : Set Y) := by
  by_contra hall
  push Not at hall
  apply hZ
  have h := d.hyp
  have hZ3 : IsPGroup 3 Z := elementary_isPGroup 3 Z d.isElemAbelian
  have hlay : CFSG.layer Y ≤ centralizer (Z : Set Y) := by
    show sSup {K : Subgroup Y | CFSG.IsComponent K} ≤ _
    exact sSup_le fun K hK =>
      le_centralizer_iff.mp (hall K ((CFSG.isComponent_iff_open K).mp hK))
  by_cases hp : CFSG.pCore 3 Y ≤ centralizer (Z : Set Y)
  · have hF : CFSG.fittingSubgroup Y = CFSG.pCore 3 Y := CFSG.Fitting_eq_pcore Y 3 h.core_eq_bot
    have hFs : CFSG.generalizedFitting Y ≤ centralizer (Z : Set Y) := by
      rw [CFSG.generalizedFitting, hF]
      exact sup_le hp hlay
    have hZF : Z ≤ CFSG.generalizedFitting Y :=
      (le_centralizer_iff.mp hFs).trans (CFSG.centralizer_generalizedFitting_le Y)
    intro z hz
    have hzF := hZF hz
    rw [CFSG.generalizedFitting, hF] at hzF
    have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
    obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hzF
    have haC : a ∈ centralizer (CFSG.layer Y : Set Y) := by
      have := commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.LocalCores.fitting_layer_commute (G := Y)) (hF ▸ ha)
      exact this
    have hzC : a * e ∈ centralizer (CFSG.layer Y : Set Y) := le_centralizer_iff.mp hlay hz
    have hec : e ∈ centralizer (CFSG.layer Y : Set Y) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ haC) hzC
      simpa using this
    have hcenter : (center (CFSG.layer Y)).map (CFSG.layer Y).subtype = ⊥ := by
      rw [(CFSG.LocalCores.layer_center (G := Y)).1]
      refine le_bot_iff.mp (iSup_le fun K => ?_)
      rw [h.center_eq_bot K.1 ((CFSG.isComponent_iff_open K.1).mp K.2), Subgroup.map_bot]
    have he1 : e = 1 := by
      have : e ∈ (center (CFSG.layer Y)).map (CFSG.layer Y).subtype :=
        (CFSG.LocalCores.mem_map_center_iff (CFSG.layer Y)).mpr ⟨he, hec⟩
      rw [hcenter] at this
      exact mem_bot.mp this
    rw [he1, mul_one]
    exact ha
  ·
    have hFp : IsPGroup 3 (CFSG.pCore 3 Y) := CFSG.pCore_isPGroup
    have hFn : (CFSG.pCore 3 Y).Normal := CFSG.pCore_normal
    have hFne : CFSG.pCore 3 Y ≠ ⊥ := fun hb => hp (hb ▸ bot_le)
    rcases d.inf_eq_bot_or_eq (D := CFSG.pCore 3 Y) (fun s _ e he => hFn.conj_mem e he s) with
      hZF | hZF
    swap
    · exact fun z hz => (hZF.ge hz).1
    obtain ⟨v, hvF, hv1, hv3, hvc⟩ := exists_central_order_three hFp hFne
    have hEp : IsPGroup 3 (Z ⊔ zpowers x : Subgroup Y) :=
      elementary_isPGroup 3 _ d.isElemAbelian_E
    have hsup : IsPGroup 3 (Z ⊔ zpowers x ⊔ CFSG.pCore 3 Y : Subgroup Y) :=
      hEp.to_sup_of_normal_right' hFp (by rw [Subgroup.normalizer_eq_top_iff.mpr hFn]; exact le_top)
    obtain ⟨R, hR⟩ := hsup.exists_le_sylow
    have hvE : v ∈ Z ⊔ zpowers x :=
      d.mem_E_of_pow_three (le_sup_left.trans hR) (hR (mem_sup_right hvF)) hv3
    set D : Subgroup Y := (Z ⊔ zpowers x) ⊓ CFSG.pCore 3 Y ⊓ centralizer (CFSG.pCore 3 Y : Set Y)
      with hD
    have hDE : D ≤ Z ⊔ zpowers x := inf_le_left.trans inf_le_left
    have hDS : ∀ s ∈ S, ∀ e ∈ D, s * e * s⁻¹ ∈ D := by
      intro s hs e he
      refine ⟨⟨d.normalizes_E hs he.1.1, hFn.conj_mem e he.1.2 s⟩, mem_centralizer_iff.mpr ?_⟩
      intro f hf
      have h1 : s⁻¹ * f * s⁻¹⁻¹ ∈ CFSG.pCore 3 Y := hFn.conj_mem f hf s⁻¹
      have h2 := mem_centralizer_iff.mp he.2 _ h1
      calc f * (s * e * s⁻¹) = s * ((s⁻¹ * f * s⁻¹⁻¹) * e) * s⁻¹ := by group
        _ = s * (e * (s⁻¹ * f * s⁻¹⁻¹)) * s⁻¹ := by rw [h2]
        _ = s * e * s⁻¹ * f := by group
    have hDZ : D ⊓ Z = ⊥ := by
      rw [eq_bot_iff, ← hZF]
      exact inf_le_inf_right Z (inf_le_left.trans inf_le_right)
    have hDx := d.le_zpowers_of_inf_eq_bot hDE hDS hDZ
    have hvD : v ∈ D := ⟨⟨hvE, hvF⟩, mem_centralizer_iff.mpr fun f hf => (hvc f hf).symm⟩
    have hxo : orderOf x = 3 := orderOf_eq_prime h.pow_eq_one h.ne_one
    have hzx : zpowers v = zpowers x :=
      zpowers_eq_of_mem_zpowers_of_orderOf_eq_three hxo (hDx hvD) hv1
    have hxD : x ∈ D := zpowers_le.mpr hvD (hzx ▸ mem_zpowers x)
    exact d.le_pCore_of_mem_pCore hxD.1.2

theorem exists_elemAbelian_of_not_isCyclic {K : Subgroup Y} (P : Sylow 3 K)
    (hnc : ¬ IsCyclic (P : Subgroup K)) :
    ∃ B : Subgroup Y, B ≤ K ∧ IsElemAbelian 3 B ∧ Nat.card B = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨B₀, hB₀, hB₀c⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (p := 3) (by decide) P.isPGroup' hnc
  have hB₁ : CFSG.IsElementaryAbelian 3 (B₀.map (P : Subgroup K).subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  have hB₂ : CFSG.IsElementaryAbelian 3 ((B₀.map (P : Subgroup K).subtype).map K.subtype) :=
    CFSG.IsElementaryAbelian.map_subtype
  refine ⟨(B₀.map (P : Subgroup K).subtype).map K.subtype, Subgroup.map_subtype_le _,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 hB₂, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective (P : Subgroup K).subtype_injective, hB₀c]

theorem isCyclic_sylow_of_moved (d : Data Y x Z S O) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    {s : Y} (hsK : s ∉ normalizer (K : Set Y)) (P : Sylow 3 K) : IsCyclic (P : Subgroup K) := by
  by_contra hnc
  obtain ⟨B, hBK, hBel, hBc⟩ := exists_elemAbelian_of_not_isCyclic P hnc
  have h := d.hyp
  have hK₂ : IsComponentOf (K.map (MulAut.conj s).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj s) K).mpr hK
  have hne : K.map (MulAut.conj s).toMonoidHom ≠ K := fun h' =>
    hsK (mem_normalizer_iff_map_conj_eq.mpr h')
  have hKK : K ≤ centralizer ((K.map (MulAut.conj s).toMonoidHom : Subgroup Y) : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK hK₂ hne.symm)
  have hKK' : K.map (MulAut.conj s).toMonoidHom ≤ centralizer (K : Set Y) :=
    le_centralizer_iff.mp hKK
  set B₂ : Subgroup Y := B.map (MulAut.conj s).toMonoidHom with hB₂
  have hB₂K : B₂ ≤ K.map (MulAut.conj s).toMonoidHom := Subgroup.map_mono hBK
  have hcomm : ∀ b ∈ B, ∀ b' ∈ B₂, b * b' = b' * b := fun b hb b' hb' =>
    (mem_centralizer_iff.mp (hKK (hBK hb)) b' (hB₂K hb')).symm
  have hBB : B ⊓ B₂ = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    have h1 : e ∈ K := hBK he.1
    have h2 : e ∈ centralizer (K : Set Y) := hKK' (hB₂K he.2)
    exact mem_bot.mpr (GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer
      (h.center_eq_bot K hK) h1 h2)
  have hB₂el : IsElemAbelian 3 B₂ := by
    have := hBel.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := a.2
      obtain ⟨b', hb', hb'e⟩ := b.2
      apply Subtype.ext
      show (a : Y) * b = b * a
      rw [← ha'e, ← hb'e]
      have := congrArg (MulAut.conj s) (setLike_mul_comm ha' hb')
      simpa using this
    · obtain ⟨y', hy', rfl⟩ := hy
      have : y' ^ 3 = 1 := hBel.2 y' hy'
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, this, map_one]
  have hB₂c : Nat.card B₂ = 3 ^ 2 := by
    rw [hB₂, Subgroup.card_map_of_injective (MulAut.conj s).injective, hBc]
  have hsupel : IsElemAbelian 3 (B ⊔ B₂) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting 3 hBel hB₂el
      (fun b hb => mem_centralizer_iff.mpr fun b' hb' => (hcomm b hb b' hb').symm)
  have hsupc : Nat.card ↥(B ⊔ B₂) = 3 ^ 4 := by
    obtain ⟨hc, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute B B₂ hcomm
    rw [hBB, Subgroup.card_bot, mul_one, hBc, hB₂c] at hc
    rw [hc]
    norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR⟩ := (elementary_isPGroup 3 _ hsupel).exists_le_sylow
  have := h.rank R _ hR hsupel
  rw [hsupc] at this
  omega

theorem exists_inv_mul_mem_centralizer' (hInn : KFactInnerAction) {K : Subgroup Y}
    (hsimple : IsSimpleGroup K) (hnonab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K)
    {Q : Sylow 3 Y} {P : Sylow 3 K} (hPab : IsMulCommutative (P : Subgroup K))
    (hP : (P : Subgroup K) = (Q : Subgroup Y).subgroupOf K) (hP1 : (P : Subgroup K) ≠ ⊥)
    {y : Y} (hyc : ∀ q ∈ (Q : Subgroup Y), y * q = q * y) (hyN : y ∈ normalizer (K : Set Y))
    (hyp : y ^ 3 = 1) : ∃ r ∈ (Q : Subgroup Y) ⊓ K, r⁻¹ * y ∈ centralizer (K : Set Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem := GL83Generic5MComp.mem_sylow_iff hP
  set φ : MulAut K := K.normalizerMonoidHom ⟨y, hyN⟩ with hφdef
  have hφ : ∀ k : K, ((φ k : K) : Y) = y * k * y⁻¹ := fun _ => rfl
  have hφp : φ ^ 3 = 1 := by
    have h1 : (⟨y, hyN⟩ : normalizer (K : Set Y)) ^ 3 = 1 :=
      Subtype.ext (by rw [coe_pow, coe_one]; exact hyp)
    rw [hφdef, ← map_pow, h1, map_one]
  obtain ⟨g, hgP, hg⟩ := hInn 3 Nat.prime_three (by norm_num) K hsimple hnonab hcat P hP1 hPab
    φ ⟨1, by rw [pow_one, hφp]⟩
    (fun g hg => by
      have hyg : y * (g : Y) = g * y := hyc g ((hmem g).mp hg)
      ext m
      change y * ((g : Y) * m * (g : Y)⁻¹) * y⁻¹ = (g : Y) * (y * m * y⁻¹) * (g : Y)⁻¹
      calc y * ((g : Y) * m * (g : Y)⁻¹) * y⁻¹ = (y * g) * m * (y * g)⁻¹ := by group
        _ = (g * y) * m * (g * y)⁻¹ := by rw [hyg]
        _ = (g : Y) * (y * m * y⁻¹) * (g : Y)⁻¹ := by group)
  refine ⟨g, ⟨(hmem g).mp hgP, g.2⟩, mem_centralizer_iff.mpr fun k hk => ?_⟩
  have h1 : y * k * y⁻¹ = (g : Y) * k * (g : Y)⁻¹ := by
    rw [← hφ ⟨k, hk⟩, hg]
    rfl
  calc k * ((g : Y)⁻¹ * y) = (g : Y)⁻¹ * ((g : Y) * k * (g : Y)⁻¹) * y := by group
    _ = (g : Y)⁻¹ * (y * k * y⁻¹) * y := by rw [h1]
    _ = (g : Y)⁻¹ * y * k := by group

theorem mem_of_isCyclic_sylow (d : Data Y x Z S O) (hInn : KFactInnerAction) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) (hxN : x ∈ normalizer (K : Set Y)) (hxC : x ∉ centralizer (K : Set Y))
    (hcyc : ∀ P : Sylow 3 K, IsCyclic (P : Subgroup K)) : x ∈ K := by
  have h := d.hyp
  have hZ := h.center_eq_bot K hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hxp : IsPGroup 3 (zpowers x) :=
    elementary_isPGroup 3 _ (CFSG.AGLEmbedding.isElemAbelian_zpowers h.pow_eq_one)
  obtain ⟨Q, hQ, P, hP⟩ :=
    GL83Generic5MComp.exists_sylow_le_subgroupOf hxp (zpowers_le.mpr hxN)
  have hxQ : x ∈ (Q : Subgroup Y) := hQ (mem_zpowers x)
  have hxcQ := h.le_centralizer_of_mem hxQ
  have hP1 : (P : Subgroup K) ≠ ⊥ := by
    obtain ⟨t, htQK, hto, -⟩ :=
      exists_mem_sylow_inf_component Nat.prime_three (by norm_num) h.core_eq_bot Q hK
    intro hbot
    have ht : (⟨t, (mem_inf.mp htQK).2⟩ : K) ∈ (P : Subgroup K) := by
      rw [hP, mem_subgroupOf]
      exact (mem_inf.mp htQK).1
    rw [hbot, mem_bot] at ht
    rw [show t = 1 from congrArg Subtype.val ht, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hPc := hcyc P
  have hPab : IsMulCommutative (P : Subgroup K) :=
    IsMulCommutative.of_comm fun a b => (hPc.commGroup).mul_comm a b
  obtain ⟨r, hrQK, hc⟩ := exists_inv_mul_mem_centralizer' hInn hsimple hnonab
    (h.catalog.simple_subgroup K hsimple hnonab) hPab hP hP1
    (fun q hq => (mem_centralizer_singleton_iff.mp (hxcQ hq)).symm) hxN h.pow_eq_one
  have hrc : Commute r (r⁻¹ * x) := mem_centralizer_iff.mp hc r hrQK.2
  have hrp : r ^ 3 = 1 := by
    have h1 : r ^ 3 * (r⁻¹ * x) ^ 3 = 1 := by
      rw [← hrc.mul_pow, mul_inv_cancel_left, h.pow_eq_one]
    exact GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer hZ (pow_mem hrQK.2 3)
      ((eq_inv_of_mul_eq_one_left h1) ▸ inv_mem (pow_mem hc 3))
  have hro : orderOf r = 3 := by
    refine orderOf_eq_prime hrp fun hr1 => hxC ?_
    rwa [hr1, inv_one, one_mul] at hc
  have hmem := GL83Generic5MComp.mem_sylow_iff hP
  set r' : K := ⟨r, hrQK.2⟩ with hr'
  have hr'P : r' ∈ (P : Subgroup K) := (hmem r').mpr hrQK.1
  obtain ⟨g, hgN, a, haP, hap, hga⟩ :=
    CFSG.RankThree.PartOne.D4RC.rcb_exists_normalizer_elt_perfect
      hK.2.2.1 P.isPGroup' P.not_dvd_index hPc hP1
  have ha1 : a ≠ 1 := fun ha => hga (by rw [ha, mul_one, mul_inv_cancel])
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, r' ^ j = a := by
    have hr'p : (⟨r', hr'P⟩ : (P : Subgroup K)) ^ 3 = 1 :=
      Subtype.ext (Subtype.ext (by simp [hr', ← hro, pow_orderOf_eq_one]))
    have hr'1 : (⟨r', hr'P⟩ : (P : Subgroup K)) ≠ 1 := fun h1 => by
      have h2 : r = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
      rw [h2, orderOf_one] at hro
      exact absurd hro (by norm_num)
    have heq : zpowers (⟨a, haP⟩ : (P : Subgroup K)) = zpowers ⟨r', hr'P⟩ := by
      rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
        orderOf_eq_prime (Subtype.ext hap) (fun h1 => ha1 (congrArg Subtype.val h1)),
        orderOf_eq_prime hr'p hr'1]
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (heq ▸ mem_zpowers (⟨a, haP⟩ : (P : Subgroup K)))
    exact ⟨j, congrArg Subtype.val hj⟩
  have hgr : (g : Y) * r * (g : Y)⁻¹ ∈ (Q : Subgroup Y) :=
    (hmem _).mp ((mem_normalizer_iff.mp hgN r').mp hr'P)
  obtain ⟨m, hm, hcm⟩ := GL83Generic5MComp.exists_conj_eq_zpow hZ (h.weakClosed Q hxQ) hxQ
    hrQK.1 hrQK.2 hc g.2 hgr
  have hrm : r ^ (m - 1) ≠ 1 := by
    intro hr1
    apply hga
    have hfix : g * r' * g⁻¹ = r' := Subtype.ext (by
      rw [zpow_sub_one, mul_inv_eq_one] at hr1
      simpa [hr1] using hm)
    rw [← conj_zpow, hfix]
  set c := r⁻¹ * x with hcdef
  have hcp : c ^ 3 = 1 := by
    have hrx : Commute r⁻¹ x :=
      mem_centralizer_singleton_iff.mp (hxcQ (inv_mem (mem_inf.mp hrQK).1))
    have hrp : r ^ 3 = 1 := hro ▸ pow_orderOf_eq_one r
    rw [hcdef, hrx.mul_pow, inv_pow, hrp, inv_one, one_mul, h.pow_eq_one]
  have hc1 : c = 1 := by
    have hcm1 : c ^ (m - 1) = 1 := by rw [zpow_sub_one, hcm, mul_inv_cancel]
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hcp) with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      refine hrm (orderOf_dvd_iff_zpow_eq_one.mp ?_)
      rw [hro, ← h1]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hcm1
  have hxr : x = r := by
    rw [hcdef, inv_mul_eq_one] at hc1
    exact hc1.symm
  exact hxr ▸ hrQK.2

theorem isElemAbelian_subgroupOf {A B : Subgroup Y} (hA : IsElemAbelian 3 A) :
    IsElemAbelian 3 (A.subgroupOf B) := by
  have := hA.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
  · apply Subtype.ext
    exact hA.2 (a : Y) (Subgroup.mem_subgroupOf.mp ha)

theorem false_of_normalized (d : Data Y x Z S O) (hWC3 : KFactWeakClosureOmega3)
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) (hSN : ∀ s ∈ S, s ∈ normalizer (K : Set Y))
    (hZN : ∀ z ∈ Z, z ∈ normalizer (K : Set Y)) (hxN : x ∈ normalizer (K : Set Y))
    (hxC : x ∉ centralizer (K : Set Y)) (hZK : ¬ Z ≤ centralizer (K : Set Y)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := d.hyp
  have hZ0 := h.center_eq_bot K hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ0
  have hcat : IsCatalogGroup K := h.catalog.simple_subgroup K hsimple hnonab
  set N : Subgroup Y := normalizer (K : Set Y) with hNdef
  have hEN : Z ⊔ zpowers x ≤ N := sup_le (fun z hz => hZN z hz) (zpowers_le.mpr hxN)
  set D : Subgroup Y := (Z ⊔ zpowers x) ⊓ centralizer (K : Set Y) with hD
  have hDS : ∀ s ∈ S, ∀ e ∈ D, s * e * s⁻¹ ∈ D := by
    intro s hs e he
    refine ⟨d.normalizes_E hs he.1, mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' : s⁻¹ * k * s ∈ K := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSN s hs)) k).mp hk
      simpa using this
    have h2 := mem_centralizer_iff.mp he.2 _ hk'
    calc k * (s * e * s⁻¹) = s * ((s⁻¹ * k * s) * e) * s⁻¹ := by group
      _ = s * (e * (s⁻¹ * k * s)) * s⁻¹ := by rw [h2]
      _ = s * e * s⁻¹ * k := by group
  have hDbot : D = ⊥ :=
    d.eq_bot_of_not_mem inf_le_left hDS (fun hx => hxC hx.2)
      (fun hZD => hZK fun z hz => (hZD hz).2)
  have hEp : IsPGroup 3 (Z ⊔ zpowers x : Subgroup Y) :=
    elementary_isPGroup 3 _ d.isElemAbelian_E
  obtain ⟨R₀, hR₀⟩ := (hEp.comap_subtype (K := N)).exists_le_sylow
  set Rh : Subgroup Y := (R₀ : Subgroup N).map N.subtype with hRh
  have hRhsyl : IsSylowOf 3 Rh N := ⟨R₀, rfl⟩
  have hERh : Z ⊔ zpowers x ≤ Rh := fun e he => ⟨⟨e, hEN he⟩, hR₀ he, rfl⟩
  obtain ⟨R, hR⟩ := hRhsyl.isPGroup.exists_le_sylow
  have hER : Z ⊔ zpowers x ≤ (R : Subgroup Y) := hERh.trans hR
  have hRhE : ∀ v ∈ Rh, v ^ 3 = 1 → v ∈ Z ⊔ zpowers x := fun v hv hv3 =>
    d.mem_E_of_pow_three hER (hR hv) hv3
  have hCR : Rh ⊓ centralizer (K : Set Y) = ⊥ := by
    by_contra hne
    obtain ⟨u, hu, hu1, hu3, -⟩ :=
      exists_central_order_three (F := Rh ⊓ centralizer (K : Set Y)) hRhsyl.isPGroup.to_inf_left hne
    have huD : u ∈ D := ⟨hRhE u hu.1 hu3, hu.2⟩
    rw [hDbot, mem_bot] at huD
    exact hu1 huD
  have hRhN : Rh ≤ N := Subgroup.map_subtype_le _
  have hKN : K ≤ N := Subgroup.le_normalizer
  have hXN : Rh ⊔ K ≤ N := sup_le hRhN hKN
  have hXset : ((Rh ⊔ K : Subgroup Y) : Set Y) = (Rh : Set Y) * (K : Set Y) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Rh K hRhN
  set X : Subgroup Y := Rh ⊔ K with hX
  have hKX : K ≤ X := le_sup_right
  have hRhX : Rh ≤ X := le_sup_left
  set K' : Subgroup ↥X := K.subgroupOf X with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  let eK : ↥K' ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have hK'simple : IsSimpleGroup ↥K' := by
    have := hsimple
    exact eK.isSimpleGroup
  have hK'nonab : ∃ a b : ↥K', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eK.symm a, eK.symm b, fun hba => hab (by simpa using congrArg eK hba)⟩
  have hK'cat : IsCatalogGroup ↥K' := IsCatalogGroup.of_mulEquiv eK hcat
  have h3K : 3 ∣ Nat.card ↥K' := by
    obtain ⟨t, htK, hto, -⟩ := h.exists_order_three hK
    have h1 : orderOf (⟨t, htK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hto] at h1
    rwa [Nat.card_congr eK.toEquiv]
  obtain ⟨Q, hQ⟩ := (hRhsyl.of_le hRhX hXN).exists_sylow_eq_subgroupOf
  have hcK : ∀ c' ∈ centralizer (K' : Set ↥X), ∀ k ∈ K, k * (c' : Y) = (c' : Y) * k := by
    intro c' hc' k hk
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc' ⟨k, hKX hk⟩
      (Subgroup.mem_subgroupOf.mpr hk))
  have h3pow : ∀ c' ∈ centralizer (K' : Set ↥X), ∃ a : ℕ, c' ^ 3 ^ a = 1 := by
    intro c' hc'
    have hcX : (c' : Y) ∈ ((Rh ⊔ K : Subgroup Y) : Set Y) := c'.2
    rw [hXset] at hcX
    obtain ⟨r, hr, k₀, hk₀, hrk⟩ := hcX
    obtain ⟨a, ha⟩ := hRhsyl.isPGroup ⟨r, hr⟩
    have hra : r ^ 3 ^ a = 1 := congrArg Subtype.val ha
    have hcomm : Commute (c' : Y) k₀⁻¹ := by
      have := hcK c' hc' k₀⁻¹ (K.inv_mem hk₀)
      exact this.symm
    have hr' : r = (c' : Y) * k₀⁻¹ := by rw [← hrk]; group
    have h1 : (c' : Y) ^ 3 ^ a * (k₀⁻¹) ^ 3 ^ a = 1 := by
      rw [← hcomm.mul_pow, ← hr']
      exact hra
    have h2 : (c' : Y) ^ 3 ^ a = k₀ ^ 3 ^ a := by
      rw [inv_pow] at h1
      exact mul_inv_eq_one.mp h1
    have hcc : (c' : Y) ^ 3 ^ a ∈ centralizer (K : Set Y) :=
      Subgroup.pow_mem _ (mem_centralizer_iff.mpr fun k hk => hcK c' hc' k hk) _
    have hkk : (c' : Y) ^ 3 ^ a ∈ K := h2 ▸ K.pow_mem hk₀ _
    refine ⟨a, Subtype.ext ?_⟩
    simpa using GL83Generic5MComp.eq_one_of_mem_of_mem_centralizer hZ0 hkk hcc
  have hKcent : centralizer (K' : Set ↥X) = ⊥ := by
    rw [eq_bot_iff]
    haveI := hK'n
    have hTp : IsPGroup 3 (centralizer (K' : Set ↥X)) := fun g => by
      obtain ⟨a, ha⟩ := h3pow g.1 g.2
      exact ⟨a, Subtype.ext ha⟩
    have hTQ : centralizer (K' : Set ↥X) ≤ (Q : Subgroup ↥X) := hTp.le_sylow_of_normal Q
    intro c hc
    have hcRh : (c : Y) ∈ Rh := by
      have := hTQ hc
      rw [hQ] at this
      exact Subgroup.mem_subgroupOf.mp this
    have hcC : (c : Y) ∈ centralizer (K : Set Y) :=
      mem_centralizer_iff.mpr fun k hk => hcK c hc k hk
    have : (c : Y) ∈ Rh ⊓ centralizer (K : Set Y) := ⟨hcRh, hcC⟩
    rw [hCR, mem_bot] at this
    exact mem_bot.mpr (Subtype.ext this)
  have hKQ : K' ⊔ (Q : Subgroup ↥X) = ⊤ := by
    rw [hQ, hK', ← Subgroup.subgroupOf_sup hKX hRhX, sup_comm]
    exact Subgroup.subgroupOf_self X
  have hzx : zpowers x ≤ X := zpowers_le.mpr (hERh.trans hRhX (mem_sup_right (mem_zpowers x)))
  have hΩ : ∃ E' : Subgroup ↥X, E' ≤ (Q : Subgroup ↥X) ∧ IsElemAbelian 3 E' ∧
      Nat.card E' = 3 ^ 3 ∧ ∀ y ∈ (Q : Subgroup ↥X), y ^ 3 = 1 → y ∈ E' := by
    refine ⟨(Z ⊔ zpowers x).subgroupOf X, ?_, isElemAbelian_subgroupOf d.isElemAbelian_E, ?_, ?_⟩
    · rw [hQ]
      exact fun e he => Subgroup.mem_subgroupOf.mpr (hERh (Subgroup.mem_subgroupOf.mp he))
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hERh.trans hRhX)).toEquiv, d.card_E]
    · intro y hy hy3
      rw [hQ] at hy
      exact Subgroup.mem_subgroupOf.mpr (hRhE (y : Y) (Subgroup.mem_subgroupOf.mp hy)
        (by simpa using congrArg Subtype.val hy3))
  have hxo : orderOf x = 3 := orderOf_eq_prime h.pow_eq_one h.ne_one
  have hAle : (zpowers x).subgroupOf X ≤ (Q : Subgroup ↥X) := by
    rw [hQ]
    exact fun a ha => Subgroup.mem_subgroupOf.mpr
      (hERh (mem_sup_right (Subgroup.mem_subgroupOf.mp ha)))
  have hAc : Nat.card ↥((zpowers x).subgroupOf X) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzx).toEquiv, Nat.card_zpowers, hxo]
  obtain ⟨g, hg1, hg2⟩ := hWC3 ↥X K' hK'n hK'simple hK'nonab hK'cat hKcent h3K Q hKQ hΩ _ hAle hAc
  apply hg2
  have hxR : x ∈ (R : Subgroup Y) := hER (mem_sup_right (mem_zpowers x))
  have hxA : (⟨x, hzx (mem_zpowers x)⟩ : ↥X) ∈ (zpowers x).subgroupOf X :=
    Subgroup.mem_subgroupOf.mpr (mem_zpowers x)
  have hgx : (g : Y) * x * (g : Y)⁻¹ ∈ Rh := by
    have h1 := hg1 (Subgroup.mem_map_of_mem _ hxA)
    rw [hQ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hmap : (zpowers x).map (MulAut.conj (g : Y)).toMonoidHom ≤ (R : Subgroup Y) := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    exact hR hgx
  have hw := h.weakClosed R hxR (g : Y) hmap
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rintro _ ⟨a, ha, rfl⟩
  refine Subgroup.mem_subgroupOf.mpr ?_
  have ha' : (a : Y) ∈ zpowers x := Subgroup.mem_subgroupOf.mp ha
  have : (g : Y) * (a : Y) * (g : Y)⁻¹ ∈ (zpowers x).map (MulAut.conj (g : Y)).toMonoidHom :=
    ⟨a, ha', rfl⟩
  rw [hw] at this
  exact this

theorem le_pCore (d : Data Y x Z S O) (hInn : KFactInnerAction)
    (hWC3 : KFactWeakClosureOmega3) : Z ≤ CFSG.pCore 3 Y := by
  by_contra hZ
  have h := d.hyp
  obtain ⟨K, hK, hZK⟩ := d.exists_component_not_centralized hZ
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    have := d.isElemAbelian.1
    exact fun a ha b hb => setLike_mul_comm ha hb
  have hZN : ∀ z ∈ Z, z ∈ normalizer (K : Set Y) := fun z hz =>
    h.mem_normalizer_of_pow_three hK (d.isElemAbelian.2 z hz)
  have hxN : x ∈ normalizer (K : Set Y) := h.mem_normalizer_of_pow_three hK h.pow_eq_one
  have hxC : x ∉ centralizer (K : Set Y) := by
    intro hxC
    refine hZK (h.centralizes_of_le_centralizer hZab hZN d.coprime d.le_centralizer
      d.normalizes_O d.normalizes_ZO hK fun k hk => ?_)
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC k hk)
  by_cases hS : ∀ s ∈ S, s ∈ normalizer (K : Set Y)
  · exact d.false_of_normalized hWC3 hK hS hZN hxN hxC hZK
  · push Not at hS
    obtain ⟨s, hs, hsK⟩ := hS
    have hcyc := d.isCyclic_sylow_of_moved hK hsK
    have hxK := d.mem_of_isCyclic_sylow hInn hK hxN hxC hcyc
    exact hsK (h.mem_normalizer_of_mem hK hxK (d.centralizes s hs))

end Data

theorem isElemAbelian_map_hom {A B : Type*} [Group A] [Group B] (f : A →* B) {E : Subgroup A}
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) := by
  have hcomm := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨a', ha', ha'f⟩ := a.2
    obtain ⟨b', hb', hb'f⟩ := b.2
    apply Subtype.ext
    show (a : B) * b = b * a
    rw [← ha'f, ← hb'f, ← map_mul, ← map_mul]
    exact congrArg f (setLike_mul_comm ha' hb')
  · obtain ⟨z', hz', rfl⟩ := hz
    rw [← map_pow, hE.2 z' hz', map_one]

theorem isElemAbelian_comap_of_injective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) {D : Subgroup B} (hD : IsElemAbelian 3 D) :
    IsElemAbelian 3 (D.comap f) := by
  have hcomm := hD.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
  · apply Subtype.ext
    show (a : A) * b = b * a
    apply hf
    rw [map_mul, map_mul]
    exact setLike_mul_comm (Subgroup.mem_comap.mp a.2) (Subgroup.mem_comap.mp b.2)
  · apply hf
    rw [map_pow, map_one]
    exact hD.2 _ (Subgroup.mem_comap.mp hz)

theorem omega_range {A B : Type*} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f)
    (hom : ∀ a b : A, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a) :
    ∀ u ∈ f.range, ∀ v ∈ f.range, u ^ 3 = 1 → v ^ 3 = 1 → u * v = v * u := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hu hv
  have ha : a ^ 3 = 1 := hf (by rw [map_pow, map_one]; exact hu)
  have hb : b ^ 3 = 1 := hf (by rw [map_pow, map_one]; exact hv)
  rw [← map_mul, ← map_mul, hom a b ha hb]

theorem rank_range {A B : Type*} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f)
    (hrk : ∀ E : Subgroup A, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3) :
    ∀ D : Subgroup B, D ≤ f.range → IsElemAbelian 3 D → Nat.card D ≤ 3 ^ 3 := by
  intro D hD hDel
  have h1 : (D.comap f).map f = D := Subgroup.map_comap_eq_self hD
  have h2 : Nat.card D = Nat.card (D.comap f) := by
    conv_lhs => rw [← h1]
    exact Subgroup.card_map_of_injective hf
  rw [h2]
  exact hrk _ (isElemAbelian_comap_of_injective hf hDel)

theorem omega_rank_of_sylow {Y : Type*} [Group Y] [Finite Y] (R₀ : Sylow 3 Y)
    (hom : ∀ a ∈ (R₀ : Subgroup Y), ∀ b ∈ (R₀ : Subgroup Y), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a)
    (hrk : ∀ B : Subgroup Y, B ≤ (R₀ : Subgroup Y) → IsElemAbelian 3 B → Nat.card B ≤ 3 ^ 3)
    (R : Sylow 3 Y) :
    (∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y), a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a) ∧
    (∀ B : Subgroup Y, B ≤ (R : Subgroup Y) → IsElemAbelian 3 B → Nat.card B ≤ 3 ^ 3) := by
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y R₀ R
  have h : ((c • R₀ : Sylow 3 Y) : Subgroup Y) = (R : Subgroup Y) := by rw [hc]
  rw [Sylow.coe_subgroup_smul] at h
  have hmem : ∀ y ∈ (R : Subgroup Y), c⁻¹ * y * c ∈ (R₀ : Subgroup Y) := by
    intro y hy
    rw [← h, Subgroup.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    show c⁻¹ * (c * z * c⁻¹) * c ∈ (R₀ : Subgroup Y)
    rw [this]
    exact hz
  constructor
  · intro a ha b hb ha3 hb3
    have h3 : ∀ y : Y, y ^ 3 = 1 → (c⁻¹ * y * c) ^ 3 = 1 := fun y hy => by
      rw [show c⁻¹ * y * c = c⁻¹ * y * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hy, mul_one,
        mul_inv_cancel]
    have := hom _ (hmem a ha) _ (hmem b hb) (h3 a ha3) (h3 b hb3)
    calc a * b = c * (c⁻¹ * a * c * (c⁻¹ * b * c)) * c⁻¹ := by group
      _ = c * (c⁻¹ * b * c * (c⁻¹ * a * c)) * c⁻¹ := by rw [this]
      _ = b * a := by group
  · intro B hB hBel
    have hB' : B.map (MulAut.conj c⁻¹).toMonoidHom ≤ (R₀ : Subgroup Y) := by
      rintro _ ⟨y, hy, rfl⟩
      have := hmem y (hB hy)
      simpa [MulAut.conj_apply] using this
    have hcard : Nat.card (B.map (MulAut.conj c⁻¹).toMonoidHom) = Nat.card B :=
      Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
    rw [← hcard]
    exact hrk _ hB' (isElemAbelian_map_hom _ hBel)

theorem eq_one_of_mk_eq_one {H : Type*} [Group H] [Finite H] {T : Subgroup H}
    (hT : IsPGroup 3 T) {t : H} (ht : t ∈ T)
    (h : QuotientGroup.mk' (primeComplementCore (G := H) 3) t = 1) : t = 1 := by
  have hO : t ∈ primeComplementCore (G := H) 3 := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
  have htn : t ^ 3 ^ n = 1 := congrArg Subtype.val hn
  have h1 : orderOf t ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one htn
  have h2 : orderOf t ∣ Nat.card (primeComplementCore (G := H) 3) :=
    Subgroup.orderOf_dvd_natCard _ hO
  have h3 := Nat.eq_one_of_dvd_coprimes ((primeComplementCore_coprime 3).pow_left n) h1 h2
  exact orderOf_eq_one_iff.mp h3

theorem center_eq_bot_of_kfact (hCen : KFactCentralOmega) {Y : Type} [Group Y] [Finite Y]
    (hcore : primeComplementCore (G := Y) 3 = ⊥) (hcat : CatalogSimpleSections Y)
    (homega : ∀ R : Sylow 3 Y, ∀ a ∈ (R : Subgroup Y), ∀ b ∈ (R : Subgroup Y),
      a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a)
    (hrank : ∀ R : Sylow 3 Y, ∀ B : Subgroup Y, B ≤ (R : Subgroup Y) → IsElemAbelian 3 B →
      Nat.card B ≤ 3 ^ 3)
    (K : Subgroup Y) (hK : IsComponentOf K ⊤) : center K = ⊥ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hKcore : primeComplementCore (G := K) 3 = ⊥ :=
    cfsg_subnormal_primeComplementCore_eq_bot 3 K hK.2.1 hcore
  have hZle : center K ≤ CFSG.pCore 3 K := trivial_primeComplementCore_center_le_pCore 3 hp hKcore
  have hZp : IsPGroup 3 (center K) := (CFSG.pCore_isPGroup (p := 3) (G := K)).to_le hZle
  by_contra hZ
  have hdvd : 3 ∣ Nat.card (center K) := by
    rcases hZp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hZ
    · exact h
  have hsimple : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
    hK.2.2
  have hcatK : IsCatalogGroup (K ⧸ center K) :=
    hcat.surjective_image K (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _) hnonab
  have hrk : CFSG.Open.pRank 3 (⊤ : Subgroup K) < 4 := by
    refine lt_of_le_of_lt (csSup_le' fun r hr => ?_) (by norm_num : 3 < 4)
    obtain ⟨E, -, hE, hcard⟩ := hr
    have hEY : IsPGroup 3 (E.map K.subtype) := (elementary_isPGroup 3 E hE).map _
    obtain ⟨R, hR⟩ := hEY.exists_le_sylow
    have h27 := hrank R (E.map K.subtype) hR (isElemAbelian_map_hom K.subtype hE)
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcard] at h27
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h27
  obtain ⟨S⟩ : Nonempty (Sylow 3 K) := inferInstance
  refine hCen K hK.2.2 hcatK hdvd hrk S ?_
  intro s hs t ht hs3 ht3
  have hSp : IsPGroup 3 ((S : Subgroup K).map K.subtype) := S.isPGroup'.map _
  obtain ⟨R, hR⟩ := hSp.exists_le_sylow
  have h1 : (s : Y) ∈ (R : Subgroup Y) := hR ⟨s, hs, rfl⟩
  have h2 : (t : Y) ∈ (R : Subgroup Y) := hR ⟨t, ht, rfl⟩
  exact Subtype.ext (homega R _ h1 _ h2 (by simpa using congrArg Subtype.val hs3)
    (by simpa using congrArg Subtype.val ht3))

theorem conj_mem_sup_of_data
    (hK : CFSG.Open.IsKProper G) (hInn : KFactInnerAction) (hWC3 : KFactWeakClosureOmega3)
    (hCen : KFactCentralOmega)
    {P : Sylow 3 G} {M : Subgroup G} (hMtop : M ≠ ⊤) (hPM : (P : Subgroup G) ≤ M)
    {x : G} (hxP : x ∈ (P : Subgroup G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    {E : Subgroup G} (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3)
    (hΩ : ∀ y ∈ (P : Subgroup G), y ^ 3 = 1 → y ∈ E)
    {K₀ : Subgroup G} (hK₀P : K₀ ≤ (P : Subgroup G)) (hK₀C : K₀ ≤ centralizer ({x} : Set G))
    (hK₀el : IsElemAbelian 3 K₀) (hK₀card : Nat.card K₀ = 9) (hxK₀ : x ∉ K₀)
    (htrans : ∀ a ∈ K₀, ∀ b ∈ K₀, a ≠ 1 → b ≠ 1 → ∃ n ∈ centralizer ({x} : Set G),
      n ∈ normalizer (K₀ : Set G) ∧ n * a * n⁻¹ = b)
    (hNM : normalizer (K₀ : Set G) ≤ M)
    (hOxM : GLBPrimeCore 3 (centralizer ({x} : Set G)) ≤ M)
    (hCM : M ⊓ centralizer ({x} : Set G) ≤
      normalizer ((K₀ ⊔ GLBPrimeCore 3 (centralizer ({x} : Set G)) : Subgroup G) : Set G)) :
    ∀ m ∈ M, ∀ q ∈ K₀, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hxM : x ∈ M := hPM hxP
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hK₀M : K₀ ≤ M := hK₀P.trans hPM
  have hxo' : orderOf (⟨x, hxM⟩ : M) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxo
  set O : Subgroup M := primeComplementCore (G := M) 3
  set π : M →* M ⧸ O := QuotientGroup.mk' O
  set xb : M ⧸ O := π ⟨x, hxM⟩ with hxb
  have hπc : ∀ a b : M, π (a * b * a⁻¹) = π a * π b * (π a)⁻¹ := fun a b => by
    rw [map_mul, map_mul, map_inv]
  set PM : Subgroup M := (P : Subgroup G).subgroupOf M with hPMdef
  have hPMp : IsPGroup 3 PM := P.isPGroup'.comap_subtype
  have hxPM : (⟨x, hxM⟩ : M) ∈ PM := mem_subgroupOf.mpr hxP
  have hinj : ∀ a ∈ PM, ∀ b ∈ PM, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.mp (eq_one_of_mk_eq_one hPMp (PM.mul_mem (PM.inv_mem ha) hb) h1)
  set φ : ↥(P : Subgroup G) →* M ⧸ O := π.comp (Subgroup.inclusion hPM) with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have := hinj (Subgroup.inclusion hPM a) (mem_subgroupOf.mpr a.2)
      (Subgroup.inclusion hPM b) (mem_subgroupOf.mpr b.2) hab
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have hrange : φ.range = PM.map π := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Subgroup.inclusion hPM a, mem_subgroupOf.mpr a.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨(m : G), mem_subgroupOf.mp hm⟩, rfl⟩
  have hPcomm : ∀ a b : ↥(P : Subgroup G), a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a := by
    intro a b ha hb
    have hEc := hEel.1
    have ha' : (a : G) ∈ E := hΩ a a.2 (by simpa using congrArg Subtype.val ha)
    have hb' : (b : G) ∈ E := hΩ b b.2 (by simpa using congrArg Subtype.val hb)
    exact Subtype.ext (setLike_mul_comm ha' hb')
  have hPrank : ∀ B : Subgroup ↥(P : Subgroup G), IsElemAbelian 3 B → Nat.card B ≤ 3 ^ 3 := by
    intro B hB
    have hle : B.map (P : Subgroup G).subtype ≤ E := by
      rintro _ ⟨b, hb, rfl⟩
      exact hΩ b b.2 (by simpa using congrArg Subtype.val (hB.2 b hb))
    calc Nat.card B = Nat.card (B.map (P : Subgroup G).subtype) :=
          (Subgroup.card_map_of_injective (P : Subgroup G).subtype_injective).symm
      _ ≤ Nat.card E := Subgroup.card_le_of_le hle
      _ = 3 ^ 3 := hEcard
  have hPsyl : IsSylowOf 3 (P : Subgroup G) M := isSylowOf_iff.mpr ⟨hPM, P.isPGroup', fun hdvd =>
    P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPM))⟩
  obtain ⟨R, hR⟩ : ∃ R : Sylow 3 (M ⧸ O), (R : Subgroup (M ⧸ O)) = PM.map π := by
    obtain ⟨-, hp', hdvd⟩ := isSylowOf_iff.1 (isSylowOf_top_map_mk hPsyl)
    rw [Subgroup.relIndex_top_right] at hdvd
    exact ⟨hp'.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩
  have hωR : ∀ a ∈ (R : Subgroup (M ⧸ O)), ∀ b ∈ (R : Subgroup (M ⧸ O)),
      a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a := by
    rw [hR, ← hrange]
    exact omega_range φ hφinj hPcomm
  have hρR : ∀ B : Subgroup (M ⧸ O), B ≤ (R : Subgroup (M ⧸ O)) → IsElemAbelian 3 B →
      Nat.card B ≤ 3 ^ 3 := by
    rw [hR, ← hrange]
    exact rank_range φ hφinj hPrank
  have hall := omega_rank_of_sylow R hωR hρR
  have homega : ∀ R' : Sylow 3 (M ⧸ O), ∀ a ∈ (R' : Subgroup (M ⧸ O)),
      ∀ b ∈ (R' : Subgroup (M ⧸ O)), a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a :=
    fun R' => (hall R').1
  have hrank : ∀ R' : Sylow 3 (M ⧸ O), ∀ B : Subgroup (M ⧸ O),
      B ≤ (R' : Subgroup (M ⧸ O)) → IsElemAbelian 3 B → Nat.card B ≤ 3 ^ 3 :=
    fun R' => (hall R').2
  have hcore : primeComplementCore (G := M ⧸ O) 3 = ⊥ := primeComplementCore_quotient_eq_bot 3
  have hcat : CatalogSimpleSections (M ⧸ O) :=
    (catalogSimpleSections_of_isKProper hK M hMtop).quotient O
  have hcen := center_eq_bot_of_kfact hCen hcore hcat homega hrank
  have hne : xb ≠ 1 := by
    intro h1
    exact hx1 (congrArg Subtype.val (eq_one_of_mk_eq_one hPMp hxPM h1))
  have hpow : xb ^ 3 = 1 := by
    rw [hxb, ← map_pow]
    have : (⟨x, hxM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hO' : GLBPrimeCore 3 M ≤ M := glbPrimeCore_le 3 M
  have hMO : M ≤ normalizer (GLBPrimeCore 3 M : Set G) := le_normalizer_glbPrimeCore 3 M
  have hPO : (P : Subgroup G) ≤ normalizer (GLBPrimeCore 3 M : Set G) := hPM.trans hMO
  have hwcR : ∀ g : M ⧸ O,
      (zpowers xb).map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup (M ⧸ O)) →
        (zpowers xb).map (MulAut.conj g).toMonoidHom = zpowers xb := by
    intro g hg
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective O g
    have hgx : π g₁ * xb * (π g₁)⁻¹ ∈ (R : Subgroup (M ⧸ O)) :=
      hg ⟨xb, mem_zpowers xb, rfl⟩
    rw [hR] at hgx
    obtain ⟨u, hu, hue⟩ := hgx
    set y : M := g₁ * ⟨x, hxM⟩ * g₁⁻¹ with hy
    have hπy : π u = π y := by rw [hue, hy, hπc, hxb]
    have hco : u⁻¹ * y ∈ O := QuotientGroup.eq.mp hπy
    have hyG : (y : G) ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M := by
      have hu' : (u : G) ∈ (P : Subgroup G) := mem_subgroupOf.mp hu
      have hr : ((u⁻¹ * y : M) : G) ∈ GLBPrimeCore 3 M :=
        (mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mp hco
      have : (y : G) = (u : G) * ((u⁻¹ * y : M) : G) := by simp
      rw [this]
      exact Subgroup.mul_mem _ (mem_sup_left hu') (mem_sup_right hr)
    have hyG' : (y : G) = (g₁ : G) * x * (g₁ : G)⁻¹ := by simp [hy]
    have hy3 : (y : G) ^ 3 = 1 := by rw [hyG', conj_pow, hx3, mul_one, mul_inv_cancel]
    have hK₁p : IsPGroup 3 (zpowers (y : G)) :=
      elementary_isPGroup 3 _ (CFSG.AGLEmbedding.isElemAbelian_zpowers hy3)
    have hK₁W : zpowers (y : G) ≤ (P : Subgroup G) ⊔ GLBPrimeCore 3 M :=
      zpowers_le.mpr hyG
    obtain ⟨o, hoO, hoy⟩ := exists_conj_le_of_isPGroup hPO hK₁p hK₁W
    have hoyP : o * (y : G) * o⁻¹ ∈ (P : Subgroup G) := hoy _ (mem_zpowers _)
    have hoM : o ∈ M := hO' hoO
    have hnorm : o * (g₁ : G) ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
      refine normalizer_of_lwc hwc ?_
      have e : o * (g₁ : G) * x * (o * (g₁ : G))⁻¹ = o * (y : G) * o⁻¹ := by
        rw [hyG']
        group
      rw [e]
      exact hoyP
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ((mem_normalizer_iff.mp hnorm x).mp (mem_zpowers x))
    have hōmem : (⟨o, hoM⟩ : M) ∈ O := (mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mpr hoO
    have hō1 : π ⟨o, hoM⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hōmem
    have hkM : (⟨o, hoM⟩ * g₁) * ⟨x, hxM⟩ * (⟨o, hoM⟩ * g₁)⁻¹ = (⟨x, hxM⟩ : M) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    have hkq : π g₁ * xb * (π g₁)⁻¹ = xb ^ k := by
      have h1 := congrArg π hkM
      rw [hπc, map_mul, hō1, one_mul, map_zpow] at h1
      exact h1
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [MonoidHom.map_zpowers, zpowers_le]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkq]
      exact zpow_mem (mem_zpowers _) k
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
  have hHyp : Hyp (M ⧸ O) xb :=
    { core_eq_bot := hcore
      catalog := hcat
      omega := homega
      rank := hrank
      center_eq_bot := hcen
      ne_one := hne
      pow_eq_one := hpow
      weakClosed := fun Q hxQ g hg => weakClosed_sylow hwcR Q hxQ g hg }
  set Z : Subgroup (M ⧸ O) := (K₀.subgroupOf M).map π with hZ
  have hZmem : ∀ z, z ∈ Z ↔ ∃ m : M, (m : G) ∈ K₀ ∧ π m = z := by
    intro z
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, mem_subgroupOf.mp hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, mem_subgroupOf.mpr hm, rfl⟩
  have hZelem : IsElemAbelian 3 Z := by
    have hK₀comm : IsMulCommutative K₀ := hK₀el.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨m₁, hm₁, h₁⟩ := (hZmem a).mp a.2
      obtain ⟨m₂, hm₂, h₂⟩ := (hZmem b).mp b.2
      apply Subtype.ext
      show (a : M ⧸ O) * b = b * a
      rw [← h₁, ← h₂, ← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext (setLike_mul_comm hm₁ hm₂))
    · obtain ⟨m, hm, rfl⟩ := (hZmem z).mp hz
      rw [← map_pow]
      have : m ^ 3 = 1 := Subtype.ext (by simpa using hK₀el.2 (m : G) hm)
      rw [this, map_one]
  have hZcard9 : Nat.card Z = 9 := by
    have hK₀p : IsPGroup 3 (K₀.subgroupOf M) := (elementary_isPGroup 3 K₀ hK₀el).comap_subtype
    rw [hZ, CFSG.AGLEmbedding.card_map_mk_of_isPGroup hp O (primeComplementCore_coprime 3) hK₀p,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₀M).toEquiv, hK₀card]
  have hZcard : Nat.card Z = 3 ^ 2 := by
    rw [hZcard9]
    norm_num
  have hZc : Z ≤ centralizer ({xb} : Set (M ⧸ O)) := by
    intro z hz
    obtain ⟨m, hm, rfl⟩ := (hZmem z).mp hz
    rw [mem_centralizer_singleton_iff, hxb, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (mem_centralizer_singleton_iff.mp (hK₀C hm)))
  have hxnZ : xb ∉ Z := by
    intro hxZ
    obtain ⟨m, hm, hme⟩ := (hZmem xb).mp hxZ
    have hmPM : m ∈ PM := mem_subgroupOf.mpr (hK₀P hm)
    have := hinj m hmPM ⟨x, hxM⟩ hxPM hme
    rw [this] at hm
    exact hxK₀ hm
  set S : Set (M ⧸ O) := {s | s * xb * s⁻¹ = xb ∧ ∀ z ∈ Z, s * z * s⁻¹ ∈ Z}
  have hirr : ∀ D : Subgroup (M ⧸ O), D ≤ Z → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) →
      D = ⊥ ∨ D = Z := by
    intro D hDZ hDS
    by_cases hD : D = ⊥
    · exact Or.inl hD
    refine Or.inr (le_antisymm hDZ fun z hz => ?_)
    obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hD ((Subgroup.eq_bot_iff_forall D).mpr hcon)
    by_cases hz1 : z = 1
    · rw [hz1]
      exact D.one_mem
    obtain ⟨ma, hma, rfl⟩ := (hZmem d).mp (hDZ hdD)
    obtain ⟨mb, hmb, rfl⟩ := (hZmem z).mp hz
    have ha1 : (ma : G) ≠ 1 := fun h => hd1 (by
      have : ma = 1 := Subtype.ext h
      rw [this, map_one])
    have hb1 : (mb : G) ≠ 1 := fun h => hz1 (by
      have : mb = 1 := Subtype.ext h
      rw [this, map_one])
    obtain ⟨n, hnC, hnN, hnab⟩ := htrans _ hma _ hmb ha1 hb1
    have hnM : n ∈ M := hNM hnN
    have hs : π ⟨n, hnM⟩ ∈ S := by
      refine ⟨?_, fun z' hz' => ?_⟩
      · have h1 : n * x = x * n := mem_centralizer_singleton_iff.mp hnC
        rw [hxb, ← hπc]
        exact congrArg π (Subtype.ext (show n * x * n⁻¹ = x by rw [h1, mul_inv_cancel_right]))
      · obtain ⟨m', hm', rfl⟩ := (hZmem z').mp hz'
        have hnm : n * (m' : G) * n⁻¹ ∈ K₀ := (mem_normalizer_iff.mp hnN _).mp hm'
        refine (hZmem _).mpr ⟨⟨n * (m' : G) * n⁻¹,
          M.mul_mem (M.mul_mem hnM m'.2) (M.inv_mem hnM)⟩, hnm, ?_⟩
        exact hπc ⟨n, hnM⟩ m'
    have hconj : π ⟨n, hnM⟩ * π ma * (π ⟨n, hnM⟩)⁻¹ = π mb := by
      rw [← hπc]
      exact congrArg π (Subtype.ext hnab)
    have := hDS _ hs _ hdD
    rwa [hconj] at this
  set Cx : Subgroup G := centralizer ({x} : Set G)
  set Ox : Subgroup G := GLBPrimeCore 3 Cx
  set Ob : Subgroup (M ⧸ O) := (Ox.subgroupOf M).map π
  have hObcop : ¬ 3 ∣ Nat.card Ob := by
    intro hdvd
    have h1 : Nat.card Ob ∣ Nat.card (Ox.subgroupOf M) :=
      Subgroup.card_dvd_of_surjective (f := π.subgroupMap (Ox.subgroupOf M))
        (π.subgroupMap_surjective _)
    have h2 : Nat.card (Ox.subgroupOf M) = Nat.card Ox :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOxM).toEquiv
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 Cx)
      (h2 ▸ hdvd.trans h1)
  have hObC : Ob ≤ centralizer ({xb} : Set (M ⧸ O)) := by
    rintro _ ⟨m, hm, rfl⟩
    have hmC : (m : G) ∈ Cx := CFSG.AGLEmbedding.glbPrimeCore_le 3 Cx (mem_subgroupOf.mp hm)
    rw [mem_centralizer_singleton_iff, hxb, ← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (mem_centralizer_singleton_iff.mp hmC))
  have hCy : centralizer ({xb} : Set (M ⧸ O)) ≤ ((M ⊓ Cx).subgroupOf M).map π :=
    (centralizer_mk_le_map hp hxo').trans (Subgroup.map_mono fun c
      (hc : c ∈ centralizer ({(⟨x, hxM⟩ : M)} : Set M)) => mem_subgroupOf.mpr
      ⟨c.2, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))⟩)
  have hnormO : centralizer ({xb} : Set (M ⧸ O)) ≤ normalizer (Ob : Set (M ⧸ O)) :=
    hCy.trans (map_subgroupOf_le_normalizer_map
      (fun c (hc : c ∈ M ⊓ Cx) => CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 Cx hc.2) π)
  have hZO : Z ⊔ Ob = ((K₀ ⊔ Ox).subgroupOf M).map π := by
    rw [Subgroup.subgroupOf_sup hK₀M hOxM, Subgroup.map_sup]
  have hnormZO : centralizer ({xb} : Set (M ⧸ O)) ≤
      normalizer ((Z ⊔ Ob : Subgroup (M ⧸ O)) : Set (M ⧸ O)) := by
    rw [hZO]
    exact hCy.trans (map_subgroupOf_le_normalizer_map hCM π)
  have hdata : Data (M ⧸ O) xb Z S Ob :=
    { hyp := hHyp
      isElemAbelian := hZelem
      card_eq := hZcard
      x_not_mem := hxnZ
      le_centralizer := hZc
      centralizes := fun s hs => hs.1
      normalizes := fun s hs => hs.2
      irreducible := hirr
      coprime := hObcop
      O_le_centralizer := hObC
      normalizes_O := hnormO
      normalizes_ZO := hnormZO }
  have hZp : Z ≤ CFSG.pCore 3 (M ⧸ O) := hdata.le_pCore hInn hWC3
  intro m hm q hq
  have hqM : q ∈ M := hK₀M hq
  have hmq : m * q * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hqM) (M.inv_mem hm)
  have hZq : π ⟨q, hqM⟩ ∈ Z := (hZmem _).mpr ⟨⟨q, hqM⟩, hq, rfl⟩
  have hcj : π ⟨m * q * m⁻¹, hmq⟩ = π ⟨m, hm⟩ * π ⟨q, hqM⟩ * (π ⟨m, hm⟩)⁻¹ :=
    hπc ⟨m, hm⟩ ⟨q, hqM⟩
  have hpc : π ⟨m * q * m⁻¹, hmq⟩ ∈ CFSG.pCore 3 (M ⧸ O) := by
    rw [hcj]
    exact (CFSG.pCore_normal (p := 3) (G := M ⧸ O)).conj_mem _ (hZp hZq) _
  have hpR : π ⟨m * q * m⁻¹, hmq⟩ ∈ (R : Subgroup (M ⧸ O)) :=
    CFSG.pCore_isPGroup.le_sylow_of_normal R hpc
  rw [hR] at hpR
  obtain ⟨p', hp', hp'eq⟩ := hpR
  have hp'P : (p' : G) ∈ (P : Subgroup G) := mem_subgroupOf.mp hp'
  have hr : (p' : G)⁻¹ * (m * q * m⁻¹) ∈ M := M.mul_mem (M.inv_mem p'.2) hmq
  have hker : π ⟨(p' : G)⁻¹ * (m * q * m⁻¹), hr⟩ = 1 := by
    have e : (⟨(p' : G)⁻¹ * (m * q * m⁻¹), hr⟩ : M) = p'⁻¹ * ⟨m * q * m⁻¹, hmq⟩ := rfl
    rw [e, map_mul, map_inv, hp'eq, inv_mul_cancel]
  have hrO : (p' : G)⁻¹ * (m * q * m⁻¹) ∈ GLBPrimeCore 3 M :=
    (mk'_primeComplementCore_eq_one_iff 3 _).mp hker
  have : m * q * m⁻¹ = (p' : G) * ((p' : G)⁻¹ * (m * q * m⁻¹)) := by group
  rw [this]
  exact Subgroup.mul_mem _ (mem_sup_left hp'P) (mem_sup_right hrO)

end Quotient

end GL83P3L34Aux

@[expose] def L34CaseOne (p : ℕ) {G : Type} [Group G] [Finite G] (P : Sylow p G)
    (M J : Subgroup G) : Prop :=
  ∀ m ∈ M, ∀ q ∈ (P : Subgroup G) ⊓ J, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore p M

@[expose] def GL83P3L34CaseOne (G : Type) [Group G] [Finite G] : Prop :=
  GenericL34At G fun p P M _ J => L34CaseOne p P M J

theorem gl83P3L34_remark_of_caseOne (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (h : GL83P3L34CaseOne G) : GL83GenericPrimeThreeL34Remark G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsL34Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have h34 := l34_prop34 hS hU0 hD1 hL.twoSignalizer hL.three hL.sylowTransitive
    hL.outerCentralizer hSig hp hM hgen hJ
  have hSC := GL83P3L34Aux.strongClosed hS hU0 hL.twoSignalizer hL.three hp hM hgen hJ h34
  have hc1 : L34CaseOne 3 P M J :=
    h 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  exact GL83P3L34Aux.normalizer_of_conj hPM inf_le_left P.isPGroup'.to_inf_left hc1 hSC

theorem gl83P3L34_caseOne_of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (hInn : KFactInnerAction) (hWC3 : KFactWeakClosureOmega3)
    (hCen : KFactCentralOmega) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G}
    {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x)
    {J : Subgroup G} (hJ : IsL34Normal M x J) : L34CaseOne 3 P M J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hS.simple
  have h34 := l34_prop34 hS hU0 hD1 hL.twoSignalizer hL.three hL.sylowTransitive
    hL.outerCentralizer hSig hp hM hgen hJ
  obtain ⟨-, hEel, hEcard, hΩ, hwc⟩ := h34
  have hxP : x ∈ (P : Subgroup G) := hgen.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hx3 : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hK₀card : Nat.card ↥((P : Subgroup G) ⊓ J) = 3 ^ 2 :=
    l34Sign_card_inf hS hU0 hL.twoSignalizer hL.three hp hM hgen hJ
  have hK₀E : (P : Subgroup G) ⊓ J ≤ ((P : Subgroup G) ⊓ J) ⊔ zpowers x := le_sup_left
  have hK₀el : IsElemAbelian 3 ((P : Subgroup G) ⊓ J) := by
    have := hEel.1
    exact ⟨⟨⟨fun a b => Subtype.ext (setLike_mul_comm (hK₀E a.2) (hK₀E b.2))⟩⟩,
      fun a ha => hEel.2 a (hK₀E ha)⟩
  have hD2 : 2 ≤ CFSG.Open.pRank 3 ((P : Subgroup G) ⊓ J) :=
    le_pRank_of_elemAbelian_card (p := 3) (k := 2) le_rfl hK₀el hK₀card
  have hNM : normalizer ((((P : Subgroup G) ⊓ J : Subgroup G)) : Set G) ≤ M := by
    refine le_trans ?_ (hU0 3 hp P M hM)
    unfold rankThreeGamma CFSG.Open.GLBCore
    exact le_sSup ⟨(P : Subgroup G) ⊓ J, inf_le_left, hD2, rfl⟩
  obtain ⟨hOxM, hCM⟩ := GL83P3L34Aux.point_facts hS hU0 hL.three hp hM hgen hJ hK₀el hK₀card
  have htrans := l34_transitive hL.sylowTransitive hgen hJ
  have hMtop : M ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hM.1.1
  have hxK₀ : x ∉ (P : Subgroup G) ⊓ J := fun hx =>
    l34_x_not_mem_J hS hU0 hL.twoSignalizer hL.three hp hM hgen hJ hx.2
  exact GL83P3L34Aux.conj_mem_sup_of_data hS.kProper hInn hWC3 hCen hMtop hPM hxP hx3 hx1 hwc
    hEel hEcard hΩ inf_le_left (inf_le_right.trans hJ.le_centralizer) hK₀el
    (by simpa using hK₀card) hxK₀ htrans hNM hOxM hCM

theorem gl83P3L34_remark_of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (hInn : KFactInnerAction) (hWC3 : KFactWeakClosureOmega3)
    (hCen : KFactCentralOmega) : GL83GenericPrimeThreeL34Remark G := by
  refine gl83P3L34_remark_of_caseOne hS hU0 hD1 hSig hL ?_
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsL34Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  exact gl83P3L34_caseOne_of_kfacts hS hU0 hD1 hSig hL hInn hWC3 hCen hp hM hgen hJ

section Closed

theorem gl83P3L34_holds (hWC3 : KFactWeakClosureOmega3) (hCen : KFactCentralOmega) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeL34Remark G :=
  fun _ _ _ hS hD1 hU0 => gl83P3L34_remark_of_kfacts hS hU0 hD1
    KFactProofs.Stroth.TwoSignalizer.signalizerTwoGroupKFact_holds
    ⟨⟨l34TwoSignalizer_proved, kFactL34Three, kFactL34Unitary, kFactL34Borel, kFactL34Graph,
      kFactL34OutThree, kFactL34SylowCentralizer, kFactL34ThreeExponent⟩,
      kFactL34SylowTransitive, l34OuterCentralizer_proved⟩
    KFactProofs.Stroth.InnerAction.kFactInnerAction_holds hWC3 hCen

end Closed

end CFSG.LocalAnalysis.RankThreeTheoremC
