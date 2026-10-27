module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenOuter
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveInner
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveInnerBlocks
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.Fischer.Classification.Recognition.Basic
public import CFSG.Monster.B.TwoA.Census.PermClasses
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe (hatOf)
open CFSG.LocalAnalysis.ComponentInitial

namespace AltTen

theorem isFiveComponent_map {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {C : Subgroup X}
    (hC : IsComponentOf C ⊤ ∧ ∃ f : ↥C →* alternatingGroup (Fin 5), Function.Surjective f) :
    IsComponentOf (C.map e.toMonoidHom) ⊤ ∧
      ∃ f : ↥(C.map e.toMonoidHom) →* alternatingGroup (Fin 5), Function.Surjective f := by
  obtain ⟨⟨-, hs, hq⟩, f, hf⟩ := hC
  let eC := C.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨⟨le_top, ?_, LeviBlock.isQuasisimple_of_mulEquiv eC hq⟩, f.comp eC.symm.toMonoidHom,
    hf.comp eC.symm.surjective⟩
  have := hs.map e.toMonoidHom
  rwa [Subgroup.map_top_of_surjective _ e.surjective] at this

theorem exists_hatOf_map_conj {A : Type} [Group A] {P J : Subgroup A} (hJP : J ≤ P) {t : A}
    (htP : t ∈ Subgroup.normalizer (P : Set A)) :
    ∃ τ : (↥P ⧸ CFSG.pCore 2 ↥P) ≃* (↥P ⧸ CFSG.pCore 2 ↥P),
      hatOf P (J.map (MulAut.conj t).toMonoidHom) = (hatOf P J).map τ.toMonoidHom := by
  have hc : ∀ s ∈ Subgroup.normalizer (P : Set A), ∀ x ∈ P, s * x * s⁻¹ ∈ P :=
    fun s hs x hx => (Subgroup.mem_normalizer_iff.mp hs x).mp hx
  let τ₀ : ↥P ≃* ↥P :=
    { toFun := fun x => ⟨t * x * t⁻¹, hc t htP x x.2⟩
      invFun := fun x => ⟨t⁻¹ * x * t⁻¹⁻¹, hc t⁻¹ (inv_mem htP) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  refine ⟨QuotientGroup.congr _ _ τ₀ (CFSG.pCore_map_iso 2 τ₀), ?_⟩
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
    obtain ⟨j, hj, hja⟩ := ha
    refine ⟨QuotientGroup.mk' _ ⟨j, hJP hj⟩, ⟨⟨j, hJP hj⟩, Subgroup.mem_subgroupOf.mpr hj, rfl⟩,
      ?_⟩
    change QuotientGroup.mk (τ₀ ⟨j, hJP hj⟩) = QuotientGroup.mk' _ a
    rw [QuotientGroup.mk'_apply]
    congr 1
    exact Subtype.ext hja
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
    refine ⟨τ₀ a, Subgroup.mem_subgroupOf.mpr ⟨a, ha, rfl⟩, rfl⟩

theorem eq_top_of_isComponentOf {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsQuasisimple X)
    {C : Subgroup X} (hC : IsComponentOf C ⊤) : C = ⊤ := by
  have hX' : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup X) :=
    LeviBlock.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hX
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hC.2.1 hX' with h | h
  · exact h
  · exfalso
    refine LeviBlock.spFlag_not_isSolvable hC.2.2 (isSolvable_of_comm fun a b => ?_)
    obtain ⟨a', ha', ha⟩ := h a.2
    obtain ⟨b', -, hb⟩ := h b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hb]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp ha' b').symm

theorem ne_of_two_components {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hO2 : CFSG.pCore 2 ↥L = ⊥)
    {C₁ C₂ : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)} (h₁ : IsComponentOf C₁ ⊤)
    (h₂ : IsComponentOf C₂ ⊤) (hne : C₁ ≠ C₂) : P ≠ L := by
  rintro rfl
  let e : (↥P ⧸ CFSG.pCore 2 ↥P) ≃* ↥P :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot
  have hX := LeviBlock.isQuasisimple_of_mulEquiv e.symm hLq
  exact hne ((eq_top_of_isComponentOf hX h₁).trans (eq_top_of_isComponentOf hX h₂).symm)

theorem ne_borel_of_alt5 {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)}
    (hC : ∃ f : ↥C →* alternatingGroup (Fin 5), Function.Surjective f) :
    ∀ T : Subgroup Y, IsSylowTwoOf T L → P ≠ L ⊓ Subgroup.normalizer (T : Set Y) := by
  rintro T ⟨hTL, hT2, hTi⟩ hPeq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ := hC
  have hTP : T ≤ P := by rw [hPeq]; exact le_inf hTL Subgroup.le_normalizer
  have hTn : (T.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : Y) ∈ Subgroup.normalizer (T : Set Y) :=
      (hPeq.le (show (g : Y) ∈ P from g.2)).2
    simpa using (Subgroup.mem_normalizer_iff.mp hg n).mp hn⟩
  have hle : T.subgroupOf P ≤ CFSG.pCore 2 ↥P :=
    le_sSup ⟨hTn, hT2.comap_of_injective P.subtype P.subtype_injective⟩
  have h60 : 60 ∣ Nat.card ↥C := by
    have h1 := Subgroup.index_dvd_card f.ker
    rw [Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      nat_card_alternatingGroup, Nat.card_fin] at h1
    exact h1
  have hCP : Nat.card ↥C ∣ (CFSG.pCore 2 ↥P).index := Subgroup.card_subgroup_dvd_card C
  apply hTi
  calc 2 ∣ 60 := by norm_num
    _ ∣ (CFSG.pCore 2 ↥P).index := h60.trans hCP
    _ ∣ (T.subgroupOf P).index := Subgroup.index_dvd_of_le hle
    _ ∣ (T.subgroupOf L).index := Dvd.intro _ (Subgroup.relIndex_mul_relIndex T P L hTP hPL)

theorem odd_card_center_of_pCore_eq_bot {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.pCore 2 Y = ⊥) : Odd (Nat.card (Subgroup.center Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzc : (z : Y) ∈ Subgroup.center Y := z.2
  have hz2 : orderOf (z : Y) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hNc : Subgroup.zpowers (z : Y) ≤ Subgroup.center Y :=
    (Subgroup.zpowers_le).mpr hzc
  have hN : (Subgroup.zpowers (z : Y)).Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.mp (hNc hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  have hN2 : IsPGroup 2 (Subgroup.zpowers (z : Y)) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hz2, pow_orderOf_eq_one,
      one_zpow]
  have hle : Subgroup.zpowers (z : Y) ≤ CFSG.pCore 2 Y := le_sSup ⟨hN, hN2⟩
  rw [h] at hle
  have h1 : (z : Y) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hz2
  omega

theorem compParab_top_subgroupOf {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hYq : CFSG.Open.IsQuasisimple ↥Y) (hO2 : pCoreOf 2 Y = ⊥)
    (htype : IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y)) (hpar : IsParabolicTwo Y P)
    {C₁ C₂ : Subgroup (↥(P.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(P.subgroupOf Y))}
    (h₁ : IsFiveComponent (P.subgroupOf Y) C₁) (h₂ : IsFiveComponent (P.subgroupOf Y) C₂)
    (hne : C₁ ≠ C₂) : CompParab (⊤ : Subgroup ↥Y) (P.subgroupOf Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥Y) :=
    LeviBlock.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hYq
  have hO2Y : CFSG.pCore 2 ↥Y = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hO2
  have hO2top : CFSG.pCore 2 ↥(⊤ : Subgroup ↥Y) = ⊥ := by
    have h := CFSG.pCore_map_iso 2 (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥Y) ≃* ↥Y)
    rw [hO2Y] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).mp h
  obtain ⟨hPY, T, ⟨hTY, hT2, hTi⟩, hNP⟩ := hpar
  refine ⟨⟨le_rfl, IsSubnormal.refl _, hq⟩, ?_, odd_card_center_of_pCore_eq_bot hO2top, ?_,
    ne_of_two_components hq hO2top h₁.1 h₂.1 hne, ne_borel_of_alt5 le_top h₁.2⟩
  ·
    let e : ↥Y ⧸ Subgroup.center ↥Y ≃* ↥(⊤ : Subgroup ↥Y) ⧸ Subgroup.center ↥(⊤ : Subgroup ↥Y) :=
      QuotientGroup.congr _ _ Subgroup.topEquiv.symm (Subgroup.map_center_eq _)
    rcases htype with ⟨d, hd, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨d, hd, ⟨φ⟩⟩
    · exact Or.inl ⟨d, hd, ⟨e.symm.trans φ⟩⟩
    · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans φ⟩⟩)
    · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans φ⟩⟩)
  ·
    refine ⟨le_top, T.subgroupOf Y, ⟨le_top, hT2.comap_of_injective _ Y.subtype_injective, ?_⟩,
      ?_⟩
    · change ¬ 2 ∣ (T.subgroupOf Y).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hTi
    · rintro g ⟨-, hg⟩
      rw [Subgroup.mem_subgroupOf]
      refine hNP ⟨g.2, Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
      · have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨x, hTY hx⟩).mp
          (Subgroup.mem_subgroupOf.mpr hx)
        rw [Subgroup.mem_subgroupOf] at h1
        simpa using h1
      · have hxY : x ∈ Y := by
          have h2 := Y.mul_mem (Y.mul_mem (Y.inv_mem g.2) (hTY hx)) g.2
          simpa [mul_assoc] using h2
        have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨x, hxY⟩).mpr
          (Subgroup.mem_subgroupOf.mpr (by simpa using hx))
        rw [Subgroup.mem_subgroupOf] at h1
        exact h1

theorem survivor_facts {A : Type} [Group A] [Finite A] {Y P : Subgroup A} (hPY : P ≤ Y)
    (hs : TwoFivesSurvivor (⊤ : Subgroup ↥Y) (P.subgroupOf Y)) :
    (∃ (T : Type) (_ : Group T) (_ : ↥Y ⧸ Subgroup.center ↥Y ≃* T),
      ∀ β : MulAut T, (∃ k : ℕ, β ^ 2 ^ k = 1) → ∃ w : T, β ^ 2 = MulAut.conj w) ∧
    ∀ C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), IsFiveComponent P C →
      C.Normal ∧ ∀ x, ∃ c ∈ C, ∀ u ∈ C, x * u * x⁻¹ = c * u * c⁻¹ := by
  classical
  rcases hs with ⟨ρ, e, hρs, hρk, -, hflag⟩ | ⟨K, _, _, _, hK, ρ, hflag⟩
  ·
    have hK4 : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card 2 2 (by norm_num)]; norm_num
    refine ⟨⟨_, inferInstance, (QuotientGroup.congr _ _ Subgroup.topEquiv.symm
      (Subgroup.map_center_eq _)).trans e, fun β _ => sq_inner_projectiveSL_four hK4 β⟩,
      fun C hC => ?_⟩
    let ρA : Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2) →* ↥Y :=
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥Y) ≃* ↥Y).toMonoidHom.comp ρ
    have hρAs : Function.Surjective ρA := Subgroup.topEquiv.surjective.comp hρs
    have hρAk : ρA.ker ≤ Subgroup.center _ := by
      intro x hx
      apply hρk
      rw [MonoidHom.mem_ker] at hx ⊢
      exact Subgroup.topEquiv.injective (by rw [map_one]; exact hx)
    have hQ : (P.subgroupOf Y).comap ρA =
        LinearFlag.flagStabilizer 4 (GaloisField 2 2) {2} := by
      rw [← hflag]
      rfl
    let ι := MulEquiv.subgroupCongr hQ
    let β := (LeviBlock.linLeviHom (GaloisField 2 2) 4 {2}).comp ι.toMonoidHom
    have hrange : β.range = (LeviBlock.linLeviHom (GaloisField 2 2) 4 {2}).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
        ← MonoidHom.range_eq_map]
    have hβ : IsPGroup 2 β.ker := by
      rw [← MonoidHom.comap_ker]
      exact (LeviBlock.isPGroup_ker_linLeviHom (by norm_num)).comap_of_injective _ ι.injective
    refine LeviFive.isFiveComponent_normal_inner hPY ρA hρAs hρAk
      (LeviBlock.linBlockSL (GaloisField 2 2) 4 {2}) β hβ
      (hrange ▸ LeviBlock.pi_le_range_linLeviHom)
      (hrange ▸ LeviBlock.commutator_range_linLeviHom_le)
      (LeviBlock.isQuasisimple_or_isSolvable_linBlockSL {2})
      (fun a hq h60 q => LeviBlock.linLeviHom_inner_of_sixty hK4 a hq h60 (ι q)) hC
  ·
    let ρA : StatedSp 3 K ≃* ↥Y := ρ.trans Subgroup.topEquiv
    refine ⟨⟨_, inferInstance, (QuotientGroup.congr _ _ ρA.symm (Subgroup.map_center_eq _)).trans
      (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv 3 K),
      fun β hβ => sq_inner_projectiveSp hK le_rfl β hβ⟩, fun C hC => ?_⟩
    have hQ : (P.subgroupOf Y).comap ρA.toMonoidHom = SymplecticHigher.flagStabilizer 3 K {2} := by
      rw [← hflag]
      rfl
    let ι := MulEquiv.subgroupCongr hQ
    have hI : ∀ i ∈ ({2} : Set ℕ), i ≤ 3 := by
      intro i hi
      rw [Set.mem_singleton_iff] at hi
      omega
    have htI : (2 : ℕ) ∈ ({2} : Set ℕ) := rfl
    let β := (LeviBlock.spFlagLeviHom (K := K) hI htI).comp ι.toMonoidHom
    have hrange : β.range = (LeviBlock.spFlagLeviHom (K := K) hI htI).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ι.surjective,
        ← MonoidHom.range_eq_map]
    have hβ : IsPGroup 2 β.ker := by
      rw [← MonoidHom.comap_ker]
      exact (LeviBlock.isPGroup_ker_spFlagLeviHom hI htI fun i hi => by
        rw [Set.mem_singleton_iff] at hi
        omega).comap_of_injective _ ι.injective
    have hρAk : ρA.toMonoidHom.ker ≤ Subgroup.center _ := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr ρA.injective]
      exact bot_le
    refine LeviFive.isFiveComponent_normal_inner hPY ρA.toMonoidHom ρA.surjective hρAk
      (LeviBlock.spFlagLeviBlock (K := K) hI 2) β hβ
      (hrange ▸ LeviBlock.pi_le_range_spFlagLeviHom hI htI fun c hc => by
        rw [Set.mem_singleton_iff] at hc
        omega)
      (hrange ▸ LeviBlock.commutator_range_spFlagLeviHom_le hI htI)
      (LeviBlock.spFlagLeviBlock_cases hI 2)
      (fun j hq h60 q => LeviBlock.spFlagLeviHom_inner_of_sixty hK hI htI j hq h60 (ι q)) hC

end AltTen

open AltTen

theorem kFactFourSixTwo_of (hTF : KFactCompParabTwoFives) : KFactFourSixTwo := by
  intro A _ _ Y P J t hYq hO2 htype hpar h3 hJP hJs hJq hJf htY htP ht2 hne
  classical
  have hPY : P ≤ Y := hpar.1
  have hC₁ : IsFiveComponent P (hatOf P J) := ⟨⟨le_top, hJs, hJq⟩, hJf⟩
  obtain ⟨τ, hτ⟩ := exists_hatOf_map_conj hJP htP
  have hC₂ : IsFiveComponent P (hatOf P (J.map (MulAut.conj t).toMonoidHom)) := by
    rw [hτ]
    exact isFiveComponent_map τ hC₁
  let e₀ : ↥P ≃* ↥(P.subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe hPY).symm
  let ê := QuotientGroup.congr (CFSG.pCore 2 ↥P) (CFSG.pCore 2 ↥(P.subgroupOf Y)) e₀
    (CFSG.pCore_map_iso 2 e₀)
  have h₁ : IsFiveComponent (P.subgroupOf Y) ((hatOf P J).map ê.toMonoidHom) :=
    isFiveComponent_map ê hC₁
  have h₂ : IsFiveComponent (P.subgroupOf Y)
      ((hatOf P (J.map (MulAut.conj t).toMonoidHom)).map ê.toMonoidHom) :=
    isFiveComponent_map ê hC₂
  have hne' : (hatOf P J).map ê.toMonoidHom ≠
      (hatOf P (J.map (MulAut.conj t).toMonoidHom)).map ê.toMonoidHom :=
    fun h => hne (Subgroup.map_injective ê.injective h).symm
  have hCP := compParab_top_subgroupOf hYq hO2 htype hpar h₁ h₂ hne'
  have h3' : Open.pRank 3 (⊤ : Subgroup ↥Y) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y]
    exact h3
  obtain ⟨⟨T, _, e, hT⟩, hinner⟩ :=
    survivor_facts hPY (hTF ↥Y ⊤ (P.subgroupOf Y) hCP h3' _ _ hne' h₁ h₂)
  obtain ⟨y, hyY, hy⟩ := exists_conj_eq_of_sq_inner hYq.1 e hT htY ht2
  have ht2P : t ^ 2 ∈ Subgroup.normalizer (P : Set A) := pow_mem htP 2
  have hyN : y ∈ Subgroup.normalizer (P : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hy x (hPY hx)]
      exact (Subgroup.mem_normalizer_iff.mp ht2P x).mp hx
    · intro hx
      have hxY : x ∈ Y := by
        have h2 := Y.mul_mem (Y.mul_mem (Y.inv_mem hyY) (hPY hx)) hyY
        simpa [mul_assoc] using h2
      rw [← hy x hxY] at hx
      exact (Subgroup.mem_normalizer_iff.mp ht2P x).mpr hx
  have hyP := mem_of_mem_normalizer_of_isParabolicTwo hpar hyY hyN
  obtain ⟨-, hinn⟩ := hinner _ hC₁
  obtain ⟨c, ⟨⟨j₀, hj₀P⟩, hj₀J, rfl⟩, hcu⟩ := hinn (QuotientGroup.mk ⟨y, hyP⟩)
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hj₀J
  have hmemP : ∀ x ∈ P, t ^ 2 * x * (t ^ 2)⁻¹ ∈ P := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp ht2P x).mp hx
  have hmk : ∀ x (hx : x ∈ J), (QuotientGroup.mk (⟨t ^ 2 * x * (t ^ 2)⁻¹,
      hmemP x (hJP hx)⟩ : ↥P) : ↥P ⧸ CFSG.pCore 2 ↥P) =
      QuotientGroup.mk (⟨j₀ * x * j₀⁻¹, P.mul_mem (P.mul_mem hj₀P (hJP hx))
        (P.inv_mem hj₀P)⟩ : ↥P) := by
    intro x hx
    have h1 := hcu (QuotientGroup.mk ⟨x, hJP hx⟩)
      ⟨⟨x, hJP hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] at h1
    have h2 : (⟨t ^ 2 * x * (t ^ 2)⁻¹, hmemP x (hJP hx)⟩ : ↥P) =
        ⟨y, hyP⟩ * ⟨x, hJP hx⟩ * ⟨y, hyP⟩⁻¹ := Subtype.ext (hy x (hPY (hJP hx)))
    rw [h2, h1]
    rfl
  have key : ∀ x ∈ J, t ^ 2 * x * (t ^ 2)⁻¹ * (j₀ * x * j₀⁻¹)⁻¹ ∈ pCoreOf 2 P := by
    intro x hx
    have h1 := hmk x hx
    rw [QuotientGroup.eq_iff_div_mem] at h1
    refine ⟨_, h1, ?_⟩
    simp [div_eq_mul_inv]
  refine ⟨?_, j₀, hj₀J, key⟩
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
    obtain ⟨x, hx, hxa⟩ := ha
    have ha' : a = ⟨t ^ 2 * x * (t ^ 2)⁻¹, hmemP x (hJP hx)⟩ := Subtype.ext hxa.symm
    rw [ha', QuotientGroup.mk'_apply, hmk x hx]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr (J.mul_mem (J.mul_mem hj₀J hx) (J.inv_mem hj₀J)), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ha
    have hxJ : j₀⁻¹ * (a : A) * j₀ ∈ J := J.mul_mem (J.mul_mem (J.inv_mem hj₀J) ha) hj₀J
    refine ⟨⟨t ^ 2 * (j₀⁻¹ * a * j₀) * (t ^ 2)⁻¹, hmemP _ (hJP hxJ)⟩,
      Subgroup.mem_subgroupOf.mpr ⟨_, hxJ, rfl⟩, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hmk _ hxJ]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mk]
    group

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
