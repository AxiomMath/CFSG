module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem stmtUnitarySocle_of (hKU1 : KFactUnitarySchur) : StmtUnitarySocle := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hcent d hd e
  obtain ⟨e₁⟩ := e
  have hZp : IsPGroup p (Subgroup.center K) := hcfg.isPGroup_center hK
  have hZ : Subgroup.center K = ⊥ := hKU1 K p d hd hK.2.2 hZp ⟨e₁⟩
  have eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  refine ⟨eK.isSimpleGroup, ⟨eK.trans e₁⟩, hcfg.ext, hcfg.glob, d1LiftX_le p H R K,
    K, normal_of_forall_isComponentOf_eq hK huniq, ⟨MulEquiv.refl _⟩,
    hcfg.centralizer_eq_bot hK huniq hcent hZ, map_d1LiftX p H R K⟩

theorem stmtUnitaryBorel_of (hKU2 : KFactUnitarySylowStructure)
    (hKU3 : KFactUnitarySylowCenterTorus) (hKU4 : KFactUnitaryTorusPPD)
    (hKU5 : KFactUnitaryUnipotentCentralizer) (hKU6 : KFactUnitaryBorelMaximal)
    (hKU7 : KFactUnitaryBorelPCore) (hKU8 : KFactUnitarySylowNormalizerSolvable)
    (hKU9 : KFactUnitaryAutElemRank) (_hKU11 : KFactUnitaryOrder) : StmtUnitaryBorel := by
  intro Y _ _ p _ Rb Y₀ K Ub Zb d hd hred hKn hK hC hUbdef hZbdef
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hred.ne_two
  set F := GaloisField p d.1.fieldExponent
  have hn1 : 1 ≤ d.1.fieldExponent := by
    obtain ⟨q, -, hq, hfe, hq1⟩ := hd.exists_eq
    omega
  have hn0 : d.1.fieldExponent ≠ 0 := by omega
  obtain ⟨TK, hTK⟩ := exists_sylow_map_subtype_eq_inf K Rb
  rw [← hUbdef] at hTK
  have hTKmem : ∀ k : K, k ∈ (TK : Subgroup K) ↔ (k : Y) ∈ Ub := fun k => by
    rw [← hTK]
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hUbK : Ub ≤ K := hUbdef ▸ inf_le_right
  have hZK : ∀ k : K, k ∈ (TK : Subgroup K) ⊓ Subgroup.centralizer ((TK : Subgroup K) : Set K) ↔
      (k : Y) ∈ Zb := by
    intro k
    rw [hZbdef]
    constructor
    · rintro ⟨hk1, hk2⟩
      refine ⟨(hTKmem k).mp hk1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have huK : u ∈ K := hUbK hu
      have := Subgroup.mem_centralizer_iff.mp hk2 ⟨u, huK⟩ ((hTKmem ⟨u, huK⟩).mpr hu)
      exact congrArg Subtype.val this
    · rintro ⟨hk1, hk2⟩
      refine ⟨(hTKmem k).mpr hk1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hk2 u ((hTKmem u).mp hu))
  have hZbUb : Zb ≤ Ub := hZbdef ▸ inf_le_left
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]
  have hrank : Open.pRank p (⊤ : Subgroup Y) ≤ 2 * d.1.fieldExponent := by
    apply csSup_le'
    rintro k ⟨E, -, hE, hcard⟩
    have h := hKU9 K p d hd hK (E.map MulAut.conjNormal) (elementary_abelian_map p hE _)
    rw [Subgroup.card_map_of_injective hinj, hcard] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  have hn2 : 2 ≤ d.1.fieldExponent := by
    have h3 := hred.three_le_pRank.trans ((pRank_mono p hp le_top).trans hrank)
    omega
  obtain ⟨hTcard, hTcomm, hTpow, E, hET, hE, hEcard⟩ := hKU2 K p d hp2 hd hK TK
  have hUbcard : Nat.card Ub = p ^ (3 * d.1.fieldExponent) := by
    rw [← hTK, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
  have hUbcomm : ⁅Ub, Ub⁆ = Zb := by
    rw [← hTK, ← Subgroup.map_commutator, hTcomm]
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (hZK k).mp hk
    · intro hy
      exact ⟨⟨y, hUbK (hZbUb hy)⟩, (hZK _).mpr hy, rfl⟩
  have hUbpow : ∀ u ∈ Ub, u ^ p = 1 := by
    intro u hu
    have := hTpow ⟨u, hUbK hu⟩ ((hTKmem _).mpr hu)
    simpa using congrArg Subtype.val this
  have hrankUb : 3 ≤ Open.pRank p Ub := by
    have hE' : IsElemAbelian p (E.map K.subtype) := elementary_abelian_map p hE _
    have hEcard' : Nat.card (E.map K.subtype) = p ^ (2 * d.1.fieldExponent) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]
    have hEU : E.map K.subtype ≤ Ub := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hTKmem x).mp (hET hx)
    exact (show 3 ≤ 2 * d.1.fieldExponent by omega).trans
      (le_csSup (pRank_bddAbove p hp _) ⟨_, hEU, hE', hEcard'⟩)
  have hN : Subgroup.normalizer (Ub : Set Y) ≤ Y₀ :=
    (normalizer_le_weakCore p (hUbdef ▸ inf_le_left) (le_trans (by norm_num) hrankUb)
      (hrankUb.trans (pRank_mono p hp le_sup_left))).trans hred.weakCore_le
  have hKY₀ : ¬ K ≤ Y₀ := not_le_of_weakCore_le hp Rb hred.weakCore_le hred.ne_top
    (hUbdef ▸ hrankUb)
  have hmap : ∀ k ∈ Subgroup.normalizer ((TK : Subgroup K) : Set K),
      (k : Y) ∈ Subgroup.normalizer (Ub : Set Y) := by
    intro k hk
    rw [← hTK]
    exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hk)
  have hY₀K : Y₀ ⊓ K ≤ Subgroup.normalizer (Ub : Set Y) := by
    have hNK : Subgroup.normalizer ((TK : Subgroup K) : Set K) ≤ Y₀.subgroupOf K :=
      fun k hk => Subgroup.mem_subgroupOf.mpr (hN (hmap k hk))
    have heq : Y₀.subgroupOf K = Subgroup.normalizer ((TK : Subgroup K) : Set K) :=
      ((hKU6 K p d hd hK TK).le_iff.mp hNK).resolve_left fun h =>
        hKY₀ (Subgroup.subgroupOf_eq_top.mp h)
    rintro y ⟨hy₀, hyK⟩
    exact hmap ⟨y, hyK⟩ (heq ▸ Subgroup.mem_subgroupOf.mpr hy₀)
  have hUY₀ : Ub ≤ Y₀ := Subgroup.le_normalizer.trans hN
  have hY₀U : Y₀ ≤ Subgroup.normalizer (Ub : Set Y) := by
    have := le_normalizer_sylow_inf K Rb (hUbdef ▸ hUY₀) (hUbdef ▸ hY₀K)
    rwa [← hUbdef] at this
  have hCU : Subgroup.centralizer (Ub : Set Y) ≤ Ub := by
    intro y hy
    set α : MulAut K := MulAut.conjNormal y
    have hfix : ∀ z ∈ (TK : Subgroup K), α z = z := by
      intro z hz
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      exact mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_iff.mp hy _ ((hTKmem z).mp hz)).symm
    obtain ⟨u, hu, hαu⟩ := hKU5 K p d hd hK TK α hfix
    have hcent : (u : Y)⁻¹ * y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := congrArg Subtype.val (DFunLike.congr_fun hαu ⟨k, hk⟩)
      simp only [α, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      calc k * ((u : Y)⁻¹ * y) = (u : Y)⁻¹ * ((u : Y) * k * (u : Y)⁻¹) * y := by group
        _ = (u : Y)⁻¹ * (y * k * y⁻¹) * y := by rw [← h]
        _ = (u : Y)⁻¹ * y * k := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    exact hcent ▸ (hTKmem u).mp hu
  obtain ⟨ψK, hψKinj, hψKZ, hcK⟩ := hKU3 K p d hd hK TK
  set ψ : Multiplicative F →* Y := K.subtype.comp ψK
  have hψ : Function.Injective ψ := K.subtype_injective.comp hψKinj
  have hψZ : ψ.range = Zb := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (hZK (ψK a)).mp (hψKZ ▸ ⟨a, rfl⟩)
    · intro hy
      have hyK : y ∈ K := hUbK (hZbUb hy)
      obtain ⟨a, ha⟩ := (show (⟨y, hyK⟩ : K) ∈ ψK.range from hψKZ ▸ (hZK ⟨y, hyK⟩).mpr hy)
      exact ⟨a, by simp [ψ, ha]⟩
  have hcY₀ : ∀ μ : Fˣ, ∃ c ∈ Y₀, ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcN, hc⟩ := hcK μ
    refine ⟨c, hN (hmap c hcN), fun a => ?_⟩
    have h := congrArg Subtype.val (hc a)
    simpa [ψ] using h
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  refine ⟨hn2, hUbcard, hUbcomm, hUbpow, ?_, ?_, hCU, ⟨ψ, hψ, hψZ, hcY₀⟩, ?_, ?_, hrank⟩
  ·
    intro W hWY₀ hY₀W
    rcases (W ⊓ Ub).bot_or_nontrivial with hWU | hWU
    · left
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ Subgroup.centralizer (Ub : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hcW : w * z * w⁻¹ * z⁻¹ ∈ W := by
          have h := (Subgroup.mem_normalizer_iff.mp (hY₀W (hUY₀ hz)) w⁻¹).mp (W.inv_mem hw)
          simpa only [mul_assoc] using W.mul_mem hw h
        have hcomm : w * z * w⁻¹ * z⁻¹ ∈ W ⊓ Ub := ⟨hcW,
          Ub.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY₀U (hWY₀ hw)) z).mp hz)
            (Ub.inv_mem hz)⟩
        rw [hWU, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hcomm
        exact hcomm.symm
      have hwWU : w ∈ W ⊓ Ub := ⟨hw, hCU hwC⟩
      rwa [hWU] at hwWU
    · right
      have hUbp : IsPGroup p Ub := hUbdef ▸ Rb.isPGroup'.to_inf_left
      have : Group.IsNilpotent Ub := hUbp.isNilpotent
      have hNn : ((W ⊓ Ub).subgroupOf Ub).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr ?_
        exact (le_inf (hUY₀.trans hY₀W) Subgroup.le_normalizer).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      have hne : (W ⊓ Ub).subgroupOf Ub ≠ ⊥ := by
        intro hbot
        obtain ⟨x, hx, hx1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp hWU
        have : (⟨x, hx.2⟩ : Ub) ∈ (W ⊓ Ub).subgroupOf Ub := Subgroup.mem_subgroupOf.mpr hx
        rw [hbot, Subgroup.mem_bot] at this
        exact hx1 (congrArg Subtype.val this)
      obtain ⟨⟨g, hgW, hgZ⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
      have hg1' : (g : Y) ≠ 1 := fun h => hg1 (Subtype.ext (Subtype.ext h))
      have hgZ' : (g : Y) ∈ Zb := by
        rw [hZbdef]
        exact ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun u hu =>
          (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hgZ) ⟨u, hu⟩))⟩
      obtain ⟨a, ha⟩ : (g : Y) ∈ ψ.range := hψZ ▸ hgZ'
      rw [← hψZ]
      refine range_le_of_torus h2 ψ (fun μ => ?_) (ha ▸ (Subgroup.mem_subgroupOf.mp hgW).1)
        (by rw [ha]; exact hg1')
      obtain ⟨c, hcY, hc⟩ := hcY₀ (μ ^ 2)
      exact ⟨c, hY₀W hcY, fun a' => by rw [hc a', Units.val_pow_eq_pow_val]⟩
  ·
    intro W hWY₀ hY₀W hWp
    set A := W.map (MulAut.conjNormal (H := K) : Y →* MulAut K)
    have hAp : IsPGroup p A := hWp.map _
    have hAn : ∀ b ∈ Subgroup.normalizer ((TK : Subgroup K) : Set K), ∀ α ∈ A,
        MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ A := by
      rintro b hb _ ⟨w, hw, rfl⟩
      have hbY₀ : (b : Y) ∈ Y₀ := hN (hmap b hb)
      refine ⟨(b : Y) * w * (b : Y)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hY₀W hbY₀) w).mp hw, ?_⟩
      ext k
      simp [MulAut.conjNormal_apply, MulAut.conj_apply, mul_assoc]
    intro w hw
    obtain ⟨u, hu, hαu⟩ := hKU7 K p d hd hK TK A hAp hAn _ ⟨w, hw, rfl⟩
    have hcent : (u : Y)⁻¹ * w ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h := congrArg Subtype.val (DFunLike.congr_fun hαu ⟨k, hk⟩)
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h
      calc k * ((u : Y)⁻¹ * w) = (u : Y)⁻¹ * ((u : Y) * k * (u : Y)⁻¹) * w := by group
        _ = (u : Y)⁻¹ * (w * k * w⁻¹) * w := by rw [← h]
        _ = (u : Y)⁻¹ * w * k := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    exact hcent ▸ (hTKmem u).mp hu
  ·
    intro r hr hrdvd hprim
    obtain ⟨c, hcN, hcord, hcirr⟩ := hKU4 K p d hd hn2 hK TK r hr hrdvd hprim
    refine ⟨c, hN (hmap c hcN), hmap c hcN, by rw [Subgroup.orderOf_coe, hcord],
      fun k hk => ⟨?_, fun V hZV hVU hcV => ?_⟩⟩
    · obtain ⟨⟨u, hu, hcu⟩, -⟩ := hcirr k hk
      refine ⟨u, (hTKmem u).mp hu, fun hmem => hcu ((hZK _).mpr ?_)⟩
      simpa using hmem
    · obtain ⟨-, hV⟩ := hcirr k hk
      have hVK : V ≤ K := hVU.trans hUbK
      have hZV' : (TK : Subgroup K) ⊓ Subgroup.centralizer ((TK : Subgroup K) : Set K) ≤
          V.subgroupOf K := fun z hz => Subgroup.mem_subgroupOf.mpr (hZV ((hZK z).mp hz))
      have hVT : V.subgroupOf K ≤ TK := fun z hz =>
        (hTKmem z).mpr (hVU (Subgroup.mem_subgroupOf.mp hz))
      have hcV' : c ^ k ∈ Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K) := by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        have := Subgroup.mem_normalizer_iff.mp hcV (z : Y)
        simpa using this
      rcases hV _ hZV' hVT hcV' with heq | heq
      · left
        apply le_antisymm
        · intro v hv
          have := (show (⟨v, hVK hv⟩ : K) ∈ V.subgroupOf K from Subgroup.mem_subgroupOf.mpr hv)
          rw [heq] at this
          exact (hZK _).mp this
        · exact hZV
      · right
        apply le_antisymm hVU
        intro u hu
        have := (hTKmem ⟨u, hUbK hu⟩).mpr hu
        rw [← heq] at this
        exact Subgroup.mem_subgroupOf.mp this
  ·
    have hA : ∀ α ∈ Y₀.map (MulAut.conjNormal (H := K) : Y →* MulAut K),
        (TK : Subgroup K).map (α : K ≃* K).toMonoidHom = TK := by
      rintro _ ⟨y, hy, rfl⟩
      refine Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) (by
        rw [Subgroup.card_map_of_injective
          (f := ((MulAut.conjNormal y : K ≃* K)).toMonoidHom) (MulAut.conjNormal y).injective])
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
      rw [hTKmem] at hx ⊢
      change ((MulAut.conjNormal y x : K) : Y) ∈ Ub
      rw [MulAut.conjNormal_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hY₀U hy) _).mp hx
    have := hKU8 K p d hd hK TK _ hA
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Y₀.equivMapOfInjective _ hinj).toMonoidHom) (Y₀.equivMapOfInjective _ hinj).injective

end CFSG.AGLEmbedding
