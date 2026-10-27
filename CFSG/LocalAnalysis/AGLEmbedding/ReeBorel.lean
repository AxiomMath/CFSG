module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorel
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem stmtReeBorel_of (hKR2 : KFactReeSylowCenterTorus) (hKR3 : KFactReeCenterCentralizer)
    (hKR4 : KFactReeBorelMaximal) (hKR5 : KFactReeSylowNormalizerSolvable)
    (hKR6 : KFactReeAutElemRank) : StmtReeBorel := by
  intro Y _ _ Rb Y₀ K d hd hred hKn hK hC
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hn3 : 3 ≤ d.1.fieldExponent := hd.three_le_fieldExponent
  have hn0 : d.1.fieldExponent ≠ 0 := by omega
  set F := GaloisField 3 d.1.fieldExponent
  set Ub : Subgroup Y := (Rb : Subgroup Y) ⊓ K with hUbdef
  set Z : Subgroup Y := Ub ⊓ Subgroup.centralizer (Ub : Set Y) with hZdef
  obtain ⟨TK, hTK⟩ := exists_sylow_map_subtype_eq_inf K Rb
  rw [← hUbdef] at hTK
  have hTKmem : ∀ k : K, k ∈ (TK : Subgroup K) ↔ (k : Y) ∈ Ub := fun k => by
    rw [← hTK]
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hZK : ∀ k : K, k ∈ (TK : Subgroup K) ⊓ Subgroup.centralizer ((TK : Subgroup K) : Set K) ↔
      (k : Y) ∈ Z := by
    intro k
    constructor
    · rintro ⟨hk1, hk2⟩
      refine ⟨(hTKmem k).mp hk1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      have huK : u ∈ K := hu.2
      have := Subgroup.mem_centralizer_iff.mp hk2 ⟨u, huK⟩ ((hTKmem ⟨u, huK⟩).mpr hu)
      exact congrArg Subtype.val this
    · rintro ⟨hk1, hk2⟩
      refine ⟨(hTKmem k).mpr hk1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hk2 u ((hTKmem u).mp hu))
  obtain ⟨ψK, hψKinj, hψKZ, hcK⟩ := hKR2 K d hd hK TK
  set ψ : Multiplicative F →* Y := K.subtype.comp ψK
  have hψ : Function.Injective ψ := K.subtype_injective.comp hψKinj
  have hψZ : ψ.range = Z := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (hZK (ψK a)).mp (hψKZ ▸ ⟨a, rfl⟩)
    · intro hy
      have hyK : y ∈ K := hy.1.2
      obtain ⟨a, ha⟩ := (show (⟨y, hyK⟩ : K) ∈ ψK.range from hψKZ ▸ (hZK ⟨y, hyK⟩).mpr hy)
      exact ⟨a, by simp [ψ, ha]⟩
  obtain ⟨hZel, hZcard⟩ := isElemAbelian_range_galoisField hn0 ψ hψ
  rw [hψZ] at hZel hZcard
  have hZp : IsPGroup 3 Z := Rb.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hrank : 3 ≤ Open.pRank 3 Ub :=
    hn3.trans (le_csSup (pRank_bddAbove 3 hp _) ⟨Z, inf_le_left, hZel, hZcard⟩)
  have hN : Subgroup.normalizer (Ub : Set Y) ≤ Y₀ :=
    (normalizer_le_weakCore 3 inf_le_left (le_trans (by norm_num) hrank)
      (hrank.trans (pRank_mono 3 hp le_sup_left))).trans hred.weakCore_le
  have hKY₀ : ¬ K ≤ Y₀ := not_le_of_weakCore_le hp Rb hred.weakCore_le hred.ne_top hrank
  have hmap : ∀ k ∈ Subgroup.normalizer ((TK : Subgroup K) : Set K),
      (k : Y) ∈ Subgroup.normalizer (Ub : Set Y) := by
    intro k hk
    rw [← hTK]
    exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hk)
  have hY₀K : Y₀ ⊓ K ≤ Subgroup.normalizer (Ub : Set Y) := by
    have hNK : Subgroup.normalizer ((TK : Subgroup K) : Set K) ≤ Y₀.subgroupOf K :=
      fun k hk => Subgroup.mem_subgroupOf.mpr (hN (hmap k hk))
    have heq : Y₀.subgroupOf K = Subgroup.normalizer ((TK : Subgroup K) : Set K) :=
      ((hKR4 K d hd hK TK).le_iff.mp hNK).resolve_left fun h =>
        hKY₀ (Subgroup.subgroupOf_eq_top.mp h)
    rintro y ⟨hy₀, hyK⟩
    exact hmap ⟨y, hyK⟩ (heq ▸ Subgroup.mem_subgroupOf.mpr hy₀)
  have hUY₀ : Ub ≤ Y₀ := Subgroup.le_normalizer.trans hN
  have hY₀U : Y₀ ≤ Subgroup.normalizer (Ub : Set Y) := le_normalizer_sylow_inf K Rb hUY₀ hY₀K
  have hCZ : Subgroup.centralizer (Z : Set Y) ≤ Ub := by
    intro y hy
    set α : MulAut K := MulAut.conjNormal y
    have hfix : ∀ z ∈ (TK : Subgroup K) ⊓ Subgroup.centralizer ((TK : Subgroup K) : Set K),
        α z = z := by
      intro z hz
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      exact mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_iff.mp hy _ ((hZK z).mp hz)).symm
    obtain ⟨u, hu, hαu⟩ := hKR3 K d hd hK TK α hfix
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
  have hcY₀ : ∀ μ : Fˣ, ∃ c ∈ Y₀, ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcN, hc⟩ := hcK (μ ^ 2)
    refine ⟨c, hN (hmap c hcN), fun a => ?_⟩
    have h := congrArg Subtype.val (hc a)
    simpa [ψ] using h
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F 3]; norm_num)
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]
  refine ⟨?_, inf_le_right.trans hCZ, ⟨ψ, hψ, hψZ, hcY₀⟩, ?_, ?_⟩
  ·
    intro W hWY₀ hY₀W
    rcases (W ⊓ Ub).bot_or_nontrivial with hWU | hWU
    · left
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ Subgroup.centralizer (Z : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hcW : w * z * w⁻¹ * z⁻¹ ∈ W := by
          have h := (Subgroup.mem_normalizer_iff.mp (hY₀W (hUY₀ hz.1)) w⁻¹).mp (W.inv_mem hw)
          simpa only [mul_assoc] using W.mul_mem hw h
        have hcomm : w * z * w⁻¹ * z⁻¹ ∈ W ⊓ Ub := ⟨hcW,
          Ub.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY₀U (hWY₀ hw)) z).mp hz.1)
            (Ub.inv_mem hz.1)⟩
        rw [hWU, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hcomm
        exact hcomm.symm
      have hwWU : w ∈ W ⊓ Ub := ⟨hw, hCZ hwC⟩
      rwa [hWU] at hwWU
    · right
      have : Fact (Nat.Prime 3) := ⟨hp⟩
      have hUbp : IsPGroup 3 Ub := Rb.isPGroup'.to_inf_left
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
      have hgZ' : (g : Y) ∈ Z := ⟨g.2, Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hgZ) ⟨u, hu⟩))⟩
      obtain ⟨a, ha⟩ : (g : Y) ∈ ψ.range := hψZ ▸ hgZ'
      rw [← hψZ]
      refine range_le_of_torus h2 ψ (fun μ => ?_) (ha ▸ (Subgroup.mem_subgroupOf.mp hgW).1)
        (by rw [ha]; exact hg1')
      obtain ⟨c, hcY, hc⟩ := hcY₀ μ
      exact ⟨c, hY₀W hcY, hc⟩
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
    have := hKR5 K d hd hK TK _ hA
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Y₀.equivMapOfInjective _ hinj).toMonoidHom) (Y₀.equivMapOfInjective _ hinj).injective
  ·
    apply csSup_le'
    rintro k ⟨E, -, hE, hcard⟩
    have h := hKR6 K d hd hK (E.map MulAut.conjNormal) (elementary_abelian_map 3 hE _)
    rw [Subgroup.card_map_of_injective hinj, hcard] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h

end CFSG.AGLEmbedding
