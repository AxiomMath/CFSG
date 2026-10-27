module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClFix
import CFSG.GroupTheory.PCore.FixedSubgroupCore
import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import Certificates.Kernel.ThCent.Leaves
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

theorem mem_centralizer_of_chevAut_eq_one {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hcomp : GLAPComponent 3 (⊤ : Subgroup Ω) S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    {t : Ω} (ht : t ∈ Subgroup.normalizer (S : Set Ω)) (h1 : chevAut 3 S ⟨t, ht⟩ = 1) :
    t ∈ Subgroup.centralizer (S : Set Ω) := by
  have hcm := centMod_iff.1 ((chevAut_eq_one_iff Nat.prime_three hcomp ht).1 h1)
  have hO : GLAPPrimeCoreOf 3 S = ⊥ := CFSG.gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.2 hcore
  refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
  have h2 := hcm.2 s hs
  rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

theorem glaPLayer_comap_ne_bot_of_equiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) {X : Subgroup H} (hX : GLAPLayer 3 X ≠ ⊥) :
    GLAPLayer 3 (X.comap e.toMonoidHom) ≠ ⊥ := by
  intro hbot
  have hL := CFSG.glaPLayer_map_eq_of_injective Nat.prime_three e.toMonoidHom e.injective
    (X.comap e.toMonoidHom)
  rw [hbot, Subgroup.map_bot, Subgroup.map_comap_eq_self_of_surjective e.surjective] at hL
  exact hX hL.symm

private theorem conj_mem_commutator {Ω : Type} [Group Ω] {B T : Subgroup Ω}
    (hbn : B ≤ Subgroup.normalizer (T : Set Ω)) {b z : Ω} (hb : b ∈ B)
    (hz : z ∈ (⁅T, B⁆ : Subgroup Ω)) : b * z * b⁻¹ ∈ (⁅T, B⁆ : Subgroup Ω) := by
  have hle : (⁅T, B⁆ : Subgroup Ω) ≤ (⁅T, B⁆ : Subgroup Ω).comap (MulAut.conj b).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun t ht c hc => ?_
    rw [Subgroup.mem_comap]
    have h1 : (MulAut.conj b).toMonoidHom ⁅t, c⁆ =
        ⁅b * t * b⁻¹, b * c * b⁻¹⁆ := map_commutatorElement (MulAut.conj b).toMonoidHom t c
    rw [h1]
    exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 (hbn hb) t).1 ht)
      (B.mul_mem (B.mul_mem hb hc) (B.inv_mem hb))
  exact hle hz

private theorem commutator_le_of_normalizes {Ω : Type} [Group Ω] {B T : Subgroup Ω}
    (hbn : B ≤ Subgroup.normalizer (T : Set Ω)) : (⁅T, B⁆ : Subgroup Ω) ≤ T :=
  Subgroup.commutator_le.2 fun t ht b hb => by
    have h' := (Subgroup.mem_normalizer_iff.1 (hbn hb) t⁻¹).1 (T.inv_mem ht)
    have : ⁅t, b⁆ = t * (b * t⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact T.mul_mem ht h'

theorem qsConcl_of_section {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSCfg 3 S B T x D K)
    (hK : catalogIs (PSimple 3 K) S9.isU5two ∨ catalogIs (PSimple 3 K) S9.isU6two)
    (hB : Nat.card B = 3 ^ 5) (hc : ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω))
    {G : Type} [Group G] {eS : PSimple 3 S →* G} (heS : Function.Injective eS)
    {W : Subgroup Ω} (ρ : W →* G)
    (hρ : ∀ (w : W) (hw : (w : Ω) ∈ Subgroup.normalizer (S : Set Ω)) (z : PSimple 3 S),
      eS (chevAut 3 S ⟨w, hw⟩ z) = ρ w * eS z * (ρ w)⁻¹)
    (hρ1 : ∀ (w : W) (hw : (w : Ω) ∈ Subgroup.normalizer (S : Set Ω)),
      ρ w = 1 ↔ chevAut 3 S ⟨w, hw⟩ = 1)
    (hBW : B ≤ W) (hTBW : (⁅T, B⁆ : Subgroup Ω) ≤ W) (hKW : ∀ y ∈ K, orderOf y = 11 → y ∈ W)
    (hP : ∀ (A T₁ : Subgroup G) (d y : G), IsElemAbelian 3 A → 81 ≤ Nat.card A → d ∈ A →
      d ≠ 1 → y ^ 11 = 1 → y ≠ 1 → d * y = y * d → IsPGroup 2 T₁ → T₁ ≠ ⊥ →
      A ≤ Subgroup.normalizer (T₁ : Set G) →
      ∃ e ∈ A, e * y ≠ y * e ∧ GLAPLayer 3 ((Subgroup.centralizer ({d} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G)).comap eS) ≠ ⊥) :
    QSConcl 3 S B D K := by
  classical
  haveI := Fact.mk Nat.prime_three
  obtain ⟨hDB, -, hD9, -, -, hKc, -⟩ := h.std
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 h.normal) ▸ Subgroup.mem_top g
  let ρB : B →* G := ρ.comp (Subgroup.inclusion hBW)
  let ρT : (⁅T, B⁆ : Subgroup Ω) →* G := ρ.comp (Subgroup.inclusion hTBW)
  have hker : ∀ b : B, ρB b = 1 ↔ (b : Ω) ∈ Subgroup.zpowers x := fun b =>
    (hρ1 ⟨b, hBW b.2⟩ (hSN b)).trans
      ((chevAut_eq_one_iff Nat.prime_three h.comp (hSN b)).trans (h.centB b b.2))
  have hordx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (h.elem.2 x h.xB) h.x1]
  have hA81 : Nat.card ρB.range = 3 ^ 4 := by
    have hk : ρB.ker = (Subgroup.zpowers x).subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hker b
    have hcard := Subgroup.card_ker_mul_card_range ρB
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 h.xB)).toEquiv,
      hordx, hB] at hcard
    omega
  have hAe : IsElemAbelian 3 ρB.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, b₁, rfl⟩ := a
      obtain ⟨_, b₂, rfl⟩ := b
      have hb : b₁ * b₂ = b₂ * b₁ := Subtype.ext (h.elem.comm b₁.2 b₂.2)
      exact Subtype.ext (by
        change ρB b₁ * ρB b₂ = ρB b₂ * ρB b₁
        rw [← map_mul, ← map_mul, hb])
    · rintro _ ⟨b, rfl⟩
      have hb : b ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact h.elem.2 b b.2)
      rw [← map_pow, hb, map_one]
  obtain ⟨d, hdD, hdx⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers x := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from hcon)
    rw [hD9, hordx] at this
    omega
  have hdB : d ∈ B := hDB hdD
  obtain ⟨y, hyK, hy11, hyn⟩ := exists_order_eleven_chevAut_ne_one h hK
  have hyW : y ∈ W := hKW y hyK hy11
  have hy1 : ρ ⟨y, hyW⟩ ≠ 1 := fun h1 => hyn (hSN y) ((hρ1 ⟨y, hyW⟩ (hSN y)).1 h1)
  have hy11' : (ρ ⟨y, hyW⟩) ^ 11 = 1 := by
    have hyp : (⟨y, hyW⟩ : W) ^ 11 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy11]
      exact pow_orderOf_eq_one y)
    rw [← map_pow, hyp, map_one]
  have hycomm : ∀ e ∈ D, ∀ he : e ∈ W, ρ ⟨e, he⟩ * ρ ⟨y, hyW⟩ = ρ ⟨y, hyW⟩ * ρ ⟨e, he⟩ :=
    fun e he heW => by
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (Subtype.ext (Subgroup.mem_centralizer_iff.1 (hKc.1 hyK).2 e he))
  obtain ⟨z, hzTB, hzC⟩ : ∃ z ∈ (⁅T, B⁆ : Subgroup Ω), z ∉ Subgroup.centralizer (S : Set Ω) := by
    by_contra hcon
    push Not at hcon
    exact hc fun z hz => hcon z hz
  have hz1 : ρ ⟨z, hTBW hzTB⟩ ≠ 1 := fun h1 =>
    hzC (mem_centralizer_of_chevAut_eq_one h.comp h.core (hSN z)
      ((hρ1 ⟨z, hTBW hzTB⟩ (hSN z)).1 h1))
  have hcn : ∀ b : B, ∀ u ∈ ρT.range, ρB b * u * (ρB b)⁻¹ ∈ ρT.range := by
    rintro b _ ⟨t, rfl⟩
    refine ⟨⟨(b : Ω) * t * (b : Ω)⁻¹, conj_mem_commutator h.bnorm b.2 t.2⟩, ?_⟩
    change ρ ⟨_, _⟩ = ρ ⟨b, _⟩ * ρ ⟨t, _⟩ * (ρ ⟨b, _⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hAT : ρB.range ≤ Subgroup.normalizer (ρT.range : Set G) := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨hcn b u, fun hu => ?_⟩
    have := hcn b⁻¹ _ hu
    rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
      inv_mul_cancel, mul_one] at this
  have hTp : IsPGroup 2 ρT.range := by
    have hT2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) :=
      h.two.of_injective (Subgroup.inclusion (commutator_le_of_normalizes h.bnorm))
        (Subgroup.inclusion_injective _)
    exact hT2.of_surjective ρT.rangeRestrict ρT.rangeRestrict_surjective
  have hT1 : ρT.range ≠ ⊥ := fun hbot =>
    hz1 (Subgroup.mem_bot.1 (hbot ▸ ⟨⟨z, hzTB⟩, rfl⟩))
  obtain ⟨e', ⟨b, rfl⟩, hecomm, hlay⟩ := hP ρB.range ρT.range (ρ ⟨d, hBW hdB⟩) (ρ ⟨y, hyW⟩)
    hAe (by rw [hA81]; norm_num) ⟨⟨d, hdB⟩, rfl⟩ (fun h1 => hdx ((hker ⟨d, hdB⟩).1 h1))
    hy11' hy1 (hycomm d hdD (hBW hdB)) hTp hT1 hAT
  have hbD : (b : Ω) ∉ D := fun hbD => hecomm (hycomm b hbD (hBW b.2))
  have hfix : ∀ (w : W), fixSubgroup (chevAut 3 S ⟨w, hSN w⟩) =
      (Subgroup.centralizer ({ρ w} : Set G)).comap eS := fun w => by
    ext z'
    rw [mem_fixSubgroup, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h1 := hρ w (hSN w) z'
    constructor
    · intro hz'
      rw [hz'] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1.symm).symm
    · intro hz'
      apply heS
      rw [h1]
      exact mul_inv_eq_iff_eq_mul.2 hz'.symm
  refine qsConcl_of_fix_pair h hdD hdx b.2 hbD (hSN d) (hSN b) fun hbot => hlay ?_
  have hl : fixSubgroup (chevAut 3 S ⟨d, hSN d⟩) ⊓ fixSubgroup (chevAut 3 S ⟨b, hSN b⟩) =
      (Subgroup.centralizer ({ρ ⟨d, hBW hdB⟩} : Set G) ⊓
        Subgroup.centralizer ({ρB b} : Set G)).comap eS := by
    rw [Subgroup.comap_inf]
    exact congrArg₂ (· ⊓ ·) (hfix ⟨d, hBW hdB⟩) (hfix ⟨b, hBW b.2⟩)
  rw [← hl]
  exact hbot

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
