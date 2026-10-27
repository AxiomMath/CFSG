module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductN2Char
public import CFSG.LocalAnalysis.EvenBN.Common.ProductSplit
public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModuleBridge
public import CFSG.LocalAnalysis.EvenBN.Common.TwoElementary
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Sylow

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (Sl2Pair sylow_prod mem_conj_iff conj_inf conj_sup conj_commutator conj_conj_of_mul_self
    conj_eq_of_mem_normalizer mem_normalizer_of_conj_eq le_normalizer_of_commutator_mem card_conj)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.SL2Aux
  (le_normalizer_inf mem_normalizer_sup)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductN3Aux

variable {G : Type} [Group G] [Finite G]

structure Cfg (K : Type) [Field K] (f : ℕ) (t s : G) (M Λ N A P Y U : Subgroup G) : Prop where
  ht : t * t = 1
  hs2 : s * s = 1
  hst : s * t = t * s
  hK : Nat.card K = 2 ^ f
  hf : 2 ≤ f
  hMΛ : M ≤ Λ
  hΛN : Λ ≤ N
  hNM : N ≤ normalizer (M : Set G)
  hsup : Λ ⊔ Λᵍ[t] = N
  hinf : Λ ⊓ Λᵍ[t] = M
  hcomm : ⁅Λ, Λᵍ[t]⁆ ≤ M
  hquot : IsQuotientIso Λ M (SL(2, K))
  hAN : A ≤ N
  hAM : A ⊓ M = ⊥
  hNA : N = A ⊔ M
  hAt : Aᵍ[t] = A
  hMt : Mᵍ[t] = M
  hsA : s ∈ A
  hPN : IsSylowOf 2 P N
  hMP : M ≤ P
  hPt : Pᵍ[t] = P
  hPPs : P ⊓ P.map (MulAut.conj s).toMonoidHom = M
  hNPs : N = P ⊔ P.map (MulAut.conj s).toMonoidHom
  hYM : Y ≤ M
  hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a
  hYsq : ∀ y ∈ Y, y * y = 1
  hMY : ∀ m ∈ M, ∀ y ∈ Y, m * y = y * m
  hNY : N ≤ normalizer (Y : Set G)
  hYt : Yᵍ[t] = Y
  hUY : U ≤ Y
  hUt : Uᵍ[t] = U
  hZP : P ⊓ centralizer (P : Set G) = U
  hUs : U ⊓ U.map (MulAut.conj s).toMonoidHom = ⊥
  hYU : Y = U ⊔ U.map (MulAut.conj s).toMonoidHom
  hfaith : P ⊓ centralizer (Y : Set G) = M
  hZN : N ⊓ centralizer (N : Set G) = ⊥
  hcY : Nat.card Y = Nat.card K ^ 4
  hcU : Nat.card U = Nat.card K ^ 2

namespace Cfg

variable {K : Type} [Field K] {f : ℕ} {t s : G} {M Λ N A P Y U : Subgroup G}
  (c : Cfg K f t s M Λ N A P Y U)

include c

theorem comm_mem' {y x : G} (hy : y ∈ Λᵍ[t]) (hx : x ∈ Λ) : y * x * y⁻¹ * x⁻¹ ∈ M := by
  have h := Subgroup.commutator_mem_commutator hy hx
  rw [commutator_comm] at h
  have h2 := c.hcomm h
  rwa [commutatorElement_def] at h2

theorem comm_mem {x y : G} (hx : x ∈ Λ) (hy : y ∈ Λᵍ[t]) : x * y * x⁻¹ * y⁻¹ ∈ M := by
  have h := Subgroup.commutator_mem_commutator hx hy
  have h2 := c.hcomm h
  rwa [commutatorElement_def] at h2

theorem le_normalizer_left : N ≤ normalizer (Λ : Set G) := by
  rw [← c.hsup]
  refine sup_le le_normalizer ?_
  exact le_normalizer_of_commutator_mem fun y hy x hx => c.hMΛ (c.comm_mem' hy hx)

theorem le_normalizer_right : N ≤ normalizer ((Λᵍ[t] : Subgroup G) : Set G) := by
  rw [← c.hsup]
  refine sup_le ?_ le_normalizer
  refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
  have h := c.comm_mem hx hy
  have hM : M ≤ Λᵍ[t] := by
    rw [← c.hMt]
    exact Subgroup.map_mono c.hMΛ
  exact hM h

theorem A_le_normalizer_M : A ≤ normalizer (M : Set G) := c.hAN.trans c.hNM

theorem M_le_conj : M ≤ Λᵍ[t] := by
  rw [← c.hMt]
  exact Subgroup.map_mono c.hMΛ

theorem decomp_left {l : G} (hl : l ∈ Λ) : ∃ x ∈ Λ ⊓ A, ∃ m ∈ M, l = x * m := by
  have hl' : l ∈ A ⊔ M := c.hNA ▸ c.hΛN hl
  obtain ⟨a, ha, m, hm, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    c.A_le_normalizer_M l hl'
  refine ⟨a, ⟨?_, ha⟩, m, hm, rfl⟩
  have := mul_mem hl (inv_mem (c.hMΛ hm))
  rwa [mul_inv_cancel_right] at this

theorem decomp_right {l : G} (hl : l ∈ Λᵍ[t]) : ∃ x ∈ Λᵍ[t] ⊓ A, ∃ m ∈ M, l = x * m := by
  have hl' : l ∈ A ⊔ M := c.hNA ▸ (c.hsup ▸ (Subgroup.mem_sup_right hl : l ∈ Λ ⊔ Λᵍ[t]))
  obtain ⟨a, ha, m, hm, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    c.A_le_normalizer_M l hl'
  refine ⟨a, ⟨?_, ha⟩, m, hm, rfl⟩
  have := mul_mem hl (inv_mem (c.M_le_conj hm))
  rwa [mul_inv_cancel_right] at this

theorem comm_X {x y : G} (hx : x ∈ Λ ⊓ A) (hy : y ∈ Λᵍ[t] ⊓ A) : x * y = y * x := by
  have h1 := c.comm_mem hx.1 hy.1
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ A := mul_mem (mul_mem (mul_mem hx.2 hy.2) (inv_mem hx.2))
    (inv_mem hy.2)
  have h3 : x * y * x⁻¹ * y⁻¹ ∈ A ⊓ M := ⟨h2, h1⟩
  rw [c.hAM, Subgroup.mem_bot] at h3
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem inf_X : (Λ ⊓ A) ⊓ (Λᵍ[t] ⊓ A) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : z ∈ Λ ⊓ Λᵍ[t] := ⟨hz.1.1, hz.2.1⟩
  rw [c.hinf] at h1
  have h2 : z ∈ A ⊓ M := ⟨hz.1.2, h1⟩
  rwa [c.hAM] at h2

theorem A_eq_mul {a : G} (ha : a ∈ A) : ∃ x ∈ Λ ⊓ A, ∃ y ∈ Λᵍ[t] ⊓ A, a = x * y := by
  have hΛ' : Λ ≤ normalizer ((Λᵍ[t] : Subgroup G) : Set G) := c.hΛN.trans c.le_normalizer_right
  have ha' : a ∈ Λ ⊔ Λᵍ[t] := c.hsup ▸ c.hAN ha
  obtain ⟨l, hl, l', hl', rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    hΛ' a ha'
  obtain ⟨x, hx, m, hm, rfl⟩ := c.decomp_left hl
  obtain ⟨y, hy, m', hm', rfl⟩ := c.decomp_right hl'
  refine ⟨x, hx, y, hy, ?_⟩
  have hm'' : y⁻¹ * m * y * m' ∈ M := by
    refine mul_mem ?_ hm'
    have := (mem_normalizer_iff.1 (c.A_le_normalizer_M (inv_mem hy.2)) m).1 hm
    simpa [mul_assoc] using this
  have e : (x * y)⁻¹ * (x * m * (y * m')) = y⁻¹ * m * y * m' := by group
  have h1 : y⁻¹ * m * y * m' ∈ A ⊓ M := by
    refine ⟨?_, hm''⟩
    rw [← e]
    have hxy : x * y ∈ A := mul_mem hx.2 hy.2
    have hinv : (x * y)⁻¹ ∈ A := inv_mem hxy
    exact mul_mem hinv ha
  rw [c.hAM, Subgroup.mem_bot] at h1
  calc x * m * (y * m') = (x * y) * (y⁻¹ * m * y * m') := by group
    _ = x * y := by rw [h1, mul_one]

theorem conj_X : (Λ ⊓ A)ᵍ[t] = Λᵍ[t] ⊓ A := by
  rw [conj_inf, c.hAt]

end Cfg

theorem nonempty_mulEquiv_of_quotient {Λ M A : Subgroup G} {T : Type*} [Group T]
    (hMΛ : M ≤ Λ) (hdec : ∀ l ∈ Λ, ∃ x ∈ Λ ⊓ A, ∃ m ∈ M, l = x * m) (hAM : A ⊓ M = ⊥)
    (h : IsQuotientIso Λ M T) : Nonempty (↥(Λ ⊓ A) ≃* T) := by
  obtain ⟨φ, hφ, hker⟩ := h
  let ι : ↥(Λ ⊓ A) →* ↥Λ := Subgroup.inclusion inf_le_left
  have hinj : Function.Injective (φ.comp ι) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ι x ∈ φ.ker := hx
    rw [hker, Subgroup.mem_subgroupOf] at h1
    have h2 : (x : G) ∈ A ⊓ M := ⟨x.2.2, h1⟩
    rw [hAM, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective (φ.comp ι) := by
    intro g
    obtain ⟨l, rfl⟩ := hφ g
    obtain ⟨x, hx, m, hm, hlm⟩ := hdec l l.2
    refine ⟨⟨x, hx⟩, ?_⟩
    have hm' : (⟨m, hMΛ hm⟩ : ↥Λ) ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact hm
    have : l = ι ⟨x, hx⟩ * ⟨m, hMΛ hm⟩ := Subtype.ext hlm
    rw [MonoidHom.comp_apply, this, map_mul, MonoidHom.mem_ker.1 hm', mul_one]
  exact ⟨MulEquiv.ofBijective (φ.comp ι) ⟨hinj, hsurj⟩⟩

namespace Cfg

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {t s : G}
  {M Λ N A P Y U : Subgroup G} (c : Cfg K f t s M Λ N A P Y U)

include c

theorem four_le : 4 ≤ Nat.card K := by
  rw [c.hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) c.hf

theorem sl2Pair : Sl2Pair K N M Λ Λᵍ[t] where
  charTwo := inferInstance
  four_le := c.four_le
  sup_eq := c.hsup
  inf_eq := c.hinf
  comm_le := c.hcomm
  isoK := c.hquot
  isoK' := by
    have := CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.IsQuotientIso.conj
      c.hquot t
    rwa [c.hMt] at this

theorem inf_left_eq : P ⊓ Λ = (P ⊓ (Λ ⊓ A)) ⊔ M := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_left P inf_le_left) (le_inf c.hMP c.hMΛ))
  intro p hp
  obtain ⟨x, hx, m, hm, rfl⟩ := c.decomp_left hp.2
  have hxP : x ∈ P := by
    have h1 : x * m ∈ P := hp.1
    have h2 : m⁻¹ ∈ P := inv_mem (c.hMP hm)
    have := mul_mem h1 h2
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨hxP, hx⟩) (Subgroup.mem_sup_right hm)

theorem inf_right_eq : P ⊓ Λᵍ[t] = (P ⊓ (Λᵍ[t] ⊓ A)) ⊔ M := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_left P inf_le_left) (le_inf c.hMP c.M_le_conj))
  intro p hp
  obtain ⟨x, hx, m, hm, rfl⟩ := c.decomp_right hp.2
  have hxP : x ∈ P := by
    have h1 : x * m ∈ P := hp.1
    have h2 : m⁻¹ ∈ P := inv_mem (c.hMP hm)
    have := mul_mem h1 h2
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨hxP, hx⟩) (Subgroup.mem_sup_right hm)

theorem card_T : Nat.card (P ⊓ (Λ ⊓ A) : Subgroup G) = Nat.card K := by
  have h1 := c.sl2Pair.relIndex_sylow c.hPN c.hMP
  have h2 := Subgroup.relIndex_mul_card M (P ⊓ Λ)
  rw [inf_eq_left.2 (le_inf c.hMP c.hMΛ), h1] at h2
  have hTN : (P ⊓ (Λ ⊓ A) : Subgroup G) ≤ normalizer (M : Set G) :=
    inf_le_right.trans (inf_le_right.trans c.A_le_normalizer_M)
  have h3 := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq hTN
  have h4 : M ⊓ (P ⊓ (Λ ⊓ A) : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ A ⊓ M := ⟨hx.2.2.2, hx.1⟩
    rwa [c.hAM] at this
  rw [h4, Subgroup.card_bot, mul_one, sup_comm, ← c.inf_left_eq] at h3
  rw [h3] at h2
  have hM : 0 < Nat.card M := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hM (h2.symm.trans (mul_comm _ _))

theorem P_le : P ≤ M ⊔ (P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)) := by
  have h := (sylow_prod c.hPN c.hsup c.hinf c.hcomm c.hMP).2.2.1
  have hT : (P ⊓ (Λ ⊓ A) : Subgroup G) ≤ M ⊔ (P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)) :=
    le_sup_right.trans le_sup_left
  have hT' : (P ⊓ (Λᵍ[t] ⊓ A) : Subgroup G) ≤ M ⊔ (P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)) :=
    le_sup_right
  have hM : M ≤ M ⊔ (P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)) := le_sup_left.trans le_sup_left
  refine h.le.trans ?_
  rw [c.inf_left_eq, c.inf_right_eq]
  exact sup_le (sup_le hT hM) (sup_le hT' hM)

theorem conj_mem_centralizer {g z : G} (hg : g ∈ normalizer (Y : Set G))
    (hz : z ∈ centralizer (Y : Set G)) : g * z * g⁻¹ ∈ centralizer (Y : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : g⁻¹ * y * g ∈ Y := by
    have := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    simpa using this
  have := mem_centralizer_iff.1 hz _ hy'
  calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = g * z * g⁻¹ * y := by group

theorem faith_X : (Λ ⊓ A) ⊓ centralizer (Y : Set G) = ⊥ := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_of_quotient c.hMΛ (fun l hl => c.decomp_left hl) c.hAM c.hquot
  haveI : IsSimpleGroup SL(2, K) :=
    CFSG.LocalAnalysis.EvenBN.Common.sl2_isSimpleGroup_of_charTwo c.four_le
  haveI : IsSimpleGroup ↥(Λ ⊓ A) := ψ.isSimpleGroup
  have hXY : (Λ ⊓ A) ≤ normalizer (Y : Set G) := inf_le_right.trans (c.hAN.trans c.hNY)
  have hnorm : ((Λ ⊓ A ⊓ centralizer (Y : Set G)).subgroupOf (Λ ⊓ A)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro x hx
    rw [mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, c.conj_mem_centralizer (hXY hx) hz2⟩
      exact (mem_normalizer_iff.1 (le_normalizer hx) z).1 hz1
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.1 (le_normalizer hx) z).2 hz1
      · have := c.conj_mem_centralizer (inv_mem (hXY hx)) hz2
        simpa [mul_assoc] using this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((Λ ⊓ A ⊓ centralizer (Y : Set G)).subgroupOf (Λ ⊓ A)) with h | h
  · rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hz.1⟩ : ↥(Λ ⊓ A)) ∈ (Λ ⊓ A ⊓ centralizer (Y : Set G)).subgroupOf (Λ ⊓ A) := hz
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · exfalso
    have hT : P ⊓ (Λ ⊓ A) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz1 : (⟨z, hz.2⟩ : ↥(Λ ⊓ A)) ∈
          (Λ ⊓ A ⊓ centralizer (Y : Set G)).subgroupOf (Λ ⊓ A) := by rw [h]; trivial
      have hzC : z ∈ centralizer (Y : Set G) := (Subgroup.mem_subgroupOf.1 hz1).2
      have hzM : z ∈ P ⊓ centralizer (Y : Set G) := ⟨hz.1, hzC⟩
      rw [c.hfaith] at hzM
      have : z ∈ A ⊓ M := ⟨hz.2.2, hzM⟩
      rwa [c.hAM] at this
    have h1 := c.card_T
    rw [hT, Subgroup.card_bot] at h1
    have h4 := c.four_le
    omega

end Cfg

theorem subgroupOf_map_aut {N : Subgroup G} (H : Subgroup G) (e : MulAut ↥N) (g : G)
    (hg : ∀ x : ↥N, ((e x : ↥N) : G) = g * (x : G) * g⁻¹) :
    (H.subgroupOf N).map e.toMonoidHom = (H.map (MulAut.conj g).toMonoidHom).subgroupOf N := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (hg a).symm⟩
  · rintro ⟨h, hh, hx⟩
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    have h1 := hg (e.symm x)
    rw [e.apply_symm_apply] at h1
    have h2 : g * ((e.symm x : ↥N) : G) * g⁻¹ = g * h * g⁻¹ := by rw [← h1]; exact hx.symm
    have h3 : ((e.symm x : ↥N) : G) = h := by
      have := mul_right_cancel h2
      exact mul_left_cancel this
    rw [h3]
    exact hh

theorem split_ambient {N X Λ V F : Subgroup G} {t r : G} {q : ℕ} (hq : 2 ≤ q)
    (ht : t * t = 1) (htN : t ∈ normalizer (N : Set G)) (hr : r ∈ N)
    (hXN : X ≤ N) (hΛN : Λ ≤ N) (hVΛ : V ≤ Λ) (hXV : X ≤ V) (hFX : F ≤ X)
    (hNX : N ≤ normalizer (X : Set G)) (hNΛ : N ≤ normalizer (Λ : Set G))
    (hσX : Xᵍ[t] = X) (hcen : X ⊓ centralizer (N : Set G) = ⊥)
    (hΛσ : Λ ⊔ Λᵍ[t] = N) (hV2 : IsPGroup 2 V)
    (hgen : Λ ≤ V ⊔ V.map (MulAut.conj r).toMonoidHom)
    (hVn : V ≤ normalizer (((Vᵍ[t]).map (MulAut.conj r).toMonoidHom : Subgroup G) : Set G))
    (hFV : F ≤ centralizer (V : Set G)) (hσF : Fᵍ[t] = F)
    (hFr : F ⊓ F.map (MulAut.conj r).toMonoidHom = ⊥)
    (hFS : ∀ B : Subgroup G, B ≤ X → N ≤ normalizer (B : Set G) →
      ¬ Λᵍ[t] ≤ centralizer (B : Set G) → q ^ 2 ≤ Nat.card B)
    (hcX : Nat.card X = q ^ 4) (hcF : q ^ 2 ≤ Nat.card F) :
    (X ⊓ centralizer (Λ : Set G)) ⊔ (X ⊓ centralizer (Λ : Set G))ᵍ[t] = X ∧
      (X ⊓ centralizer (Λ : Set G)) ⊓ (X ⊓ centralizer (Λ : Set G))ᵍ[t] = ⊥ ∧
      Nat.card (X ⊓ centralizer (Λ : Set G) : Subgroup G) = q ^ 2 := by
  have htinv : t⁻¹ ∈ normalizer (N : Set G) := inv_mem htN
  let σ : MulAut ↥N := N.normalizerMonoidHom ⟨t⁻¹, htinv⟩
  have hσ : ∀ x : ↥N, ((σ x : ↥N) : G) = t⁻¹ * (x : G) * t⁻¹⁻¹ := fun x => rfl
  let rQ : ↥N := ⟨r, hr⟩
  have hρ : ∀ x : ↥N, ((MulAut.conj rQ x : ↥N) : G) = r * (x : G) * r⁻¹ := fun x => rfl
  have hσmap : ∀ H : Subgroup G, (H.subgroupOf N).map σ.toMonoidHom = (Hᵍ[t]).subgroupOf N :=
    fun H => subgroupOf_map_aut H σ t⁻¹ hσ
  have hρmap : ∀ H : Subgroup G, (H.subgroupOf N).map (MulAut.conj rQ).toMonoidHom =
      (H.map (MulAut.conj r).toMonoidHom).subgroupOf N :=
    fun H => subgroupOf_map_aut H (MulAut.conj rQ) r hρ
  have hΛ'N : Λᵍ[t] ≤ N := hΛσ ▸ le_sup_right
  haveI : (X.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).2 hNX
  haveI : (Λ.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hΛN).2 hNΛ
  have hVN : V ≤ N := hVΛ.trans hΛN
  have hVrN : V.map (MulAut.conj r).toMonoidHom ≤ N := by
    rintro _ ⟨v, hv, rfl⟩
    have h1 : r * v * r⁻¹ ∈ N := mul_mem (mul_mem hr (hVN hv)) (inv_mem hr)
    exact h1
  have hFN : F ≤ N := hFX.trans hXN
  have key := CFSG.LocalAnalysis.EvenBN.Common.exists_split (σ := σ) (X := X.subgroupOf N)
    (Λ := Λ.subgroupOf N) (V := V.subgroupOf N) (F := F.subgroupOf N) (r := rQ) (q := q) hq
    (by rw [hσmap, hσX])
    (by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxX, hxc⟩ := hx
      have h1 : (x : G) ∈ X ⊓ centralizer (N : Set G) := by
        refine ⟨hxX, mem_centralizer_iff.2 fun n hn => ?_⟩
        have := Subgroup.mem_center_iff.1 hxc ⟨n, hn⟩
        exact congrArg Subtype.val this
      rw [hcen, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.2 (Subtype.ext h1))
    (by rw [hσmap, ← Subgroup.subgroupOf_sup hΛN hΛ'N, hΛσ, Subgroup.subgroupOf_self])
    (hV2.comap_subtype)
    (fun x hx => hVΛ hx)
    (fun x hx => hXV hx)
    (by
      rw [mem_normalizer_iff]
      intro x
      have h := mem_normalizer_iff.1 (hNΛ hr) (x : G)
      simpa [Subgroup.mem_subgroupOf] using h)
    (by
      rw [hρmap, ← Subgroup.subgroupOf_sup hVN hVrN]
      exact fun x hx => hgen hx)
    (by
      rw [hσmap, hρmap]
      intro x hx
      rw [mem_normalizer_iff]
      intro y
      have h := mem_normalizer_iff.1 (hVn hx) (y : G)
      simpa [Subgroup.mem_subgroupOf] using h)
    (fun x hx => hFX hx)
    (fun x hx => mem_centralizer_iff.2 fun v hv =>
      Subtype.ext ((mem_centralizer_iff.1 (hFV hx)) v hv))
    (by rw [hσmap, hσF])
    (by
      rw [hρmap, eq_bot_iff]
      intro x hx
      have : (x : G) ∈ F ⊓ F.map (MulAut.conj r).toMonoidHom := ⟨hx.1, hx.2⟩
      rw [hFr, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this))
    (by
      intro B hB hBn hnc
      let B' : Subgroup G := B.map N.subtype
      have hB'X : B' ≤ X := by
        rintro _ ⟨b, hb, rfl⟩
        exact hB hb
      have hNB' : N ≤ normalizer (B' : Set G) := by
        intro n hn
        rw [mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨b, hb, rfl⟩
          refine ⟨⟨n, hn⟩ * b * ⟨n, hn⟩⁻¹, hBn.conj_mem b hb ⟨n, hn⟩, ?_⟩
          rfl
        · rintro ⟨b, hb, hbe⟩
          have hbe' : (b : G) = n * y * n⁻¹ := hbe
          refine ⟨⟨n, hn⟩⁻¹ * b * ⟨n, hn⟩⁻¹⁻¹, hBn.conj_mem b hb ⟨n, hn⟩⁻¹, ?_⟩
          show n⁻¹ * (b : G) * n⁻¹⁻¹ = y
          rw [hbe']
          group
      have hnc' : ¬ Λᵍ[t] ≤ centralizer (B' : Set G) := by
        intro hle
        apply hnc
        rw [hσmap]
        intro x hx
        rw [mem_centralizer_iff]
        intro b hb
        exact Subtype.ext (mem_centralizer_iff.1 (hle hx) (b : G) ⟨b, hb, rfl⟩)
      have := hFS B' hB'X hNB' hnc'
      rwa [Subgroup.card_map_of_injective N.subtype_injective] at this)
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv).trans hcX)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv]; exact hcF)
  have hBQ : (X.subgroupOf N) ⊓ centralizer ((Λ.subgroupOf N : Subgroup ↥N) : Set ↥N) =
      (X ⊓ centralizer (Λ : Set G)).subgroupOf N := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_centralizer_iff]
    constructor
    · rintro ⟨hx, hc⟩
      refine ⟨hx, fun l hl => ?_⟩
      have := hc ⟨l, hΛN hl⟩ hl
      exact congrArg Subtype.val this
    · rintro ⟨hx, hc⟩
      exact ⟨hx, fun l hl => Subtype.ext (hc l hl)⟩
  obtain ⟨k1, k2, k3⟩ := key
  rw [hBQ, hσmap] at k1 k2
  rw [hBQ] at k3
  have hBN : (X ⊓ centralizer (Λ : Set G)) ≤ N := inf_le_left.trans hXN
  have hB'N : (X ⊓ centralizer (Λ : Set G))ᵍ[t] ≤ N := fun x hx =>
    hXN (hσX.le (Subgroup.map_mono inf_le_left hx))
  refine ⟨?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hBN hB'N] at k1
    have := Subgroup.subgroupOf_inj.1 k1
    rwa [inf_eq_left.2 (sup_le hBN hB'N), inf_eq_left.2 hXN] at this
  · rw [eq_bot_iff]
    intro z hz
    have hz' : (⟨z, hBN hz.1⟩ : ↥N) ∈ (X ⊓ centralizer (Λ : Set G)).subgroupOf N ⊓
        ((X ⊓ centralizer (Λ : Set G))ᵍ[t]).subgroupOf N := ⟨hz.1, hz.2⟩
    rw [k2, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hz')
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv]
    exact k3

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G} (hg : g ∈ normalizer (H : Set G)) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_normalizer_iff.1 hg h).1 hh
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
    simpa using this

theorem conjG_eq_map {s : G} (hs : s * s = 1) (A : Subgroup G) :
    Aᵍ[s] = A.map (MulAut.conj s).toMonoidHom := by
  rw [inv_eq_of_mul_eq_one_right hs]

namespace Cfg

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {t s : G}
  {M Λ N A P Y U : Subgroup G} (c : Cfg K f t s M Λ N A P Y U)

include c

theorem Y_le_Λ : Y ≤ Λ := c.hYM.trans c.hMΛ

theorem Y_le_conj : Y ≤ Λᵍ[t] := c.hYM.trans c.M_le_conj

theorem Y_le_P : Y ≤ P := c.hYM.trans c.hMP

theorem A_le_normalizer_Y : A ≤ normalizer (Y : Set G) := c.hAN.trans c.hNY

theorem K3_eq : Λ ⊓ (A ⊔ Y) = (Λ ⊓ A) ⊔ Y := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_left Λ le_sup_left)
    (le_inf c.Y_le_Λ le_sup_right))
  intro z hz
  obtain ⟨a, ha, y, hy, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    c.A_le_normalizer_Y z hz.2
  have haΛ : a ∈ Λ := by
    have h1 : a * y ∈ Λ := hz.1
    have h2 : y⁻¹ ∈ Λ := inv_mem (c.Y_le_Λ hy)
    have := mul_mem h1 h2
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨haΛ, ha⟩) (Subgroup.mem_sup_right hy)

theorem K3'_eq : Λᵍ[t] ⊓ (A ⊔ Y) = (Λᵍ[t] ⊓ A) ⊔ Y := by
  refine le_antisymm ?_ (sup_le (inf_le_inf_left _ le_sup_left)
    (le_inf c.Y_le_conj le_sup_right))
  intro z hz
  obtain ⟨a, ha, y, hy, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    c.A_le_normalizer_Y z hz.2
  have haΛ : a ∈ Λᵍ[t] := by
    have h1 : a * y ∈ Λᵍ[t] := hz.1
    have h2 : y⁻¹ ∈ Λᵍ[t] := inv_mem (c.Y_le_conj hy)
    have := mul_mem h1 h2
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨haΛ, ha⟩) (Subgroup.mem_sup_right hy)

theorem conj_K3 : (Λ ⊓ (A ⊔ Y))ᵍ[t] = Λᵍ[t] ⊓ (A ⊔ Y) := by
  rw [conj_inf, conj_sup, c.hAt, c.hYt]

theorem P3_eq : P ⊓ (Λ ⊓ (A ⊔ Y)) = (P ⊓ (Λ ⊓ A)) ⊔ Y := by
  rw [c.K3_eq]
  refine le_antisymm ?_ (sup_le (inf_le_inf_left P (le_sup_left)) (le_inf c.Y_le_P le_sup_right))
  intro z hz
  have hX : (Λ ⊓ A) ≤ normalizer (Y : Set G) := inf_le_right.trans c.A_le_normalizer_Y
  obtain ⟨x, hx, y, hy, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    hX z hz.2
  have hxP : x ∈ P := by
    have h1 : x * y ∈ P := hz.1
    have h2 : y⁻¹ ∈ P := inv_mem (c.Y_le_P hy)
    have := mul_mem h1 h2
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (Subgroup.mem_sup_left ⟨hxP, hx⟩) (Subgroup.mem_sup_right hy)

theorem conj_P3_eq : (P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[t] = (P ⊓ (Λᵍ[t] ⊓ A)) ⊔ Y := by
  rw [c.P3_eq, conj_sup, conj_inf, c.hPt, conj_inf, c.hAt, c.hYt]

theorem hsN : s ∈ N := c.hAN c.hsA

theorem A_le_normalizer_X : A ≤ normalizer ((Λ ⊓ A : Subgroup G) : Set G) := fun a ha =>
  le_normalizer_inf Λ A
    ⟨c.le_normalizer_left (c.hAN ha), le_normalizer ha⟩

theorem A_le_normalizer_X' : A ≤ normalizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G) := fun a ha =>
  le_normalizer_inf _ A
    ⟨c.le_normalizer_right (c.hAN ha), le_normalizer ha⟩

theorem s_normalizer_X : s ∈ normalizer ((Λ ⊓ A : Subgroup G) : Set G) :=
  c.A_le_normalizer_X c.hsA

theorem s_normalizer_X' : s ∈ normalizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G) :=
  c.A_le_normalizer_X' c.hsA

theorem X_eq : Λ ⊓ A = (P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom := by
  have hX₀X : ((P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom) ≤ Λ ⊓ A :=
    sup_le inf_le_right ((Subgroup.map_mono inf_le_right).trans
      (map_conj_eq_of_mem_normalizer c.s_normalizer_X).le)
  have hX₀'X' : ((P ⊓ (Λᵍ[t] ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)).map (MulAut.conj s).toMonoidHom) ≤
      Λᵍ[t] ⊓ A :=
    sup_le inf_le_right ((Subgroup.map_mono inf_le_right).trans
      (map_conj_eq_of_mem_normalizer c.s_normalizer_X').le)
  refine le_antisymm ?_ hX₀X
  have hHN : ((P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom) ⊔
      ((P ⊓ (Λᵍ[t] ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)).map (MulAut.conj s).toMonoidHom) ≤ A :=
    sup_le (hX₀X.trans inf_le_right) (hX₀'X'.trans inf_le_right)
  have hP1 : P ≤ M ⊔ (((P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom) ⊔
      ((P ⊓ (Λᵍ[t] ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)).map (MulAut.conj s).toMonoidHom)) := by
    refine c.P_le.trans (sup_le (sup_le le_sup_left ?_) ?_)
    · exact le_sup_left.trans (le_sup_left.trans le_sup_right)
    · exact le_sup_left.trans (le_sup_right.trans le_sup_right)
  have hP2 : P.map (MulAut.conj s).toMonoidHom ≤ M ⊔
      (((P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom) ⊔
      ((P ⊓ (Λᵍ[t] ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)).map (MulAut.conj s).toMonoidHom)) := by
    refine (Subgroup.map_mono c.P_le).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup, map_conj_eq_of_mem_normalizer
      (c.hNM c.hsN)]
    refine sup_le (sup_le le_sup_left ?_) ?_
    · exact (le_sup_right : _ ≤ (P ⊓ (Λ ⊓ A)) ⊔ _).trans (le_sup_left.trans le_sup_right)
    · exact (le_sup_right : _ ≤ (P ⊓ (Λᵍ[t] ⊓ A)) ⊔ _).trans (le_sup_right.trans le_sup_right)
  have hNH : N ≤ M ⊔ (((P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom) ⊔
      ((P ⊓ (Λᵍ[t] ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)).map (MulAut.conj s).toMonoidHom)) := by
    rw [c.hNPs]
    exact sup_le hP1 hP2
  set X₀ := (P ⊓ (Λ ⊓ A)) ⊔ (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom with hX₀
  set X₀' := (P ⊓ (Λᵍ[t] ⊓ A)) ⊔ (P ⊓ (Λᵍ[t] ⊓ A)).map (MulAut.conj s).toMonoidHom with hX₀'
  have hHnorm : X₀ ⊔ X₀' ≤ normalizer (M : Set G) := hHN.trans c.A_le_normalizer_M
  have hAH : A ≤ X₀ ⊔ X₀' := by
    intro a ha
    have h0 : a ∈ M ⊔ (X₀ ⊔ X₀') := hNH (c.hAN ha)
    obtain ⟨m, hm, h, hh, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer
      hHnorm a h0
    have hmA : m ∈ A := by
      have h1 : m * h ∈ A := ha
      have h2 : h⁻¹ ∈ A := inv_mem (hHN hh)
      have := mul_mem h1 h2
      rwa [mul_inv_cancel_right] at this
    have h3 : m ∈ A ⊓ M := ⟨hmA, hm⟩
    rw [c.hAM, Subgroup.mem_bot] at h3
    rw [h3, one_mul]
    exact hh
  have hX₀norm : X₀ ≤ normalizer (X₀' : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    have := c.comm_X (hX₀X hx) (hX₀'X' hy)
    rw [this]
    group
    exact one_mem _
  intro x hx
  have hxH : x ∈ X₀ ⊔ X₀' := hAH hx.2
  obtain ⟨x₀, hx₀, x₀', hx₀', rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    hX₀norm x hxH
  have h1 : x₀' ∈ Λ ⊓ A := by
    have h2 : x₀⁻¹ ∈ Λ ⊓ A := inv_mem (hX₀X hx₀)
    have := mul_mem h2 hx
    rwa [inv_mul_cancel_left] at this
  have h3 : x₀' ∈ (Λ ⊓ A) ⊓ (Λᵍ[t] ⊓ A) := ⟨h1, hX₀'X' hx₀'⟩
  rw [c.inf_X, Subgroup.mem_bot] at h3
  rw [h3, mul_one]
  exact hx₀

theorem s_normalizer_Y : s ∈ normalizer (Y : Set G) := c.hNY c.hsN

theorem K3_inf_M : (Λ ⊓ (A ⊔ Y)) ⊓ M = Y := by
  refine le_antisymm ?_ (le_inf (le_inf c.Y_le_Λ le_sup_right) c.hYM)
  rintro z ⟨hzK, hzM⟩
  have hz : z ∈ (Λ ⊓ A) ⊔ Y := by rw [← c.K3_eq]; exact hzK
  have hX : (Λ ⊓ A) ≤ normalizer (Y : Set G) := inf_le_right.trans c.A_le_normalizer_Y
  obtain ⟨x, hx, y, hy, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
    hX z hz
  have hxM : x ∈ M := by
    have h1 : x * y ∈ M := hzM
    have h2 : y⁻¹ ∈ M := inv_mem (c.hYM hy)
    have := mul_mem h1 h2
    rwa [mul_inv_cancel_right] at this
  have h3 : x ∈ A ⊓ M := ⟨hx.2, hxM⟩
  rw [c.hAM, Subgroup.mem_bot] at h3
  rw [h3, one_mul]
  exact hy

theorem P3_inf : (P ⊓ (Λ ⊓ (A ⊔ Y))) ⊓ (P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[s] = Y := by
  rw [conjG_eq_map c.hs2]
  refine le_antisymm ?_ ?_
  · rintro z ⟨hz1, hz2⟩
    have hzP : z ∈ P ⊓ P.map (MulAut.conj s).toMonoidHom :=
      ⟨hz1.1, (Subgroup.map_mono inf_le_left) hz2⟩
    rw [c.hPPs] at hzP
    have h : z ∈ (Λ ⊓ (A ⊔ Y)) ⊓ M := ⟨hz1.2, hzP⟩
    rwa [c.K3_inf_M] at h
  · intro y hy
    have hyP3 : y ∈ P ⊓ (Λ ⊓ (A ⊔ Y)) := ⟨c.Y_le_P hy, c.Y_le_Λ hy, Subgroup.mem_sup_right hy⟩
    refine ⟨hyP3, ?_⟩
    have hmapY : Y.map (MulAut.conj s).toMonoidHom = Y :=
      map_conj_eq_of_mem_normalizer c.s_normalizer_Y
    have hYle : Y ≤ (P ⊓ (Λ ⊓ (A ⊔ Y))).map (MulAut.conj s).toMonoidHom :=
      hmapY.symm.le.trans (Subgroup.map_mono (fun z hz =>
        ⟨c.Y_le_P hz, c.Y_le_Λ hz, Subgroup.mem_sup_right hz⟩))
    exact hYle hy

theorem K3_eq_sup : Λ ⊓ (A ⊔ Y) =
    (P ⊓ (Λ ⊓ (A ⊔ Y))) ⊔ (P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[s] := by
  have h1 : P ⊓ (Λ ⊓ (A ⊔ Y)) = (P ⊓ (Λ ⊓ A)) ⊔ Y := c.P3_eq
  have h2 : (P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[s] =
      (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom ⊔ Y := by
    rw [conjG_eq_map c.hs2, h1, Subgroup.map_sup, map_conj_eq_of_mem_normalizer c.s_normalizer_Y]
  rw [h2, h1, c.K3_eq]
  have hT : P ⊓ (Λ ⊓ A) ≤ (Λ ⊓ A) ⊔ Y := inf_le_right.trans le_sup_left
  have hTs : (P ⊓ (Λ ⊓ A)).map (MulAut.conj s).toMonoidHom ≤ (Λ ⊓ A) ⊔ Y :=
    ((Subgroup.map_mono inf_le_right).trans
      (map_conj_eq_of_mem_normalizer c.s_normalizer_X).le).trans le_sup_left
  have hY : Y ≤ (Λ ⊓ A) ⊔ Y := le_sup_right
  refine le_antisymm ?_ (sup_le (sup_le hT hY) (sup_le hTs hY))
  refine sup_le (c.X_eq.le.trans (sup_le_sup le_sup_left le_sup_left)) ?_
  exact le_sup_right.trans le_sup_left

end Cfg

theorem zc_sup_eq {X Y : Subgroup G} (hXY : X ≤ normalizer (Y : Set G))
    (hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) (hfaith : X ⊓ centralizer (Y : Set G) = ⊥) :
    zc (X ⊔ Y) = Y ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨hzK, hzC⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer'
      hXY z hzK
    have hxC : x ∈ centralizer (Y : Set G) := by
      rw [mem_centralizer_iff]
      intro v hv
      have h1 := mem_centralizer_iff.1 hzC v (Subgroup.mem_sup_right hv)
      have h2 : y * v = v * y := hYab y hy v hv
      calc v * x = (v * x * y) * y⁻¹ := by group
        _ = (x * y * v) * y⁻¹ := by rw [mul_assoc v x y, h1]
        _ = x * (y * v) * y⁻¹ := by group
        _ = x * (v * y) * y⁻¹ := by rw [h2]
        _ = x * v := by group
    have hx1 : x = 1 := by
      have : x ∈ X ⊓ centralizer (Y : Set G) := ⟨hx, hxC⟩
      rwa [hfaith, Subgroup.mem_bot] at this
    subst hx1
    rw [one_mul] at hzK hzC ⊢
    exact ⟨hy, hzC⟩
  · rintro z ⟨hzY, hzC⟩
    exact ⟨Subgroup.mem_sup_right hzY, hzC⟩

theorem inf_centralizer_sup {X Y : Subgroup G} (hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) :
    Y ⊓ centralizer ((X ⊔ Y : Subgroup G) : Set G) = Y ⊓ centralizer (X : Set G) := by
  refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le (by exact_mod_cast le_sup_left)))
    ?_
  rintro z ⟨hzY, hzC⟩
  refine ⟨hzY, ?_⟩
  have hX : X ≤ centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzC a ha)
  have hY : Y ≤ centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hYab z hzY a ha).symm
  have hXY : X ⊔ Y ≤ centralizer ({z} : Set G) := sup_le hX hY
  exact Subgroup.mem_centralizer_iff.2 fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.1 (hXY hg)

namespace Cfg

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {t s : G}
  {M Λ N A P Y U : Subgroup G} (c : Cfg K f t s M Λ N A P Y U)

include c

theorem hquot' : IsQuotientIso Λᵍ[t] M (SL(2, K)) := by
  have := CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.IsQuotientIso.conj
    c.hquot t
  rwa [c.hMt] at this

theorem nonempty_equiv_X : Nonempty (↥(Λ ⊓ A) ≃* SL(2, K)) :=
  nonempty_mulEquiv_of_quotient c.hMΛ (fun l hl => c.decomp_left hl) c.hAM c.hquot

theorem nonempty_equiv_X' : Nonempty (↥(Λᵍ[t] ⊓ A) ≃* SL(2, K)) :=
  nonempty_mulEquiv_of_quotient c.M_le_conj (fun l hl => c.decomp_right hl) c.hAM c.hquot'

theorem faith_X' : (Λᵍ[t] ⊓ A) ⊓ centralizer (Y : Set G) = ⊥ := by
  have h : (Λ ⊓ A ⊓ centralizer (Y : Set G))ᵍ[t] =
      (Λ ⊓ A)ᵍ[t] ⊓ centralizer ((Yᵍ[t] : Subgroup G) : Set G) :=
    CFSG.LocalAnalysis.EvenBN.Common.map_inf_centralizer (MulAut.conj t⁻¹) (Λ ⊓ A) Y
  rw [c.faith_X, Subgroup.map_bot, c.conj_X, c.hYt] at h
  exact h.symm

theorem zc_K3 : zc (Λ ⊓ (A ⊔ Y)) = Y ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G) := by
  rw [c.K3_eq, zc_sup_eq (inf_le_right.trans c.A_le_normalizer_Y) c.hYab c.faith_X,
    inf_centralizer_sup c.hYab]

theorem zc_K3' : zc ((Λ ⊓ (A ⊔ Y))ᵍ[t]) = Y ⊓ centralizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G) := by
  rw [c.conj_K3, c.K3'_eq, zc_sup_eq (inf_le_right.trans c.A_le_normalizer_Y) c.hYab c.faith_X',
    inf_centralizer_sup c.hYab]

theorem zc_P3 : zc (P ⊓ (Λ ⊓ (A ⊔ Y))) = Y ⊓ centralizer ((P ⊓ (Λ ⊓ A) : Subgroup G) : Set G) := by
  have hf : (P ⊓ (Λ ⊓ A)) ⊓ centralizer (Y : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ (Λ ⊓ A) ⊓ centralizer (Y : Set G) := ⟨hz.1.2, hz.2⟩
    rwa [c.faith_X] at this
  rw [c.P3_eq, zc_sup_eq (inf_le_right.trans (inf_le_right.trans c.A_le_normalizer_Y)) c.hYab hf,
    inf_centralizer_sup c.hYab]

theorem zc_P3' : zc ((P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[t]) =
    Y ⊓ centralizer ((P ⊓ (Λᵍ[t] ⊓ A) : Subgroup G) : Set G) := by
  have hf : (P ⊓ (Λᵍ[t] ⊓ A)) ⊓ centralizer (Y : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ (Λᵍ[t] ⊓ A) ⊓ centralizer (Y : Set G) := ⟨hz.1.2, hz.2⟩
    rwa [c.faith_X'] at this
  rw [c.conj_P3_eq, zc_sup_eq (inf_le_right.trans (inf_le_right.trans c.A_le_normalizer_Y))
    c.hYab hf, inf_centralizer_sup c.hYab]

theorem X_le_normalizer_of_le_X' {E : Subgroup G} (hE : E ≤ Λᵍ[t] ⊓ A) :
    (Λ ⊓ A) ≤ normalizer (E : Set G) := by
  refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
  rw [c.comm_X hx (hE hy)]
  group
  exact one_mem _

theorem X'_le_normalizer_of_le_X {E : Subgroup G} (hE : E ≤ Λ ⊓ A) :
    (Λᵍ[t] ⊓ A) ≤ normalizer (E : Set G) := by
  refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
  rw [← c.comm_X (hE hy) hx]
  group
  exact one_mem _

theorem split :
    (Y ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G)) ⊔
        (Y ⊓ centralizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G)) = Y ∧
      (Y ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G)) ⊓
        (Y ⊓ centralizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G)) = ⊥ ∧
      Nat.card (Y ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G) : Subgroup G) =
        Nat.card K ^ 2 := by
  obtain ⟨ψ'⟩ := c.nonempty_equiv_X'
  have hAYY : A ⊔ Y ≤ normalizer (Y : Set G) := sup_le c.A_le_normalizer_Y le_normalizer
  have hAYN : A ⊔ Y ≤ N := sup_le c.hAN (c.Y_le_Λ.trans c.hΛN)
  have hAYΛ : A ⊔ Y ≤ normalizer (Λ : Set G) := hAYN.trans c.le_normalizer_left
  have hK4 := c.four_le
  have hcen : Y ⊓ centralizer ((A ⊔ Y : Subgroup G) : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyY, hyC⟩
    have hyN : y ∈ N ⊓ centralizer (N : Set G) := by
      refine ⟨c.hΛN (c.Y_le_Λ hyY), Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have hgN : N ≤ centralizer ({y} : Set G) := by
        rw [c.hNA]
        refine sup_le (fun a ha => ?_) (fun m hm => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (mem_centralizer_iff.1 hyC a (Subgroup.mem_sup_left ha))
        · exact Subgroup.mem_centralizer_singleton_iff.2 (c.hMY m hm y hyY)
      exact Subgroup.mem_centralizer_singleton_iff.1 (hgN hg)
    rwa [c.hZN] at hyN
  have hΛσ : (Λ ⊓ (A ⊔ Y)) ⊔ (Λ ⊓ (A ⊔ Y))ᵍ[t] = A ⊔ Y := by
    rw [c.conj_K3, c.K3_eq, c.K3'_eq]
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · exact sup_le (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
        (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
    · intro a ha
      obtain ⟨x, hx, y, hy, rfl⟩ := c.A_eq_mul ha
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left hy))
    · exact le_sup_right.trans le_sup_left
  have hgen : Λ ⊓ (A ⊔ Y) ≤ (P ⊓ (Λ ⊓ (A ⊔ Y))) ⊔
      (P ⊓ (Λ ⊓ (A ⊔ Y))).map (MulAut.conj s).toMonoidHom := by
    have := c.K3_eq_sup
    rw [conjG_eq_map c.hs2] at this
    exact this.le
  have hVn : P ⊓ (Λ ⊓ (A ⊔ Y)) ≤ normalizer ((((P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[t]).map
      (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
    rw [c.conj_P3_eq, Subgroup.map_sup, map_conj_eq_of_mem_normalizer c.s_normalizer_Y]
    have hT's : (P ⊓ (Λᵍ[t] ⊓ A)).map (MulAut.conj s).toMonoidHom ≤ Λᵍ[t] ⊓ A :=
      (Subgroup.map_mono inf_le_right).trans
        (map_conj_eq_of_mem_normalizer c.s_normalizer_X').le
    refine c.P3_eq.le.trans (sup_le ?_ ?_)
    · intro x hx
      exact mem_normalizer_sup (c.X_le_normalizer_of_le_X' hT's hx.2)
        (c.A_le_normalizer_Y hx.2.2)
    · exact le_sup_right.trans le_normalizer
  have hFV : U ≤ centralizer ((P ⊓ (Λ ⊓ (A ⊔ Y)) : Subgroup G) : Set G) := by
    have h1 : U ≤ centralizer (P : Set G) := c.hZP ▸ inf_le_right
    exact h1.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 inf_le_left))
  have hFS : ∀ B : Subgroup G, B ≤ Y → A ⊔ Y ≤ normalizer (B : Set G) →
      ¬ (Λ ⊓ (A ⊔ Y))ᵍ[t] ≤ centralizer (B : Set G) → Nat.card K ^ 2 ≤ Nat.card B := by
    intro B hBY hNB hnc
    have hnc' : ¬ (Λᵍ[t] ⊓ A) ≤ centralizer (B : Set G) := by
      intro hle
      apply hnc
      rw [c.conj_K3, c.K3'_eq]
      refine sup_le hle ?_
      intro y hy
      exact Subgroup.mem_centralizer_iff.2 fun b hb => c.hYab b (hBY hb) y hy
    have h := CFSG.LocalAnalysis.EvenBN.Common.sl2_card_sq_le_of_not_le_centralizer ψ' c.hK c.hf
      (fun v hv => c.hYsq v (hBY hv)) (inf_le_right.trans (le_sup_left.trans hNB)) hnc'
    exact h
  have key := split_ambient (N := A ⊔ Y) (X := Y) (Λ := Λ ⊓ (A ⊔ Y))
    (V := P ⊓ (Λ ⊓ (A ⊔ Y))) (F := U) (t := t) (r := s) (q := Nat.card K) (by omega) c.ht
    (mem_normalizer_sup (mem_normalizer_of_conj_eq c.hAt) (mem_normalizer_of_conj_eq c.hYt))
    (Subgroup.mem_sup_left c.hsA) le_sup_right inf_le_right inf_le_right
    (le_inf c.Y_le_P (le_inf c.Y_le_Λ le_sup_right)) c.hUY hAYY
    (fun x hx => le_normalizer_inf Λ (A ⊔ Y) ⟨hAYΛ hx, le_normalizer hx⟩) c.hYt hcen hΛσ
    (c.hPN.isPGroup.to_le inf_le_left) hgen hVn hFV c.hUt c.hUs hFS c.hcY
    (le_of_eq c.hcU.symm)
  have hB : Y ⊓ centralizer ((Λ ⊓ (A ⊔ Y) : Subgroup G) : Set G) =
      Y ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G) := by
    rw [c.K3_eq, inf_centralizer_sup c.hYab]
  have hBt : (Y ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G))ᵍ[t] =
      Y ⊓ centralizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G) := by
    have := CFSG.LocalAnalysis.EvenBN.Common.map_inf_centralizer (MulAut.conj t⁻¹) Y (Λ ⊓ A)
    rw [c.hYt, c.conj_X] at this
    exact this
  rw [hB, hBt] at key
  exact key

abbrev V₂ (Y Λ A : Subgroup G) : Subgroup G := Y ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G)

abbrev V₁ (t : G) (Y Λ A : Subgroup G) : Subgroup G :=
  Y ⊓ centralizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G)

abbrev Tsub (P Λ A : Subgroup G) : Subgroup G := P ⊓ (Λ ⊓ A)

abbrev Tsub' (t : G) (P Λ A : Subgroup G) : Subgroup G := P ⊓ (Λᵍ[t] ⊓ A)

theorem conj_V₂ : (V₂ Y Λ A)ᵍ[t] = V₁ t Y Λ A := by
  have := CFSG.LocalAnalysis.EvenBN.Common.map_inf_centralizer (MulAut.conj t⁻¹) Y (Λ ⊓ A)
  rw [c.hYt, c.conj_X] at this
  exact this

theorem card_V : Nat.card (V₂ Y Λ A) = Nat.card K ^ 2 ∧ Nat.card (V₁ t Y Λ A) = Nat.card K ^ 2 := by
  have h := c.split.2.2
  refine ⟨h, ?_⟩
  rw [← c.conj_V₂, card_conj]
  exact h

theorem V_inf : V₂ Y Λ A ⊓ V₁ t Y Λ A = ⊥ := c.split.2.1

theorem V_sup : V₂ Y Λ A ⊔ V₁ t Y Λ A = Y := c.split.1

theorem decomp_Y {y : G} (hy : y ∈ Y) : ∃ v₂ ∈ V₂ Y Λ A, ∃ v₁ ∈ V₁ t Y Λ A, y = v₂ * v₁ := by
  have hn : V₂ Y Λ A ≤ normalizer ((V₁ t Y Λ A : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    rw [c.hYab x hx.1 y hy.1]
    group
    exact one_mem _
  have hy' : y ∈ V₂ Y Λ A ⊔ V₁ t Y Λ A := by rw [c.V_sup]; exact hy
  exact CFSG.LocalAnalysis.EvenBN.Common.exists_mul_of_le_normalizer' hn y hy'

theorem X_le_normalizer_V₁ : (Λ ⊓ A) ≤ normalizer ((V₁ t Y Λ A : Subgroup G) : Set G) := by
  have key : ∀ g ∈ (Λ ⊓ A : Subgroup G), ∀ w ∈ V₁ t Y Λ A, g * w * g⁻¹ ∈ V₁ t Y Λ A := by
    intro g hg w hw
    refine ⟨(mem_normalizer_iff.1 (c.A_le_normalizer_Y hg.2) w).1 hw.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hc : y * w = w * y := Subgroup.mem_centralizer_iff.1 hw.2 y hy
    have hxy : g * y = y * g := c.comm_X hg hy
    have hyx' : y * g⁻¹ = g⁻¹ * y := by
      calc y * g⁻¹ = g⁻¹ * (g * y) * g⁻¹ := by group
        _ = g⁻¹ * (y * g) * g⁻¹ := by rw [hxy]
        _ = g⁻¹ * y := by group
    calc y * (g * w * g⁻¹) = (y * g) * w * g⁻¹ := by group
      _ = (g * y) * w * g⁻¹ := by rw [hxy]
      _ = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hc]
      _ = g * w * (y * g⁻¹) := by group
      _ = g * w * (g⁻¹ * y) := by rw [hyx']
      _ = g * w * g⁻¹ * y := by group
  intro x hx
  rw [mem_normalizer_iff]
  intro v
  constructor
  · exact key x hx v
  · intro h
    have := key x⁻¹ (inv_mem hx) _ h
    simpa [mul_assoc] using this

theorem X'_le_normalizer_V₂ : (Λᵍ[t] ⊓ A) ≤ normalizer ((V₂ Y Λ A : Subgroup G) : Set G) := by
  have key : ∀ g ∈ (Λᵍ[t] ⊓ A : Subgroup G), ∀ w ∈ V₂ Y Λ A, g * w * g⁻¹ ∈ V₂ Y Λ A := by
    intro g hg w hw
    refine ⟨(mem_normalizer_iff.1 (c.A_le_normalizer_Y hg.2) w).1 hw.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hc : y * w = w * y := Subgroup.mem_centralizer_iff.1 hw.2 y hy
    have hxy : y * g = g * y := c.comm_X hy hg
    have hyx' : y * g⁻¹ = g⁻¹ * y := by
      calc y * g⁻¹ = g⁻¹ * (g * y) * g⁻¹ := by group
        _ = g⁻¹ * (y * g) * g⁻¹ := by rw [hxy]
        _ = g⁻¹ * y := by group
    calc y * (g * w * g⁻¹) = (y * g) * w * g⁻¹ := by group
      _ = (g * y) * w * g⁻¹ := by rw [hxy]
      _ = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hc]
      _ = g * w * (y * g⁻¹) := by group
      _ = g * w * (g⁻¹ * y) := by rw [hyx']
      _ = g * w * g⁻¹ * y := by group
  intro x hx
  rw [mem_normalizer_iff]
  intro v
  constructor
  · exact key x hx v
  · intro h
    have := key x⁻¹ (inv_mem hx) _ h
    simpa [mul_assoc] using this

theorem conj_T : (Tsub P Λ A)ᵍ[t] = Tsub' t P Λ A := by
  show (P ⊓ (Λ ⊓ A))ᵍ[t] = P ⊓ (Λᵍ[t] ⊓ A)
  rw [conj_inf, c.hPt, conj_inf, c.hAt]

theorem card_T' : Nat.card (Tsub' t P Λ A) = Nat.card K := by
  rw [← c.conj_T, card_conj]
  exact c.card_T

theorem P_eq : P = M ⊔ Tsub P Λ A ⊔ Tsub' t P Λ A :=
  le_antisymm c.P_le (sup_le (sup_le c.hMP inf_le_left) inf_le_left)

theorem mem_U_of_centralizes {v : G} (hvY : v ∈ Y) (hT : v ∈ centralizer (Tsub P Λ A : Set G))
    (hT' : v ∈ centralizer (Tsub' t P Λ A : Set G)) : v ∈ U := by
  have hP : P ≤ centralizer ({v} : Set G) := by
    rw [c.P_eq]
    refine sup_le (sup_le (fun m hm => ?_) (fun a ha => ?_)) (fun a ha => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (c.hMY m hm v hvY)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hT a ha)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hT' a ha)
  have h : v ∈ P ⊓ centralizer (P : Set G) :=
    ⟨c.Y_le_P hvY, Subgroup.mem_centralizer_iff.2 fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.1 (hP hg)⟩
  rwa [c.hZP] at h

theorem U_le_centralizer {u : G} (hu : u ∈ U) :
    u ∈ centralizer (P : Set G) := by
  have h : u ∈ P ⊓ centralizer (P : Set G) := by rw [c.hZP]; exact hu
  exact h.2

theorem U1_le_U : V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G) ≤ U := by
  rintro v ⟨hv1, hvT⟩
  exact c.mem_U_of_centralizes hv1.1 hvT (Subgroup.mem_centralizer_iff.2 fun a ha =>
    Subgroup.mem_centralizer_iff.1 hv1.2 a ha.2)

theorem U2_le_U : V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G) ≤ U := by
  rintro v ⟨hv2, hvT'⟩
  exact c.mem_U_of_centralizes hv2.1 (Subgroup.mem_centralizer_iff.2 fun a ha =>
    Subgroup.mem_centralizer_iff.1 hv2.2 a ha.2) hvT'

theorem U_le : U ≤ (V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G)) ⊔
    (V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G)) := by
  intro u hu
  have huY : u ∈ Y := c.hUY hu
  have huC := c.U_le_centralizer hu
  obtain ⟨v₂, hv₂, v₁, hv₁, rfl⟩ := c.decomp_Y huY
  have h1 : v₁ ∈ V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G) := by
    refine ⟨hv₁, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have h2 : a * v₂ = v₂ * a := Subgroup.mem_centralizer_iff.1 hv₂.2 a ha.2
    have hcT : a * (v₂ * v₁) = (v₂ * v₁) * a := Subgroup.mem_centralizer_iff.1 huC a ha.1
    refine mul_left_cancel (a := v₂) ?_
    calc v₂ * (a * v₁) = (v₂ * a) * v₁ := by group
      _ = (a * v₂) * v₁ := by rw [h2]
      _ = a * (v₂ * v₁) := by group
      _ = (v₂ * v₁) * a := hcT
      _ = v₂ * (v₁ * a) := by group
  have h2 : v₂ ∈ V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G) := by
    refine ⟨hv₂, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have h3 : a * v₁ = v₁ * a := Subgroup.mem_centralizer_iff.1 hv₁.2 a ha.2
    have hcT : a * (v₂ * v₁) = (v₂ * v₁) * a := Subgroup.mem_centralizer_iff.1 huC a ha.1
    refine mul_right_cancel (b := v₁) ?_
    calc a * v₂ * v₁ = a * (v₂ * v₁) := by group
      _ = (v₂ * v₁) * a := hcT
      _ = v₂ * (v₁ * a) := by group
      _ = v₂ * (a * v₁) := by rw [h3]
      _ = v₂ * a * v₁ := by group
  exact mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left h1)

theorem fix_V₁ : V₁ t Y Λ A ⊓ centralizer ((Λ ⊓ A : Subgroup G) : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv1, hvC⟩
  have h : v ∈ V₂ Y Λ A ⊓ V₁ t Y Λ A := ⟨⟨hv1.1, hvC⟩, hv1⟩
  rwa [c.V_inf] at h

theorem fix_V₂ : V₂ Y Λ A ⊓ centralizer ((Λᵍ[t] ⊓ A : Subgroup G) : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hv2, hvC⟩
  have h : v ∈ V₂ Y Λ A ⊓ V₁ t Y Λ A := ⟨hv2, ⟨hv2.1, hvC⟩⟩
  rwa [c.V_inf] at h

theorem card_U1_le :
    Nat.card (V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G) : Subgroup G) ≤ 2 ^ f := by
  obtain ⟨ψ⟩ := c.nonempty_equiv_X
  exact CFSG.LocalAnalysis.EvenBN.Common.card_inf_centralizer_le_of_inf_centralizer_eq_bot c.hK ψ
    (fun a ha b hb => c.hYab a ha.1 b hb.1) c.X_le_normalizer_V₁
    (by rw [c.card_V.2, c.hK]) c.fix_V₁ inf_le_right c.card_T

theorem card_U2_le :
    Nat.card (V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G) : Subgroup G) ≤ 2 ^ f := by
  obtain ⟨ψ⟩ := c.nonempty_equiv_X'
  exact CFSG.LocalAnalysis.EvenBN.Common.card_inf_centralizer_le_of_inf_centralizer_eq_bot c.hK ψ
    (fun a ha b hb => c.hYab a ha.1 b hb.1) c.X'_le_normalizer_V₂
    (by rw [c.card_V.1, c.hK]) c.fix_V₂ inf_le_right c.card_T'

theorem U_eq : U = (V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G)) ⊔
    (V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G)) :=
  le_antisymm c.U_le (sup_le c.U1_le_U c.U2_le_U)

theorem card_U_eq :
    Nat.card (V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G) : Subgroup G) = 2 ^ f ∧
      Nat.card (V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G) : Subgroup G) = 2 ^ f := by
  have h1 := c.card_U1_le
  have h2 := c.card_U2_le
  have hn : (V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G)) ≤
      normalizer (((V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G)) : Subgroup G) : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    rw [c.hYab x hx.1.1 y hy.1.1]
    group
    exact one_mem _
  have hcard := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq hn
  have hinf : (V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G)) ⊓
      (V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : z ∈ V₂ Y Λ A ⊓ V₁ t Y Λ A := ⟨hz.2.1, hz.1.1⟩
    rwa [c.V_inf] at this
  rw [hinf, Subgroup.card_bot, mul_one, ← c.U_eq, c.hcU, c.hK] at hcard
  have hpos : 0 < 2 ^ f := by positivity
  constructor
  · by_contra hne
    have hlt := lt_of_le_of_ne h1 hne
    nlinarith
  · by_contra hne
    have hlt := lt_of_le_of_ne h2 hne
    nlinarith

end Cfg

theorem commutator_self_of_equiv {K : Type} [Field K] [Finite K] {X : Subgroup G}
    (e : ↥X ≃* SL(2, K)) (h4 : 4 ≤ Nat.card K) : ⁅X, X⁆ = X := by
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  have htop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) := by
    have h1 : (⁅(⊤ : Subgroup SL(2, K)), (⊤ : Subgroup SL(2, K))⁆).map
        e.symm.toMonoidHom = ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
      rw [map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.symm.surjective]
    rw [← h1, ← commutator_def, Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 e.symm.surjective]
  have h2 := congrArg (Subgroup.map X.subtype) htop
  rwa [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

namespace Cfg

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {t s : G}
  {M Λ N A P Y U : Subgroup G} (c : Cfg K f t s M Λ N A P Y U)

include c

theorem X_perfect : ⁅Λ ⊓ A, Λ ⊓ A⁆ = Λ ⊓ A := by
  obtain ⟨ψ⟩ := c.nonempty_equiv_X
  exact commutator_self_of_equiv ψ c.four_le

theorem B3 : zc (P ⊓ (Λ ⊓ (A ⊔ Y))) = zc (Λ ⊓ (A ⊔ Y)) ⊔ U := by
  rw [c.zc_P3, c.zc_K3]
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro v hv
    obtain ⟨v₂, hv₂, v₁, hv₁, rfl⟩ := c.decomp_Y hv.1
    have hv₁T : v₁ ∈ centralizer (Tsub P Λ A : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      have h2 : a * v₂ = v₂ * a := Subgroup.mem_centralizer_iff.1 hv₂.2 a ha.2
      have hcT : a * (v₂ * v₁) = (v₂ * v₁) * a := Subgroup.mem_centralizer_iff.1 hv.2 a ha
      refine mul_left_cancel (a := v₂) ?_
      calc v₂ * (a * v₁) = (v₂ * a) * v₁ := by group
        _ = (a * v₂) * v₁ := by rw [h2]
        _ = a * (v₂ * v₁) := by group
        _ = (v₂ * v₁) * a := hcT
        _ = v₂ * (v₁ * a) := by group
    exact mul_mem (Subgroup.mem_sup_left hv₂) (Subgroup.mem_sup_right (c.U1_le_U ⟨hv₁, hv₁T⟩))
  · exact fun v hv => ⟨hv.1, Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_iff.1 hv.2 a ha.2⟩
  · intro u hu
    exact ⟨c.hUY hu, Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_iff.1 (c.U_le_centralizer hu) a ha.1⟩

theorem B3' : zc ((P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[t]) = zc ((Λ ⊓ (A ⊔ Y))ᵍ[t]) ⊔ U := by
  rw [c.zc_P3', c.zc_K3']
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro v hv
    obtain ⟨v₂, hv₂, v₁, hv₁, rfl⟩ := c.decomp_Y hv.1
    have hv₂T : v₂ ∈ centralizer (Tsub' t P Λ A : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun a ha => ?_
      have h3 : a * v₁ = v₁ * a := Subgroup.mem_centralizer_iff.1 hv₁.2 a ha.2
      have hcT : a * (v₂ * v₁) = (v₂ * v₁) * a := Subgroup.mem_centralizer_iff.1 hv.2 a ha
      refine mul_right_cancel (b := v₁) ?_
      calc a * v₂ * v₁ = a * (v₂ * v₁) := by group
        _ = (v₂ * v₁) * a := hcT
        _ = v₂ * (v₁ * a) := by group
        _ = v₂ * (a * v₁) := by rw [h3]
        _ = v₂ * a * v₁ := by group
    exact mul_mem (Subgroup.mem_sup_right (c.U2_le_U ⟨hv₂, hv₂T⟩)) (Subgroup.mem_sup_left hv₁)
  · exact fun v hv => ⟨hv.1, Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_iff.1 hv.2 a ha.2⟩
  · intro u hu
    exact ⟨c.hUY hu, Subgroup.mem_centralizer_iff.2 fun a ha =>
      Subgroup.mem_centralizer_iff.1 (c.U_le_centralizer hu) a ha.1⟩

theorem comm_X_V₁ : ⁅Λ ⊓ A, V₁ t Y Λ A⁆ = V₁ t Y Λ A := by
  obtain ⟨ψ⟩ := c.nonempty_equiv_X
  have hXV₁ := c.X_le_normalizer_V₁
  have hnc : ¬ (Λ ⊓ A) ≤ centralizer ((V₁ t Y Λ A : Subgroup G) : Set G) := by
    intro h
    have h1 : V₁ t Y Λ A ≤ centralizer ((Λ ⊓ A : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.1 h
    have h2 : V₁ t Y Λ A ≤ ⊥ := by
      rw [← c.fix_V₁]
      exact le_inf le_rfl h1
    have h3 := c.card_V.2
    rw [le_bot_iff.1 h2, Subgroup.card_bot] at h3
    have h4 := c.four_le
    nlinarith
  have hVA : ⁅Λ ⊓ A, V₁ t Y Λ A⁆ ≤ V₁ t Y Λ A := by
    rw [commutator_le]
    intro x hx v hv
    rw [commutatorElement_def]
    have h1 : x * v * x⁻¹ ∈ V₁ t Y Λ A := (mem_normalizer_iff.1 (hXV₁ hx) v).1 hv
    have h2 : v⁻¹ ∈ V₁ t Y Λ A := inv_mem hv
    exact mul_mem h1 h2
  have hXC : (Λ ⊓ A) ≤ normalizer ((⁅Λ ⊓ A, V₁ t Y Λ A⁆ : Subgroup G) : Set G) := by
    intro x hx
    apply mem_normalizer_of_conj_eq
    rw [conj_commutator, conj_eq_of_mem_normalizer (le_normalizer hx),
      conj_eq_of_mem_normalizer (hXV₁ hx)]
  have hcard : Nat.card (V₁ t Y Λ A) = 2 ^ (2 * f) := by
    rw [c.card_V.2, c.hK, ← pow_mul, mul_comm, pow_mul]
  rcases CFSG.LocalAnalysis.EvenBN.Common.sl2_eq_bot_or_eq_of_card_le (X := Λ ⊓ A)
    (A := V₁ t Y Λ A) (V₀ := ⁅Λ ⊓ A, V₁ t Y Λ A⁆) ψ c.hK c.hf
    (fun x hx y hy => c.hYab x hx.1 y hy.1) hcard le_rfl hXV₁ hXC hVA hnc with h | h
  · exfalso
    apply hnc
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, h]
  · exact h

theorem B4 : ⁅(Λ ⊓ A) ⊔ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t]), (Λ ⊓ A) ⊔ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t])⁆ =
    (Λ ⊓ A) ⊔ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t]) := by
  rw [c.zc_K3']
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    have h1 : a * b ∈ (Λ ⊓ A) ⊔ V₁ t Y Λ A := mul_mem ha hb
    have h2 : a⁻¹ ∈ (Λ ⊓ A) ⊔ V₁ t Y Λ A := inv_mem ha
    have h3 : b⁻¹ ∈ (Λ ⊓ A) ⊔ V₁ t Y Λ A := inv_mem hb
    exact mul_mem (mul_mem h1 h2) h3
  · calc Λ ⊓ A = ⁅Λ ⊓ A, Λ ⊓ A⁆ := c.X_perfect.symm
      _ ≤ _ := commutator_mono le_sup_left le_sup_left
  · calc V₁ t Y Λ A = ⁅Λ ⊓ A, V₁ t Y Λ A⁆ := c.comm_X_V₁.symm
      _ ≤ _ := commutator_mono le_sup_left le_sup_right

end Cfg

open CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule (actionFixed mem_actionFixed
  even_linear_two_half_fixed_module_transitivity diagTorus mem_diagTorus)
open CFSG.Timmesfeld.ARS.NaturalModule (weylElt diagElt weylElt_mul_diagElt weylElt_mul_self
  diagElt_mem_normalizer_upperUnipotent)

theorem exists_torus_conj {X A T : Subgroup G} {k : Type} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) (ψ : ↥X ≃* SL(2, k))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hXA : X ≤ normalizer (A : Set G))
    (hcard : Nat.card A = (2 ^ n) ^ 2) (hfix : A ⊓ centralizer (X : Set G) = ⊥)
    (hTX : T ≤ X) (hT : Nat.card T = Nat.card k)
    (hfixT : Nat.card (A ⊓ centralizer (T : Set G) : Subgroup G) = 2 ^ n) :
    ∀ a ∈ A, a ∉ centralizer (T : Set G) → ∀ b ∈ A, b ∉ centralizer (T : Set G) →
      ∃ x ∈ X ⊓ normalizer (T : Set G), x * a * x⁻¹ * b⁻¹ ∈ centralizer (T : Set G) := by
  classical
  set T₀ : Subgroup ↥X := T.subgroupOf X with hT₀
  have hT₀card : Nat.card (T₀.map ψ.toMonoidHom) = Nat.card k := by
    rw [Subgroup.card_map_of_injective ψ.injective, hT₀,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, hT]
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.EvenBN.Common.exists_conj_eq_upperUnipotent hk hT₀card
  set ψ' : ↥X ≃* SL(2, k) := ψ.trans (MulAut.conj g) with hψ'
  have hψ'T : ∀ x : ↥X, ψ' x ∈ CFSG.Timmesfeld.upperUnipotent k ↔ (x : G) ∈ T := by
    intro x
    rw [← hg, Subgroup.map_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := ψ'.injective hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  let ρ : SL(2, k) →* MulAut A :=
    (A.normalizerMonoidHom).comp ((Subgroup.inclusion hXA).comp ψ'.symm.toMonoidHom)
  have hρ : ∀ (s : SL(2, k)) (a : A), ((ρ s a : A) : G) =
      ((ψ'.symm s : X) : G) * a * ((ψ'.symm s : X) : G)⁻¹ := fun s a => rfl
  have hρ' : ∀ (x : X) (a : A), ((ρ (ψ' x) a : A) : G) = (x : G) * a * (x : G)⁻¹ := by
    intro x a
    rw [hρ, MulEquiv.symm_apply_apply]
  have hD : actionFixed ρ ⊤ = ⊥ := by
    refine eq_bot_iff.2 fun a ha => ?_
    have haC : (a : G) ∈ A ⊓ centralizer (X : Set G) := by
      refine ⟨a.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
      have e := congrArg Subtype.val (ha (ψ' ⟨x, hx⟩) (Subgroup.mem_top _))
      rw [hρ'] at e
      calc x * (a : G) = (x * a * x⁻¹) * x := by group
        _ = (a : G) * x := by rw [e]
    rw [hfix, Subgroup.mem_bot] at haC
    exact Subgroup.mem_bot.2 (Subtype.ext haC)
  have hfixmem : ∀ a : A, a ∈ actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k) ↔
      (a : G) ∈ centralizer (T : Set G) := by
    intro a
    rw [mem_actionFixed, Subgroup.mem_centralizer_iff]
    constructor
    · intro ha x hx
      have e := congrArg Subtype.val (ha (ψ' ⟨x, hTX hx⟩) ((hψ'T _).2 hx))
      rw [hρ'] at e
      calc x * (a : G) = (x * a * x⁻¹) * x := by group
        _ = (a : G) * x := by rw [e]
    · intro ha s hs
      obtain ⟨x, rfl⟩ := ψ'.surjective s
      apply Subtype.ext
      rw [hρ']
      have hc := ha x ((hψ'T x).1 hs)
      rw [hc, mul_inv_cancel_right]
  have hB : Nat.card (actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k)) = 2 ^ n := by
    rw [← hfixT]
    have e : (actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k)).map A.subtype =
        A ⊓ centralizer (T : Set G) := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, (hfixmem a).1 ha⟩
      · intro hy
        exact ⟨⟨y, hy.1⟩, (hfixmem ⟨y, hy.1⟩).2 hy.2, rfl⟩
    rw [← e, Subgroup.card_map_of_injective A.subtype_injective]
  obtain ⟨-, hcompl, htorusU, hreg, -, -, -⟩ :=
    even_linear_two_half_fixed_module_transitivity hk hcard ρ hD hB
  set U := actionFixed ρ (CFSG.Timmesfeld.upperUnipotent k) with hUdef
  have hdec : ∀ a : A, ∃ u ∈ U, ∃ y ∈ U, a = u * ρ (weylElt k)⁻¹ y := by
    intro a
    have ha : a ∈ U ⊔ U.map (ρ (weylElt k)⁻¹).toMonoidHom := hcompl.sup_eq_top ▸ Subgroup.mem_top a
    obtain ⟨u, hu, w, hw, huw⟩ := Subgroup.mem_sup.1 ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hw
    exact ⟨u, hu, y, hy, huw.symm⟩
  intro a haA ha b hbA hb
  let a' : A := ⟨a, haA⟩
  let b' : A := ⟨b, hbA⟩
  have ha' : a' ∉ U := fun h => ha ((hfixmem a').1 h)
  have hb' : b' ∉ U := fun h => hb ((hfixmem b').1 h)
  obtain ⟨u, hu, y, hy, hay⟩ := hdec a'
  obtain ⟨u', hu', y', hy', hby⟩ := hdec b'
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply ha'
    rw [hay, map_one, mul_one]
    exact hu
  have hy1' : y' ≠ 1 := by
    rintro rfl
    apply hb'
    rw [hby, map_one, mul_one]
    exact hu'
  obtain ⟨⟨τ₀, hτ₀⟩, hτ₀y, -⟩ := hreg y hy hy1 y' hy' hy1'
  obtain ⟨cu, rfl⟩ := mem_diagTorus.1 hτ₀
  have hτmem : diagElt cu⁻¹ ∈ diagTorus k := mem_diagTorus.2 ⟨cu⁻¹, rfl⟩
  set τ : SL(2, k) := diagElt cu⁻¹ with hτ
  have hid : ρ τ (ρ (weylElt k)⁻¹ y) = ρ (weylElt k)⁻¹ y' := by
    have h1 : ρ τ (ρ (weylElt k)⁻¹ y) = ρ (τ * (weylElt k)⁻¹) y := by rw [map_mul]; rfl
    have h2 : τ * (weylElt k)⁻¹ = (weylElt k)⁻¹ * diagElt cu := by
      rw [inv_eq_of_mul_eq_one_right (weylElt_mul_self (K := k))]
      exact (weylElt_mul_diagElt cu).symm
    rw [h1, h2, map_mul]
    show ρ (weylElt k)⁻¹ (ρ (diagElt cu) y) = _
    rw [show ρ (diagElt cu) y = y' from hτ₀y]
  refine ⟨((ψ'.symm τ : ↥X) : G), ⟨(ψ'.symm τ).2, ?_⟩, ?_⟩
  · show ((ψ'.symm τ : ↥X) : G) ∈ normalizer (T : Set G)
    rw [mem_normalizer_iff]
    have key : ∀ z : ↥X, (z : G) ∈ T ↔
        (((ψ'.symm τ * z * (ψ'.symm τ)⁻¹ : ↥X)) : G) ∈ T := by
      intro z
      rw [← hψ'T z, ← hψ'T (ψ'.symm τ * z * (ψ'.symm τ)⁻¹), map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
      exact mem_normalizer_iff.1 (diagElt_mem_normalizer_upperUnipotent cu⁻¹) (ψ' z)
    intro h
    constructor
    · intro hh
      have hhX : h ∈ X := hTX hh
      exact (key ⟨h, hhX⟩).1 hh
    · intro hh
      have hxh : (((ψ'.symm τ : ↥X) : G)) * h * (((ψ'.symm τ : ↥X) : G))⁻¹ ∈ X := hTX hh
      have hhX : h ∈ X := by
        have h1 : ((ψ'.symm τ : ↥X) : G)⁻¹ ∈ X := inv_mem (ψ'.symm τ).2
        have := mul_mem (mul_mem h1 hxh) (ψ'.symm τ).2
        simpa [mul_assoc] using this
      exact (key ⟨h, hhX⟩).2 hh
  · have hxe : ((ρ τ a' : A) : G) =
        ((ψ'.symm τ : ↥X) : G) * a * ((ψ'.symm τ : ↥X) : G)⁻¹ := hρ τ a'
    have hmem : (ρ τ a' * b'⁻¹ : A) ∈ U := by
      have hcalc : ρ τ a' * b'⁻¹ = ρ τ u * u'⁻¹ := by
        rw [hay, hby, map_mul, hid]
        group
      rw [hcalc]
      exact mul_mem (htorusU τ hτmem u hu) (inv_mem hu')
    have h2 := (hfixmem _).1 hmem
    simpa [hxe] using h2

theorem exists_third {V Cc : Subgroup G} (hCV : Cc ≤ V) (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hVsq : ∀ a ∈ V, a * a = 1) (hcard : 2 * Nat.card Cc < Nat.card V) {v : G} (hv : v ∈ V) :
    ∃ b ∈ V, b ∉ Cc ∧ b * v⁻¹ ∉ Cc := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ Cc ⊔ zpowers v := by
    intro b hb
    by_cases hbC : b ∈ Cc
    · exact Subgroup.mem_sup_left hbC
    · have h1 : b * v⁻¹ ∈ Cc := hcon b hb hbC
      have e : b = (b * v⁻¹) * v := by group
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right (mem_zpowers v))
  have hn : zpowers v ≤ normalizer (Cc : Set G) := by
    refine le_normalizer_of_commutator_mem fun x hx y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have hxV : v ^ k ∈ V := zpow_mem hv k
    rw [hVab _ hxV y (hCV hy)]
    group
    exact one_mem _
  have h1 := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq hn
  have h2 : Nat.card (zpowers v) ≤ 2 := by
    rw [Nat.card_zpowers]
    have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hVsq v hv)
    exact Nat.le_of_dvd (by norm_num) this
  have h3 : Nat.card V ≤ Nat.card (Cc ⊔ zpowers v : Subgroup G) := Subgroup.card_le_of_le hle
  have h4 : 0 < Nat.card (Cc ⊓ zpowers v : Subgroup G) := Nat.card_pos
  nlinarith

theorem claim_gen {W V Cc E : Subgroup G} {w v₂ v₁ : G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hVsq : ∀ a ∈ V, a * a = 1)
    (hCV : Cc ≤ V) (hCW : Cc ≤ W) (hcard : 2 * Nat.card Cc < Nat.card V)
    (hEV : ∀ x ∈ E, ∀ a ∈ V, x * a * x⁻¹ ∈ V) (hEW : ∀ x ∈ E, ∀ a ∈ W, x * a * x⁻¹ ∈ W)
    (hN : ∀ a ∈ V, a ∉ Cc → ∀ b ∈ V, b ∉ Cc → ∃ x ∈ E, x * a * x⁻¹ * b⁻¹ ∈ Cc)
    (hv₂ : ∀ x ∈ E, x * v₂ * x⁻¹ = v₂) (hv₂c : ∀ a ∈ V, v₂ * a = a * v₂)
    (hw : w ∈ W) (hwe : w = v₂ * v₁) (hv₁ : v₁ ∈ V) (hv₁C : v₁ ∉ Cc) : V ≤ W := by
  obtain ⟨b, hbV, hbC, hbv⟩ := exists_third hCV hVab hVsq hcard hv₁
  obtain ⟨x, hxE, hx⟩ := hN v₁ hv₁ hv₁C b hbV hbC
  have hu : x * v₁ * x⁻¹ ∈ V := hEV x hxE v₁ hv₁
  have hzV : x * v₁ * x⁻¹ * v₁⁻¹ ∈ V := by
    have h1 : v₁⁻¹ ∈ V := inv_mem hv₁
    exact mul_mem hu h1
  have hzW : x * v₁ * x⁻¹ * v₁⁻¹ ∈ W := by
    have h1 : x * w * x⁻¹ ∈ W := hEW x hxE w hw
    have h2 : x * w * x⁻¹ * w⁻¹ ∈ W := mul_mem h1 (inv_mem hw)
    have e : x * w * x⁻¹ * w⁻¹ = x * v₁ * x⁻¹ * v₁⁻¹ := by
      rw [hwe]
      have e1 : x * (v₂ * v₁) * x⁻¹ = v₂ * (x * v₁ * x⁻¹) := by
        calc x * (v₂ * v₁) * x⁻¹ = (x * v₂ * x⁻¹) * (x * v₁ * x⁻¹) := by group
          _ = v₂ * (x * v₁ * x⁻¹) := by rw [hv₂ x hxE]
      rw [e1]
      have hc : v₂ * (x * v₁ * x⁻¹ * v₁⁻¹) = (x * v₁ * x⁻¹ * v₁⁻¹) * v₂ := hv₂c _ hzV
      calc v₂ * (x * v₁ * x⁻¹) * (v₂ * v₁)⁻¹
          = v₂ * (x * v₁ * x⁻¹ * v₁⁻¹) * v₂⁻¹ := by group
        _ = ((x * v₁ * x⁻¹ * v₁⁻¹) * v₂) * v₂⁻¹ := by rw [hc]
        _ = x * v₁ * x⁻¹ * v₁⁻¹ := by group
    rw [← e]
    exact h2
  have hzC : x * v₁ * x⁻¹ * v₁⁻¹ ∉ Cc := by
    intro hzC
    apply hbv
    have h1 : (x * v₁ * x⁻¹ * b⁻¹)⁻¹ * (x * v₁ * x⁻¹ * v₁⁻¹) ∈ Cc := mul_mem (inv_mem hx) hzC
    have e : (x * v₁ * x⁻¹ * b⁻¹)⁻¹ * (x * v₁ * x⁻¹ * v₁⁻¹) = b * v₁⁻¹ := by group
    rwa [e] at h1
  intro a ha
  by_cases hac : a ∈ Cc
  · exact hCW hac
  · obtain ⟨x', hx'E, hx'⟩ := hN _ hzV hzC a ha hac
    have h1 : x' * (x * v₁ * x⁻¹ * v₁⁻¹) * x'⁻¹ ∈ W := hEW x' hx'E _ hzW
    have h2 : (x' * (x * v₁ * x⁻¹ * v₁⁻¹) * x'⁻¹ * a⁻¹)⁻¹ ∈ W := inv_mem (hCW hx')
    have e : (x' * (x * v₁ * x⁻¹ * v₁⁻¹) * x'⁻¹ * a⁻¹)⁻¹ *
        (x' * (x * v₁ * x⁻¹ * v₁⁻¹) * x'⁻¹) = a := by group
    rw [← e]
    exact mul_mem h2 h1

namespace Cfg

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {t s : G}
  {M Λ N A P Y U : Subgroup G} (c : Cfg K f t s M Λ N A P Y U)

include c

theorem two_mul_lt₁ : 2 * Nat.card (V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G) : Subgroup G) <
    Nat.card (V₁ t Y Λ A) := by
  rw [c.card_U_eq.1, c.card_V.2, c.hK]
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) c.hf
  nlinarith

theorem two_mul_lt₂ : 2 * Nat.card (V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G) : Subgroup G) <
    Nat.card (V₂ Y Λ A) := by
  rw [c.card_U_eq.2, c.card_V.1, c.hK]
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) c.hf
  nlinarith

theorem mem_normalizer_P_of_X {x : G} (hx : x ∈ Λ ⊓ A) (hxT : x ∈ normalizer (Tsub P Λ A : Set G)) :
    x ∈ N ⊓ normalizer (P : Set G) := by
  refine ⟨c.hAN hx.2, ?_⟩
  have h := mem_normalizer_sup (mem_normalizer_sup (c.hNM (c.hAN hx.2)) hxT)
    (c.X_le_normalizer_of_le_X' (inf_le_right : Tsub' t P Λ A ≤ Λᵍ[t] ⊓ A) hx)
  rwa [← c.P_eq] at h

theorem mem_normalizer_P_of_X' {x : G} (hx : x ∈ Λᵍ[t] ⊓ A)
    (hxT : x ∈ normalizer (Tsub' t P Λ A : Set G)) : x ∈ N ⊓ normalizer (P : Set G) := by
  refine ⟨c.hAN hx.2, ?_⟩
  have h := mem_normalizer_sup (mem_normalizer_sup (c.hNM (c.hAN hx.2))
    (c.X'_le_normalizer_of_le_X (inf_le_right : Tsub P Λ A ≤ Λ ⊓ A) hx)) hxT
  rwa [← c.P_eq] at h

theorem claim₁ {W : Subgroup G} (hUW : U ≤ W)
    (hinv : ∀ g ∈ N ⊓ normalizer (P : Set G), g ∈ normalizer (W : Set G))
    {w v₂ v₁ : G} (hw : w ∈ W) (hv₂ : v₂ ∈ V₂ Y Λ A) (hv₁ : v₁ ∈ V₁ t Y Λ A) (hwe : w = v₂ * v₁)
    (hv₁C : v₁ ∉ centralizer (Tsub P Λ A : Set G)) : V₁ t Y Λ A ≤ W := by
  obtain ⟨ψ⟩ := c.nonempty_equiv_X
  have hN := exists_torus_conj (X := Λ ⊓ A) (A := V₁ t Y Λ A) (T := Tsub P Λ A) c.hK ψ
    (fun a ha b hb => c.hYab a ha.1 b hb.1) c.X_le_normalizer_V₁
    (by rw [c.card_V.2, c.hK]) c.fix_V₁ inf_le_right c.card_T
    (by rw [c.card_U_eq.1])
  refine claim_gen (E := (Λ ⊓ A) ⊓ normalizer (Tsub P Λ A : Set G))
    (Cc := V₁ t Y Λ A ⊓ centralizer (Tsub P Λ A : Set G)) (v₂ := v₂)
    (fun a ha b hb => c.hYab a ha.1 b hb.1) (fun a ha => c.hYsq a ha.1) inf_le_left
    (c.U1_le_U.trans hUW) c.two_mul_lt₁
    (fun x hx a ha => (mem_normalizer_iff.1 (c.X_le_normalizer_V₁ hx.1) a).1 ha)
    (fun x hx a ha => (mem_normalizer_iff.1 (hinv x (c.mem_normalizer_P_of_X hx.1 hx.2)) a).1 ha)
    ?_ ?_ ?_ hw hwe hv₁ (fun h => hv₁C h.2)
  · intro a ha haC b hb hbC
    obtain ⟨x, hx, hxab⟩ := hN a ha (fun h => haC ⟨ha, h⟩) b hb (fun h => hbC ⟨hb, h⟩)
    refine ⟨x, hx, ?_, hxab⟩
    have h1 : x * a * x⁻¹ ∈ V₁ t Y Λ A := (mem_normalizer_iff.1 (c.X_le_normalizer_V₁ hx.1) a).1 ha
    have h2 : b⁻¹ ∈ V₁ t Y Λ A := inv_mem hb
    exact mul_mem h1 h2
  · intro x hx
    have := Subgroup.mem_centralizer_iff.1 hv₂.2 x hx.1
    rw [this]
    group
  · intro a ha
    exact c.hYab v₂ hv₂.1 a ha.1

theorem claim₂ {W : Subgroup G} (hUW : U ≤ W)
    (hinv : ∀ g ∈ N ⊓ normalizer (P : Set G), g ∈ normalizer (W : Set G))
    {w v₂ v₁ : G} (hw : w ∈ W) (hv₂ : v₂ ∈ V₂ Y Λ A) (hv₁ : v₁ ∈ V₁ t Y Λ A) (hwe : w = v₂ * v₁)
    (hv₂C : v₂ ∉ centralizer (Tsub' t P Λ A : Set G)) : V₂ Y Λ A ≤ W := by
  obtain ⟨ψ⟩ := c.nonempty_equiv_X'
  have hN := exists_torus_conj (X := Λᵍ[t] ⊓ A) (A := V₂ Y Λ A) (T := Tsub' t P Λ A) c.hK ψ
    (fun a ha b hb => c.hYab a ha.1 b hb.1) c.X'_le_normalizer_V₂
    (by rw [c.card_V.1, c.hK]) c.fix_V₂ inf_le_right c.card_T'
    (by rw [c.card_U_eq.2])
  have hwe' : w = v₁ * v₂ := by rw [hwe]; exact c.hYab v₂ hv₂.1 v₁ hv₁.1
  refine claim_gen (E := (Λᵍ[t] ⊓ A) ⊓ normalizer (Tsub' t P Λ A : Set G))
    (Cc := V₂ Y Λ A ⊓ centralizer (Tsub' t P Λ A : Set G)) (v₂ := v₁)
    (fun a ha b hb => c.hYab a ha.1 b hb.1) (fun a ha => c.hYsq a ha.1) inf_le_left
    (c.U2_le_U.trans hUW) c.two_mul_lt₂
    (fun x hx a ha => (mem_normalizer_iff.1 (c.X'_le_normalizer_V₂ hx.1) a).1 ha)
    (fun x hx a ha => (mem_normalizer_iff.1 (hinv x (c.mem_normalizer_P_of_X' hx.1 hx.2)) a).1 ha)
    ?_ ?_ ?_ hw hwe' hv₂ (fun h => hv₂C h.2)
  · intro a ha haC b hb hbC
    obtain ⟨x, hx, hxab⟩ := hN a ha (fun h => haC ⟨ha, h⟩) b hb (fun h => hbC ⟨hb, h⟩)
    refine ⟨x, hx, ?_, hxab⟩
    have h1 : x * a * x⁻¹ ∈ V₂ Y Λ A := (mem_normalizer_iff.1 (c.X'_le_normalizer_V₂ hx.1) a).1 ha
    have h2 : b⁻¹ ∈ V₂ Y Λ A := inv_mem hb
    exact mul_mem h1 h2
  · intro x hx
    have := Subgroup.mem_centralizer_iff.1 hv₁.2 x hx.1
    rw [this]
    group
  · intro a ha
    exact c.hYab v₁ hv₁.1 a ha.1

theorem C_classify {W : Subgroup G} (hUW : U ≤ W) (hWY : W ≤ Y)
    (hinv : ∀ g ∈ N ⊓ normalizer (P : Set G), g ∈ normalizer (W : Set G)) :
    W = U ∨ W = zc (P ⊓ (Λ ⊓ (A ⊔ Y))) ∨ W = zc ((P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[t]) ∨ W = Y := by
  have hzP : zc (P ⊓ (Λ ⊓ (A ⊔ Y))) = V₂ Y Λ A ⊔ U := by rw [c.B3, c.zc_K3]
  have hzP' : zc ((P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[t]) = V₁ t Y Λ A ⊔ U := by rw [c.B3', c.zc_K3']
  have hcomp : ∀ w ∈ W, ∃ v₂ ∈ V₂ Y Λ A, ∃ v₁ ∈ V₁ t Y Λ A, w = v₂ * v₁ :=
    fun w hw => c.decomp_Y (hWY hw)
  by_cases hA : V₁ t Y Λ A ≤ W
  · by_cases hB : V₂ Y Λ A ≤ W
    · right; right; right
      refine le_antisymm hWY ?_
      rw [← c.V_sup]
      exact sup_le hB hA
    · right; right; left
      rw [hzP']
      refine le_antisymm ?_ (sup_le hA hUW)
      intro w hw
      obtain ⟨v₂, hv₂, v₁, hv₁, rfl⟩ := hcomp w hw
      have hv₂C : v₂ ∈ centralizer (Tsub' t P Λ A : Set G) := by
        by_contra hnot
        exact hB (c.claim₂ hUW hinv hw hv₂ hv₁ rfl hnot)
      have hv₂U : v₂ ∈ U := c.U2_le_U ⟨hv₂, hv₂C⟩
      exact mul_mem (Subgroup.mem_sup_right hv₂U) (Subgroup.mem_sup_left hv₁)
  · by_cases hB : V₂ Y Λ A ≤ W
    · right; left
      rw [hzP]
      refine le_antisymm ?_ (sup_le hB hUW)
      intro w hw
      obtain ⟨v₂, hv₂, v₁, hv₁, rfl⟩ := hcomp w hw
      have hv₁C : v₁ ∈ centralizer (Tsub P Λ A : Set G) := by
        by_contra hnot
        exact hA (c.claim₁ hUW hinv hw hv₂ hv₁ rfl hnot)
      have hv₁U : v₁ ∈ U := c.U1_le_U ⟨hv₁, hv₁C⟩
      exact mul_mem (Subgroup.mem_sup_left hv₂) (Subgroup.mem_sup_right hv₁U)
    · left
      refine le_antisymm ?_ hUW
      intro w hw
      obtain ⟨v₂, hv₂, v₁, hv₁, rfl⟩ := hcomp w hw
      have hv₂C : v₂ ∈ centralizer (Tsub' t P Λ A : Set G) := by
        by_contra hnot
        exact hB (c.claim₂ hUW hinv hw hv₂ hv₁ rfl hnot)
      have hv₁C : v₁ ∈ centralizer (Tsub P Λ A : Set G) := by
        by_contra hnot
        exact hA (c.claim₁ hUW hinv hw hv₂ hv₁ rfl hnot)
      exact mul_mem (c.U2_le_U ⟨hv₂, hv₂C⟩) (c.U1_le_U ⟨hv₁, hv₁C⟩)

end Cfg

namespace Cfg

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} {t s : G}
  {M Λ N A P Y U : Subgroup G} (c : Cfg K f t s M Λ N A P Y U)

include c

theorem abstract_713 :
    ((P ⊓ (Λ ⊓ (A ⊔ Y))) ⊓ (P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[s] = Y ∧
      Λ ⊓ (A ⊔ Y) = (P ⊓ (Λ ⊓ (A ⊔ Y))) ⊔ (P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[s]) ∧
    (zc (Λ ⊓ (A ⊔ Y)) ⊔ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t]) = Y ∧
      zc (Λ ⊓ (A ⊔ Y)) ⊓ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t]) = ⊥ ∧
      zc (P ⊓ (Λ ⊓ (A ⊔ Y))) = zc (Λ ⊓ (A ⊔ Y)) ⊔ U ∧
      ⁅(Λ ⊓ A) ⊔ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t]), (Λ ⊓ A) ⊔ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t])⁆ =
        (Λ ⊓ A) ⊔ zc ((Λ ⊓ (A ⊔ Y))ᵍ[t])) ∧
    (∀ W : Subgroup G, U ≤ W → W ≤ Y →
      (∀ g ∈ N ⊓ normalizer (P : Set G), g ∈ normalizer (W : Set G)) →
      W = U ∨ W = zc (P ⊓ (Λ ⊓ (A ⊔ Y))) ∨ W = zc ((P ⊓ (Λ ⊓ (A ⊔ Y)))ᵍ[t]) ∨ W = Y) := by
  refine ⟨⟨c.P3_inf, c.K3_eq_sup⟩, ⟨?_, ?_, c.B3, c.B4⟩, fun W hUW hWY hinv =>
    c.C_classify hUW hWY hinv⟩
  · rw [c.zc_K3, c.zc_K3']
    exact c.V_sup
  · rw [c.zc_K3, c.zc_K3']
    exact c.V_inf

end Cfg

theorem mem_normalizer_commutator_self {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((⁅K, K⁆ : Subgroup G) : Set G) :=
  CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.mem_normalizer_commutator hg

theorem conj_centralizer_of_commute {S : Subgroup G} {t : G} (hS : ∀ j ∈ S, j * t = t * j) :
    (centralizer (S : Set G))ᵍ[t] = centralizer (S : Set G) := by
  ext x
  rw [mem_conj_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have hj' : ∀ j ∈ S, t * j * t⁻¹ = j := fun j hj => by rw [← hS j hj]; group
  constructor
  · intro hx j hj
    have h1 := hx j hj
    calc j * x = t⁻¹ * ((t * j * t⁻¹) * (t * x * t⁻¹)) * t := by group
      _ = t⁻¹ * (j * (t * x * t⁻¹)) * t := by rw [hj' j hj]
      _ = t⁻¹ * ((t * x * t⁻¹) * j) * t := by rw [h1]
      _ = t⁻¹ * ((t * x * t⁻¹) * (t * j * t⁻¹)) * t := by rw [hj' j hj]
      _ = x * j := by group
  · intro hx j hj
    have h1 := hx j hj
    calc j * (t * x * t⁻¹) = (t * j * t⁻¹) * (t * x * t⁻¹) := by rw [hj' j hj]
      _ = t * (j * x) * t⁻¹ := by group
      _ = t * (x * j) * t⁻¹ := by rw [h1]
      _ = (t * x * t⁻¹) * (t * j * t⁻¹) := by group
      _ = (t * x * t⁻¹) * j := by rw [hj' j hj]

end ProductN3Aux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]


namespace ProductN3Aux

theorem cfg (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₂ : Subgroup G}
    (hΛ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K) :
    CFSG.LocalAnalysis.EvenBN.G2.ProductN3Aux.Cfg K f t d.wb (yamadaM₆ d t) Λ₂ (yamadaN₂ d t)
      hp.Astar (yamadaP d t) (yamadaY₂ d t) (yamadaU₁ d t) := by
  obtain ⟨α, hex, -⟩ := hp.exact₂
  have hD := hQ.doubling
  have hK₂ : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
    (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
      (h.normalizer_L_inf_Y_le_yamadaM₆ hW d hK hQ)
  have hNM : yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) := yamadaN₂_le_normalizer d t hK₂
  have hY₂comm : ⁅yamadaM₆ d t, yamadaM₆ d t⁆ = yamadaY₂ d t := (h.yamada_5_55_1 hW d hK hQ).2.2
  have htM₆ : t ∈ normalizer (yamadaM₆ d t : Set G) := Q44.t_mem_normalizer_M₆ hW h d hK hQ
  exact
    { ht := h.t_mul_t
      hs2 := Q44.wb_mul_self h d hK
      hst := Q44.wb_mul_t h d
      hK := hK
      hf := h.two_le
      hMΛ := hΛ.X_le
      hΛN := hΛ.le
      hNM := hNM
      hsup := hΛ.sup
      hinf := hΛ.inf
      hcomm := hΛ.comm
      hquot := hΛ.quot
      hAN := hp.Astar_spec.le_cen.trans inf_le_left
      hAM := hp.Astar_spec.inf_eq
      hNA := hp.Astar_spec.sup_eq
      hAt := hp.Astar_spec.conj_eq
      hMt := conj_eq_of_mem_normalizer htM₆
      hsA := hp.Astar_spec.levi_le d.wb_mem_leviB
      hPN := hp.sylow₂
      hMP := h.yamadaM₆_le_yamadaP hW d hK hQ
      hPt := conj_eq_of_mem_normalizer (h.yamada_5_51 hW d hK hQ).1.2.1
      hPPs := (h.yamadaP_inf_map_conj_wb hW d hK hQ hp.sylow₂ hex).1
      hNPs := (h.yamadaP_inf_map_conj_wb hW d hK hQ hp.sylow₂ hex).2
      hYM := h.yamadaY₂_le_yamadaM₆ hW d hK hQ
      hYab := fun a ha b hb => h.yamadaY₂_mul_comm d hK hD ha hb
      hYsq := fun y hy => h.yamadaY₂_mul_self hW d hK hD hy
      hMY := fun m hm y hy =>
        (mem_centralizer_iff.1 (Q44.M₆_le_centralizer_Y₂ hW h d hK hQ hm) y hy).symm
      hNY := fun g hg => by
        rw [← hY₂comm]
        exact ProductN3Aux.mem_normalizer_commutator_self (hNM hg)
      hYt := conj_eq_of_mem_normalizer (by
        rw [← hY₂comm]
        exact ProductN3Aux.mem_normalizer_commutator_self htM₆)
      hUY := yamadaU₁_le_yamadaY₂ d t
      hUt := conj_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaU₁ d hK hD).1
      hZP := by
        rw [← map_upperCentralSeries_one]
        exact (h.yamada_5_57_1 hW d hK hQ).1
      hUs := (h.yamada_5_13_1 d hK hD).1.1
      hYU := rfl
      hfaith := (h.yamadaP_inf_centralizer_yamadaY₂ hW d hK hQ hex).1
      hZN := (h.yamadaN₂_centers hW d hK hQ hp.sylow₂ hex).2.2.2.2.2
      hcY := h.card_yamadaY₂ d hK hD
      hcU := hQ.doubling.yamada_5_10_1.2.2 }

end ProductN3Aux

theorem yamada_7_13 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) {Λ₂ : Subgroup G}
    (hΛ : IsFactor (yamadaM₆ d t) (yamadaN₂ d t) Λ₂ t K) :
    (yamadaP₃ d t Λ₂ ⊓ (yamadaP₃ d t Λ₂)ᵍ[d.wb] = yamadaY₂ d t ∧
      yamadaK₃ d t Λ₂ = yamadaP₃ d t Λ₂ ⊔ (yamadaP₃ d t Λ₂)ᵍ[d.wb]) ∧
    (zc (yamadaK₃ d t Λ₂) ⊔ zc ((yamadaK₃ d t Λ₂)ᵍ[t]) = yamadaY₂ d t ∧
      zc (yamadaK₃ d t Λ₂) ⊓ zc ((yamadaK₃ d t Λ₂)ᵍ[t]) = ⊥ ∧
      zc (yamadaP₃ d t Λ₂) = zc (yamadaK₃ d t Λ₂) ⊔ yamadaU₁ d t ∧
      ⁅leviFactor₂ hp.Astar Λ₂ ⊔ zc ((yamadaK₃ d t Λ₂)ᵍ[t]),
          leviFactor₂ hp.Astar Λ₂ ⊔ zc ((yamadaK₃ d t Λ₂)ᵍ[t])⁆ =
        leviFactor₂ hp.Astar Λ₂ ⊔ zc ((yamadaK₃ d t Λ₂)ᵍ[t])) ∧
    (∀ X : Subgroup G, yamadaU₁ d t ≤ X → X ≤ yamadaY₂ d t →
      (∀ g ∈ yamadaN₂ d t ⊓ normalizer (yamadaP d t : Set G), g ∈ normalizer (X : Set G)) →
      X = yamadaU₁ d t ∨ X = zc (yamadaP₃ d t Λ₂) ∨ X = zc ((yamadaP₃ d t Λ₂)ᵍ[t]) ∨
        X = yamadaY₂ d t) := by
  have c := ProductN3Aux.cfg hW h d hK hQ hp hΛ
  have hN₃ : yamadaN₃ d t = hp.Astar ⊔ yamadaY₂ d t :=
    hp.Astar_spec.yamadaN₃_eq c.hNM hp.inf₂
  unfold yamadaP₃ yamadaK₃ leviFactor₂
  rw [hN₃]
  exact c.abstract_713

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
