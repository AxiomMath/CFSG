module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyRank
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall)
open CFSG.ComponentClassification.PerfectAutomorphisms
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {G : Type} [Group G]

@[expose] def oqSub (p : ℕ) (J : Subgroup G) : Subgroup ↥(Subgroup.normalizer (J : Set G)) :=
  (GLAPPrimeCoreOf p J).subgroupOf _

instance oqSub_normal (p : ℕ) (J : Subgroup G) : (oqSub p J).Normal :=
  ⟨fun n hn g => by
    have h1 := Subgroup.mem_subgroupOf.1 hn
    have h2 := Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_glaPPrimeCoreOf p J g.2) (n : G)
    exact Subgroup.mem_subgroupOf.2 (by simpa using h2.1 h1)⟩

variable (p : ℕ) (J : Subgroup G)

abbrev WQ : Type := ↥(Subgroup.normalizer (J : Set G)) ⧸ oqSub p J

@[expose] def psiHom : PQuot p J →* WQ p J :=
  QuotientGroup.lift (GLAPPrimeCore p ↥J)
    ((QuotientGroup.mk' (oqSub p J)).comp (Subgroup.inclusion (Subgroup.le_normalizer (H := J))))
    (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem J.subtype hx))

theorem psiHom_mk (x : ↥J) :
    psiHom p J (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion (Subgroup.le_normalizer (H := J)) x) := rfl

theorem psiHom_injective : Function.Injective (psiHom p J) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker, psiHom_mk, QuotientGroup.eq_one_iff] at hq
  have h1 := Subgroup.mem_subgroupOf.1 hq
  obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_map).1 h1
  have : y = x := Subtype.ext hyx
  subst this
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact hy

theorem psiHom_barAut (γ : ↥(Subgroup.normalizer (J : Set G))) (q : PQuot p J) :
    psiHom p J (barAut p J γ q) =
      QuotientGroup.mk γ * psiHom p J q * (QuotientGroup.mk γ)⁻¹ := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [barAut_mk, psiHom_mk, psiHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

theorem card_le_of_normalizes_quotient {G : Type} [Group G] [Finite G] {B N : Subgroup G}
    (hB : GLAIsBmax 3 B) (O : Subgroup ↥N) [O.Normal] (hO : ¬ 3 ∣ Nat.card O)
    {E T : Subgroup (↥N ⧸ O)} (hE : IsElemAbelian 3 E) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set (↥N ⧸ O))) : Nat.card E ≤ Nat.card B := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hEp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank 3 E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hk
  have h2 := pRank_le_glaTwoLocalRank_of_normalizes hp hT hT2 hET
  have h3 := glaTwoLocalRank_quotient_le hp (by norm_num) O hO
  have h4 := glaTwoLocalRank_subgroup_le hp N
  rw [hk, hB.2.1]
  exact Nat.pow_le_pow_right (by norm_num) (h1.trans (h2.trans (h3.trans h4)))


theorem card_comap_eq {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K) (L : Subgroup K)
    (hL : L ≤ f.range) : Nat.card (L.comap f) = Nat.card L * Nat.card f.ker := by
  let g : ↥(L.comap f) →* ↥L := (f.comp (L.comap f).subtype).codRestrict L fun x => x.2
  have hrange : g.range = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨h, hh⟩ := hL y.2
    exact ⟨⟨h, by rw [Subgroup.mem_comap, hh]; exact y.2⟩, Subtype.ext hh⟩
  have hker : g.ker = f.ker.subgroupOf (L.comap f) := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, g]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hsplit : Nat.card ↥(L.comap f) = Nat.card g.range * Nat.card g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
  rw [hsplit, hker, hrange, Subgroup.card_top]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => by
    rw [Subgroup.mem_comap]; rw [MonoidHom.mem_ker] at hx; rw [hx]; exact L.one_mem)).toEquiv

private theorem glaPPrimeCoreOf_le_self (p : ℕ) (J : Subgroup G) : GLAPPrimeCoreOf p J ≤ J := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem card_oqSub (p : ℕ) (J : Subgroup G) : Nat.card (oqSub p J) = Nat.card (GLAPPrimeCoreOf p J) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    ((glaPPrimeCoreOf_le_self p J).trans Subgroup.le_normalizer)).toEquiv

theorem not_dvd_card_oqSub [Finite G] (J : Subgroup G) : ¬ 3 ∣ Nat.card (oqSub 3 J) := by
  rw [card_oqSub]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (i183_coprime_card_glaPPrimeCoreOf Nat.prime_three J)

theorem card_eq_range_mul_ker {H K : Type*} [Group H] [Group K] [Finite H] (f : H →* K) :
    Nat.card H = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

theorem card_mul_le_card_actImage [Finite G] {B J : Subgroup G}
    (hB : GLAIsBmax 3 B) (hBJ : B ≤ Subgroup.normalizer (J : Set G))
    (hZ : Subgroup.center (PQuot 3 J) = ⊥) (hcen : Subgroup.center (PSimple 3 J) = ⊥)
    (F : Subgroup (PSimple 3 J)) (z : PSimple 3 J) (X₁ : Subgroup (MulAut (PSimple 3 J)))
    (hX₁ : X₁ ≤ actImage 3 J B) (hX₁I : X₁ ⊓ Inn (PSimple 3 J) = ⊥) (hF : IsElemAbelian 3 F)
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hFz : ∀ s ∈ F, s * z = z * s)
    (hX₁z : ∀ a ∈ X₁, a z = z) (hX₁F : ∀ a ∈ X₁, ∀ s ∈ F, a s = s) :
    Nat.card F * Nat.card X₁ ≤ Nat.card (actImage 3 J B) := by
  classical
  set N := Subgroup.normalizer (J : Set G) with hN
  set φ : ↥N →* MulAut (PSimple 3 J) := actHom 3 J with hφ
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  let σ : PSimple 3 J →* WQ 3 J := QuotientGroup.lift (Subgroup.center (PQuot 3 J)) (psiHom 3 J)
    (fun x hx => by rw [hZ, Subgroup.mem_bot] at hx; subst hx; exact map_one _)
  have hσmk : ∀ q, σ (QuotientGroup.mk q) = psiHom 3 J q := fun q => rfl
  have hσinj : Function.Injective σ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    rw [MonoidHom.mem_ker, hσmk] at hs
    have : q = 1 := psiHom_injective 3 J (hs.trans (map_one _).symm)
    rw [this]
    exact (Subgroup.mem_bot).2 (QuotientGroup.mk_one _)
  have hcompat : ∀ (γ : ↥N) (s : PSimple 3 J),
      σ (φ γ s) = QuotientGroup.mk γ * σ s * (QuotientGroup.mk γ)⁻¹ := by
    intro γ s
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    have h1 : φ γ (QuotientGroup.mk q) = QuotientGroup.mk (barAut 3 J γ q) :=
      onCenterQuotient_apply_mk (barAut 3 J γ) q
    rw [h1, hσmk, hσmk, psiHom_barAut]
  let f : ↥B' →* MulAut (PSimple 3 J) := φ.comp B'.subtype
  let β : ↥B' →* WQ 3 J := (QuotientGroup.mk' (oqSub 3 J)).comp B'.subtype
  have hBab : ∀ x y : ↥B', x * y = y * x := fun x y =>
    Subtype.ext (Subtype.ext (isElemAbelian_commute hB.1 (Subgroup.mem_subgroupOf.1 x.2)
      (Subgroup.mem_subgroupOf.1 y.2)))
  have hB3 : ∀ x : ↥B', x ^ 3 = 1 := fun x =>
    Subtype.ext (Subtype.ext (hB.1.2 _ (Subgroup.mem_subgroupOf.1 x.2)))
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have h1 : ((b : ↥N) : G) ∈ GLAPPrimeCoreOf 3 J :=
      Subgroup.mem_subgroupOf.1
        ((QuotientGroup.eq_one_iff (N := oqSub 3 J) ((b : ↥B') : ↥N)).1 hb)
    have h2 : ((b : ↥N) : G) ^ 3 = 1 := hB.1.2 _ (Subgroup.mem_subgroupOf.1 b.2)
    let o : ↥(GLAPPrimeCoreOf 3 J) := ⟨_, h1⟩
    have h3 : orderOf o ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext h2)
    have h4 : orderOf o ∣ Nat.card (GLAPPrimeCoreOf 3 J) := orderOf_dvd_natCard o
    have h5 : orderOf o = 1 := Nat.eq_one_of_dvd_coprimes
      (i183_coprime_card_glaPPrimeCoreOf (G := G) Nat.prime_three J) h3 h4
    have h6 : o = 1 := orderOf_eq_one_iff.1 h5
    have h7 : ((b : ↥N) : G) = 1 := congrArg Subtype.val h6
    exact (Subgroup.mem_bot).2 (Subtype.ext (Subtype.ext h7))
  have hrange : f.range = actImage 3 J B := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  set B₁ : Subgroup ↥B' := X₁.comap f with hB₁
  have hcomm : ∀ (s : ↥F) (b : ↥B₁),
      Commute ((σ.comp F.subtype) s) ((β.comp B₁.subtype) b) := by
    intro s b
    have hb : f (b : ↥B') ∈ X₁ := b.2
    have h1 := hcompat ((b : ↥B') : ↥N) (s : PSimple 3 J)
    have h2 : φ ((b : ↥B') : ↥N) (s : PSimple 3 J) = (s : PSimple 3 J) :=
      hX₁F _ hb _ s.2
    rw [h2] at h1
    show σ (s : PSimple 3 J) * β (b : ↥B') = β (b : ↥B') * σ (s : PSimple 3 J)
    change σ (s : PSimple 3 J) = QuotientGroup.mk ((b : ↥B') : ↥N) * σ (s : PSimple 3 J) *
      (QuotientGroup.mk ((b : ↥B') : ↥N))⁻¹ at h1
    have h3 : σ (s : PSimple 3 J) * QuotientGroup.mk ((b : ↥B') : ↥N) =
        QuotientGroup.mk ((b : ↥B') : ↥N) * σ (s : PSimple 3 J) := by
      rw [eq_mul_inv_iff_mul_eq] at h1
      exact h1
    exact h3
  let μ : ↥F × ↥B₁ →* WQ 3 J :=
    MonoidHom.noncommCoprod (σ.comp F.subtype) (β.comp B₁.subtype) hcomm
  have hμ : ∀ (s : ↥F) (b : ↥B₁), μ (s, b) = σ (s : PSimple 3 J) * β ((b : ↥B') : ↥B') := fun s b =>
    MonoidHom.noncommCoprod_apply _ _ _ _
  have hμinj : Function.Injective μ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨s, b⟩ hu
    rw [MonoidHom.mem_ker, hμ] at hu
    have hb : f (b : ↥B') ∈ X₁ := b.2
    have h1 : QuotientGroup.mk ((b : ↥B') : ↥N) = (σ (s : PSimple 3 J))⁻¹ := by
      change β (b : ↥B') = _
      exact eq_inv_of_mul_eq_one_right hu
    have h2 : ∀ t : PSimple 3 J, φ ((b : ↥B') : ↥N) t = (s : PSimple 3 J)⁻¹ * t * (s : PSimple 3 J) := by
      intro t
      apply hσinj
      rw [hcompat, h1, map_mul, map_mul, map_inv, inv_inv]
    have h3 : φ ((b : ↥B') : ↥N) = MulAut.conj ((s : PSimple 3 J)⁻¹) := by
      ext t
      rw [h2, MulAut.conj_apply, inv_inv]
    have h4 : φ ((b : ↥B') : ↥N) ∈ X₁ ⊓ Inn (PSimple 3 J) :=
      ⟨hb, ⟨(s : PSimple 3 J)⁻¹, h3.symm⟩⟩
    rw [hX₁I, Subgroup.mem_bot] at h4
    rw [h4] at h3
    have h5 : (s : PSimple 3 J) ∈ Subgroup.center (PSimple 3 J) := by
      rw [Subgroup.mem_center_iff]
      intro t
      have := congrArg (fun a : MulAut (PSimple 3 J) => a t) h3
      simp only [MulAut.one_apply, MulAut.conj_apply, inv_inv] at this
      calc t * (s : PSimple 3 J) = (s : PSimple 3 J) * (s : PSimple 3 J)⁻¹ * t * (s : PSimple 3 J) := by group
        _ = (s : PSimple 3 J) * ((s : PSimple 3 J)⁻¹ * t * (s : PSimple 3 J)) := by group
        _ = (s : PSimple 3 J) * t := by rw [← this]
    rw [hcen, Subgroup.mem_bot] at h5
    have h6 : s = 1 := Subtype.ext h5
    rw [h5, map_one, inv_one] at h1
    have h7 : (b : ↥B') = 1 := hβinj (h1.trans (map_one β).symm)
    exact (Subgroup.mem_bot).2 (Prod.ext h6 (Subtype.ext h7))
  have hĒ : IsElemAbelian 3 μ.range := by
    refine isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext (hBab _ _))
      exact isElemAbelian_commute hF u.1.2 v.1.2
    · rintro _ ⟨u, rfl⟩
      rw [← map_pow]
      have h1 : u ^ 3 = 1 := by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext (hB3 _))
        exact hF.2 _ u.1.2
      rw [h1, map_one]
  have hcardĒ : Nat.card μ.range = Nat.card F * Nat.card B₁ := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (MonoidHom.ofInjective hμinj).toEquiv).symm
  have hσz : ∀ e ∈ μ.range, e * σ z = σ z * e := by
    rintro _ ⟨⟨s, b⟩, rfl⟩
    rw [hμ]
    have hb : f (b : ↥B') ∈ X₁ := b.2
    have h1 : σ (s : PSimple 3 J) * σ z = σ z * σ (s : PSimple 3 J) := by
      rw [← map_mul, ← map_mul, hFz _ s.2]
    have h2 := hcompat ((b : ↥B') : ↥N) z
    have hz' : φ ((b : ↥B') : ↥N) z = z := hX₁z _ hb
    rw [hz'] at h2
    change σ z = QuotientGroup.mk ((b : ↥B') : ↥N) * σ z * (QuotientGroup.mk ((b : ↥B') : ↥N))⁻¹
      at h2
    rw [eq_mul_inv_iff_mul_eq] at h2
    change σ (s : PSimple 3 J) * QuotientGroup.mk ((b : ↥B') : ↥N) * σ z =
      σ z * (σ (s : PSimple 3 J) * QuotientGroup.mk ((b : ↥B') : ↥N))
    calc σ (s : PSimple 3 J) * QuotientGroup.mk ((b : ↥B') : ↥N) * σ z
        = σ (s : PSimple 3 J) * (σ z * QuotientGroup.mk ((b : ↥B') : ↥N)) := by rw [mul_assoc, h2]
      _ = σ (s : PSimple 3 J) * σ z * QuotientGroup.mk ((b : ↥B') : ↥N) := by rw [← mul_assoc]
      _ = σ z * σ (s : PSimple 3 J) * QuotientGroup.mk ((b : ↥B') : ↥N) := by rw [h1]
      _ = σ z * (σ (s : PSimple 3 J) * QuotientGroup.mk ((b : ↥B') : ↥N)) := by rw [mul_assoc]
  have hT : Subgroup.zpowers (σ z) ≠ ⊥ := by
    intro h
    have : σ z = 1 := by
      have := Subgroup.mem_zpowers (σ z)
      rw [h, Subgroup.mem_bot] at this
      exact this
    exact hz1 (hσinj (this.trans (map_one σ).symm))
  have hT2 : IsPGroup 2 (Subgroup.zpowers (σ z)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hz2, map_one])
  have hET : μ.range ≤ Subgroup.normalizer (Subgroup.zpowers (σ z) : Set (WQ 3 J)) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have h1 : e * σ z ^ n = σ z ^ n * e := (Commute.zpow_right (show Commute e (σ z) from hσz e he) n).eq
    rw [h1, mul_inv_cancel_right]
    exact hk
  have hle := card_le_of_normalizes_quotient hB (oqSub 3 J) (not_dvd_card_oqSub J) hĒ hT hT2 hET
  have hB'card : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv
  have hX₁r : X₁ ≤ f.range := hrange ▸ hX₁
  have hc1 : Nat.card B₁ = Nat.card X₁ * Nat.card f.ker := card_comap_eq f X₁ hX₁r
  have hc2 : Nat.card ↥B' = Nat.card f.range * Nat.card f.ker := card_eq_range_mul_ker f
  have hkpos : 0 < Nat.card f.ker := Nat.card_pos
  rw [hcardĒ, hc1, ← hB'card, hc2, hrange] at hle
  have : Nat.card F * Nat.card X₁ * Nat.card f.ker ≤ Nat.card (actImage 3 J B) * Nat.card f.ker := by
    calc Nat.card F * Nat.card X₁ * Nat.card f.ker = Nat.card F * (Nat.card X₁ * Nat.card f.ker) := by
          rw [mul_assoc]
      _ ≤ _ := hle
  exact Nat.le_of_mul_le_mul_right this hkpos

theorem isElemAbelian_map_equiv {A B : Type} [Group A] [Group B] {p : ℕ} (f : A ≃* B)
    {E : Subgroup A} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f.toMonoidHom) := by
  refine isElemAbelian_of_forall ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change f x * f y = f y * f x
    rw [← map_mul, ← map_mul, isElemAbelian_commute hE hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    change f x ^ p = 1
    rw [← map_pow, hE.2 x hx, map_one]

end CFSG.LocalAnalysis.GLTheoremA
