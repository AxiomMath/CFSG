module

import CFSG.Walter.Bender1970.S3.Basic
import CFSG.Walter.Bender1970.S2.Layer
import CFSG.Walter.Bender1970.S2.PGroup
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.Goldschmidt.Steps.Components
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.Walter.Bender1970.S3.Setup

public section

namespace CFSG.Goldschmidt.G75

open CFSG.Open

section Components

theorem not_le_oddCore {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK : CFSG.IsComponent K) : ¬ K ≤ goldschmidtOddCore X := by
  intro hle
  have hodd : Odd (Nat.card (goldschmidtOddCore X)) :=
    CFSG.ComponentClassification.OddCore.odd_card X
  have hq : CFSG.Open.IsQuasisimple K := ((CFSG.isComponent_iff_open K).1 hK).2.2
  have h2 := LemmaX.two_dvd_card_of_isQuasisimple hq
  have hdvd : Nat.card K ∣ Nat.card (goldschmidtOddCore X) :=
    Subgroup.card_dvd_of_le hle
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h2.trans hdvd))

theorem commutator_self_of_isComponent {Q : Type*} [Group Q] {L : Subgroup Q}
    (hL : CFSG.IsComponent L) : ⁅L, L⁆ = L := by
  have hperf : commutator L = ⊤ := hL.1.1.commutator_eq_top
  rw [← Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem ne_bot_of_isComponent {Q : Type*} [Group Q] {L : Subgroup Q}
    (hL : CFSG.IsComponent L) : L ≠ ⊥ := by
  intro h
  obtain ⟨a, b, hab⟩ := hL.1.2.2
  apply hab
  have : Subsingleton (L ⧸ Subgroup.center L) := by
    have : Subsingleton L := by
      rw [h]; infer_instance
    infer_instance
  exact Subsingleton.elim _ _

theorem normal_of_isComponent {X : Type} [Group X] [Finite X]
    (hE : CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X) ⊔
      goldschmidtLayer (X ⧸ goldschmidtOddCore X) = ⊤)
    (hZ : CFSG.Open.pCore 2 (X ⧸ goldschmidtOddCore X) ≤
      Subgroup.center (X ⧸ goldschmidtOddCore X))
    {K : Subgroup X} (hK : CFSG.IsComponent K) : K.Normal := by
  set π := QuotientGroup.mk' (goldschmidtOddCore X) with hπ
  have hKb : CFSG.IsComponent (K.map π) :=
    CFSG.LocalAnalysis.ComponentInitial.component_quotient_image hK (not_le_oddCore hK)
  have hKb' : IsComponentOf (K.map π) ⊤ := (CFSG.isComponent_iff_open _).1 hKb
  have hN : ⊤ ≤ Subgroup.normalizer
      ((K.map π : Subgroup _) : Set (X ⧸ goldschmidtOddCore X)) := by
    rw [← hE]
    refine sup_le (hZ.trans (Subgroup.center_le_normalizer _)) (sSup_le fun L hL => ?_)
    by_cases hLK : L = K.map π
    · rw [hLK]; exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (N8b _ L _ hL hKb' hLK)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hmapK : ∀ x : X, (K.map (MulAut.conj x).toMonoidHom).map π = K.map π := by
    intro x
    have hx := hN (Subgroup.mem_top (π x))
    rw [Subgroup.map_map]
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hx (π k)).1 ⟨k, hk, rfl⟩
      simpa [MulAut.conj_apply, hπ] using this
    · intro hz
      obtain ⟨k, hk, rfl⟩ := hz
      have hx' := (Subgroup.normalizer _).inv_mem hx
      have := (Subgroup.mem_normalizer_iff.1 hx' (π k)).1 ⟨k, hk, rfl⟩
      obtain ⟨k', hk', hk'eq⟩ := this
      refine ⟨k', hk', ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv, hk'eq]
      group
  constructor
  intro k hk x
  by_contra hne
  have hK' : CFSG.IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj x) hK
  rcases CFSG.LocalCores.distinct_components_commute hK hK' with heq | hcomm
  · apply hne
    rw [heq]
    exact ⟨k, hk, rfl⟩
  · have h1 : ⁅K.map π, K.map π⁆ = ⊥ := by
      have := congrArg (Subgroup.map π) hcomm
      rwa [Subgroup.map_commutator, Subgroup.map_bot, hmapK x] at this
    rw [commutator_self_of_isComponent hKb] at h1
    exact ne_bot_of_isComponent hKb h1

end Components

variable {G : Type} [Group G] [Finite G]

section NormalClosure

omit [Finite G] in
theorem le_normalClosureIn {H A : Subgroup G} (hAH : A ≤ H) : A ≤ normalClosureIn H A := by
  intro a ha
  exact ⟨⟨a, hAH ha⟩, Subgroup.subset_normalClosure (by simpa [Subgroup.mem_subgroupOf] using ha),
    rfl⟩

omit [Finite G] in
theorem normalClosureIn_le (H A : Subgroup G) : normalClosureIn H A ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [Finite G] in
theorem le_normalizer_normalClosureIn (H A : Subgroup G) :
    H ≤ Subgroup.normalizer (normalClosureIn H A : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hN := Subgroup.normalClosure_normal (s := ((A.subgroupOf H : Subgroup H) : Set H))
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hN.conj_mem y hy ⟨h, hh⟩, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨h, hh⟩⁻¹ * y * ⟨h, hh⟩, ?_, ?_⟩
    · simpa using hN.conj_mem y hy ⟨h, hh⟩⁻¹
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
      rw [hyx]
      group

theorem normalClosureIn_le_normalizer {H A K : Subgroup G} (hS : IsSStarIn H A)
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A)) :
    normalClosureIn H A ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨_, _, _, _, _, _, hE, hZ, _, _⟩ := hS
  have hK' := CFSG.Walter.isComponent_subgroupOf_of_isComponentOf hK
  have hn := normal_of_isComponent hE hZ hK'
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hK.1).mp hn

theorem le_normalizer_of_isComponentOf {H A K : Subgroup G} (hS : IsSStarIn H A)
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A)) :
    A ≤ Subgroup.normalizer (K : Set G) :=
  (le_normalClosureIn hS.1).trans (normalClosureIn_le_normalizer hS hK)

end NormalClosure

section Setting

variable {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem le_centralizer_of_mem {A : Subgroup G} (hA : IsElemAbelian 2 A) {a : G} (ha : a ∈ A) :
    A ≤ Subgroup.centralizer ({a} : Set G) := fun b hb => by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)

theorem isSStarIn_of_mem_benderM (hset : GoldSetting G S A) {a : G} (ha : a ∈ A)
    {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) : IsSStarIn H A := by
  have hAH : A ≤ H := (le_centralizer_of_mem hset.elem ha).trans hH.2.1
  obtain ⟨g, hle, hS⟩ := hset.sstar H hH.1.1
  rw [inf_of_le_left hAH] at hle
  have hAg : A = conjSub g A := Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])
  rw [← hAg, inf_of_le_left hAH] at hS
  exact hS

theorem le_of_mem_benderM (hset : GoldSetting G S A) {a : G} (ha : a ∈ A)
    {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) : A ≤ H :=
  (le_centralizer_of_mem hset.elem ha).trans hH.2.1

theorem mem_of_mem_normalizer (hset : GoldSetting G S A) {a : G} (ha1 : a ≠ 1)
    {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : g ∈ H := by
  have hs := hset.isSimpleGroup
  by_cases hle : Subgroup.normalizer (H : Set G) ≤ H
  · exact hle hg
  · exfalso
    have hlt : H < Subgroup.normalizer (H : Set G) :=
      lt_of_le_of_ne Subgroup.le_normalizer (fun h => hle (h ▸ le_refl _))
    have htop := hH.1.2 _ hlt
    have hn : H.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hn.eq_bot_or_eq_top with h | h
    · have := CFSG.Walter.mem_of_mem_benderM hH
      rw [h, Subgroup.mem_bot] at this
      exact ha1 this
    · exact hH.1.1 h

theorem mem_of_benderM_eq (hset : GoldSetting G S A) {b : G} (hb1 : b ≠ 1) {H : Subgroup G}
    (hb : CFSG.Walter.benderM b = {H}) {g : G}
    (hg : CFSG.Walter.benderM (g * b * g⁻¹) = {H}) : g ∈ H := by
  have h1 := CFSG.Walter.benderM_conj_eq_singleton g hb
  rw [hg, Set.singleton_eq_singleton_iff] at h1
  have hH : H ∈ CFSG.Walter.benderM b := by rw [hb]; rfl
  refine mem_of_mem_normalizer hset hb1 hH ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : g * h * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := ⟨h, hh, rfl⟩
    rwa [← h1] at this
  · intro hh
    rw [h1] at hh
    obtain ⟨h', hh', hh'eq⟩ := hh
    have : h' = h := by
      have := hh'eq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      simpa using this
    rwa [← this]

end Setting

section Coprime

variable {A : Subgroup G}

omit [Finite G] in
theorem commutator_zpowers_le_self {y : G} (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    ⁅A, Subgroup.zpowers y⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro a ha z hz
  have hzN : z ∈ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hy hz
  rw [commutatorElement_def]
  have : z * a⁻¹ * z⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hzN _).1 (A.inv_mem ha)
  simpa [mul_assoc] using A.mul_mem ha this

omit [Finite G] in
theorem commutator_zpowers_le_of_mem {K : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    {y : G} (hyK : y ∈ K) : ⁅A, Subgroup.zpowers y⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha z hz
  have hzK : z ∈ K := Subgroup.zpowers_le.mpr hyK hz
  rw [commutatorElement_def]
  have : a * z * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hAK ha) z).1 hzK
  exact K.mul_mem this (K.inv_mem hzK)

omit [Finite G] in
theorem isPGroup_of_isElemAbelian (hA : IsElemAbelian 2 A) : IsPGroup 2 A :=
  CFSG.Open.IsElemAbelian.isPGroup hA

theorem coprime_decomp (hA : IsElemAbelian 2 A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (hodd : Odd (orderOf y)) :
    A ⊓ Subgroup.centralizer ({y} : Set G) ⊔ ⁅A, Subgroup.zpowers y⁆ = A ∧
      Disjoint (A ⊓ Subgroup.centralizer ({y} : Set G)) ⁅A, Subgroup.zpowers y⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  have hcop : (Nat.card (Subgroup.zpowers y)).Coprime (Nat.card A) := by
    rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have h := CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp A (Subgroup.zpowers y)
    (Subgroup.zpowers_le.mpr hy) (fun x z => hA.1.is_comm.comm x z) hcop
  rwa [CFSG.Walter.centralizer_zpowers_eq'] at h

theorem commutator_inf_centralizer_eq_bot (hA : IsElemAbelian 2 A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (hodd : Odd (orderOf y)) :
    ⁅A, Subgroup.zpowers y⁆ ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
  have hd := (coprime_decomp hA hy hodd).2
  rw [disjoint_iff] at hd
  rw [eq_bot_iff, ← hd]
  exact le_inf (le_inf (inf_le_left.trans (commutator_zpowers_le_self hy)) inf_le_right)
    inf_le_left

omit [Finite G] in
theorem inf_centralizer_le_of_mem {K : Subgroup G} {y : G} (hyK : y ∈ K) :
    A ⊓ Subgroup.centralizer (K : Set G) ≤ A ⊓ Subgroup.centralizer ({y} : Set G) :=
  inf_le_inf_left _ (Subgroup.centralizer_le (by simpa using hyK))

theorem eq_sup_inf_centralizer (hA : IsElemAbelian 2 A) {K : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {y : G} (hyK : y ∈ K)
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (hodd : Odd (orderOf y))
    (hC : A ⊓ Subgroup.centralizer ({y} : Set G) = A ⊓ Subgroup.centralizer (K : Set G)) :
    A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G) = A := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have h := (coprime_decomp hA hy hodd).1
  rw [hC] at h
  calc A = A ⊓ Subgroup.centralizer (K : Set G) ⊔ ⁅A, Subgroup.zpowers y⁆ := h.symm
    _ ≤ A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G) :=
      sup_le le_sup_right (le_sup_of_le_left (le_inf (commutator_zpowers_le_self hy)
        (commutator_zpowers_le_of_mem hAK hyK)))

end Coprime

section TI

variable {A : Subgroup G}

omit [Finite G] in
theorem conjSub_centralizer (x : G) (K : Subgroup G) :
    conjSub x (Subgroup.centralizer (K : Set G)) =
      Subgroup.centralizer ((conjSub x K : Subgroup G) : Set G) := by
  unfold conjSub
  rw [CFSG.Walter.map_centralizer_mulEquiv]
  rfl

omit [Finite G] in
theorem conjSub_eq_of_mem_normalizer {x : G} (hx : x ∈ Subgroup.normalizer (A : Set G)) :
    conjSub x A = A := by
  ext z
  rw [mem_conjSub]
  exact ((Subgroup.mem_normalizer_iff.1 hx z).symm)

omit [Finite G] in
theorem conjSub_inf_centralizer {x : G} (hx : x ∈ Subgroup.normalizer (A : Set G))
    (K : Subgroup G) :
    conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) =
      A ⊓ Subgroup.centralizer ((conjSub x K : Subgroup G) : Set G) := by
  unfold conjSub
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x⁻¹).injective]
  have h1 := conjSub_eq_of_mem_normalizer hx
  have h2 := conjSub_centralizer x K
  unfold conjSub at h1 h2
  rw [h1, h2]

omit [Finite G] in
theorem conjSub_inf {x : G} (hx : x ∈ Subgroup.normalizer (A : Set G)) (K : Subgroup G) :
    conjSub x (A ⊓ K) = A ⊓ conjSub x K := by
  unfold conjSub
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x⁻¹).injective]
  have h1 := conjSub_eq_of_mem_normalizer hx
  unfold conjSub at h1
  rw [h1]

theorem inf_conjSub_eq_bot_of_ne {H K : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A))
    (hsup : A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G) = A)
    (hcard : Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ^ 2 ≤ Nat.card A)
    (hAab : IsMulCommutative A) {x : G} (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxH : x ∈ H) (hKK' : conjSub x K ≠ K) :
    A ⊓ Subgroup.centralizer (K : Set G) ⊓
      conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
  set W := A ⊓ Subgroup.centralizer (K : Set G) with hW
  set K' := conjSub x K with hK'def
  have hxN : x⁻¹ ∈ Subgroup.normalizer (normalClosureIn H A : Set G) :=
    le_normalizer_normalClosureIn H A (H.inv_mem hxH)
  have hK' : GorensteinWalter.IsComponentOf K' (normalClosureIn H A) :=
    CFSG.Walter.isComponentOf_map_conj hK hxN
  have hWx : conjSub x W = A ⊓ Subgroup.centralizer (K' : Set G) :=
    conjSub_inf_centralizer hxA K
  have hcomm : ⁅K, K'⁆ = ⊥ := by
    rcases CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot hK hK' with h | h
    · exact absurd h.symm hKK'
    · exact h
  have hK'C : K' ≤ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hKC : K ≤ Subgroup.centralizer (K' : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have h1 : A ⊓ K' ≤ W := inf_le_inf_left _ hK'C
  have h2 : A ⊓ K ≤ conjSub x W := by rw [hWx]; exact inf_le_inf_left _ hKC
  have hcardK' : Nat.card (A ⊓ K' : Subgroup G) = Nat.card (A ⊓ K : Subgroup G) := by
    rw [hK'def, ← conjSub_inf hxA, card_conjSub]
  have hcomm' : ∀ u ∈ A ⊓ K, ∀ v ∈ W, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.is_comm.comm ⟨u, hu.1⟩ ⟨v, hv.1⟩)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (A ⊓ K) W hcomm').1
  rw [hsup] at hprod
  have hWpos : 0 < Nat.card W := Nat.card_pos
  have hinfpos : 0 < Nat.card (A ⊓ K ⊓ W : Subgroup G) := Nat.card_pos
  have hle1 : Nat.card (A ⊓ K : Subgroup G) ≤ Nat.card W := by
    rw [← hcardK']; exact Subgroup.card_le_of_le h1
  have hA1 : Nat.card A ≤ Nat.card (A ⊓ K : Subgroup G) * Nat.card W := by
    rw [← hprod]; exact Nat.le_mul_of_pos_right _ hinfpos
  have hKW : Nat.card (A ⊓ K : Subgroup G) = Nat.card W := by
    by_contra hneq
    have hlt : Nat.card (A ⊓ K : Subgroup G) < Nat.card W := lt_of_le_of_ne hle1 hneq
    have : Nat.card (A ⊓ K : Subgroup G) * Nat.card W < Nat.card W * Nat.card W :=
      Nat.mul_lt_mul_of_pos_right hlt hWpos
    rw [sq] at hcard
    exact absurd (lt_of_le_of_lt hA1 (lt_of_lt_of_le this hcard)) (lt_irrefl _)
  have hinf1 : Nat.card (A ⊓ K ⊓ W : Subgroup G) = 1 := by
    have h3 : Nat.card A * Nat.card (A ⊓ K ⊓ W : Subgroup G) ≤ Nat.card A * 1 := by
      rw [hprod, hKW, mul_one, ← sq]; exact hcard
    have := Nat.le_of_mul_le_mul_left h3 Nat.card_pos
    omega
  have hKeq : A ⊓ K = conjSub x W :=
    Subgroup.eq_of_le_of_card_ge h2 (by rw [card_conjSub, hKW])
  rw [← hKeq, inf_comm]
  exact Subgroup.card_eq_one.mp hinf1

theorem inf_conjSub_eq_bot {H K : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A))
    (hsup : A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G) = A)
    (hcard : Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ^ 2 ≤ Nat.card A)
    (hAab : IsMulCommutative A) {x : G} (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxH : x ∈ H)
    (hne : conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) ≠
      A ⊓ Subgroup.centralizer (K : Set G)) :
    A ⊓ Subgroup.centralizer (K : Set G) ⊓
      conjSub x (A ⊓ Subgroup.centralizer (K : Set G)) = ⊥ := by
  refine inf_conjSub_eq_bot_of_ne hK hsup hcard hAab hxA hxH fun h => hne ?_
  rw [conjSub_inf_centralizer hxA, h]

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {K : Subgroup G} {x : G} (h : conjSub x K = K) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    rw [← h] at hk
    simpa [mul_assoc] using mem_conjSub.1 hk
  · intro hk
    have : k ∈ conjSub x K := mem_conjSub.2 hk
    rwa [h] at this

end TI

end CFSG.Goldschmidt.G75
