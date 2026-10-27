module

public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement Pointwise

variable {X : Type} [Group X] [Finite X]

theorem zpow_eq_one_or_self {t : X} (ht2 : t * t = 1) (n : ℤ) : t ^ n = 1 ∨ t ^ n = t := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, show t ^ (2 : ℤ) = 1 by rw [zpow_two]; exact ht2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, show t ^ (2 : ℤ) = 1 by rw [zpow_two]; exact ht2, one_zpow,
      one_mul]

theorem mem_sup_zpowers_iff {K : Subgroup X} {t : X} (ht2 : t * t = 1)
    (hK : ∀ k ∈ K, k * t = t * k) {x : X} :
    x ∈ K ⊔ zpowers t ↔ ∃ k ∈ K, x = k ∨ x = k * t := by
  have hc : ∀ k ∈ K, ∀ h ∈ zpowers t, k * h = h * k := by
    intro k hk h hh
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hh
    exact (Commute.zpow_right (show Commute k t from hK k hk) n).eq
  have hnorm : K ≤ normalizer (zpowers t : Set X) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : k * h * k⁻¹ = h := by rw [hc k hk h hh]; group
      rw [this]
      exact hh
    · intro hh
      have h1 : k⁻¹ * (k * h * k⁻¹) * k = h := by group
      have hc' : k⁻¹ * (k * h * k⁻¹) = (k * h * k⁻¹) * k⁻¹ := by
        have := hc k⁻¹ (K.inv_mem hk) _ hh
        exact this
      rw [hc', mul_assoc, inv_mul_cancel, mul_one] at h1
      rw [← h1]
      exact hh
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K (zpowers t) hnorm
  have hx : x ∈ (↑(K ⊔ zpowers t) : Set X) ↔ x ∈ (K : Set X) * (zpowers t : Set X) := by
    rw [hmul]
  constructor
  · intro h
    have h' := hx.mp h
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp h'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    rcases zpow_eq_one_or_self ht2 n with h1 | h1
    · exact ⟨a, ha, Or.inl (by rw [h1, mul_one])⟩
    · exact ⟨a, ha, Or.inr (by rw [h1])⟩
  · rintro ⟨k, hk, rfl | rfl⟩
    · exact mem_sup_left hk
    · exact mul_mem (mem_sup_left hk) (mem_sup_right (mem_zpowers t))

theorem isPGroup_zpowers_of_mul_self {t : X} (ht2 : t * t = 1) : IsPGroup 2 (zpowers t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ht2)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact ⟨0, by rw [Nat.card_zpowers, h]; rfl⟩
  · exact ⟨1, by rw [Nat.card_zpowers, h]; rfl⟩

theorem pCore_two_eq_bot {t : X} {Y : Subgroup X} [IsSimpleGroup Y] (hY2 : ¬ IsPGroup 2 Y)
    (ht2 : t * t = 1) (htn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    (hout : ¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹)
    (hcent : centralizer ({t} : Set X) ≤ (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t) :
    pCore 2 X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set Q : Subgroup X := pCore 2 X with hQ
  haveI hQn : Q.Normal := pCore_normal
  have hQp : IsPGroup 2 Q := pCore_isPGroup
  have hYQ : Q.subgroupOf Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.subgroupOf Y) with h | h
    · exact h
    · exfalso
      apply hY2
      have hle : Y ≤ Q := subgroupOf_eq_top.mp h
      exact hQp.to_le hle
  have hYQ' : ∀ y ∈ Y, y ∈ Q → y = 1 := by
    intro y hy hyQ
    have : (⟨y, hy⟩ : Y) ∈ Q.subgroupOf Y := hyQ
    rw [hYQ, mem_bot] at this
    exact congrArg Subtype.val this
  set P : Subgroup X := Q ⊔ zpowers t with hP
  have hPp : IsPGroup 2 P := hQp.to_sup_of_normal_left (isPGroup_zpowers_of_mul_self ht2)
  haveI : Group.IsNilpotent P := hPp.isNilpotent
  have hQP : Q ≤ P := le_sup_left
  haveI : (Q.subgroupOf P).Normal := inferInstance
  have hQP0 : Q.subgroupOf P ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hQP hx⟩ : P) ∈ Q.subgroupOf P := hx
    rw [h, mem_bot] at this
    have := congrArg Subtype.val this
    simpa using this
  obtain ⟨z, hzQ, hzt, hz1⟩ : ∃ z : X, z ∈ Q ∧ t * z = z * t ∧ z ≠ 1 := by
    have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal hQP0
    by_contra hcon
    push Not at hcon
    apply h1
    rw [eq_bot_iff]
    intro w hw
    rw [mem_bot]
    obtain ⟨hwQ, hwc⟩ := hw
    have htP : t ∈ P := mem_sup_right (mem_zpowers t)
    have hwt : (⟨t, htP⟩ : P) * w = w * ⟨t, htP⟩ := mem_center_iff.mp hwc ⟨t, htP⟩
    have hwt' : t * (w : X) = (w : X) * t := congrArg Subtype.val hwt
    by_contra hw1
    exact hw1 (Subtype.ext (hcon (w : X) hwQ hwt'))
  have hzC : z ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hzt.symm
  have hKt : ∀ k ∈ Y ⊓ centralizer ({t} : Set X), k * t = t * k := fun k hk =>
    mem_centralizer_singleton_iff.mp hk.2
  obtain ⟨k, hk, hzk | hzk⟩ := (mem_sup_zpowers_iff ht2 hKt).mp (hcent hzC)
  · exact hz1 (by rw [hzk]; exact hYQ' k hk.1 (hzk ▸ hzQ))
  ·
    have hzY : ∀ y ∈ Y, z * y * z⁻¹ ∈ Y := by
      intro y hy
      rw [hzk, mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc t y, ← mul_assoc]
      have h1 : t * y * t⁻¹ ∈ Y := htn y hy
      have h2 : k * (t * y * t⁻¹) * k⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hk.1 h1) (Y.inv_mem hk.1)
      simpa [mul_assoc] using h2
    have hcomm : ∀ y ∈ Y, y * z = z * y := by
      intro y hy
      have hyi : y⁻¹ ∈ Y := Y.inv_mem hy
      have hw1 : y * (z * y⁻¹ * z⁻¹) ∈ Y := Y.mul_mem hy (hzY y⁻¹ hyi)
      have hw2 : y * (z * y⁻¹ * z⁻¹) ∈ Q := by
        have h3 : y * z * y⁻¹ ∈ Q := hQn.conj_mem z hzQ y
        have h4 : (y * z * y⁻¹) * z⁻¹ ∈ Q := Q.mul_mem h3 (Q.inv_mem hzQ)
        have : y * (z * y⁻¹ * z⁻¹) = (y * z * y⁻¹) * z⁻¹ := by group
        rw [this]
        exact h4
      have h5 := hYQ' _ hw1 hw2
      calc y * z = (y * (z * y⁻¹ * z⁻¹)) * z * y := by group
        _ = z * y := by rw [h5]; group
    apply hout
    refine ⟨k⁻¹, Y.inv_mem hk.1, fun y hy => ?_⟩
    have h6 : z * y * z⁻¹ = y := by
      rw [← hcomm y hy]; group
    rw [hzk] at h6
    have h7 : k * t * y * (k * t)⁻¹ = y := by simpa [mul_assoc] using h6
    calc t * y * t⁻¹ = k⁻¹ * (k * t * y * (k * t)⁻¹) * k := by group
      _ = k⁻¹ * y * (k⁻¹)⁻¹ := by rw [h7]; group

theorem fitting_eq_bot (hO : oddCore X = ⊥) (hp : pCore 2 X = ⊥) : fittingSubgroup X = ⊥ := by
  have h := WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore (G := X)
  rw [hO, hp, sup_bot_eq] at h
  exact le_bot_iff.mp h

theorem eq_one_of_mem_layer_of_commute (hF : fittingSubgroup X = ⊥) {x : X} (hx : x ∈ layer X)
    (hc : ∀ l ∈ layer X, l * x = x * l) : x = 1 := by
  have h := WholeGroup.center_layer_le_fittingSubgroup (G := X)
  rw [hF] at h
  have hx' : x ∈ (center (layer X)).map (layer X).subtype :=
    (LocalCores.mem_map_center_iff (layer X)).mpr ⟨hx, mem_centralizer_iff.mpr hc⟩
  exact mem_bot.mp (h hx')

theorem centralizer_layer_eq_bot (hF : fittingSubgroup X = ⊥) :
    centralizer (layer X : Set X) = ⊥ := by
  have h1 : CFSG.Open.genFittingFStar X = layer X := by
    rw [CFSG.Open.genFittingFStar.eq_sup, CFSG.Adapters.genFittingFitting_eq_foundations, hF,
      CFSG.Adapters.genFittingLayer_eq_foundations, bot_sup_eq]
  have h2 := CFSG.Adapters.generalized_fitting_self_centralizing X
  rw [h1] at h2
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [mem_bot]
  exact eq_one_of_mem_layer_of_commute hF (h2 hx) (mem_centralizer_iff.mp hx)

theorem layer_le_commutator : layer X ≤ commutator X := by
  have h : ⁅layer X, layer X⁆ = layer X := LocalCores.layer_perfect
  calc layer X = ⁅layer X, layer X⁆ := h.symm
    _ ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := commutator_mono le_top le_top

theorem exists_ne_one_mem_centralizer_of_nonabelian {L : Subgroup X} {t : X} (ht2 : t * t = 1)
    (hLn : ∀ x ∈ L, t * x * t⁻¹ ∈ L) (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) :
    ∃ x ∈ L, x ≠ 1 ∧ x * t = t * x := by
  by_contra hcon
  push Not at hcon
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let f : L → L := fun x => ⟨x⁻¹ * (t * x * t⁻¹), L.mul_mem (L.inv_mem x.2) (hLn x x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (x : X)⁻¹ * (t * x * t⁻¹) = (y : X)⁻¹ * (t * y * t⁻¹) := congrArg Subtype.val hxy
    have h2 : t * ((y : X) * (x : X)⁻¹) * t⁻¹ = (y : X) * (x : X)⁻¹ := by
      calc t * ((y : X) * (x : X)⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
        _ = (y : X) * ((y : X)⁻¹ * (t * y * t⁻¹)) * (t * x * t⁻¹)⁻¹ := by group
        _ = (y : X) * ((x : X)⁻¹ * (t * x * t⁻¹)) * (t * x * t⁻¹)⁻¹ := by rw [← h1]
        _ = (y : X) * (x : X)⁻¹ := by group
    have hz : ((y : X) * (x : X)⁻¹) * t = t * ((y : X) * (x : X)⁻¹) :=
      (mul_inv_eq_iff_eq_mul.mp h2).symm
    by_contra hne
    have hz1 : (y : X) * (x : X)⁻¹ ≠ 1 := fun h => hne (Subtype.ext (mul_inv_eq_one.mp h).symm)
    exact hcon _ (L.mul_mem y.2 (L.inv_mem x.2)) hz1 hz
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  have hinv : ∀ l ∈ L, t * l * t⁻¹ = l⁻¹ := by
    intro l hl
    obtain ⟨x, hx⟩ := hsurj ⟨l, hl⟩
    have hl' : l = (x : X)⁻¹ * (t * x * t⁻¹) := (congrArg Subtype.val hx).symm
    have e : t * (t * (x : X) * t⁻¹) * t⁻¹ = x := by
      rw [htinv]
      calc t * (t * (x : X) * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [ht2]; group
    rw [hl']
    calc t * ((x : X)⁻¹ * (t * x * t⁻¹)) * t⁻¹
        = (t * (x : X)⁻¹ * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
      _ = (t * (x : X)⁻¹ * t⁻¹) * x := by rw [e]
      _ = ((x : X)⁻¹ * (t * x * t⁻¹))⁻¹ := by group
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  apply hab
  have h1 : t * (a * b) * t⁻¹ = (a * b)⁻¹ := hinv _ (L.mul_mem ha hb)
  have h2 : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
  rw [h2, hinv a ha, hinv b hb] at h1
  have h3 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by rw [h1, mul_inv_rev]
  have h4 := congrArg (fun w => w⁻¹) h3
  simpa using h4.symm

theorem le_of_normal_of_not_mem {t : X} {Y L : Subgroup X} [IsSimpleGroup Y] [L.Normal]
    (ht2 : t * t = 1)
    (hcent : centralizer ({t} : Set X) ≤ (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t)
    (hZ : ∀ k ∈ Y ⊓ centralizer ({t} : Set X),
      (∀ k' ∈ Y ⊓ centralizer ({t} : Set X), k * k' = k' * k) → k = 1)
    (htL : t ∉ L) (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) : Y ≤ L := by
  by_contra hYL
  have hLn : ∀ x ∈ L, t * x * t⁻¹ ∈ L := fun x hx => Normal.conj_mem inferInstance x hx t
  obtain ⟨x, hxL, hx1, hxt⟩ := exists_ne_one_mem_centralizer_of_nonabelian ht2 hLn hnab
  have hxC : x ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hxt
  have hKt : ∀ k ∈ Y ⊓ centralizer ({t} : Set X), k * t = t * k := fun k hk =>
    mem_centralizer_singleton_iff.mp hk.2
  have hYL' : ∀ y ∈ Y, y ∈ L → y = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf Y) with h | h
    · intro y hy hyL
      have : (⟨y, hy⟩ : Y) ∈ L.subgroupOf Y := hyL
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    · exact absurd (subgroupOf_eq_top.mp h) hYL
  obtain ⟨k, hk, hxk | hxk⟩ := (mem_sup_zpowers_iff ht2 hKt).mp (hcent hxC)
  · exact hx1 (by rw [hxk]; exact hYL' k hk.1 (hxk ▸ hxL))
  · have hk1 : k = 1 := by
      apply hZ k hk
      intro k' hk'
      have hw1 : x⁻¹ * (k' * x * k'⁻¹) ∈ L :=
        L.mul_mem (L.inv_mem hxL) (Normal.conj_mem inferInstance x hxL k')
      have hm : k⁻¹ * k' * k * k'⁻¹ ∈ Y ⊓ centralizer ({t} : Set X) :=
        mul_mem (mul_mem (mul_mem (inv_mem hk) hk') hk) (inv_mem hk')
      have hmt : (k⁻¹ * k' * k * k'⁻¹) * t = t * (k⁻¹ * k' * k * k'⁻¹) := hKt _ hm
      have hk't : t * k'⁻¹ = k'⁻¹ * t := (hKt k'⁻¹ (inv_mem hk')).symm
      have hw2 : x⁻¹ * (k' * x * k'⁻¹) = k⁻¹ * k' * k * k'⁻¹ := by
        rw [hxk]
        calc (k * t)⁻¹ * (k' * (k * t) * k'⁻¹) = t⁻¹ * (k⁻¹ * k' * k * (t * k'⁻¹)) := by group
          _ = t⁻¹ * (k⁻¹ * k' * k * (k'⁻¹ * t)) := by rw [hk't]
          _ = t⁻¹ * ((k⁻¹ * k' * k * k'⁻¹) * t) := by group
          _ = t⁻¹ * (t * (k⁻¹ * k' * k * k'⁻¹)) := by rw [hmt]
          _ = k⁻¹ * k' * k * k'⁻¹ := by group
      rw [hw2] at hw1
      have h3 := hYL' _ hm.1 hw1
      have h4 : k' * k * k'⁻¹ = k := by
        have : k⁻¹ * (k' * k * k'⁻¹) = 1 := by simpa [mul_assoc] using h3
        exact (inv_mul_eq_one.mp this).symm
      have h5 : k' * k = k * k' := by
        calc k' * k = (k' * k * k'⁻¹) * k' := by group
          _ = k * k' := by rw [h4]
      exact h5.symm
    apply htL
    have : t = k⁻¹ * x := by rw [hxk, hk1]; group
    rw [this, hk1]
    simpa using hxL

theorem normalizes_sSup {A : Subgroup X} {𝒮 : Set (Subgroup X)}
    (h : ∀ T ∈ 𝒮, ∀ a ∈ A, ∀ x ∈ T, a * x * a⁻¹ ∈ T) :
    ∀ a ∈ A, ∀ x ∈ sSup 𝒮, a * x * a⁻¹ ∈ sSup 𝒮 := by
  intro a ha x hx
  have hle : sSup 𝒮 ≤ (sSup 𝒮).comap (MulAut.conj a).toMonoidHom :=
    sSup_le fun T hT y hy => by
      show a * y * a⁻¹ ∈ sSup 𝒮
      exact le_sSup hT (h T hT a ha y hy)
  exact hle hx

theorem even_card_of_isComponent {K : Subgroup X} (hK : IsComponent K) : Even (Nat.card K) := by
  by_contra hodd
  have hsol : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
  have : Nontrivial K := LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable K hsol

theorem conj_mem_centralizer_of_mem_normalizer {S : Subgroup X} {y x : X}
    (hy : y ∈ normalizer (S : Set X)) (hx : x ∈ centralizer (S : Set X)) :
    y * x * y⁻¹ ∈ centralizer (S : Set X) := by
  rw [mem_centralizer_iff]
  intro s hs
  have hy' : y⁻¹ ∈ normalizer (S : Set X) := inv_mem hy
  have hs' : y⁻¹ * s * y⁻¹⁻¹ ∈ S := (mem_normalizer_iff.mp hy' s).mp hs
  rw [inv_inv] at hs'
  have h1 := mem_centralizer_iff.mp hx _ hs'
  calc s * (y * x * y⁻¹) = y * ((y⁻¹ * s * y) * x) * y⁻¹ := by group
    _ = y * (x * (y⁻¹ * s * y)) * y⁻¹ := by rw [h1]
    _ = (y * x * y⁻¹) * s := by group

theorem isSimpleGroup_layer_of_sylow {Y U : Subgroup X} [IsSimpleGroup Y]
    (hF : fittingSubgroup X = ⊥) (hYL : Y ≤ layer X) (hUY : U ≤ Y)
    (hU : IsSylowOf 2 U (layer X)) : IsSimpleGroup (layer X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hYS⟩ : ∃ S : Subgroup X, IsComponent S ∧ ¬ Y ≤ centralizer (S : Set X) := by
    by_contra hcon
    push Not at hcon
    have hYC : Y ≤ centralizer (layer X : Set X) := by
      intro y hy
      rw [mem_centralizer_iff]
      intro l hl
      have hle : layer X ≤ centralizer ({y} : Set X) := by
        refine sSup_le fun K hK z hz => ?_
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp (hcon K hK hy) z hz)
      exact mem_centralizer_singleton_iff.mp (hle hl)
    rw [centralizer_layer_eq_bot hF] at hYC
    have hY1 : ∀ y : Y, y = 1 := fun y => Subtype.ext (mem_bot.mp (hYC y.2))
    obtain ⟨a, b, hab⟩ := exists_pair_ne Y
    exact hab ((hY1 a).trans (hY1 b).symm)
  obtain ⟨hEC, hLE⟩ := WholeGroup.layer_eq_sup_others hS
  set E : Subgroup X := sSup {T : Subgroup X | IsComponent T ∧ T ≠ S} with hEdef
  have hEL : E ≤ layer X := hLE ▸ le_sup_right
  have hLnE : layer X ≤ normalizer (E : Set X) := by
    have hnorm := normalizes_sSup (A := layer X) (𝒮 := {T : Subgroup X | IsComponent T ∧ T ≠ S})
      (fun T hT a ha x hx => (mem_normalizer_iff.mp (LocalCores.layer_le_normalizer hT.1 ha) x).mp hx)
    intro l hl
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hnorm l hl h hh, fun hh => ?_⟩
    have h2 := hnorm l⁻¹ (inv_mem hl) _ hh
    have e1 : l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h := by group
    rw [e1] at h2
    exact h2
  have hYC1 : Y ⊓ centralizer (S : Set X) = ⊥ := by
    have hn : ((Y ⊓ centralizer (S : Set X)).subgroupOf Y).Normal := by
      refine (Subgroup.normal_subgroupOf_iff inf_le_left).mpr fun h k hh hk => ?_
      refine ⟨Y.mul_mem (Y.mul_mem hk hh.1) (Y.inv_mem hk), ?_⟩
      exact conj_mem_centralizer_of_mem_normalizer
        (LocalCores.layer_le_normalizer hS (hYL hk)) hh.2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Y ⊓ centralizer (S : Set X)).subgroupOf Y)
      with h | h
    · refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hx.1⟩ : Y) ∈ (Y ⊓ centralizer (S : Set X)).subgroupOf Y := hx
      rw [h, mem_bot] at this
      exact mem_bot.mpr (congrArg Subtype.val this)
    · exact absurd (fun y hy => (subgroupOf_eq_top.mp h hy).2) hYS
  have hUE : U ⊓ E = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : x ∈ Y ⊓ centralizer (S : Set X) := ⟨hUY hx.1, hEC hx.2 ⟩
    rw [hYC1] at h1
    exact h1
  have hSylE : IsSylowOf 2 (U ⊓ E) E := hU.inf_of_le_normalizer hEL hLnE
  have hcardE : Nat.card ((U ⊓ E : Subgroup X)) = 2 ^ (Nat.card E).factorization 2 := hSylE.card_eq
  rw [hUE] at hcardE
  have hEodd : ¬ 2 ∣ Nat.card E := by
    intro hdvd
    have hpos : Nat.card E ≠ 0 := Nat.card_pos.ne'
    have hfac : (Nat.card E).factorization 2 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hpos hdvd).ne'
    have : (2 : ℕ) ^ (Nat.card E).factorization 2 = 1 := by
      rw [← hcardE]; simp
    exact hfac (by simpa using (Nat.pow_eq_one.mp this).resolve_left (by norm_num))
  have hnone : ∀ T : Subgroup X, IsComponent T → T = S := by
    intro T hT
    by_contra hne
    have hTE : T ≤ E := le_sSup ⟨hT, hne⟩
    have hdvd : Nat.card T ∣ Nat.card E := Subgroup.card_dvd_of_le hTE
    obtain ⟨k, hk⟩ := even_card_of_isComponent hT
    exact hEodd ((by omega : 2 ∣ Nat.card T).trans hdvd)
  have hEbot : E = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun T hT => ?_)
    exact absurd (hnone T hT.1) hT.2
  have hLS : layer X = S := by rw [hLE, hEbot, sup_bot_eq]
  have hZS : ∀ z : S, z ∈ center S → z = 1 := by
    intro z hz
    refine Subtype.ext (eq_one_of_mem_layer_of_commute hF (hLS ▸ z.2) fun l hl => ?_)
    have hl' : l ∈ S := hLS ▸ hl
    have := mem_center_iff.mp hz ⟨l, hl'⟩
    exact congrArg Subtype.val this
  have hinj : Function.Injective (QuotientGroup.mk' (center S)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', eq_bot_iff]
    intro z hz
    exact hZS z hz
  have e : S ≃* (S ⧸ center S) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center S)) ⟨hinj, QuotientGroup.mk'_surjective _⟩
  haveI : IsSimpleGroup (S ⧸ center S) := hS.1.2.1
  haveI : IsSimpleGroup S := e.isSimpleGroup
  subst hLS
  exact this

theorem mem_sup_zpowers_iff_of_normalizes {U : Subgroup X} {t : X} (ht2 : t * t = 1)
    (htn : ∀ u ∈ U, t * u * t⁻¹ ∈ U) {x : X} :
    x ∈ U ⊔ zpowers t ↔ ∃ u ∈ U, x = u ∨ x = u * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hnorm : zpowers t ≤ normalizer (U : Set X) := by
    intro g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    rw [mem_normalizer_iff]
    intro h
    rcases zpow_eq_one_or_self ht2 n with h1 | h1
    · rw [h1]; simp
    · rw [h1]
      refine ⟨fun hh => htn h hh, fun hh => ?_⟩
      have := htn _ hh
      have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
        rw [htinv]
        calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
          _ = h := by rw [ht2]; group
      rw [e] at this
      exact this
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) U hnorm
  rw [sup_comm] at hmul
  have hx : x ∈ (↑(U ⊔ zpowers t) : Set X) ↔ x ∈ (zpowers t : Set X) * (U : Set X) := by
    rw [hmul]
  constructor
  · intro h
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_mul.mp (hx.mp h)
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    rcases zpow_eq_one_or_self ht2 n with h1 | h1
    · exact ⟨a, ha, Or.inl (by rw [h1, one_mul])⟩
    · refine ⟨t * a * t⁻¹, htn a ha, Or.inr ?_⟩
      rw [h1]
      group
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))

theorem index_eq_two_of_normalizes {U : Subgroup X} {t : X} (ht2 : t * t = 1)
    (htn : ∀ u ∈ U, t * u * t⁻¹ ∈ U) (htU : t ∉ U) :
    (U.subgroupOf (U ⊔ zpowers t)).index = 2 := by
  have htM : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨t, htM⟩, fun b => ?_⟩
  obtain ⟨x, hxM⟩ := b
  obtain ⟨u, hu, rfl | rfl⟩ := (mem_sup_zpowers_iff_of_normalizes ht2 htn).mp hxM
  · change Xor' (x * t ∈ U) (x ∈ U)
    refine Or.inr ⟨hu, fun h => htU ?_⟩
    have : x⁻¹ * (x * t) ∈ U := U.mul_mem (U.inv_mem hu) h
    simpa using this
  · change Xor' (u * t * t ∈ U) (u * t ∈ U)
    have h1 : u * t * t ∈ U := by rw [mul_assoc, ht2, mul_one]; exact hu
    refine Or.inl ⟨h1, fun h => htU ?_⟩
    have : u⁻¹ * (u * t) ∈ U := U.mul_mem (U.inv_mem hu) h
    simpa using this

theorem card_sup_zpowers_of_normalizes {U : Subgroup X} {t : X} (ht2 : t * t = 1)
    (htn : ∀ u ∈ U, t * u * t⁻¹ ∈ U) (htU : t ∉ U) :
    Nat.card (U ⊔ zpowers t : Subgroup X) = 2 * Nat.card U := by
  have h := index_eq_two_of_normalizes ht2 htn htU
  have h2 := (U.subgroupOf (U ⊔ zpowers t)).card_mul_index
  rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : U ≤ U ⊔ zpowers t)).toEquiv]
    at h2
  rw [← h2, mul_comm]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
