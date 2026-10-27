module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Four
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NoInv
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin
open scoped commutatorElement Pointwise

theorem not_dvd_card_mulAut_of_card_le_256 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W ≤ 256) : ¬ 343 ∣ Nat.card (MulAut W) := by
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn8 : n ≤ 8 := by
    by_contra h
    have : 2 ^ 9 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm a b) (fun a => hW a) hn
  have hGL : Nat.card (MulAut W) = Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :=
    Nat.card_congr (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toEquiv
  rw [hGL, Matrix.card_GL_field]
  interval_cases n <;> simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]

theorem commute_of_card_pow_le_two {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} {k : ℕ} (hk : Nat.card ↥H = p ^ k) (hk2 : k ≤ 2) :
    ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  have hcomm : ∀ a b : H, a * b = b * a := by
    interval_cases k
    · intro a b
      have : Nat.card H = 1 := by simpa using hk
      have h1 : Subsingleton H := (Nat.card_eq_one_iff_unique.mp this).1
      exact Subsingleton.elim _ _
    · have hp : Nat.card H = p := by simpa using hk
      have : IsCyclic H := isCyclic_of_prime_card hp
      exact fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b
    · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hk
      exact fun a b => this.is_comm.comm a b
  intro a ha b hb
  have := hcomm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val this

theorem odd_orderOf_of_isPGroup_seven {G : Type*} [Group G] {H : Subgroup G} (h7 : IsPGroup 7 ↥H)
    {x : G} (hx : x ∈ H) : Odd (orderOf x) := by
  obtain ⟨k, hk⟩ := h7 ⟨x, hx⟩
  have h1 : x ^ 7 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one h1)

theorem conj_mem_map_of_characteristic' {H : Type*} [Group H] {X : Subgroup H} {D : Subgroup X}
    [hD : D.Characteristic] {g : H} (hg : g ∈ Subgroup.normalizer (X : Set H)) {x : H}
    (hx : x ∈ D.map X.subtype) : g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem map_pCore_le_pCore_of_isSubnormal' {H : Type*} [Group H] [Finite H] {p : ℕ}
    {X : Subgroup H} (hX : X.IsSubnormal) :
    (CFSG.pCore p X).map X.subtype ≤ CFSG.pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.pCore p X).map X.subtype ≤ (CFSG.pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using conj_mem_map_of_characteristic' (hYN y.2) hl
      · exact ((CFSG.pCore_isPGroup).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (CFSG.pCore p X).map X.subtype
        = (((CFSG.pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hX with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => conj_mem_map_of_characteristic' ?_ hl⟩,
      (CFSG.pCore_isPGroup).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

theorem le_pCore_of_isSubnormal {H : Type*} [Group H] [Finite H] {p : ℕ} {Z : Subgroup H}
    (hZ : Z.IsSubnormal) (hp : IsPGroup p ↥Z) : Z ≤ CFSG.pCore p H := by
  have htop : CFSG.pCore p Z = ⊤ :=
    le_antisymm le_top (le_sSup ⟨inferInstance, hp.of_equiv Subgroup.topEquiv.symm⟩)
  have h := map_pCore_le_pCore_of_isSubnormal' (p := p) hZ
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

structure Odd54 (V : Type) [CommGroup V] (Y X K : Subgroup (MulAut V)) : Prop where
  elem : ∀ v : V, v ^ 2 = 1
  yx : Y ≤ X
  ycard : Nat.card ↥Y = 3
  ucard : Nat.card ↥(commV Y) = 4
  kx : K ≤ X
  knorm : X ≤ Subgroup.normalizer (K : Set (MulAut V))
  k7 : IsPGroup 7 ↥K
  xsup : Y ⊔ K = X
  xodd : Odd (Nat.card ↥X)
  hgen : ∀ N : Subgroup (MulAut V), N ≤ X → Y ≤ N →
    X ≤ Subgroup.normalizer (N : Set (MulAut V)) → N = X

namespace Odd54

variable {V : Type} [CommGroup V] [Finite V] {Y X K : Subgroup (MulAut V)} (h : Odd54 V Y X K)
include h

theorem eq_one_of_mem_inf {y : MulAut V} (hyY : y ∈ Y) (hyK : y ∈ K) : y = 1 := by
  have h3 : y ^ 3 = 1 := by
    have : (⟨y, hyY⟩ : ↥Y) ^ Nat.card ↥Y = 1 := pow_card_eq_one'
    rw [h.ycard] at this
    simpa using congrArg Subtype.val this
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨m, hm⟩ := h.k7.exists_card_eq
  have h7 : y ^ 7 ^ m = 1 := by
    have : (⟨y, hyK⟩ : ↥K) ^ Nat.card ↥K = 1 := pow_card_eq_one'
    rw [hm] at this
    simpa using congrArg Subtype.val this
  have hg : Nat.gcd 3 (7 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
  have := pow_gcd_eq_one.mpr ⟨h3, h7⟩
  rwa [hg, pow_one] at this

omit [Finite V] in
theorem conj_mem {x : MulAut V} (hx : x ∈ X) {k : MulAut V} (hk : k ∈ K) : x * k * x⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp (h.knorm hx) k).mp hk

theorem le_commutator : K ≤ ⁅K, Y⁆ := by
  set C : Subgroup (MulAut V) := ⁅K, Y⁆ with hC
  have hYN : Y ≤ Subgroup.normalizer (K : Set (MulAut V)) := fun y hy => h.knorm (h.yx hy)
  have hCK : C ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hYN
  have hKnormC : K ≤ Subgroup.normalizer (C : Set (MulAut V)) :=
    Subgroup.normalizer_commutator_ge_left K Y
  have hYnormC : Y ≤ Subgroup.normalizer (C : Set (MulAut V)) :=
    Subgroup.normalizer_commutator_ge_right K Y
  have hkey : ∀ k' ∈ K, ∀ m ∈ Y ⊔ C, k' * m * k'⁻¹ ∈ Y ⊔ C := by
    intro k' hk' m hm
    have hm' : m ∈ ((Y : Set (MulAut V)) * (C : Set (MulAut V))) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y C hYnormC]
      exact hm
    obtain ⟨y, hy, c, hc, rfl⟩ := hm'
    have h1 : k' * y * k'⁻¹ = ⁅k', y⁆ * y := by rw [commutatorElement_def]; group
    have h2 : ⁅k', y⁆ ∈ C := Subgroup.commutator_mem_commutator hk' hy
    have h3 : k' * c * k'⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hKnormC hk') c).mp hc
    have e : k' * (y * c) * k'⁻¹ = (k' * y * k'⁻¹) * (k' * c * k'⁻¹) := by group
    rw [e, h1]
    exact mul_mem (mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hy))
      (Subgroup.mem_sup_right h3)
  have hnorm : X ≤ Subgroup.normalizer ((Y ⊔ C : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [← h.xsup]
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
    intro k hk
    exact mem_normalizer_of_conj_mem (fun m hm => hkey k hk m hm)
      (fun m hm => by simpa using hkey k⁻¹ (K.inv_mem hk) m hm)
  have hYC : Y ⊔ C = X := h.hgen (Y ⊔ C) (sup_le h.yx (hCK.trans h.kx)) le_sup_left hnorm
  intro k hk
  have hkX : k ∈ ((Y : Set (MulAut V)) * (C : Set (MulAut V))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y C hYnormC, hYC]
    exact h.kx hk
  obtain ⟨y, hy, c, hc, hyc0⟩ := hkX
  have hyc : y * c = k := hyc0
  have hyK : y ∈ K := by
    have : y = k * c⁻¹ := by rw [← hyc]; group
    rw [this]
    exact K.mul_mem hk (K.inv_mem (hCK hc))
  have hy1 : y = 1 := h.eq_one_of_mem_inf hy hyK
  rw [hy1, one_mul] at hyc
  rw [← hyc]
  exact hc

theorem card_commV_commutator_le {r y : MulAut V} (hy : y ∈ Y) :
    Nat.card ↥(commV (Subgroup.zpowers ⁅r, y⁆)) ≤ 16 := by
  have hcH : ⁅r, y⁆ ∈ Y ⊔ Y.map (MulAut.conj r).toMonoidHom := by
    have h1 : r * y * r⁻¹ ∈ Y.map (MulAut.conj r).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    have h2 : y⁻¹ ∈ Y ⊔ Y.map (MulAut.conj r).toMonoidHom := Subgroup.mem_sup_left (Y.inv_mem hy)
    rw [commutatorElement_def]
    exact mul_mem (Subgroup.mem_sup_right h1) h2
  have hle : Subgroup.zpowers ⁅r, y⁆ ≤ Y ⊔ Y.map (MulAut.conj r).toMonoidHom :=
    Subgroup.zpowers_le.mpr hcH
  exact (Subgroup.card_le_of_le (commV_mono hle)).trans (card_commV_sup_conj_le h.ucard r)

omit [Finite V] in
theorem commutator_mem {r y : MulAut V} (hr : r ∈ K) (hy : y ∈ X) : ⁅r, y⁆ ∈ K := by
  have : ⁅r, y⁆ = r * (y * r⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  rw [this]
  exact K.mul_mem hr (h.conj_mem hy (K.inv_mem hr))

theorem commute_commutators {r₁ y₁ r₂ y₂ : MulAut V} (hr₁ : r₁ ∈ K) (hy₁ : y₁ ∈ Y) (hr₂ : r₂ ∈ K)
    (hy₂ : y₂ ∈ Y) : ⁅r₁, y₁⁆ * ⁅r₂, y₂⁆ = ⁅r₂, y₂⁆ * ⁅r₁, y₁⁆ := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc₁K : ⁅r₁, y₁⁆ ∈ K := h.commutator_mem hr₁ (h.yx hy₁)
  have hc₂K : ⁅r₂, y₂⁆ ∈ K := h.commutator_mem hr₂ (h.yx hy₂)
  set S : Subgroup (MulAut V) := Subgroup.zpowers ⁅r₁, y₁⁆ ⊔ Subgroup.zpowers ⁅r₂, y₂⁆ with hS
  have hSK : S ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hc₁K) (Subgroup.zpowers_le.mpr hc₂K)
  have hS7 : IsPGroup 7 ↥S := h.k7.to_le hSK
  have hSodd : ∀ x ∈ S, Odd (orderOf x) := fun x hx => odd_orderOf_of_isPGroup_seven hS7 hx
  have hcommV : Nat.card ↥(commV S) ≤ 256 := by
    have h1 := Subgroup.card_le_of_le (commV_sup_le (Subgroup.zpowers ⁅r₁, y₁⁆)
      (Subgroup.zpowers ⁅r₂, y₂⁆))
    have h2 := card_sup_le_mul (commV (Subgroup.zpowers ⁅r₁, y₁⁆))
      (commV (Subgroup.zpowers ⁅r₂, y₂⁆))
    have h3 := h.card_commV_commutator_le (r := r₁) hy₁
    have h4 := h.card_commV_commutator_le (r := r₂) hy₂
    calc Nat.card ↥(commV S) ≤ Nat.card ↥(commV (Subgroup.zpowers ⁅r₁, y₁⁆) ⊔
          commV (Subgroup.zpowers ⁅r₂, y₂⁆)) := h1
      _ ≤ _ := h2
      _ ≤ 16 * 16 := Nat.mul_le_mul h3 h4
  have hinj := injective_resHom h.elem hSodd
  have hWelem : ∀ w : ↥(commV S), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using h.elem w)
  have hdvd : Nat.card ↥S ∣ Nat.card (MulAut ↥(commV S)) := by
    have h1 : Nat.card ↥S = Nat.card ↥(resHom S).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨m, hm⟩ := hS7.exists_card_eq
  have hm2 : m ≤ 2 := by
    by_contra hm3
    have h343 : 7 ^ 3 ∣ 7 ^ m := Nat.pow_dvd_pow 7 (by omega)
    rw [← hm] at h343
    exact not_dvd_card_mulAut_of_card_le_256 hWelem hcommV (by simpa using h343.trans hdvd)
  exact commute_of_card_pow_le_two hm hm2 _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem commute {a b : MulAut V} (ha : a ∈ K) (hb : b ∈ K) : a * b = b * a := by
  set S₀ : Set (MulAut V) := {g | ∃ g₁ ∈ K, ∃ g₂ ∈ Y, ⁅g₁, g₂⁆ = g} with hS₀
  have hKcl : K ≤ Subgroup.closure S₀ := by
    have := h.le_commutator
    rwa [Subgroup.commutator_def] at this
  have hS₀cent : S₀ ⊆ Subgroup.centralizer S₀ := by
    rintro _ ⟨r₁, hr₁, y₁, hy₁, rfl⟩ _ ⟨r₂, hr₂, y₂, hy₂, rfl⟩
    exact (h.commute_commutators hr₁ hy₁ hr₂ hy₂).symm
  have hcl : Subgroup.closure S₀ ≤ Subgroup.centralizer S₀ := (Subgroup.closure_le _).mpr hS₀cent
  rw [← Subgroup.centralizer_closure] at hcl
  exact Subgroup.mem_centralizer_iff.mp (hcl (hKcl hb)) a (hKcl ha)

theorem commute_of_subnormal (hs : (Y.subgroupOf X).IsSubnormal) {y k : MulAut V} (hy : y ∈ Y)
    (hk : k ∈ K) : y * k = k * y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYt3 : IsPGroup 3 ↥(Y.subgroupOf X) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.yx).toEquiv, h.ycard]
    simp
  have hle : Y.subgroupOf X ≤ CFSG.pCore 3 ↥X := le_pCore_of_isSubnormal hs hYt3
  set Oc : Subgroup (MulAut V) := (CFSG.pCore 3 ↥X).map X.subtype with hOc
  have hOc3 : IsPGroup 3 ↥Oc := (CFSG.pCore_isPGroup (p := 3) (G := ↥X)).map X.subtype
  have hyOc : y ∈ Oc := ⟨⟨y, h.yx hy⟩, hle hy, rfl⟩
  have hOcnorm : ∀ x ∈ X, ∀ a ∈ Oc, x * a * x⁻¹ ∈ Oc := by
    rintro x hx _ ⟨a', ha', rfl⟩
    exact ⟨⟨x, hx⟩ * a' * ⟨x, hx⟩⁻¹, (CFSG.pCore_normal (p := 3) (G := ↥X)).conj_mem a' ha' ⟨x, hx⟩,
      by simp⟩
  have hcK : ⁅y, k⁆ ∈ K := by
    have : ⁅y, k⁆ = (y * k * y⁻¹) * k⁻¹ := by rw [commutatorElement_def]
    rw [this]
    exact K.mul_mem (h.conj_mem (h.yx hy) hk) (K.inv_mem hk)
  have hcOc : ⁅y, k⁆ ∈ Oc := by
    have : ⁅y, k⁆ = y * (k * y⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact Oc.mul_mem hyOc (hOcnorm k (h.kx hk) y⁻¹ (Oc.inv_mem hyOc))
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := hOc3 ⟨⁅y, k⁆, hcOc⟩
  obtain ⟨b, hb⟩ := h.k7 ⟨⁅y, k⁆, hcK⟩
  have h3 : ⁅y, k⁆ ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have h7 : ⁅y, k⁆ ^ 7 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hg : Nat.gcd (3 ^ a) (7 ^ b) = 1 := Nat.Coprime.pow a b (by norm_num)
  have h1 : ⁅y, k⁆ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h3, h7⟩
    rwa [hg, pow_one] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem commutator_mul {a b y : MulAut V} (ha : a ∈ K) (hb : b ∈ K) (hy : y ∈ X) :
    ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆ := by
  have e : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
    simp only [commutatorElement_def]; group
  have h1 : a * ⁅b, y⁆ * a⁻¹ = ⁅b, y⁆ := by
    have := h.commute ha (h.commutator_mem hb hy)
    rw [this]; group
  rw [e, h1]
  exact h.commute (h.commutator_mem hb hy) (h.commutator_mem ha hy)

theorem commutator_inv {a y : MulAut V} (ha : a ∈ K) (hy : y ∈ X) : ⁅a⁻¹, y⁆ = ⁅a, y⁆⁻¹ := by
  have h1 := h.commutator_mul (K.inv_mem ha) ha hy
  rw [inv_mul_cancel] at h1
  have h2 : ⁅(1 : MulAut V), y⁆ = 1 := by simp [commutatorElement_def]
  rw [h2] at h1
  exact (eq_inv_of_mul_eq_one_left h1.symm)

end Odd54


namespace Sec5Hyp

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)} (h : Sec5Hyp V G T Y)
include h

theorem eq_of_normalizes {X : Subgroup (MulAut V)} (hXG : X ≤ G) (hYX : Y ≤ X)
    (hodd : Odd (Nat.card ↥X))
    (hgen : ∀ N : Subgroup (MulAut V), N ≤ X → Y ≤ N →
      X ≤ Subgroup.normalizer (N : Set (MulAut V)) → N = X)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut V))) : X = Y := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨R, hRX, hXR, hR7, hYR⟩ :=
    exists_normal_seven_of_odd h.elem hYX hodd h.ycard h.ucard hgen
  set K : Subgroup (MulAut V) := (CFSG.pCore 7 ↥X).map X.subtype with hK
  have hKX : K ≤ X := Subgroup.map_subtype_le _
  have hK7 : IsPGroup 7 ↥K := (CFSG.pCore_isPGroup (p := 7) (G := ↥X)).map X.subtype
  have hKnorm : X ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
    intro x hx
    have key : ∀ x ∈ X, ∀ a ∈ K, x * a * x⁻¹ ∈ K := by
      rintro x hx _ ⟨a', ha', rfl⟩
      exact ⟨⟨x, hx⟩ * a' * ⟨x, hx⟩⁻¹,
        (CFSG.pCore_normal (p := 7) (G := ↥X)).conj_mem a' ha' ⟨x, hx⟩, by simp⟩
    exact mem_normalizer_of_conj_mem (key x hx) (fun a ha => by simpa using key x⁻¹ (X.inv_mem hx) a ha)
  have hRK : R ≤ K := by
    have hRn : (R.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mpr hXR
    have hle : R.subgroupOf X ≤ CFSG.pCore 7 ↥X :=
      le_sSup ⟨hRn, hR7.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm⟩
    intro r hr
    exact ⟨⟨r, hRX hr⟩, hle hr, rfl⟩
  have hXK : Y ⊔ K = X := le_antisymm (sup_le hYX hKX) (hYR ▸ sup_le_sup_left hRK Y)
  have hTK : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun t ht k hk =>
    conj_mem_map_of_characteristic' (D := CFSG.pCore 7 ↥X) (hTX ht) hk
  have hdata : Odd54 V Y X K :=
    ⟨h.elem, hYX, h.ycard, h.ucard, hKX, hKnorm, hK7, hXK, hodd, hgen⟩
  by_cases hKbot : K = ⊥
  · rw [hKbot, sup_bot_eq] at hXK
    exact hXK.symm
  exfalso
  by_cases hTc : ∀ t ∈ T, ∀ k ∈ K, t * k = k * t
  ·
    have hXH : X ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V)) := by
      rw [← hXK]
      refine sup_le h.yle ?_
      intro k hk
      exact ⟨hXG (hKX hk), Subgroup.mem_centralizer_iff.mpr fun t ht => hTc t ht k hk⟩
    have hsub : (Y.subgroupOf X).IsSubnormal := by
      have := h.ysub.comap (Subgroup.inclusion hXH)
      rwa [Subgroup.comap_inclusion_subgroupOf] at this
    have hKcent : K ≤ Subgroup.centralizer (Y : Set (MulAut V)) := fun k hk =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hdata.commute_of_subnormal hsub hy hk
    have hcomm : ⁅K, Y⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKcent
    apply hKbot
    rw [eq_bot_iff]
    have := hdata.le_commutator
    rwa [hcomm] at this
  · push Not at hTc
    have hex : ∃ n : ℕ, ∃ t ∈ T, (∃ k ∈ K, t * k ≠ k * t) ∧ orderOf t = n := by
      obtain ⟨t, ht, k, hk, hne⟩ := hTc
      exact ⟨orderOf t, t, ht, ⟨k, hk, hne⟩, rfl⟩
    obtain ⟨t, htT, htn, hmin⟩ : ∃ t ∈ T, (∃ k ∈ K, t * k ≠ k * t) ∧
        ∀ t' ∈ T, (∃ k ∈ K, t' * k ≠ k * t') → orderOf t ≤ orderOf t' := by
      obtain ⟨t, ht, hnt, hord⟩ := Nat.find_spec hex
      refine ⟨t, ht, hnt, fun t' ht' hnt' => ?_⟩
      rw [hord]
      exact Nat.find_min' hex ⟨t', ht', hnt', rfl⟩
    have hsq : ∀ k ∈ K, t ^ 2 * k = k * t ^ 2 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨k, hk, hne⟩ := hcon
      obtain ⟨n, hn⟩ := h.tTwo ⟨t, htT⟩
      have ht2 : t ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ht2)
      have ha1 : 1 ≤ a := by
        by_contra ha0
        have : a = 0 := by omega
        rw [this, pow_zero] at ha
        have ht1 : t = 1 := orderOf_eq_one_iff.mp ha
        obtain ⟨k', hk', hne'⟩ := htn
        apply hne'
        rw [ht1]
        simp
      have hlt : orderOf (t ^ 2) < orderOf t := by
        rw [orderOf_pow' t (by norm_num : (2 : ℕ) ≠ 0), ha]
        have hgcd : Nat.gcd (2 ^ a) 2 = 2 := Nat.gcd_eq_right (dvd_pow_self 2 (by omega))
        rw [hgcd]
        have h2 : 0 < 2 ^ a := by positivity
        omega
      have := hmin (t ^ 2) (T.pow_mem htT 2) ⟨k, hk, hne⟩
      omega
    obtain ⟨k₀, hk₀K, hk₀⟩ := htn
    have hmoved : ∃ r ∈ K, ∃ y ∈ Y, t * ⁅r, y⁆ ≠ ⁅r, y⁆ * t := by
      by_contra hcon
      push Not at hcon
      apply hk₀
      set S₀ : Set (MulAut V) := {g | ∃ g₁ ∈ K, ∃ g₂ ∈ Y, ⁅g₁, g₂⁆ = g} with hS₀
      have hKcl : K ≤ Subgroup.closure S₀ := by
        have := hdata.le_commutator
        rwa [Subgroup.commutator_def] at this
      have hS₀c : S₀ ⊆ Subgroup.centralizer ({t} : Set (MulAut V)) := by
        rintro _ ⟨r, hr, y, hy, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff] at hu
        rw [hu]
        exact hcon r hr y hy
      have hcl : Subgroup.closure S₀ ≤ Subgroup.centralizer ({t} : Set (MulAut V)) :=
        (Subgroup.closure_le _).mpr hS₀c
      exact Subgroup.mem_centralizer_iff.mp (hcl (hKcl hk₀K)) t (Set.mem_singleton t)
    obtain ⟨r, hrK, y, hyY, hrt⟩ := hmoved
    have hyX : y ∈ X := hYX hyY
    have hty : t * y = y * t := Subgroup.mem_centralizer_iff.mp (h.yle hyY).2 t htT
    have hy' : t * y * t⁻¹ = y := by rw [hty]; group
    have hconj : ∀ a : MulAut V, ⁅t * a * t⁻¹, y⁆ = t * ⁅a, y⁆ * t⁻¹ := by
      intro a
      calc ⁅t * a * t⁻¹, y⁆ = ⁅t * a * t⁻¹, t * y * t⁻¹⁆ := by rw [hy']
        _ = t * ⁅a, y⁆ * t⁻¹ := by simp only [commutatorElement_def]; group
    obtain ⟨r', hr'⟩ : ∃ r' : MulAut V, r' = t * r * t⁻¹ := ⟨_, rfl⟩
    have hr'K : r' ∈ K := hr' ▸ hTK t htT r hrK
    have hr'r : t * r' * t⁻¹ = r := by
      have h2 := hsq r hrK
      calc t * r' * t⁻¹ = t ^ 2 * r * (t ^ 2)⁻¹ := by rw [hr', pow_two]; group
        _ = r := by rw [h2]; group
    obtain ⟨g, hg⟩ : ∃ g : MulAut V, g = r * r'⁻¹ := ⟨_, rfl⟩
    have hgK : g ∈ K := hg ▸ K.mul_mem hrK (K.inv_mem hr'K)
    obtain ⟨c, hc⟩ : ∃ c : MulAut V, c = ⁅g, y⁆ := ⟨_, rfl⟩
    have hcK : c ∈ K := hc ▸ hdata.commutator_mem hgK hyX
    have hcdef : c = ⁅r, y⁆ * (t * ⁅r, y⁆ * t⁻¹)⁻¹ := by
      rw [hc, hg, hdata.commutator_mul hrK (K.inv_mem hr'K) hyX,
        hdata.commutator_inv hr'K hyX, hr', hconj]
    have hc1 : c ≠ 1 := by
      intro h1
      apply hrt
      rw [hcdef] at h1
      have h2 : ⁅r, y⁆ = t * ⁅r, y⁆ * t⁻¹ := mul_inv_eq_one.mp h1
      calc t * ⁅r, y⁆ = (t * ⁅r, y⁆ * t⁻¹) * t := by group
        _ = ⁅r, y⁆ * t := by rw [← h2]
    have htc : t * c * t⁻¹ = c⁻¹ := by
      have e1 : t * g * t⁻¹ = g⁻¹ := by
        calc t * g * t⁻¹ = (t * r * t⁻¹) * (t * r' * t⁻¹)⁻¹ := by rw [hg]; group
          _ = r' * r⁻¹ := by rw [hr'r, ← hr']
          _ = g⁻¹ := by rw [hg]; group
      calc t * c * t⁻¹ = ⁅t * g * t⁻¹, y⁆ := by rw [hc, hconj]
        _ = ⁅g⁻¹, y⁆ := by rw [e1]
        _ = c⁻¹ := by rw [hc]; exact hdata.commutator_inv hgK hyX
    set W : Subgroup V := commV (Subgroup.zpowers c) with hW
    have hWcard : Nat.card ↥W ≤ 16 := by
      have := hdata.card_commV_commutator_le (r := g) hyY
      rwa [← hc] at this
    have hcstab : c ∈ stabV W := le_stabV_commV _ (Subgroup.mem_zpowers c)
    have htnorm : t ∈ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup (MulAut V)) :
        Set (MulAut V)) := by
      refine mem_normalizer_of_conj_mem (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have : t * c ^ k * t⁻¹ = c⁻¹ ^ k := by rw [← htc, conj_zpow]
        rw [this]
        exact (Subgroup.zpowers c).zpow_mem ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c)) k
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have h1 : t⁻¹ * c * t = c⁻¹ := by
          have : c = t⁻¹ * c⁻¹ * t := by rw [← htc]; group
          have h2 : c⁻¹ = t⁻¹ * c * t := by
            conv_lhs => rw [this]
            group
          exact h2.symm
        have : t⁻¹ * c ^ k * t = c⁻¹ ^ k := by
          rw [← h1]
          have := conj_zpow (a := t⁻¹) (b := c) (i := k)
          simpa using this.symm
        rw [this]
        exact (Subgroup.zpowers c).zpow_mem ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c)) k
    have htstab : t ∈ stabV W := mem_stabV_commV htnorm
    let z : MulAut ↥W := resStab W ⟨c, hcstab⟩
    let s : MulAut ↥W := resStab W ⟨t, htstab⟩
    have hWelem : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using h.elem w)
    have hcodd : Odd (orderOf c) := odd_orderOf_of_isPGroup_seven hK7 hcK
    have hz1 : z ≠ 1 := by
      intro hz
      apply hc1
      apply eq_one_of_trivial_on_commV h.elem (X := Subgroup.zpowers c) (Subgroup.mem_zpowers c)
        hcodd
      intro w hw
      have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : V)) hz
      simpa [z, resStab_apply] using this
    have hz7 : z ^ 7 = 1 := by
      obtain ⟨k, hk⟩ := hK7 ⟨c, hcK⟩
      have hck : c ^ 7 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hzk : z ^ 7 ^ k = 1 := by
        have : (⟨c, hcstab⟩ : ↥(stabV W)) ^ 7 ^ k = 1 := Subtype.ext (by simpa using hck)
        show (resStab W ⟨c, hcstab⟩) ^ 7 ^ k = 1
        rw [← map_pow, this, map_one]
      have hdvd7 : orderOf z ∣ 7 ^ k := orderOf_dvd_of_pow_eq_one hzk
      have hdvd20160 : orderOf z ∣ 20160 :=
        (orderOf_dvd_natCard z).trans (card_mulAut_dvd_of_card_le_sixteen hWelem hWcard)
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hdvd7
      have hcop : Nat.Coprime (orderOf z) 2880 := by
        rw [hj]
        exact Nat.Coprime.pow_left j (by norm_num)
      have : orderOf z ∣ 7 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd20160)
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have hsz : s * z * s⁻¹ = z⁻¹ := by
      have e : (⟨t, htstab⟩ * ⟨c, hcstab⟩ * ⟨t, htstab⟩⁻¹ : ↥(stabV W)) = ⟨c, hcstab⟩⁻¹ :=
        Subtype.ext (by simpa using htc)
      have := congrArg (resStab W) e
      simp only [map_mul, map_inv] at this
      exact this
    exact no_inversion_of_order_seven hWelem hWcard hz7 hz1 hsz

end Sec5Hyp

end CFSG.CGT.PushingUpLit.CGT6
