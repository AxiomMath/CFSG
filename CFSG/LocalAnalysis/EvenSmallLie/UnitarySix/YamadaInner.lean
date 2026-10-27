module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaFacts
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaLocal
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreGW
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernel
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

structure Setting (G : Type) [Group G] [Finite G] (L : Subgroup G) (D : ToddParabolic L)
    (t : G) : Prop where
  std : StandardSetting G L
  center_eq : center L = ⊥
  facts : YamadaFacts D
  mem : t ∈ centralizer (L : Set G)
  order : orderOf t = 2

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

@[expose] noncomputable def autH (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G)) :
    centralizer ({t} : Set G) →* MulAut L :=
  L.normalizerMonoidHom.comp (inclusion hHN)

theorem autH_apply (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (h : centralizer ({t} : Set G)) (l : L) : ((autH hHN h l : L) : G) = h * l * (h : G)⁻¹ :=
  L.normalizerMonoidHom_apply_apply_coe _ l

variable [Finite G] {D : ToddParabolic L}

namespace Setting

theorem t_sq (h : Setting G L D t) : t ^ 2 = 1 := by
  rw [← h.order]
  exact pow_orderOf_eq_one t

theorem t_ne_one (h : Setting G L D t) : t ≠ 1 := fun h1 => by
  have := h.order
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem comm (h : Setting G L D t) {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_iff.1 h.mem l hl

theorem le_H (h : Setting G L D t) : L ≤ centralizer ({t} : Set G) := fun _ hl =>
  mem_centralizer_singleton_iff.2 (h.comm hl)

theorem H_le (h : Setting G L D t) : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  centralizer_le_normalizer_of_standard h.std.standard h.mem h.order

theorem eq_one_of_mem (h : Setting G L D t) {x : G} (hxL : x ∈ L)
    (hxC : x ∈ centralizer (L : Set G)) : x = 1 := by
  have hz : (⟨x, hxL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.1 hxC l l.2)
  rw [h.center_eq, mem_bot] at hz
  exact congrArg Subtype.val hz

theorem t_not_mem (h : Setting G L D t) : t ∉ L := fun htL => h.t_ne_one (h.eq_one_of_mem htL h.mem)

theorem conj_injective (h : Setting G L D t) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro m hm
  rw [MonoidHom.mem_ker] at hm
  have hz : m ∈ center L := by
    rw [mem_center_iff]
    intro l
    have h1 : m * l * m⁻¹ = l := by
      have := congrArg (fun φ : MulAut L => φ l) hm
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc l * m = m * l * m⁻¹ * m := by rw [h1]
      _ = m * l := by group
  rw [h.center_eq] at hz
  exact hz

theorem T_facts (h : Setting G L D t) :
    IsCyclic (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      IsPGroup 2 (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set tC : centralizer (L : Set G) := ⟨t, h.mem⟩ with htCdef
  have htC2 : orderOf tC = 2 := by rw [htCdef, orderOf_mk, h.order]
  have hp : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have htS : tC ∈ (S : Subgroup (centralizer (L : Set G))) := hS (mem_zpowers tC)
  obtain ⟨⟨-, hc, hp2⟩, -⟩ :=
    ComponentClassification.StandardRecognition.standard_cyclic_local_centralizer_kernel_two_group
      h.std.standard S (h.std.isCyclic_sylow S) htS htC2 (h.std.core t h.order)
  exact ⟨hc, hp2⟩

theorem t_mem_T (h : Setting G L D t) :
    t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) :=
  ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩

theorem eq_t_of_mem_T (h : Setting G L D t) {c : G}
    (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) (hc2 : c ^ 2 = 1) :
    c = 1 ∨ c = t := by
  by_cases h1 : c = 1
  · exact Or.inl h1
  right
  have := h.T_facts.1
  have hord : orderOf c = 2 := orderOf_eq_prime hc2 h1
  have := ABGLocalTools.eq_of_orderOf_eq_two_of_isCyclic (a := (⟨c, hc⟩ :
    (centralizer (L : Set G) ⊓ centralizer ({t} : Set G) : Subgroup G))) (b := ⟨t, h.t_mem_T⟩)
    (by rw [orderOf_mk, hord]) (by rw [orderOf_mk, h.order])
  exact congrArg Subtype.val this

omit [Finite G] in
theorem comm_T :
    ∀ a ∈ L, ∀ b ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G), a * b = b * a :=
  fun a ha _ hb => mem_centralizer_iff.1 hb.1 a ha

theorem autH_eq_one_iff (h : Setting G L D t) (x : centralizer ({t} : Set G)) :
    autH h.H_le x = 1 ↔ (x : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro l hl
    have h2 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) h1
    simp only [autH_apply, MulAut.one_apply] at h2
    calc l * x = x * l * (x : G)⁻¹ * x := by rw [h2]
      _ = x * l := by group
  · intro hx
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [autH_apply, MulAut.one_apply, ← mem_centralizer_iff.1 hx l l.2, mul_inv_cancel_right]

theorem inv_mul_mem_T (h : Setting G L D t) (x : centralizer ({t} : Set G)) (m : L)
    (hm : autH h.H_le x = MulAut.conj m) :
    (m : G)⁻¹ * x ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
  have hc : (m : G)⁻¹ * x ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h2 := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : G)) hm
    simp only [autH_apply, MulAut.conj_apply, coe_mul, coe_inv] at h2
    calc l * ((m : G)⁻¹ * x) = (m : G)⁻¹ * (m * l * (m : G)⁻¹) * x := by group
      _ = (m : G)⁻¹ * (x * l * (x : G)⁻¹) * x := by rw [h2]
      _ = (m : G)⁻¹ * x * l := by group
  exact mem_inf.2 ⟨hc, mul_mem (inv_mem (h.le_H m.2)) x.2⟩

theorem exists_conj_iff (h : Setting G L D t) (x : centralizer ({t} : Set G)) :
    (∃ m : L, autH h.H_le x = MulAut.conj m) ↔
      (x : G) ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) := by
  constructor
  · rintro ⟨m, hm⟩
    have e : (x : G) = m * ((m : G)⁻¹ * x) := by group
    rw [e]
    exact mul_mem (mem_sup_left m.2) (mem_sup_right (h.inv_mul_mem_T x m hm))
  · intro hx
    obtain ⟨l, hl, c, hc, hlc⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute comm_T hx
    refine ⟨⟨l, hl⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
    rw [autH_apply, MulAut.conj_apply]
    simp only [coe_mul, coe_inv]
    have hyc : (y : G) * c = c * y := mem_centralizer_iff.1 hc.1 y y.2
    rw [← hlc]
    calc l * c * y * (l * c)⁻¹ = l * (c * y) * c⁻¹ * l⁻¹ := by group
      _ = l * (y * c) * c⁻¹ * l⁻¹ := by rw [hyc]
      _ = l * y * l⁻¹ := by group

theorem relIndex_dvd_six (h : Setting G L D t) :
    (L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))).relIndex
        (centralizer ({t} : Set G)) ∣ 6 ∧
      ((L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))).subgroupOf
        (centralizer ({t} : Set G))).Normal := by
  set ψ := (QuotientGroup.mk' (inner L)).comp (autH h.H_le) with hψ
  have hker : ψ.ker = (L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))).subgroupOf
      (centralizer ({t} : Set G)) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← h.exists_conj_iff, hψ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change autH h.H_le x ∈ (MulAut.conj : L →* MulAut L).range ↔ _
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, hm.symm⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, hm.symm⟩
  constructor
  · rw [relIndex, ← hker, Subgroup.index_ker, ← h.facts.card_outer]
    exact Subgroup.card_subgroup_dvd_card _
  · rw [← hker]
    infer_instance

theorem commutator_commutator_le (h : Setting G L D t) {F : Subgroup G}
    (hF : F ≤ centralizer ({t} : Set G)) :
    ⁅⁅F, F⁆, ⁅F, F⁆⁆ ≤ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) :=
  commutator_commutator_le_of_relIndex_dvd_six (sup_le h.le_H inf_le_right)
    h.relIndex_dvd_six.2 h.relIndex_dvd_six.1 hF

theorem eq_or_eq_mul_t (h : Setting G L D t) {y : G}
    (hy : y ∈ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G))) (hy2 : y ^ 2 = 1) :
    ∃ l ∈ L, l ^ 2 = 1 ∧ (y = l ∨ y = l * t) := by
  obtain ⟨l, hl, c, hc, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute comm_T hy
  have hlc : Commute l c := comm_T l hl c hc
  rw [hlc.mul_pow] at hy2
  have hl2 : l ^ 2 = 1 := by
    have e : l ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hy2
    refine h.eq_one_of_mem (pow_mem hl 2) ?_
    rw [e]
    exact inv_mem (pow_mem hc.1 2)
  rw [hl2, one_mul] at hy2
  rcases h.eq_t_of_mem_T hc hy2 with rfl | rfl
  · exact ⟨l, hl, hl2, Or.inl (mul_one l)⟩
  · exact ⟨l, hl, hl2, Or.inr rfl⟩

end Setting

omit [Finite G] in
theorem card_eq_card_ker_mul_card_range' {X Y : Type*} [Group X] [Group Y] [Finite X]
    (ψ : X →* Y) : Nat.card X = Nat.card ψ.ker * Nat.card ψ.range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem card_le_of_theta' {Q : Type} [Group Q]
    (hconj : Function.Injective (MulAut.conj : Q →* MulAut Q)) {H C : Subgroup G}
    (θ : H →* MulAut Q) (hθ1 : ∀ h : H, θ h = 1 ↔ (h : G) ∈ C)
    (hC2 : ∀ X : Subgroup G, X ≤ C → (∀ x ∈ X, x ^ 2 = 1) → Nat.card X ≤ 2) {τ : H}
    (hrank : ∀ B : Subgroup Q, (∀ b ∈ B, θ τ b = b) → (∀ b ∈ B, b ^ 2 = 1) →
      Nat.card B ≤ 2 ^ 6) {B : Subgroup G} (hBH : B ≤ H)
    (hBτ : ∀ b ∈ B, b * τ = τ * b) (hsq : ∀ b ∈ B, b ^ 2 = 1)
    (hinner : ∀ b (hb : b ∈ B), ∃ q, θ ⟨b, hBH hb⟩ = MulAut.conj q) :
    Nat.card B ≤ 2 * 2 ^ 6 := by
  set ψ : B →* MulAut Q := θ.comp (Subgroup.inclusion hBH)
  have hψ : ∀ b : B, ψ b = θ ⟨b, hBH b.2⟩ := fun b => rfl
  rw [card_eq_card_ker_mul_card_range' ψ]
  refine Nat.mul_le_mul ?_ ?_
  · have h := hC2 (ψ.ker.map B.subtype) (by
      rintro _ ⟨b, hb, rfl⟩
      exact (hθ1 _).1 hb) (by
      rintro _ ⟨b, -, rfl⟩
      exact hsq _ b.2)
    rwa [Subgroup.card_map_of_injective B.subtype_injective] at h
  · set B'' := ψ.range.comap (MulAut.conj : Q →* MulAut Q)
    have hle : ψ.range ≤ (MulAut.conj : Q →* MulAut Q).range := by
      rintro _ ⟨b, rfl⟩
      obtain ⟨q, hq⟩ := hinner b b.2
      exact ⟨q, by rw [hψ, hq]⟩
    have hcard : Nat.card ψ.range = Nat.card B'' := by
      rw [← Subgroup.card_map_of_injective hconj, Subgroup.map_comap_eq_self hle]
    have hconjα : ∀ (α : MulAut Q) (q : Q), α * MulAut.conj q * α⁻¹ = MulAut.conj (α q) :=
      fun α q => MulEquiv.ext fun x => by
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [hcard]
    refine hrank _ (fun q hq => hconj ?_) (fun q hq => hconj ?_)
    · obtain ⟨b, hb⟩ := hq
      rw [← hconjα, ← hb, hψ]
      have hbt : (τ : H) * ⟨b, hBH b.2⟩ * τ⁻¹ = ⟨b, hBH b.2⟩ := by
        refine Subtype.ext ?_
        simp only [coe_mul, coe_inv]
        rw [← hBτ _ b.2, mul_inv_cancel_right]
      rw [← map_inv, ← map_mul, ← map_mul, hbt]
    · obtain ⟨b, hb⟩ := hq
      rw [map_pow, ← hb, hψ, ← map_pow, map_one]
      have : (⟨b, hBH b.2⟩ : H) ^ 2 = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hsq _ b.2)
      rw [this, map_one]

omit [Finite G] in
theorem isPGroup_of_sq {B : Subgroup G} (hsq : ∀ b ∈ B, b ^ 2 = 1) : IsPGroup 2 B :=
  fun b => ⟨1, Subtype.ext (by simpa using hsq _ b.2)⟩

theorem relIndex_le_two_of_dvd_six {H N B : Subgroup G} (hN : (N.subgroupOf H).Normal)
    (h6 : N.relIndex H ∣ 6) (hBH : B ≤ H) (hsq : ∀ b ∈ B, b ^ 2 = 1) : N.relIndex B ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd6 : N.relIndex B ∣ 6 := by
    have h1 := Subgroup.relIndex_dvd_index_of_normal (N.subgroupOf H) (B.subgroupOf H)
    rw [Subgroup.relIndex_subgroupOf hBH] at h1
    exact h1.trans h6
  obtain ⟨n, hn⟩ := (isPGroup_of_sq hsq).exists_card_eq
  have hdB : N.relIndex B ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdB
  rw [hk'] at hd6 ⊢
  have hk1 : k ≤ 1 := by
    by_contra hc
    push Not at hc
    exact absurd ((Nat.pow_dvd_pow 2 hc).trans hd6) (by norm_num)
  calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 2 := by norm_num

namespace Setting

theorem card_le_two_of_le_T (h : Setting G L D t) {X : Subgroup G}
    (hX : X ≤ centralizer (L : Set G) ⊓ centralizer ({t} : Set G))
    (hsq : ∀ x ∈ X, x ^ 2 = 1) : Nat.card X ≤ 2 := by
  have hle : X ≤ zpowers t := fun x hx => by
    rcases h.eq_t_of_mem_T (hX hx) (hsq x hx) with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  calc Nat.card X ≤ Nat.card (zpowers t) := Subgroup.card_le_of_le hle
    _ = 2 := by rw [Nat.card_zpowers, h.order]

theorem card_le_of_not_mem (h : Setting G L D t) {τ : G} (hτ : τ ∈ centralizer ({t} : Set G))
    (hτ2 : τ ^ 2 = 1) (hτF : τ ∉ L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)))
    {B : Subgroup G} (hB : B ≤ centralizer ({t} : Set G) ⊓ centralizer ({τ} : Set G))
    (hsq : ∀ b ∈ B, b ^ 2 = 1) : Nat.card B ≤ 2 ^ 8 := by
  set F := L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) with hFdef
  have hBH : B ≤ centralizer ({t} : Set G) := hB.trans inf_le_left
  have h1 : Nat.card B ≤ 2 * Nat.card (F ⊓ B : Subgroup G) := by
    have e : Nat.card B = Nat.card (F ⊓ B : Subgroup G) * F.relIndex B := by
      rw [← relIndex_bot_left, ← relIndex_bot_left, ← inf_relIndex_right F B,
        relIndex_mul_relIndex _ _ _ bot_le inf_le_right]
    rw [e, mul_comm]
    exact Nat.mul_le_mul_right _
      (relIndex_le_two_of_dvd_six h.relIndex_dvd_six.2 h.relIndex_dvd_six.1 hBH hsq)
  set τH : centralizer ({t} : Set G) := ⟨τ, hτ⟩
  have hττ : autH h.H_le τH * autH h.H_le τH = 1 := by
    rw [← map_mul]
    have : τH * τH = 1 := Subtype.ext (by rw [coe_mul, ← sq, hτ2]; rfl)
    rw [this, map_one]
  have hout : ∀ m : L, autH h.H_le τH ≠ MulAut.conj m := fun m hm =>
    hτF ((h.exists_conj_iff τH).1 ⟨m, hm⟩)
  have h2 : Nat.card (F ⊓ B : Subgroup G) ≤ 2 * 2 ^ 6 := by
    refine card_le_of_theta' h.conj_injective (autH h.H_le)
      (C := centralizer (L : Set G) ⊓ centralizer ({t} : Set G)) (fun x => ?_)
      (fun X hX hX2 => h.card_le_two_of_le_T hX hX2) (τ := τH)
      (fun B' hB' hB'2 => h.facts.rank _ hττ hout B' hB' hB'2)
      (inf_le_right.trans hBH) (fun b hb => ?_) (fun b hb => hsq b hb.2) (fun b hb => ?_)
    · rw [h.autH_eq_one_iff]
      exact ⟨fun hx => ⟨hx, x.2⟩, fun hx => hx.1⟩
    · exact mem_centralizer_singleton_iff.1 (hB hb.2).2
    · exact (h.exists_conj_iff _).2 hb.1
  calc Nat.card B ≤ 2 * Nat.card (F ⊓ B : Subgroup G) := h1
    _ ≤ 2 * (2 * 2 ^ 6) := Nat.mul_le_mul_left 2 h2
    _ = 2 ^ 8 := by norm_num

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
