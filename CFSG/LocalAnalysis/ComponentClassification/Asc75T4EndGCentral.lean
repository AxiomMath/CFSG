module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGNormal
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGPsl

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

section InjOn

variable {G G' : Type*} [Group G] [Group G'] (f : G →* G') {X : Subgroup G}

noncomputable def equivMapOfInjOn (hf : Set.InjOn f X) : X ≃* X.map f :=
  MulEquiv.ofBijective ((f.comp X.subtype).codRestrict (X.map f) fun x => ⟨x, x.2, rfl⟩)
    ⟨fun x y h => Subtype.ext (hf x.2 y.2 (congrArg Subtype.val h)),
      fun ⟨_, x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem card_map_of_injOn (hf : Set.InjOn f X) : Nat.card (X.map f) = Nat.card X :=
  (Nat.card_congr (equivMapOfInjOn f hf).toEquiv).symm

theorem twoPrimeLayerIn_map_of_injOn [Finite G] (hf : Set.InjOn f X) :
    twoPrimeLayerIn (X.map f) = (twoPrimeLayerIn X).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (twoPrimeLayerIn_le (X.map f)) hy
    exact ⟨x, (mem_twoPrimeLayerIn_iff_of_mulEquiv (equivMapOfInjOn f hf) ⟨x, hx⟩).mpr hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_twoPrimeLayerIn_iff_of_mulEquiv (equivMapOfInjOn f hf)
      ⟨x, twoPrimeLayerIn_le X hx⟩).mp hx

theorem oddCoreIn_map_of_injOn [Finite G] (hf : Set.InjOn f X) :
    oddCoreIn (X.map f) = (oddCoreIn X).map f := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (oddCoreIn_le (X.map f)) hy
    exact ⟨x, (mem_oddCoreIn_iff_of_mulEquiv (equivMapOfInjOn f hf) ⟨x, hx⟩).mpr hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_oddCoreIn_iff_of_mulEquiv (equivMapOfInjOn f hf) ⟨x, oddCoreIn_le X hx⟩).mp hx

theorem oUpperTwoPrime_map_of_injOn (hf : Set.InjOn f X) :
    (oUpperTwoPrime X).map f = oUpperTwoPrime (X.map f) := by
  rw [oUpperTwoPrime, oUpperTwoPrime, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, k, hk⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, k, hk⟩
    refine ⟨x, ⟨hx, k, hf (pow_mem hx _) (one_mem X) ?_⟩, rfl⟩
    rw [map_pow, hk, map_one]

end InjOn

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem zpowers_normal_of_mem_center {a : G} (ha : a ∈ center G) : (zpowers a).Normal where
  conj_mem n hn g := by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hn
    have h := mem_center_iff.mp (zpow_mem ha i) g
    rw [h, mul_inv_cancel_right]
    exact hn

theorem mem_sup_zpowers_iff {X : Subgroup G} {a : G} (ha : a ∈ center G) (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) {y : G} : y ∈ X ⊔ zpowers a ↔ y ∈ X ∨ y * a ∈ X := by
  have hN : zpowers a ≤ normalizer (X : Set G) := (zpowers_le).mpr (by
    rw [mem_normalizer_iff]
    intro x
    rw [(mem_center_iff.mp ha x).symm, mul_inv_cancel_right])
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  constructor
  · intro hy
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hN] at hy
    obtain ⟨x, hx, b, hb, rfl⟩ := Set.mem_mul.mp hy
    rcases eq_one_or_eq_of_mem_zpowers ha2 ha1 hb with rfl | rfl
    · left
      rwa [mul_one]
    · right
      rwa [mul_assoc, haa, mul_one]
  · rintro (h | h)
    · exact mem_sup_left h
    · have : y = y * a * a := by rw [mul_assoc, haa, mul_one]
      rw [this]
      exact mul_mem (mem_sup_left h) (mem_sup_right (mem_zpowers a))

omit [Finite G] in
theorem toBar_mem_centralizer_of_mem_center {Q : Subgroup G} {a : G} (ha : a ∈ center G)
    (haN : a ∈ normalizer (Q : Set G)) :
    toBar Q ⟨a, haN⟩ ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) := by
  rw [mem_centralizer_iff]
  intro z _
  obtain ⟨h, rfl⟩ := toBar_surjective Q z
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_center_iff.mp ha h)

omit [Finite G] in
theorem mem_normalizer_of_mem_center {Q : Subgroup G} {a : G} (ha : a ∈ center G) :
    a ∈ normalizer (Q : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [(mem_center_iff.mp ha x).symm, mul_inv_cancel_right]

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem not_mem_of_mem_center {a : G} (ha : a ∈ center G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    a ∉ Q := by
  intro haQ
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ normalizer (Q : Set G) := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hE.main.proper (eq_top_iff.mpr fun x _ => h x)
  apply hg
  refine mem_normalizer_of_le_rightConjugate hE.main.tight ((zpowers_le).mpr haQ) ?_
    ((zpowers_le).mpr ?_)
  · rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
    exact even_two
  · rw [mem_rightConjugate_iff, mem_center_iff.mp ha g, mul_inv_cancel_right]
    exact haQ

omit [Finite G] in
theorem mem_normalizer_of_conj_mem {x v : G} (hvQ : v ∈ Q) (hv2 : v ^ 2 = 1) (hv1 : v ≠ 1)
    (hxv : x * v * x⁻¹ ∈ Q) : x ∈ normalizer (Q : Set G) := by
  have h1 : x * v * x⁻¹ ∈ rightConjugate Q x⁻¹ := by
    rw [mem_rightConjugate_iff, show x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v by group]
    exact hvQ
  have hxv1 : x * v * x⁻¹ ≠ 1 := by
    intro h
    apply hv1
    rw [show v = x⁻¹ * (x * v * x⁻¹) * x by group, h]
    group
  have hxv2 : (x * v * x⁻¹) ^ 2 = 1 := by rw [conj_pow, hv2]; group
  have heven : Even (Nat.card (Q ⊓ rightConjugate Q x⁻¹ : Subgroup G)) := by
    have hz : Nat.card (zpowers (x * v * x⁻¹)) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hxv2 hxv1]
    exact even_iff_two_dvd.mpr (hz ▸ card_dvd_of_le ((zpowers_le).mpr ⟨hxv, h1⟩))
  exact inv_mem_iff.mp (mem_normalizer_of_even_inf hE.main.tight heven)

theorem mem_normalizer_of_conj_le {a : G} (ha : a ∈ center G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    {x : G} (hx : ∀ k ∈ twoPrimeLayerIn Q, x * k * x⁻¹ ∈ Q ⊔ zpowers a) :
    x ∈ normalizer (Q : Set G) := by
  obtain ⟨u, huK, w, hwK, hu, hw, hu1, hw1, huw, huwc⟩ := hE.main.four.exists_commute
  have huQ := twoPrimeLayerIn_le Q huK
  have hwQ := twoPrimeLayerIn_le Q hwK
  rcases (mem_sup_zpowers_iff ha ha2 ha1).mp (hx u huK) with h | h
  · exact hE.mem_normalizer_of_conj_mem huQ hu hu1 h
  rcases (mem_sup_zpowers_iff ha ha2 ha1).mp (hx w hwK) with h' | h'
  · exact hE.mem_normalizer_of_conj_mem hwQ hw hw1 h'
  have huw2 : (u * w) ^ 2 = 1 := by rw [(show Commute u w from huwc).mul_pow, hu, hw, one_mul]
  have huw1 : u * w ≠ 1 := by
    intro h1
    apply huw
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu)
    rw [← hu', eq_inv_of_mul_eq_one_left h1, inv_inv]
  refine hE.mem_normalizer_of_conj_mem (mul_mem huQ hwQ) huw2 huw1 ?_
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hac : ∀ y : G, a * y = y * a := fun y => (mem_center_iff.mp ha y).symm
  have : x * (u * w) * x⁻¹ = (x * u * x⁻¹ * a) * (x * w * x⁻¹ * a) := by
    calc x * (u * w) * x⁻¹ = (x * u * x⁻¹) * (x * w * x⁻¹) := by group
      _ = (x * u * x⁻¹) * (a * a) * (x * w * x⁻¹) := by rw [haa, mul_one]
      _ = (x * u * x⁻¹ * a) * (a * (x * w * x⁻¹)) := by group
      _ = (x * u * x⁻¹ * a) * (x * w * x⁻¹ * a) := by rw [hac]
  rw [this]
  exact mul_mem h h'

theorem tightlyEmbedded_map_mk
    {a : G} (ha : a ∈ center G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    [(zpowers a).Normal] (hinj : Set.InjOn (QuotientGroup.mk' (zpowers a)) Q) :
    TightlyEmbedded (Q.map (QuotientGroup.mk' (zpowers a))) := by
  set π := QuotientGroup.mk' (zpowers a) with hπ
  refine ⟨by rw [card_map_of_injOn π hinj]; exact hE.main.tight.1, fun xb hxb => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zpowers a) xb
  have hxH : x ∉ normalizer (Q : Set G) := fun h => hxb (le_normalizer_map π ⟨x, h, rfl⟩)
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨⟨yb, hyb⟩, hyb2⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Q.map π ⊓ rightConjugate (Q.map π) (π x))) 2 (even_iff_two_dvd.mp hodd)
  rw [Subgroup.orderOf_mk] at hyb2
  obtain ⟨hybQ, hybx⟩ := mem_inf.mp hyb
  obtain ⟨q, hqQ, rfl⟩ := hybQ
  have hq1 : q ≠ 1 := fun h => by rw [h, map_one, orderOf_one] at hyb2; norm_num at hyb2
  have hq2 : q ^ 2 = 1 := by
    have h1 : π (q ^ 2) = π 1 := by rw [map_pow, ← hyb2, pow_orderOf_eq_one, map_one]
    exact hinj (pow_mem hqQ 2) (one_mem Q) h1
  have hxq : x * q * x⁻¹ ∈ Q ⊔ zpowers a := by
    rw [← (QuotientGroup.ker_mk' (zpowers a)), ← comap_map_eq]
    have := (mem_rightConjugate_iff _ _ _).mp hybx
    rw [mem_comap, map_mul, map_mul, map_inv]
    exact this
  have haN := mem_normalizer_of_mem_center (Q := Q) ha
  rcases (mem_sup_zpowers_iff ha ha2 ha1).mp hxq with h | h
  · exact hxH (hE.mem_normalizer_of_conj_mem hqQ hq2 hq1 h)
  ·
    have haQ := hE.not_mem_of_mem_center ha ha2 ha1
    have hac : a * q = q * a := (mem_center_iff.mp ha q).symm
    have hov : IsOverlapInv Q (q * a) := by
      refine ⟨by rw [(show Commute q a from hac.symm).mul_pow, hq2, ha2, one_mul], fun h1 => ?_,
        mul_mem (le_normalizer hqQ) haN, x, hxH, ?_⟩
      · apply haQ
        rw [show a = q⁻¹ * (q * a) by group, h1, mul_one]
        exact inv_mem hqQ
      · rw [mem_rightConjugate_iff]
        have : x * (q * a) * x⁻¹ = x * q * x⁻¹ * a := by
          calc x * (q * a) * x⁻¹ = x * q * (a * x⁻¹) := by group
            _ = x * q * (x⁻¹ * a) := by rw [(mem_center_iff.mp ha x⁻¹).symm]
            _ = x * q * x⁻¹ * a := by group
        rw [this]
        exact h
    apply hE.not_mem_layer_sup_centralizer hov
    have hqbar : toBar Q ⟨q, le_normalizer hqQ⟩ ∈ bar Q (twoPrimeLayerIn Q) := by
      refine hE.mem_layer_of_sq (toBar_mem_bar Q hqQ) ?_
      rw [← map_pow]
      have : (⟨q, le_normalizer hqQ⟩ : normalizer (Q : Set G)) ^ 2 = 1 := Subtype.ext (by
        simpa using hq2)
      rw [this, map_one]
    have : toBar Q ⟨q * a, hov.mem_normalizer⟩ =
        toBar Q ⟨q, le_normalizer hqQ⟩ * toBar Q ⟨a, haN⟩ := by
      rw [← map_mul]
      rfl
    rw [this]
    exact mul_mem_sup hqbar (toBar_mem_centralizer_of_mem_center ha haN)

end EndSetting

namespace MainCounterexample

variable {Q : Subgroup G} (hM : MainCounterexample G Q) (hE : EndSetting Q)
include hM hE

omit hM in
theorem thm4Case3_of_map_mk (M : PSLModel Q) {a : G} (ha : a ∈ center G) (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) [(zpowers a).Normal]
    (h3 : Thm4Case3 (Q.map (QuotientGroup.mk' (zpowers a)))) : Thm4Case3 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (zpowers a) with hπ
  have hker : π.ker = zpowers a := QuotientGroup.ker_mk' (zpowers a)
  have haQ := hE.not_mem_of_mem_center ha ha2 ha1
  have hinjOf : ∀ X : Subgroup G, a ∉ X → Set.InjOn π X := by
    intro X haX y hy y' hy' hyy'
    have h1 : y⁻¹ * y' ∈ zpowers a := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel]
    rcases eq_one_or_eq_of_mem_zpowers ha2 ha1 h1 with h | h
    · exact (inv_mul_eq_one.mp h)
    · exact absurd (h ▸ mul_mem (inv_mem hy) hy') haX
  obtain ⟨gb, hgb, Tb, hTb, hTbN, n, hn, φb, hφb, hkerφb⟩ := h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zpowers a) gb
  have hgH : g ∉ normalizer (Q : Set G) := fun h => hgb (le_normalizer_map π ⟨g, h, rfl⟩)
  have hQg : (rightConjugate Q g).map π = rightConjugate (Q.map π) (π g) := by
    rw [rightConjugate, rightConjugate, map_map, map_map]
    congr 1
  have haQg : a ∉ rightConjugate Q g := by
    rw [mem_rightConjugate_iff, mem_center_iff.mp ha g, mul_inv_cancel_right]
    exact haQ
  have hinjQg := hinjOf _ haQg
  set T := Tb.comap π ⊓ rightConjugate Q g with hT
  have hTmap : T.map π = Tb := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_inf.mp hy).1
    · intro t ht
      have ht' : t ∈ (rightConjugate Q g).map π := hQg ▸ hTb.le ht
      obtain ⟨y, hy, rfl⟩ := ht'
      exact ⟨y, mem_inf.mpr ⟨ht, hy⟩, rfl⟩
  have hTQg : T ≤ rightConjugate Q g := inf_le_right
  have hinjT : Set.InjOn π T := hinjQg.mono hTQg
  have hT2 : IsPGroup 2 T := by
    have h := hTb.isPGroup
    rw [← hTmap] at h
    exact h.of_equiv (equivMapOfInjOn π hinjT).symm
  have hTsyl : IsSylowOf 2 T (rightConjugate Q g) := by
    refine isSylowOf_of_card hTQg ?_
    rw [← card_map_of_injOn π hinjT, hTmap, hTb.card_eq, ← hQg, card_map_of_injOn π hinjQg]
  have hTH : T ≤ normalizer (Q : Set G) := by
    intro y hy
    refine hE.mem_normalizer_of_conj_le ha ha2 ha1 fun q hqK => ?_
    have hq := twoPrimeLayerIn_le Q hqK
    have hyN : π y ∈ normalizer (Q.map π : Set (G ⧸ zpowers a)) :=
      hTbN (show π y ∈ Tb from (mem_inf.mp hy).1)
    have h1 : π (y * q * y⁻¹) ∈ Q.map π := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hyN _).mp ⟨q, hq, rfl⟩
    rw [← hker, ← comap_map_eq]
    exact h1
  have hQT : a ∉ Q ⊔ T := by
    intro haQT
    have hTN' : T ≤ normalizer (Q : Set G) := hTH
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hTN'] at haQT
    obtain ⟨q, hq, t, ht, hqt⟩ := Set.mem_mul.mp haQT
    have htq : t = q⁻¹ * a := by rw [← hqt]; group
    have ht1 : t ≠ 1 := fun h => haQ (by rw [← hqt, h, mul_one]; exact hq)
    have ht2 : t ^ 2 = 1 := M.sq_eq_one_of_isPGroup hE hgH (hTQg ht) (hTH ht)
      (hT2.to_le ((zpowers_le).mpr ht))
    have hov : IsOverlapInv Q t := ⟨ht2, ht1, hTH ht, g, hgH, hTQg ht⟩
    apply hE.not_mem_bar_sup_centralizer hov
    have haN := mem_normalizer_of_mem_center (Q := Q) ha
    have : toBar Q ⟨t, hov.mem_normalizer⟩ =
        (toBar Q ⟨q, le_normalizer hq⟩)⁻¹ * toBar Q ⟨a, haN⟩ := by
      rw [← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp [htq])
    rw [this]
    exact mul_mem_sup (inv_mem (toBar_mem_bar Q hq))
      (toBar_mem_centralizer_of_mem_center ha haN)
  have hinjQT := hinjOf _ hQT
  set U := oUpperTwoPrime (Q ⊔ T) with hU
  have hUmap : U.map π = oUpperTwoPrime (Q.map π ⊔ Tb) := by
    rw [hU, oUpperTwoPrime_map_of_injOn π hinjQT, Subgroup.map_sup, hTmap]
  have hUQT : U ≤ Q ⊔ T := oUpperTwoPrime_le _
  let ρ : U →* oUpperTwoPrime (Q.map π ⊔ Tb) :=
    (π.comp U.subtype).codRestrict (oUpperTwoPrime (Q.map π ⊔ Tb)) fun u => by
    rw [← hUmap]
    exact ⟨u, u.2, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    rw [← hUmap] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨⟨u, hu⟩, rfl⟩
  have hOQ : oddCoreIn (Q.map π) = (oddCoreIn Q).map π :=
    oddCoreIn_map_of_injOn π (hinjOf Q haQ)
  refine ⟨g, hgH, T, hTsyl, hTH, n, hn, φb.comp ρ, hφb.comp hρ, ?_⟩
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hkerφb, mem_subgroupOf,
    mem_subgroupOf, hOQ]
  show π u ∈ (oddCoreIn Q).map π ↔ (u : G) ∈ oddCoreIn Q
  constructor
  · rintro ⟨y, hy, hyu⟩
    have hyQT : y ∈ Q ⊔ T := mem_sup_left (oddCoreIn_le Q hy)
    rw [← hinjQT hyQT (hUQT u.2) hyu]
    exact hy
  · intro hu
    exact ⟨u, hu, rfl⟩

theorem false_of_mem_center
    {a : G} (ha : a ∈ center G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    False := by
  have : (zpowers a).Normal := zpowers_normal_of_mem_center ha
  obtain ⟨M⟩ := hE.nonempty_pslModel
  set π := QuotientGroup.mk' (zpowers a) with hπ
  have hker : π.ker = zpowers a := QuotientGroup.ker_mk' (zpowers a)
  have haQ := hE.not_mem_of_mem_center ha ha2 ha1
  have hinjQ : Set.InjOn π Q := by
    intro y hy y' hy' hyy'
    have h1 : y⁻¹ * y' ∈ zpowers a := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel]
    rcases eq_one_or_eq_of_mem_zpowers ha2 ha1 h1 with h | h
    · exact (inv_mul_eq_one.mp h)
    · exact absurd (h ▸ mul_mem (inv_mem hy) hy') haQ
  have hcard : Nat.card (G ⧸ zpowers a) < Nat.card G := by
    have h := card_eq_card_quotient_mul_card_subgroup (zpowers a)
    rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1] at h
    have hpos : 0 < Nat.card (G ⧸ zpowers a) := Nat.card_pos
    omega
  have htight := hE.tightlyEmbedded_map_mk ha ha2 ha1 hinjQ
  have hKmap : twoPrimeLayerIn (Q.map π) = (twoPrimeLayerIn Q).map π :=
    twoPrimeLayerIn_map_of_injOn π hinjQ
  have hOmap : oddCoreIn (Q.map π) = (oddCoreIn Q).map π := oddCoreIn_map_of_injOn π hinjQ
  have hinjK : Set.InjOn π (twoPrimeLayerIn Q) := hinjQ.mono (twoPrimeLayerIn_le Q)
  have h4 : HasFourGroup (twoPrimeLayerIn (Q.map π)) := by
    obtain ⟨E, hEK, hE2, hE4⟩ := hM.four
    refine ⟨E.map π, hKmap ▸ map_mono hEK, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      rw [← map_pow, hE2 e he, map_one]
    · rw [card_map_of_injOn π (hinjK.mono hEK), hE4]
  have hne : twoPrimeLayerIn (Q.map π) ≠ oddCoreIn (Q.map π) := by
    intro h
    have h1 := odd_card_oddCoreIn (Q.map π)
    rw [← h] at h1
    exact Nat.not_even_iff_odd.mpr h1 h4.even_card
  rcases hM.ih (G ⧸ zpowers a) hcard (Q.map π) htight hne with h1 | h2 | h3
  ·
    apply hM.not_case1
    set W := (twoPrimeLayerIn (⊤ : Subgroup (G ⧸ zpowers a))).comap π with hW
    have hWn : W.Normal := by
      have hn : (twoPrimeLayerIn (⊤ : Subgroup (G ⧸ zpowers a))).Normal :=
        normalizer_eq_top_iff.mp (eq_top_iff.mpr (normalIn_le_normalizer
          (twoPrimeLayerIn_normalIn (⊤ : Subgroup (G ⧸ zpowers a)))))
      exact hn.comap π
    have hKW : twoPrimeLayerIn Q ≤ W := by
      intro k hk
      rw [hW, mem_comap]
      exact h1.1 (hKmap ▸ ⟨k, hk, rfl⟩)
    have hWH : W ≤ normalizer (Q : Set G) := by
      intro w hw
      have hwN : π w ∈ normalizer ((twoPrimeLayerIn (Q.map π) : Set (G ⧸ zpowers a))) :=
        normalIn_le_normalizer h1 hw
      refine hE.mem_normalizer_of_conj_le ha ha2 ha1 fun k hk => ?_
      have h2 : π (w * k * w⁻¹) ∈ (twoPrimeLayerIn Q).map π := by
        rw [map_mul, map_mul, map_inv, ← hKmap]
        exact (mem_normalizer_iff.mp hwN _).mp (hKmap ▸ ⟨k, hk, rfl⟩)
      have h3 : w * k * w⁻¹ ∈ twoPrimeLayerIn Q ⊔ zpowers a := by
        rw [← hker, ← comap_map_eq]
        exact h2
      exact (sup_le_sup_right (twoPrimeLayerIn_le Q) _) h3
    have hKWn : NormalIn (twoPrimeLayerIn Q) W :=
      normalIn_of_le_normalizer hKW (hWH.trans (normalizer_le_normalizer_twoPrimeLayerIn Q))
    have hWtop : NormalIn W ⊤ :=
      normalIn_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hWn])
    exact thm4Case1_of_normalIn_chain hM.tight hM.four hKWn hWtop inferInstance
  · have h : CFSG.Open.pRank 2 (twoPrimeLayerIn (Q.map π)) = 1 := h2
    have := h4.two_le_pRank
    omega
  · exact hM.not_case3 (thm4Case3_of_map_mk hE M ha ha2 ha1 h3)

end MainCounterexample

end CFSG.ComponentClassification.Asc75T4
