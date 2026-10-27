module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.OuterStructure
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.TransferFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.OneClass

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup MulAction CFSG.RankThree.Transfer
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

@[instance_reducible] def invAction (L P : Subgroup G) (hP : ∀ p ∈ P, p ∈ normalizer (L : Set G)) :
    MulAction P {x : G // x ∈ L ∧ x * x = 1 ∧ x ≠ 1} where
  smul p x := ⟨(p : G) * x.1 * (p : G)⁻¹,
    (mem_normalizer_iff.1 (hP p p.2) x.1).1 x.2.1,
    by
      calc (p : G) * x.1 * (p : G)⁻¹ * ((p : G) * x.1 * (p : G)⁻¹)
          = (p : G) * (x.1 * x.1) * (p : G)⁻¹ := by group
        _ = 1 := by rw [x.2.2.1]; group,
    fun h => x.2.2.2 (by
      have : x.1 = (p : G)⁻¹ * ((p : G) * x.1 * (p : G)⁻¹) * (p : G) := by group
      rw [this, h]; group)⟩
  one_smul x := Subtype.ext (by
    show ((1 : P) : G) * x.1 * ((1 : P) : G)⁻¹ = x.1
    simp)
  mul_smul p q x := Subtype.ext (by
    show ((p * q : P) : G) * x.1 * ((p * q : P) : G)⁻¹ =
      (p : G) * ((q : G) * x.1 * (q : G)⁻¹) * (p : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

theorem odd_card_fixed_involutions [Finite G] (hLeven : Even (Nat.card L)) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPn : ∀ p ∈ P, p ∈ normalizer (L : Set G)) :
    Odd (Nat.card {w : G // w ∈ L ∧ w * w = 1 ∧ w ≠ 1 ∧ ∀ p ∈ P, p * w = w * p}) := by
  classical
  let _inst := invAction L P hPn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints {x : G // x ∈ L ∧ x * x = 1 ∧ x ≠ 1}
  have hodd : Odd (Nat.card {x : G // x ∈ L ∧ x * x = 1 ∧ x ≠ 1}) := by
    have h := M23Std.odd_card_involutions hLeven
    have e : {x : G // x ∈ L ∧ x * x = 1 ∧ x ≠ 1} ≃ {x : L // x * x = 1 ∧ x ≠ 1} :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (by simpa using x.2.2.1),
          fun h => x.2.2.2 (congrArg Subtype.val h)⟩
        invFun := fun x => ⟨x.1.1, x.1.2, by simpa using congrArg Subtype.val x.2.1,
          fun h => x.2.2 (Subtype.ext h)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rwa [Nat.card_congr e]
  have hfix : Nat.card (fixedPoints P {x : G // x ∈ L ∧ x * x = 1 ∧ x ≠ 1}) =
      Nat.card {w : G // w ∈ L ∧ w * w = 1 ∧ w ≠ 1 ∧ ∀ p ∈ P, p * w = w * p} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2.1, x.1.2.2.2, fun p hp => by
          have := congrArg Subtype.val (mem_fixedPoints.1 x.2 ⟨p, hp⟩)
          have h2 : p * x.1.1 * p⁻¹ = x.1.1 := this
          calc p * x.1.1 = p * x.1.1 * p⁻¹ * p := by group
            _ = x.1.1 * p := by rw [h2]⟩
        invFun := fun w => ⟨⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1⟩, mem_fixedPoints.2 fun p =>
          Subtype.ext (by
            show (p : G) * w.1 * (p : G)⁻¹ = w.1
            rw [w.2.2.2.2 p p.2]; group)⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
  rw [← hfix]
  have h2 : Nat.card {x : G // x ∈ L ∧ x * x = 1 ∧ x ≠ 1} % 2 =
      Nat.card (fixedPoints P {x : G // x ∈ L ∧ x * x = 1 ∧ x ≠ 1}) % 2 := hmod
  rw [Nat.odd_iff] at hodd ⊢
  omega

section Fusion

variable [Finite G]

theorem exists_fixed_coset_mul_mem [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : OuterSetup G L t) {u : G} (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    {H : Subgroup G} (hH : ∀ x, x ∈ H ↔ x * u = u * x) (htu : t ∈ H)
    (φ : H →* Multiplicative (ZMod 2)) (hφ : φ ⟨t, htu⟩ ≠ 1)
    {P : Subgroup G} (hPM : P ≤ centralizer ({t} : Set G)) (hP : IsPGroup 2 P)
    (hodd : ¬ 2 ∣ P.relIndex (centralizer ({t} : Set G))) (htP : t ∈ P) :
    ∃ x : G, (∀ p ∈ P, x⁻¹ * p * x ∈ H) ∧ x * u * x⁻¹ * t ∈ L := by
  classical
  by_contra hno
  push Not at hno
  have hPt : ∀ p ∈ P, p * t = t * p := fun p hp => mem_centralizer_singleton_iff.1 (hPM hp)
  have : Fintype (fixedPoints P (G ⧸ H)) := Fintype.ofFinite _
  have hev := even_card_fixed_ne_one hnonab S.t_sq hP htP hPt φ
  have hPn : ∀ p ∈ P, p ∈ normalizer (L : Set G) := fun p hp => S.norm p (hPt p hp)
  have hLeven : Even (Nat.card L) := by rw [S.card_L]; decide
  have hodd' := odd_card_fixed_involutions hLeven hP hPn
  have hct : ∀ c ∈ L, c⁻¹ * t * c = t := fun c hc => by
    rw [mul_assoc, S.t_comm c hc]; group
  have hcc : ∀ w : {w : G // w ∈ L ∧ w * w = 1 ∧ w ≠ 1 ∧ ∀ p ∈ P, p * w = w * p},
      ∃ c ∈ L, w.1 = c * u * c⁻¹ := fun w =>
    S.one_class u hu w.1 w.2.1 hu2 w.2.2.1 hu1 w.2.2.2.1
  choose cc hccL hccw using hcc
  have hfix : ∀ w : {w : G // w ∈ L ∧ w * w = 1 ∧ w ≠ 1 ∧ ∀ p ∈ P, p * w = w * p},
      (((cc w : G)) : G ⧸ H) ∈ fixedPoints P (G ⧸ H) := by
    intro w
    rw [coe_mem_fixedPoints_iff]
    intro p hp
    have hpw := w.2.2.2.2 p hp
    rw [hccw w] at hpw
    show (cc w)⁻¹ * p * cc w ∈ H
    rw [hH]
    calc ((cc w)⁻¹ * p * cc w) * u = (cc w)⁻¹ * (p * (cc w * u * (cc w)⁻¹)) * cc w := by group
      _ = (cc w)⁻¹ * ((cc w * u * (cc w)⁻¹) * p) * cc w := by rw [hpw]
      _ = u * ((cc w)⁻¹ * p * cc w) := by group
  have hval : ∀ w : {w : G // w ∈ L ∧ w * w = 1 ∧ w ≠ 1 ∧ ∀ p ∈ P, p * w = w * p},
      cosetValue φ t (((cc w : G)) : G ⧸ H) ≠ 1 := by
    intro w
    have hx : (cc w)⁻¹ * t * cc w ∈ H := by rw [hct _ (hccL w)]; exact htu
    rw [cosetValue_coe φ hx]
    have : (⟨(cc w)⁻¹ * t * cc w, hx⟩ : H) = ⟨t, htu⟩ := Subtype.ext (hct _ (hccL w))
    rw [this]
    exact hφ
  let f : {w : G // w ∈ L ∧ w * w = 1 ∧ w ≠ 1 ∧ ∀ p ∈ P, p * w = w * p} →
      {X : fixedPoints P (G ⧸ H) // cosetValue φ t X ≠ 1} :=
    fun w => ⟨⟨(((cc w : G)) : G ⧸ H), hfix w⟩, hval w⟩
  have hinj : Function.Injective f := by
    intro w w' hww'
    have h1 : (((cc w : G)) : G ⧸ H) = (((cc w' : G)) : G ⧸ H) :=
      congrArg (fun y => (y.1 : G ⧸ H)) hww'
    have h2 := QuotientGroup.eq.1 h1
    have hd : ((cc w)⁻¹ * cc w') * u = u * ((cc w)⁻¹ * cc w') := (hH _).1 h2
    apply Subtype.ext
    rw [hccw w, hccw w']
    calc cc w * u * (cc w)⁻¹
        = cc w * (u * ((cc w)⁻¹ * cc w') * ((cc w)⁻¹ * cc w')⁻¹) * (cc w)⁻¹ := by group
      _ = cc w * (((cc w)⁻¹ * cc w') * u * ((cc w)⁻¹ * cc w')⁻¹) * (cc w)⁻¹ := by rw [hd]
      _ = cc w' * u * (cc w')⁻¹ := by group
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨X, hX⟩, hv⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective X
    have hX' := (coe_mem_fixedPoints_iff x).1 hX
    have hwP : ∀ p ∈ P, p * (x * u * x⁻¹) = (x * u * x⁻¹) * p := by
      intro p hp
      have h := (hH _).1 (hX' p hp)
      calc p * (x * u * x⁻¹) = x * ((x⁻¹ * p * x) * u) * x⁻¹ := by group
        _ = x * (u * (x⁻¹ * p * x)) * x⁻¹ := by rw [h]
        _ = (x * u * x⁻¹) * p := by group
    have hw2 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
      calc (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hw1 : x * u * x⁻¹ ≠ 1 := by
      intro h
      apply hu1
      calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    have hwL : x * u * x⁻¹ ∈ L := by
      rcases S.mem_or_mul_mem hPM hP hodd htP hwP hw2 with h | h
      · exact h
      · exact (hno x hX' h).elim
    refine ⟨⟨x * u * x⁻¹, hwL, hw2, hw1, hwP⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show (((cc ⟨x * u * x⁻¹, hwL, hw2, hw1, hwP⟩ : G)) : G ⧸ H) = (x : G ⧸ H)
    apply QuotientGroup.eq.2
    rw [hH]
    have hc := hccw ⟨x * u * x⁻¹, hwL, hw2, hw1, hwP⟩
    simp only at hc
    set c := cc ⟨x * u * x⁻¹, hwL, hw2, hw1, hwP⟩
    calc (c⁻¹ * x) * u = c⁻¹ * (x * u * x⁻¹) * x := by group
      _ = c⁻¹ * (c * u * c⁻¹) * x := by rw [← hc]
      _ = u * (c⁻¹ * x) := by group
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [hcard] at hodd'
  exact (Nat.not_even_iff_odd.2 hodd') hev

end Fusion

theorem false_of_hom_nonzero [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : OuterSetup G L t) {u : G} (hu : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (htu : t ∈ centralizer ({u} : Set G))
    (φ : centralizer ({u} : Set G) →* Multiplicative (ZMod 2)) (hφ : φ ⟨t, htu⟩ ≠ 1) :
    False := by
  classical
  obtain ⟨P, hPM, hP, htP, hodd⟩ := S.exists_sylow
  have hPt : ∀ p ∈ P, p * t = t * p := fun p hp => mem_centralizer_singleton_iff.1 (hPM hp)
  have htM : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hcomm : commutator ↥(centralizer ({t} : Set G)) ≤
      L.subgroupOf (centralizer ({t} : Set G)) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show ((⁅a, b⁆ : centralizer ({t} : Set G)) : G) ∈ L
    have : ((⁅a, b⁆ : centralizer ({t} : Set G)) : G) = ⁅(a : G), (b : G)⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact S.comm_mem (mem_centralizer_singleton_iff.1 a.2) (mem_centralizer_singleton_iff.1 b.2)
  have hψ : (Abelianization.of : centralizer ({t} : Set G) →* _) ⟨t, htM⟩ ≠ 1 := by
    intro h
    have h2 : (⟨t, htM⟩ : centralizer ({t} : Set G)) ∈
        commutator ↥(centralizer ({t} : Set G)) := (QuotientGroup.eq_one_iff _).1 h
    exact S.t_not_mem (hcomm h2)
  obtain ⟨g, hgt, hgP⟩ := exists_conj_ne_centralizing hnonab S.t_sq hP htP hPt
    (Abelianization.of : centralizer ({t} : Set G) →* _) hψ
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right S.t_sq
  have hv2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [S.t_sq]; group
  have hv1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply S.t_ne
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hconj_tu : ¬ IsConj t u := S.not_isConj hu hu2 hu1
  rcases S.mem_or_mul_mem hPM hP hodd htP hgP hv2 with hvL | hvtL
  · exact S.not_isConj hvL hv2 hv1 (isConj_iff.2 ⟨g, rfl⟩)
  have hvt : t * (g * t * g⁻¹) = (g * t * g⁻¹) * t := hgP t htP
  have hl₀2 : (g * t * g⁻¹ * t) * (g * t * g⁻¹ * t) = 1 := by
    calc (g * t * g⁻¹ * t) * (g * t * g⁻¹ * t)
        = (g * t * g⁻¹) * (t * (g * t * g⁻¹)) * t := by group
      _ = (g * t * g⁻¹) * ((g * t * g⁻¹) * t) * t := by rw [hvt]
      _ = ((g * t * g⁻¹) * (g * t * g⁻¹)) * (t * t) := by group
      _ = 1 := by rw [hv2, S.t_sq, mul_one]
  have hl₀1 : g * t * g⁻¹ * t ≠ 1 := by
    intro h
    apply hgt
    calc g * t * g⁻¹ = (g * t * g⁻¹ * t) * t⁻¹ := by group
      _ = t := by rw [h, hti, one_mul]
  obtain ⟨x, hxP, hxL⟩ := exists_fixed_coset_mul_mem hnonab S hu hu2 hu1
    (H := centralizer ({u} : Set G)) (fun _ => mem_centralizer_singleton_iff) htu φ hφ hPM hP hodd
    htP
  have hwP : ∀ p ∈ P, p * (x * u * x⁻¹) = (x * u * x⁻¹) * p := by
    intro p hp
    have h := mem_centralizer_singleton_iff.1 (hxP p hp)
    calc p * (x * u * x⁻¹) = x * ((x⁻¹ * p * x) * u) * x⁻¹ := by group
      _ = x * (u * (x⁻¹ * p * x)) * x⁻¹ := by rw [h]
      _ = (x * u * x⁻¹) * p := by group
  have hw2 : (x * u * x⁻¹) * (x * u * x⁻¹) = 1 := by
    calc (x * u * x⁻¹) * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hwt : t * (x * u * x⁻¹) = (x * u * x⁻¹) * t := hwP t htP
  have hl₁2 : (x * u * x⁻¹ * t) * (x * u * x⁻¹ * t) = 1 := by
    calc (x * u * x⁻¹ * t) * (x * u * x⁻¹ * t)
        = (x * u * x⁻¹) * (t * (x * u * x⁻¹)) * t := by group
      _ = (x * u * x⁻¹) * ((x * u * x⁻¹) * t) * t := by rw [hwt]
      _ = ((x * u * x⁻¹) * (x * u * x⁻¹)) * (t * t) := by group
      _ = 1 := by rw [hw2, S.t_sq, mul_one]
  have hl₁1 : x * u * x⁻¹ * t ≠ 1 := by
    intro h
    apply hconj_tu
    refine isConj_iff.2 ⟨x⁻¹, ?_⟩
    have hwt' : x * u * x⁻¹ = t := by
      calc x * u * x⁻¹ = (x * u * x⁻¹ * t) * t⁻¹ := by group
        _ = t := by rw [h, hti, one_mul]
    calc x⁻¹ * t * x⁻¹⁻¹ = x⁻¹ * (x * u * x⁻¹) * x := by rw [hwt']; group
      _ = u := by group
  obtain ⟨c, hcL, hc⟩ := S.one_class (g * t * g⁻¹ * t) hvtL (x * u * x⁻¹ * t) hxL hl₀2 hl₁2
    hl₀1 hl₁1
  have hwc : x * u * x⁻¹ = c * (g * t * g⁻¹) * c⁻¹ := by
    have h1 : x * u * x⁻¹ * t = (c * (g * t * g⁻¹) * c⁻¹) * t := by
      rw [hc]
      calc c * (g * t * g⁻¹ * t) * c⁻¹ = c * (g * t * g⁻¹) * (t * c⁻¹) := by group
        _ = c * (g * t * g⁻¹) * (c⁻¹ * t) := by rw [S.t_comm c⁻¹ (L.inv_mem hcL)]
        _ = (c * (g * t * g⁻¹) * c⁻¹) * t := by group
    exact mul_right_cancel h1
  apply hconj_tu
  refine isConj_iff.2 ⟨x⁻¹ * c * g, ?_⟩
  calc (x⁻¹ * c * g) * t * (x⁻¹ * c * g)⁻¹ = x⁻¹ * (c * (g * t * g⁻¹) * c⁻¹) * x := by group
    _ = x⁻¹ * (x * u * x⁻¹) * x := by rw [← hwc]
    _ = u := by group

end CFSG.EvenSporadicStandard.McLStd
