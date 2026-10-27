module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Fusion
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Holt.TwoGroups
import CFSG.GH74.GLS.C3.Layer1.Th2P72cR28F
import CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution
import CFSG.Holt.Fixed

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.SixOne

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits
open CFSG.Holt (cyclic_or_dihedral_or_semidihedral_or_quaternion_of_no_normal_four)
open CFSG.GH74.GLS.Th2.R714Dsd (card_centralizer_le_four_of_model)
open CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution
  (eq_of_orderOf_eq_two_of_isCyclic eq_of_orderOf_eq_two_of_quaternion)

variable {G : Type} [Group G] {t u : G}

theorem inv_mul_mem_subgroupOf_of_conj_eq {P : Subgroup G} {w : G} {α β : P}
    (h : (α : G) * w * (α : G)⁻¹ = (β : G) * w * (β : G)⁻¹) :
    α⁻¹ * β ∈ (centralizer ({w} : Set G)).subgroupOf P := by
  rw [Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff, Subgroup.coe_mul, Subgroup.coe_inv]
  calc (α : G)⁻¹ * β * w = (α : G)⁻¹ * ((β : G) * w * (β : G)⁻¹) * β := by group
    _ = (α : G)⁻¹ * ((α : G) * w * (α : G)⁻¹) * β := by rw [h]
    _ = w * ((α : G)⁻¹ * β) := by group

variable [Finite G]

theorem card_inf_centralizer_conj_le (h : SecTwoHyp G t u) {P : Subgroup G} (hP : IsPGroup 2 P)
    (g : G) : Nat.card (centralizer ({g * t * g⁻¹} : Set G) ⊓ P :) ≤ 8 := by
  let D : Subgroup G := centralizer ({g * t * g⁻¹} : Set G) ⊓ P
  let f : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hD2 : IsPGroup 2 D := hP.to_le inf_le_right
  have hDt : D.map f ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp hx.1
    change g⁻¹ * x * g⁻¹⁻¹ * t = t * (g⁻¹ * x * g⁻¹⁻¹)
    calc g⁻¹ * x * g⁻¹⁻¹ * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h1]
      _ = t * (g⁻¹ * x * g⁻¹⁻¹) := by group
  obtain ⟨c, -, hc⟩ := secTwo_exists_conj_le h.sylow hDt (hD2.map f)
  let f' : G →* G := (MulAut.conj c).toMonoidHom
  have hf' : Function.Injective f' := (MulAut.conj c).injective
  have hle : (D.map f).map f' ≤ secTwoR t u := by
    rintro _ ⟨y, hy, rfl⟩
    exact hc y hy
  calc Nat.card D = Nat.card ((D.map f).map f') := by
        rw [Subgroup.card_map_of_injective hf', Subgroup.card_map_of_injective hf]
    _ ≤ Nat.card (secTwoR t u) := Subgroup.card_le_of_le hle
    _ ≤ 8 := h.card_R_le

theorem relIndex_centralizer_le_card {P : Subgroup G} {w : G} (S : Set G)
    (hS : ∀ p ∈ P, p * w * p⁻¹ ∈ S) : (centralizer ({w} : Set G)).relIndex P ≤ Nat.card S := by
  let C : Subgroup P := (centralizer ({w} : Set G)).subgroupOf P
  let f : P ⧸ C → S := fun c =>
    ⟨((Quotient.out c : P) : G) * w * ((Quotient.out c : P) : G)⁻¹, hS _ (Quotient.out c).2⟩
  have hf : Function.Injective f := fun a b hab =>
    calc a = ((Quotient.out a : P) : P ⧸ C) := (QuotientGroup.out_eq' a).symm
      _ = ((Quotient.out b : P) : P ⧸ C) :=
          QuotientGroup.eq.mpr (inv_mul_mem_subgroupOf_of_conj_eq (congrArg Subtype.val hab))
      _ = b := QuotientGroup.out_eq' b
  exact Nat.card_le_card_of_injective f hf

theorem relIndex_le_two {P K : Subgroup G} (hP : IsPGroup 2 P) (h3 : K.relIndex P ≤ 3) :
    K.relIndex P ≤ 2 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hn ▸ K.relIndex_dvd_card P)
  by_cases hk2 : 2 ≤ k
  · have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  · interval_cases k <;> omega

theorem relIndex_centralizer_le_two {P V : Subgroup G} (hP : IsPGroup 2 P)
    (hVn : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) (hV4 : Nat.card V = 4) {w : G} (hwV : w ∈ V)
    (hw1 : w ≠ 1) : (centralizer ({w} : Set G)).relIndex P ≤ 2 := by
  have hS : ∀ p ∈ P, p * w * p⁻¹ ∈ ((V : Set G) \ {1}) := by
    intro p hp
    refine ⟨hVn p hp w hwV, ?_⟩
    intro h1
    apply hw1
    have h1' : p * w * p⁻¹ = 1 := h1
    calc w = p⁻¹ * (p * w * p⁻¹) * p := by group
      _ = 1 := by rw [h1']; group
  have hScard : Nat.card ((V : Set G) \ {1} : Set G) = 3 := by
    have h4 : (V : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hV4
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem V.one_mem, h4]
  have h3 := relIndex_centralizer_le_card _ hS
  rw [hScard] at h3
  exact relIndex_le_two hP h3

theorem card_le_sixteen (h : SecTwoHyp G t u) {P : Subgroup G} (hP : IsPGroup 2 P)
    {V : Subgroup G} (hVn : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) (hV4 : Nat.card V = 4) {g : G}
    (hgV : g * t * g⁻¹ ∈ V) : Nat.card P ≤ 16 := by
  have hw1 : g * t * g⁻¹ ≠ 1 := by
    intro h1
    apply h.t_ne_one
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have h2 := relIndex_centralizer_le_two hP hVn hV4 hgV hw1
  have h8 := card_inf_centralizer_conj_le h hP g
  calc Nat.card P = (centralizer ({g * t * g⁻¹} : Set G)).relIndex P *
        Nat.card (centralizer ({g * t * g⁻¹} : Set G) ⊓ P :) :=
        (Subgroup.relIndex_mul_card _ _).symm
    _ ≤ 2 * 8 := Nat.mul_le_mul h2 h8
    _ = 16 := rfl

theorem eight_le_card_centralizer (h : SecTwoHyp G t u) {P : Subgroup G} (hRP : secTwoR t u ≤ P)
    {tP : P} (htP : (tP : G) = t) : 8 ≤ Nat.card (centralizer ({tP} : Set P)) := by
  have hle : (secTwoR t u).subgroupOf P ≤ centralizer ({tP} : Set P) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, htP]; exact
      h.commute_t_of_mem_R hr)
  calc 8 = Nat.card (secTwoR t u) := (card_R_eq h).symm
    _ = Nat.card ((secTwoR t u).subgroupOf P) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv).symm
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem exists_normal_four (h : SecTwoHyp G t u) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hRP : secTwoR t u ≤ P) :
    ∃ V : Subgroup G, V ≤ P ∧ (∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) ∧ IsElemAbelian 2 V ∧
      Nat.card V = 4 := by
  by_contra hno
  have hno' : ∀ V : Subgroup P, V.Normal → IsElemAbelian 2 V → Nat.card V ≠ 4 := by
    intro V hVn hVe hV4
    refine hno ⟨V.map P.subtype, Subgroup.map_subtype_le V, ?_,
      CFSG.Open.IsElemAbelian.map hVe P.subtype, ?_⟩
    · rintro p hp _ ⟨v, hv, rfl⟩
      exact ⟨⟨p, hp⟩ * v * ⟨p, hp⟩⁻¹, hVn.conj_mem v hv ⟨p, hp⟩, rfl⟩
    · rw [Subgroup.card_map_of_injective P.subtype_injective, hV4]
  have hG := cyclic_or_dihedral_or_semidihedral_or_quaternion_of_no_normal_four (P := P) hP hno'
  obtain ⟨tP, htP⟩ : ∃ tP : P, (tP : G) = t := ⟨⟨t, hRP SecTwoHyp.t_mem_R⟩, rfl⟩
  obtain ⟨zP, hzP⟩ : ∃ zP : P, (zP : G) = u ^ 2 :=
    ⟨⟨u ^ 2, hRP (pow_mem SecTwoHyp.u_mem_R 2)⟩, rfl⟩
  have htP2 : orderOf tP = 2 := by
    rw [← Subgroup.orderOf_coe, htP]
    exact h.orderOf_t
  have hzP2 : orderOf zP = 2 := by
    rw [← Subgroup.orderOf_coe, hzP]
    exact h.orderOf_z
  have htz : tP ≠ zP := fun h1 => h.sq_ne (by rw [← hzP, ← htP, h1])
  have hcent : Nat.card (centralizer ({tP} : Set P)) ≤ 4 → False := fun h4 => by
    have := eight_le_card_centralizer h hRP htP
    omega
  have h8 : 8 ≤ Nat.card P := by
    calc 8 = Nat.card (secTwoR t u) := (card_R_eq h).symm
      _ ≤ Nat.card P := Subgroup.card_le_of_le hRP
  have hzc : ∀ s : P, s * zP = zP * s := fun s =>
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hzP]; exact h.z_mem_center hP hRP s.2)
  have hz2 : zP * zP = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, hzP, ← sq]
    exact h.z_sq)
  have hz1 : zP ≠ 1 := fun h1 => h.z_ne_one (by rw [← hzP, h1]; rfl)
  have ht2 : tP * tP = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, htP]
    exact h.t_mul_t)
  have ht1 : tP ≠ 1 := fun h1 => h.t_ne_one (by rw [← htP, h1]; rfl)
  rcases hG with hcyc | ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
  · have := hcyc
    exact htz (eq_of_orderOf_eq_two_of_isCyclic htP2 hzP2)
  · exact hcent (card_centralizer_le_four_of_model zP tP hzc hz2 hz1 ht2 ht1 htz h8
      (Or.inl ⟨m, hm, ⟨e⟩⟩))
  · exact hcent (card_centralizer_le_four_of_model zP tP hzc hz2 hz1 ht2 ht1 htz h8
      (Or.inr ⟨n, hn, ⟨e⟩⟩))
  · have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    exact htz (eq_of_orderOf_eq_two_of_quaternion e htP2 hzP2)

end CFSG.LocalAnalysis.EvenBN.Tits.I21.SixOne

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_six_two_a_one (h : SecTwoHyp G t u) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hRP : secTwoR t u ≤ P) :
    ((∃ V : Subgroup G, V ≤ P ∧ (∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) ∧ IsElemAbelian 2 V ∧
        Nat.card V = 4 ∧ ∃ v ∈ V, ∃ g : G, g * t * g⁻¹ = v) ∧ Nat.card P ≤ 16) ∨
    ((∀ W : Subgroup G, W ≤ P → (∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ ∈ W) → IsElemAbelian 2 W →
        Nat.card W = 4 → ∀ w ∈ W, ∀ g : G, g * t * g⁻¹ ≠ w) ∧
      ∃ V : Subgroup G, V ≤ P ∧ (∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) ∧ IsElemAbelian 2 V ∧
        Nat.card V = 4) := by
  by_cases hY : ∃ V : Subgroup G, V ≤ P ∧ (∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V) ∧
      IsElemAbelian 2 V ∧ Nat.card V = 4 ∧ ∃ v ∈ V, ∃ g : G, g * t * g⁻¹ = v
  · left
    obtain ⟨V, hVP, hVn, hVe, hV4, v, hv, g, hg⟩ := hY
    exact ⟨⟨V, hVP, hVn, hVe, hV4, v, hv, g, hg⟩,
      I21.SixOne.card_le_sixteen h hP hVn hV4 (hg ▸ hv)⟩
  · right
    exact ⟨fun W hWP hWn hWe hW4 w hw g hg => hY ⟨W, hWP, hWn, hWe, hW4, w, hw, g, hg⟩,
      I21.SixOne.exists_normal_four h hP hRP⟩

end CFSG.LocalAnalysis.EvenBN.Tits
