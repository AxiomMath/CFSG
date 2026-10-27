module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResCSA6Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResH4Core

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M24Std.CResH4

theorem natCard_subgroupOf_of_le {X : Type*} [Group X] {H K : Subgroup X} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  rw [← Subgroup.card_map_of_injective K.subtype_injective (K := H.subgroupOf K),
    Subgroup.subgroupOf_map_subtype, inf_of_le_left h]

variable {X : Type} [Group X] [Finite X] {ζ : X}

theorem normal_map_inf_centralizer {E : Subgroup X} [E.Normal]
    (φ : ↥(centralizer ({ζ} : Set X)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) :
    (((E ⊓ centralizer ({ζ} : Set X)).subgroupOf (centralizer ({ζ} : Set X))).map
        φ.toMonoidHom).Normal :=
  (inf_centralizer_subgroupOf_normal inferInstance ζ).map φ.toMonoidHom φ.surjective

theorem card_map_inf_centralizer {E : Subgroup X} [E.Normal]
    (φ : ↥(centralizer ({ζ} : Set X)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) :
    Nat.card (((E ⊓ centralizer ({ζ} : Set X)).subgroupOf (centralizer ({ζ} : Set X))).map
        φ.toMonoidHom) = Nat.card (E ⊓ centralizer ({ζ} : Set X) : Subgroup X) := by
  rw [Subgroup.card_map_of_injective φ.injective,
    natCard_subgroupOf_of_le (inf_le_right)]

theorem le_centralizer_of_layer_alt6 (hA6 : AutA6Table) (hζ : ζ * ζ = 1)
    (φ : ↥(centralizer ({ζ} : Set X)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (E : Subgroup X) [E.Normal] (e : E ≃* alternatingGroup (Fin 6)) :
    E ≤ centralizer ({ζ} : Set X) := by
  have h1 := card_normal_z2s6 _ (normal_map_inf_centralizer (E := E) φ)
  have h2 := card_inf_centralizer_alt6 hA6 E e hζ
  rw [card_map_inf_centralizer φ] at h1
  have h360 : Nat.card ↥(E ⊓ centralizer ({ζ} : Set X) : Subgroup X) = 360 := by omega
  have hE360 : Nat.card E = 360 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
  have hEN : E ⊓ centralizer ({ζ} : Set X) = E :=
    eq_of_le_of_card_ge inf_le_left (by rw [h360, hE360])
  rw [← hEN]
  exact inf_le_right

theorem card_le_two_of_layer_alt6
    (φ : ↥(centralizer ({ζ} : Set X)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (E : Subgroup X) [E.Normal] (hEc : E ≤ centralizer ({ζ} : Set X)) (hE : Nat.card E = 360)
    (U : Subgroup X) (hUK : U ≤ centralizer (E : Set X)) (hUc : U ≤ centralizer ({ζ} : Set X)) :
    Nat.card U ≤ 2 := by
  have hEinf : E ⊓ centralizer ({ζ} : Set X) = E := inf_eq_left.2 hEc
  have hMn := normal_map_inf_centralizer (E := E) φ
  have hMc := card_map_inf_centralizer (E := E) φ
  rw [hEinf] at hMn hMc
  have hM360 : Nat.card ((E.subgroupOf (centralizer ({ζ} : Set X))).map φ.toMonoidHom) = 360 := by
    rw [hMc, hE]
  have hsnd : ∀ w ∈ U.subgroupOf (centralizer ({ζ} : Set X)), (φ w).2 = 1 := by
    intro w hw
    refine snd_eq_one_of_commute_normal _ hMn hM360 (φ w) ?_
    rintro _ ⟨e', he', rfl⟩
    have hcomm : (e' : X) * (w : X) = (w : X) * (e' : X) :=
      mem_centralizer_iff.1 (hUK (mem_subgroupOf.1 hw)) (e' : X) he'
    have : e' * w = w * e' := Subtype.ext hcomm
    show φ w * φ e' = φ e' * φ w
    rw [← map_mul, ← map_mul, this]
  have hle : (U.subgroupOf (centralizer ({ζ} : Set X))).map φ.toMonoidHom ≤
      (MonoidHom.snd (Multiplicative (ZMod 2)) (Equiv.Perm (Fin 6))).ker := by
    rintro _ ⟨w, hw, rfl⟩
    exact hsnd w hw
  have h1 := Subgroup.card_le_of_le hle
  rw [card_ker_snd, Subgroup.card_map_of_injective φ.injective,
    natCard_subgroupOf_of_le hUc] at h1
  exact h1

theorem central_of_layer_alt6_of_equiv (hA6 : AutA6Table) (hζ : ζ * ζ = 1)
    (φ : ↥(centralizer ({ζ} : Set X)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6))
    (hX : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (E : Subgroup X) [E.Normal] (e : E ≃* alternatingGroup (Fin 6)) (x : X) :
    x * ζ * x⁻¹ = ζ := by
  by_cases hζ1 : ζ = 1
  · rw [hζ1]
    simp
  have hEc := le_centralizer_of_layer_alt6 hA6 hζ φ E e
  have hE360 : Nat.card E = 360 := by rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six]
  have hζK : ζ ∈ centralizer (E : Set X) :=
    mem_centralizer_iff.2 fun h hh => mem_centralizer_singleton_iff.1 (hEc hh)
  have hU : ∀ U : Subgroup X, IsPGroup 2 U → U ≤ centralizer (E : Set X) →
      U ≤ centralizer ({ζ} : Set X) → Nat.card U ≤ 2 := fun U _ hUK hUc =>
    card_le_two_of_layer_alt6 φ E hEc hE360 U hUK hUc
  exact conj_eq_of_normal (centralizer (E : Set X)) hζK hζ hζ1 hU hX x

theorem autA6Table : AutA6Table :=
  fun e₀ α hα => DRes.card_fix_involution_alt6 e₀ α hα

theorem mem_fusionZStar_of_layer_alt6 {G : Type} [Group G]
    [Finite G] {z : G} (hz : orderOf z = 2)
    (hC : Nonempty (↥(centralizer ({z} : Set G)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (e : Nonempty (egaLayer (G ⧸ fusionOddCore G) ≃* alternatingGroup (Fin 6))) :
    z ∈ fusionZStar G := by
  obtain ⟨e⟩ := e
  obtain ⟨c⟩ := id hC
  have htt : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hζ : (QuotientGroup.mk' (fusionOddCore G) z) * (QuotientGroup.mk' (fusionOddCore G) z) =
      1 := by rw [← map_mul, htt, map_one]
  let φ : ↥(centralizer ({QuotientGroup.mk' (fusionOddCore G) z} : Set (G ⧸ fusionOddCore G))) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6) :=
    (centralizerMkEquiv hz (inf_fusionOddCore_centralizer_eq_bot ⟨c⟩)).symm.trans c
  have hX : ∀ N : Subgroup (G ⧸ fusionOddCore G), N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hN hodd
    have h := standardComponentOddCore_quotient_fusionOddCore_eq_bot G
    exact le_bot_iff.1 (h ▸ le_sSup ⟨hN, hodd⟩)
  have hEn : (egaLayer (G ⧸ fusionOddCore G)).Normal := egaLayer_normal _
  have hc := central_of_layer_alt6_of_equiv autA6Table hζ φ hX _ e
  show QuotientGroup.mk' (fusionOddCore G) z ∈ Subgroup.center (G ⧸ fusionOddCore G)
  rw [Subgroup.mem_center_iff]
  intro g
  have := hc g
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

end CFSG.EvenSporadicStandard.M22Std
