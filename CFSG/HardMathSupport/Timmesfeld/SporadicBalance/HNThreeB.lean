module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PrimeCommute
public import CFSG.Sporadic.HNSchreier.Simple
public import CFSG.Sporadic.HNSchreier.Sylow3
public import Certificates.Certificate13609
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open Equiv Subgroup
open CFSG.Sporadic.HNSchreier

section Abstract

variable {G : Type*} [Group G]

theorem centralizer_pow_eq {y : G} {k : ℕ} (hk : orderOf (y ^ k) = orderOf y)
    (hy : 0 < orderOf y) : centralizer ({y ^ k} : Set G) = centralizer ({y} : Set G) := by
  have hle : zpowers (y ^ k) ≤ zpowers y := zpowers_le.2 (pow_mem (mem_zpowers y) k)
  have : Finite (zpowers y) := Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hz : zpowers (y ^ k) = zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hk])
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 (hz ▸ mem_zpowers y : y ∈ zpowers (y ^ k))
  apply le_antisymm
  · intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    rw [← hm]
    exact ((Commute.zpow_right (show Commute c (y ^ k) from hc) m)).eq
  · intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    exact ((Commute.pow_right (show Commute c y from hc) k)).eq

theorem card_inf_centralizer_conj (K : Subgroup G) {g x : G} (hg : g ∈ K) :
    Nat.card (K ⊓ centralizer ({g * x * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have e : (K ⊓ centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      K ⊓ centralizer ({g * x * g⁻¹} : Set G) := by
    ext c
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨d, ⟨hdK, hdx⟩, rfl⟩
      refine ⟨K.mul_mem (K.mul_mem hg hdK) (K.inv_mem hg), ?_⟩
      calc g * d * g⁻¹ * (g * x * g⁻¹) = g * (d * x) * g⁻¹ := by group
        _ = g * (x * d) * g⁻¹ := by rw [hdx]
        _ = g * x * g⁻¹ * (g * d * g⁻¹) := by group
    · rintro ⟨hcK, hcx⟩
      refine ⟨g⁻¹ * c * g, ⟨K.mul_mem (K.mul_mem (K.inv_mem hg) hcK) hg, ?_⟩, by group⟩
      calc g⁻¹ * c * g * x = g⁻¹ * (c * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * c) * g := by rw [hcx]
        _ = x * (g⁻¹ * c * g) := by group
  rw [← e, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem not_dvd_card_inf_centralizer [Finite G] (K : Subgroup G) {p m : ℕ} [Fact p.Prime]
    (hK : ¬ p ^ 2 ∣ Nat.card K) {x y : G} (hx : x ∈ K) (hy : y ∈ K) (hxo : orderOf x = p)
    (hyo : orderOf y = p) (hm : Nat.Coprime m p)
    (hlt : Nat.card (K ⊓ centralizer ({y} : Set G) : Subgroup G) < m * p) :
    ¬ m ∣ Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  intro hdvd
  have hyo' : orderOf (⟨y, hy⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact hyo
  have hxo' : orderOf (⟨x, hx⟩ : K) = p := by rw [Subgroup.orderOf_mk]; exact hxo
  obtain ⟨g, k, hgk⟩ := CFSG.RankThree.PartOne.HNRed.exists_conj_pow_of_orderOf_prime hK hyo' hxo'
  have hgk' : (g : G) * x * (g : G)⁻¹ = y ^ k := congrArg Subtype.val hgk
  have hk : orderOf (y ^ k) = orderOf y := by rw [← hgk', orderOf_conj_eq, hxo, hyo]
  have hcard : Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) =
      Nat.card (K ⊓ centralizer ({y} : Set G) : Subgroup G) := by
    rw [← card_inf_centralizer_conj K g.2 (x := x), hgk',
      centralizer_pow_eq hk (by rw [hyo]; exact (Fact.out : p.Prime).pos)]
  have hp : p ∣ Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have := orderOf_dvd_natCard (⟨x, Subgroup.mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2
      rfl⟩⟩ : (K ⊓ centralizer ({x} : Set G) : Subgroup G))
    rwa [Subgroup.orderOf_mk, hxo] at this
  have hmp := Nat.Coprime.mul_dvd_of_dvd_of_dvd hm hdvd hp
  have hpos : 0 < Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := Nat.card_pos
  have := Nat.le_of_dvd hpos hmp
  omega

end Abstract

@[expose] def yJ : JH := c3J 6 * c3J 0 * c3J 0

theorem yJ_mem :
    yJ ∈ CJ (sJ 2) :=
  mul_mem (mul_mem (mem_CJ.2 (c3J_comm (by norm_num)).symm)
    (mem_CJ.2 (c3J_comm (by norm_num)).symm)) (mem_CJ.2 (c3J_comm (by norm_num)).symm)

theorem orderOf_yJ : orderOf yJ = 5 :=
  Certificates.certificate13609.2

theorem card_inf_centralizer_yJ_le :
    Nat.card (CJ (sJ 2) ⊓ CJ yJ : Subgroup JH) ≤ 30 :=
  Certificates.certificate13609.1

theorem not_nine_dvd_card_inf_centralizer
    {x : JH} (hx : x ∈ CJ (sJ 2))
    (hxo : orderOf x = 5) : ¬ 9 ∣ Nat.card (CJ (sJ 2) ⊓ CJ x : Subgroup JH) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact not_dvd_card_inf_centralizer (CJ (sJ 2)) (by rw [card_CJ_s3]; norm_num) hx yJ_mem hxo
    orderOf_yJ (by norm_num) (card_inf_centralizer_yJ_le.trans_lt (by norm_num))

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
