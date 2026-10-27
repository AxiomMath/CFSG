module

import CFSG.Quasithin.Background.A1cTransferVariants
import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.CGT.Foote82.T66.CaseII513G10
public import CFSG.CGT.Foote82.T66.CaseII513Syl
public import CFSG.CGT.Foote82.T66.CaseIIOmega

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel
open scoped commutatorElement

namespace CaseII

theorem factorization_25920 : (25920 : ℕ).factorization 2 = 6 := by
  rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem conj_mem_layerIn' {G : Subgroup (GLV V)} {g e : GLV V} (hg : g ∈ G)
    (he : e ∈ layerIn G) : g * e * g⁻¹ ∈ layerIn G := by
  have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨e₀, he₀, rfl⟩ := he
  have hn : (CFSG.layer ↥G).Normal := inferInstance
  exact ⟨⟨g, hg⟩ * e₀ * ⟨g, hg⟩⁻¹, hn.conj_mem e₀ he₀ ⟨g, hg⟩, rfl⟩

theorem conj_mem_of_isComponentOf {G K : Subgroup (GLV V)} (hK : IsComponentOf K G)
    {e k : GLV V} (he : e ∈ layerIn G) (hk : k ∈ K) : e * k * e⁻¹ ∈ K := by
  have hKG : K ≤ G := hK.1
  have hcomp' : CFSG.IsComponent (K.subgroupOf G) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKG).1
      (CFSG.Assembly.isComponentOf_iff_open.2 hK)
  have hnorm := CFSG.LocalCores.layer_le_normalizer hcomp'
  obtain ⟨e₀, he₀, rfl⟩ := he
  exact Subgroup.mem_subgroupOf.1
    ((Subgroup.mem_normalizer_iff.1 (hnorm he₀) ⟨k, hKG hk⟩).1 (Subgroup.mem_subgroupOf.2 hk))

theorem layerIn_le_of_commutator_le {G N : Subgroup (GLV V)} (hN : ⁅G, G⁆ ≤ N) :
    layerIn G ≤ N := by
  rw [layerIn_eq_sSup]
  refine sSup_le fun K hK => ?_
  have hK' : IsComponentOf K G := hK
  calc K = ⁅K, K⁆ := (commutator_eq_self_of_isQuasisimple hK'.2.2).symm
    _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono hK'.1 hK'.1
    _ ≤ N := hN

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem mul_z_mem_H_iff {b : GLV V} (hb : b ∈ H₁) : b * z ∈ HH G L v ↔ b ∉ HH G L v := by
  constructor
  · intro hbz hbH
    apply c.z_not_mem_H
    have : z = b⁻¹ * (b * z) := by group
    rw [this]
    exact (HH G L v).mul_mem ((HH G L v).inv_mem hbH) hbz
  · exact c.mul_z_mem_H hb

theorem fus (hs : CaseIISplit) (hG1 : CaseIIG1) (h513 : ∀ x ∈ G, x * z * x⁻¹ ∉ HH G L v)
    {a : GLV V} (ha : a ∈ H₁) {x : GLV V} (hxG : x ∈ G) (hax : a = x * z * x⁻¹) :
    ∃ h ∈ HH G L v, a = h * z * h⁻¹ := by
  have haH : a ∉ HH G L v := hax ▸ h513 x hxG
  have hazH : a * z ∈ HH G L v := c.mul_z_mem_H ha haH
  have hzaH : z⁻¹ * a ∈ HH G L v := by
    have := c.conj_mem_H (H₁.inv_mem c.z_mem) hazH
    have e : z⁻¹ * (a * z) * z⁻¹⁻¹ = z⁻¹ * a := by
      rw [inv_inv, mul_assoc, mul_assoc, c.z_mul_z, mul_one]
    rwa [e] at this
  have h1 := c.finrank_range_subOne hs ha
  have h2 := c.finrank_range_subOne hs c.z_mem
  have hV₁ : (fixedSpace (HH G L v)).map (subOne a) =
      (fixedSpace (HH G L v)).map (subOne z) := by
    have := c.map_V₁_eq (a := z) hzaH
    rwa [show z * (z⁻¹ * a) = a by group] at this
  have hconj : Module.finrank (ZMod 2) ↥(LinearMap.range (subOne a)) =
      Module.finrank (ZMod 2) ↥(LinearMap.range (subOne z)) := by
    subst hax
    exact finrank_eq_of_card_eq (card_range_subOne_conj x z)
  rw [hV₁] at h1
  have hz1 : cdim6 (ψ ⟨z, c.z_mem⟩) = 1 := c.data.ψ_z
  have hcdim : cdim6 (ψ ⟨a, ha⟩) = 1 := by omega
  have ho : orderOf ((ψ ⟨a, ha⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hax, c.orderOf_conj_z]
  obtain ⟨w, hw, hwz⟩ := (hG1 _ (ψ ⟨z, c.z_mem⟩).2 c.orderOf_psi_z c.data.ψ_z).1 _
    (ψ ⟨a, ha⟩).2 ho hcdim
  set h : ↥(HH G L v) := c.phi.symm ⟨w, hw⟩ with hh
  refine ⟨h, h.2, ?_⟩
  have hhH₁ : (h : GLV V) ∈ H₁ := c.H_le h.2
  have hψh : ((ψ ⟨h, hhH₁⟩ : ↥(orthogonalMinus 2 (ZMod 2) 1 1)) : GL I6 (ZMod 2)) = w := by
    rw [← c.phi_coe, hh, MulEquiv.apply_symm_apply]
  have hm : (h : GLV V) * z * (h : GLV V)⁻¹ ∈ H₁ :=
    H₁.mul_mem (H₁.mul_mem hhH₁ c.z_mem) (H₁.inv_mem hhH₁)
  have key : ψ ⟨a, ha⟩ = ψ ⟨(h : GLV V) * z * (h : GLV V)⁻¹, hm⟩ := by
    apply Subtype.ext
    have e : (⟨(h : GLV V) * z * (h : GLV V)⁻¹, hm⟩ : ↥H₁) =
        ⟨h, hhH₁⟩ * ⟨z, c.z_mem⟩ * (⟨h, hhH₁⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hψh,
      hwz]
  exact congrArg Subtype.val (ψ.injective key)

theorem sylow_T (hs : CaseIISplit) (haut : CaseIIAut) (hG1 : CaseIIG1)
    (h513 : ∀ x ∈ G, x * z * x⁻¹ ∉ HH G L v) {g : GLV V} (d : GD c g) {T : Subgroup (GLV V)}
    (hTH₁ : T ≤ H₁) (hT2 : IsPGroup 2 ↥T) (hTc : Nat.card ↥T = 2 ^ (Nat.card ↥H₁).factorization 2)
    (hzT : z ∈ T) (huT : g * z * g⁻¹ ∈ T) :
    ∀ Y : Subgroup (GLV V), Y ≤ G → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ Nat.card ↥T :=
  card_le_of_sylow (hTH₁.trans c.H₁_le_G) hT2 fun Y hTY hYG hY2 =>
    d.lemma57 hs haut hG1 hTH₁ hTc hzT huT
      (fun _ haT ⟨_, hxG, hax⟩ => c.fus hs hG1 h513 (hTH₁ haT) hxG hax) Y hYG hY2 hTY

theorem z_not_mem_layerIn (h513 : ∀ x ∈ G, x * z * x⁻¹ ∉ HH G L v) {T : Subgroup (GLV V)}
    (hTH₁ : T ≤ H₁) (hT2 : IsPGroup 2 ↥T) (hzT : z ∈ T)
    (hmax : ∀ Y : Subgroup (GLV V), Y ≤ G → IsPGroup 2 ↥Y → Nat.card ↥Y ≤ Nat.card ↥T) :
    z ∉ layerIn G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTG : T ≤ G := hTH₁.trans c.H₁_le_G
  have hidx : ¬ 2 ∣ T.relIndex G := by
    intro h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT2
    have hTG' : Nat.card ↥(T.subgroupOf G) = 2 ^ k := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv, hk]
    have hdvd : 2 ^ (k + 1) ∣ Nat.card ↥G := by
      have h := (T.subgroupOf G).card_mul_index
      rw [hTG'] at h
      rw [← h, pow_succ]
      exact Nat.mul_dvd_mul_left _ h2
    obtain ⟨K, hK, -⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hTG'
    have h1 := hmax (K.map G.subtype) (Subgroup.map_subtype_le _)
      (IsPGroup.of_card (n := k + 1)
        (by rw [Subgroup.card_map_of_injective G.subtype_injective, hK]))
    rw [Subgroup.card_map_of_injective G.subtype_injective, hK, hk] at h1
    have : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hQidx : (T ⊓ HH G L v).relIndex T = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨z, hzT, fun b hb => ?_⟩
    have h1 := c.mul_z_mem_H_iff (hTH₁ hb)
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    by_cases hbH : b ∈ HH G L v
    · exact Or.inr ⟨⟨hb, hbH⟩, fun h => (h1.1 h.2) hbH⟩
    · exact Or.inl ⟨⟨T.mul_mem hb hzT, h1.2 hbH⟩, fun h => hbH h.2⟩
  obtain ⟨N, hNG, hNn, hNsq, hzN⟩ := CFSG.Quasithin.thompson_transfer_exists_normal_subgroup hTG
    hT2 hidx inf_le_left hQidx c.z_mem_G c.orderOf_z
    (fun x hxG h => h513 x⁻¹ (G.inv_mem hxG) (by simpa using h.2))
  have hN' : ∀ x ∈ G, ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x hx n hn => by
    have := hNn.conj_mem ⟨n, hNG hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨x, hx⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hcomm : ⁅G, G⁆ ≤ N := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have e : ⁅a, b⁆ = (a * b) ^ 2 * (b⁻¹ * a⁻¹ ^ 2 * b⁻¹⁻¹) * b⁻¹ ^ 2 := by
      rw [commutatorElement_def, sq (a * b)]
      group
    rw [e]
    exact N.mul_mem (N.mul_mem (hNsq _ (G.mul_mem ha hb))
      (hN' _ (G.inv_mem hb) _ (hNsq _ (G.inv_mem ha)))) (hNsq _ (G.inv_mem hb))
  exact fun hz => hzN (layerIn_le_of_commutator_le hcomm hz)

theorem card_G_eq (hzE : z ∉ layerIn G) : Nat.card ↥G = 2 * Nat.card ↥(layerIn G) := by
  have hnorm : Subgroup.zpowers z ≤ Subgroup.normalizer (layerIn G : Set (GLV V)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨conj_mem_layerIn' c.z_mem_G, fun he => ?_⟩
    have := conj_mem_layerIn' (G.inv_mem c.z_mem_G) he
    simpa [mul_assoc] using this
  have h1 := card_sup_mul_card_inf hnorm
  have hinf : Subgroup.zpowers z ⊓ layerIn G = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    rcases eq_one_or_eq_of_mem_zpowers c.z_mul_z hy1 with h | h
    · exact h
    · exact absurd (h ▸ hy2) hzE
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, c.orderOf_z, sup_comm,
    ← c.std.eq_layerIn_sup] at h1
  exact h1

theorem index_layerIn (hzE : z ∉ layerIn G) : ((layerIn G).subgroupOf G).index = 2 := by
  have h := ((layerIn G).subgroupOf G).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (layerIn_le G)).toEquiv, c.card_G_eq hzE] at h
  have hpos : 0 < Nat.card ↥(layerIn G) := Nat.card_pos
  have : Nat.card ↥(layerIn G) * ((layerIn G).subgroupOf G).index = Nat.card ↥(layerIn G) * 2 := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem centralizer_layerIn_le (hzE : z ∉ layerIn G) :
    G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)) ≤ layerIn G := by
  intro x hx
  have hodd := c.std.extremal.setup.odd_card_centralizer_layerIn
  have hsq : x ^ 2 ∈ layerIn G := by
    have := Subgroup.sq_mem_of_index_two (c.index_layerIn hzE) ⟨x, hx.1⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hox : Odd (orderOf x) := by
    have h1 : orderOf (⟨x, hx⟩ : ↥(G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)))) ∣
        Nat.card ↥(G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V))) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact hodd.of_dvd_nat h1
  obtain ⟨j, hj⟩ := hox
  have e : x = (x ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [e]
  exact (layerIn G).pow_mem hsq _

theorem odd_card_center_layerIn : Odd (Nat.card ↥(Subgroup.center ↥(layerIn G))) := by
  have h1 := c.std.extremal.setup.odd_card_centralizer_layerIn
  refine h1.of_dvd_nat ?_
  have hle : (Subgroup.center ↥(layerIn G)).map (layerIn G).subtype ≤
      G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)) := by
    rintro _ ⟨c', hc', rfl⟩
    refine ⟨layerIn_le G c'.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    have := Subgroup.mem_center_iff.1 hc' ⟨g, hg⟩
    exact congrArg Subtype.val this
  rw [← Subgroup.card_map_of_injective (layerIn G).subtype_injective]
  exact Subgroup.card_dvd_of_le hle

end Ctx

end CaseII

end CFSG.CGT.Foote82
