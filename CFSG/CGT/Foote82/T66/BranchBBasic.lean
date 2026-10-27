module

public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.CGT.Foote82.T66.Inherit
public import CFSG.CGT.Foote82.T66.Prop35
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans
import CFSG.Quasithin.Background.G11Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

namespace BranchB

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem add_self_eq_zero_of_zmod {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (x : W) :
    x + x = 0 := by
  rw [← two_nsmul]
  exact ZModModule.char_nsmul_eq_zero 2 x

theorem mul_self_of_mem_zpowers {G : Type*} [Group G] {z s : G} (hz : z * z = 1)
    (hs : s ∈ Subgroup.zpowers z) : s * s = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz, one_zpow]

theorem apply_eq_of_mem_commSpace {z : GLV V} (hz : z * z = 1) {w : V}
    (hw : w ∈ commSpace (Subgroup.zpowers z) ⊤) : z w = w := by
  let S : Subgroup (GLV V) :=
    { carrier := {g | ∀ u, z (g u - u) = g u - u}
      mul_mem' := fun {a b} ha hb u => by
        have e : (a * b) u - u = (a (b u) - b u) + (b u - u) := by
          show a (b u) - u = _
          abel
        rw [e, map_add, ha, hb]
      one_mem' := fun u => by
        change z (u - u) = u - u
        rw [sub_self, map_zero]
      inv_mem' := fun {a} ha u => by
        have e : a⁻¹ u - u = -(a (a⁻¹ u) - a⁻¹ u) := by
          rw [show a (a⁻¹ u) = u from a.apply_symm_apply u]
          abel
        rw [e, map_neg, ha] }
  have hzS : z ∈ S := fun u => by
    show z (z u - u) = z u - u
    rw [map_sub, show z (z u) = u from congrArg (fun f : GLV V => f u) hz]
    have h2 := add_self_eq_zero_of_zmod (z u - u)
    rw [← sub_eq_zero]
    calc u - z u - (z u - u) = -((z u - u) + (z u - u)) := by abel
      _ = 0 := by rw [h2, neg_zero]
  have hle : Subgroup.zpowers z ≤ S := Subgroup.zpowers_le.2 hzS
  have hsub : commSpace (Subgroup.zpowers z) ⊤ ≤
      LinearMap.eqLocus (z : V →ₗ[ZMod 2] V) LinearMap.id :=
    commSpace_le_iff.2 fun g hg u _ => hle hg u
  exact hsub hw

theorem ne_bot_of_isQuasisimple {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    (hq : CFSG.Open.IsQuasisimple ↥L) : L ≠ ⊥ := by
  intro hL
  have hs := hq.2
  have : Subsingleton ↥L := by
    rw [hL]
    infer_instance
  have hnt := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (congrArg _ (Subsingleton.elim a b))

theorem perfect_of_isQuasisimple {Γ : Type*} [Group Γ] {L : Subgroup Γ}
    (hq : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hq.1)

theorem layerIn_le (H : Subgroup (GLV V)) : layerIn H ≤ H := Subgroup.map_subtype_le _

theorem conj_mem_layerIn {H : Subgroup (GLV V)} {g : GLV V} (hg : g ∈ H) {e : GLV V}
    (he : e ∈ layerIn H) : g * e * g⁻¹ ∈ layerIn H := by
  have : (CFSG.layer ↥H).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨e₀, he₀, rfl⟩ := he
  exact ⟨⟨g, hg⟩ * e₀ * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance e₀ he₀ ⟨g, hg⟩,
    by simp⟩

theorem commutator_subgroupOf_self {Γ : Type*} [Group Γ] {H L : Subgroup Γ} (hLH : L ≤ H)
    (hL : ⁅L, L⁆ = L) : ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH, hL]

theorem subgroupOf_ne_bot {Γ : Type*} [Group Γ] {H L : Subgroup Γ} (hLH : L ≤ H) (hL : L ≠ ⊥) :
    L.subgroupOf H ≠ ⊥ := by
  intro h'
  apply hL
  have := congrArg (Subgroup.map H.subtype) h'
  rwa [Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_bot] at this

abbrev bbL₀ (G L : Subgroup (GLV V)) (v : V) : Subgroup (GLV V) :=
  normalClosure (layerIn (G ⊓ vFix v)) L

abbrev bbH₁ (G L : Subgroup (GLV V)) (z : GLV V) (v : V) : Subgroup (GLV V) :=
  bbL₀ G L v ⊔ Subgroup.zpowers z

abbrev bbW₁ (G L : Subgroup (GLV V)) (v : V) : Submodule (ZMod 2) V :=
  commSpace (bbL₀ G L v) ⊤

abbrev bbW₀ (G L : Subgroup (GLV V)) (v : V) : Submodule (ZMod 2) V :=
  tildeVBot (bbL₀ G L v)

structure Hyp (G L : Subgroup (GLV V)) (z : GLV V) (v : V) : Prop where
  std : StdForm G L z
  rank : CFSG.Open.pRank 2 (G ⊓ Subgroup.centralizer (L : Set (GLV V))) = 1
  mem : v ∈ commSpace (Subgroup.zpowers z) ⊤
  ne : v ≠ 0
  not_sub : ¬ IsSubnormal L (G ⊓ vFix v)

namespace Hyp

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} (h : Hyp G L z v)

include h

theorem setup6 : Setup6 G (Subgroup.zpowers z) L :=
  h.std.extremal.setup.toSetup6

theorem z_mem_G : z ∈ G := h.setup6.S_le (Subgroup.mem_zpowers z)

theorem zz : z * z = 1 := by
  have h1 := pow_orderOf_eq_one z
  rw [h.std.orderOf_s, sq] at h1
  exact h1

theorem L_le_G : L ≤ G := h.std.extremal.toConf66.L_le

theorem L_ne_bot : L ≠ ⊥ := ne_bot_of_isQuasisimple h.setup6.component.2.2

theorem L_perfect : ⁅L, L⁆ = L := perfect_of_isQuasisimple h.setup6.component.2.2

theorem L_fix : ∀ l ∈ L, l v = v := fun l hl =>
  (h.setup6.lemma61 (Subgroup.mem_zpowers z)).1 l hl v h.mem

theorem z_fix : z v = v := apply_eq_of_mem_commSpace h.zz h.mem

theorem sup_le_H₀ : L ⊔ Subgroup.zpowers z ≤ G ⊓ vFix v := by
  refine sup_le (fun l hl => ⟨h.L_le_G hl, h.L_fix l hl⟩) ?_
  rw [Subgroup.zpowers_le]
  exact ⟨h.z_mem_G, h.z_fix⟩

theorem setup6₀ : Setup6 (G ⊓ vFix v) (Subgroup.zpowers z) L :=
  Lemma63.setup6_of_le h.setup6 inf_le_left h.sup_le_H₀

theorem L_le_layerIn : L ≤ layerIn (G ⊓ vFix v) := h.setup6₀.le_layerIn

theorem L_le_L₀ : L ≤ bbL₀ G L v := le_normalClosure _ _

theorem L₀_le_layerIn : bbL₀ G L v ≤ layerIn (G ⊓ vFix v) := normalClosure_le h.L_le_layerIn

theorem L₀_le_H₀ : bbL₀ G L v ≤ G ⊓ vFix v := h.L₀_le_layerIn.trans (layerIn_le _)

theorem L₀_le_H₁ : bbL₀ G L v ≤ bbH₁ G L z v := le_sup_left

theorem L_le_H₁ : L ≤ bbH₁ G L z v := h.L_le_L₀.trans h.L₀_le_H₁

theorem z_mem_H₁ : z ∈ bbH₁ G L z v := (le_sup_right : Subgroup.zpowers z ≤ _)
  (Subgroup.mem_zpowers z)

theorem H₁_le_H₀ : bbH₁ G L z v ≤ G ⊓ vFix v :=
  sup_le h.L₀_le_H₀ (le_sup_right.trans h.sup_le_H₀)

theorem H₁_le_G : bbH₁ G L z v ≤ G := h.H₁_le_H₀.trans inf_le_left

theorem isSubnormal_L₀ : IsSubnormal (bbL₀ G L v) (G ⊓ vFix v) := by
  refine IsSubnormal.step h.L₀_le_layerIn ?_ (IsSubnormal.step (layerIn_le _) ?_
    (IsSubnormal.refl _))
  · rw [Subgroup.normal_subgroupOf_iff h.L₀_le_layerIn]
    intro a g ha hg
    exact normalClosure_conj hg ha
  · rw [Subgroup.normal_subgroupOf_iff (layerIn_le _)]
    intro e g he hg
    exact conj_mem_layerIn hg he

theorem orbitData : ∃ K : Subgroup (GLV V),
    Lemma63.OrbitData ((bbL₀ G L v).subgroupOf (bbH₁ G L z v))
      ((Subgroup.zpowers z).subgroupOf (bbH₁ G L z v)) (K.subgroupOf (bbH₁ G L z v)) :=
  Lemma63.exists_orbitData h.setup6₀ rfl

theorem conj_mem_L₀ {g : GLV V} (hg : g ∈ bbH₁ G L z v) {a : GLV V} (ha : a ∈ bbL₀ G L v) :
    g * a * g⁻¹ ∈ bbL₀ G L v := by
  obtain ⟨K, hO⟩ := h.orbitData
  exact ((Subgroup.normal_subgroupOf_iff h.L₀_le_H₁).1 hO.normal) a g ha hg

theorem mul_self_mem_L₀ {g : GLV V} (hg : g ∈ bbH₁ G L z v) : g * g ∈ bbL₀ G L v := by
  obtain ⟨K, hO⟩ := h.orbitData
  haveI := hO.normal
  have hy : (⟨g, hg⟩ : ↥(bbH₁ G L z v)) ∈ (bbL₀ G L v).subgroupOf (bbH₁ G L z v) ⊔
      (Subgroup.zpowers z).subgroupOf (bbH₁ G L z v) := by
    rw [hO.sup_eq]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, s, hs, has⟩ := Subgroup.mem_sup_of_normal_left.1 hy
  have hg' : g = (a : GLV V) * (s : GLV V) := by
    rw [← Subgroup.coe_mul, has]
  have hss : (s : GLV V) * (s : GLV V) = 1 := mul_self_of_mem_zpowers h.zz hs
  have hsa : (s : GLV V) * a * (s : GLV V)⁻¹ ∈ bbL₀ G L v := h.conj_mem_L₀ s.2 ha
  have e : g * g = (a : GLV V) * ((s : GLV V) * a * (s : GLV V)⁻¹) * ((s : GLV V) * s) := by
    rw [hg']
    group
  rw [e, hss, mul_one]
  exact (bbL₀ G L v).mul_mem ha hsa

theorem mem_L₀_of_odd {g : GLV V} (hg : g ∈ bbH₁ G L z v) (hodd : Odd (orderOf g)) :
    g ∈ bbL₀ G L v := by
  obtain ⟨m, hm⟩ := hodd
  have e : g = (g * g) ^ (m + 1) := by
    calc g = g ^ (orderOf g + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
      _ = (g * g) ^ (m + 1) := by
        rw [hm, ← sq, ← pow_mul]
        ring_nf
  rw [e]
  exact pow_mem (h.mul_self_mem_L₀ hg) _

theorem false_of_involution {t : GLV V} (htG : t ∈ G) (ht : orderOf t = 2)
    (hc : ∀ a ∈ bbL₀ G L v, t * a = a * t) : False := by
  have htL : t ∈ Subgroup.centralizer (L : Set (GLV V)) :=
    Subgroup.mem_centralizer_iff.2 fun l hl => (hc l (h.L_le_L₀ hl)).symm
  have hcomp := h.std.component_of_inv t htG ht htL
  have hL₀ : bbL₀ G L v ≤ G ⊓ Subgroup.centralizer ({t} : Set (GLV V)) := fun a ha =>
    ⟨(h.L₀_le_H₀ ha).1, Subgroup.mem_centralizer_singleton_iff.2 (hc a ha).symm⟩
  have hsub : IsSubnormal L (bbL₀ G L v) := by
    have := hcomp.2.1.inf_of_le hL₀
    rwa [inf_eq_left.2 h.L_le_L₀] at this
  exact h.not_sub (hsub.trans h.isSubnormal_L₀)

theorem odd_of_commute {g : GLV V} (hg : g ∈ bbH₁ G L z v)
    (hc : ∀ a ∈ bbL₀ G L v, g * a = a * g) : Odd (orderOf g) := by
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have ht : orderOf (g ^ (orderOf g / 2)) = 2 :=
    orderOf_pow_orderOf_div hpos (even_iff_two_dvd.1 heven)
  exact h.false_of_involution (pow_mem (h.H₁_le_G hg) _) ht
    fun a ha => (Commute.pow_left (hc a ha) _).eq

theorem mem_L₀_of_commute {g : GLV V} (hg : g ∈ bbH₁ G L z v)
    (hc : ∀ a ∈ bbL₀ G L v, g * a = a * g) : g ∈ bbL₀ G L v :=
  h.mem_L₀_of_odd hg (h.odd_of_commute hg hc)

theorem commSpace_L_ne_bot : commSpace L ⊤ ≠ ⊥ := by
  intro h0
  apply h.L_ne_bot
  rw [eq_bot_iff]
  intro l hl
  rw [Subgroup.mem_bot]
  ext u
  exact commSpace_eq_bot_iff.1 h0 l hl u Submodule.mem_top

theorem not_fix_commSpace (hfix : ∀ l ∈ L, ∀ u ∈ commSpace L ⊤, l u = u) : False := by
  have h0 : commSpace L (commSpace L ⊤) = ⊥ := commSpace_eq_bot_iff.2 hfix
  rw [commSpace_commSpace_top_of_perfect h.L_perfect] at h0
  exact h.commSpace_L_ne_bot h0

theorem inv₁ : Invariant (bbH₁ G L z v) (bbW₁ G L v) :=
  invariant_commSpace (fun _ hg _ ha => h.conj_mem_L₀ hg ha) (invariant_top _)

theorem inv₀ : Invariant (bbH₁ G L z v) (bbW₀ G L v) :=
  (invariant_fixedSpace (fun _ hg _ ha => h.conj_mem_L₀ hg ha)).inf h.inv₁

theorem L₀_le_normalClosure : bbL₀ G L v ≤ normalClosure (bbH₁ G L z v) L := by
  obtain ⟨K, hO⟩ := h.orbitData
  have hNH : normalClosure (bbH₁ G L z v) L ≤ bbH₁ G L z v := normalClosure_le h.L_le_H₁
  haveI hN : ((normalClosure (bbH₁ G L z v) L).subgroupOf (bbH₁ G L z v)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNH]
    intro a g ha hg
    exact normalClosure_conj hg ha
  have hle := hO.le_of_normal
    (N := (normalClosure (bbH₁ G L z v) L).subgroupOf (bbH₁ G L z v))
    (commutator_subgroupOf_self h.L_le_H₁ h.L_perfect)
    (subgroupOf_ne_bot h.L_le_H₁ h.L_ne_bot) (Subgroup.comap_mono h.L_le_L₀)
    (Subgroup.comap_mono (le_normalClosure (bbH₁ G L z v) L))
  intro a ha
  exact hle (show (⟨a, h.L₀_le_H₁ ha⟩ : ↥(bbH₁ G L z v)) ∈ (bbL₀ G L v).subgroupOf _ from ha)

theorem irrSec : IrrSec (bbH₁ G L z v) (bbW₀ G L v) (bbW₁ G L v) := by
  have hL₀N := h.L₀_le_normalClosure
  refine ⟨lt_of_le_of_ne inf_le_right fun heq => ?_, fun J hJ hJ₀ hJ₁ => ?_⟩
  · refine h.not_fix_commSpace fun l hl u hu => ?_
    have hu' : u ∈ bbW₀ G L v := heq ▸ (commSpace_mono h.L_le_L₀ le_rfl hu)
    exact hu'.1 l (h.L_le_L₀ hl)
  · rcases trivial_or_commSpace_le h.L_perfect h.setup6.irrTilde (hJ.mono h.L_le_H₁) with
      hJL | hJL
    · left
      have hfix : normalClosure (bbH₁ G L z v) L ≤ centralizerOn ⊤ J := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨g, hg, l, hl, rfl⟩
        refine ⟨Subgroup.mem_top _, fun w hw => ?_⟩
        show g (l (g⁻¹ w)) = w
        rw [hJL l hl _ (hJ g⁻¹ ((bbH₁ G L z v).inv_mem hg) w hw)]
        exact g.apply_symm_apply w
      refine le_antisymm (fun u hu => ⟨fun a ha => (hfix (hL₀N ha)).2 u hu, hJ₁ hu⟩) hJ₀
    · right
      refine le_antisymm hJ₁ ?_
      let M : Subgroup (GLV V) :=
        { carrier := {g | ∀ u, g u - u ∈ J}
          mul_mem' := fun {a b} ha hb u => by
            have e : (a * b) u - u = (a (b u) - b u) + (b u - u) := by
              show a (b u) - u = _
              abel
            rw [e]
            exact J.add_mem (ha _) (hb _)
          one_mem' := fun u => by
            change u - u ∈ J
            rw [sub_self]
            exact J.zero_mem
          inv_mem' := fun {a} ha u => by
            have e : a⁻¹ u - u = -(a (a⁻¹ u) - a⁻¹ u) := by
              rw [show a (a⁻¹ u) = u from a.apply_symm_apply u]
              abel
            rw [e]
            exact J.neg_mem (ha _) }
      have hM : normalClosure (bbH₁ G L z v) L ≤ M := by
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨g, hg, l, hl, rfl⟩
        intro u
        have e : (g * l * g⁻¹) u - u = g (l (g⁻¹ u) - g⁻¹ u) := by
          show g (l (g⁻¹ u)) - u = _
          rw [map_sub, show g (g⁻¹ u) = u from g.apply_symm_apply u]
        rw [e]
        exact hJ g hg _ (hJL (sub_mem_commSpace hl Submodule.mem_top))
      exact commSpace_le_iff.2 fun a ha u _ => hM (hL₀N ha) u

theorem not_trivial : ¬ ∀ x ∈ bbH₁ G L z v, ∀ w ∈ bbW₁ G L v, x w - w ∈ bbW₀ G L v := by
  intro hall
  have h1 : commSpace L (commSpace L ⊤) ≤ fixedSpace L := by
    refine commSpace_le_iff.2 fun l hl u hu => ?_
    have := hall l (h.L_le_H₁ hl) u (commSpace_mono h.L_le_L₀ le_rfl hu)
    exact fixedSpace_anti h.L_le_L₀ this.1
  have h2 : commSpace L (commSpace L (commSpace L ⊤)) = ⊥ :=
    commSpace_eq_bot_iff.2 fun l hl u hu => h1 hu l hl
  rw [commSpace_commSpace_top_of_perfect h.L_perfect,
    commSpace_commSpace_top_of_perfect h.L_perfect] at h2
  exact h.commSpace_L_ne_bot h2

theorem H₀_lt_G : G ⊓ vFix v < G := by
  refine lt_of_le_of_ne inf_le_left fun heq => ?_
  have hGv : ∀ g ∈ G, g v = v := fun g hg => by
    have : g ∈ G ⊓ vFix v := by rw [heq]; exact hg
    exact this.2
  have hinv : Invariant G (fixedSpace G) :=
    invariant_fixedSpace fun k' hk' k hk => G.mul_mem (G.mul_mem hk' hk) (G.inv_mem hk')
  rcases h.std.extremal.setup.irr.eq_bot_or_eq hinv le_top with h0 | h0
  · have hvF : v ∈ fixedSpace G := hGv
    rw [h0] at hvF
    exact h.ne ((Submodule.mem_bot _).1 hvF)
  · apply h.L_ne_bot
    rw [eq_bot_iff]
    intro l hl
    exact (Subgroup.mem_bot).2 (fixedSpace_eq_top_iff.1 h0 l (h.L_le_G hl))

theorem card_lt : Nat.card (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range < Nat.card G := by
  calc Nat.card (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range ≤ Nat.card ↥(bbH₁ G L z v) :=
        Nat.card_le_card_of_surjective _
          (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).rangeRestrict_surjective
    _ ≤ Nat.card ↥(G ⊓ vFix v) := Subgroup.card_le_of_le h.H₁_le_H₀
    _ < Nat.card G := Subgroup.card_lt_of_lt h.H₀_lt_G

end Hyp

theorem sub_one_pow_two_pow_of_two_eq_zero {R : Type*} [Ring R] (h2 : (2 : R) = 0) (x : R)
    (k : ℕ) : (x - 1) ^ 2 ^ k = x ^ 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsq : ∀ y : R, (y - 1) ^ 2 = y ^ 2 - 1 := fun y => by
      have : (y - 1) ^ 2 = y ^ 2 - 1 - 2 * (y - 1) := by noncomm_ring
      rw [this, h2, zero_mul, sub_zero]
    rw [pow_succ, pow_mul, pow_mul, ih, hsq]

theorem eq_one_of_odd_of_series {x : GLV V} (hodd : Odd (orderOf x))
    {W₀ W₁ : Submodule (ZMod 2) V} (h₂ : ∀ u, x u - u ∈ W₁) (h₁ : ∀ w ∈ W₁, x w - w ∈ W₀)
    (h₀ : ∀ w ∈ W₀, x w = w) : x = 1 := by
  set N : Module.End (ZMod 2) V := (x : Module.End (ZMod 2) V) - 1 with hN
  have hNu : ∀ u, N u = x u - u := fun u => by simp [hN]
  have h3 : N ^ 2 ^ 2 = 0 := by
    ext u
    have e : (N ^ 2 ^ 2) u = N (N (N (N u))) := by
      simp only [show (2 : ℕ) ^ 2 = 4 from rfl, pow_succ, pow_zero, one_mul,
        Module.End.mul_apply]
    rw [e, LinearMap.zero_apply]
    have hw₁ : N u ∈ W₁ := by rw [hNu]; exact h₂ u
    have hw₀ : N (N u) ∈ W₀ := by rw [hNu]; exact h₁ _ hw₁
    have hz : N (N (N u)) = 0 := by rw [hNu, h₀ _ hw₀, sub_self]
    rw [hz, map_zero]
  have h2 : (2 : Module.End (ZMod 2) V) = 0 := by
    ext v
    simp [two_nsmul, add_self_eq_zero_of_zmod]
  have h4 : (x : Module.End (ZMod 2) V) ^ 2 ^ 2 = 1 := by
    have := sub_one_pow_two_pow_of_two_eq_zero h2 (x : Module.End (ZMod 2) V) 2
    rw [← hN, h3] at this
    exact (sub_eq_zero.1 this.symm)
  have hpow := map_pow
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)) x (2 ^ 2)
  have hx4 : x ^ 2 ^ 2 = 1 := LinearEquiv.toLinearMap_injective (hpow.trans h4)
  have hdvd : orderOf x ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hx4
  have hcop : Nat.Coprime (orderOf x) (2 ^ 2) := (Nat.coprime_two_right.2 hodd).pow_right 2
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

namespace Hyp

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} (h : Hyp G L z v)

include h

theorem injective : Function.Injective (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) := by
  set φ := sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ with hφ
  obtain ⟨K, hO⟩ := h.orbitData
  have hnA := Lemma63.not_le_ker h.inv₀ h.inv₁ h.irrSec h.not_trivial hO
  have hperf : ⁅(bbL₀ G L v).subgroupOf (bbH₁ G L z v),
      (bbL₀ G L v).subgroupOf (bbH₁ G L z v)⁆ = (bbL₀ G L v).subgroupOf (bbH₁ G L z v) := by
    rw [← hO.layer_eq]
    exact CFSG.LocalCores.layer_perfect
  have hcomm := hO.commutator_ker_eq_bot hperf le_rfl φ hnA
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : ∀ a ∈ bbL₀ G L v, (x : GLV V) * a = a * x := by
    intro a ha
    have := Subgroup.mem_centralizer_iff.1
      (hcen (show (⟨a, h.L₀_le_H₁ ha⟩ : ↥(bbH₁ G L z v)) ∈ (bbL₀ G L v).subgroupOf _ from ha))
      x hx
    exact congrArg Subtype.val this
  have hodd := h.odd_of_commute x.2 hxc
  have hxL₀ := h.mem_L₀_of_odd x.2 hodd
  have hker : ∀ w ∈ bbW₁ G L v, (x : GLV V) w - w ∈ bbW₀ G L v := by
    intro w hw
    have h1 := congrArg (fun f : GLV (Sect (bbW₀ G L v) (bbW₁ G L v)) =>
      f (Submodule.Quotient.mk ⟨w, hw⟩)) hx
    simp only [hφ, sectHom_mk] at h1
    have h2 := (Submodule.Quotient.eq _).1 h1
    exact h2
  have hx1 : (x : GLV V) = 1 := eq_one_of_odd_of_series hodd
    (fun u => sub_mem_commSpace hxL₀ Submodule.mem_top) hker (fun w hw => hw.1 _ hxL₀)
  exact Subtype.ext hx1

end Hyp

namespace Hyp

variable {G L : Subgroup (GLV V)} {z : GLV V} {v : V} (h : Hyp G L z v)

include h

theorem sect :
    Conf66 (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range
        (((Subgroup.zpowers z).subgroupOf (bbH₁ G L z v)).map
          (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁))
        ((L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) ∧
      FaithfulTildeV ((L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) ∧
      ∀ x : ↥(bbH₁ G L z v), (x : GLV V) ∈ L → sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ x = 1 →
        x = 1 :=
  h.std.extremal.toConf66.conf66_sect h.std.extremal.faithful h.setup6 inf_le_left h.sup_le_H₀
    rfl h.inv₀ h.inv₁ h.irrSec h.not_trivial

theorem concl : Concl66 (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range
    ((L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁)) :=
  h.std.extremal.min _ _ _ _ h.card_lt h.sect.1 h.sect.2.1

theorem layerIn_range : layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range =
    ((bbL₀ G L v).subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) := by
  obtain ⟨K, hO⟩ := h.orbitData
  rw [← Lemma63.map_layerIn_eq hO]
  congr 1
  have h1 : (layerIn (bbH₁ G L z v)).subgroupOf (bbH₁ G L z v) = CFSG.layer ↥(bbH₁ G L z v) :=
    Subgroup.comap_map_eq_self_of_injective (bbH₁ G L z v).subtype_injective _
  rw [h1, hO.layer_eq]

theorem map_mem_layerIn {a : ↥(bbH₁ G L z v)} (ha : (a : GLV V) ∈ bbL₀ G L v) :
    sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ a ∈
      layerIn (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range := by
  rw [h.layerIn_range]
  exact ⟨a, ha, rfl⟩

theorem map_L_ne_range :
    (L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) ≠
      (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁).range := by
  intro heq
  have hH₁L : bbH₁ G L z v ≤ L := by
    intro g hg
    have hmem : sectHom (bbH₁ G L z v) h.inv₀ h.inv₁ ⟨g, hg⟩ ∈
        (L.subgroupOf (bbH₁ G L z v)).map (sectHom (bbH₁ G L z v) h.inv₀ h.inv₁) := by
      rw [heq]
      exact ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨l, hl, hlg⟩ := hmem
    have := h.injective hlg
    subst this
    exact hl
  have hLL₀ : L = bbL₀ G L v := le_antisymm h.L_le_L₀ (h.L₀_le_H₁.trans hH₁L)
  exact h.not_sub (hLL₀ ▸ h.isSubnormal_L₀)

end Hyp

theorem map_conj_eq_self {Γ : Type*} [Group Γ] {H : Subgroup Γ} {x : Γ} (hx : x ∈ H) :
    H.map (MulAut.conj x).toMonoidHom = H := by
  refine le_antisymm ?_ fun y hy => ⟨x⁻¹ * y * x, H.mul_mem (H.mul_mem (H.inv_mem hx) hy) hx, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)
  · simp [MulAut.conj_apply, mul_assoc]

theorem le_normalizer_of_isSubnormal {G L : Subgroup (GLV V)} {z : GLV V} (hstd : StdForm G L z)
    {v : V} (hsub : IsSubnormal L (G ⊓ vFix v)) :
    G ⊓ vFix v ≤ Subgroup.normalizer (L : Set (GLV V)) := by
  have hq : CFSG.Open.IsQuasisimple ↥L := hstd.extremal.setup.component.2.2
  have hcomp : IsComponentOf L (G ⊓ vFix v) := ⟨hsub.le, hsub, hq⟩
  intro x hx
  have hH₀ := map_conj_eq_self hx
  have hcomp' : IsComponentOf (L.map (MulAut.conj x).toMonoidHom) (G ⊓ vFix v) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← hH₀]
      exact Subgroup.map_mono hsub.le
    · have := hsub.map (MulAut.conj x).toMonoidHom
      rwa [hH₀] at this
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (L.equivMapOfInjective _ (MulAut.conj x).injective).symm hq
  rcases CFSG.LocalAnalysis.GLTheoremA.I142N.isComponent_commute_or_eq hcomp hcomp' with
    heq | hc
  · rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      have hmem : (MulAut.conj x).toMonoidHom l ∈ L.map (MulAut.conj x).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hl
      rw [← heq] at hmem
      simpa [MulAut.conj_apply] using hmem
    · intro hl
      have hl' : x * l * x⁻¹ ∈ L.map (MulAut.conj x).toMonoidHom := by
        rw [← heq]
        exact hl
      obtain ⟨y, hy, hyl⟩ := hl'
      have : y = l := by
        have := hyl
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        simpa using this
      rwa [← this]
  · exact absurd hc (hstd.commutator_ne_bot x hx.1)

end BranchB

end CFSG.CGT.Foote82
