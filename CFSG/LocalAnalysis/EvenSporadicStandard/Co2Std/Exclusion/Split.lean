module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.WElem
public import CFSG.GroupTheory.GL52.InvolutionsTransvection

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G} {W : Subgroup G}

private theorem A_le_normalizer_zpowers (h : Hyp G L A T z t) :
    A ≤ Subgroup.normalizer (zpowers z : Set G) := by
  have hzA : z ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h.commute_of_mem (h.jc.le ha)
  have hAz : A ≤ Subgroup.centralizer (zpowers z : Set G) :=
    Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hzA)
  exact hAz.trans (Subgroup.centralizer_le_normalizer _)

private theorem W_inf_B (h : Hyp G L A T z t) (h3 : E3Facts A z W) :
    W ⊓ B A z = A := by
  refine le_antisymm ?_ (le_inf h3.A_le le_sup_left)
  intro x hx
  obtain ⟨hxW, hxB⟩ := Subgroup.mem_inf.mp hx
  rw [B] at hxB
  have hxB' : x ∈ (A : Set G) * (zpowers z : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A (zpowers z)
      (A_le_normalizer_zpowers h)]
    exact hxB
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hxB'
  have hbW : b ∈ W := by
    have h := W.mul_mem (W.inv_mem (h3.A_le ha)) hxW
    simpa using h
  rcases eq_one_or_eq_of_mem_zpowers h.set.z_sq hb with rfl | rfl
  · simpa using ha
  · exact absurd hbW h3.z_not_mem

private abbrev Esub (L : Subgroup G) (t : G) : Subgroup G :=
  L ⊓ Subgroup.centralizer ({t} : Set G)

private abbrev Ssub (L : Subgroup G) (t z : G) : Subgroup G :=
  Esub L t ⊔ zpowers z

private theorem A_le_Esub (h : Hyp G L A T z t) : A ≤ Esub L t := by
  haveI : IsElementaryAbelian 2 A := h.jc.module.elemAb
  intro a ha
  refine ⟨h.jc.le ha, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨t, h.jc.t_mem⟩))

private theorem Esub_le_centralizer_zpowers (h : Hyp G L A T z t) :
    Esub L t ≤ Subgroup.centralizer (zpowers z : Set G) := by
  rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro e he
  exact h.commute_of_mem he.1

private theorem Esub_le_normalizer_zpowers (h : Hyp G L A T z t) :
    Esub L t ≤ Subgroup.normalizer (zpowers z : Set G) :=
  (Esub_le_centralizer_zpowers h).trans (Subgroup.centralizer_le_normalizer _)

private theorem commutator_Esub (h : Hyp G L A T z t) : ⁅Esub L t, Esub L t⁆ = Esub L t := by
  haveI : Group.IsPerfect ↥(Esub L t) := Group.isPerfect_def.mpr h.jc.perfectE
  exact Subgroup.commutator_eq_self

private theorem mem_Ssub_iff (h : Hyp G L A T z t) {u : G} :
    u ∈ Ssub L t z ↔ ∃ e ∈ Esub L t, ∃ b ∈ zpowers z, e * b = u := by
  constructor
  · intro hu
    have hu' : u ∈ (Esub L t : Set G) * (zpowers z : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Esub L t) (zpowers z)
        (Esub_le_normalizer_zpowers h)]
      exact hu
    exact Set.mem_mul.mp hu'
  · rintro ⟨e, he, b, hb, rfl⟩
    have hu' : e * b ∈ (Esub L t : Set G) * (zpowers z : Set G) :=
      Set.mem_mul.mpr ⟨e, he, b, hb, rfl⟩
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Esub L t) (zpowers z)
      (Esub_le_normalizer_zpowers h)] at hu'
    simpa [Ssub] using hu'

private theorem centralizer_inf_eq (h : Hyp G L A T z t) :
    Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) =
      Ssub L t z := by
  refine le_antisymm ?_ ?_
  · intro u hu
    obtain ⟨hut, huz⟩ := Subgroup.mem_inf.mp hu
    have hut' : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp hut
    have huz' : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.mp huz
    have hLnorm : L ≤ Subgroup.normalizer (zpowers z : Set G) := by
      have hzL : z ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact h.commute_of_mem hl
      have hL : L ≤ Subgroup.centralizer (zpowers z : Set G) :=
        Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hzL)
      exact hL.trans (Subgroup.centralizer_le_normalizer _)
    have huLz : u ∈ L ⊔ zpowers z := by
      rw [← h.set.centralizer_z]
      exact huz
    have hu' : u ∈ (L : Set G) * (zpowers z : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L (zpowers z) hLnorm]
      exact huLz
    obtain ⟨l, hl, b, hb, rfl⟩ := Set.mem_mul.mp hu'
    have hbt : b * t = t * b := by
      have hzT : z ∈ Subgroup.centralizer ({t} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (h.commute_of_mem (A_le_Esub h h.jc.t_mem).1).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.zpowers_le.mpr hzT) hb)
    have hlt : l * t = t * l := by
      have hb' : Commute b t := hbt
      have hbinv : b⁻¹ * t = t * b⁻¹ := hb'.inv_left.eq
      have h1 : (l * b) * t = t * (l * b) := hut'
      calc l * t = (l * b) * (b⁻¹ * t) := by group
        _ = (l * b) * (t * b⁻¹) := by rw [hbinv]
        _ = ((l * b) * t) * b⁻¹ := by group
        _ = (t * (l * b)) * b⁻¹ := by rw [h1]
        _ = t * l := by group
    have hlE : l ∈ Esub L t :=
      ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr hlt⟩
    rw [mem_Ssub_iff h]
    exact ⟨l, hlE, b, hb, rfl⟩
  · refine sup_le ?_ ?_
    · intro e he
      refine Subgroup.mem_inf.mpr ⟨he.2, ?_⟩
      rw [h.set.centralizer_z]
      exact Subgroup.mem_sup_left he.1
    · intro b hb
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp
            ((Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
              (h.commute_of_mem (A_le_Esub h h.jc.t_mem).1).symm)) hb))
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact ((Commute.refl z).zpow_left m).eq

private theorem commutator_Ssub_le (h : Hyp G L A T z t) :
    ⁅Ssub L t z, Ssub L t z⁆ ≤ Esub L t := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨e1, he1, b1, hb1, rfl⟩ := (mem_Ssub_iff h).mp hx
  obtain ⟨e2, he2, b2, hb2, rfl⟩ := (mem_Ssub_iff h).mp hy
  have hb1E : b1 ∈ Subgroup.centralizer (Esub L t : Set G) := by
    have hzE : z ∈ Subgroup.centralizer (Esub L t : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact h.commute_of_mem he.1
    exact (Subgroup.zpowers_le.mpr hzE) hb1
  have hb2E : b2 ∈ Subgroup.centralizer (Esub L t : Set G) := by
    have hzE : z ∈ Subgroup.centralizer (Esub L t : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact h.commute_of_mem he.1
    exact (Subgroup.zpowers_le.mpr hzE) hb2
  have hb1b2 : Commute b1 b2 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb1
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb2
    exact (Commute.refl z).zpow_left k |>.zpow_right l
  have hb1e2 : Commute b1 e2 :=
    (Subgroup.mem_centralizer_iff.mp hb1E e2 he2).symm
  have he1b2 : Commute e1 b2 := Subgroup.mem_centralizer_iff.mp hb2E e1 he1
  have hc1 : Commute b1 (e2 * b2) := hb1e2.mul_right hb1b2
  have hcomm_eq : ⁅e1 * b1, e2 * b2⁆ = ⁅e1, e2⁆ := by
    calc ⁅e1 * b1, e2 * b2⁆
        = e1 * ⁅b1, e2 * b2⁆ * e1⁻¹ * ⁅e1, e2 * b2⁆ :=
          commutatorElement_mul_left_eq_conj_mul e1 b1 (e2 * b2)
      _ = e1 * 1 * e1⁻¹ * ⁅e1, e2 * b2⁆ := by rw [hc1.commutator_eq]
      _ = ⁅e1, e2 * b2⁆ := by group
      _ = ⁅e1, e2⁆ * e2 * ⁅e1, b2⁆ * e2⁻¹ :=
          commutatorElement_mul_right_eq_mul_conj e1 e2 b2
      _ = ⁅e1, e2⁆ * e2 * 1 * e2⁻¹ := by rw [he1b2.commutator_eq]
      _ = ⁅e1, e2⁆ := by group
  rw [hcomm_eq, ← commutator_Esub h]
  exact Subgroup.commutator_mem_commutator he1 he2

private theorem commutator_Ssub (h : Hyp G L A T z t) :
    ⁅Ssub L t z, Ssub L t z⁆ = Esub L t := by
  refine le_antisymm (commutator_Ssub_le h) ?_
  calc Esub L t = ⁅Esub L t, Esub L t⁆ := (commutator_Esub h).symm
    _ ≤ ⁅Ssub L t z, Ssub L t z⁆ := Subgroup.commutator_mono le_sup_left le_sup_left

private theorem conj_mem_Ssub (h : Hyp G L A T z t) {g u : G} (hgt : Commute g t)
    (hgz : g * z * g⁻¹ = z * t) (hu : u ∈ Ssub L t z) : g * u * g⁻¹ ∈ Ssub L t z := by
  have huC : u ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
    rw [centralizer_inf_eq h]
    exact hu
  have hut : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp huC.1
  have huz : u * z = z * u := Subgroup.mem_centralizer_singleton_iff.mp huC.2
  have hcomm_t : (g * u * g⁻¹) * t = t * (g * u * g⁻¹) := by
    have hginv : Commute g⁻¹ t := hgt.inv_left
    calc g * u * g⁻¹ * t = g * u * (g⁻¹ * t) := by group
      _ = g * u * (t * g⁻¹) := by rw [hginv.eq]
      _ = g * (u * t) * g⁻¹ := by group
      _ = g * (t * u) * g⁻¹ := by rw [hut]
      _ = (g * t) * u * g⁻¹ := by group
      _ = (t * g) * u * g⁻¹ := by rw [hgt.eq]
      _ = t * (g * u * g⁻¹) := by group
  have hcomm_zt : (g * u * g⁻¹) * (z * t) = (z * t) * (g * u * g⁻¹) := by
    calc (g * u * g⁻¹) * (z * t) = (g * u * g⁻¹) * (g * z * g⁻¹) := by rw [hgz]
      _ = g * (u * z) * g⁻¹ := by group
      _ = g * (z * u) * g⁻¹ := by rw [huz]
      _ = (g * z * g⁻¹) * (g * u * g⁻¹) := by group
      _ = (z * t) * (g * u * g⁻¹) := by rw [hgz]
  have hzt : (z * t) * t = z := by rw [mul_assoc, h.set.t_sq, mul_one]
  have hcomm_z : (g * u * g⁻¹) * z = z * (g * u * g⁻¹) := by
    calc (g * u * g⁻¹) * z = (g * u * g⁻¹) * ((z * t) * t) := by rw [hzt]
      _ = ((g * u * g⁻¹) * (z * t)) * t := by group
      _ = ((z * t) * (g * u * g⁻¹)) * t := by rw [hcomm_zt]
      _ = (z * t) * ((g * u * g⁻¹) * t) := by group
      _ = (z * t) * (t * (g * u * g⁻¹)) := by rw [hcomm_t]
      _ = ((z * t) * t) * (g * u * g⁻¹) := by group
      _ = z * (g * u * g⁻¹) := by rw [hzt]
  rw [← centralizer_inf_eq h]
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm_t,
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm_z⟩

private theorem exists_lift (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) :
    ∃ y : G, y ∈ W ∧ delta z y = t ∧ ∀ e ∈ Esub L t, y * e * y⁻¹ = e := by
  obtain ⟨c, hc⟩ := E3Facts.deltaRestrict_surjective h h2 h3 ⟨t, h.jc.t_mem⟩
  have hcG : delta z (c : G) = t := congrArg Subtype.val hc
  have hcR : (c : G) ∈ R₀ A z := h3.le_R₀ c.2
  have hcA : (c : G) ∈ Subgroup.centralizer (A : Set G) := hcR.2
  have hct : Commute (c : G) t :=
    (Subgroup.mem_centralizer_iff.mp hcA t h.jc.t_mem).symm
  have hcz : (c : G) * z * (c : G)⁻¹ = z * t := by
    have h := mul_delta z (c : G)
    rw [hcG] at h
    exact h.symm
  have hcS : (c : G) ∈ Subgroup.normalizer (Ssub L t z : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      simpa [MulAut.conj_apply] using conj_mem_Ssub h hct hcz hu
    · rw [Subgroup.card_map_of_injective (MulAut.conj (c : G)).injective]
  have hmapE : (Esub L t).map (MulAut.conj (c : G)) = Esub L t := by
    rw [← commutator_Ssub h]
    rw [Subgroup.map_commutator]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq.mp hcS]
  let α : MulAut ↥(Esub L t) :=
    (MulEquiv.subgroupMap (MulAut.conj (c : G)) (Esub L t)).trans
      (MulEquiv.subgroupCongr hmapE)
  obtain ⟨e0, he0⟩ := h.jc.outE α
  have hα_apply : ∀ x : ↥(Esub L t),
      ((α x : ↥(Esub L t)) : G) = (c : G) * (x : G) * (c : G)⁻¹ := by
    intro x
    change (((MulEquiv.subgroupCongr hmapE)
      ((MulEquiv.subgroupMap (MulAut.conj (c : G)) (Esub L t)) x : _)) : G) = _
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  have he0_apply : ∀ x : ↥(Esub L t),
      (e0 : G) * (x : G) * (e0 : G)⁻¹ = (c : G) * (x : G) * (c : G)⁻¹ := by
    intro x
    calc (e0 : G) * (x : G) * (e0 : G)⁻¹ =
          ((MulAut.conj e0 x : ↥(Esub L t)) : G) := by
          rw [show ((MulAut.conj e0 x : ↥(Esub L t)) : G) = (e0 : G) * (x : G) * (e0 : G)⁻¹
            from congrArg Subtype.val (MulAut.conj_apply e0 x)]
      _ = ((α x : ↥(Esub L t)) : G) := by rw [← he0]
      _ = (c : G) * (x : G) * (c : G)⁻¹ := hα_apply x
  have he0_fixes_A : ∀ a ∈ A, (e0 : G) * a * (e0 : G)⁻¹ = a := by
    intro a ha
    have h1 := he0_apply ⟨a, A_le_Esub h ha⟩
    have hca : a * (c : G) = (c : G) * a :=
      Subgroup.mem_centralizer_iff.mp hcA a ha
    have h2 : (c : G) * a * (c : G)⁻¹ = a := by
      calc (c : G) * a * (c : G)⁻¹ = a * ((c : G) * (c : G)⁻¹) := by
            rw [hca.symm]; group
        _ = a := by group
    rw [h1, h2]
  have he0_cent : (e0 : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := he0_fixes_A a ha
    calc a * (e0 : G) = (e0 : G) * a * (e0 : G)⁻¹ * (e0 : G) := by rw [h]
      _ = (e0 : G) * a := by group
  have he0A : (e0 : G) ∈ A := by
    rw [← h.jc.centralizer_eq]
    exact ⟨(e0 : ↥(Esub L t)).2.1, he0_cent⟩
  have hyW : (e0 : G)⁻¹ * (c : G) ∈ W :=
    W.mul_mem (W.inv_mem (h3.A_le he0A)) c.2
  have hAB : A ≤ B A z := le_sup_left
  have hdelta_e0 : delta z (e0 : G) = 1 :=
    (h.delta_eq_one_iff h2 (h.B_le_R₀ (hAB he0A))).mpr (hAB he0A)
  have hdelta_e0inv : delta z (e0 : G)⁻¹ = 1 :=
    (h.delta_eq_one_iff h2 ((R₀ A z).inv_mem (h.B_le_R₀ (hAB he0A)))).mpr
      ((B A z).inv_mem (hAB he0A))
  have hydelta : delta z ((e0 : G)⁻¹ * (c : G)) = t := by
    rw [h2.delta_mul ((R₀ A z).inv_mem (h.B_le_R₀ (hAB he0A))) hcR,
      hdelta_e0inv, hcG, one_mul]
  refine ⟨(e0 : G)⁻¹ * (c : G), hyW, hydelta, ?_⟩
  intro e he
  have h1 := he0_apply ⟨e, he⟩
  calc (e0 : G)⁻¹ * (c : G) * e * ((e0 : G)⁻¹ * (c : G))⁻¹
      = (e0 : G)⁻¹ * ((c : G) * e * (c : G)⁻¹) * (e0 : G) := by group
    _ = (e0 : G)⁻¹ * ((e0 : G) * e * (e0 : G)⁻¹) * (e0 : G) := by rw [← h1]
    _ = e := by group

private theorem A_le_centralizer_W (h : Hyp G L A T z t) (h3 : E3Facts A z W) :
    A ≤ Subgroup.centralizer (W : Set G) :=
  Subgroup.le_centralizer_iff.mpr (h3.le_R₀.trans inf_le_right)

private theorem mul_comm_of_mem_W (hW : IsElementaryAbelian 2 W) {u v : G}
    (hu : u ∈ W) (hv : v ∈ W) : u * v = v * u := by
  haveI : IsElementaryAbelian 2 W := hW
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := W)).comm ⟨u, hu⟩ ⟨v, hv⟩)

private theorem mul_comm_of_mem_A (h : Hyp G L A T z t) {u v : G}
    (hu : u ∈ A) (hv : v ∈ A) : u * v = v * u := by
  haveI : IsElementaryAbelian 2 A := h.jc.module.elemAb
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨u, hu⟩ ⟨v, hv⟩)

private theorem sq_eq_one_of_mem_W (hW : IsElementaryAbelian 2 W) {w : G} (hw : w ∈ W) :
    w * w = 1 := by
  haveI : IsElementaryAbelian 2 W := hW
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw
  simpa [pow_two] using h

private theorem sq_eq_one_of_mem_A (h : Hyp G L A T z t) {a : G} (ha : a ∈ A) :
    a * a = 1 := by
  haveI : IsElementaryAbelian 2 A := h.jc.module.elemAb
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  simpa [pow_two] using h

private structure DeltaSection (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) where
  s : A →* W
  delta_s : ∀ a, E3Facts.deltaRestrict h2 h3 (s a) = a

private noncomputable def deltaSectionAux (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) :
    DeltaSection h h2 h3 hW := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hA : IsElementaryAbelian 2 A := h.jc.module.elemAb
  haveI hW' : IsElementaryAbelian 2 W := hW
  let f : Additive W →ₗ[ZMod 2] Additive A :=
    (MonoidHom.toAdditive (E3Facts.deltaRestrict h2 h3)).toZModLinearMap 2
  have hf : f.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro a
    obtain ⟨w, hw⟩ := E3Facts.deltaRestrict_surjective h h2 h3 (Additive.toMul a)
    refine ⟨Additive.ofMul w, ?_⟩
    change Additive.ofMul (E3Facts.deltaRestrict h2 h3 w) = a
    rw [hw, ofMul_toMul]
  let g := Classical.choose (f.exists_rightInverse_of_surjective hf)
  have hg : f ∘ₗ g = LinearMap.id :=
    Classical.choose_spec (f.exists_rightInverse_of_surjective hf)
  refine ⟨{ toFun := fun a => Additive.toMul (g (Additive.ofMul a))
            map_one' := by simp
            map_mul' := ?_ }, ?_⟩
  · intro a b
    show Additive.toMul (g (Additive.ofMul (a * b))) =
      Additive.toMul (g (Additive.ofMul a)) * Additive.toMul (g (Additive.ofMul b))
    rw [ofMul_mul, map_add, toMul_add]
  · intro a
    have h := LinearMap.congr_fun hg (Additive.ofMul a)
    have h' : f (g (Additive.ofMul a)) = Additive.ofMul a := by simpa using h
    change E3Facts.deltaRestrict h2 h3 (Additive.toMul (g (Additive.ofMul a))) = a
    have h'' := congrArg Additive.toMul h'
    simpa [f] using h''

private noncomputable def conjA (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) : A :=
  ⟨(x : G) * (b : G) * (x : G)⁻¹, (Subgroup.mem_normalizer_iff.mp x.2.2 b).mp b.2⟩

private noncomputable def conjAInv (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) : A :=
  ⟨(x : G)⁻¹ * (b : G) * (x : G), (Subgroup.mem_normalizer_iff''.mp x.2.2 b).mp b.2⟩

@[simp]
private theorem conjA_apply (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) :
    (conjA x b : G) = (x : G) * (b : G) * (x : G)⁻¹ := rfl

@[simp]
private theorem conjAInv_apply (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) :
    (conjAInv x b : G) = (x : G)⁻¹ * (b : G) * (x : G) := rfl

private theorem delta_inv_mul (h2 : E2Facts L A z) {r : G} (hr : r ∈ R₀ A z) :
    delta z r⁻¹ * delta z r = 1 := by
  rw [delta_inv_of_conj_mem h2.conj_mem hr, inv_mul_cancel]

private noncomputable def gammaRaw (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) : A :=
  ⟨(S.s b : G)⁻¹ * ((x : G) * (S.s (conjAInv x b) : W) * (x : G)⁻¹),
    gammaRaw_mem h h2 h3 hW S x b⟩
where
  gammaRaw_mem (h : Hyp G L A T z t) (h2 : E2Facts L A z) (h3 : E3Facts A z W)
      (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
      (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) :
      (S.s b : G)⁻¹ * ((x : G) * (S.s (conjAInv x b) : W) * (x : G)⁻¹) ∈ A := by
    have hxM : (x : G) ∈ M A z := h.le_M x.2
    have hqW : (x : G) * (S.s (conjAInv x b) : W) * (x : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (h3.M_le hxM) (S.s (conjAInv x b) : G)).mp
        (S.s (conjAInv x b)).2
    have hWmem : (S.s b : G)⁻¹ * ((x : G) * (S.s (conjAInv x b) : W) * (x : G)⁻¹) ∈ W :=
      W.mul_mem (W.inv_mem (S.s b).2) hqW
    have hqdelta : delta z ((x : G) * (S.s (conjAInv x b) : W) * (x : G)⁻¹) = b := by
      rw [h.delta_conj (x := (x : G)) (r := (S.s (conjAInv x b) : W)) x.2.1]
      rw [show delta z (S.s (conjAInv x b) : G) = (conjAInv x b : G) from
        congrArg Subtype.val (S.delta_s (conjAInv x b))]
      simp only [conjAInv, Subgroup.coe_mk]
      group
    have hsb : delta z (S.s b : G) = b := congrArg Subtype.val (S.delta_s b)
    have hinv : delta z (S.s b : G)⁻¹ * b = 1 := by
      have h := delta_inv_mul h2 (h3.le_R₀ (S.s b).2)
      rwa [hsb] at h
    have hprod : delta z ((S.s b : G)⁻¹ *
        ((x : G) * (S.s (conjAInv x b) : W) * (x : G)⁻¹)) = 1 := by
      rw [h2.delta_mul ((R₀ A z).inv_mem (h3.le_R₀ (S.s b).2)) (h3.le_R₀ hqW), hqdelta]
      exact hinv
    have hB : (S.s b : G)⁻¹ * ((x : G) * (S.s (conjAInv x b) : W) * (x : G)⁻¹) ∈ B A z :=
      (h.delta_eq_one_iff h2 (h3.le_R₀ hWmem)).mp hprod
    exact (W_inf_B h h3).le ⟨hWmem, hB⟩

private theorem gammaRaw_mul_of_mem_A (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (x a : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (ha : (a : G) ∈ A) (b : A) :
    gammaRaw h h2 h3 hW S (x * a) b = gammaRaw h h2 h3 hW S x b := by
  apply Subtype.ext
  have hconjA : conjAInv (x * a) b = conjAInv x b := by
    apply Subtype.ext
    simp only [conjAInv, Subgroup.coe_mk]
    have hcomm : (a : G) * ((x : G)⁻¹ * (b : G) * (x : G)) =
        ((x : G)⁻¹ * (b : G) * (x : G)) * (a : G) :=
      mul_comm_of_mem_A h ha (conjAInv x b).2
    have hcomm_inv : (a : G)⁻¹ * ((x : G)⁻¹ * (b : G) * (x : G)) =
        ((x : G)⁻¹ * (b : G) * (x : G)) * (a : G)⁻¹ := by
      calc (a : G)⁻¹ * ((x : G)⁻¹ * (b : G) * (x : G)) =
            (a : G)⁻¹ * (((x : G)⁻¹ * (b : G) * (x : G)) * (a : G)) * (a : G)⁻¹ := by
            group
        _ = (a : G)⁻¹ * ((a : G) * ((x : G)⁻¹ * (b : G) * (x : G))) * (a : G)⁻¹ := by
            rw [← hcomm]
        _ = ((x : G)⁻¹ * (b : G) * (x : G)) * (a : G)⁻¹ := by group
    calc ((x : G) * (a : G))⁻¹ * (b : G) * ((x : G) * (a : G)) =
          (a : G)⁻¹ * ((x : G)⁻¹ * (b : G) * (x : G)) * (a : G) := by group
      _ = (((x : G)⁻¹ * (b : G) * (x : G)) * (a : G)⁻¹) * (a : G) := by
          rw [hcomm_inv]
      _ = (x : G)⁻¹ * (b : G) * (x : G) := by group
  have hcomm_s : (a : G) * (S.s (conjAInv x b) : G) =
      (S.s (conjAInv x b) : G) * (a : G) :=
    (Subgroup.mem_centralizer_iff.mp (A_le_centralizer_W h h3 ha)
      (S.s (conjAInv x b) : G) (S.s (conjAInv x b)).2).symm
  simp only [gammaRaw, Subgroup.coe_mk]
  rw [hconjA]
  have hxa : ((x * a : ↥(L ⊓ Subgroup.normalizer (A : Set G))) : G) = (x : G) * (a : G) :=
    rfl
  have hxas : (x : G) * (a : G) * (S.s (conjAInv x b) : G) * ((x : G) * (a : G))⁻¹ =
      (x : G) * (S.s (conjAInv x b) : G) * (x : G)⁻¹ := by
    calc (x : G) * (a : G) * (S.s (conjAInv x b) : G) * ((x : G) * (a : G))⁻¹
        = (x : G) * ((a : G) * (S.s (conjAInv x b) : G)) * ((x : G) * (a : G))⁻¹ := by
          group
      _ = (x : G) * ((S.s (conjAInv x b) : G) * (a : G)) * ((x : G) * (a : G))⁻¹ := by
          rw [hcomm_s]
      _ = (x : G) * (S.s (conjAInv x b) : G) * (x : G)⁻¹ := by group
  rw [hxa, hxas]

private theorem gammaRaw_dep (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    {x y : ↥(L ⊓ Subgroup.normalizer (A : Set G))}
    (hxy : conjN L A x = conjN L A y) (b : A) :
    gammaRaw h h2 h3 hW S x b = gammaRaw h h2 h3 hW S y b := by
  have hker : conjN L A (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, hxy]
    simp
  have haA : (((x⁻¹ * y : ↥(L ⊓ Subgroup.normalizer (A : Set G)))) : G) ∈ A :=
    (conjN_eq_one_iff h.jc.centralizer_eq (x⁻¹ * y)).mp hker
  have hy : y = x * (x⁻¹ * y) := by group
  rw [hy]
  exact (gammaRaw_mul_of_mem_A h h2 h3 hW S x (x⁻¹ * y) haA b).symm

private theorem conjN_eq_conjA (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) :
    conjN L A x b = conjA x b := by
  apply Subtype.ext
  simp [conjN_apply, conjA_apply]

private noncomputable def gamma (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW) :
    ↥(autImage L A) → A → A :=
  fun g b => descend (fun x => gammaRaw h h2 h3 hW S x b) g

private theorem gamma_toAutImage (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) :
    gamma h h2 h3 hW S (toAutImage x) b = gammaRaw h h2 h3 hW S x b :=
  descend_toAutImage (fun x => gammaRaw h h2 h3 hW S x b)
    (fun x y hxy => gammaRaw_dep h h2 h3 hW S hxy b) x

private theorem gammaRaw_mul (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (a b : A) :
    gammaRaw h h2 h3 hW S x (a * b) =
      gammaRaw h h2 h3 hW S x a * gammaRaw h h2 h3 hW S x b := by
  have hconj : conjAInv x (a * b) = conjAInv x a * conjAInv x b := by
    apply Subtype.ext
    simp only [conjAInv, Subgroup.coe_mk, Subgroup.coe_mul]
    group
  apply Subtype.ext
  simp only [gammaRaw, Subgroup.coe_mk]
  rw [Subgroup.coe_mul]
  have hsaW : (S.s a : G) ∈ W := (S.s a).2
  have hsbW : (S.s b : G) ∈ W := (S.s b).2
  have hqaw : x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (h3.M_le (h.le_M x.2))
      (S.s (conjAInv x a) : G)).mp (S.s (conjAInv x a)).2
  have hqbw : x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (h3.M_le (h.le_M x.2))
      (S.s (conjAInv x b) : G)).mp (S.s (conjAInv x b)).2
  have hL : (S.s (a * b) : G)⁻¹ * (x.1 * (S.s (conjAInv x (a * b)) : G) * x.1⁻¹) =
      (S.s b : G)⁻¹ * (S.s a : G)⁻¹ *
        (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹) *
        (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹) := by
    rw [show S.s (a * b) = S.s a * S.s b from map_mul S.s a b]
    rw [show S.s (conjAInv x (a * b)) = S.s (conjAInv x a) * S.s (conjAInv x b) from by
      rw [hconj]
      exact map_mul S.s _ _]
    simp only [Subgroup.coe_mul]
    rw [mul_inv_rev]
    group
  have hR : ((S.s a : G)⁻¹ * (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹)) *
      ((S.s b : G)⁻¹ * (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹)) =
      (S.s b : G)⁻¹ * (S.s a : G)⁻¹ *
        (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹) *
        (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹) := by
    have h1 : (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹) * (S.s b : G)⁻¹ =
        (S.s b : G)⁻¹ * (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹) :=
      mul_comm_of_mem_W hW hqaw (W.inv_mem hsbW)
    have h2 : (S.s b : G)⁻¹ * (S.s a : G)⁻¹ =
        (S.s a : G)⁻¹ * (S.s b : G)⁻¹ :=
      mul_comm_of_mem_W hW (W.inv_mem hsbW) (W.inv_mem hsaW)
    calc ((S.s a : G)⁻¹ * (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹)) *
          ((S.s b : G)⁻¹ * (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹))
        = (S.s a : G)⁻¹ *
            ((x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹) * (S.s b : G)⁻¹) *
            (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹) := by group
      _ = (S.s a : G)⁻¹ * ((S.s b : G)⁻¹ *
            (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹)) *
            (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹) := by rw [h1]
      _ = (S.s a : G)⁻¹ * (S.s b : G)⁻¹ *
            (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹) *
            (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹) := by group
      _ = (S.s b : G)⁻¹ * (S.s a : G)⁻¹ *
            (x.1 * (S.s (conjAInv x a) : G) * x.1⁻¹) *
            (x.1 * (S.s (conjAInv x b) : G) * x.1⁻¹) := by rw [h2]
  rw [hL, hR]

private theorem gamma_mul (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (g : ↥(autImage L A)) (a b : A) :
    gamma h h2 h3 hW S g (a * b) = gamma h h2 h3 hW S g a * gamma h h2 h3 hW S g b := by
  obtain ⟨x, hx⟩ := exists_toAutImage_eq g
  subst hx
  rw [gamma_toAutImage, gamma_toAutImage, gamma_toAutImage, gammaRaw_mul]

private theorem gammaRaw_cocycle (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (x y : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (a : A) :
    gammaRaw h h2 h3 hW S (x * y) a =
      gammaRaw h h2 h3 hW S x a *
        conjA x (gammaRaw h h2 h3 hW S y (conjAInv x a)) := by
  have hconj : conjAInv (x * y) a = conjAInv y (conjAInv x a) := by
    apply Subtype.ext
    simp only [conjAInv, Subgroup.coe_mk, Subgroup.coe_mul]
    group
  apply Subtype.ext
  simp only [gammaRaw, Subgroup.coe_mk, conjA]
  rw [hconj]
  simp only [Subgroup.coe_mul]
  group

private theorem gamma_cocycle (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (g g' : ↥(autImage L A)) (a : A) :
    gamma h h2 h3 hW S (g * g') a =
      gamma h h2 h3 hW S g a *
        (g : MulAut A) (gamma h h2 h3 hW S g' ((g : MulAut A)⁻¹ a)) := by
  obtain ⟨x, rfl⟩ := exists_toAutImage_eq g
  obtain ⟨y, rfl⟩ := exists_toAutImage_eq g'
  have hinv : (toAutImage x : ↥(autImage L A))⁻¹ = toAutImage x⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← toAutImage_mul, mul_inv_cancel, toAutImage_one]
  have harg : (((toAutImage x : ↥(autImage L A)) : MulAut A)⁻¹) a = conjAInv x a := by
    have h1 : (((toAutImage x : ↥(autImage L A)) : MulAut A)⁻¹) =
        ((toAutImage x⁻¹ : ↥(autImage L A)) : MulAut A) := by
      rw [← Subgroup.coe_inv, hinv]
    rw [h1]
    apply Subtype.ext
    rw [show ((toAutImage x⁻¹ : ↥(autImage L A)) : MulAut A) = conjN L A x⁻¹ from rfl,
      conjN_apply, conjAInv_apply]
    simp
  rw [← toAutImage_mul, gamma_toAutImage, gamma_toAutImage, harg, gamma_toAutImage]
  change gammaRaw h h2 h3 hW S (x * y) a =
    gammaRaw h h2 h3 hW S x a *
      conjN L A x (gammaRaw h h2 h3 hW S y (conjAInv x a))
  rw [conjN_eq_conjA]
  exact gammaRaw_cocycle h h2 h3 hW S x y a

private theorem exists_fixed_lift (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    {y : G} (hyW : y ∈ W) (hydelta : delta z y = t)
    (hyE : ∀ e ∈ Esub L t, y * e * y⁻¹ = e) :
    ∃ u : A, ∀ g : ↥(autImage L A),
      (g : MulAut A) ⟨t, h.jc.t_mem⟩ = ⟨t, h.jc.t_mem⟩ →
      gamma h h2 h3 hW S g ⟨t, h.jc.t_mem⟩ = u * (g : MulAut A) u := by
  let tA : A := ⟨t, h.jc.t_mem⟩
  have hst : delta z (S.s tA : G) = t := by
    have h := congrArg Subtype.val (S.delta_s tA)
    rw [E3Facts.coe_deltaRestrict] at h
    simpa [tA] using h
  have hst_inv_delta : delta z (S.s tA : G)⁻¹ * t = 1 := by
    have h := delta_inv_mul h2 (h3.le_R₀ (S.s tA).2)
    rwa [hst] at h
  have huW : (S.s tA : G)⁻¹ * y ∈ W := W.mul_mem (W.inv_mem (S.s tA).2) hyW
  have huB : (S.s tA : G)⁻¹ * y ∈ B A z := by
    refine (h.delta_eq_one_iff h2 (h3.le_R₀ huW)).mp ?_
    rw [h2.delta_mul ((R₀ A z).inv_mem (h3.le_R₀ (S.s tA).2)) (h3.le_R₀ hyW), hydelta]
    exact hst_inv_delta
  have huA : (S.s tA : G)⁻¹ * y ∈ A := (W_inf_B h h3).le ⟨huW, huB⟩
  refine ⟨⟨(S.s tA : G)⁻¹ * y, huA⟩, ?_⟩
  intro g hg
  obtain ⟨x, hx⟩ := exists_toAutImage_eq g
  subst hx
  have hxtA : conjN L A x tA = tA := hg
  have hxt : (x : G) * t * (x : G)⁻¹ = t := by
    have h := congrArg Subtype.val hxtA
    rw [conjN_apply] at h
    simpa [tA] using h
  have hxt' : (x : G)⁻¹ * t * (x : G) = t := by
    have hconj := congrArg (fun a => (x : G)⁻¹ * a * (x : G)) hxt
    rw [← hconj]
    group
  have hxE : (x : G) ∈ Esub L t := by
    refine ⟨x.2.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc (x : G) * t = (x : G) * t * (x : G)⁻¹ * (x : G) := by group
        _ = t * (x : G) := by rw [hxt])
  have hxy : (x : G) * y * (x : G)⁻¹ = y := by
    have hcomm := hyE (x : G) hxE
    have hyx : y * (x : G) = (x : G) * y := by
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [hcomm]
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [hyx.symm]
      _ = y := by
        simp only [zpow_neg_one, Subgroup.coe_inv]
        group
  have hconj_t : conjAInv x tA = tA := by
    apply Subtype.ext
    simp only [conjAInv, Subgroup.coe_mk]
    simpa [tA] using hxt'
  have hstW : (S.s tA : G) ∈ W := (S.s tA).2
  have hsq_st : (S.s tA : G) * (S.s tA : G) = 1 := sq_eq_one_of_mem_W hW hstW
  have hst_inv : (S.s tA : G)⁻¹ = (S.s tA : G) := inv_eq_of_mul_eq_one_left hsq_st
  have hDW : (x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (h3.M_le (h.le_M x.2)) (S.s tA : G)⁻¹).mp
      (W.inv_mem hstW)
  have hyD : y * ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) =
      ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) * y :=
    mul_comm_of_mem_W hW hyW hDW
  have hsq_y : y * y = 1 := sq_eq_one_of_mem_W hW hyW
  rw [gamma_toAutImage]
  simp only [coe_toAutImage]
  rw [conjN_eq_conjA]
  simp only [gammaRaw, Subgroup.coe_mk, conjA, hconj_t, tA]
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have hL : (S.s tA : G)⁻¹ * ((x : G) * (S.s tA : G) * (x : G)⁻¹) =
      (S.s tA : G)⁻¹ * (x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹ := by
    rw [hst_inv]
    group
  have hR : (⟨(S.s tA : G)⁻¹ * y, huA⟩ : A) *
      ((x : G) * ((⟨(S.s tA : G)⁻¹ * y, huA⟩ : A) : G) * (x : G)⁻¹) =
      (S.s tA : G)⁻¹ * (x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹ := by
    simp only [Subgroup.coe_mk]
    have hstep : (x : G) * ((S.s tA : G)⁻¹ * y) * (x : G)⁻¹ =
        ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) * y := by
      calc (x : G) * ((S.s tA : G)⁻¹ * y) * (x : G)⁻¹
          = ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) * ((x : G) * y * (x : G)⁻¹) := by
            group
        _ = ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) * y := by rw [hxy]
    calc ((S.s tA : G)⁻¹ * y) * ((x : G) * ((S.s tA : G)⁻¹ * y) * (x : G)⁻¹)
        = ((S.s tA : G)⁻¹ * y) *
            (((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) * y) := by rw [hstep]
      _ = ((S.s tA : G)⁻¹ * y) *
            (y * ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹)) := by rw [hyD]
      _ = (S.s tA : G)⁻¹ * (y * y) *
            ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) := by group
      _ = (S.s tA : G)⁻¹ * ((x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹) := by
          rw [hsq_y]
          group
      _ = (S.s tA : G)⁻¹ * (x : G) * (S.s tA : G)⁻¹ * (x : G)⁻¹ := by group
  rw [hL, hR]

private noncomputable def sec' (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : A →* W where
  toFun a := S.s a * Subgroup.inclusion h3.A_le (X a)
  map_one' := by simp
  map_mul' a b := by
    show S.s (a * b) * Subgroup.inclusion h3.A_le (X (a * b)) =
      (S.s a * Subgroup.inclusion h3.A_le (X a)) *
        (S.s b * Subgroup.inclusion h3.A_le (X b))
    rw [show S.s (a * b) = S.s a * S.s b from map_mul S.s a b]
    rw [show X (a * b) = X a * X b from map_mul X a b]
    rw [map_mul]
    ac_rfl

@[simp]
private theorem sec'_apply (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) (a : A) :
    ((sec' h h2 h3 hW S X a : W) : G) = (S.s a : G) * (X a : G) := rfl

private theorem deltaRestrict_sec' (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) (a : A) :
    E3Facts.deltaRestrict h2 h3 (sec' h h2 h3 hW S X a) = a := by
  apply Subtype.ext
  change delta z ((sec' h h2 h3 hW S X a : W) : G) = (a : G)
  rw [sec'_apply]
  have hXW : (X a : G) ∈ W := h3.A_le (X a).2
  have hXdelta : delta z (X a : G) = 1 := by
    have hAB : A ≤ B A z := le_sup_left
    exact (h.delta_eq_one_iff h2 (h.B_le_R₀ (hAB (X a).2))).mpr (hAB (X a).2)
  rw [h2.delta_mul (h3.le_R₀ (S.s a).2) (h3.le_R₀ hXW),
    show delta z (S.s a : G) = a from congrArg Subtype.val (S.delta_s a), hXdelta, mul_one]

private theorem sec'_injective (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : Function.Injective (sec' h h2 h3 hW S X) := by
  intro a b hab
  have h := congrArg (E3Facts.deltaRestrict h2 h3) hab
  rwa [deltaRestrict_sec', deltaRestrict_sec'] at h

private theorem sec'_conj (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A)
    (hX : ∀ g a, gamma h h2 h3 hW S g a =
      X a * (g : MulAut A) (X ((g : MulAut A)⁻¹ a)))
    (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) (b : A) :
    (x : G) * ((sec' h h2 h3 hW S X b : W) : G) * (x : G)⁻¹ =
      ((sec' h h2 h3 hW S X (conjN L A x b) : W) : G) := by
  let c : A := conjA x b
  have hc : conjAInv x c = b := by
    apply Subtype.ext
    simp only [c, conjA, conjAInv, Subgroup.coe_mk]
    group
  have hcN : conjN L A x b = c := conjN_eq_conjA x b
  have hx_s : (x : G) * (S.s b : G) * (x : G)⁻¹ =
      (S.s c : G) * (gammaRaw h h2 h3 hW S x c : G) := by
    simp only [gammaRaw, Subgroup.coe_mk, c]
    rw [hc]
    group
  have hx_X : (x : G) * (X b : G) * (x : G)⁻¹ = (conjA x (X b) : G) := by
    simp [conjA]
  have hinv_c : (((toAutImage x : ↥(autImage L A)) : MulAut A)⁻¹) c = conjAInv x c := by
    have hinv : (toAutImage x : ↥(autImage L A))⁻¹ = toAutImage x⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← toAutImage_mul, mul_inv_cancel, toAutImage_one]
    have h1 : (((toAutImage x : ↥(autImage L A)) : MulAut A)⁻¹) =
        ((toAutImage x⁻¹ : ↥(autImage L A)) : MulAut A) := by
      rw [← Subgroup.coe_inv, hinv]
    rw [h1]
    apply Subtype.ext
    rw [show ((toAutImage x⁻¹ : ↥(autImage L A)) : MulAut A) = conjN L A x⁻¹ from rfl,
      conjN_apply, conjAInv_apply]
    simp
  have hgamma : gamma h h2 h3 hW S (toAutImage x) c = X c * conjA x (X b) := by
    rw [hX, hinv_c, hc]
    simp only [coe_toAutImage, conjN_eq_conjA]
  have hgammaRaw : gammaRaw h h2 h3 hW S x c = X c * conjA x (X b) := by
    rw [← gamma_toAutImage]
    exact hgamma
  have hD : (conjA x (X b) : G) * (conjA x (X b) : G) = 1 :=
    sq_eq_one_of_mem_A h (conjA x (X b)).2
  rw [sec'_apply, sec'_apply, hcN]
  change (x : G) * ((S.s b : G) * (X b : G)) * (x : G)⁻¹ =
    (S.s c : G) * (X c : G)
  calc (x : G) * ((S.s b : G) * (X b : G)) * (x : G)⁻¹
      = ((x : G) * (S.s b : G) * (x : G)⁻¹) *
          ((x : G) * (X b : G) * (x : G)⁻¹) := by group
    _ = ((S.s c : G) * (gammaRaw h h2 h3 hW S x c : G)) * (conjA x (X b) : G) := by
        rw [hx_s, hx_X]
    _ = (S.s c : G) * (X c : G) := by
        rw [hgammaRaw]
        calc (S.s c : G) * ((X c : G) * (conjA x (X b) : G)) * (conjA x (X b) : G)
            = (S.s c : G) * (X c : G) *
                ((conjA x (X b) : G) * (conjA x (X b) : G)) := by group
          _ = (S.s c : G) * (X c : G) := by rw [hD, mul_one]

private noncomputable def W1 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : Subgroup G :=
  (sec' h h2 h3 hW S X).range.map W.subtype

private noncomputable def W2 (W₁ : Subgroup G) (z : G) : Subgroup G :=
  W₁.map (MulAut.conj z)

private theorem mem_W1 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) {g : G} :
    g ∈ W1 h h2 h3 hW S X ↔ ∃ a : A, ((sec' h h2 h3 hW S X a : W) : G) = g := by
  rw [W1, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [MonoidHom.mem_range] at hw
    obtain ⟨a, rfl⟩ := hw
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨sec' h h2 h3 hW S X a, ⟨a, rfl⟩, rfl⟩

private theorem mem_W2 {W₁ : Subgroup G} {z g : G} :
    g ∈ W2 W₁ z ↔ ∃ w ∈ W₁, z * w * z⁻¹ = g := by
  rw [W2, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    exact ⟨w, hw, by simpa [MulAut.conj_apply] using hwz⟩
  · rintro ⟨w, hw, hwz⟩
    exact ⟨w, hw, by simpa [MulAut.conj_apply] using hwz⟩

private theorem W1_le_W (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : W1 h h2 h3 hW S X ≤ W := by
  rintro g ⟨w, hw, rfl⟩
  exact w.2

private theorem card_W1 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : Nat.card (W1 h h2 h3 hW S X) = 2 ^ 10 := by
  have hinj : Function.Injective (sec' h h2 h3 hW S X) := sec'_injective h h2 h3 hW S X
  have hrange : Nat.card (sec' h h2 h3 hW S X).range = Nat.card A := by
    change Nat.card (Set.range (sec' h h2 h3 hW S X)) = Nat.card A
    exact (Nat.card_congr (Equiv.ofInjective (sec' h h2 h3 hW S X) hinj)).symm
  rw [W1, Subgroup.card_map_of_injective W.subtype_injective, hrange, h.jc.module.card]

private theorem W1_inf_A (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : W1 h h2 h3 hW S X ⊓ A = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro g ⟨hgW1, hgA⟩
  obtain ⟨a, ha⟩ := (mem_W1 h h2 h3 hW S X).mp hgW1
  have hgW : g ∈ W := W1_le_W h h2 h3 hW S X hgW1
  have hdelta_g : delta z g = 1 := by
    have hgB : g ∈ B A z := (show A ≤ B A z from le_sup_left) hgA
    exact (h.delta_eq_one_iff h2 (h3.le_R₀ hgW)).mpr hgB
  have ha1 : a = 1 := by
    have hdelta : delta z g = (a : G) := by
      have h := congrArg Subtype.val (deltaRestrict_sec' h h2 h3 hW S X a)
      rw [E3Facts.coe_deltaRestrict] at h
      rwa [ha] at h
    rw [hdelta_g] at hdelta
    exact Subtype.ext hdelta.symm
  have hg1 : g = 1 := by
    rw [← ha, ha1]
    exact congrArg Subtype.val (map_one (sec' h h2 h3 hW S X))
  rwa [hg1, Subgroup.mem_bot]

private theorem z_normalizes_W (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) : z ∈ Subgroup.normalizer (W : Set G) := by
  have hzB : z ∈ B A z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  exact h3.M_le ((Subgroup.le_normalizer (H := B A z)) hzB)

private theorem W2_le_W (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : W2 (W1 h h2 h3 hW S X) z ≤ W := by
  rintro g ⟨w, hw, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (z_normalizes_W h h2 h3) w).mp
    (W1_le_W h h2 h3 hW S X hw)

private theorem card_W2 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : Nat.card (W2 (W1 h h2 h3 hW S X) z) = 2 ^ 10 := by
  rw [W2, Subgroup.card_map_of_injective (MulAut.conj z).injective]
  exact card_W1 h h2 h3 hW S X

private theorem N_normalizes_W1 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) (hX : ∀ g a, gamma h h2 h3 hW S g a =
      X a * (g : MulAut A) (X ((g : MulAut A)⁻¹ a)))
    (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) :
    (x : G) ∈ Subgroup.normalizer (W1 h h2 h3 hW S X : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro g ⟨w, hw, rfl⟩
    obtain ⟨a, ha⟩ := (mem_W1 h h2 h3 hW S X).mp hw
    change (x : G) * w * (x : G)⁻¹ ∈ W1 h h2 h3 hW S X
    rw [← ha, sec'_conj h h2 h3 hW S X hX x a]
    exact (mem_W1 h h2 h3 hW S X).mpr ⟨conjN L A x a, rfl⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective]

private theorem N_normalizes_W2 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) (hX : ∀ g a, gamma h h2 h3 hW S g a =
      X a * (g : MulAut A) (X ((g : MulAut A)⁻¹ a)))
    (x : ↥(L ⊓ Subgroup.normalizer (A : Set G))) :
    (x : G) ∈ Subgroup.normalizer (W2 (W1 h h2 h3 hW S X) z : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro g ⟨w, hw, rfl⟩
    obtain ⟨u, hu, huw⟩ := (mem_W2).mp hw
    refine (mem_W2).mpr ⟨(x : G) * u * (x : G)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (N_normalizes_W1 h h2 h3 hW S X hX x) u).mp hu
    · change z * ((x : G) * u * (x : G)⁻¹) * z⁻¹ = (x : G) * w * (x : G)⁻¹
      have hxz : (x : G) * z = z * (x : G) := h.commute_of_mem x.2.1
      have hxzi : (x : G)⁻¹ * z⁻¹ = z⁻¹ * (x : G)⁻¹ := by
        calc (x : G)⁻¹ * z⁻¹ = (z * (x : G))⁻¹ := by rw [mul_inv_rev]
          _ = ((x : G) * z)⁻¹ := by rw [← hxz]
          _ = z⁻¹ * (x : G)⁻¹ := by rw [mul_inv_rev]
      rw [← huw]
      calc z * ((x : G) * u * (x : G)⁻¹) * z⁻¹
          = (z * (x : G)) * u * ((x : G)⁻¹ * z⁻¹) := by group
        _ = ((x : G) * z) * u * ((x : G)⁻¹ * z⁻¹) := by rw [← hxz]
        _ = ((x : G) * z) * u * (z⁻¹ * (x : G)⁻¹) := by rw [hxzi]
        _ = (x : G) * (z * u * z⁻¹) * (x : G)⁻¹ := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective]

private theorem W1_ne_W2 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) : W1 h h2 h3 hW S X ≠ W2 (W1 h h2 h3 hW S X) z := by
  intro hEq
  have hmap : (W1 h h2 h3 hW S X).map (MulAut.conj z) = W1 h h2 h3 hW S X := by
    change W2 (W1 h h2 h3 hW S X) z = W1 h h2 h3 hW S X
    rw [← hEq]
  have hz_norm : z ∈ Subgroup.normalizer (W1 h h2 h3 hW S X : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hbot : W1 h h2 h3 hW S X = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro w hw
    have hwW : w ∈ W := W1_le_W h h2 h3 hW S X hw
    have hconj : z * w * z⁻¹ ∈ W1 h h2 h3 hW S X :=
      (Subgroup.mem_normalizer_iff.mp hz_norm w).mp hw
    have hzw : z * w * z⁻¹ = delta z w * w := by
      have h2' : w * z = z * delta z w * w := by
        calc w * z = (w * z * w⁻¹) * w := by group
          _ = (z * delta z w) * w := by rw [← mul_delta z w]
          _ = z * delta z w * w := by group
      have hzw' : z * w * z = delta z w * w := by
        calc z * w * z = z * (w * z) := by group
          _ = z * (z * delta z w * w) := by rw [h2']
          _ = (z * z) * delta z w * w := by group
          _ = delta z w * w := by rw [h.set.z_sq, one_mul]
      rw [h.z_inv]
      exact hzw'
    have hdelta_mem : delta z w ∈ W1 h h2 h3 hW S X := by
      have h1 : delta z w * w ∈ W1 h h2 h3 hW S X := by
        simpa [hzw] using hconj
      have h2' := (W1 h h2 h3 hW S X).mul_mem h1 ((W1 h h2 h3 hW S X).inv_mem hw)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h2'
    have hdelta_one : delta z w = 1 := by
      have hmemA : delta z w ∈ A := h2.delta_mem (h3.le_R₀ hwW)
      have hinf : delta z w ∈ W1 h h2 h3 hW S X ⊓ A := ⟨hdelta_mem, hmemA⟩
      rwa [W1_inf_A h h2 h3 hW S X] at hinf
    have hwB : w ∈ B A z := (h.delta_eq_one_iff h2 (h3.le_R₀ hwW)).mp hdelta_one
    have hwA : w ∈ A := (W_inf_B h h3).le ⟨hwW, hwB⟩
    have hwbot : w ∈ W1 h h2 h3 hW S X ⊓ A := ⟨hw, hwA⟩
    rwa [W1_inf_A h h2 h3 hW S X] at hwbot
  have hcard : Nat.card (W1 h h2 h3 hW S X) = 1 := by rw [hbot, Subgroup.card_bot]
  rw [card_W1 h h2 h3 hW S X] at hcard
  norm_num at hcard

private noncomputable def Uint (h2 : E2Facts L A z) (h3 : E3Facts A z W)
    (I : Subgroup G) : Subgroup A :=
  (I.subgroupOf W).map (E3Facts.deltaRestrict h2 h3)

private theorem mem_Uint (h2 : E2Facts L A z) (h3 : E3Facts A z W) (I : Subgroup G)
    {u : A} :
    u ∈ Uint (W := W) h2 h3 I ↔
      ∃ i : W, i ∈ I.subgroupOf W ∧ E3Facts.deltaRestrict h2 h3 i = u := by
  rw [Uint, Subgroup.mem_map]

private theorem Uint_invariant (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) (hX : ∀ g a, gamma h h2 h3 hW S g a =
      X a * (g : MulAut A) (X ((g : MulAut A)⁻¹ a))) :
    ∀ g ∈ ⁅autImage L A, autImage L A⁆,
      ∀ u ∈ Uint (W := W) h2 h3 (W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z),
        g u ∈ Uint (W := W) h2 h3
          (W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z) := by
  intro g hg u hu
  obtain ⟨i, hi, rfl⟩ := (mem_Uint h2 h3 _).mp hu
  have hgQ : g ∈ autImage L A := by
    have h := (Subgroup.commutator_le_sup (autImage L A) (autImage L A)) hg
    rwa [sup_idem] at h
  obtain ⟨x, hx⟩ := exists_toAutImage_eq ⟨g, hgQ⟩
  have hgx : ((toAutImage x : ↥(autImage L A)) : MulAut A) = g := by rw [hx]
  rw [← hgx]
  have hiI : ((i : W) : G) ∈ W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z :=
    Subgroup.mem_subgroupOf.mp hi
  have hxiI : (x : G) * (i : G) * (x : G)⁻¹ ∈
      W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z :=
    ⟨(Subgroup.mem_normalizer_iff.mp (N_normalizes_W1 h h2 h3 hW S X hX x) (i : G)).mp
        hiI.1,
      (Subgroup.mem_normalizer_iff.mp (N_normalizes_W2 h h2 h3 hW S X hX x) (i : G)).mp
        hiI.2⟩
  have hxiW : (x : G) * (i : G) * (x : G)⁻¹ ∈ W :=
    W1_le_W h h2 h3 hW S X hxiI.1
  refine (mem_Uint h2 h3 _).mpr
    ⟨⟨(x : G) * (i : G) * (x : G)⁻¹, hxiW⟩, Subgroup.mem_subgroupOf.mpr hxiI, ?_⟩
  apply Subtype.ext
  have hdi : delta z (i : G) = ((E3Facts.deltaRestrict h2 h3 i : A) : G) :=
    (E3Facts.coe_deltaRestrict h2 h3 i).symm
  rw [E3Facts.coe_deltaRestrict, h.delta_conj (x := (x : G)) x.2.1, hdi]
  rw [show ((toAutImage x : ↥(autImage L A)) : MulAut A) (E3Facts.deltaRestrict h2 h3 i) =
    conjN L A x (E3Facts.deltaRestrict h2 h3 i) from rfl, conjN_apply]
  simp

private theorem W1_inf_W2 (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW)
    (X : A →* A) (hX : ∀ g a, gamma h h2 h3 hW S g a =
      X a * (g : MulAut A) (X ((g : MulAut A)⁻¹ a))) :
    W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z = ⊥ := by
  have hU := h.jc.module.irreducible_derived
    (Uint (W := W) h2 h3 (W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z))
    (Uint_invariant h h2 h3 hW S X hX)
  rcases hU with hbot | htop
  · refine le_antisymm ?_ bot_le
    intro i hi
    have hiW : i ∈ W := W1_le_W h h2 h3 hW S X
      ((show W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z ≤ W1 h h2 h3 hW S X
        from inf_le_left) hi)
    have hmem : E3Facts.deltaRestrict h2 h3 ⟨i, hiW⟩ ∈
        Uint (W := W) h2 h3 (W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z) :=
      (mem_Uint h2 h3 _).mpr ⟨⟨i, hiW⟩, Subgroup.mem_subgroupOf.mpr hi, rfl⟩
    rw [hbot] at hmem
    have hd1 : E3Facts.deltaRestrict h2 h3 ⟨i, hiW⟩ = 1 := Subgroup.mem_bot.mp hmem
    have hdG : delta z i = 1 := by
      have := congrArg Subtype.val hd1
      rwa [E3Facts.coe_deltaRestrict] at this
    have hiB : i ∈ B A z := (h.delta_eq_one_iff h2 (h3.le_R₀ hiW)).mp hdG
    have hiA : i ∈ A := (W_inf_B h h3).le ⟨hiW, hiB⟩
    have hiWA : i ∈ W1 h h2 h3 hW S X ⊓ A :=
      ⟨(show W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z ≤ W1 h h2 h3 hW S X
        from inf_le_left) hi, hiA⟩
    rwa [W1_inf_A h h2 h3 hW S X] at hiWA
  · exfalso
    have hcardU : Nat.card (Uint (W := W) h2 h3
        (W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z)) = 2 ^ 10 := by
      rw [htop, Subgroup.card_top, h.jc.module.card]
    have hdvd := Subgroup.card_map_dvd (E3Facts.deltaRestrict h2 h3)
      (H := (W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z).subgroupOf W)
    have hle1 : Nat.card (Uint (W := W) h2 h3
        (W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z)) ≤
        Nat.card ↥(W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z) := by
      have hpos : 0 < Nat.card
          ↥((W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z).subgroupOf W) := Nat.card_pos
      have hle := Nat.le_of_dvd hpos hdvd
      have hsub : Nat.card ↥((W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z).subgroupOf W) =
          Nat.card ↥(W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show
          W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z ≤ W from
          inf_le_left.trans (W1_le_W h h2 h3 hW S X))).toEquiv
      rwa [hsub] at hle
    have hle2 : Nat.card ↥(W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z) ≤
        Nat.card (W1 h h2 h3 hW S X) :=
      Subgroup.card_le_of_le (show _ ≤ W1 h h2 h3 hW S X from inf_le_left)
    have hIcard : Nat.card ↥(W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z) = 2 ^ 10 := by
      have ha1 := hcardU
      have ha2 := hle1
      have ha3 := hle2
      rw [card_W1 h h2 h3 hW S X] at ha3
      omega
    have hIeq1 : W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z =
        W1 h h2 h3 hW S X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hIcard, card_W1 h h2 h3 hW S X])
    have hIeq2 : W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z =
        W2 (W1 h h2 h3 hW S X) z :=
      Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [hIcard, card_W2 h h2 h3 hW S X])
    refine W1_ne_W2 h h2 h3 hW S X ?_
    calc W1 h h2 h3 hW S X = W1 h h2 h3 hW S X ⊓ W2 (W1 h h2 h3 hW S X) z :=
          hIeq1.symm
      _ = W2 (W1 h h2 h3 hW S X) z := hIeq2

private theorem exists_X (h : Hyp G L A T z t) (h2 : E2Facts L A z)
    (h3 : E3Facts A z W) (hW : IsElementaryAbelian 2 W) (S : DeltaSection h h2 h3 hW) :
    ∃ X : A →* A, ∀ g a, gamma h h2 h3 hW S g a =
      X a * (g : MulAut A) (X ((g : MulAut A)⁻¹ a)) := by
  obtain ⟨y, hyW, hydelta, hyE⟩ := exists_lift h h2 h3
  obtain ⟨u, hu⟩ := exists_fixed_lift h h2 h3 hW S hyW hydelta hyE
  exact h.jc.module.split_of_fixed (gamma h h2 h3 hW S) (gamma_mul h h2 h3 hW S)
    (gamma_cocycle h h2 h3 hW S) ⟨u, hu⟩

theorem Hyp.exists_wFacts {G : Type} [Group G] [Finite G] {L A T : Subgroup G} {z t : G}
    (h : Hyp G L A T z t) (h2 : E2Facts L A z) {W : Subgroup G} (h3 : E3Facts A z W)
    (hW : IsElementaryAbelian 2 W) : ∃ W₁ W₂ : Subgroup G, WFacts L A z W₁ W₂ ∧ W₁ ⊔ W₂ = W := by
  classical
  let S : DeltaSection h h2 h3 hW := deltaSectionAux h h2 h3 hW
  obtain ⟨X, hX⟩ := exists_X h h2 h3 hW S
  let W₁ : Subgroup G := W1 h h2 h3 hW S X
  let W₂ : Subgroup G := W2 W₁ z
  have hW1le : W₁ ≤ W := W1_le_W h h2 h3 hW S X
  have hW2le : W₂ ≤ W := W2_le_W h h2 h3 hW S X
  have hcard1 : Nat.card W₁ = 2 ^ 10 := card_W1 h h2 h3 hW S X
  have hcard2 : Nat.card W₂ = 2 ^ 10 := card_W2 h h2 h3 hW S X
  have hinf : W₁ ⊓ W₂ = ⊥ := W1_inf_W2 h h2 h3 hW S X hX
  have hinfA : W₁ ⊓ A = ⊥ := W1_inf_A h h2 h3 hW S X
  have hcomm : W₂ ≤ Subgroup.centralizer (W₁ : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact mul_comm_of_mem_W hW (hW1le hv) (hW2le hw)
  have hcardsup : Nat.card ↥(W₁ ⊔ W₂) = 2 ^ 20 := by
    rw [CFSG.GroupTheory.GL52.inv_card_sup
      (hcomm.trans (Subgroup.centralizer_le_normalizer _)) hinf, hcard1, hcard2]
    norm_num
  have hsup : W₁ ⊔ W₂ = W := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hW1le hW2le) ?_
    rw [hcardsup, h3.card]
  refine ⟨W₁, W₂, ?_, hsup⟩
  refine
    { elemAb := ?_
      A_le := ?_
      le_R₀ := ?_
      M_le := ?_
      card₁ := hcard1
      card₂ := hcard2
      inf_eq_bot := hinf
      inf_A := hinfA
      swap := ?_
      normalizes := ?_ }
  · rw [hsup]; exact hW
  · rw [hsup]; exact h3.A_le
  · exact sup_le (hW1le.trans h3.le_R₀) (hW2le.trans h3.le_R₀)
  · rw [hsup]; exact h3.M_le
  · intro w hw
    exact (mem_W2).mpr ⟨w, hw, rfl⟩
  · intro x hx w hw
    exact (Subgroup.mem_normalizer_iff.mp (N_normalizes_W1 h h2 h3 hW S X hX ⟨x, hx⟩) w).mp hw

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
