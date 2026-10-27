module

public import CFSG.LocalAnalysis.EvenBN.Tits.Model.HypStarCert
public import CFSG.LocalAnalysis.EvenBN.Tits.Model.ParrottCert
public import Certificates.Certificate27014

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

namespace Model

open Certificates.TitsAschbacherSecFour CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem exists_comm_eq_titsZ
    : ∃ a ∈ titsD, ∃ b ∈ titsD, a * titsZ = titsZ * a ∧ b * titsZ = titsZ * b ∧
      ⁅a, b⁆ = titsZ := by
  obtain ⟨-, -, x, hx, y, hy, hxy⟩ := comm_hatE
  have hxJ : x ∈ titsJ := hatE_le_titsJ hx
  have hH : titsH ≤ centralizer {titsZ} := by
    rw [← titsD_centralizer_z]
    exact inf_le_right
  refine ⟨x, titsJ_le_titsD hxJ, y, titsJ_le_titsD hy, ?_, ?_, ?_⟩
  · exact mem_centralizer_singleton_iff.1 (hH (titsJ_le_titsH hxJ))
  · exact mem_centralizer_singleton_iff.1 (hH (titsJ_le_titsH hy))
  · rw [commutatorElement_def]
    exact hxy

theorem rep_nArr {w : List ℕ} (hw : nLetters w = true) :
    Rep 1755 (nArr w) (w.map (chainGen titsNArrs)).prod :=
  rep_prodArr fun i hi => chainGen_N_rep (by
    have := List.all_eq_true.1 hw i hi
    simpa using this)

theorem nArr_mem {w : List ℕ}
    (hw : nLetters w = true) : (w.map (chainGen titsNArrs)).prod ∈ titsN :=
  list_prod_map_mem fun i hi => chainGen_N_mem (by
    have := List.all_eq_true.1 hw i hi
    simpa using this)

theorem exists_comm_eq_titsTInv :
    ∃ a ∈ titsD, ∃ b ∈ titsD, a * titsTInv = titsTInv * a ∧ b * titsTInv = titsTInv * b ∧
      ⁅a, b⁆ = titsTInv := by
  have h := Certificates.certificate27014
  unfold tCommCheck at h
  repeat rw [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, ha⟩, hb⟩, hab⟩ := h
  have rA := rep_nArr hA
  have rB := rep_nArr hB
  refine ⟨_, titsN_le_titsD (nArr_mem hA), _, titsN_le_titsD (nArr_mem hB),
    (commA_iff rA titsTInv_rep).1 ha, (commA_iff rB titsTInv_rep).1 hb, ?_⟩
  have e := eq_of_eqA (rep_compA rA rB) (rep_compA (rep_compA titsTInv_rep rB) rA) hab
  rw [commutatorElement_def, e]
  group

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

open Classical in
@[expose] noncomputable def lift (d : Data G) (a : Equiv.Perm (Fin 1755)) : G :=
  if h : a ∈ titsD then (d.θ.symm ⟨a, h⟩ : d.L) else 1

omit [Finite G] in
theorem lift_eq (d : Data G) {a : Equiv.Perm (Fin 1755)} (ha : a ∈ titsD) :
    d.lift a = (d.θ.symm ⟨a, ha⟩ : d.L) := dite_eq_left ha

omit [Finite G] in
theorem lift_mem (d : Data G) (a : Equiv.Perm (Fin 1755)) : d.lift a ∈ d.L := by
  unfold lift
  split_ifs with h
  · exact (d.θ.symm ⟨a, h⟩).2
  · exact one_mem _

@[expose] noncomputable def z (d : Data G) : G := d.lift titsZ

@[expose] noncomputable def v (d : Data G) : G := d.lift titsTInv

omit [Finite G] in
theorem z_eq_theta_symm (d : Data G) :
    d.z = (d.θ.symm ⟨titsZ, titsZ_mem_titsD⟩ : d.L) :=
  d.lift_eq titsZ_mem_titsD

omit [Finite G] in
theorem v_eq_theta_symm (d : Data G) :
    d.v = (d.θ.symm ⟨titsTInv, titsTInv_mem_titsD⟩ : d.L) :=
  d.lift_eq titsTInv_mem_titsD

omit [Finite G] in
theorem z_mem (d : Data G) : d.z ∈ d.L := d.lift_mem titsZ

omit [Finite G] in
theorem v_mem (d : Data G) : d.v ∈ d.L := d.lift_mem titsTInv

omit [Finite G] in
theorem θ_z (d : Data G) :
    ((d.θ ⟨d.z, d.z_mem⟩ : titsD) : Equiv.Perm (Fin 1755)) = titsZ := by
  simp [z, lift, titsZ_mem_titsD]

omit [Finite G] in
theorem θ_v (d : Data G) :
    ((d.θ ⟨d.v, d.v_mem⟩ : titsD) : Equiv.Perm (Fin 1755)) = titsTInv := by
  simp [v, lift, titsTInv_mem_titsD]

omit [Finite G] in
theorem θ_val_injective (d : Data G) {l m : d.L}
    (h : ((d.θ l : titsD) : Equiv.Perm (Fin 1755)) = (d.θ m : titsD)) : l = m :=
  d.θ.injective (Subtype.ext h)

theorem Hyp.card_centralizer_eq_mul
    (hd : d.Hyp) :
    Nat.card (centralizer ({d.t} : Set G)) = 2 * Nat.card d.L ∨
      Nat.card (centralizer ({d.t} : Set G)) = 4 * Nat.card d.L := by
  have hL : Nat.card d.L = Nat.card titsD := Nat.card_congr d.θ.toEquiv
  have hD : Nat.card (titsD.subgroupOf titsA) = Nat.card titsD :=
    Nat.card_congr (subgroupOfEquivOfLe titsD_le_titsA).toEquiv
  rw [hd.card_centralizer_eq_two_mul Model.hypothesisOneStar_titsD, hL]
  rcases hd.range_ρ with h | h
  · left
    rw [h, hD]
  · right
    rw [h, card_top, ← index_mul_card (titsD.subgroupOf titsA), titsD_index, hD]
    ring

theorem Hyp.card_quotient
    (hd : d.Hyp) :
    Nat.card (centralizer ({d.t} : Set G) ⧸ d.L.subgroupOf (centralizer ({d.t} : Set G))) = 2 ∨
      Nat.card (centralizer ({d.t} : Set G) ⧸ d.L.subgroupOf (centralizer ({d.t} : Set G))) =
        4 := by
  have hcard := card_eq_card_quotient_mul_card_subgroup
    (d.L.subgroupOf (centralizer ({d.t} : Set G)))
  rw [Nat.card_congr (subgroupOfEquivOfLe hd.L_le).toEquiv] at hcard
  have hpos : 0 < Nat.card d.L := Nat.card_pos
  rcases hd.card_centralizer_eq_mul with h | h
  · left
    rw [h] at hcard
    exact (Nat.eq_of_mul_eq_mul_right hpos hcard).symm
  · right
    rw [h] at hcard
    exact (Nat.eq_of_mul_eq_mul_right hpos hcard).symm

theorem Hyp.commutator_mem
    (hd : d.Hyp) {x y : G} (hx : x ∈ centralizer ({d.t} : Set G))
    (hy : y ∈ centralizer ({d.t} : Set G)) : ⁅x, y⁆ ∈ d.L := by
  have : (d.L.subgroupOf (centralizer ({d.t} : Set G))).Normal := hd.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ a b : centralizer ({d.t} : Set G) ⧸ d.L.subgroupOf (centralizer ({d.t} : Set G)),
      a * b = b * a := by
    rcases hd.card_quotient with h | h
    · have := isCyclic_of_prime_card h
      exact (inferInstance : IsMulCommutative _).is_comm.comm
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2)
        (by rw [h]; norm_num)).is_comm.comm
  have h := hcomm (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at h
  have hc : (x * y)⁻¹ * (y * x) ∈ d.L := by simpa using h
  have hm := hd.conj_mem ⟨x * y, mul_mem hx hy⟩ (inv_mem hc)
  have e : (x * y) * ((x * y)⁻¹ * (y * x))⁻¹ * (x * y)⁻¹ = ⁅x, y⁆ := by
    rw [commutatorElement_def]
    group
  rw [← e]
  exact hm

omit [Finite G] in
theorem involution_L_conj
    (d : Data G) {a : G} (ha : a ∈ d.L) (ha2 : orderOf a = 2) :
    ∃ m ∈ d.L, a = m * d.z * m⁻¹ ∨ a = m * d.v * m⁻¹ := by
  have h2 : orderOf ((d.θ ⟨a, ha⟩ : titsD) : Equiv.Perm (Fin 1755)) = 2 := by
    rw [orderOf_submonoid, MulEquiv.orderOf_eq, orderOf_mk, ha2]
  obtain ⟨-, e, he, hz | hv⟩ := Model.titsA_involution_conj (titsD_le_titsA (d.θ ⟨a, ha⟩).2) h2
  · refine ⟨d.θ.symm ⟨e, he⟩, (d.θ.symm ⟨e, he⟩).2, Or.inl ?_⟩
    have := d.θ_val_injective (l := ⟨a, ha⟩)
      (m := d.θ.symm ⟨e, he⟩ * ⟨d.z, d.z_mem⟩ * (d.θ.symm ⟨e, he⟩)⁻¹) (by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        simp only [coe_mul, coe_inv]
        rw [d.θ_z, hz])
    exact congrArg Subtype.val this
  · refine ⟨d.θ.symm ⟨e, he⟩, (d.θ.symm ⟨e, he⟩).2, Or.inr ?_⟩
    have := d.θ_val_injective (l := ⟨a, ha⟩)
      (m := d.θ.symm ⟨e, he⟩ * ⟨d.v, d.v_mem⟩ * (d.θ.symm ⟨e, he⟩)⁻¹) (by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        simp only [coe_mul, coe_inv]
        rw [d.θ_v, hv])
    exact congrArg Subtype.val this

omit [Finite G] in
theorem exists_comm_eq_of_z_or_v
    (d : Data G) {x : G} (hx : x = d.z ∨ x = d.v) :
    ∃ p ∈ d.L, ∃ q ∈ d.L, p * x = x * p ∧ q * x = x * q ∧ ⁅p, q⁆ = x := by
  have key : ∀ (xh : Equiv.Perm (Fin 1755)) (hxh : xh ∈ titsD),
      (∃ a ∈ titsD, ∃ b ∈ titsD, a * xh = xh * a ∧ b * xh = xh * b ∧ ⁅a, b⁆ = xh) →
      ∃ p ∈ d.L, ∃ q ∈ d.L, p * (d.θ.symm ⟨xh, hxh⟩ : G) = (d.θ.symm ⟨xh, hxh⟩ : G) * p ∧
        q * (d.θ.symm ⟨xh, hxh⟩ : G) = (d.θ.symm ⟨xh, hxh⟩ : G) * q ∧
        ⁅p, q⁆ = (d.θ.symm ⟨xh, hxh⟩ : G) := by
    rintro xh hxh ⟨a, ha, b, hb, hax, hbx, hab⟩
    have hθ : ∀ (u w : titsD), (u : Equiv.Perm (Fin 1755)) * w = w * u →
        ((d.θ.symm u : d.L) : G) * (d.θ.symm w : d.L) = (d.θ.symm w : d.L) * (d.θ.symm u) := by
      intro u w huw
      rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, show u * w = w * u from Subtype.ext huw]
    refine ⟨d.θ.symm ⟨a, ha⟩, (d.θ.symm ⟨a, ha⟩).2, d.θ.symm ⟨b, hb⟩, (d.θ.symm ⟨b, hb⟩).2,
      hθ ⟨a, ha⟩ ⟨xh, hxh⟩ hax, hθ ⟨b, hb⟩ ⟨xh, hxh⟩ hbx, ?_⟩
    have e : (⁅(⟨a, ha⟩ : titsD), ⟨b, hb⟩⁆ : titsD) = ⟨xh, hxh⟩ := Subtype.ext (by
      simpa [commutatorElement_def] using hab)
    rw [← e, map_commutatorElement]
    simp [commutatorElement_def]
  rcases hx with rfl | rfl
  · rw [d.z_eq_theta_symm]
    exact key titsZ titsZ_mem_titsD Model.exists_comm_eq_titsZ
  · rw [d.v_eq_theta_symm]
    exact key titsTInv titsTInv_mem_titsD Model.exists_comm_eq_titsTInv

theorem Hyp.conj_t_not_mem
    (hd : d.Hyp) (g : G) : g * d.t * g⁻¹ ∉ d.L := by
  intro ha
  have ha2 : orderOf (g * d.t * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hd.t_two]
  obtain ⟨m, hm, hx⟩ := involution_L_conj d ha ha2
  obtain ⟨x, hxzv, hax⟩ : ∃ x, (x = d.z ∨ x = d.v) ∧ g * d.t * g⁻¹ = m * x * m⁻¹ := by
    rcases hx with h | h
    · exact ⟨d.z, Or.inl rfl, h⟩
    · exact ⟨d.v, Or.inr rfl, h⟩
  obtain ⟨p, hp, q, hq, hpx, hqx, hpq⟩ := exists_comm_eq_of_z_or_v d hxzv
  set k := m⁻¹ * g with hk
  have hkt : k * d.t * k⁻¹ = x := by
    rw [hk, mul_inv_rev, inv_inv]
    calc m⁻¹ * g * d.t * (g⁻¹ * m) = m⁻¹ * (g * d.t * g⁻¹) * m := by group
      _ = x := by rw [hax]; group
  have hc : ∀ r : G, r * x = x * r → k⁻¹ * r * k ∈ centralizer ({d.t} : Set G) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    have : r * (k * d.t * k⁻¹) = (k * d.t * k⁻¹) * r := by rw [hkt]; exact hr
    calc k⁻¹ * r * k * d.t = k⁻¹ * (r * (k * d.t * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * d.t * k⁻¹) * r) * k := by rw [this]
      _ = d.t * (k⁻¹ * r * k) := by group
  have ht := hd.commutator_mem (hc p hpx) (hc q hqx)
  have e : ⁅k⁻¹ * p * k, k⁻¹ * q * k⁆ = d.t := by
    rw [commutatorElement_def]
    have : k⁻¹ * ⁅p, q⁆ * k = d.t := by
      rw [hpq, ← hkt]
      group
    rw [← this, commutatorElement_def]
    group
  rw [e] at ht
  exact hd.t_not_mem ht

theorem Hyp.conj_t_cases
    (hd : d.Hyp) {g : G} (hg : g * d.t * g⁻¹ ∈ centralizer ({d.t} : Set G)) :
    g * d.t * g⁻¹ = d.t ∨ ∃ m ∈ d.L,
      g * d.t * g⁻¹ = m * (d.t * d.z) * m⁻¹ ∨ g * d.t * g⁻¹ = m * (d.t * d.v) * m⁻¹ := by
  set s := g * d.t * g⁻¹ with hs
  have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  have hs2 : s ^ 2 = 1 := by
    rw [hs, sq]
    calc g * d.t * g⁻¹ * (g * d.t * g⁻¹) = g * (d.t * d.t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hst : s * d.t = d.t * s := mem_centralizer_singleton_iff.1 hg
  rcases hd.involution_mem hg hs2 with hsL | hts
  · exact absurd hsL (hd.conj_t_not_mem g)
  · obtain ⟨a, ha⟩ : ∃ a, a = d.t * s := ⟨_, rfl⟩
    rw [← ha] at hts
    have ha2 : a * a = 1 := by
      calc a * a = d.t * (s * d.t) * s := by rw [ha]; group
        _ = d.t * d.t * (s * s) := by rw [hst]; group
        _ = 1 := by rw [ht2, ← sq, hs2, one_mul]
    have hsa : s = d.t * a := by rw [ha, ← mul_assoc, ht2, one_mul]
    by_cases ha1 : a = 1
    · left
      rw [hsa, ha1, mul_one]
    · right
      obtain ⟨m, hm, hx⟩ := involution_L_conj d hts (orderOf_eq_prime (by rw [sq]; exact ha2) ha1)
      have htm : d.t * m = m * d.t := (mem_centralizer_iff.1 hd.t_mem m hm).symm
      refine ⟨m, hm, ?_⟩
      have key : ∀ x : G, a = m * x * m⁻¹ → s = m * (d.t * x) * m⁻¹ := by
        intro x hx
        rw [hsa, hx]
        calc d.t * (m * x * m⁻¹) = (d.t * m) * x * m⁻¹ := by group
          _ = m * (d.t * x) * m⁻¹ := by rw [htm]; group
      rcases hx with hx | hx
      · exact Or.inl (key _ hx)
      · exact Or.inr (key _ hx)

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
