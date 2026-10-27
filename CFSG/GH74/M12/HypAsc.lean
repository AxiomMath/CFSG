module

public import CFSG.GH74.M12.HypGroup
public import CFSG.GH74.M12.Statements

public section

namespace CFSG.GH74.M12.Hyp

open Subgroup CFSG

structure LocalHyp (H : Type*) [Group H] (z : H) : Prop where
  card_eq : Nat.card H = 192
  card_core : Nat.card ↥(pCore 2 H) = 32
  extraspecial : IsExtraspecial 2 ↥(pCore 2 H)
  quotient_S3 : Nonempty (H ⧸ pCore 2 H ≃* Equiv.Perm (Fin 3))
  centralizer_X : ∀ x : H, orderOf x = 3 → ∀ q ∈ pCore 2 H, x * q = q * x → q ∈ zpowers z

theorem LocalHyp.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {z : H} {z' : H'}
    (hz : e z = z') (h : LocalHyp H z) : LocalHyp H' z' := by
  have hmap : (pCore 2 H).map e.toMonoidHom = pCore 2 H' := pCore_map_iso 2 e
  have hmap' : (pCore 2 H').map e.symm.toMonoidHom = pCore 2 H := pCore_map_iso 2 e.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr e.toEquiv]; exact h.card_eq
  · rw [← hmap, Subgroup.card_map_of_injective e.injective]; exact h.card_core
  · exact isExtraspecial_of_mulEquiv ((e.subgroupMap (pCore 2 H)).trans
      (MulEquiv.subgroupCongr hmap)) h.extraspecial
  · obtain ⟨f⟩ := h.quotient_S3
    exact ⟨(QuotientGroup.congr (pCore 2 H') (pCore 2 H) e.symm hmap').trans f⟩
  · intro x' hx' q' hq' hcomm
    have hq'mem : q' ∈ (pCore 2 H).map e.toMonoidHom := by rw [hmap]; exact hq'
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hq'mem
    have hx : orderOf (e.symm x') = 3 := by rw [MulEquiv.orderOf_eq]; exact hx'
    have hc : e.symm x' * q = q * e.symm x' := by
      apply e.injective
      simpa using hcomm
    have := h.centralizer_X (e.symm x') hx q hq hc
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [← hz, ← map_zpow, hn]
    rfl

@[expose] def zElt' {G : Type*} [Group G] (z : G) : ↥(centralizer ({z} : Set G)) :=
  ⟨z, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem asc03Hyp_of_local {G : Type*} [Group G] [Finite G] (z : G) (hz : orderOf z = 2)
    (hloc : LocalHyp ↥(centralizer ({z} : Set G)) (zElt' z))
    (hwc : ∃ g : G, g * z * g⁻¹ ≠ z ∧
      ∃ q ∈ pCore 2 ↥(centralizer ({z} : Set G)), (q : G) = g * z * g⁻¹) :
    Asc03Hyp G z where
  orderTwo := hz
  card_core := hloc.card_core
  extraspecial := hloc.extraspecial
  quotient_S3 := hloc.quotient_S3
  centralizer_X := by
    intro X q hq hcomm
    have h3 : Nat.card (X : Subgroup ↥(centralizer ({z} : Set G))) = 3 := by
      have h : Nat.card (X : Subgroup ↥(centralizer ({z} : Set G))) =
          3 ^ Nat.factorization (Nat.card ↥(centralizer ({z} : Set G))) 3 :=
        Sylow.card_eq_multiplicity X
      rw [hloc.card_eq] at h
      have h192 : Nat.factorization 192 3 = 1 := by
        rw [Nat.factorization_def _ Nat.prime_three]
        have h : (192 : ℕ) = 3 * 2 ^ 6 := by norm_num
        rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
          padicValNat.eq_zero_of_not_dvd (by norm_num)]
      rw [h192] at h
      simpa using h
    have hXne : (X : Subgroup ↥(centralizer ({z} : Set G))) ≠ ⊥ := by
      intro h
      rw [h] at h3
      simp at h3
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hXne
    have hxo : orderOf (x : ↥(centralizer ({z} : Set G))) = 3 := by
      rw [Subgroup.orderOf_coe]
      have hdvd : orderOf x ∣ 3 := by
        have := orderOf_dvd_natCard x
        rwa [h3] at this
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hx1
      · exact h
    have := hloc.centralizer_X (x : ↥(centralizer ({z} : Set G))) hxo q hq (hcomm x x.2)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hn]; rfl⟩
  not_weakly_closed := hwc

theorem q8_normal_of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : ∀ K ∈ q8Subgroups (pCore 2 H), K.Normal) :
    ∀ K' ∈ q8Subgroups (pCore 2 H'), K'.Normal := by
  intro K' hK'
  obtain ⟨hle, ⟨iso⟩⟩ := hK'
  have hmap' : (pCore 2 H').map e.symm.toMonoidHom = pCore 2 H := pCore_map_iso 2 e.symm
  have hK : K'.map e.symm.toMonoidHom ∈ q8Subgroups (pCore 2 H) := by
    refine ⟨?_, ⟨(e.symm.subgroupMap K').symm.trans iso⟩⟩
    rw [← hmap']
    exact Subgroup.map_mono hle
  have hnorm := h _ hK
  have hback : (K'.map e.symm.toMonoidHom).map e.toMonoidHom = K' := by
    rw [Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H' :=
      MonoidHom.ext fun x => e.apply_symm_apply x
    rw [this, Subgroup.map_id]
  rw [← hback]
  exact hnorm.map _ e.surjective

theorem exists_q8_normal_of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : ∃ K ∈ q8Subgroups (pCore 2 H), K.Normal) :
    ∃ K' ∈ q8Subgroups (pCore 2 H'), K'.Normal := by
  obtain ⟨K, ⟨hle, ⟨iso⟩⟩, hnorm⟩ := h
  refine ⟨K.map e.toMonoidHom, ⟨?_, ⟨(e.subgroupMap K).symm.trans iso⟩⟩,
    hnorm.map _ e.surjective⟩
  rw [← pCore_map_iso 2 e]
  exact Subgroup.map_mono hle

@[expose] def conjCentralizerEquiv {G : Type*} [Group G] (g z : G) :
    ↥(centralizer ({z} : Set G)) ≃* ↥(centralizer ({g * z * g⁻¹} : Set G)) where
  toFun x := ⟨g * x.1 * g⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 x.2
    calc g * x.1 * g⁻¹ * (g * z * g⁻¹) = g * (x.1 * z) * g⁻¹ := by group
      _ = g * (z * x.1) * g⁻¹ := by rw [this]
      _ = g * z * g⁻¹ * (g * x.1 * g⁻¹) := by group⟩
  invFun y := ⟨g⁻¹ * y.1 * g, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 y.2
    calc g⁻¹ * y.1 * g * z = g⁻¹ * (y.1 * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * y.1) * g := by rw [this]
      _ = z * (g⁻¹ * y.1 * g) := by group⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjCentralizerEquiv_apply {G : Type*} [Group G] (g z : G)
    (x : ↥(centralizer ({z} : Set G))) :
    ((conjCentralizerEquiv g z x : ↥(centralizer ({g * z * g⁻¹} : Set G))) : G) = g * x.1 * g⁻¹ :=
  rfl

theorem conjCentralizerEquiv_zElt {G : Type*} [Group G] (g z : G) :
    conjCentralizerEquiv g z (zElt' z) = zElt' (g * z * g⁻¹) :=
  rfl

end CFSG.GH74.M12.Hyp
