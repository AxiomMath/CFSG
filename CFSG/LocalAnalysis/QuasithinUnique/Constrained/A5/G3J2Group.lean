module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3A314Red
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3TabBlock

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv

@[expose] def NoPairTwoFive (Y : Type) [Group Y] : Prop :=
  ¬ ∃ t x : Y, orderOf t = 2 ∧ orderOf x = 5 ∧ orderOf (t * x) = 5 ∧
    orderOf (t * x * t⁻¹ * x⁻¹) = 2

theorem NoPairTwoFive.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : NoPairTwoFive Y) : NoPairTwoFive Y' := by
  rintro ⟨t, x, h2, h5, h5', h2'⟩
  apply h
  refine ⟨e.symm t, e.symm x, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, h2]
  · rw [MulEquiv.orderOf_eq, h5]
  · rw [← map_mul, MulEquiv.orderOf_eq, h5']
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, MulEquiv.orderOf_eq, h2']

theorem centralizes_of_noPair {X : Type} [Group X] (hX : NoPairTwoFive X) {V : Subgroup X}
    (hV : IsElemAbelian 2 V) {x : X} (hx : orderOf x = 5)
    (hnorm : ∀ v ∈ V, x * v * x⁻¹ ∈ V) : ∀ v ∈ V, x * v * x⁻¹ = v := by
  intro v hv
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx5 : x ^ 5 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx5' : x * x * x * x * x = 1 := by
    have := hx5
    simp only [pow_succ, pow_zero, one_mul] at this
    exact this
  have hcomm : ∀ p ∈ V, ∀ q ∈ V, p * q = q * p := fun p hp q hq =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨p, hp⟩ ⟨q, hq⟩)
  have hsq : ∀ p ∈ V, p * p = 1 := fun p hp => by
    have := hV.2 p hp
    rwa [sq] at this
  have hvv : v * v = 1 := hsq v hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  set a1 := x * v * x⁻¹ with ha1
  set a2 := x * a1 * x⁻¹ with ha2
  have ha1V : a1 ∈ V := hnorm v hv
  have ha2V : a2 ∈ V := hnorm a1 ha1V
  have hc1 : a1 * v = v * a1 := (hcomm v hv a1 ha1V).symm
  have hc2 : a2 * v = v * a2 := (hcomm v hv a2 ha2V).symm
  have ha1sq : a1 * a1 = 1 := hsq a1 ha1V
  have ha2sq : a2 * a2 = 1 := hsq a2 ha2V
  have ha2v : a2 ≠ v := by
    intro h
    apply hne
    have h4 : x * (x * (x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ = v := by
      calc x * (x * (x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹
          = (x * x * x * x * x) * v * (x * x * x * x * x)⁻¹ := by group
        _ = v := by rw [hx5']; group
    have hh : x * (x * v * x⁻¹) * x⁻¹ = v := h
    have h5 : x * (x * (x * (x * (x * v * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹ = x * v * x⁻¹ := by
      rw [hh, hh]
    exact h5.symm.trans h4
  set t := v * a1 with ht
  have ht2 : t * t = 1 := by
    calc v * a1 * (v * a1) = v * (a1 * v) * a1 := by group
      _ = v * (v * a1) * a1 := by rw [hc1]
      _ = (v * v) * (a1 * a1) := by group
      _ = 1 := by rw [hvv, ha1sq, one_mul]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ht1 : t ≠ 1 := by
    intro h
    apply hne
    have : a1 = v⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hvinv] at this
    exact this
  have hord_t : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have htx : t * x = v * x * v⁻¹ := by
    rw [hvinv]
    calc v * a1 * x = v * x * v := by rw [ha1]; group
      _ = v * x * v := rfl
  have htx5 : (t * x) ^ 5 = 1 := by
    rw [htx, conj_pow, hx5]
    simp
  have htx1 : t * x ≠ 1 := by
    intro h
    have hxt : x = t⁻¹ := eq_inv_of_mul_eq_one_right h
    have : x ^ 2 = 1 := by rw [hxt, htinv, sq, ht2]
    have := orderOf_dvd_of_pow_eq_one this
    rw [hx] at this
    omega
  have hord_tx : orderOf (t * x) = 5 := orderOf_eq_prime htx5 htx1
  have hcomm_tx : t * x * t⁻¹ * x⁻¹ = v * a2 := by
    rw [htinv]
    calc t * x * t * x⁻¹ = v * x * (v * v) * x * v * x⁻¹ * x⁻¹ := by rw [ht, ha1]; group
      _ = v * x * x * v * x⁻¹ * x⁻¹ := by rw [hvv, mul_one]
      _ = v * a2 := by rw [ha2, ha1]; group
  have hva2sq : (v * a2) * (v * a2) = 1 := by
    calc v * a2 * (v * a2) = v * (a2 * v) * a2 := by group
      _ = v * (v * a2) * a2 := by rw [hc2]
      _ = (v * v) * (a2 * a2) := by group
      _ = 1 := by rw [hvv, ha2sq, one_mul]
  have hva2 : v * a2 ≠ 1 := by
    intro h
    apply ha2v
    have : a2 = v⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hvinv] at this
    exact this
  have hord_c : orderOf (t * x * t⁻¹ * x⁻¹) = 2 := by
    rw [hcomm_tx]
    exact orderOf_eq_prime (by rw [sq]; exact hva2sq) hva2
  exact hX ⟨t, x, hord_t, hx, hord_tx, hord_c⟩

theorem fixed_vector_of_five : ∀ σ : Perm (Fin 5), σ ^ 5 = 1 → σ ≠ 1 →
    ∀ w : Fin 5 → ZMod 2, (∑ i, w i = 0) → (∀ i, w (σ⁻¹ i) = w i) → w = 0 := by
  decide +kernel

theorem false_of_isPGroup_of_orderOf_five {Z : Type*} [Group Z] (hZ : IsPGroup 2 Z) {z : Z}
    (hz : orderOf z = 5) : False := by
  obtain ⟨k, hk⟩ := hZ z
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  rw [hz] at h1
  have h2 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) h1
  omega

theorem vector_eq_zero_of_fixed {σ : Perm (Fin 5)} (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1)
    (w : evenWeight 5) (hw : ∀ i, (w : Fin 5 → ZMod 2) (σ⁻¹ i) = (w : Fin 5 → ZMod 2) i) :
    w = 0 := by
  have hsum : ∑ i, (w : Fin 5 → ZMod 2) i = 0 := (Delta5.mem_evenWeight_iff _).1 w.2
  exact Subtype.ext (fixed_vector_of_five σ h5 h1 _ hsum hw)

theorem noDelta5In_of_noPair {X : Type} [Group X] [Finite X] (hX : NoPairTwoFive X) :
    NoDelta5In X := by
  intro T hT B hB hne hTB hD
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ∣ Nat.card ↥B := by rw [hD.card]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hD' := hD
  obtain ⟨α, β, -, hαk, hβ, hact⟩ := hD'
  set V : Subgroup X := (CFSG.pCore 2 ↥B).map B.subtype with hV
  have hVe : IsElemAbelian 2 V := Lin2.isElemAbelian_map' hD.isElemAbelian_pCore B.subtype
  have hxo : orderOf (x : X) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hnorm : ∀ v ∈ V, (x : X) * v * (x : X)⁻¹ ∈ V := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨x * u * x⁻¹, (CFSG.pCore_normal (G := ↥B) (p := 2)).conj_mem u hu x, ?_⟩
    simp
  have hcent := centralizes_of_noPair hX hVe hxo hnorm
  have hxp : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hσ5 : ((α x : alternatingGroup (Fin 5)) : Perm (Fin 5)) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hxp, map_one]
    rfl
  have hσ1 : ((α x : alternatingGroup (Fin 5)) : Perm (Fin 5)) ≠ 1 := by
    intro h
    have hx1 : x ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h
    rw [hαk] at hx1
    exact false_of_isPGroup_of_orderOf_five (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
      (z := ⟨x, hx1⟩) (by rw [← Subgroup.orderOf_coe]; exact hx)
  have htriv : ∀ u : ↥(CFSG.pCore 2 ↥B), u = 1 := by
    intro u
    have hu : ((u : ↥B) : X) ∈ V := ⟨u, u.2, rfl⟩
    have hc := hcent _ hu
    have hxu : (u : ↥B) = x * u * x⁻¹ := by
      apply B.subtype_injective
      simpa using hc.symm
    have hfix := hact x u u hxu
    have hzero := vector_eq_zero_of_fixed hσ5 hσ1 (Multiplicative.toAdd (β u))
      (fun i => (hfix i).symm)
    apply hβ.1
    rw [map_one]
    apply Multiplicative.toAdd.injective
    simpa using hzero
  have hbot : CFSG.pCore 2 ↥B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have := htriv ⟨u, hu⟩
    exact congrArg Subtype.val this
  have := hD.card_pCore
  rw [hbot, Subgroup.card_bot] at this
  omega

section Block

variable {G : Type} [Group G] [Finite G] {K L : Subgroup G}

theorem false_of_alt5_block_of_noPair {X : Type} [Group X] (hX : NoPairTwoFive X)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* X) (hs : IsShort2 L) (hL : IsAltType L 5) (hLK : L ≤ K)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥K)) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set π := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  set ρ : ↥L →* ↥K ⧸ Subgroup.center ↥K := π.comp (Subgroup.inclusion hLK) with hρ
  have hkerπ : IsPGroup 2 π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hZ
  have hkerρ : ρ.ker ≤ CFSG.pCore 2 ↥L := ker_le_pCore hLK π hkerπ
  have h5 : 5 ∣ Nat.card ↥L := (show 5 ∣ 960 by norm_num).trans (nineSixty_dvd_card hs hL)
  obtain ⟨ℓ, hℓ⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hℓp : ℓ ^ 5 = 1 := by rw [← hℓ]; exact pow_orderOf_eq_one ℓ
  have hL' := hL
  obtain ⟨α, hα, hαk, β, hβ, hβk, hβe⟩ := hL'
  have hℓq : ℓ ∉ CFSG.pCore 2 ↥L := fun h =>
    false_of_isPGroup_of_orderOf_five (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      (z := ⟨ℓ, h⟩) (by rw [← Subgroup.orderOf_coe]; exact hℓ)
  have hσ5 : ((α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hℓp, map_one]
    rfl
  have hσ1 : ((α ℓ : alternatingGroup (Fin 5)) : Perm (Fin 5)) ≠ 1 := by
    intro h
    apply hℓq
    rw [← hαk, MonoidHom.mem_ker]
    exact Subtype.ext h
  set θ : ↥L →* X := e.toMonoidHom.comp ρ with hθ
  have hθk : ∀ y : ↥L, θ y = 1 → y ∈ CFSG.pCore 2 ↥L := fun y hy => by
    apply hkerρ
    rw [MonoidHom.mem_ker]
    exact e.injective (by simpa [hθ] using hy)
  have hxo : orderOf (θ ℓ) = 5 :=
    orderOf_eq_prime (by rw [← map_pow, hℓp, map_one]) (fun h => hℓq (hθk ℓ h))
  set U' : Subgroup ↥L := (blockU L).subgroupOf L with hU'
  have hU'e : IsElemAbelian 2 U' :=
    Lin2.OddRank.isElemAbelian_subgroupOf (Lin2.OddRank.isElemAbelian_blockU hs)
  have hUnorm : ∀ u ∈ U', ℓ * u * ℓ⁻¹ ∈ U' := by
    intro u hu
    rw [hU', Subgroup.mem_subgroupOf] at hu ⊢
    have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) (u : G)).mp hu
    simpa using this
  have hVe : IsElemAbelian 2 (U'.map θ) := Lin2.isElemAbelian_map' hU'e θ
  have hnorm : ∀ v ∈ U'.map θ, θ ℓ * v * (θ ℓ)⁻¹ ∈ U'.map θ := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨ℓ * u * ℓ⁻¹, hUnorm u hu, by simp⟩
  have hcent := centralizes_of_noPair hX hVe hxo hnorm
  have hβ1 : ∀ u : ↥(blockU L), β u = 1 := by
    intro u
    set uL : ↥L := ⟨(u : G), (Lin2.OddRank.blockU_le_L hs) u.2⟩ with huL
    have huU' : uL ∈ U' := by rw [hU', Subgroup.mem_subgroupOf]; exact u.2
    have hc := hcent (θ uL) ⟨uL, huU', rfl⟩
    set v : ↥(blockU L) := ⟨ℓ * (u : G) * ℓ⁻¹, by
      have := (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) (u : G)).mp u.2
      simpa using this⟩ with hv
    have hvL : (⟨(v : G), (Lin2.OddRank.blockU_le_L hs) v.2⟩ : ↥L) = ℓ * uL * ℓ⁻¹ := by
      apply Subtype.ext
      simp [hv, huL]
    have hθv : θ (⟨(v : G), (Lin2.OddRank.blockU_le_L hs) v.2⟩ : ↥L) = θ uL := by
      rw [hvL, map_mul, map_mul, map_inv]
      exact hc
    have hcK : (⟨((v * u⁻¹ : ↥(blockU L)) : G), hLK ((Lin2.OddRank.blockU_le_L hs)
        (v * u⁻¹).2)⟩ : ↥K) ∈ Subgroup.center ↥K := by
      have h1 : θ (⟨(v : G), (Lin2.OddRank.blockU_le_L hs) v.2⟩ * uL⁻¹) = 1 := by
        rw [map_mul, map_inv, hθv, mul_inv_cancel]
      have h2 := e.injective (h1.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hZmem : ((v * u⁻¹ : ↥(blockU L)) : G) ∈ blockZ L :=
      mem_blockZ_of_mem_center (v * u⁻¹).2 hLK (hLK ((Lin2.OddRank.blockU_le_L hs) (v * u⁻¹).2)) hcK
    have hker : v * u⁻¹ ∈ β.ker := by
      rw [hβk]
      exact hZmem
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hker
    have hfix := hβe ℓ u v (by simp [hv])
    have hzero := vector_eq_zero_of_fixed hσ5 hσ1 (Multiplicative.toAdd (β u))
      (fun i => by
        have := hfix i
        rw [hker] at this
        exact this.symm)
    apply Multiplicative.toAdd.injective
    simpa using hzero
  have h16 : Nat.card β.range = 16 := by
    rw [MonoidHom.range_eq_top.mpr hβ, Subgroup.card_top,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
    exact card_evenWeight_five
  have hbot : β.range = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨u, rfl⟩
    rw [hβ1 u]
    exact Subgroup.one_mem _
  rw [hbot, Subgroup.card_bot] at h16
  omega

end Block

end CFSG.QuasithinUnique.A5.G3
