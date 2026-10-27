module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_8

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type*} [Group G] [Finite G] {x z : G} {S T P Q Rd F U : Subgroup G}

omit [Finite G] in
theorem comm_zpowers {U : Subgroup G} {x : G} (hc : ∀ u ∈ U, x * u = u * x) :
    ∀ a ∈ U, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  exact (Commute.zpow_right (show Commute a x from (hc a ha).symm) k).eq

omit [Finite G] in
theorem card_sup_zpowers_four {U : Subgroup G} (hU : IsFour U) {x : G} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hxU : x ∉ U) (hc : ∀ u ∈ U, x * u = u * x) :
    Nat.card (U ⊔ Subgroup.zpowers x : Subgroup G) = 8 := by
  have hd : U ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcU, hcx⟩
    rcases zpowers_sq_cases hx2 hcx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hcU hxU
  rw [card_sup_of_commute (comm_zpowers hc) hd, hU.2, card_zpowers_of_sq hx2 hx1]

omit [Finite G] in
theorem isElemAb2_sup_zpowers {U : Subgroup G} (hU : IsFour U) {x : G} (hx2 : x * x = 1)
    (hc : ∀ u ∈ U, x * u = u * x) : IsElemAb2 (U ⊔ Subgroup.zpowers x) :=
  hU.1.sup (isElemAb2_zpowers hx2) (comm_zpowers hc)

omit [Finite G] in
theorem normalIn_sup_zpowers {U T : Subgroup G} {x : G} (hxT : x ∈ T)
    (hxc : ∀ t ∈ T, x * t = t * x) (hUT : U ≤ T) (hUn : ∀ t ∈ T, ∀ u ∈ U, t * u * t⁻¹ ∈ U) :
    NormalIn (U ⊔ Subgroup.zpowers x) T := by
  refine ⟨sup_le hUT ((Subgroup.zpowers_le).2 hxT), fun t ht e he => ?_⟩
  have hle : U ⊔ Subgroup.zpowers x ≤ Hconj t (U ⊔ Subgroup.zpowers x) := by
    refine sup_le (fun u hu => mem_Hconj.2 (Subgroup.mem_sup_left (hUn t ht u hu)))
      ((Subgroup.zpowers_le).2 (mem_Hconj.2 ?_))
    have : t * x * t⁻¹ = x := by rw [← hxc t ht]; group
    rw [this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  exact mem_Hconj.1 (hle he)

omit [Finite G] in
theorem mem_normalizer_iff_Hconj {E : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (E : Set G) ↔ Hconj g E = E := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext e
    rw [mem_Hconj]
    exact (h e).symm
  · intro h e
    have := SetLike.ext_iff.1 h e
    rw [mem_Hconj] at this
    exact this.symm

theorem x_not_mem_U (h : HBase G x S T P Q Rd F) (hU : HU S T U) (h129 : 2 < T.relIndex S) :
    x ∉ U := by
  intro hxU
  have hsub : {y | ∃ n ∈ S, n * x * n⁻¹ = y} ⊆ ((U : Set G) \ {1}) := by
    rintro y ⟨n, hn, rfl⟩
    refine ⟨hU.normal.2 n hn x hxU, ?_⟩
    intro h1
    apply h.x_ne_one
    have h1' : n * x * n⁻¹ = 1 := h1
    calc x = n⁻¹ * (n * x * n⁻¹) * n := by group
      _ = 1 := by rw [h1']; group
  have hc4 : (U : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hU.four.2
  have hc3 : ((U : Set G) \ {1}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem U.one_mem]
    omega
  have hle3 : {y | ∃ n ∈ S, n * x * n⁻¹ = y}.ncard ≤ 3 := by
    rw [← hc3]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcount := ncard_conj_mul_card_inf_centralizer S x
  have hST : S ⊓ Subgroup.centralizer ({x} : Set G) = T := by
    apply le_antisymm
    · intro s hs
      exact h.extremal s hs.1 (Subgroup.mem_centralizer_singleton_iff.1 hs.2)
    · exact le_inf h.T_le_S h.T_le_C
  rw [hST] at hcount
  have hrel := Subgroup.relIndex_mul_card (H := T) (K := S)
  rw [inf_of_le_left h.T_le_S] at hrel
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have heq : {y | ∃ n ∈ S, n * x * n⁻¹ = y}.ncard = T.relIndex S :=
    Nat.eq_of_mul_eq_mul_right hTpos (hcount.trans hrel.symm)
  have h3 : T.relIndex S = 3 := by omega
  obtain ⟨j, hj⟩ := h.S_pgroup.exists_card_eq
  have hdvd : T.relIndex S ∣ 2 ^ j := hj ▸ Subgroup.relIndex_dvd_card T S
  rw [h3] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

theorem z_mem_U (h : HBase G x S T P Q Rd F) (hz : HZ T P z) (h127 : After127 G x z S T P Q Rd F)
    (h4 : Nat.card (omegaZ T) = 4) (hexp : IP_cent_P_exp T P Q) (hU : HU S T U) {a : G}
    (haS : a ∈ S) (haT : a ∉ T) (haTn : ∀ t : G, t ∈ T ↔ a * t * a⁻¹ ∈ T) : z ∈ U := by
  have hUne : U ≠ ⊥ := by
    intro hb
    have := hU.four.2
    rw [hb] at this
    simp at this
  obtain ⟨u, huU, hu1, hu2, huc⟩ :=
    exists_central_involution_of_normal h.S_pgroup hU.normal.1 hU.normal.2 hUne
  have hb := part_b4 h hz h127 h4 hexp haS haT haTn (hU.le_T huU) (fun s' hs' => huc s' hs')
  rcases h.P_inf_Z hz h4 (Subgroup.mem_inf.1 hb).2 (Subgroup.mem_inf.1 hb).1 with h1 | h1
  · exact absurd h1 hu1
  · rw [← h1]; exact huU

theorem normalizes_EV (h : HBase G x S T P Q Rd F) (hE8 : IP_E8_two T) (hU : HU S T U)
    (hxU : x ∉ U) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) {g : G}
    (hgT : ∀ t : G, t ∈ T ↔ g * t * g⁻¹ ∈ T)
    (hgU : g ∈ Subgroup.normalizer ((U ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
  have hxc : ∀ u ∈ U, x * u = u * x := fun u hu => h.x_central u (hU.le_T hu)
  have hEUnorm : NormalIn (U ⊔ Subgroup.zpowers x) T :=
    normalIn_sup_zpowers h.x_mem_T h.x_central hU.le_T
      (fun t ht u hu => hU.normal.2 t (h.T_le_S ht) u hu)
  have hEU8 := card_sup_zpowers_four hU.four h.x_sq h.x_ne_one hxU hxc
  have hEUab := isElemAb2_sup_zpowers hU.four h.x_sq hxc
  have hEV8 := card_E h hVP hV
  have hEVab := isElemAb2_sup_zpowers hV h.x_sq
    (fun v hv => h.x_central v (h.P_le_T (hVP hv)))
  have hEVT : V ⊔ Subgroup.zpowers x ≤ T := E_le_T h hVP
  have hgTe : Hconj g T = T := by
    ext t
    rw [mem_Hconj]
    exact (hgT t).symm
  have hEg8 : Nat.card (Hconj g (V ⊔ Subgroup.zpowers x) : Subgroup G) = 8 := by
    rw [Hconj_card]; exact hEV8
  have hEgT : Hconj g (V ⊔ Subgroup.zpowers x) ≤ T := by
    have := Hconj_le_Hconj (g := g) hEVT
    rwa [hgTe] at this
  have key := hE8 ⟨U ⊔ Subgroup.zpowers x, hEUnorm.1, hEUab, hEU8,
    fun t ht e he => hEUnorm.2 t ht e he⟩
    (V ⊔ Subgroup.zpowers x) (U ⊔ Subgroup.zpowers x) (Hconj g (V ⊔ Subgroup.zpowers x))
    hEVT hEUnorm.1 hEgT hEVab hEUab (hEVab.hconj g) hEV8 hEU8 hEg8
  have hgEU : Hconj g (U ⊔ Subgroup.zpowers x) = U ⊔ Subgroup.zpowers x :=
    mem_normalizer_iff_Hconj.1 hgU
  rw [mem_normalizer_iff_Hconj]
  rcases key with h1 | h2 | h3
  · rw [h1]; exact hgEU
  · exact h2.symm
  · have h4 : Hconj g (V ⊔ Subgroup.zpowers x) = Hconj g (U ⊔ Subgroup.zpowers x) := by
      rw [hgEU, ← h3]
    have h5 := congrArg (Hconj g⁻¹) h4
    rw [Hconj_inv_Hconj, Hconj_inv_Hconj] at h5
    rw [h5]
    exact hgEU

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
