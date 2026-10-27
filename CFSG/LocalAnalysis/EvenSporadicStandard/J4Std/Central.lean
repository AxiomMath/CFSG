module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G}

theorem T0_le_Hloc [Finite G] (hD : LocalData L U T0) : T0 ≤ Hloc L U := by
  have key : ∀ t ∈ T0, ∀ u ∈ U, t * u * t⁻¹ ∈ U := by
    intro t ht u hu
    let A : Subgroup G := U.map (MulAut.conj t).toMonoidHom
    have hA : A = U := by
      apply hD.unique A
      · rintro _ ⟨v, hv, rfl⟩
        exact mul_mem (mul_mem ht (hD.U_le_T0 hv)) (inv_mem ht)
      · rintro _ ⟨v, hv, rfl⟩
        show t * v * t⁻¹ * (t * v * t⁻¹) = 1
        calc t * v * t⁻¹ * (t * v * t⁻¹) = t * (v * v) * t⁻¹ := by group
          _ = 1 := by rw [hD.U_sq v hv]; group
      · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
        show t * v * t⁻¹ * (t * w * t⁻¹) = t * w * t⁻¹ * (t * v * t⁻¹)
        calc t * v * t⁻¹ * (t * w * t⁻¹) = t * (v * w) * t⁻¹ := by group
          _ = t * (w * v) * t⁻¹ := by rw [hD.U_comm v hv w hw]
          _ = t * w * t⁻¹ * (t * v * t⁻¹) := by group
      · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective, hD.card_U]
    have : t * u * t⁻¹ ∈ A := ⟨u, hu, rfl⟩
    rwa [hA] at this
  intro t ht
  refine mem_Hloc_of (hD.T0_le_L ht) (key t ht) (fun u hu => ?_)
  have := key t⁻¹ (inv_mem ht) u hu
  rwa [inv_inv] at this

variable (hS : Setting L z) (hD : LocalData L U T0)
include hS hD

theorem T_le_N [Finite G] : Vsub T0 z ≤ Nsub U z := by
  intro x hx
  obtain ⟨t, ht, hxt⟩ := (mem_Vsub_iff hS hD.T0_le_L).1 hx
  have htH : t ∈ Hloc L U := T0_le_Hloc hD ht
  have htN : t ∈ Nsub U z := Hloc_le_N hS (hD.U_le_T0.trans hD.T0_le_L) htH
  rcases hxt with hxt | hxt
  · rw [hxt]; exact htN
  · rw [hxt]; exact mul_mem (V_le_N z_mem_V) htN

theorem N_eq_of_central [Finite G] (hcen : ∀ n ∈ Nsub U z, n * z = z * n) :
    Nsub U z = Vsub (Hloc L U) z := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  apply le_antisymm
  · intro n hn
    obtain ⟨l, hl, hnl⟩ := exists_Hloc_of_mem_N_comm hS hUL hn (hcen n hn).symm
    refine (mem_Vsub_iff hS Hloc_le_L).2 ⟨l, hl, ?_⟩
    rcases hnl with hnl | hnl
    · exact Or.inl hnl
    · exact Or.inr (by rw [hnl, (hS.z_comm l (Hloc_le_L hl))])
  · refine sup_le (Hloc_le_N hS hUL) ?_
    rw [zpowers_le]
    exact V_le_N z_mem_V

theorem V_unique [Finite G] (A : Subgroup G) (hAT : A ≤ Vsub T0 z) (hA2 : ∀ a ∈ A, a * a = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAcard : Nat.card A = 2 ^ 12) :
    A = Vsub U z := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hT0L := hD.T0_le_L
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  have hc : ∀ t ∈ T0, z * t = t * z := fun t ht => z_comm_U hS hT0L ht
  let P : Subgroup G :=
    { carrier := {t | t ∈ T0 ∧ (t ∈ A ∨ z * t ∈ A)}
      mul_mem' := by
        rintro t t' ⟨ht, hta⟩ ⟨ht', hta'⟩
        refine ⟨mul_mem ht ht', ?_⟩
        have e1 : z * (t * t') = (z * t) * t' := by group
        have e2 : z * (t * t') = t * (z * t') := by
          calc z * (t * t') = (z * t) * t' := by group
            _ = (t * z) * t' := by rw [hc t ht]
            _ = t * (z * t') := by group
        have e3 : (z * t) * (z * t') = t * t' := by
          calc (z * t) * (z * t') = z * (t * z) * t' := by group
            _ = z * (z * t) * t' := by rw [hc t ht]
            _ = (z * z) * t * t' := by group
            _ = t * t' := by rw [hS.z_mul_self, one_mul]
        rcases hta with hta | hta <;> rcases hta' with hta' | hta'
        · exact Or.inl (mul_mem hta hta')
        · right; rw [e2]; exact mul_mem hta hta'
        · right; rw [e1]; exact mul_mem hta hta'
        · left; rw [← e3]; exact mul_mem hta hta'
      one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
      inv_mem' := by
        rintro t ⟨ht, hta⟩
        refine ⟨inv_mem ht, ?_⟩
        rcases hta with hta | hta
        · exact Or.inl (inv_mem hta)
        · right
          have := inv_mem hta
          rw [mul_inv_rev, hzi] at this
          have e : t⁻¹ * z = z * t⁻¹ := (hc t⁻¹ (inv_mem ht)).symm
          rwa [e] at this }
  have hPT : P ≤ T0 := fun t ht => ht.1
  have hP2 : ∀ a ∈ P, a * a = 1 := by
    rintro t ⟨ht, hta | hta⟩
    · exact hA2 t hta
    · have := hA2 _ hta
      calc t * t = z * z * (t * t) := by rw [hS.z_mul_self, one_mul]
        _ = z * t * (z * t) := by
          calc z * z * (t * t) = z * (z * t) * t := by group
            _ = z * (t * z) * t := by rw [hc t ht]
            _ = z * t * (z * t) := by group
        _ = 1 := this
  have hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    rintro t ⟨ht, hta⟩ t' ⟨ht', hta'⟩
    have hct := hc t ht
    have hct' := hc t' ht'
    rcases hta with hta | hta <;> rcases hta' with hta' | hta'
    · exact hAc t hta t' hta'
    · have h := hAc t hta (z * t') hta'
      have e1 : t * (z * t') = z * (t * t') := by
        calc t * (z * t') = (t * z) * t' := by group
          _ = (z * t) * t' := by rw [hct]
          _ = z * (t * t') := by group
      have e2 : z * t' * t = z * (t' * t) := by group
      rw [e1, e2] at h
      exact mul_left_cancel h
    · have h := hAc (z * t) hta t' hta'
      have e1 : z * t * t' = z * (t * t') := by group
      have e2 : t' * (z * t) = z * (t' * t) := by
        calc t' * (z * t) = (t' * z) * t := by group
          _ = (z * t') * t := by rw [hct']
          _ = z * (t' * t) := by group
      rw [e1, e2] at h
      exact mul_left_cancel h
    · have h := hAc (z * t) hta (z * t') hta'
      have e1 : z * t * (z * t') = t * t' := by
        calc z * t * (z * t') = z * (t * z) * t' := by group
          _ = z * (z * t) * t' := by rw [hct]
          _ = (z * z) * (t * t') := by group
          _ = t * t' := by rw [hS.z_mul_self, one_mul]
      have e2 : z * t' * (z * t) = t' * t := by
        calc z * t' * (z * t) = z * (t' * z) * t := by group
          _ = z * (z * t') * t := by rw [hct']
          _ = (z * z) * (t' * t) := by group
          _ = t' * t := by rw [hS.z_mul_self, one_mul]
      rw [e1, e2] at h
      exact h
  have hAsub : (A : Set G) ⊆ (P : Set G) ∪ (fun t => z * t) '' (P : Set G) := by
    intro a ha
    obtain ⟨t, ht, hat⟩ := (mem_Vsub_iff hS hT0L).1 (hAT ha)
    rcases hat with hat | hat
    · left; rw [hat]; exact ⟨ht, Or.inl (hat ▸ ha)⟩
    · right; exact ⟨t, ⟨ht, Or.inr (hat ▸ ha)⟩, hat.symm⟩
  have hcardP : 2 ^ 11 ≤ Nat.card P := by
    have h1 : Nat.card A ≤ ((P : Set G) ∪ (fun t => z * t) '' (P : Set G)).ncard := by
      rw [show Nat.card A = (A : Set G).ncard from Nat.card_coe_set_eq (A : Set G)]
      exact Set.ncard_le_ncard hAsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (P : Set G) ((fun t => z * t) '' (P : Set G))
    have h3 : ((fun t => z * t) '' (P : Set G)).ncard ≤ (P : Set G).ncard :=
      Set.ncard_image_le (Set.toFinite _)
    have h4 : Nat.card P = (P : Set G).ncard := Nat.card_coe_set_eq (P : Set G)
    omega
  have hPU : P = U := hD.unique P hPT hP2 hPc hcardP
  have hAV : A ≤ Vsub U z := by
    intro a ha
    rcases hAsub ha with hP' | ⟨t, hP', rfl⟩
    · have : a ∈ U := hPU ▸ hP'
      exact mem_sup_left this
    · have : t ∈ U := hPU ▸ hP'
      exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left this)
  refine eq_of_le_of_card_ge hAV ?_
  rw [card_Vsub hS hUL, hD.card_U, hAcard]
  norm_num

theorem V_sq [Finite G] {v : G} (hv : v ∈ Vsub U z) : v * v = 1 := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨u, hu, hvu⟩ := (mem_Vsub_iff hS hUL).1 hv
  rcases hvu with hvu | hvu
  · rw [hvu]; exact hD.U_sq u hu
  · rw [hvu]
    calc z * u * (z * u) = z * (u * z) * u := by group
      _ = z * (z * u) * u := by rw [z_comm_U hS hUL hu]
      _ = (z * z) * (u * u) := by group
      _ = 1 := by rw [hS.z_mul_self, hD.U_sq u hu, one_mul]

theorem V_comm [Finite G] {v w : G} (hv : v ∈ Vsub U z) (hw : w ∈ Vsub U z) : v * w = w * v := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  obtain ⟨u, hu, hvu⟩ := (mem_Vsub_iff hS hUL).1 hv
  obtain ⟨u', hu', hwu⟩ := (mem_Vsub_iff hS hUL).1 hw
  have hz : ∀ u ∈ U, z * u = u * z := fun u hu => z_comm_U hS hUL hu
  rcases hvu with hvu | hvu <;> rcases hwu with hwu | hwu <;> rw [hvu, hwu]
  · exact hD.U_comm u hu u' hu'
  · calc u * (z * u') = (u * z) * u' := by group
      _ = z * u * u' := by rw [← hz u hu]
      _ = z * (u * u') := by group
      _ = z * (u' * u) := by rw [hD.U_comm u hu u' hu']
      _ = z * u' * u := by group
  · calc z * u * u' = z * (u * u') := by group
      _ = z * (u' * u) := by rw [hD.U_comm u hu u' hu']
      _ = (z * u') * u := by group
      _ = u' * z * u := by rw [hz u' hu']
      _ = u' * (z * u) := by group
  · calc z * u * (z * u') = z * (u * z) * u' := by group
      _ = z * (z * u) * u' := by rw [hz u hu]
      _ = (z * z) * (u * u') := by group
      _ = (z * z) * (u' * u) := by rw [hD.U_comm u hu u' hu']
      _ = z * (z * u') * u := by group
      _ = z * (u' * z) * u := by rw [hz u' hu']
      _ = z * u' * (z * u) := by group

theorem T_sylow_in_N [Finite G] (hcen : ∀ n ∈ Nsub U z, n * z = z * n) (Q : Subgroup G)
    (hTQ : Vsub T0 z ≤ Q) (hQN : Q ≤ Nsub U z) (hQ : IsPGroup 2 Q) : Q = Vsub T0 z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT0L := hD.T0_le_L
  have hHT := T0_le_Hloc hD
  have hcT : Nat.card (Vsub T0 z) = 2 * Nat.card T0 := card_Vsub hS hT0L
  have hcN : Nat.card (Nsub U z) = 2 * Nat.card (Hloc L U) := by
    rw [N_eq_of_central hS hD hcen]; exact card_Vsub hS Hloc_le_L
  have hm : (T0.relIndex (Hloc L U)) * Nat.card T0 = Nat.card (Hloc L U) := by
    have := Subgroup.relIndex_mul_card (H := T0) (K := Hloc L U)
    rwa [inf_eq_left.2 hHT] at this
  have hmodd : ¬ 2 ∣ T0.relIndex (Hloc L U) := by
    intro h2
    apply hD.T0_index_odd
    rw [← Subgroup.relIndex_mul_relIndex T0 (Hloc L U) L hHT Hloc_le_L]
    exact Dvd.dvd.mul_right h2 _
  obtain ⟨k, hk⟩ := hD.T0_pGroup.exists_card_eq
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have h1 : Nat.card (Vsub T0 z) ∣ Nat.card Q := Subgroup.card_dvd_of_le hTQ
  have h2 : Nat.card Q ∣ Nat.card (Nsub U z) := Subgroup.card_dvd_of_le hQN
  rw [hcT, hk, hn] at h1
  have hNm : Nat.card (Nsub U z) = 2 ^ (k + 1) * T0.relIndex (Hloc L U) := by
    rw [hcN, ← hm, hk]; ring
  rw [hn, hNm] at h2
  have hcop : Nat.Coprime (2 ^ n) (T0.relIndex (Hloc L U)) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 (Nat.odd_iff.2 (by
      by_contra hc
      exact hmodd (Nat.dvd_of_mod_eq_zero (by omega)))))
  have h3 : 2 ^ n ∣ 2 ^ (k + 1) := hcop.dvd_of_dvd_mul_right h2
  have h4 : n ≤ k + 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h3
  have h5 : k + 1 ≤ n := by
    have : 2 ^ (k + 1) ∣ 2 ^ n := by rw [pow_succ, mul_comm]; exact h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hnk : n = k + 1 := le_antisymm h4 h5
  refine (eq_of_le_of_card_ge hTQ ?_).symm
  rw [hcT, hk, hn, hnk, pow_succ, mul_comm]

theorem false_of_central [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hcen : ∀ n ∈ Nsub U z, n * z = z * n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hT0L := hD.T0_le_L
  set T := Vsub T0 z with hTdef
  have hcT : Nat.card T = 2 * Nat.card T0 := card_Vsub hS hT0L
  have hT2 : IsPGroup 2 T := by
    obtain ⟨k, hk⟩ := hD.T0_pGroup.exists_card_eq
    exact IsPGroup.of_card (n := k + 1) (by rw [hcT, hk, pow_succ, mul_comm])
  have hT0T : T0 ≤ T := le_sup_left
  have hzT : z ∈ T := mem_sup_right (mem_zpowers z)
  have hzT0 : z ∉ T0 := fun h => hS.z_not_mem (hT0L h)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hS.z_mul_self) hS.z_ne_one
  have hVT : Vsub U z ≤ T := sup_le_sup_right hD.U_le_T0 _
  obtain ⟨P, hTP⟩ := hT2.exists_le_sylow
  have hTeq : T = (P : Subgroup G) := by
    by_contra hne
    have hlt : T < (P : Subgroup G) := lt_of_le_of_ne hTP hne
    have hP2 : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
    have : Group.IsNilpotent (P : Subgroup G) := hP2.isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := (P : Subgroup G))
    have hbot : T.subgroupOf (P : Subgroup G) < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hne ?_
      apply le_antisymm hTP
      intro x hx
      have : (⟨x, hx⟩ : (P : Subgroup G)) ∈ T.subgroupOf (P : Subgroup G) := by rw [h]; trivial
      exact this
    obtain ⟨x', hx'N, hx'T⟩ := IsConcreteLE.exists_of_lt (hnc _ hbot)
    set n : G := (x' : G) with hn
    have hnP : n ∈ (P : Subgroup G) := x'.2
    have hnT : n ∉ T := hx'T
    have hconj : ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
      intro t ht
      have h1 : (⟨t, hTP ht⟩ : (P : Subgroup G)) ∈ T.subgroupOf (P : Subgroup G) := ht
      have := (mem_normalizer_iff.1 hx'N _).1 h1
      exact this
    have hconj' : ∀ t ∈ T, n⁻¹ * t * n⁻¹⁻¹ ∈ T := by
      intro t ht
      have h1 : (x'⁻¹ * ⟨t, hTP ht⟩ * x'⁻¹⁻¹ : (P : Subgroup G)) ∈
          T.subgroupOf (P : Subgroup G) := by
        rw [mem_normalizer_iff.1 hx'N]
        have e : x' * (x'⁻¹ * ⟨t, hTP ht⟩ * x'⁻¹⁻¹) * x'⁻¹ = (⟨t, hTP ht⟩ : (P : Subgroup G)) := by
          group
        rw [e]
        exact ht
      exact h1
    have hnV : ∀ v ∈ Vsub U z, n * v * n⁻¹ ∈ Vsub U z := by
      intro v hv
      let A : Subgroup G := (Vsub U z).map (MulAut.conj n).toMonoidHom
      have hA : A = Vsub U z := by
        apply V_unique hS hD A
        · rintro _ ⟨w, hw, rfl⟩
          exact hconj w (hVT hw)
        · rintro _ ⟨w, hw, rfl⟩
          show n * w * n⁻¹ * (n * w * n⁻¹) = 1
          calc n * w * n⁻¹ * (n * w * n⁻¹) = n * (w * w) * n⁻¹ := by group
            _ = 1 := by rw [V_sq hS hD hw]; group
        · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
          show n * w * n⁻¹ * (n * w' * n⁻¹) = n * w' * n⁻¹ * (n * w * n⁻¹)
          calc n * w * n⁻¹ * (n * w' * n⁻¹) = n * (w * w') * n⁻¹ := by group
            _ = n * (w' * w) * n⁻¹ := by rw [V_comm hS hD hw hw']
            _ = n * w' * n⁻¹ * (n * w * n⁻¹) := by group
        · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, card_Vsub hS hUL,
            hD.card_U]
          norm_num
      have : n * v * n⁻¹ ∈ A := ⟨v, hv, rfl⟩
      rwa [hA] at this
    have hnV' : ∀ v ∈ Vsub U z, n⁻¹ * v * n ∈ Vsub U z := by
      intro v hv
      let A : Subgroup G := (Vsub U z).map (MulAut.conj n⁻¹).toMonoidHom
      have hA : A = Vsub U z := by
        apply V_unique hS hD A
        · rintro _ ⟨w, hw, rfl⟩
          have := hconj' w (hVT hw)
          simpa using this
        · rintro _ ⟨w, hw, rfl⟩
          show n⁻¹ * w * n⁻¹⁻¹ * (n⁻¹ * w * n⁻¹⁻¹) = 1
          calc n⁻¹ * w * n⁻¹⁻¹ * (n⁻¹ * w * n⁻¹⁻¹) = n⁻¹ * (w * w) * n⁻¹⁻¹ := by group
            _ = 1 := by rw [V_sq hS hD hw]; group
        · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
          show n⁻¹ * w * n⁻¹⁻¹ * (n⁻¹ * w' * n⁻¹⁻¹) = n⁻¹ * w' * n⁻¹⁻¹ * (n⁻¹ * w * n⁻¹⁻¹)
          calc n⁻¹ * w * n⁻¹⁻¹ * (n⁻¹ * w' * n⁻¹⁻¹) = n⁻¹ * (w * w') * n⁻¹⁻¹ := by group
            _ = n⁻¹ * (w' * w) * n⁻¹⁻¹ := by rw [V_comm hS hD hw hw']
            _ = n⁻¹ * w' * n⁻¹⁻¹ * (n⁻¹ * w * n⁻¹⁻¹) := by group
        · rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, card_Vsub hS hUL,
            hD.card_U]
          norm_num
      have : n⁻¹ * v * n⁻¹⁻¹ ∈ A := ⟨v, hv, rfl⟩
      rwa [hA, inv_inv] at this
    have hnN : n ∈ Nsub U z := by
      rw [Nsub, mem_normalizer_iff]
      intro v
      refine ⟨hnV v, fun hv => ?_⟩
      have := hnV' _ hv
      have e : n⁻¹ * (n * v * n⁻¹) * n = v := by group
      rwa [e] at this
    have hQN : T ⊔ zpowers n ≤ Nsub U z :=
      sup_le (T_le_N hS hD) (by rw [zpowers_le]; exact hnN)
    have hQP : T ⊔ zpowers n ≤ (P : Subgroup G) :=
      sup_le hTP (by rw [zpowers_le]; exact hnP)
    have hQ2 : IsPGroup 2 ↥(T ⊔ zpowers n) := hP2.to_le hQP
    have hQT := T_sylow_in_N hS hD hcen (T ⊔ zpowers n) le_sup_left hQN hQ2
    apply hnT
    have hQT' : T ⊔ zpowers n = T := hQT
    have hmem : n ∈ T ⊔ zpowers n := mem_sup_right (mem_zpowers n)
    rwa [hQT'] at hmem
  have hindex : ¬ 2 ∣ T.index := by
    rw [hTeq]
    exact P.not_dvd_index
  have hrel : T0.relIndex T = 2 := by
    have := Subgroup.relIndex_mul_card (H := T0) (K := T)
    rw [inf_eq_left.2 hT0T, hcT] at this
    have hpos : 0 < Nat.card T0 := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos this
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hT2 hindex hT0T hrel hzT hzT0 hz2
  exact hS.conj_not_mem_of_mul_self (g := g⁻¹) (by simpa using hT0L hg)

end CFSG.EvenSporadicStandard.J4Std
