module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Mu

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix

variable {G : Type*} [Group G]

theorem closure_le_centralizer_of_comm {k : Set G} (hk : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x) :
    closure k ≤ centralizer (closure k : Set G) := by
  have h1 : closure k ≤ centralizer k := by
    rw [closure_le]
    intro x hx
    exact mem_centralizer_iff.2 fun y hy => hk y hy x hx
  rw [closure_le]
  intro x hx
  refine mem_centralizer_iff.2 fun y hy => ?_
  exact (mem_centralizer_iff.1 (h1 hy) x hx).symm

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
  (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS hZ

@[expose] noncomputable def muW [Finite G] : V6 := Classical.choose (hS.exists_mu hZ)

theorem gam_eq_mu [Finite G] (x y : Fin 6) :
    hS.gam hZ x y = hS.muW hZ y • basisVec x + hS.muW hZ x • basisVec y :=
  Classical.choose_spec (hS.exists_mu hZ) x y

@[expose] def tPow (t : G) (c : ZMod 2) : G := if c = 1 then t else 1

omit hZ in
theorem tPow_mem_D (c : ZMod 2) : tPow t c ∈ Dsub t Q := by
  unfold tPow
  split_ifs
  · exact hS.t_mem_D
  · exact one_mem _

@[expose] noncomputable def dW [Finite G] (j : Fin 6) : G := hS.dB hZ j * tPow t (hS.muW hZ j)

theorem dW_mem [Finite G] (j : Fin 6) : hS.dW hZ j ∈ Dsub t Q :=
  mul_mem (hS.dB_mem hZ j) (hS.tPow_mem_D _)

theorem tauD_t : tauD t ψ t = 0 := (hS.tauD_eq_zero_iff hZ hS.t_mem_D).2 (t_mem_sup (X := Q))

theorem coord_kap_tPow_right {x : G} (hx : x ∈ Dsub t Q) (c : ZMod 2) :
    coord ψ (kap x (tPow t c)) = c • tauD t ψ x := by
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c with rfl | rfl
  · simp only [tPow, show ¬ (0 : ZMod 2) = 1 by decide, ite_false, zero_smul]
    rw [show kap x 1 = 1 by simp [kap], hS.rad.coord_one]
  · simp only [tPow, ite_true, one_smul]
    rw [hS.kap_t_right hZ hx, hS.rad.coord_ψ]

theorem coord_kap_tPow_left (c : ZMod 2) {y : G} (hy : y ∈ Dsub t Q) :
    coord ψ (kap (tPow t c) y) = c • tauD t ψ y := by
  rw [hS.kap_symm hZ hy (hS.tPow_mem_D c), hS.coord_kap_tPow_right hZ hy]

theorem kap_dW [Finite G] (i j : Fin 6) : kap (hS.dW hZ i) (hS.dW hZ j) = 1 := by
  have hbi := hS.dB_mem hZ i
  have hbj := hS.dB_mem hZ j
  have hti := hS.tPow_mem_D (hS.muW hZ i)
  have htj := hS.tPow_mem_D (hS.muW hZ j)
  have hk : kap (hS.dW hZ i) (hS.dW hZ j) ∈ Q :=
    hS.kap_mem_Q hZ (hS.dW_mem hZ i) (hS.dW_mem hZ j)
  have hc : coord ψ (kap (hS.dW hZ i) (hS.dW hZ j)) = 0 := by
    rw [dW, dW, hS.kap_mul_left hZ hbi hti (mul_mem hbj htj), hS.kap_mul_right hZ hbi hbj htj,
      hS.kap_mul_right hZ hti hbj htj]
    have q1 := hS.kap_mem_Q hZ hbi hbj
    have q2 := hS.kap_mem_Q hZ hbi htj
    have q3 := hS.kap_mem_Q hZ hti hbj
    have q4 := hS.kap_mem_Q hZ hti htj
    rw [hS.rad.coord_mul (mul_mem q1 q2) (mul_mem q3 q4), hS.rad.coord_mul q1 q2,
      hS.rad.coord_mul q3 q4, hS.coord_kap_tPow_right hZ hbi, hS.coord_kap_tPow_left hZ _ hbj,
      hS.coord_kap_tPow_left hZ _ htj, tPow]
    have h1 : coord ψ (kap (hS.dB hZ i) (hS.dB hZ j)) = hS.gam hZ i j := rfl
    rw [h1, hS.gam_eq_mu hZ, hS.tauD_dB hZ, hS.tauD_dB hZ]
    have h2 : tauD t ψ (if hS.muW hZ j = 1 then t else 1) = 0 := by
      split_ifs
      · exact hS.tauD_t hZ
      · exact (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)
    rw [h2, smul_zero, add_zero]
    ext c
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact (by decide : ∀ A B : ZMod 2, A + B + A + B = 0) _ _
  rw [← hS.rad.ψ_coord hk, hc, hS.rad.ψ_zero]

@[expose] noncomputable def Wsub [Finite G] : Subgroup G :=
  closure ((Q : Set G) ∪ Set.range (hS.dW hZ))

omit hZ in
theorem Q_le_D : Q ≤ Dsub t Q := le_sup_left.trans hS.E_le_D

theorem Wsub_le_D [Finite G] : hS.Wsub hZ ≤ Dsub t Q := by
  rw [Wsub, closure_le]
  rintro x (hx | ⟨j, rfl⟩)
  · exact hS.Q_le_D hx
  · exact hS.dW_mem hZ j

theorem Q_le_Wsub [Finite G] : Q ≤ hS.Wsub hZ := fun _ hx => subset_closure (Or.inl hx)

theorem dW_mem_Wsub [Finite G] (j : Fin 6) : hS.dW hZ j ∈ hS.Wsub hZ :=
  subset_closure (Or.inr ⟨j, rfl⟩)

theorem Wsub_comm [Finite G] {x y : G} (hx : x ∈ hS.Wsub hZ) (hy : y ∈ hS.Wsub hZ) :
    x * y = y * x := by
  have h := closure_le_centralizer_of_comm (k := (Q : Set G) ∪ Set.range (hS.dW hZ)) (by
    rintro _ (hx | ⟨i, rfl⟩) _ (hy | ⟨j, rfl⟩)
    · exact hS.rad.Q_comm hx hy
    · exact (D_comm_Q (hS.dW_mem hZ j) hx).symm
    · exact D_comm_Q (hS.dW_mem hZ i) hy
    · exact kap_eq_one_iff.1 (hS.kap_dW hZ i j))
  exact (mem_centralizer_iff.1 (h hy) x hx)

theorem tauD_dW [Finite G] (j : Fin 6) : tauD t ψ (hS.dW hZ j) = basisVec j := by
  rw [dW, hS.tauD_mul hZ (hS.dB_mem hZ j) (hS.tPow_mem_D _), hS.tauD_dB hZ]
  have : tauD t ψ (tPow t (hS.muW hZ j)) = 0 := by
    unfold tPow
    split_ifs
    · exact hS.tauD_t hZ
    · exact (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)
  rw [this, add_zero]

theorem t_not_mem_Wsub [Finite G] : t ∉ hS.Wsub hZ := by
  intro ht
  have h := hS.Wsub_comm hZ (hS.dW_mem_Wsub hZ 0) ht
  have h1 := hS.kap_t_right hZ (hS.dW_mem hZ 0)
  rw [kap_eq_one_iff.2 h, hS.tauD_dW hZ, ← hS.rad.ψ_zero] at h1
  have h2 := congrFun (hS.rad.ψ_inj h1) 0
  rw [basisVec, toVec_two_pow' 0] at h2
  simp at h2

theorem tauD_surj_Wsub [Finite G] (v : V6) : ∃ w ∈ hS.Wsub hZ, tauD t ψ w = v := by
  set l := (List.finRange 6).map fun j => if v j = 1 then hS.dW hZ j else 1
  have hlW : ∀ x ∈ l, x ∈ hS.Wsub hZ := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    split_ifs
    · exact hS.dW_mem_Wsub hZ j
    · exact one_mem _
  refine ⟨l.prod, list_prod_mem hlW, ?_⟩
  rw [(hS.tauD_list_prod hZ fun x hx => hS.Wsub_le_D hZ (hlW x hx)).2, List.map_map,
    ← Fin.sum_univ_def]
  conv_rhs => rw [eq_sum_basisVec v]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (v j) with h | h
  · simp only [h, zero_smul, show ¬ (0 : ZMod 2) = 1 by decide, ite_false]
    exact (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _)
  · simp only [h, one_smul, ite_true, hS.tauD_dW hZ]

theorem card_Wsub [Finite G] : Nat.card (hS.Wsub hZ) = 4096 := by
  set f : hS.Wsub hZ →* Multiplicative V6 := (hS.tauHom hZ).comp (inclusion (hS.Wsub_le_D hZ))
  have hrange : f.range = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, hwv⟩ := hS.tauD_surj_Wsub hZ (Multiplicative.toAdd v)
    exact ⟨⟨w, hw⟩, by change Multiplicative.ofAdd (tauD t ψ w) = v; rw [hwv]; rfl⟩
  have hker : 64 ≤ Nat.card f.ker := by
    rw [← hS.rad.card_Q]
    refine Nat.card_le_card_of_injective (fun q => ⟨⟨q.1, hS.Q_le_Wsub hZ q.2⟩,
      MonoidHom.mem_ker.2 ?_⟩) fun q q' h => ?_
    · change Multiplicative.ofAdd (tauD t ψ q.1) = 1
      rw [(hS.tauD_eq_zero_iff hZ (hS.Q_le_D q.2)).2 (mem_sup_left q.2)]
      rfl
    · simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hrange, Subgroup.card_top] at h1
  have h64 : Nat.card (Multiplicative V6) = 64 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [h64] at h1
  have hlow : 4096 ≤ Nat.card (hS.Wsub hZ) := by omega
  have hdvd : Nat.card (hS.Wsub hZ) ∣ 2 ^ 13 := by
    have := Subgroup.card_dvd_of_le (hS.Wsub_le_D hZ)
    rwa [hS.card_D hZ] at this
  have hne : Nat.card (hS.Wsub hZ) ≠ 2 ^ 13 := fun h => by
    have hWD : hS.Wsub hZ = Dsub t Q :=
      Subgroup.eq_of_le_of_card_ge (hS.Wsub_le_D hZ) (by rw [h, hS.card_D hZ]; norm_num)
    exact hS.t_not_mem_Wsub hZ (hWD ▸ hS.t_mem_D)
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk12 : k ≤ 12 := by
    rcases Nat.lt_or_ge k 13 with h | h
    · omega
    · exact absurd (hkc.trans (by rw [show k = 13 by omega])) hne
  have hup : Nat.card (hS.Wsub hZ) ≤ 4096 := by
    rw [hkc]
    calc 2 ^ k ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) hk12
      _ = 4096 := rfl
  omega

theorem relIndex_Wsub_D [Finite G] : (hS.Wsub hZ).relIndex (Dsub t Q) = 2 := by
  have h := Subgroup.relIndex_mul_card (H := hS.Wsub hZ) (K := Dsub t Q)
  rw [inf_of_le_left (hS.Wsub_le_D hZ), hS.card_Wsub hZ, hS.card_D hZ] at h
  omega

theorem eq_Wsub [Finite G] {A : Subgroup G} (hAD : A ≤ Dsub t Q)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hcard : Nat.card A = 4096) : A = hS.Wsub hZ := by
  by_contra hne
  have hnot : ¬ A ≤ hS.Wsub hZ := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hS.card_Wsub hZ]))
  obtain ⟨x₀, hx₀A, hx₀W⟩ := Set.not_subset.1 hnot
  have hidx : ((hS.Wsub hZ).subgroupOf (Dsub t Q)).index = 2 := hS.relIndex_Wsub_D hZ
  have hw₀ : t⁻¹ * x₀ ∈ hS.Wsub hZ := by
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t, hS.t_mem_D⟩⁻¹)
      (b := ⟨x₀, hAD hx₀A⟩)).2 (by
        rw [inv_mem_iff]
        exact ⟨fun h => absurd h (hS.t_not_mem_Wsub hZ), fun h => absurd h hx₀W⟩)
    exact h
  have hAWE : A ⊓ hS.Wsub hZ ≤ (Q ⊔ zpowers t : Subgroup G) := by
    rintro x ⟨hxA, hxW⟩
    have h1 := hA x hxA x₀ hx₀A
    have h2 := hS.Wsub_comm hZ hxW hw₀
    have htx : t * x = x * t := by
      have h3 : x₀ = t * (t⁻¹ * x₀) := by group
      rw [h3] at h1
      have h4 : x * t * (t⁻¹ * x₀) = t * x * (t⁻¹ * x₀) := by
        calc x * t * (t⁻¹ * x₀) = x * (t * (t⁻¹ * x₀)) := by group
          _ = t * (t⁻¹ * x₀) * x := h1
          _ = t * ((t⁻¹ * x₀) * x) := by group
          _ = t * (x * (t⁻¹ * x₀)) := by rw [h2]
          _ = t * x * (t⁻¹ * x₀) := by group
      exact (mul_right_cancel h4).symm
    have hxD := hAD hxA
    rw [← hS.tauD_eq_zero_iff hZ hxD]
    have h5 := hS.kap_t_left hZ hxD
    rw [kap_eq_one_iff.2 htx, ← hS.rad.ψ_zero] at h5
    exact (hS.rad.ψ_inj h5).symm
  have hsmall : Nat.card (A ⊓ hS.Wsub hZ : Subgroup G) ≤ 128 := by
    rw [← hS.card_E]
    exact Subgroup.card_le_of_le hAWE
  have hbig : 2048 ≤ Nat.card (A ⊓ hS.Wsub hZ : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := hS.Wsub hZ) (K := A)
    have hle : (hS.Wsub hZ).relIndex A ≤ 2 := by
      rw [← hS.relIndex_Wsub_D hZ]
      exact relIndex_le_of_le_right hAD (by rw [hS.relIndex_Wsub_D hZ]; norm_num)
    rw [hcard, inf_comm] at h
    nlinarith
  omega

theorem D_le_normalizer_Wsub [Finite G] : Dsub t Q ≤ normalizer (hS.Wsub hZ : Set G) := by
  have key : ∀ x ∈ Dsub t Q, ∀ w ∈ hS.Wsub hZ, x * w * x⁻¹ ∈ hS.Wsub hZ := by
    intro x hx w hw
    have h : x * w * x⁻¹ = kap x w * w := by rw [kap]; group
    rw [h]
    exact mul_mem (hS.Q_le_Wsub hZ (hS.kap_mem_Q hZ hx (hS.Wsub_le_D hZ hw))) hw
  intro x hx
  refine mem_normalizer_iff.2 fun w => ⟨key x hx w, fun hw => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ hw
  simpa [mul_assoc] using this

theorem P_le_normalizer_Wsub [Finite G] : P ≤ normalizer (hS.Wsub hZ : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  refine hS.eq_Wsub hZ ?_ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact hS.conj_mem_D hx (hS.Wsub_le_D hZ hw)
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    change x * w * x⁻¹ * (x * w' * x⁻¹) = x * w' * x⁻¹ * (x * w * x⁻¹)
    have := hS.Wsub_comm hZ hw hw'
    calc x * w * x⁻¹ * (x * w' * x⁻¹) = x * (w * w') * x⁻¹ := by group
      _ = x * (w' * w) * x⁻¹ := by rw [this]
      _ = x * w' * x⁻¹ * (x * w * x⁻¹) := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hS.card_Wsub hZ]

theorem normalizer_E_le_normalizer_Wsub [Finite G] :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (hS.Wsub hZ : Set G) := by
  intro g hg
  obtain ⟨d, hd, x, hx, rfl⟩ := hS.exists_D_mul hZ hg
  exact mul_mem (hS.D_le_normalizer_Wsub hZ hd) (hS.P_le_normalizer_Wsub hZ hx)

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
