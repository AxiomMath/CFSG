module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveBound
public import CFSG.Quasithin.Recognition.M12AscTrans

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

theorem card_inf_centralizer_conj {U : Subgroup G} {g : G} (hg : g ∈ normalizer (U : Set G))
    (a : G) :
    Nat.card (U ⊓ centralizer ({g * a * g⁻¹} : Set G) : Subgroup G) =
      Nat.card (U ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  have key : ∀ (g a : G), g ∈ normalizer (U : Set G) →
      Nat.card (U ⊓ centralizer ({a} : Set G) : Subgroup G) ≤
        Nat.card (U ⊓ centralizer ({g * a * g⁻¹} : Set G) : Subgroup G) := by
    intro g a hg
    rw [← Subgroup.card_map_of_injective (K := U ⊓ centralizer ({a} : Set G))
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
    apply Subgroup.card_le_of_le
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxU, hxa⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxU, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxa ⊢
    change g * x * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  refine le_antisymm ?_ (key g a hg)
  have := key g⁻¹ (g * a * g⁻¹) (inv_mem hg)
  rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this

theorem card_eq_two_mul_inf {V X₀ Y : Subgroup G} (hX₀ : X₀ ≤ V)
    (hV : V ≤ normalizer (X₀ : Set G)) (hcard : Nat.card V = 2 * Nat.card X₀) (hY : Y ≤ V)
    (hYX : ¬ Y ≤ X₀) : Nat.card Y = 2 * Nat.card (Y ⊓ X₀ : Subgroup G) := by
  have h1 := card_sup_mul_card_inf (hY.trans hV)
  have h2 : Nat.card (Y ⊔ X₀ : Subgroup G) ∣ 2 * Nat.card X₀ :=
    hcard ▸ Subgroup.card_dvd_of_le (sup_le hY hX₀)
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le (le_sup_right : X₀ ≤ Y ⊔ X₀)
  have hX0 : 0 < Nat.card X₀ := Nat.card_pos
  have hd2 : d ∣ 2 := by
    rw [hd, mul_comm 2] at h2
    exact (Nat.mul_dvd_mul_iff_left hX0).mp h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with rfl | rfl
  · exfalso
    have : X₀ = Y ⊔ X₀ := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hd, mul_one])
    exact hYX (le_sup_left.trans this.symm.le)
  · rw [hd] at h1
    have h3 : Nat.card X₀ * (2 * Nat.card (Y ⊓ X₀ : Subgroup G)) = Nat.card X₀ * Nat.card Y := by
      calc Nat.card X₀ * (2 * Nat.card (Y ⊓ X₀ : Subgroup G)) =
            Nat.card X₀ * 2 * Nat.card (Y ⊓ X₀ : Subgroup G) := by ring
        _ = Nat.card Y * Nat.card X₀ := h1
        _ = Nat.card X₀ * Nat.card Y := by ring
    exact (Nat.eq_of_mul_eq_mul_left hX0 h3).symm

theorem card_le_of_isPGroup_two {B : Subgroup G} (hB : IsPGroup 2 B) {a b : ℕ}
    (hd : Nat.card B ∣ 3 ^ a * 2 ^ b) : Nat.card B ≤ 2 ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  rw [hk] at hd ⊢
  have hcop : Nat.Coprime (2 ^ k) (3 ^ a) := Nat.Coprime.pow _ _ (by norm_num)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_left hd)

namespace Hyp

variable {fr : JankoFrame G z}

theorem N_le_U (h : Hyp fr) : fr.N ≤ fr.U :=
  le_oddCoreOf Subgroup.le_normalizer le_rfl h.odd_card_N

theorem U_le_V (_h : Hyp fr) : fr.U ≤ normalizer (fr.N : Set G) := oddCoreOf_le _

theorem V_le_normalizer_U (_h : Hyp fr) :
    normalizer (fr.N : Set G) ≤ normalizer (fr.U : Set G) :=
  le_normalizer_oddCoreOf _

theorem odd_card_U (_h : Hyp fr) : Odd (Nat.card fr.U) := odd_card_oddCoreOf _

theorem card_U_dvd (h : Hyp fr) : Nat.card fr.U ∣ 3 ^ 9 := by
  have h1 : Nat.card fr.U ∣ 3 ^ 9 * 2 ^ 4 :=
    h.card_normalizer_N ▸ Subgroup.card_dvd_of_le h.U_le_V
  have hcop : Nat.Coprime (Nat.card fr.U) (2 ^ 4) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr h.odd_card_U)
  exact hcop.dvd_of_dvd_mul_right h1

theorem t_mem_V (h : Hyp fr) : fr.t ∈ normalizer (fr.N : Set G) :=
  h.L_le_normalizer_N h.t_mem_L

theorem t_mem_normalizer_U (h : Hyp fr) : fr.t ∈ normalizer (fr.U : Set G) :=
  h.V_le_normalizer_U h.t_mem_V

theorem z_mem_normalizer_U (h : Hyp fr) : z ∈ normalizer (fr.U : Set G) :=
  h.V_le_normalizer_U h.z_mem_normalizer_N

theorem normalizer_N_inf_H_le (h : Hyp fr) :
    normalizer (fr.N : Set G) ⊓ centralizer ({z} : Set G) ≤
      normalizer (fr.E : Set G) ⊓ centralizer ({z} : Set G) := by
  intro g hg
  obtain ⟨hgN, hgz⟩ := Subgroup.mem_inf.mp hg
  refine Subgroup.mem_inf.mpr ⟨?_, hgz⟩
  rw [← h.p11.N_inf_centralizer_z]
  exact inf_mem_normalizer hgN
    (mem_normalizer_centralizer_singleton (Subgroup.mem_centralizer_singleton_iff.mp hgz))

theorem card_E_sup_K (_h : Hyp fr) : Nat.card (fr.E ⊔ fr.K : Subgroup G) = 1296 := by
  rw [sup_comm, card_sup_of_inf_eq_bot fr.K_le_normalizer (by rw [inf_comm]; exact fr.E_inf_K),
    fr.card_K, fr.card_E]

theorem card_dvd_of_le_V_H (h : Hyp fr) {D : Subgroup G}
    (hD : D ≤ normalizer (fr.N : Set G) ⊓ centralizer ({z} : Set G)) : Nat.card D ∣ 1296 := by
  rw [← h.card_E_sup_K, ← fr.normalizer_E]
  exact Subgroup.card_dvd_of_le (hD.trans h.normalizer_N_inf_H_le)

theorem card_Q (_h : Hyp fr) : Nat.card fr.Q = 8 := by
  rw [Nat.card_congr fr.Q_quaternion.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem Q_le_L (h : Hyp fr) : fr.Q ≤ fr.L := by
  rw [fr.Q_eq, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.pow_mem _ h.ℓ_mem_L 2
  · exact Subgroup.mul_mem _ h.t_mem_L h.ℓ_mem_L

theorem z_mem_Q (_h : Hyp fr) : z ∈ fr.Q := by
  have h1 : fr.ℓ ^ 2 ∈ fr.Q := by
    rw [fr.Q_eq]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have := Subgroup.pow_mem _ h1 2
  rwa [← pow_mul, fr.ℓ_pow_four] at this

theorem isPGroup_L (_h : Hyp fr) : IsPGroup 2 fr.L := IsPGroup.of_card (n := 4) fr.card_L

theorem eq_L_of_le (h : Hyp fr) (R : Subgroup G) (hR : R ≤ normalizer (fr.N : Set G))
    (hR2 : IsPGroup 2 R) (hLR : fr.L ≤ R) : R = fr.L := by
  have hd : Nat.card R ∣ 3 ^ 9 * 2 ^ 4 := h.card_normalizer_N ▸ Subgroup.card_dvd_of_le hR
  exact (Subgroup.eq_of_le_of_card_ge hLR
    (by rw [fr.card_L]; exact card_le_of_isPGroup_two hR2 hd)).symm

theorem conj_t_not_mem_Q (h : Hyp fr) {a : G} (ha : a ∈ normalizer (fr.N : Set G)) :
    a⁻¹ * fr.t * a ∉ fr.Q := by
  intro hQ
  have h2 : orderOf (a⁻¹ * fr.t * a) = 2 := by
    rw [show a⁻¹ * fr.t * a = a⁻¹ * fr.t * a⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq, fr.orderOf_t]
  have hz := fr.eq_z_of_mem_Q _ hQ h2
  obtain ⟨x, hxA, hxP⟩ := IsConcreteLE.not_le_iff_exists.mp h.p10.not_At_le
  rw [Subgroup.mem_centralizer_iff] at hxP
  push Not at hxP
  obtain ⟨p, hp, hpx⟩ := hxP
  have hmem : ∀ w ∈ fr.N ⊓ centralizer ({fr.t} : Set G), a⁻¹ * w * a ∈ fr.E := by
    intro w hw
    obtain ⟨hwN, hwt⟩ := Subgroup.mem_inf.mp hw
    rw [← h.p11.N_inf_centralizer_z]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) w).mp hwN
      rwa [inv_inv] at this
    · rw [Subgroup.mem_centralizer_singleton_iff] at hwt ⊢
      rw [← hz]
      calc a⁻¹ * w * a * (a⁻¹ * fr.t * a) = a⁻¹ * (w * fr.t) * a := by group
        _ = a⁻¹ * (fr.t * w) * a := by rw [hwt]
        _ = a⁻¹ * fr.t * a * (a⁻¹ * w * a) := by group
  have hxN : x ∈ fr.N ⊓ centralizer ({fr.t} : Set G) :=
    Subgroup.mem_inf.mpr ⟨h.M_le_N (Subgroup.mem_inf.mp hxA).1, (Subgroup.mem_inf.mp hxA).2⟩
  have hpN : p ∈ fr.N ⊓ centralizer ({fr.t} : Set G) := by
    rw [← fr.E_inf_centralizer_t] at hp
    exact Subgroup.mem_inf.mpr ⟨h.E_le_N (Subgroup.mem_inf.mp hp).1, (Subgroup.mem_inf.mp hp).2⟩
  have hc := fr.E_comm _ (hmem p hpN) _ (hmem x hxN)
  apply hpx
  calc p * x = a * ((a⁻¹ * p * a) * (a⁻¹ * x * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * x * a) * (a⁻¹ * p * a)) * a⁻¹ := by rw [hc]
    _ = x * p := by group

theorem card_U_inf_t_eq_tz (h : Hyp fr) :
    Nat.card (fr.U ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) =
      Nat.card (fr.U ⊓ centralizer ({fr.t} : Set G) : Subgroup G) := by
  rw [← h.ℓ_sq_conj_t]
  exact card_inf_centralizer_conj (h.V_le_normalizer_U h.ℓ_sq_mem_normalizer_N) _

theorem bw (h : Hyp fr) {W : Subgroup G} (htW : fr.t ∈ normalizer (W : Set G))
    (hzW : z ∈ normalizer (W : Set G)) (hW : Odd (Nat.card W)) :
    Nat.card W * Nat.card (W ⊓ centralizer ({fr.t} : Set G) ⊓ centralizer ({z} : Set G) :
      Subgroup G) ^ 2 =
    Nat.card (W ⊓ centralizer ({fr.t} : Set G) : Subgroup G) *
      Nat.card (W ⊓ centralizer ({z} : Set G) : Subgroup G) *
      Nat.card (W ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) :=
  CFSG.Walter.J1.card_mul_card_sq_eq_mul h.t_mul_t h.z_mul_z h.t_ne_one h.z_ne_one fr.t_ne
    h.t_comm_z W htW hzW hW

theorem card_P₂ (_h : Hyp fr) : Nat.card fr.P₂ = 3 := by
  rw [fr.P₂_eq, Nat.card_zpowers, fr.orderOf_s₂]

theorem inf_t_inf_z_eq (_h : Hyp fr) {W : Subgroup G}
    (hW : W ⊓ centralizer ({z} : Set G) = fr.E) :
    W ⊓ centralizer ({fr.t} : Set G) ⊓ centralizer ({z} : Set G) = fr.P₂ := by
  rw [inf_right_comm, hW, fr.E_inf_centralizer_t]

theorem arith_quaternion {a b d : ℕ} (ha7 : 7 ≤ a) (ha9 : a ≤ 9) (ha : a ≠ 9) (hb3 : 3 ≤ b)
    (hba : b ≤ a) (hd : d ∣ 1296) (heq : 3 ^ 9 * 8 * 3 ^ b = d * 3 ^ a) : a = 8 ∧ b = 3 := by
  have hd' := Nat.le_of_dvd (by norm_num) hd
  interval_cases a <;> interval_cases b <;> omega

theorem card_U (h : Hyp fr) : Nat.card fr.U = 3 ^ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := normalizer (fr.N : Set G)
  obtain ⟨a, ha9, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h.card_U_dvd
  have ha7 : 7 ≤ a := by
    have h7 : 3 ^ 7 ∣ 3 ^ a := ha ▸ h.p11.card_N ▸ Subgroup.card_dvd_of_le h.N_le_U
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h7
  by_contra hne
  have ha9' : a ≠ 9 := fun h9 => hne (h9 ▸ ha)
  obtain ⟨X₀, hX₀V, hX₀n, hX₀card, htX₀, -, -⟩ := CFSG.Quasithin.thompson_transfer_index_two_sub
    V fr.L fr.Q h.L_le_normalizer_N h.isPGroup_L h.eq_L_of_le
    (by
      have := Subgroup.relIndex_mul_card fr.Q fr.L
      rw [inf_of_le_left h.Q_le_L, h.card_Q, fr.card_L] at this
      omega)
    h.t_mul_t h.t_mem_L fun a ha => h.conj_t_not_mem_Q ha
  have hVX₀ : V ≤ normalizer (X₀ : Set G) := fun x hx =>
    CFSG.Walter.J1.mem_normalizer_of_conj_mem fun w hw => hX₀n x hx w hw
  have hX₀c : Nat.card X₀ = 3 ^ 9 * 8 := by
    rw [h.card_normalizer_N] at hX₀card
    omega
  have hUX₀ : fr.U ≤ X₀ :=
    le_of_odd_of_card_eq_two_mul hX₀V hVX₀ hX₀card h.U_le_V h.odd_card_U
  have hLX : ¬ fr.L ≤ X₀ := fun hle => htX₀ (hle h.t_mem_L)
  have hL8 : Nat.card (fr.L ⊓ X₀ : Subgroup G) = 8 := by
    have := card_eq_two_mul_inf hX₀V hVX₀ hX₀card h.L_le_normalizer_N hLX
    rw [fr.card_L] at this
    omega
  have hsyl : IsSylowOf X₀ 2 (fr.L ⊓ X₀) := by
    refine isSylowOf_of_forall_card_le inf_le_right (h.isPGroup_L.to_le inf_le_left) ?_
    intro B hB hB2
    rw [hL8]
    exact card_le_of_isPGroup_two hB2 (b := 3) (a := 9)
      (by rw [show (3 : ℕ) ^ 9 * 2 ^ 3 = 3 ^ 9 * 8 by norm_num, ← hX₀c]
          exact Subgroup.card_dvd_of_le hB)
  have hO : oddCoreOf X₀ ≤ fr.U := by
    refine le_oddCoreOf ((oddCoreOf_le X₀).trans hX₀V) (fun g hg => ?_) (odd_card_oddCoreOf X₀)
    exact mem_normalizer_oddCoreOf (hVX₀ hg)
  rcases fr.eq_of_le_L _ inf_le_left hL8 (fun ht => htX₀ (Subgroup.mem_inf.mp ht).2) with
    hL₁ | hQ
  ·
    rw [hL₁] at hsyl hL8
    have hcyc : IsCyclic fr.L₁ := by rw [fr.L₁_eq]; infer_instance
    have h1 := card_oddCoreOf_mul_of_isCyclic hsyl hcyc (by rw [hL8]; norm_num)
    rw [hL8, hX₀c] at h1
    have h2 : Nat.card (oddCoreOf X₀) = 3 ^ 9 := by omega
    have h3 := Subgroup.card_le_of_le hO
    rw [h2, ha] at h3
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h3
    omega
  ·
    rw [hQ] at hsyl
    have hBS := exists_mul_oddCoreOf_of_quaternion h.set.orderOf_z hsyl h.z_mem_Q fr.Q_quaternion
    set D := X₀ ⊓ centralizer ({z} : Set G)
    have hDV : D ≤ V ⊓ centralizer ({z} : Set G) := inf_le_inf_right _ hX₀V
    have hDU : D ≤ normalizer (fr.U : Set G) := (inf_le_left.trans hX₀V).trans h.V_le_normalizer_U
    have hsup : D ⊔ fr.U = X₀ := by
      refine le_antisymm (sup_le inf_le_left hUX₀) fun g hg => ?_
      obtain ⟨c, hc, k, hk, rfl⟩ := hBS g hg
      exact Subgroup.mul_mem_sup hc (hO hk)
    have hinf : D ⊓ fr.U = fr.U ⊓ centralizer ({z} : Set G) := by
      refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨hxD, hxU⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr ⟨hxU, (Subgroup.mem_inf.mp hxD).2⟩
      · obtain ⟨hxU, hxz⟩ := Subgroup.mem_inf.mp hx
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hUX₀ hxU, hxz⟩, hxU⟩
    have hprod := card_sup_mul_card_inf hDU
    rw [hsup, hinf, hX₀c, ha] at hprod
    obtain ⟨b, hba, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (ha ▸ Subgroup.card_dvd_of_le (inf_le_left : fr.U ⊓ centralizer ({z} : Set G) ≤ fr.U))
    have hEUz : fr.E ≤ fr.U ⊓ centralizer ({z} : Set G) := by
      rw [← h.p11.N_inf_centralizer_z]
      exact inf_le_inf_right _ h.N_le_U
    have hb3 : 3 ≤ b := by
      have h27 : 3 ^ 3 ∣ 3 ^ b := by
        have := Subgroup.card_dvd_of_le hEUz
        rw [fr.card_E, hb] at this
        simpa using this
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h27
    rw [hb] at hprod
    obtain ⟨rfl, rfl⟩ := arith_quaternion ha7 ha9 ha9' hb3 hba (h.card_dvd_of_le_V_H hDV) hprod
    have hUz : fr.U ⊓ centralizer ({z} : Set G) = fr.E :=
      (Subgroup.eq_of_le_of_card_ge hEUz (by rw [hb, fr.card_E]; all_goals norm_num)).symm
    have hbw := h.bw h.t_mem_normalizer_U h.z_mem_normalizer_U h.odd_card_U
    rw [h.inf_t_inf_z_eq hUz, h.card_P₂, hUz, fr.card_E, h.card_U_inf_t_eq_tz, ha] at hbw
    obtain ⟨e, he, hxe⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (ha ▸ Subgroup.card_dvd_of_le (inf_le_left : fr.U ⊓ centralizer ({fr.t} : Set G) ≤ fr.U))
    rw [hxe] at hbw
    interval_cases e <;> omega

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
