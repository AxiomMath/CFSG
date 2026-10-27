module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveR
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveS

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Hyp

variable {fr : JankoFrame G z} {m : G}

theorem S_le_U (h : Hyp fr) : fr.S ≤ fr.U := h.center_U ▸ inf_le_left

theorem zpowers_m_inf_U (h : Hyp fr) (hmK : m ∈ fr.K) : zpowers m ⊓ fr.U = ⊥ := by
  rw [eq_bot_iff, ← h.U_inf_K, inf_comm]
  exact inf_le_inf_left _ (Subgroup.zpowers_le.mpr hmK)

theorem card_R (h : Hyp fr) (hmK : m ∈ fr.K) (hm3 : orderOf m = 3) :
    Nat.card (fr.R m) = 3 ^ 10 := by
  rw [JankoFrame.R, sup_comm, card_sup_of_inf_eq_bot
    (Subgroup.zpowers_le.mpr (h.K_le_normalizer_U hmK)) (h.zpowers_m_inf_U hmK),
    Nat.card_zpowers, hm3, h.card_U]
  ring

theorem isPGroup_R (h : Hyp fr) (hmK : m ∈ fr.K) (hm3 : orderOf m = 3) :
    IsPGroup 3 (fr.R m) := IsPGroup.of_card (h.card_R hmK hm3)

theorem U_le_R (_h : Hyp fr) : fr.U ≤ fr.R m := le_sup_left

theorem m_mem_R (_h : Hyp fr) : m ∈ fr.R m := (le_sup_right : zpowers m ≤ fr.R m) (mem_zpowers m)

theorem R_le_centralizer_P3bar (h : Hyp fr) (hmP : m ∈ centralizer (fr.P3bar : Set G)) :
    fr.R m ≤ centralizer (fr.P3bar : Set G) := by
  refine sup_le ?_ (Subgroup.zpowers_le.mpr hmP)
  rw [← h.centralizer_S]
  exact Subgroup.centralizer_le fun x hx => (le_sup_left : fr.P3bar ≤ fr.S) hx

theorem S_inf_centralizer_m (h : Hyp fr) (hmK : m ∈ fr.K) (hm3 : orderOf m = 3)
    (hmP : m ∈ centralizer (fr.P3bar : Set G)) :
    fr.S ⊓ centralizer ({m} : Set G) = fr.P3bar := by
  have hle : fr.P3bar ≤ fr.S ⊓ centralizer ({m} : Set G) :=
    le_inf le_sup_left fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hmP x hx)
  have h3 : 3 ∣ Nat.card (fr.S ⊓ centralizer ({m} : Set G) : Subgroup G) :=
    h.p11.card_P3bar ▸ Subgroup.card_dvd_of_le hle
  have h9 : Nat.card (fr.S ⊓ centralizer ({m} : Set G) : Subgroup G) ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : fr.S ⊓ centralizer ({m} : Set G) ≤ fr.S)
    rwa [h.card_S] at this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
  have hk1 : k = 1 := by
    interval_cases k
    · rw [pow_zero] at hk'
      rw [hk'] at h3
      exact absurd h3 (by norm_num)
    · rfl
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left : fr.S ⊓ centralizer ({m} : Set G) ≤
        fr.S) (by rw [hk', h.card_S]; all_goals norm_num)
      have hm1 := h.eq_one_of_le_centralizer hmK (heq ▸ inf_le_right)
      rw [hm1, orderOf_one] at hm3
      exact absurd hm3 (by norm_num)
  subst hk1
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hk', h.p11.card_P3bar]; all_goals norm_num)).symm

theorem center_R (h : Hyp fr) (hmK : m ∈ fr.K) (hm3 : orderOf m = 3)
    (hmP : m ∈ centralizer (fr.P3bar : Set G)) :
    fr.R m ⊓ centralizer (fr.R m : Set G) = fr.P3bar := by
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ ?_)
  · have hxC := (Subgroup.mem_inf.mp hx).2
    rw [← h.S_inf_centralizer_m hmK hm3 hmP]
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hxC m h.m_mem_R).symm⟩
    rw [← h.centralizer_U]
    exact Subgroup.centralizer_le (fun u hu => h.U_le_R hu) hxC
  · exact (le_sup_left : fr.P3bar ≤ fr.S).trans (h.S_le_U.trans h.U_le_R)
  · exact Subgroup.le_centralizer_iff.mp (h.R_le_centralizer_P3bar hmP)

theorem z_mem_normalizer_R (h : Hyp fr) (hmK : m ∈ fr.K) : z ∈ normalizer (fr.R m : Set G) := by
  refine mem_normalizer_sup h.z_mem_normalizer_U ?_
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [centralizer_zpowers, Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_singleton_iff.mp (fr.K_le hmK)).symm

theorem t_mem_normalizer_R (h : Hyp fr) (htm : fr.t * m * fr.t⁻¹ = m⁻¹) :
    fr.t ∈ normalizer (fr.R m : Set G) :=
  mem_normalizer_sup h.t_mem_normalizer_U (h.t_mem_normalizer_zpowers htm)

theorem t_mem_Vfour (_h : Hyp fr) : fr.t ∈ fr.V := by
  rw [fr.V_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem z_mem_Vfour (_h : Hyp fr) : z ∈ fr.V := by
  rw [fr.V_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem normalizer_P3bar (h : Hyp fr) (hmK : m ∈ fr.K) (hm3 : orderOf m = 3)
    (hmP : m ∈ centralizer (fr.P3bar : Set G)) (htm : fr.t * m * fr.t⁻¹ = m⁻¹) :
    normalizer (fr.P3bar : Set G) = fr.R m ⊔ fr.V := by
  obtain ⟨y, hyP, hy3⟩ := h.exists_P3bar_eq
  have hy : y ∈ fr.P3bar := hyP ▸ Subgroup.mem_zpowers y
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  have hyS : y ∈ fr.S := (le_sup_left : fr.P3bar ≤ fr.S) hy
  have hys : IsConj y fr.s₃ := h.isConj_s₃_of_mem_S hyS hy1
  have hyt : y ∈ centralizer ({fr.t} : Set G) := (Subgroup.mem_inf.mp hy).2
  set C₃ := centralizer ({y} : Set G)
  set W₃ := oddCoreOf C₃
  have htC : fr.t ∈ C₃ := h.t_mem_centralizer_of_mem_P3bar hy
  have hC₃ : Nat.card C₃ = 2 * Nat.card W₃ := h.card_centralizer_eq_two_mul hys fr.orderOf_t htC
  have hCP : centralizer (fr.P3bar : Set G) = C₃ := by rw [hyP, centralizer_zpowers]
  have hRC : fr.R m ≤ C₃ := hCP ▸ h.R_le_centralizer_P3bar hmP
  have hRodd : Odd (Nat.card (fr.R m)) := by rw [h.card_R hmK hm3]; decide
  have hRW : fr.R m ≤ W₃ := le_oddCoreOf_of_card hC₃ hRC hRodd
  have htW : fr.t ∈ normalizer (W₃ : Set G) := le_normalizer_oddCoreOf C₃ htC
  have hzN : z ∈ normalizer (fr.P3bar : Set G) := h.z_mem_normalizer_P3bar
  have hzW : z ∈ normalizer (W₃ : Set G) := by
    refine mem_normalizer_oddCoreOf ?_
    have := mem_normalizer_centralizer hzN
    rwa [hCP] at this
  have hWodd : Odd (Nat.card W₃) := odd_card_oddCoreOf C₃
  have hbw := h.bw htW hzW hWodd
  have h162 := (h.p7.isConj_s₃_iff fr.t fr.orderOf_t y hyt
    (h.pow_three_of_mem_M (h.S_le_M hyS))).mp hys
  have c1 : Nat.card (W₃ ⊓ centralizer ({fr.t} : Set G) : Subgroup G) ≤ 81 := by
    have hd : Nat.card (W₃ ⊓ centralizer ({fr.t} : Set G) : Subgroup G) ∣ 2 * 81 := by
      rw [show (2 : ℕ) * 81 = 162 by norm_num, ← h162]
      exact Subgroup.card_dvd_of_le (inf_le_inf_right _ (oddCoreOf_le C₃))
    have hodd := Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_le
      (inf_le_left : W₃ ⊓ centralizer ({fr.t} : Set G) ≤ W₃))
    exact Nat.le_of_dvd (by norm_num) ((Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left hd)
  have hEm : fr.E ⊔ zpowers m ≤ W₃ ⊓ centralizer ({z} : Set G) := by
    refine sup_le (le_inf (((h.E_le_N.trans h.N_le_U).trans h.U_le_R).trans hRW) fr.E_le) ?_
    exact le_inf ((le_sup_right : zpowers m ≤ fr.R m).trans hRW)
      (Subgroup.zpowers_le.mpr (fr.K_le hmK))
  have hEmc : Nat.card (fr.E ⊔ zpowers m : Subgroup G) = 81 := by
    have hb : zpowers m ⊓ fr.E = ⊥ := by
      rw [eq_bot_iff, ← fr.E_inf_K, inf_comm]
      exact inf_le_inf_left _ (Subgroup.zpowers_le.mpr hmK)
    rw [sup_comm, card_sup_of_inf_eq_bot (Subgroup.zpowers_le.mpr (fr.K_le_normalizer hmK)) hb,
      Nat.card_zpowers, hm3, fr.card_E]
  have c2 : Nat.card (W₃ ⊓ centralizer ({z} : Set G) : Subgroup G) = 81 :=
    fr.card_eq_of_odd _ inf_le_right (Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_le inf_le_left))
      (hEmc ▸ Subgroup.card_dvd_of_le hEm)
  obtain ⟨fr'⟩ := h.frs (fr.t * z) h.orderOf_tz
  have c3 : Nat.card (W₃ ⊓ centralizer ({fr.t * z} : Set G) : Subgroup G) = 81 := by
    refine fr'.card_eq_of_odd _ inf_le_right
      (Odd.of_dvd_nat hWodd (Subgroup.card_dvd_of_le inf_le_left)) ?_
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num, ← h.card_U_inf_tz]
    exact Subgroup.card_dvd_of_le (inf_le_inf_right _ (h.U_le_R.trans hRW))
  have c0 : 3 ≤ Nat.card (W₃ ⊓ centralizer ({fr.t} : Set G) ⊓ centralizer ({z} : Set G) :
      Subgroup G) := by
    rw [← h.card_P₂]
    refine Subgroup.card_le_of_le (le_inf (le_inf ?_ ?_) ?_)
    · exact ((h.P₂_le_E.trans (h.E_le_N.trans h.N_le_U)).trans h.U_le_R).trans hRW
    · rw [← fr.E_inf_centralizer_t]
      exact inf_le_right
    · exact h.P₂_le_E.trans fr.E_le
  have hW10 : Nat.card W₃ ≤ 3 ^ 10 := by
    have h1 : Nat.card W₃ * 3 ^ 2 ≤ Nat.card W₃ * Nat.card (W₃ ⊓ centralizer ({fr.t} : Set G) ⊓
        centralizer ({z} : Set G) : Subgroup G) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left c0 2)
    rw [hbw, c2, c3] at h1
    have h2 := Nat.mul_le_mul_right 81 (Nat.mul_le_mul_right 81 c1)
    norm_num at h1 h2 ⊢
    omega
  have hWR : W₃ = fr.R m :=
    (Subgroup.eq_of_le_of_card_ge hRW (by rw [h.card_R hmK hm3]; exact hW10)).symm
  have htR : zpowers fr.t ≤ normalizer (fr.R m : Set G) :=
    Subgroup.zpowers_le.mpr (h.t_mem_normalizer_R htm)
  have htRb : zpowers fr.t ⊓ fr.R m = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
    (by rw [Nat.card_zpowers, fr.orderOf_t, h.card_R hmK hm3]; norm_num))
  have hC₃eq : C₃ = fr.R m ⊔ zpowers fr.t := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hRC (Subgroup.zpowers_le.mpr htC)) ?_).symm
    rw [sup_comm, card_sup_of_inf_eq_bot htR htRb, Nat.card_zpowers, fr.orderOf_t, hC₃, hWR]
  have hC₃V : C₃ ≤ fr.R m ⊔ fr.V := by
    rw [hC₃eq]
    exact sup_le_sup_left (Subgroup.zpowers_le.mpr h.t_mem_Vfour) _
  refine le_antisymm (fun g hg => ?_) (sup_le ?_ ?_)
  · rw [hyP] at hg
    rcases conj_eq_or_eq_inv hy3 hg with h1 | h1
    · refine hC₃V (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      calc g * y = g * y * g⁻¹ * g := by group
        _ = y * g := by rw [h1]
    · have hzy := h.z_inv_of_mem_S hyS
      have hgz : g * z ∈ C₃ := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : g * z * y * (g * z)⁻¹ = y := by
          calc g * z * y * (g * z)⁻¹ = g * (z * y * z⁻¹) * g⁻¹ := by group
            _ = (g * y * g⁻¹)⁻¹ := by rw [hzy]; group
            _ = y := by rw [h1, inv_inv]
        calc g * z * y = g * z * y * (g * z)⁻¹ * (g * z) := by group
          _ = y * (g * z) := by rw [hc]
      have := mul_mem (hC₃V hgz) ((le_sup_right : fr.V ≤ fr.R m ⊔ fr.V) (inv_mem h.z_mem_Vfour))
      rwa [mul_inv_cancel_right] at this
  · exact (h.R_le_centralizer_P3bar hmP).trans (Subgroup.centralizer_le_normalizer _)
  · rw [fr.V_eq, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.centralizer_le_normalizer _ (h.t_mem_centralizer_P3bar)
    · exact hzN

theorem factorization_three (h : Hyp fr) : (Nat.card G).factorization 3 = 10 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hmK, hm3, -, -⟩ := h.exists_m
  obtain ⟨R', hRR'⟩ := (h.isPGroup_R hmK hm3).exists_le_sylow
  have hR'1 : (R' : Subgroup G) ≠ ⊥ := by
    intro hb
    have := Subgroup.card_le_of_le hRR'
    rw [hb, Subgroup.card_bot, h.card_R hmK hm3] at this
    exact absurd this (by norm_num)
  obtain ⟨x, -, hx1, hxC⟩ := exists_mem_ne_one_mem_centralizer R'.isPGroup' le_rfl
    Subgroup.le_normalizer hR'1
  have hxS : x ∈ fr.S := by
    rw [← h.centralizer_U]
    exact Subgroup.centralizer_le (fun u hu => hRR' (h.U_le_R hu)) hxC
  have hR'C : (R' : Subgroup G) ≤ normalizer ((zpowers x : Subgroup G) : Set G) := by
    intro g hg
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [centralizer_zpowers, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxC g hg
  have hle := h.card_le_of_isConj_s₃ (h.isConj_s₃_of_mem_S hxS hx1) hR'C R'.isPGroup'
  have hge := Subgroup.card_le_of_le hRR'
  rw [Sylow.card_eq_multiplicity] at hle hge
  rw [h.card_R hmK hm3] at hge
  have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hle
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hge
  omega

theorem exists_choiceM (h : Hyp fr) : ∃ m : G, JankoChoiceM fr m := by
  obtain ⟨m, hmK, hm3, hmP, htm⟩ := h.exists_m
  exact ⟨m, hmK, hm3, hmP, htm, h.card_R hmK hm3, h.center_R hmK hm3 hmP,
    h.normalizer_P3bar hmK hm3 hmP htm⟩

end Hyp

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
