module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR8C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise commutatorElement

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_card_O_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    Nat.card (l41O2 t x₁ x₂) = 2 * Nat.card (l41R t x₁ x₂ rho) := by
  have h1 := Subgroup.relIndex_mul_card (H := l41R t x₁ x₂ rho) (K := l41O2 t x₁ x₂)
  rw [inf_eq_left.mpr (n4_R_le_O h.toL41GPh1), (n4_R_main h).1] at h1
  omega

theorem n4_O2_eq_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    l41O2 t x₁ x₂ = l41R t x₁ x₂ rho ⊔ zpowers t := by
  have hRO := n4_R_le_O h.toL41GPh1
  have htO := n4_t_mem_O h.toL41GPh3
  have htR := (n4_R_main h).2
  have hle : l41R t x₁ x₂ rho ⊔ zpowers t ≤ l41O2 t x₁ x₂ :=
    sup_le hRO (Subgroup.zpowers_le.mpr htO)
  have hcard := n4_card_O_R h
  have hdvd1 : Nat.card (l41R t x₁ x₂ rho) ∣ Nat.card ↥(l41R t x₁ x₂ rho ⊔ zpowers t) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hdvd2 : Nat.card ↥(l41R t x₁ x₂ rho ⊔ zpowers t) ∣ Nat.card (l41O2 t x₁ x₂) :=
    Subgroup.card_dvd_of_le hle
  obtain ⟨m, hm⟩ := hdvd1
  have hRpos : 0 < Nat.card (l41R t x₁ x₂ rho) := Nat.card_pos
  have hmdvd : m ∣ 2 := by
    rw [hm, hcard, mul_comm 2] at hdvd2
    exact Nat.dvd_of_mul_dvd_mul_left hRpos hdvd2
  have hm2 : m ≤ 2 := Nat.le_of_dvd (by norm_num) hmdvd
  have hmpos : 0 < Nat.card ↥(l41R t x₁ x₂ rho ⊔ zpowers t) := Nat.card_pos
  symm
  interval_cases m
  · omega
  · exfalso
    have hEq : l41R t x₁ x₂ rho = l41R t x₁ x₂ rho ⊔ zpowers t :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    apply htR
    rw [hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  · exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem n4_conj_R_le (h : L41GPh1 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ l41N t x₁ x₂)
    (hgρ : g * rho * g⁻¹ ∈ zpowers rho) :
    ∀ x ∈ l41R t x₁ x₂ rho, g * x * g⁻¹ ∈ l41R t x₁ x₂ rho := by
  have hmap := Subgroup.map_commutator (l41O2 t x₁ x₂) (zpowers rho) (MulAut.conj g).toMonoidHom
  have hle : (l41R t x₁ x₂ rho).map (MulAut.conj g).toMonoidHom ≤ l41R t x₁ x₂ rho := by
    rw [l41R, hmap]
    refine Subgroup.commutator_mono ?_ ?_
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
      exact pCoreOf_two_conj_mem hg hq
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      have e : (MulAut.conj g).toMonoidHom (rho ^ k) = (g * rho * g⁻¹) ^ k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_zpow]
      rw [e]
      exact Subgroup.zpow_mem _ hgρ k
  intro x hx
  exact hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

theorem n4_normal_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    NormalIn (l41R t x₁ x₂ rho) (l41N t x₁ x₂) := by
  have hRO := n4_R_le_O h.toL41GPh1
  have hρN : rho ∈ l41N t x₁ x₂ := n4_rho_mem_N h.toL41GPh1
  have hlamN : lam ∈ l41N t x₁ x₂ :=
    n4_K_le_N h.toL41GPh1 (Subgroup.subset_closure (by simp))
  refine ⟨hRO.trans (pCoreOf_two_le _), fun g hg k hk => ?_⟩
  have hO : l41O2 t x₁ x₂ ≤ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
    intro o ho
    refine mem_normalizer_of_conj_mem fun r hr => ?_
    have hc := n4_O_comm h.toL41GPh6 ho (hRO hr)
    have e : o * r * o⁻¹ = (o * r * o⁻¹ * r⁻¹) * r := by group
    rw [e]
    exact Subgroup.mul_mem _ (n4_four_le_R h.toL41GPh3 hc) hr
  have hK : closure ({rho, lam} : Set G) ≤
      normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine mem_normalizer_of_conj_mem (n4_conj_R_le h.toL41GPh1 hρN ?_)
      have e : g * g * g⁻¹ = g := by group
      rw [e]
      exact Subgroup.mem_zpowers g
    · refine mem_normalizer_of_conj_mem (n4_conj_R_le h.toL41GPh1 hlamN ?_)
      rw [h.lam_rho]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers rho)
  have hN : l41N t x₁ x₂ ≤ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [n4_N_eq h.toL41GPh3]
    exact sup_le hO hK
  exact (Subgroup.mem_normalizer_iff.mp (hN hg) k).mp hk

theorem n4_cent_rho_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    l41R t x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨hrR, hrC⟩ := Subgroup.mem_inf.mp hr
  have hmem : r ∈ l41O2 t x₁ x₂ ⊓ centralizer ({rho} : Set G) :=
    ⟨n4_R_le_O h.toL41GPh1 hrR, hrC⟩
  rw [h.nbar.cent_O2_rho] at hmem
  rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hmem with h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · exfalso
    rw [h1] at hrR
    exact (n4_R_main h).2 hrR

theorem n4_cent_t_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    l41R t x₁ x₂ rho ⊓ invCent t = baseGrp x₁ x₂ := by
  have hP : twoCore t = zpowers t := h.p2
  apply le_antisymm
  · intro r hr
    obtain ⟨hrR, hrt⟩ := Subgroup.mem_inf.mp hr
    have hrO : r ∈ l41O2 t x₁ x₂ := n4_R_le_O h.toL41GPh1 hrR
    have hrW : r ∈ ctxW t x₁ x₂ :=
      n4_O2_cent_t h.toL41GPh3 hrO (n4_conj_eq_of_comm (mem_invCent_iff.mp hrt).symm)
    obtain ⟨p, hp, b, hb, rfl⟩ := (mem_sup_iff_of_commute (pt_comm_base h.toCtx0)).mp hrW
    have hbR : b ∈ l41R t x₁ x₂ rho := n4_base_le_R h.toL41GPh3 hb
    have hpR : p ∈ l41R t x₁ x₂ rho := by
      have := Subgroup.mul_mem _ hrR (Subgroup.inv_mem _ hbR)
      rwa [mul_inv_cancel_right] at this
    rw [hP] at hp
    rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
    · rw [h1, one_mul]
      exact hb
    · exfalso
      rw [h1] at hpR
      exact (n4_R_main h).2 hpR
  · exact le_inf (n4_base_le_R h.toL41GPh3) fun b hb =>
      L_le_invCent h.hyp (pt_base_le_L h.toCtx0 hb)

theorem n4_N_decomp (h : L41GPh3 t L S x₁ x₂ lam rho) {n : G} (hn : n ∈ l41N t x₁ x₂) :
    ∃ o ∈ l41O2 t x₁ x₂, ∃ k ∈ closure ({rho, lam} : Set G), n = o * k := by
  have hK : closure ({rho, lam} : Set G) ≤ normalizer ((l41O2 t x₁ x₂ : Subgroup G) : Set G) :=
    fun k hk => mem_normalizer_of_conj_mem fun q hq =>
      pCoreOf_two_conj_mem (n4_K_le_N h.toL41GPh1 hk) hq
  have hn' : n ∈ ((l41O2 t x₁ x₂ ⊔ closure ({rho, lam} : Set G) : Subgroup G) : Set G) := by
    rw [← n4_N_eq h]
    exact hn
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hK] at hn'
  obtain ⟨o, ho, k, hk, rfl⟩ := Set.mem_mul.mp hn'
  exact ⟨o, ho, k, hk, rfl⟩

theorem n4_orbit_t_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    conjIn (l41R t x₁ x₂ rho) t = t • (fourGrp x₁ x₂ : Set G) := by
  have hRO := n4_R_le_O h.toL41GPh1
  have hNR := n4_normal_R h
  have htN : t ∈ l41N t x₁ x₂ := pCoreOf_two_le _ (n4_t_mem_O h.toL41GPh3)
  apply Set.Subset.antisymm
  · rintro u ⟨k, hk, rfl⟩
    have hmem : k * t * k⁻¹ ∈ conjIn (l41N t x₁ x₂) t :=
      ⟨k, pCoreOf_two_le _ (hRO hk), rfl⟩
    rwa [h.normalizerFacts.orbit_t] at hmem
  · intro x hx
    rw [← h.normalizerFacts.orbit_t] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    obtain ⟨o, ho, k, hk, rfl⟩ := n4_N_decomp h.toL41GPh3 hn
    have hzN : zpowers t ≤ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
      intro p hp
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
      exact mem_normalizer_of_conj_mem fun r hr =>
        hNR.2 _ (Subgroup.zpow_mem _ htN j) r hr
    have ho' : o ∈ ((l41R t x₁ x₂ rho ⊔ zpowers t : Subgroup G) : Set G) := by
      rw [← n4_O2_eq_R h]
      exact ho
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at ho'
    obtain ⟨r, hr, p, hp, rfl⟩ := Set.mem_mul.mp ho'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    refine ⟨r, hr, ?_⟩
    have hkt : k * t * k⁻¹ = t := n4_K_fix_t h.toCtx0 hk
    have hjt : t ^ j * t = t * t ^ j := (Commute.refl t).zpow_left j |>.eq
    calc r * t * r⁻¹ = r * (t ^ j * t * (t ^ j)⁻¹) * r⁻¹ := by
          rw [hjt]
          group
      _ = r * t ^ j * (k * t * k⁻¹) * (t ^ j)⁻¹ * r⁻¹ := by rw [hkt]; group
      _ = r * t ^ j * k * t * (r * t ^ j * k)⁻¹ := by group

theorem n4_V_eq_R (h : L41GPh7 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ = l41R t x₁ x₂ rho ⊔ closure ({t, lam} : Set G) := by
  have hP : twoCore t = zpowers t := h.p2
  have hRO := n4_R_le_O h.toL41GPh1
  have htS : t ∈ S := by
    rw [h.basic.S_eq]
    exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  have hlamS : lam ∈ S := n4_lam_mem_S h.toCtx0
  have hztc : zpowers t ≤ closure ({t, lam} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hlamc : lam ∈ closure ({t, lam} : Set G) := Subgroup.subset_closure (by simp)
  have hx₁ : x₁ ∈ l41R t x₁ x₂ rho :=
    n4_base_le_R h.toL41GPh3 (Subgroup.subset_closure (by simp))
  have hx₂ : x₂ ∈ l41R t x₁ x₂ rho :=
    n4_base_le_R h.toL41GPh3 (Subgroup.subset_closure (by simp))
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [n4_O2_eq_R h]
      exact sup_le_sup_left hztc _
    · rw [h.basic.S_eq, hP]
      refine sup_le (hztc.trans le_sup_right) ?_
      refine (Subgroup.closure_le (K := l41R t x₁ x₂ rho ⊔ closure ({t, lam} : Set G))).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left hx₁
      · exact Subgroup.mem_sup_left hx₂
      · exact Subgroup.mem_sup_right hlamc
  · refine sup_le (hRO.trans le_sup_left) ?_
    refine (Subgroup.closure_le (K := l41V S t x₁ x₂)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.mem_sup_right htS
    · exact Subgroup.mem_sup_right hlamS

theorem l41_r_of (h : L41GPh7 t L S x₁ x₂ lam rho) : L41RFacts t S x₁ x₂ lam rho where
  card_R := n4_card_R h
  normal_R := n4_normal_R h
  t_not_mem := (n4_R_main h).2
  O2_eq := n4_O2_eq_R h
  cent_rho := n4_cent_rho_R h
  cent_t := n4_cent_t_R h
  orbit_t := n4_orbit_t_R h
  fourGrp_le := n4_four_le_R h.toL41GPh3
  fourGrp_central := by
    intro f hf r hr
    have hrO := n4_R_le_O h.toL41GPh1 hr
    rw [n4_O2_eq h.toL41GPh3] at hrO
    exact (Subgroup.mem_centralizer_iff.mp hrO.2) f hf
  comm_le :=
    Subgroup.commutator_le.mpr fun a ha b hb =>
      n4_O_comm h.toL41GPh6 (n4_R_le_O h.toL41GPh1 ha) (n4_R_le_O h.toL41GPh1 hb)
  sq_mem := fun r hr => n4_O_sq h.toL41GPh6 (n4_R_le_O h.toL41GPh1 hr)
  V_eq := n4_V_eq_R h

end S4A

theorem l41_r_holds : L41RStmt :=
  fun h => S4A.l41_r_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
