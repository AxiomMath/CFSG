module

public import CFSG.CGT.Timmesfeld75.Sec4Two
public import CFSG.CGT.Timmesfeld75.Sec4SixAux
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise
open CFSG.BenderSuzuki (PSU3Model)

section Card

variable {G : Type*} [Group G]

theorem card_sup_le_of_le_normalizer {H K : Subgroup G} [Finite H] [Finite K]
    (h : H ≤ Subgroup.normalizer (K : Set G)) : Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right H K h
  let f : H × K → ↥(H ⊔ K) := fun p => ⟨(p.1 : G) * p.2,
    Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ (H : Set G) * (K : Set G) := by
      rw [← hmul]
      exact hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz'
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

end Card

section Main

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.card_sec4N_le (h : Sec4Hyp T T₁ a T₂) :
    Nat.card (sec4N T T₁ T₂) ≤ Nat.card (normIn T T₁) ^ 3 := by
  have hab := h.isElemAbelian_sec4N
  have h1 : Nat.card (cfgM T T₁) ≤ Nat.card (normIn T T₁) * Nat.card (normIn T₁ T) :=
    card_sup_le_of_le_normalizer h.sec3.cfg.normIn_le_normalizer
  have h2 : Nat.card (sec4N T T₁ T₂) ≤ Nat.card (cfgM T T₁) * Nat.card (normIn T₂ T) :=
    card_sup_le_of_le_normalizer fun x hx => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun y hy =>
        elemAbelian_mul_comm hab (normIn_le_sec4N_right hy) (cfgM_le_sec4N hx))
  rw [h.card_normIn₁] at h1
  rw [h.card_normIn₂_eq h.mem_normalizer_normIn] at h2
  calc Nat.card (sec4N T T₁ T₂) ≤ Nat.card (cfgM T T₁) * Nat.card (normIn T T₁) := h2
    _ ≤ (Nat.card (normIn T T₁) * Nat.card (normIn T T₁)) * Nat.card (normIn T T₁) :=
      Nat.mul_le_mul_right _ h1
    _ = Nat.card (normIn T T₁) ^ 3 := by ring

theorem prime_dvd_card_psu3Model {f r : ℕ} (hfr : (f = 2 ∧ r = 13) ∨ (f = 3 ∧ r = 19)) :
    r ∣ Nat.card (PSU3Model f) := by
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  have hf : 1 ≤ f := by rcases hfr with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have h := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd hf
  rw [hmodel]
  rcases hfr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · norm_num at h
    omega
  · norm_num at h
    omega

theorem Sec4Hyp.commutator_quotient_eq_top (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T)
    [((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal] :
    commutator (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) = ⊤ := by
  obtain ⟨f, hf2, hcardT, X, _, S, ι, hsimple, hpair, hTS, -⟩ :=
    h.exists_L2_embedding hq (K := sec4Y T T₁ T₂) le_rfl
  have hfinX := hpair.finite
  have hS4 : 4 ≤ Nat.card S := by
    rw [hpair.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hcl : Subgroup.normalClosure ((S.map ι : Subgroup (↥(sec4Y T T₁ T₂) ⧸
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) : Set (↥(sec4Y T T₁ T₂) ⧸
        (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) = ⊤ := by
    rw [← hTS]
    exact normalClosure_img_eq_top h.normalClosure_sec4Y
  exact commutator_eq_top_of_transitive ι hS4
    (fun x hx hx1 y hy hy1 => hpair.transitive hx hx1 hy hy1) hcl

theorem Sec4Hyp.false_of_card_sixteen
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T = 16) : False := by
  have hN : ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal := h.normal_sec4N
  obtain ⟨-, f, hf2, hcardT, hNormal, ⟨e⟩⟩ := h.sec4_two hAsc hq
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hL2 : 2 ≤ Nat.card (normIn T T₁) := (Subgroup.one_lt_card_iff_ne_bot _).2 h.sec3.cfg.ne
  have hf3 : f ≤ 3 := by
    by_contra hlt
    have h16' : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 * 2 ^ 4 ≤ Nat.card (normIn T T₁) * 2 ^ f := Nat.mul_le_mul hL2 h16'
    omega
  have hLf : (f = 2 ∧ Nat.card (normIn T T₁) = 4) ∨ (f = 3 ∧ Nat.card (normIn T T₁) = 2) := by
    rw [h16] at hcardT
    interval_cases f <;> omega
  have hNle : Nat.card (sec4N T T₁ T₂) ≤ 2 ^ 6 := by
    have h3 := h.card_sec4N_le
    rcases hLf with ⟨-, hL⟩ | ⟨-, hL⟩ <;> rw [hL] at h3 <;> omega
  obtain ⟨m, hm⟩ := h.isPGroup_sec4N.exists_card_eq
  have hm6 : m ≤ 6 := by
    rw [hm] at hNle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hNle
  obtain ⟨r, hr, hrdvd⟩ : ∃ r : ℕ, (r = 13 ∨ r = 19) ∧ r ∣ Nat.card (PSU3Model f) := by
    rcases hLf with ⟨hf, -⟩ | ⟨hf, -⟩
    · exact ⟨13, Or.inl rfl, prime_dvd_card_psu3Model (Or.inl ⟨hf, rfl⟩)⟩
    · exact ⟨19, Or.inr rfl, prime_dvd_card_psu3Model (Or.inr ⟨hf, rfl⟩)⟩
  have hperf := h.commutator_quotient_eq_top hq
  have hBsimple : IsSimpleGroup ((↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup
      (CFSG.BenderSuzuki.IsBenderGroup.isPSU3 f hf2 e)
  have hrB : r ∣ Nat.card ((↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) := by
    rw [Nat.card_congr e.toEquiv]
    exact hrdvd
  have hNab : ∀ n ∈ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂),
      ∀ n' ∈ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂), n * n' = n' * n := fun n hn n' hn' =>
    Subtype.ext (elemAbelian_mul_comm h.isElemAbelian_sec4N (Subgroup.mem_subgroupOf.1 hn)
      (Subgroup.mem_subgroupOf.1 hn'))
  have hNcard : Nat.card ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) = 2 ^ m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec4N_le_sec4Y).toEquiv, hm]
  have hcen := normal_le_center_of_perfect_quotient
    ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) hNab hNcard hm6 hr hperf hBsimple hrB
  obtain ⟨x, hxT, hxL⟩ := IsConcreteLE.exists_of_lt (h.sec3.cfg.normIn_lt h.pair.conj)
  have hxN : x ∉ sec4N T T₁ T₂ := fun hx => hxL (h.inf_sec4N_eq ▸ ⟨hxT, hx⟩)
  have hxM : x ∉ cfgM T T₁ := fun hx => hxN (cfgM_le_sec4N hx)
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.sec3.cfg.ne₁
  have hlN : l ∈ sec4N T T₁ T₂ := normIn_le_sec4N_mid hl
  have hl' : (⟨l, sec4N_le_sec4Y hlN⟩ : ↥(sec4Y T T₁ T₂)) ∈
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂) := Subgroup.mem_subgroupOf.2 hlN
  have hxl : x * l = l * x :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (hcen hl')
      (⟨x, left_le_sec4Y hxT⟩ : ↥(sec4Y T T₁ T₂)))
  have hlM : l ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({x} : Set G) :=
    ⟨Cfg.normIn_le_cfgM_right T T₁ hl, Subgroup.mem_centralizer_singleton_iff.2 hxl.symm⟩
  rw [h.sec3.cfg.cfgM_inf_centralizer hxT hxM] at hlM
  have hlT : l ∈ T ⊓ T₁ := ⟨normIn_le _ _ hlM, normIn_le _ _ hl⟩
  rw [h.sec3.cfg.inf, Subgroup.mem_bot] at hlT
  exact hl1 (Subtype.ext hlT)

end Main

section Statement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem sec4_two_six
    (hAsc : AschbacherNoPolarInput) (hP : MaxPair T T₁) (hS : Sec3Global T)
    (hI : Sec3IsoGlobal T) {a : G} (ha : a ∈ normD T) (haL : a ∉ T ⊔ normIn T₁ T)
    (hcomm : ∀ l ∈ normIn T₁ T, ⁅a, l⁆ ∈ T) {T₂ : Subgroup G}
    (hT₂ : ∃ g : G, T₂ = conjSubgroup g T) (haT₂ : a ∈ T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T = 16) : False :=
  Sec4Hyp.false_of_card_sixteen hAsc ⟨hP, hS, hI, ha, haL, hcomm, hT₂, haT₂⟩ hq h16

end Statement

end CFSG.CGT.Timmesfeld75
