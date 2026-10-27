module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma p0_y_ne_z (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    x₁ ^ 2 ≠ (x₁ * x₂) ^ 2 := by
  intro h
  have hx2sq : x₂ ^ 2 = 1 := by
    rw [hc.wreath.x₂_sq, ← h]
    exact (S4A.y_mul_self_ne_one hc.wreath).1
  have hdvd : orderOf x₂ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2sq
  rw [hc.wreath.ord_x₂] at hdvd
  norm_num at hdvd

private lemma p0_lam_commute_z (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    lam * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * lam := by
  have hlam2 : lam * lam = 1 := by
    have h := pow_orderOf_eq_one lam
    rw [hc.wreath.ord_lam, pow_two] at h
    exact h
  have hx2 : lam * x₂ * lam⁻¹ = x₁ := by
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by
          rw [hc.wreath.conj_x₁]
      _ = (lam * lam) * x₁ * (lam * lam)⁻¹ := by group
      _ = x₁ := by rw [hlam2]; group
  have hmul : lam * (x₁ * x₂) * lam⁻¹ = x₁ * x₂ := by
    calc lam * (x₁ * x₂) * lam⁻¹
        = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) := by group
      _ = x₂ * x₁ := by rw [hc.wreath.conj_x₁, hx2]
      _ = x₁ * x₂ := hc.wreath.comm.symm
  have hconj : lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
    rw [← conj_pow, hmul]
  calc lam * (x₁ * x₂) ^ 2 = (lam * (x₁ * x₂) ^ 2 * lam⁻¹) * lam := by group
    _ = (x₁ * x₂) ^ 2 * lam := by rw [hconj]

private lemma p0_conj_y_ne_z (hc : Ctx8a t L S x₁ x₂ lam rho tau) {m : G}
    (hm : m * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * m) :
    m * x₁ ^ 2 * m⁻¹ ≠ (x₁ * x₂) ^ 2 := by
  intro h
  have hconjz : m * (x₁ * x₂) ^ 2 * m⁻¹ = (x₁ * x₂) ^ 2 := by
    rw [hm]; group
  have hyz : x₁ ^ 2 = (x₁ * x₂) ^ 2 := by
    have hconj : m * x₁ ^ 2 * m⁻¹ = m * (x₁ * x₂) ^ 2 * m⁻¹ := by rw [h, hconjz]
    have := congrArg (fun t => m⁻¹ * t * m) hconj
    have lhs : m⁻¹ * (m * x₁ ^ 2 * m⁻¹) * m = x₁ ^ 2 := by group
    have rhs : m⁻¹ * (m * (x₁ * x₂) ^ 2 * m⁻¹) * m = (x₁ * x₂) ^ 2 := by group
    rwa [lhs, rhs] at this
  exact p0_y_ne_z hc hyz

private lemma p0_orderOf_rho_sq (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    orderOf (rho ^ 2) = 3 := by
  have hrho3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, show 2 * 3 = 3 * 2 from by norm_num, pow_mul, hrho3, one_pow]
  · intro h
    have hdvd : orderOf rho ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hc.ord_rho] at hdvd
    norm_num at hdvd

theorem p0_conjIn_z (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    conjIn (ctxM t tau x₁ x₂) ((x₁ * x₂) ^ 2) = {u | u ∈ fourGrp x₁ x₂ ∧ u ≠ 1} := by
  ext u
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨hc.normal_V.2 m hm ((x₁ * x₂) ^ 2) (Subgroup.subset_closure (by simp)), ?_⟩
    intro h
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      calc (x₁ * x₂) ^ 2 = m⁻¹ * (m * (x₁ * x₂) ^ 2 * m⁻¹) * m := by group
        _ = m⁻¹ * 1 * m := by rw [h]
        _ = 1 := by group
    exact hc.wreath.sq_x₁x₂_ne_one hz1
  · rintro ⟨huV, hu1⟩
    have hzV : (x₁ * x₂) ^ 2 ∈ fourGrp x₁ x₂ := Subgroup.subset_closure (by simp)
    have hz1 : (x₁ * x₂) ^ 2 ≠ 1 := hc.wreath.sq_x₁x₂_ne_one
    have hM := p0_gens_mem_M hc.toCtx4
    have hrhoM : rho ∈ ctxM t tau x₁ x₂ := hM.2.2.2.2.1
    rcases p0_rho_orbit_V hc.toCtx4 hzV hz1 huV hu1 with h | h | h
    · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
    · exact ⟨rho, hrhoM, by rw [h]⟩
    · exact ⟨rho⁻¹, Subgroup.inv_mem _ hrhoM, by rw [h]; group⟩

theorem p0_card_Cz (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ({(x₁ * x₂) ^ 2} : Set G)) = 2 ^ 10 := by
  have h := card_eq_ncard_conjIn_mul (ctxM t tau x₁ x₂) ((x₁ * x₂) ^ 2)
  rw [p0_conjIn_z hc] at h
  have hVn : ({u : G | u ∈ fourGrp x₁ x₂ ∧ u ≠ 1}).ncard = 3 := by
    have hset : {u : G | u ∈ fourGrp x₁ x₂ ∧ u ≠ 1}
        = ((fourGrp x₁ x₂ : Subgroup G) : Set G) \ {1} := by
      ext u; simp [Set.mem_sdiff]
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)]
    have hncard : ((fourGrp x₁ x₂ : Subgroup G) : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hc.wreath.fourGrp_eq_omega.2.2
    rw [hncard]
  rw [hVn, hc.card_M] at h
  exact (Nat.mul_left_cancel (by norm_num : 0 < 3) h).symm

theorem p0_conjIn_y (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    conjIn (ctxM t tau x₁ x₂ ⊓ centralizer ({(x₁ * x₂) ^ 2} : Set G)) (x₁ ^ 2) =
      {x₁ ^ 2, x₁ ^ 2 * (x₁ * x₂) ^ 2} := by
  ext u
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmM : m ∈ ctxM t tau x₁ x₂ := hm.1
    have hmC : m * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * m :=
      Subgroup.mem_centralizer_singleton_iff.mp hm.2
    have huV : m * x₁ ^ 2 * m⁻¹ ∈ fourGrp x₁ x₂ :=
      hc.normal_V.2 m hmM (x₁ ^ 2) (Subgroup.subset_closure (by simp))
    have hu1 : m * x₁ ^ 2 * m⁻¹ ≠ 1 := by
      intro h
      have hy1 : x₁ ^ 2 = 1 := by
        calc x₁ ^ 2 = m⁻¹ * (m * x₁ ^ 2 * m⁻¹) * m := by group
          _ = m⁻¹ * 1 * m := by rw [h]
          _ = 1 := by group
      exact (S4A.y_mul_self_ne_one hc.wreath).2 hy1
    have huz : m * x₁ ^ 2 * m⁻¹ ≠ (x₁ * x₂) ^ 2 := p0_conj_y_ne_z hc hmC
    have hcases := (mem_closure_pair_of_invol (a := x₁ ^ 2) (b := (x₁ * x₂) ^ 2)
      (x := m * x₁ ^ 2 * m⁻¹) (S4A.y_mul_self_ne_one hc.wreath).1
      hc.wreath.sq_x₁x₂_mul_self (S4A.y_commute_z hc.wreath)).mp
      (by simpa [fourGrp] using huV)
    rcases hcases with h | h | h | h
    · exact absurd h hu1
    · simp [h]
    · exact absurd h huz
    · simp [h]
  · intro hu
    have hu' : u = x₁ ^ 2 ∨ u = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by simpa using hu
    have hM := p0_gens_mem_M hc.toCtx4
    have hlamM : lam ∈ ctxM t tau x₁ x₂ := hM.2.2.2.2.2
    rcases hu' with rfl | rfl
    · exact ⟨1, ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩, by group⟩
    · refine ⟨lam, ⟨hlamM, Subgroup.mem_centralizer_singleton_iff.mpr
        (p0_lam_commute_z hc)⟩, ?_⟩
      rw [← conj_pow, hc.wreath.conj_x₁, hc.wreath.x₂_sq]

theorem p0_CV_eq (x₁ x₂ : G) (M : Subgroup G) :
    M ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      (M ⊓ centralizer ({(x₁ * x₂) ^ 2} : Set G)) ⊓ centralizer ({x₁ ^ 2} : Set G) := by
  have hpair : centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      centralizer ({x₁ ^ 2} : Set G) ⊓ centralizer ({(x₁ * x₂) ^ 2} : Set G) := by
    have hcl : centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
        centralizer ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) := by
      rw [fourGrp]
      exact Subgroup.centralizer_closure _
    rw [hcl]
    ext g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      exact ⟨fun a ha => h a (by
              rw [Set.mem_insert_iff]
              exact Or.inl (by simpa using ha)),
            fun a ha => h a (by
              rw [Set.mem_insert_iff]
              exact Or.inr (by simpa using ha))⟩
    · rintro ⟨h1, h2⟩ a ha
      rw [Set.mem_insert_iff] at ha
      rcases ha with ha | ha
      · rw [ha]
        exact h1 (x₁ ^ 2) (by simp)
      · have haz : a = (x₁ * x₂) ^ 2 := by simpa using ha
        rw [haz]
        exact h2 ((x₁ * x₂) ^ 2) (by simp)
  rw [hpair]
  rw [inf_assoc, inf_comm (centralizer ({(x₁ * x₂) ^ 2} : Set G))
    (centralizer ({x₁ ^ 2} : Set G))]

theorem p0_card_CV (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)) =
      2 ^ 9 := by
  have h := card_eq_ncard_conjIn_mul
    (ctxM t tau x₁ x₂ ⊓ centralizer ({(x₁ * x₂) ^ 2} : Set G)) (x₁ ^ 2)
  rw [p0_conjIn_y hc] at h
  have hyz : x₁ ^ 2 ≠ x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
    intro hh
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have := congrArg (fun w => (x₁ ^ 2)⁻¹ * w) hh
      simpa [mul_assoc] using this.symm
    exact hc.wreath.sq_x₁x₂_ne_one hz1
  rw [Set.ncard_pair hyz, p0_card_Cz hc] at h
  have h3 : Nat.card ↥((ctxM t tau x₁ x₂ ⊓ centralizer ({(x₁ * x₂) ^ 2} : Set G)) ⊓
      centralizer ({x₁ ^ 2} : Set G)) = 2 ^ 9 := by
    rw [show 2 ^ 10 = 2 * 2 ^ 9 from by norm_num] at h
    exact (Nat.mul_left_cancel (by norm_num : 0 < 2) h).symm
  rw [p0_CV_eq x₁ x₂ (ctxM t tau x₁ x₂)]
  exact h3

theorem p0_normal_CV (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G))
      (ctxM t tau x₁ x₂) := by
  refine ⟨inf_le_left, ?_⟩
  intro g hg c hc'
  have hcM : c ∈ ctxM t tau x₁ x₂ := hc'.1
  have hcC : c ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := hc'.2
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcM) (Subgroup.inv_mem _ hg), ?_⟩
  show g * c * g⁻¹ ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff] at hcC ⊢
  intro v hv
  have hgv : g⁻¹ * v * g ∈ fourGrp x₁ x₂ := by
    simpa using hc.normal_V.2 g⁻¹ (inv_mem hg) v hv
  have hcomm := hcC (g⁻¹ * v * g) hgv
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
    _ = (g * c * g⁻¹) * v := by group

theorem p0_CV_le_O (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) ≤
      ctxO t tau x₁ x₂ :=
  p0_le_O_of_normal t tau x₁ x₂ (p0_normal_CV hc)
    (IsPGroup.of_card (p := 2) (n := 9) (p0_card_CV hc))

theorem p0_lam_not_mem_O (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    lam ∉ ctxO t tau x₁ x₂ := by
  intro hlam
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := p0_gens_mem_M hc.toCtx4
  have hrhoM : rho ∈ ctxM t tau x₁ x₂ := hM.2.2.2.2.1
  have hnorm := p0_normal_O t tau x₁ x₂
  have hrho2O : rho ^ 2 ∈ ctxO t tau x₁ x₂ := by
    have h1 : rho * lam * rho⁻¹ ∈ ctxO t tau x₁ x₂ := hnorm.2 rho hrhoM lam hlam
    have h2 : (rho * lam * rho⁻¹) * lam⁻¹ ∈ ctxO t tau x₁ x₂ :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hlam)
    have heq : (rho * lam * rho⁻¹) * lam⁻¹ = rho ^ 2 := by
      have hconj : lam * rho⁻¹ * lam⁻¹ = rho := by
        calc lam * rho⁻¹ * lam⁻¹ = (lam * rho * lam⁻¹)⁻¹ := by group
          _ = (rho⁻¹)⁻¹ := by rw [hc.lam_rho]
          _ = rho := by group
      calc (rho * lam * rho⁻¹) * lam⁻¹ = rho * (lam * rho⁻¹ * lam⁻¹) := by group
        _ = rho * rho := by rw [hconj]
        _ = rho ^ 2 := by rw [pow_two]
    rwa [heq] at h2
  have hne : (⟨rho ^ 2, hrho2O⟩ : ctxO t tau x₁ x₂) ≠ 1 := by
    intro h
    have hr2 : rho ^ 2 = 1 := congrArg Subtype.val h
    have hdvd : orderOf rho ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hr2
    rw [hc.ord_rho] at hdvd
    norm_num at hdvd
  have hdvd2 : 2 ∣ orderOf (⟨rho ^ 2, hrho2O⟩ : ctxO t tau x₁ x₂) :=
    (p0_isPGroup_O t tau x₁ x₂).dvd_orderOf hne
  have hord : orderOf (⟨rho ^ 2, hrho2O⟩ : ctxO t tau x₁ x₂) = 3 := by
    rw [Subgroup.orderOf_mk, p0_orderOf_rho_sq hc]
  rw [hord] at hdvd2
  norm_num at hdvd2

theorem p0_card_O (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxO t tau x₁ x₂) = 2 ^ 9 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM := p0_gens_mem_M hc.toCtx4
  have hlamM : lam ∈ ctxM t tau x₁ x₂ := hM.2.2.2.2.2
  have hCV := p0_card_CV hc
  have hCleO : ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G)
      ≤ ctxO t tau x₁ x₂ := p0_CV_le_O hc
  have h9dvd : 2 ^ 9 ∣ Nat.card ↥(ctxO t tau x₁ x₂) := by
    rw [← hCV]
    exact Subgroup.card_dvd_of_le hCleO
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (p0_isPGroup_O t tau x₁ x₂)
  have hkge : 9 ≤ k := by
    have h : 2 ^ 9 ∣ 2 ^ k := by rw [← hk]; exact h9dvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h
  let P : Subgroup G := ctxO t tau x₁ x₂ ⊔ zpowers lam
  have hzp : IsPGroup 2 (zpowers lam : Subgroup G) :=
    IsPGroup.of_card (p := 2) (n := 1)
      (by rw [Nat.card_zpowers, hc.wreath.ord_lam, pow_one])
  have hnorm : (zpowers lam : Subgroup G) ≤ Subgroup.normalizer (ctxO t tau x₁ x₂ : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => (p0_normal_O t tau x₁ x₂).2 lam hlamM x hx, fun hx => by
      have h := (p0_normal_O t tau x₁ x₂).2 lam⁻¹ (inv_mem hlamM) (lam * x * lam⁻¹) hx
      have h2 : lam⁻¹ * (lam * x * lam⁻¹) * (lam⁻¹)⁻¹ = x := by group
      rwa [h2] at h⟩
  have hP2 : IsPGroup 2 P := by
    dsimp only [P]
    exact IsPGroup.to_sup_of_normal_left' (p0_isPGroup_O t tau x₁ x₂) hzp hnorm
  have hPleM : P ≤ ctxM t tau x₁ x₂ := by
    dsimp only [P]
    exact sup_le (p0_O_le_M t tau x₁ x₂) (Subgroup.zpowers_le.mpr hlamM)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
  have hkn : k ≤ n := by
    have hle : Nat.card ↥(ctxO t tau x₁ x₂) ≤ Nat.card P :=
      Subgroup.card_le_of_le (by dsimp only [P]; exact le_sup_left)
    rw [hk, hn] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hnle : n ≤ 10 := by
    have h : 2 ^ n ∣ 3 * 2 ^ 10 := by
      rw [← hn, ← hc.card_M]
      exact Subgroup.card_dvd_of_le hPleM
    have hcop : Nat.Coprime (2 ^ n) 3 := (show Nat.Coprime 2 3 by norm_num).pow_left n
    have h' : 2 ^ n ∣ 2 ^ 10 * 3 := by
      rw [← Nat.mul_comm 3 (2 ^ 10)]
      exact h
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp
      (hcop.dvd_of_dvd_mul_right h')
  have hk_id : k = 9 := by
    rcases (by omega : k = 9 ∨ k = 10) with hk9 | hk10
    · exact hk9
    · exfalso
      have hnge : 10 ≤ n := by rw [← hk10]; exact hkn
      have hneq : n = 10 := le_antisymm hnle hnge
      have hOP : ctxO t tau x₁ x₂ = P := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · dsimp only [P]; exact le_sup_left
        · rw [hn, hk, hk10, hneq]
      have hlamP : lam ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
      rw [← hOP] at hlamP
      exact p0_lam_not_mem_O hc hlamP
  rw [hk, hk_id]

theorem p0_O_eq_C (hc : Ctx8a t L S x₁ x₂ lam rho tau) :
    ctxO t tau x₁ x₂ =
      ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hCO : ctxM t tau x₁ x₂ ⊓ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) =
      ctxO t tau x₁ x₂ :=
    Subgroup.eq_of_le_of_card_ge (p0_CV_le_O hc) (by rw [p0_card_O hc, p0_card_CV hc])
  exact hCO.symm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
