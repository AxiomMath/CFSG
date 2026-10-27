module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.PMScalar

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

private theorem pow_natCard_eq_one_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) :
    x ^ Nat.card ↥H = 1 := by
  have h : (⟨x, hx⟩ : ↥H) ^ Nat.card ↥H = 1 := pow_card_eq_one'
  exact congrArg Subtype.val h

namespace TightSylowDataTR

variable (hd : TightSylowDataTR r K z S W L t V)
include hd

theorem exists_mem_centralizer_not_actsPM (hr : 4 ≤ r)
    (hS : ¬ (S : Subgroup G) ≤ pmSubgroup (K ⊓ W)) :
    ∃ a ∈ (S : Subgroup G), a ∈ Subgroup.centralizer ({t} : Set G) ∧
      ¬ ActsPM (K ⊓ W) a := by
  obtain ⟨g, hgS, hg⟩ := SetLike.not_le_iff_exists.mp hS
  obtain ⟨r₀, hr₀, hr₀t⟩ := hd.exists_conj_eq_mul
  rcases hd.conj_t_eq_or_of_le_normalizer hd.le_normalizer_W hgS with h | h
  · refine ⟨g, hgS, ?_, hg⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h]
  · refine ⟨r₀⁻¹ * g, (S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hr₀.1) hgS, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have e : r₀⁻¹ * g * t * (r₀⁻¹ * g)⁻¹ = t := by
        calc r₀⁻¹ * g * t * (r₀⁻¹ * g)⁻¹ = r₀⁻¹ * (g * t * g⁻¹) * r₀ := by group
          _ = r₀⁻¹ * (r₀ * t * r₀⁻¹) * r₀ := by rw [h, hr₀t]
          _ = t := by group
      calc r₀⁻¹ * g * t = r₀⁻¹ * g * t * (r₀⁻¹ * g)⁻¹ * (r₀⁻¹ * g) := by group
        _ = t * (r₀⁻¹ * g) := by rw [e]
    · intro hAct
      apply hg
      have h1 := (pmSubgroup (K ⊓ W)).mul_mem (hd.inf_core_le_pm hr hr₀) hAct
      simpa using h1

theorem exists_exponent_of_sq_mem (hr : 4 ≤ r) {a : G} (haS : a ∈ (S : Subgroup G))
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) (ha2 : a * a ∈ pmSubgroup (K ⊓ W))
    (ha : a ∉ pmSubgroup (K ⊓ W)) :
    ∃ α : ℤ, (∀ w ∈ W, a * w * a⁻¹ = w ^ α) ∧
      ((2 : ℤ) ^ (r - 1) ∣ α - (1 + 2 ^ (r - 1 - 1)) ∨
        (2 : ℤ) ^ (r - 1) ∣ α + (1 + 2 ^ (r - 1 - 1))) := by
  obtain ⟨α, hα⟩ := hd.exists_scalar (hd.hSz haS) hat (hd.le_normalizer_W haS)
  refine ⟨α, hα, ?_⟩
  obtain ⟨u, hUz⟩ : ∃ u : G, Subgroup.zpowers u = K ⊓ W := by
    haveI := hd.isCyclic_inf
    obtain ⟨g, hg⟩ : ∃ g : ↥(K ⊓ W), ∀ x : ↥(K ⊓ W), x ∈ Subgroup.zpowers g :=
      IsCyclic.exists_generator
    refine ⟨(g : G), le_antisymm (Subgroup.zpowers_le.mpr g.2) ?_⟩
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hu : orderOf u = 2 ^ (r - 1) := by
    rw [← Nat.card_zpowers, hUz, hd.natCard_inf_W]
  have huW : u ∈ W := by
    have h : u ∈ K ⊓ W := by
      rw [← hUz]
      exact Subgroup.mem_zpowers u
    exact h.2
  have hαu : a * u * a⁻¹ = u ^ α := hα u huW
  have hau : a * u * a⁻¹ ∈ Subgroup.zpowers u := by
    rw [hαu]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) α
  have ha2' : ActsPM (Subgroup.zpowers u) (a * a) := by
    rw [hUz]
    exact mem_pmSubgroup.mp ha2
  have ha' : ¬ ActsPM (Subgroup.zpowers u) a := by
    rw [hUz]
    exact fun h => ha (mem_pmSubgroup.mpr h)
  obtain ⟨α', hα'u, hcong⟩ :=
    exists_exponent_of_actsPM_sq (n := r - 1) (by omega) hu hau ha2' ha'
  have e : u ^ α = u ^ α' := hαu.symm.trans hα'u
  have hdvd : ((orderOf u : ℕ) : ℤ) ∣ α - α' := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, e, mul_inv_cancel]
  rw [hu] at hdvd
  push_cast at hdvd
  rcases hcong with h | h
  · refine Or.inl ?_
    have e2 : α - (1 + 2 ^ (r - 1 - 1)) = (α - α') + (α' - (1 + 2 ^ (r - 1 - 1))) := by
      ring
    rw [e2]
    exact dvd_add hdvd h
  · refine Or.inr ?_
    have e2 : α + (1 + 2 ^ (r - 1 - 1)) = (α - α') + (α' + (1 + 2 ^ (r - 1 - 1))) := by
      ring
    rw [e2]
    exact dvd_add hdvd h

private theorem pow_eq_one_of_mem_W {w : G} (hw : w ∈ W) : w ^ (2 ^ (r - 1)) = 1 := by
  have hcomm := hd.comm_of_mem
  let P : Subgroup G :=
    { carrier := {x | x ∈ W ∧ x ^ (2 ^ (r - 1)) = 1}
      mul_mem' := fun {x y} hx hy => ⟨W.mul_mem hx.1 hy.1, by
        rw [(show Commute x y from hcomm x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨W.one_mem, one_pow _⟩
      inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hsub : K ⊓ W ⊔ V ≤ P := by
    refine sup_le (fun x hx => ⟨hx.2, ?_⟩) (fun v hv => ⟨hd.leW hv, ?_⟩)
    · have h := pow_natCard_eq_one_of_mem (H := K ⊓ W) hx
      rwa [hd.natCard_inf_W] at h
    · have h := pow_natCard_eq_one_of_mem (H := V) hv
      rwa [hd.natCard_V] at h
  rw [hd.sup_eq_inf_sup] at hw
  exact (hsub hw).2

theorem mul_self_mem_W (hB : TightBPrimeBot K S W L) (hr : 4 ≤ r) {a : G}
    (haS : a ∈ (S : Subgroup G)) {α : ℤ}
    (hα : (2 : ℤ) ^ (r - 1) ∣ α - (1 + 2 ^ (r - 1 - 1)) ∨
      (2 : ℤ) ^ (r - 1) ∣ α + (1 + 2 ^ (r - 1 - 1)))
    (haW : ∀ w ∈ W, a * w * a⁻¹ = w ^ α) : a * a ∈ W := by
  have hcc : (2 : ℤ) ^ (r - 1) ∣ (1 + 2 ^ (r - 1 - 1)) * (1 + 2 ^ (r - 1 - 1)) - 1 := by
    have e : (1 + (2 : ℤ) ^ (r - 1 - 1)) * (1 + 2 ^ (r - 1 - 1)) - 1 =
        2 * 2 ^ (r - 1 - 1) + 2 ^ ((r - 1 - 1) + (r - 1 - 1)) := by
      rw [pow_add]
      ring
    have e2 : (2 : ℤ) * 2 ^ (r - 1 - 1) = 2 ^ (r - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e]
    exact dvd_add (dvd_of_eq e2.symm) (pow_dvd_pow _ (by omega))
  have hsq : (2 : ℤ) ^ (r - 1) ∣ α * α - 1 := by
    rcases hα with h | h
    · have e3 : α * α - 1 = (α - (1 + 2 ^ (r - 1 - 1))) * (α + (1 + 2 ^ (r - 1 - 1))) +
          ((1 + 2 ^ (r - 1 - 1)) * (1 + 2 ^ (r - 1 - 1)) - 1) := by
        ring
      rw [e3]
      exact dvd_add (dvd_mul_of_dvd_left h _) hcc
    · have e3 : α * α - 1 = (α + (1 + 2 ^ (r - 1 - 1))) * (α - (1 + 2 ^ (r - 1 - 1))) +
          ((1 + 2 ^ (r - 1 - 1)) * (1 + 2 ^ (r - 1 - 1)) - 1) := by
        ring
      rw [e3]
      exact dvd_add (dvd_mul_of_dvd_left h _) hcc
  obtain ⟨m, hm⟩ := hsq
  have hpow : ∀ w ∈ W, w ^ (α * α) = w := by
    intro w hw
    have hexp : w ^ ((2 : ℤ) ^ (r - 1)) = 1 := by
      have e4 : (2 : ℤ) ^ (r - 1) = ((2 ^ (r - 1) : ℕ) : ℤ) := by norm_cast
      rw [e4, zpow_natCast]
      exact hd.pow_eq_one_of_mem_W hw
    have e5 : α * α = (2 : ℤ) ^ (r - 1) * m + 1 := by linarith
    rw [e5, zpow_add, zpow_mul, hexp, one_zpow, one_mul, zpow_one]
  have hC : a * a ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hconj : a * a * h * (a * a)⁻¹ = h := by
      have h1 : a * h * a⁻¹ = h ^ α := haW h hh
      have h2 : (a * h * a⁻¹) ^ α = a * h ^ α * a⁻¹ := conj_zpow
      calc a * a * h * (a * a)⁻¹ = a * (a * h * a⁻¹) * a⁻¹ := by group
        _ = a * (h ^ α) * a⁻¹ := by rw [h1]
        _ = (a * h * a⁻¹) ^ α := h2.symm
        _ = (h ^ α) ^ α := by rw [h1]
        _ = h ^ (α * α) := (zpow_mul h α α).symm
        _ = h := hpow h hh
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  exact (hd.inf_centralizer_W_eq hB).le ⟨(S : Subgroup G).mul_mem haS haS, hC⟩

theorem exists_involution (hB : TightBPrimeBot K S W L) (hr : 4 ≤ r)
    (hS : ¬ (S : Subgroup G) ≤ pmSubgroup (K ⊓ W)) :
    ∃ x ∈ (S : Subgroup G), x * x = 1 ∧ x ∉ pmSubgroup (K ⊓ W) := by
  obtain ⟨a₁, ha₁S, ha₁t, ha₁⟩ := hd.exists_mem_centralizer_not_actsPM hr hS
  obtain ⟨m, hm⟩ := (S.isPGroup' ⟨a₁, ha₁S⟩)
  have hm' : a₁ ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  obtain ⟨j, hj1, hj2⟩ := exists_pow_not_mem_mul_self_mem (pmSubgroup (K ⊓ W)) hm' ha₁
  have haS : a₁ ^ 2 ^ j ∈ (S : Subgroup G) := (S : Subgroup G).pow_mem ha₁S _
  have hat : a₁ ^ 2 ^ j ∈ Subgroup.centralizer ({t} : Set G) :=
    (Subgroup.centralizer ({t} : Set G)).pow_mem ha₁t _
  obtain ⟨α, hα, hαmod⟩ := hd.exists_exponent_of_sq_mem hr haS hat hj2 hj1
  have ha2W : a₁ ^ 2 ^ j * a₁ ^ 2 ^ j ∈ W := hd.mul_self_mem_W hB hr haS hαmod hα
  obtain ⟨w, hwW, hw⟩ := exists_mul_mul_eq_one (W := W) (U := K ⊓ W) (V := V) (n := r - 1)
    (by omega) hd.isCyclic_inf hd.isCyclic_V hd.natCard_inf_W hd.natCard_V hd.inf_inf_eq_bot
    hd.sup_eq_inf_sup hd.toTightSylowDataR.comm_of_mem hαmod hα ha2W
  refine ⟨a₁ ^ 2 ^ j * w, (S : Subgroup G).mul_mem haS (hd.hWS hwW), hw, fun hx => hj1 ?_⟩
  have h1 := (pmSubgroup (K ⊓ W)).mul_mem hx ((pmSubgroup (K ⊓ W)).inv_mem (hd.W_le_pm hwW))
  simpa using h1

end TightSylowDataTR

end CFSG.CGT.PushingUpLit.SolKNA.R4
