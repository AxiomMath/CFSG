module

public import CFSG.ClassicalInvolution.AschTight.S19CData
public import CFSG.ClassicalInvolution.AschTight.S19CMir
public import CFSG.ClassicalInvolution.AschTight.S19CFix

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

omit [Finite G] [IsSimpleGroup G] in
theorem mul_comm_of_conj_eq {a x : G} (h : a * x * a⁻¹ = x) : x * a = a * x := by
  calc x * a = a * x * a⁻¹ * a := by rw [h]
    _ = a * x := by group

omit [Finite G] [IsSimpleGroup G] in
theorem exists_eq_conj_of_mem_conjSub {U : Subgroup G} {c y : G} (hy : y ∈ conjSub c U) :
    ∃ x ∈ U, y = c * x * c⁻¹ :=
  ⟨c⁻¹ * y * c, mem_conjSub_iff.mp hy, by group⟩

theorem exists_conj_eq_t (hd : Sec19DataT p f K z S W L t V) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1)
    (hat : a ∈ Subgroup.centralizer ({t} : Set G)) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : (∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) :
    ∃ c : G, c * a = a * c ∧ c * z * c⁻¹ = t := by
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  have hΩ := hypOmegaMod_of_tightD ht
  have hWc := S1911.comm_of_mem hd0
  have haN : a ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight ht.toTightBranch]
    exact hd.hSz haS
  have haW : a ∈ Subgroup.normalizer (W : Set G) := S19B.le_normalizer_W hd haS
  have hconjKW : ∀ x ∈ K ⊓ W, a * x * a⁻¹ ∈ K ⊓ W := fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp haN x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp haW x).mp hx.2⟩
  have hconjR : ∀ x ∈ (S : Subgroup G) ⊓ K, a * x * a⁻¹ ∈ (S : Subgroup G) ⊓ K := fun x hx =>
    ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem haS hx.1) ((S : Subgroup G).inv_mem haS),
      (Subgroup.mem_normalizer_iff.mp haN x).mp hx.2⟩
  have hactU : (∀ x ∈ Subgroup.zpowers u, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ x ∈ Subgroup.zpowers u, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k - 1) := by
    rw [hu]
    exact hact
  obtain ⟨r₀, hr₀R, hr₀U⟩ := S1911.exists_mem_not_mem (S1911.card_inf_eq hd0)
  obtain ⟨u₀, K₀, hu₀, hdd₀⟩ := exists_dData_K_of hd hr₀R hr₀U
  have hasr : a * r₀ * a⁻¹ * r₀⁻¹ ∈ Subgroup.zpowers u := by
    rw [hu, ← hu₀]
    exact mul_inv_mem_of_dData hdd₀ ha2 (hconjR r₀ hr₀R) (by rw [hu₀]; exact hconjKW)
  obtain ⟨w, hw, hwr⟩ := exists_mul_fixed hk huo ha2 hasr hactU
  have hwKW : w ∈ K ⊓ W := hu ▸ hw
  have hrR : w * r₀ ∈ (S : Subgroup G) ⊓ K :=
    ((S : Subgroup G) ⊓ K).mul_mem ⟨hd.hWS hwKW.2, hwKW.1⟩ hr₀R
  have hrU : w * r₀ ∉ K ⊓ W := fun h => hr₀U (by
    have := (K ⊓ W).mul_mem ((K ⊓ W).inv_mem hwKW) h
    rwa [inv_mul_cancel_left] at this)
  obtain ⟨u₁, K', hu₁, hdK⟩ := exists_dData_K_of hd hrR hrU
  obtain ⟨RL, v, -, haRL, hRLD, hv, hvV, hcardRL⟩ := exists_RL hd haS hat
  have hconjRL : ∀ x ∈ RL, a * x * a⁻¹ ∈ RL := fun x hx => haRL ▸ conj_mem_conjSub hx
  have hconjV : ∀ x ∈ Subgroup.zpowers v, a * x * a⁻¹ ∈ Subgroup.zpowers v := by
    rw [hv]
    exact fun x hx => ⟨hconjRL x hx.1, (Subgroup.mem_normalizer_iff.mp haW x).mp hx.2⟩
  obtain ⟨rL₀, hrL₀, hrL₀V⟩ := S1911.exists_mem_not_mem hcardRL
  obtain ⟨L₀, hdL₀⟩ := exists_dData_L_of hd hRLD hv hvV hcardRL hrL₀ hrL₀V
  obtain ⟨hc₀K, -⟩ := conj_eq_of_dData hd hdK hdL₀
  have hasL₀ : a * rL₀ * a⁻¹ * rL₀⁻¹ ∈ Subgroup.zpowers v :=
    mul_inv_mem_of_dData hdL₀ ha2 (hconjRL _ hrL₀) hconjV
  have hy₀W : a * rL₀ * a⁻¹ * rL₀⁻¹ ∈ W := (hv ▸ hasL₀ : _ ∈ RL ⊓ W).2
  have haL₀ : a * rL₀ * a⁻¹ = (a * rL₀ * a⁻¹ * rL₀⁻¹) * rL₀ := by group
  have hc₀W : (w * r₀)⁻¹ * rL₀ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hdK.r_normW) hdL₀.r_normW
  have himg : conjSub ((w * r₀)⁻¹ * rL₀) (K ⊓ W) = Subgroup.zpowers v := by
    rw [← hu₁, ← hdK.inf_eq, conjSub_inf, hc₀K, mem_normalizer_iff_conjSub_eq.mp hc₀W,
      hdL₀.inf_eq]
  have hactV : (∀ y ∈ Subgroup.zpowers v, a * y * a⁻¹ = y ^ ((2 : ℤ) ^ k + 1)) ∨
      ∀ y ∈ Subgroup.zpowers v, a * y * a⁻¹ = y ^ ((2 : ℤ) ^ k - 1) := by
    rcases hact with h1 | h2
    · refine Or.inl fun y hy => ?_
      rw [← himg] at hy
      obtain ⟨x, hx, rfl⟩ := exists_eq_conj_of_mem_conjSub hy
      exact conj_conj_zpow inf_le_right hWc hwr haL₀ hy₀W hdL₀.r_normW h1 hx
    · refine Or.inr fun y hy => ?_
      rw [← himg] at hy
      obtain ⟨x, hx, rfl⟩ := exists_eq_conj_of_mem_conjSub hy
      exact conj_conj_zpow inf_le_right hWc hwr haL₀ hy₀W hdL₀.r_normW h2 hx
  have hvo : orderOf v = 2 ^ (k + 1) := by
    rw [← Sec71.orderOf_eq_orderOf hΩ hdK hdL₀, ← huo, ← Nat.card_zpowers, ← Nat.card_zpowers,
      hu₁, hu]
  obtain ⟨w', hw', hw'r⟩ := exists_mul_fixed hk hvo ha2 hasL₀ hactV
  have hw'RL : w' ∈ RL := (hv ▸ hw' : w' ∈ RL ⊓ W).1
  have hrL : w' * rL₀ ∈ RL := RL.mul_mem hw'RL hrL₀
  have hrLV : w' * rL₀ ∉ Subgroup.zpowers v := fun h => hrL₀V (by
    have := (Subgroup.zpowers v).mul_mem ((Subgroup.zpowers v).inv_mem hw') h
    rwa [inv_mul_cancel_left] at this)
  obtain ⟨L₁, hdL⟩ := exists_dData_L_of hd hRLD hv hvV hcardRL hrL hrLV
  obtain ⟨-, hczt⟩ := conj_eq_of_dData hd hdK hdL
  exact ⟨(w * r₀)⁻¹ * (w' * rL₀),
    ((Commute.inv_left (mul_comm_of_conj_eq hwr)).mul_left (mul_comm_of_conj_eq hw'r)).eq, hczt⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
