module

public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassLCS
public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassConj
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Walter.W67
open scoped commutatorElement

universe u

structure MB (P : Type u) [Group P] [Finite P] where
  m : ℕ
  hm : 5 ≤ m
  hP : IsPGroup 3 P
  hcard : Nat.card P = 3 ^ m
  hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥

structure MC (P : Type u) [Group P] [Finite P] extends MB P where
  abel : ∀ a ∈ (⊤ : Subgroup P).lowerCentralSeries 1, ∀ b ∈ (⊤ : Subgroup P).lowerCentralSeries 1,
    a * b = b * a

theorem comm_central_mul {G : Type*} [Group G] (s t u v : G) (hu : ∀ q, u * q = q * u)
    (hv : ∀ q, v * q = q * v) : ⁅s * u, t * v⁆ = ⁅s, t⁆ := by
  simp only [commutatorElement_def]
  calc s * u * (t * v) * (s * u)⁻¹ * (t * v)⁻¹
      = s * (u * (t * v)) * u⁻¹ * s⁻¹ * (t * v)⁻¹ := by group
    _ = s * ((t * v) * u) * u⁻¹ * s⁻¹ * (t * v)⁻¹ := by rw [hu (t * v)]
    _ = s * (t * v) * s⁻¹ * (t * v)⁻¹ := by group
    _ = s * t * (v * s⁻¹) * v⁻¹ * t⁻¹ := by group
    _ = s * t * (s⁻¹ * v) * v⁻¹ * t⁻¹ := by rw [hv s⁻¹]
    _ = s * t * s⁻¹ * t⁻¹ := by group

namespace MB

variable {P : Type u} [Group P] [Finite P] (d : MB P)

include d

abbrev L (_d : MB P) (j : ℕ) : Subgroup P := (⊤ : Subgroup P).lowerCentralSeries j

theorem card_L {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ d.m - 1) : Nat.card (d.L j) = 3 ^ (d.m - 1 - j) :=
  card_lcs_of_maxClass d.m P d.hP d.hcard d.hne (by have := d.hm; omega) j hj hjm

theorem L_bot {j : ℕ} (hj : d.m - 1 ≤ j) : d.L j = ⊥ := by
  have h := lcs_eq_bot_of_card d.m P d.hP d.hcard (by have := d.hm; omega)
  rw [eq_bot_iff, ← h]
  exact Subgroup.lowerCentralSeries_antitone _ hj

instance L_normal (j : ℕ) : (d.L j).Normal := inferInstance

theorem L_center: d.L (d.m - 2) = Subgroup.center P :=
  lcs_pred_eq_center d.hP (by have := d.hm; omega) d.hcard d.hne

theorem card_center: Nat.card (Subgroup.center P) = 3 :=
  card_center_of_maxClass d.hP (by have := d.hm; omega) d.hcard d.hne

theorem comm_mem_L {j : ℕ} {u : P} (hu : u ∈ d.L j) (g : P) : ⁅u, g⁆ ∈ d.L (j + 1) := by
  show ⁅u, g⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries (j + 1)
  rw [Subgroup.lowerCentralSeries_succ]
  exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_top g)

theorem L_anti {i j : ℕ} (h : i ≤ j) : d.L j ≤ d.L i :=
  Subgroup.lowerCentralSeries_antitone _ h

theorem L_le_normal {N : Subgroup P} [N.Normal] {r : ℕ} (hr2 : 2 ≤ r) (hrm : r ≤ d.m - 2)
    (hN : Nat.card N = 3 ^ r) : d.L (d.m - 3) ≤ N := by
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hQ : Nat.card (P ⧸ N) = 3 ^ (d.m - r) := by
    have : 3 ^ d.m = 3 ^ (d.m - r) * 3 ^ r := by
      rw [← pow_add]; congr 1; omega
    rw [hN, d.hcard, this] at hmul
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) hmul).symm
  have h1 := lcs_eq_bot_of_card (p := 3) (d.m - r) (P ⧸ N) (d.hP.to_quotient N) hQ (by omega)
  have h2 := lcs_le_of_quotient_eq_bot N h1
  exact (d.L_anti (by omega : d.m - r - 1 ≤ d.m - 3)).trans h2

theorem L1_ne_le_L2: ¬ d.L 1 ≤ d.L 2 := by
  intro h
  have h1 := d.card_L (j := 1) le_rfl (by have := d.hm; omega)
  have h2 := d.card_L (j := 2) (by omega) (by have := d.hm; omega)
  have heq : d.L 1 = d.L 2 := le_antisymm h (d.L_anti (by omega))
  have : Nat.card (d.L 1) = Nat.card (d.L 2) := by rw [heq]
  rw [h1, h2] at this
  have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  have := d.hm
  omega

theorem Q_card: Nat.card (P ⧸ d.L 2) = 27 := by
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.L 2)
  rw [d.card_L (j := 2) (by omega) (by have := d.hm; omega), d.hcard] at hmul
  have : 3 ^ d.m = 27 * 3 ^ (d.m - 1 - 2) := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num, ← pow_add]; congr 1; have := d.hm; omega
  rw [this] at hmul
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) hmul).symm

theorem Q_center: Subgroup.center (P ⧸ d.L 2) = (d.L 1).map (QuotientGroup.mk' (d.L 2)) := by
  have hZ := card_center_of_maxClass (p := 3) (d.hP.to_quotient (d.L 2)) (m := 3) le_rfl
    (by rw [d.Q_card]; norm_num) (by
      intro h
      have h' : (⊤ : Subgroup (P ⧸ d.L 2)).lowerCentralSeries 1 = ⊥ := by simpa using h
      exact d.L1_ne_le_L2 (lcs_le_of_quotient_eq_bot (d.L 2) h'))
  have hle : (d.L 1).map (QuotientGroup.mk' (d.L 2)) ≤ Subgroup.center (P ⧸ d.L 2) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (d.L 2) q
    have h0 := d.comm_mem_L (j := 1) hu g
    have h1 : ((⁅u, g⁆ : P) : P ⧸ d.L 2) = 1 := (QuotientGroup.eq_one_iff _).mpr h0
    rw [commutatorElement_def] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    simp only [QuotientGroup.mk'_apply]
    exact h1.symm
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hZ]
  have hd : Nat.card ((d.L 1).map (QuotientGroup.mk' (d.L 2))) ∣ 3 := by
    rw [← hZ]; exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
  · exfalso
    rw [Subgroup.card_eq_one] at h1
    apply d.L1_ne_le_L2
    intro u hu
    have : QuotientGroup.mk' (d.L 2) u ∈ (d.L 1).map (QuotientGroup.mk' (d.L 2)) :=
      Subgroup.mem_map_of_mem _ hu
    rw [h1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  · rw [h1]

theorem mem_L1_of_comm_L2 {g : P} (hg : ∀ h : P, ⁅g, h⁆ ∈ d.L 2) : g ∈ d.L 1 := by
  have hc : (g : P ⧸ d.L 2) ∈ Subgroup.center (P ⧸ d.L 2) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (d.L 2) q
    have h1 : ((⁅g, h⁆ : P) : P ⧸ d.L 2) = 1 := (QuotientGroup.eq_one_iff _).mpr (hg h)
    rw [commutatorElement_def] at h1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    simp only [QuotientGroup.mk'_apply]
    exact h1.symm
  rw [d.Q_center] at hc
  obtain ⟨u, hu, hug⟩ := hc
  have : u⁻¹ * g ∈ d.L 2 := by
    rw [← QuotientGroup.eq]; exact hug
  have h2 : g = u * (u⁻¹ * g) := by group
  rw [h2]
  exact Subgroup.mul_mem _ hu (d.L_anti (by omega) this)

theorem card_quot_L1: Nat.card (P ⧸ d.L 1) = 9 := by
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.L 1)
  rw [d.card_L (j := 1) le_rfl (by have := d.hm; omega), d.hcard] at hmul
  have : 3 ^ d.m = 9 * 3 ^ (d.m - 1 - 1) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; have := d.hm; omega
  rw [this] at hmul
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) _) hmul).symm

theorem not_cyclic_quot: ¬ IsCyclic (P ⧸ d.L 1) := by
  intro hcyc
  let f : P ⧸ d.L 2 →* P ⧸ d.L 1 :=
    QuotientGroup.map (d.L 2) (d.L 1) (MonoidHom.id P) (by
      rw [Subgroup.comap_id]; exact d.L_anti (by omega))
  have hker : f.ker ≤ Subgroup.center (P ⧸ d.L 2) := by
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (d.L 2) q
    rw [MonoidHom.mem_ker] at hq
    have : g ∈ d.L 1 := by
      have h' : (f ((QuotientGroup.mk' (d.L 2)) g)) = ((g : P) : P ⧸ d.L 1) := rfl
      rw [h'] at hq
      exact (QuotientGroup.eq_one_iff _).mp hq
    rw [d.Q_center]
    exact Subgroup.mem_map_of_mem _ this
  have hcomm := f.isMulCommutative_of_isCyclic_of_ker_le_center hker
  have h1 : (⊤ : Subgroup (P ⧸ d.L 2)).lowerCentralSeries 1 = ⊥ :=
    lcs_one_eq_bot_of_comm (fun a b => hcomm.is_comm.comm a b)
  exact d.L1_ne_le_L2 (lcs_le_of_quotient_eq_bot (d.L 2) h1)

theorem pow_three_mem_L1 (g : P) : g ^ 3 ∈ d.L 1 := by
  have hcard := d.card_quot_L1
  have hord : orderOf (g : P ⧸ d.L 1) ∣ 9 := by
    rw [← hcard]; exact orderOf_dvd_natCard _
  have h3 : orderOf (g : P ⧸ d.L 1) ∣ 3 := by
    have : orderOf (g : P ⧸ d.L 1) ∣ 3 ^ 2 := by simpa using hord
    rcases (Nat.dvd_prime_pow Nat.prime_three).mp this with ⟨k, hk, hk'⟩
    interval_cases k
    · rw [hk']; simp
    · rw [hk']; simp
    · exfalso
      apply d.not_cyclic_quot
      exact isCyclic_of_orderOf_eq_card (g : P ⧸ d.L 1) (by rw [hk', hcard]; norm_num)
  have : (g : P ⧸ d.L 1) ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
  exact this

theorem card_H: Nat.card (d.L (d.m - 3)) = 9 := by
  rw [d.card_L (j := d.m - 3) (by have := d.hm; omega) (by omega)]
  rw [show d.m - 1 - (d.m - 3) = 2 by have := d.hm; omega]; norm_num

theorem exists_not_centralizes: ∃ a : P, ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a := by
  by_contra hno
  push Not at hno
  have hle : d.L (d.m - 3) ≤ Subgroup.center P := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro g
    exact hno g w hw
  have hd := Subgroup.card_dvd_of_le hle
  rw [d.card_H, d.card_center] at hd
  omega

theorem comm_mem_L1 (x y : P) : ⁅x, y⁆ ∈ d.L 1 := by
  show ⁅x, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries 1
  rw [Subgroup.top_lowerCentralSeries_one]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

theorem mk_L1_central {u : P} (hu : u ∈ d.L 1) (g : P ⧸ d.L 2) :
    (u : P ⧸ d.L 2) * g = g * (u : P ⧸ d.L 2) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (d.L 2) g
  have h0 := d.comm_mem_L (j := 1) hu h
  have h1 : ((⁅u, h⁆ : P) : P ⧸ d.L 2) = 1 := (QuotientGroup.eq_one_iff _).mpr h0
  rw [commutatorElement_def] at h1
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  simp only [QuotientGroup.mk'_apply]
  exact h1

theorem comm_mem_L2_iff (x g : P) :
    ⁅x, g⁆ ∈ d.L 2 ↔ (x : P ⧸ d.L 2) * (g : P ⧸ d.L 2) = (g : P ⧸ d.L 2) * (x : P ⧸ d.L 2) := by
  rw [← QuotientGroup.eq_one_iff]
  have h1 : ((⁅x, g⁆ : P) : P ⧸ d.L 2) = ⁅(x : P ⧸ d.L 2), (g : P ⧸ d.L 2)⁆ := by
    have := map_commutatorElement (QuotientGroup.mk' (d.L 2)) x g
    simpa only [QuotientGroup.mk'_apply] using this
  rw [h1, commutatorElement_eq_one_iff_mul_comm]

theorem exists_not_mem_both (D T : Subgroup P) (hD : D ≠ ⊤) (hT : T ≠ ⊤) :
    ∃ a : P, a ∉ D ∧ a ∉ T := by
  by_contra hno
  push Not at hno
  obtain ⟨a₁, ha₁⟩ : ∃ a, a ∉ D := by
    by_contra h; push Not at h; exact hD (eq_top_iff.mpr fun a _ => h a)
  obtain ⟨a₂, ha₂⟩ : ∃ a, a ∉ T := by
    by_contra h; push Not at h; exact hT (eq_top_iff.mpr fun a _ => h a)
  have h1 : a₁ ∈ T := hno a₁ ha₁
  have h2 : a₂ ∈ D := by by_contra h; exact ha₂ (hno a₂ h)
  by_cases h3 : a₁ * a₂ ∈ D
  · exact ha₁ (by simpa using D.mul_mem h3 (D.inv_mem h2))
  · have := hno _ h3
    exact ha₂ (by simpa using T.mul_mem (T.inv_mem h1) this)

end MB

namespace MC

variable {P : Type u} [Group P] [Finite P] (d : MC P)

include d

theorem L1_commutes_H {a : P} (ha : a ∈ d.L 1) {w : P} (hw : w ∈ d.L (d.m - 3)) :
    a * w = w * a :=
  d.abel a ha w (d.L_anti (by have := d.hm; omega) hw)

theorem fixed_le_center {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) :
    ∀ u ∈ d.L 1, a * u * a⁻¹ = u → u ∈ d.L (d.m - 2) := by
  have hm := d.hm
  set K : Subgroup P := d.L 1 ⊓ Subgroup.centralizer ({a} : Set P) with hK
  have hKnorm : K.Normal := by
    constructor
    intro u hu g
    have huA : u ∈ d.L 1 := hu.1
    have hua : a * u = u * a := (Subgroup.mem_centralizer_singleton_iff.mp hu.2).symm
    refine ⟨(d.L_normal 1).conj_mem u huA g, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hc : ⁅g⁻¹, a⁆ ∈ d.L 1 := d.comm_mem_L1 _ _
    have hgag : g⁻¹ * a * g = ⁅g⁻¹, a⁆ * a := by
      rw [commutatorElement_def]; group
    have hcu : ⁅g⁻¹, a⁆ * u = u * ⁅g⁻¹, a⁆ := d.abel _ hc u huA
    have key : g⁻¹ * a * g * u = u * (g⁻¹ * a * g) := by
      rw [hgag, mul_assoc, hua, ← mul_assoc, hcu, mul_assoc]
    calc g * u * g⁻¹ * a = g * (u * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * a * g * u) * g⁻¹ := by rw [key]
      _ = a * (g * u * g⁻¹) := by group
  have hKp : IsPGroup 3 K := d.hP.to_subgroup K
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp hKp
  have hKA : K ≤ d.L 1 := inf_le_left
  have hdvd := Subgroup.card_dvd_of_le hKA
  rw [hr, d.card_L (j := 1) le_rfl (by omega)] at hdvd
  have hrm : r ≤ d.m - 1 - 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hZK : d.L (d.m - 2) ≤ K := by
    refine le_inf (d.L_anti (by omega)) ?_
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : z ∈ Subgroup.center P := by rw [← d.L_center]; exact hz
    exact (Subgroup.mem_center_iff.mp this a).symm
  have hZcard : Nat.card (d.L (d.m - 2)) = 3 := by rw [d.L_center]; exact d.card_center
  have hr1 : r ≤ 1 := by
    by_contra hr2
    push Not at hr2
    obtain ⟨w, hw, hne⟩ := ha
    have := d.L_le_normal (N := K) (r := r) (by omega) (by omega) hr
    have hwK := this hw
    exact hne (Subgroup.mem_centralizer_singleton_iff.mp hwK.2).symm
  have hKZ : K = d.L (d.m - 2) := by
    refine (Subgroup.eq_of_le_of_card_ge hZK ?_).symm
    rw [hr, hZcard]
    have : 3 ^ r ≤ 3 := by
      calc 3 ^ r ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hr1
        _ = 3 := by norm_num
    exact this
  intro u hu hau
  have : u ∈ K := by
    refine ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc u * a = (a * u * a⁻¹) * a := by rw [hau]
      _ = a * u := by group
  rw [hKZ] at this
  exact this

theorem cube_central {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) :
    ∀ g : P, g * a ^ 3 = a ^ 3 * g := by
  have h1 : a ^ 3 ∈ d.L 1 := d.pow_three_mem_L1 a
  have h2 : a ^ 3 ∈ d.L (d.m - 2) := d.fixed_le_center ha _ h1 (by group)
  have : a ^ 3 ∈ Subgroup.center P := by rw [← d.L_center]; exact h2
  intro g
  exact Subgroup.mem_center_iff.mp this g

abbrev Mod : Type u := NMod (d.L 1) d.abel

theorem cube_central' {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) :
    ∀ g : P, g * (a * a * a) = (a * a * a) * g := by
  intro g
  have := d.cube_central ha g
  rwa [show a ^ 3 = a * a * a by rw [pow_succ, pow_succ, pow_one]] at this

theorem rho_cube {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (u : d.Mod) :
    conjEnd a (conjEnd a (conjEnd a u)) = u := by
  apply NMod.toP_injective
  simp only [toP_conjEnd]
  have e : a * (a * (a * u.toP * a⁻¹) * a⁻¹) * a⁻¹ = (a * a * a) * u.toP * (a * a * a)⁻¹ := by
    group
  rw [e, ← d.cube_central' ha u.toP]
  group

theorem nrho1 {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (w : d.Mod) :
    (1 + conjEnd a + conjEnd a * conjEnd a : Module.End ℤ d.Mod)
      ((conjEnd a - 1 : Module.End ℤ d.Mod) w) = 0 := by
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply,
    LinearMap.sub_apply, map_sub]
  rw [d.rho_cube ha w]
  abel

theorem nrho2 {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (k : P) :
    (1 + conjEnd a + conjEnd a * conjEnd a : Module.End ℤ d.Mod)
      (NMod.ofP (hN := d.abel) ⁅k, a⁆ (d.comm_mem_L1 k a)) = 0 := by
  apply NMod.toP_injective
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, NMod.toP_add,
    toP_conjEnd, NMod.toP_ofP, NMod.toP_zero]
  have e : ⁅k, a⁆ * (a * ⁅k, a⁆ * a⁻¹) * (a * (a * ⁅k, a⁆ * a⁻¹) * a⁻¹) =
      (k * (a * a * a) * k⁻¹) * (a * a * a)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e, show k * (a * a * a) = (a * a * a) * k from d.cube_central' ha k]
  group

theorem hcomm_mem' (g : P) (j : ℕ) (u : d.Mod) (hu : u ∈ GS (N := d.L 1) (hN := d.abel) (d.L j)) :
    (conjEnd g - 1 : Module.End ℤ d.Mod) u ∈ GS (N := d.L 1) (hN := d.abel) (d.L (j + 1)) := by
  rw [mem_GS, toP_conjEnd_sub, ← commutatorElement_inv]
  exact Subgroup.inv_mem _ (d.comm_mem_L (mem_GS.mp hu) g)

theorem hker' {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (u : d.Mod)
    (hu : (conjEnd a - 1 : Module.End ℤ d.Mod) u = 0) :
    u ∈ GS (N := d.L 1) (hN := d.abel) (d.L (d.m - 1 - 1)) := by
  have hm := d.hm
  rw [mem_GS, show d.m - 1 - 1 = d.m - 2 by omega]
  have h1 : ⁅a, u.toP⁆ = 1 := by rw [← toP_conjEnd_sub, hu]; exact NMod.toP_zero
  have h2 : a * u.toP * a⁻¹ = u.toP := by
    rw [commutatorElement_def] at h1
    exact mul_inv_eq_one.mp h1
  exact d.fixed_le_center ha u.toP u.toP_mem h2

theorem hbotG (j : ℕ) (hj : d.m - 1 ≤ j) :
    GS (N := d.L 1) (hN := d.abel) (d.L j) = ⊥ := by
  ext u
  rw [mem_GS, d.L_bot hj, Subgroup.mem_bot, AddSubgroup.mem_bot]
  constructor
  · intro h; exact NMod.toP_injective (h.trans NMod.toP_zero.symm)
  · intro h; rw [h]; exact NMod.toP_zero

theorem hG1: GS (N := d.L 1) (hN := d.abel) (d.L 1) = ⊤ := by
  ext u
  simp only [mem_GS, AddSubgroup.mem_top, iff_true]
  exact u.toP_mem

noncomputable def core0 (a k : P) (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a)
    (hk : ⁅k, a⁆ ∉ d.L 2) : Core0 d.Mod :=
  { ρ := conjEnd a
    G := fun j => GS (d.L j)
    n := d.m - 1
    y := NMod.ofP (hN := d.abel) ⁅k, a⁆ (d.comm_mem_L1 k a)
    hn := by have := d.hm; omega
    G1 := d.hG1
    anti := fun j _ u hu => mem_GS.mpr (d.L_anti (Nat.le_succ j) (mem_GS.mp hu))
    card := fun j hj hjn => by
      show Nat.card (GS (d.L j)) = 3 ^ (d.m - 1 - j)
      rw [card_GS (d.L_anti hj), d.card_L hj hjn]
    bot := fun j hj => d.hbotG j hj
    hρ := fun j _ u hu => d.hcomm_mem' a j u hu
    ker := fun u hu => d.hker' ha u hu
    nρ1 := fun w => d.nrho1 ha w
    nρ2 := d.nrho2 ha k
    hy := fun h => hk (mem_GS.mp h) }

theorem card_le_nine_of_le_L1 {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) {k : P}
    (hk : ⁅k, a⁆ ∉ d.L 2) (F : Subgroup P) (hF : F ≤ d.L 1) (hexp : ∀ u ∈ F, u ^ 3 = 1) :
    Nat.card F ≤ 9 := by
  have c0 := d.core0 a k ha hk
  have h9 := c0.card_ker_triple
  refine le_of_le_of_eq (Nat.card_le_card_of_injective
    (fun u : F => (⟨NMod.ofP (hN := d.abel) u.1 (hF u.2), ?_⟩ : (Core0.triple d.Mod).ker)) ?_) h9
  · rw [AddMonoidHom.mem_ker, Core0.triple_apply]
    apply NMod.toP_injective
    have h3 : ((3 : ℤ) • (NMod.ofP (hN := d.abel) u.1 (hF u.2) : d.Mod)) =
        (3 : ℕ) • (NMod.ofP (hN := d.abel) u.1 (hF u.2) : d.Mod) := by
      simpa using natCast_zsmul (NMod.ofP (hN := d.abel) u.1 (hF u.2) : d.Mod) 3
    rw [h3, NMod.toP_nsmul, NMod.toP_ofP, NMod.toP_zero]
    exact hexp u.1 u.2
  · intro u v huv
    have := congrArg (fun z : (Core0.triple d.Mod).ker => NMod.toP (z : d.Mod)) huv
    simp only [NMod.toP_ofP] at this
    exact Subtype.ext this

theorem comm_conj {a : P} (x : P) : (conjEnd a * conjEnd x : Module.End ℤ d.Mod) =
    conjEnd x * conjEnd a := by
  ext u
  apply NMod.toP_injective
  simp only [Module.End.mul_apply, toP_conjEnd]
  have hc : ⁅a, x⁆ ∈ d.L 1 := d.comm_mem_L1 a x
  have hv : x * (a * u.toP * a⁻¹) * x⁻¹ ∈ d.L 1 :=
    (d.L_normal 1).conj_mem _ ((d.L_normal 1).conj_mem _ u.toP_mem a) x
  have hax : a * x = ⁅a, x⁆ * (x * a) := by rw [commutatorElement_def]; group
  have hcv : ⁅a, x⁆ * (x * (a * u.toP * a⁻¹) * x⁻¹) = (x * (a * u.toP * a⁻¹) * x⁻¹) * ⁅a, x⁆ :=
    d.abel _ hc _ hv
  calc a * (x * u.toP * x⁻¹) * a⁻¹ = (a * x) * u.toP * (a * x)⁻¹ := by group
    _ = ⁅a, x⁆ * (x * (a * u.toP * a⁻¹) * x⁻¹) * ⁅a, x⁆⁻¹ := by rw [hax]; group
    _ = x * (a * u.toP * a⁻¹) * x⁻¹ := mul_inv_eq_iff_eq_mul.mpr hcv

theorem nf_conj {a : P} (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) {x : P} (hx3 : x ^ 3 = 1) :
    (1 + conjEnd x + conjEnd x * conjEnd x : Module.End ℤ d.Mod)
      (NMod.ofP (hN := d.abel) ⁅x, a⁆ (d.comm_mem_L1 x a)) = 0 := by
  have hx3' : x * x * x = 1 := by rw [← hx3, pow_succ, pow_succ, pow_one]
  have hrev : (1 + conjEnd x + conjEnd x * conjEnd x : Module.End ℤ d.Mod)
      (NMod.ofP (hN := d.abel) ⁅x, a⁆ (d.comm_mem_L1 x a)) =
      conjEnd x (conjEnd x (NMod.ofP (hN := d.abel) ⁅x, a⁆ (d.comm_mem_L1 x a))) +
      conjEnd x (NMod.ofP (hN := d.abel) ⁅x, a⁆ (d.comm_mem_L1 x a)) +
      NMod.ofP (hN := d.abel) ⁅x, a⁆ (d.comm_mem_L1 x a) := by
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply]
    abel
  rw [hrev]
  apply NMod.toP_injective
  simp only [NMod.toP_add, toP_conjEnd, NMod.toP_ofP, NMod.toP_zero]
  have e : (x * (x * ⁅x, a⁆ * x⁻¹) * x⁻¹) * (x * ⁅x, a⁆ * x⁻¹) * ⁅x, a⁆ =
      (x * x * x) * (a * (x * x * x)⁻¹ * a⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e, hx3']
  group

theorem fx_conj {x : P} (hxH : ∀ w ∈ d.L (d.m - 3), x * w = w * x) (u : d.Mod)
    (hu : u ∈ GS (N := d.L 1) (hN := d.abel) (d.L (d.m - 1 - 2))) : conjEnd x u = u := by
  have hm := d.hm
  rw [show d.m - 1 - 2 = d.m - 3 by omega] at hu
  apply NMod.toP_injective
  simp only [toP_conjEnd]
  rw [mul_inv_eq_iff_eq_mul]
  exact hxH _ (mem_GS.mp hu)

noncomputable def core (a x : P) (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (hx3 : x ^ 3 = 1)
    (hxH : ∀ w ∈ d.L (d.m - 3), x * w = w * x) (hy : ⁅x, a⁆ ∉ d.L 2) : Core d.Mod :=
  { toCore0 := d.core0 a x ha hy
    f := conjEnd x
    hf := fun j _ u hu => d.hcomm_mem' x j u hu
    comm := d.comm_conj x
    nf := d.nf_conj ha hx3
    fx := fun u hu => d.fx_conj hxH u hu }

theorem false_of_data (a x : P) (ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) (hx3 : x ^ 3 = 1)
    (hxH : ∀ w ∈ d.L (d.m - 3), x * w = w * x) (hy : ⁅x, a⁆ ∉ d.L 2) : False :=
  (d.core a x ha hx3 hxH hy).false_aux

theorem no_abelian_complement (E : Subgroup P) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsurj : ∀ g : P, ∃ e ∈ E, ∃ u ∈ d.L 1, g = e * u) : False := by
  apply d.L1_ne_le_L2
  have hL1 : d.L 1 = ⁅(⊤ : Subgroup P), ⊤⁆ := Subgroup.top_lowerCentralSeries_one
  rw [hL1]
  refine Subgroup.commutator_le.mpr ?_
  intro g _ h _
  obtain ⟨e, he, u, hu, rfl⟩ := hsurj g
  obtain ⟨e', he', u', hu', rfl⟩ := hsurj h
  rw [← QuotientGroup.eq_one_iff]
  have h1 : ((⁅e * u, e' * u'⁆ : P) : P ⧸ d.L 2) =
      ⁅((e : P ⧸ d.L 2) * (u : P ⧸ d.L 2)), ((e' : P ⧸ d.L 2) * (u' : P ⧸ d.L 2))⁆ := by
    have := map_commutatorElement (QuotientGroup.mk' (d.L 2)) (e * u) (e' * u')
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul] at this
    exact this
  rw [h1, comm_central_mul _ _ _ _ (fun q => d.mk_L1_central hu q)
    (fun q => d.mk_L1_central hu' q)]
  apply commutatorElement_eq_one_iff_mul_comm.mpr
  have := congrArg (fun z : P => (z : P ⧸ d.L 2)) (hE e he e' he')
  simp only [QuotientGroup.mk_mul] at this
  exact this

theorem card_le_three_mul_inf (E : Subgroup P) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ d.L 1 : Subgroup P) := by
  let ψ : E →* P ⧸ d.L 1 := (QuotientGroup.mk' (d.L 1)).comp E.subtype
  have hmul := Subgroup.card_ker_mul_card_range ψ
  have hker : Nat.card ψ.ker ≤ Nat.card (E ⊓ d.L 1 : Subgroup P) := by
    refine Nat.card_le_card_of_injective
      (fun u => (⟨(u : E).1, (u : E).2, ?_⟩ : (E ⊓ d.L 1 : Subgroup P))) ?_
    · have := u.2
      rw [MonoidHom.mem_ker] at this
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro a b hab
      have := congrArg (fun z : (E ⊓ d.L 1 : Subgroup P) => (z : P)) hab
      exact Subtype.ext (Subtype.ext this)
  have hdvd : Nat.card ψ.range ∣ 9 := by
    rw [← d.card_quot_L1]; exact Subgroup.card_subgroup_dvd_card _
  have hr3 : Nat.card ψ.range ≤ 3 := by
    by_contra hgt
    push Not at hgt
    have h9 : Nat.card ψ.range = 9 := by
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have : Nat.card ψ.range ∣ 3 ^ 2 := by simpa using hdvd
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp this with ⟨k, hk, hk'⟩
      interval_cases k
      · rw [hk'] at hgt; simp at hgt
      · rw [hk'] at hgt; simp at hgt
      · rw [hk']; norm_num
    have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h9, d.card_quot_L1])
    apply d.no_abelian_complement E hE
    intro g
    have : ((g : P) : P ⧸ d.L 1) ∈ ψ.range := by rw [htop]; trivial
    obtain ⟨e, he⟩ := this
    refine ⟨e.1, e.2, e.1⁻¹ * g, ?_, by group⟩
    have he' : ((e.1 : P) : P ⧸ d.L 1) = (g : P ⧸ d.L 1) := he
    rw [QuotientGroup.eq] at he'
    exact he'
  calc Nat.card E = Nat.card ψ.ker * Nat.card ψ.range := hmul.symm
    _ ≤ Nat.card (E ⊓ d.L 1 : Subgroup P) * 3 := Nat.mul_le_mul hker hr3
    _ = 3 * Nat.card (E ⊓ d.L 1 : Subgroup P) := mul_comm _ _

def W : Subgroup P where
  carrier := {u | u ∈ d.L 1 ∧ u ^ 3 = 1}
  one_mem' := ⟨(d.L 1).one_mem, one_pow 3⟩
  mul_mem' := fun {u v} hu hv => ⟨(d.L 1).mul_mem hu.1 hv.1, by
    rw [(show Commute u v from d.abel u hu.1 v hv.1).mul_pow, hu.2, hv.2, one_mul]⟩
  inv_mem' := fun {u} hu => ⟨(d.L 1).inv_mem hu.1, by rw [inv_pow, hu.2, inv_one]⟩

instance W_normal: (d.W).Normal where
  conj_mem := fun u hu g => ⟨(d.L_normal 1).conj_mem u hu.1 g, by
    rw [conj_pow, hu.2]; simp⟩

theorem W_le: d.W ≤ d.L 1 := fun _ hu => hu.1

theorem exists_regular_pair: ∃ a k : P, (∃ w ∈ d.L (d.m - 3), a * w ≠ w * a) ∧ ⁅k, a⁆ ∉ d.L 2 := by
  obtain ⟨a, w, hw, hne⟩ := d.exists_not_centralizes
  have haL : a ∉ d.L 1 := fun h => hne (d.L1_commutes_H h hw)
  have : ¬ ∀ h : P, ⁅a, h⁆ ∈ d.L 2 := fun h => haL (d.mem_L1_of_comm_L2 h)
  push Not at this
  obtain ⟨k, hk⟩ := this
  refine ⟨a, k, ⟨w, hw, hne⟩, fun h => hk ?_⟩
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ h

theorem card_le_nine_L1 (F : Subgroup P) (hF : F ≤ d.L 1) (hexp : ∀ u ∈ F, u ^ 3 = 1) :
    Nat.card F ≤ 9 := by
  obtain ⟨a, k, ha, hk⟩ := d.exists_regular_pair
  exact d.card_le_nine_of_le_L1 ha hk F hF hexp

theorem card_le_nine (E : Subgroup P) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hexp : ∀ u ∈ E, u ^ 3 = 1) : Nat.card E ≤ 9 := by
  have hm := d.hm
  by_contra hgt
  push Not at hgt
  have h27 : 27 ≤ Nat.card E := by
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp (d.hP.to_subgroup E)
    rw [hr] at hgt ⊢
    by_contra hlt
    push Not at hlt
    have : r ≤ 2 := by
      by_contra h2
      push Not at h2
      have : 3 ^ 3 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) h2
      omega
    have : 3 ^ r ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  set F : Subgroup P := E ⊓ d.L 1 with hF
  have hFcard : 9 ≤ Nat.card F := by
    have h := d.card_le_three_mul_inf E hE
    rw [← hF] at h
    omega
  have hFW : F ≤ d.W := fun u hu => ⟨hu.2, hexp u hu.1⟩
  have hW9 : Nat.card d.W ≤ 9 :=
    d.card_le_nine_L1 d.W d.W_le fun u hu => hu.2
  have hWF : F = d.W := Subgroup.eq_of_le_of_card_ge hFW (by
    have : Nat.card F ≤ Nat.card d.W := Nat.card_le_card_of_injective (Subgroup.inclusion hFW)
      (Subgroup.inclusion_injective hFW)
    omega)
  have hWcard : Nat.card d.W = 9 := by
    have : Nat.card F ≤ Nat.card d.W := Nat.card_le_card_of_injective (Subgroup.inclusion hFW)
      (Subgroup.inclusion_injective hFW)
    omega
  have hHW : d.L (d.m - 3) ≤ d.W :=
    d.L_le_normal (N := d.W) (r := 2) le_rfl (by omega) (by rw [hWcard]; norm_num)
  have hHeqW : d.L (d.m - 3) = d.W := Subgroup.eq_of_le_of_card_ge hHW (by
    rw [d.card_H, hWcard])
  obtain ⟨x, hxE, hxL⟩ : ∃ x ∈ E, x ∉ d.L 1 := by
    by_contra hno
    push Not at hno
    have hle : E ≤ d.L 1 := fun u hu => hno u hu
    have := d.card_le_nine_L1 E hle hexp
    omega
  have hxH : ∀ w ∈ d.L (d.m - 3), x * w = w * x := by
    intro w hw
    have hwW : w ∈ d.W := hHW hw
    have hwF : w ∈ F := by rw [hWF]; exact hwW
    exact hE x hxE w hwF.1
  have hx3 : x ^ 3 = 1 := hexp x hxE
  set D : Subgroup P := Subgroup.centralizer (d.L (d.m - 3) : Set P) with hD
  have hDtop : D ≠ ⊤ := by
    obtain ⟨a, w, hw, hne⟩ := d.exists_not_centralizes
    intro h
    have : a ∈ D := by rw [h]; trivial
    rw [hD, Subgroup.mem_centralizer_iff] at this
    exact hne (this w hw).symm
  set T : Subgroup P := (Subgroup.centralizer ({(x : P ⧸ d.L 2)} : Set (P ⧸ d.L 2))).comap
    (QuotientGroup.mk' (d.L 2)) with hT
  have hmemT : ∀ g : P, g ∈ T ↔ ⁅x, g⁆ ∈ d.L 2 := by
    intro g
    rw [d.comm_mem_L2_iff, hT, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    simp only [QuotientGroup.mk'_apply]
    exact eq_comm
  have hTtop : T ≠ ⊤ := by
    intro h
    apply hxL
    apply d.mem_L1_of_comm_L2
    intro g
    exact (hmemT g).mp (by rw [h]; trivial)
  obtain ⟨a, haD, haT⟩ := d.exists_not_mem_both D T hDtop hTtop
  have ha : ∃ w ∈ d.L (d.m - 3), a * w ≠ w * a := by
    rw [hD, Subgroup.mem_centralizer_iff] at haD
    push Not at haD
    obtain ⟨w, hw, hne⟩ := haD
    exact ⟨w, hw, fun h => hne h.symm⟩
  exact d.false_of_data a x ha hx3 hxH (fun h => haT ((hmemT a).mpr h))

end MC

end CFSG.HardMathSupport.Lang.E6Descent
