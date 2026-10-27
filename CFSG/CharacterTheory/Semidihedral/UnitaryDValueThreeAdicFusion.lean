module

public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueThreeAdicQ
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueStep

public section

namespace CFSG.Semidihedral.UnitaryDValue

theorem card_centralizer_conj {G : Type*} [Group G] (g a : G) :
    Nat.card (Subgroup.centralizer {g * a * g⁻¹}) = Nat.card (Subgroup.centralizer {a}) := by
  have h : (Subgroup.centralizer {a}).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {g * a * g⁻¹} := by
    ext c
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      calc g * b * g⁻¹ * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
        _ = g * (a * b) * g⁻¹ := by rw [hb]
        _ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
    · intro hc
      refine ⟨g⁻¹ * c * g, ?_, by group⟩
      calc g⁻¹ * c * g * a = g⁻¹ * (c * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹ * c) * g := by rw [hc]
        _ = a * (g⁻¹ * c * g) := by group
  rw [← h]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem exists_conj_mem_primaryPart_three (h3 : 3 ∣ D.q + 1) {w : G}
    (hw : ∃ k : ℕ, orderOf w = 3 ^ k) {i : G} (hi : orderOf i = 2) (hiw : i * w = w * i) :
    ∃ g : G, g * w * g⁻¹ ∈ D.primaryPart 3 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (D.involution_conj i hi)
  have hcw : c * w * c⁻¹ ∈ D.N := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    calc c * w * c⁻¹ * (c * i * c⁻¹) = c * (w * i) * c⁻¹ := by group
      _ = c * (i * w) * c⁻¹ := by rw [hiw]
      _ = c * i * c⁻¹ * (c * w * c⁻¹) := by group
  have hPN : D.primaryPart 3 ≤ D.N := fun u hu => D.C_le_N (D.primaryPart_le_C 3 hu)
  have hcard : Nat.card ((D.primaryPart 3).subgroupOf D.N) =
      3 ^ (Nat.card D.N).factorization 3 := by
    rw [card_subgroupOf_of_le' hPN, D.card_primaryPart_odd (by norm_num),
      D.factorization_card_N Nat.prime_three (by norm_num) h3]
  let Q₀ : Sylow 3 D.N := Sylow.ofCard _ hcard
  obtain ⟨k, hk⟩ := hw
  have hp : IsPGroup 3 (Subgroup.zpowers (⟨c * w * c⁻¹, hcw⟩ : D.N)) := by
    apply IsPGroup.of_card (n := k)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_conj_eq, hk]
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq D.N R Q₀
  have hmem : (⟨c * w * c⁻¹, hcw⟩ : D.N) ∈ (R : Subgroup D.N) := hR (Subgroup.mem_zpowers _)
  have h2 : n * ⟨c * w * c⁻¹, hcw⟩ * n⁻¹ ∈ (Q₀ : Subgroup D.N) := by
    rw [← hn, Sylow.coe_subgroup_smul]
    exact ⟨_, hmem, rfl⟩
  rw [Sylow.coe_ofCard] at h2
  refine ⟨n * c, ?_⟩
  have h3' : ((n * ⟨c * w * c⁻¹, hcw⟩ * n⁻¹ : D.N) : G) ∈ D.primaryPart 3 := h2
  convert h3' using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  group

namespace Exceptional

variable {D} (E : D.Exceptional)

theorem not_comm_commutator :
    ¬ (D.t * (D.t * E.u₀ * D.t⁻¹ * E.u₀⁻¹) = (D.t * E.u₀ * D.t⁻¹ * E.u₀⁻¹) * D.t) := by
  intro hc
  have hX : D.t * E.u₀ * D.t⁻¹ * E.u₀⁻¹ = E.u₀ ^ (E.l * E.s₀) * E.u₁ ^ (1 : ℤ) := by
    have e : E.u₀⁻¹ = E.u₀ ^ (-1 : ℤ) * E.u₁ ^ (0 : ℤ) := by rw [zpow_zero, mul_one, zpow_neg_one]
    rw [E.ht₀', e, zpow_mul_zpow_mul_zpow_mul_zpow E.comm,
      show (1 + E.l * E.s₀) + -1 = E.l * E.s₀ by ring, show (1 : ℤ) + 0 = 1 by ring]
  have h1 := conj_eq_of_comm hc
  rw [hX, E.t_conj, E.coord] at h1
  have e : (1 + E.l * E.s₀) * (E.l * E.s₀) + -(E.l * E.s₀) * 1 - E.l * E.s₀ =
      E.l * (E.s₀ * (E.l * E.s₀ - 1)) := by ring
  have h2 := h1.1
  rw [e, ← E.three_mul_l, mul_comm (3 : ℤ)] at h2
  have h3 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp h2
  rcases Int.prime_three.dvd_or_dvd h3 with h4 | h4
  · exact E.hs₀ h4
  · have h5 : (3 : ℤ) ∣ E.l * E.s₀ := dvd_mul_of_dvd_left E.three_dvd_l _
    have h6 := dvd_sub h5 h4
    rw [show E.l * E.s₀ - (E.l * E.s₀ - 1) = 1 by ring] at h6
    exact absurd (Int.eq_one_of_dvd_one (by norm_num) h6) (by norm_num)

theorem centralizer_le_normalizer_T (hgw : D.GWStep) {z : G} (hz : z ∈ E.Z) (hz1 : z ≠ 1) :
    Subgroup.centralizer {z} ≤ Subgroup.normalizer (D.T : Set G) := by
  rcases hgw z (E.Z_le_W hz) hz1 (E.Z_le_P hz).2 (E.t_comm_Z hz) with h | h
  · exact h
  · exact absurd (h E.u₀ E.u₀_mem_C E.u₀_mem_P.2) E.not_comm_commutator

abbrev w₀ : G := E.u₀ ^ (3 ^ (E.h - 1))

theorem w₀_mem_Z : E.w₀ ∈ E.Z := by
  have hh := E.three_le_h
  refine Subgroup.mem_zpowers_iff.mpr ⟨(3 ^ (E.h - 2) : ℕ), ?_⟩
  rw [zpow_natCast, ← pow_mul, ← pow_succ', show E.h - 2 + 1 = E.h - 1 by omega]

theorem w₀_ne_one : E.w₀ ≠ 1 := by
  intro h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [E.hu₀o, ← E.h_def] at h2
  have h3 := Nat.le_of_dvd (by positivity) h2
  have h4 : 3 ^ (E.h - 1) < 3 ^ E.h := Nat.pow_lt_pow_right (by norm_num) (by
    have := E.three_le_h; omega)
  omega

theorem w₀_cube : E.w₀ ^ 3 = 1 := by
  rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by have := E.three_le_h; omega), E.h_def,
    ← E.hu₀o, pow_orderOf_eq_one]

theorem w₀_mem_W : E.w₀ ∈ D.W := D.W.pow_mem E.u₀_mem_W _

include E in
theorem mem_C_of_centralizes_P {g : G} (hg : ∀ u ∈ D.primaryPart 3, g * u = u * g) :
    g ∈ D.C := by
  have hu₁1 : E.u₁ ≠ 1 := by
    intro h
    have := E.hu₁o
    rw [h, orderOf_one] at this
    omega
  have hgN : g ∈ D.N :=
    D.A_confine _ E.u₁_mem_A hu₁1 (Subgroup.mem_centralizer_singleton_iff.mpr
      (hg _ E.u₁_mem_P))
  have hu₀1 : E.u₀ ≠ 1 := by
    intro h
    have := E.hu₀o
    rw [h, orderOf_one] at this
    have h1 : 1 < 3 ^ (D.q + 1).factorization 3 := Nat.one_lt_pow (by
      have := E.three_le_h; rw [E.h_def] at this; omega) (by norm_num)
    omega
  have hgz := D.W_centralizer _ E.u₀_mem_W hu₀1
    ⟨hgN, Subgroup.mem_centralizer_singleton_iff.mpr (hg _ E.u₀_mem_P)⟩
  exact ⟨hgN, hgz⟩

include E in
theorem normalizer_P_le {g : G} (hg : g ∈ Subgroup.normalizer (D.primaryPart 3 : Set G)) :
    g ∈ Subgroup.normalizer (D.T : Set G) := by
  have hgP : ∀ u ∈ D.primaryPart 3, g⁻¹ * u * g ∈ D.primaryPart 3 := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) u).mp hu
    simpa using this
  have hgC : ∀ c ∈ D.C, g * c * g⁻¹ ∈ D.C := by
    intro c hc
    apply E.mem_C_of_centralizes_P
    intro u hu
    have h1 := D.C_comm c hc _ (D.primaryPart_le_C 3 (hgP u hu))
    calc g * c * g⁻¹ * u = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by rw [h1]
      _ = u * (g * c * g⁻¹) := by group
  apply D.normalizer_U_le
  apply mem_normalizer_of_conj_mem_of_finite
  intro u hu
  exact ⟨hgC u hu.1, hu.2.imp fun k hk => by rw [orderOf_conj_eq, hk]⟩

theorem u₀_cube_inv_ne : (E.u₀ ^ 3)⁻¹ ≠ E.u₀ ^ 3 := by
  intro h
  have h2 : (E.u₀ ^ 3) ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [← h]
    exact inv_mul_cancel _
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [E.orderOf_u₀_cube] at h3
  have h4 := Nat.le_of_dvd (by norm_num) h3
  have h5 : 3 ^ 2 ≤ 3 ^ (E.h - 1) := Nat.pow_le_pow_right (by norm_num) (by
    have := E.three_le_h; omega)
  omega

include E in
theorem mem_CT_of_three_element {g : G} (hg : g ∈ Subgroup.normalizer (D.T : Set G))
    {a : ℕ} (hga : orderOf g = 3 ^ a) : g ∈ D.CT := by
  obtain ⟨i, j, -, hj, hc⟩ := D.normalizer_T_cases hg
  have hg' : g = D.t ^ i * D.y ^ j * ((D.t ^ i * D.y ^ j)⁻¹ * g) := by group
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · have hc' : (D.t ^ i)⁻¹ * g ∈ D.C := by simpa using hc
    have ht : D.t ∈ D.CT := ⟨1, D.C.one_mem, 1, by simp⟩
    have hg'' : g = D.t ^ i * ((D.t ^ i)⁻¹ * g) := by group
    rw [hg'']
    exact mul_mem (pow_mem ht i) (D.C_le_CT hc')
  · exfalso
    have hc1 : (D.t ^ i * D.y)⁻¹ * g ∈ D.C := by simpa using hc
    have hg1 : g = D.t ^ i * (D.y * ((D.t ^ i * D.y)⁻¹ * g)) := by group
    have hz : g * E.u₀ ^ 3 * g⁻¹ = (E.u₀ ^ 3)⁻¹ := by
      rw [hg1, conj_mul_eq, conj_mul_eq,
        D.C_conj hc1 (E.Z_le_C E.u₀_cube_mem_Z), D.y_W _ (E.Z_le_W E.u₀_cube_mem_Z)]
      exact conj_eq_of_comm ((Commute.pow_left
        (E.t_comm_Z ((E.Z).inv_mem E.u₀_cube_mem_Z) : Commute D.t _) i).eq)
    have heven := even_orderOf_of_conj_eq_inv hz (by
      intro h2
      apply E.u₀_cube_inv_ne
      rw [pow_two] at h2
      exact (eq_inv_of_mul_eq_one_left h2).symm)
    rw [hga] at heven
    exact (Nat.not_even_iff_odd.mpr (Odd.pow (by decide))) heven

theorem mem_Z_of_t_zpow_fix {p : G} (hp : p ∈ D.primaryPart 3) {i : ℤ} (hi : ¬ (3 : ℤ) ∣ i)
    (hfix : D.t ^ i * p * (D.t ^ i)⁻¹ = p) : p ∈ E.Z := by
  have hn : ¬ 3 ∣ i.natAbs := fun h => hi (Int.natCast_dvd.mpr h)
  have hfix' : D.t ^ i.natAbs * p * (D.t ^ i.natAbs)⁻¹ = p := by
    rcases Int.natAbs_eq i with h | h
    · rw [h, zpow_natCast] at hfix
      exact hfix
    · rw [h, zpow_neg, zpow_natCast, inv_inv] at hfix
      calc D.t ^ i.natAbs * p * (D.t ^ i.natAbs)⁻¹
          = D.t ^ i.natAbs * ((D.t ^ i.natAbs)⁻¹ * p * D.t ^ i.natAbs) *
              (D.t ^ i.natAbs)⁻¹ := by rw [hfix]
        _ = p := by group
  exact E.mem_Z_of_t_pow_fix hp hn hfix'

theorem eq_P_of_isPGroup {u : G} (hu : u ∈ D.primaryPart 3) (huZ : u ∉ E.Z)
    {R : Subgroup G} (hR : IsPGroup 3 R) (hPR : D.primaryPart 3 ≤ R)
    (hRu : R ≤ Subgroup.centralizer {u}) : R = D.primaryPart 3 := by
  by_contra hne
  have hlt : (D.primaryPart 3).subgroupOf R < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm (fun r hr => ?_) hPR
    have : (⟨r, hr⟩ : R) ∈ (D.primaryPart 3).subgroupOf R := by rw [htop]; exact Subgroup.mem_top _
    exact this
  have := hR.isNilpotent
  obtain ⟨r, hrN, hrP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent ((D.primaryPart 3).subgroupOf R) hlt)
  apply hrP
  have hrG : (r : G) ∈ Subgroup.normalizer (D.primaryPart 3 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [Subgroup.mem_normalizer_iff] at hrN
    constructor
    · intro hw
      exact (hrN ⟨w, hPR hw⟩).mp hw
    · intro hw
      have hwR : w ∈ R := by
        have e : w = (r : G)⁻¹ * ((r : G) * w * (r : G)⁻¹) * r := by group
        rw [e]
        exact R.mul_mem (R.mul_mem (R.inv_mem r.2) (hPR hw)) r.2
      exact (hrN ⟨w, hwR⟩).mpr hw
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR) r
  rw [← Subgroup.orderOf_coe] at hk
  have hrCT := E.mem_CT_of_three_element (E.normalizer_P_le hrG) hk
  obtain ⟨c, hc, i, hci⟩ := hrCT
  have hru : (r : G) * u * (r : G)⁻¹ = u :=
    conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp (hRu r.2))
  have hti : D.t ^ i * u * (D.t ^ i)⁻¹ = u := by
    have hcu : c⁻¹ * u * c⁻¹⁻¹ = u := D.C_conj (D.C.inv_mem hc) (D.primaryPart_le_C 3 hu)
    calc D.t ^ i * u * (D.t ^ i)⁻¹ = c⁻¹ * ((r : G) * u * (r : G)⁻¹) * c⁻¹⁻¹ := by
          rw [hci]; group
      _ = u := by rw [hru, hcu]
  by_cases h3 : (3 : ℤ) ∣ i
  ·
    obtain ⟨m, rfl⟩ := h3
    have hrC : (r : G) ∈ D.C := by
      rw [hci, zpow_mul]
      refine D.C.mul_mem hc (D.C.zpow_mem ?_ m)
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact D.t_cube_mem_C
    show (r : G) ∈ D.primaryPart 3
    exact ⟨hrC, k, hk⟩
  · exact absurd (E.mem_Z_of_t_zpow_fix hu h3 hti) huZ

include E in
theorem exists_sylow_le_QT {u : G} (hu : u ∈ D.primaryPart 3) :
    ∃ R : Sylow 3 (Subgroup.centralizer ({u} : Set G)),
      ∀ g ∈ (R : Subgroup (Subgroup.centralizer ({u} : Set G))), (g : G) ∈ D.QT := by
  by_cases huZ : u ∈ E.Z
  · have hle : ((D.sylowQT E.three_dvd_q : Sylow 3 G) : Subgroup G) ≤
        Subgroup.centralizer {u} := by
      rw [D.coe_sylowQT]
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact E.Z_comm_QT huZ hg
    refine ⟨(D.sylowQT E.three_dvd_q).subtype hle, fun g hg => ?_⟩
    rw [Sylow.coe_subtype] at hg
    have : (g : G) ∈ ((D.sylowQT E.three_dvd_q : Sylow 3 G) : Subgroup G) := hg
    rwa [D.coe_sylowQT] at this
  · have hPu : D.primaryPart 3 ≤ Subgroup.centralizer {u} := by
      intro g hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact D.C_comm _ (D.primaryPart_le_C 3 hg) _ (D.primaryPart_le_C 3 hu)
    refine ⟨{ toSubgroup := (D.primaryPart 3).subgroupOf (Subgroup.centralizer {u})
              isPGroup' := (D.isPGroup_primaryPart 3).comap_of_injective _ Subtype.val_injective
              is_maximal' := ?_ },
      fun g hg => D.P_le_QT (show (g : G) ∈ D.primaryPart 3 from hg)⟩
    intro R hR hle
    have hR' : IsPGroup 3 (R.map (Subgroup.centralizer {u}).subtype) := hR.map _
    have hPR : D.primaryPart 3 ≤ R.map (Subgroup.centralizer {u}).subtype := by
      intro g hg
      exact ⟨⟨g, hPu hg⟩, hle hg, rfl⟩
    have hRu : R.map (Subgroup.centralizer {u}).subtype ≤ Subgroup.centralizer {u} := by
      rintro _ ⟨c, -, rfl⟩
      exact c.2
    have heq := E.eq_P_of_isPGroup hu huZ hR' hPR hRu
    ext c
    constructor
    · intro hc
      change (c : G) ∈ D.primaryPart 3
      rw [← heq]
      exact ⟨c, hc, rfl⟩
    · intro hc
      exact hle hc

include E in
theorem not_conj_mem_P (hgw : D.GWStep) {v : G} (hv : v ∈ D.QT) (hvP : v ∉ D.primaryPart 3)
    {g : G} (hg : g * v * g⁻¹ ∈ D.primaryPart 3) : False := by
  set u := g * v * g⁻¹ with hudef
  obtain ⟨R₂, hR₂⟩ := E.exists_sylow_le_QT hg
  have hgZ : ∀ z ∈ E.Z, g * z * g⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff, hudef]
    have hzv : z * v = v * z := E.Z_comm_QT hz hv |>.symm
    calc g * z * g⁻¹ * (g * v * g⁻¹) = g * (z * v) * g⁻¹ := by group
      _ = g * (v * z) * g⁻¹ := by rw [hzv]
      _ = g * v * g⁻¹ * (g * z * g⁻¹) := by group
  let Zg : Subgroup (Subgroup.centralizer ({u} : Set G)) :=
    ((E.Z).map (MulAut.conj g).toMonoidHom).subgroupOf (Subgroup.centralizer {u})
  have hZg : IsPGroup 3 Zg := by
    have h1 : IsPGroup 3 E.Z := (D.isPGroup_primaryPart 3).to_le E.Z_le_P
    exact (h1.map _).comap_of_injective _ Subtype.val_injective
  obtain ⟨R, hR⟩ := hZg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (Subgroup.centralizer ({u} : Set G)) R R₂
  have hcZ : ∀ z ∈ E.Z, (c : G) * g * z * ((c : G) * g)⁻¹ ∈ D.QT := by
    intro z hz
    have hmem : (⟨g * z * g⁻¹, hgZ z hz⟩ : Subgroup.centralizer ({u} : Set G)) ∈
        (R : Subgroup _) := hR ⟨z, hz, rfl⟩
    have h2 : c * ⟨g * z * g⁻¹, hgZ z hz⟩ * c⁻¹ ∈ (R₂ : Subgroup _) := by
      rw [← hc, Sylow.coe_subgroup_smul]
      exact ⟨_, hmem, rfl⟩
    have h3 := hR₂ _ h2
    convert h3 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  set r := (c : G) * g with hrdef
  have hrv : r * v * r⁻¹ = u := by
    rw [hrdef, conj_mul_eq, ← hudef]
    exact conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp c.2)
  have hh := E.three_le_h
  have hw₀P : r * E.w₀ * r⁻¹ ∈ D.primaryPart 3 := by
    have h1 := D.cube_mem_P_of_mem_QT (hcZ _ E.u₀_cube_mem_Z)
    rw [conj_pow] at h1
    have e : E.w₀ = ((E.u₀ ^ 3) ^ 3) ^ (3 ^ (E.h - 3)) := by
      rw [← pow_mul, ← pow_mul]
      show E.u₀ ^ (3 ^ (E.h - 1)) = _
      congr 1
      rw [← mul_assoc, ← pow_two, ← pow_add]
      congr 1
      omega
    rw [e, ← conj_pow]
    exact (D.primaryPart 3).pow_mem h1 _
  have hw₀3 : (r * E.w₀ * r⁻¹) ^ 3 = 1 := by
    rw [conj_pow, E.w₀_cube, mul_one, mul_inv_cancel]
  have hw₀1 : r * E.w₀ * r⁻¹ ≠ 1 := by
    intro h1
    apply E.w₀_ne_one
    have : E.w₀ = r⁻¹ * (r * E.w₀ * r⁻¹) * r := by group
    rw [this, h1]
    group
  obtain ⟨a, b, hab⟩ := E.exists_coord hw₀P
  have ha : (3 : ℤ) ^ (E.h - 1) ∣ a := by
    have h1 : E.u₀ ^ (3 * a) * E.u₁ ^ (3 * b) = 1 := by
      rw [← hw₀3, hab, E.comm.zpow_zpow a b |>.mul_pow, ← zpow_natCast, ← zpow_natCast,
        ← zpow_mul, ← zpow_mul]
      push_cast
      ring_nf
    have h2 := ((E.coord_one _ _).mp h1).1
    rw [← E.three_mul_l] at h2
    exact (mul_dvd_mul_iff_left (by norm_num)).mp h2
  obtain ⟨a', rfl⟩ := ha
  by_cases hb : (3 : ℤ) ∣ b
  ·
    have hb1 : E.u₁ ^ b = 1 := by
      obtain ⟨b', rfl⟩ := hb
      rw [zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← E.hu₁o,
        pow_orderOf_eq_one, one_zpow]
    rw [hb1, mul_one] at hab
    have hrw : r * E.w₀ * r⁻¹ = E.w₀ ^ a' := by
      rw [hab, zpow_mul]
      norm_cast
    have ha' : ¬ (3 : ℤ) ∣ a' := by
      rintro ⟨a'', rfl⟩
      apply hw₀1
      rw [hrw, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, E.w₀_cube,
        one_zpow]
    have hrT : r ∈ Subgroup.normalizer (D.T : Set G) := by
      have hw₀Z := E.w₀_mem_Z
      have hcases : a' % 3 = 1 ∨ a' % 3 = 2 := by omega
      have hw3 : ∀ m : ℤ, E.w₀ ^ (3 * m) = 1 := fun m => by
        rw [zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, E.w₀_cube,
          one_zpow]
      rcases hcases with h1 | h1
      · have hfix : r * E.w₀ * r⁻¹ = E.w₀ := by
          rw [hrw, show a' = 3 * (a' / 3) + 1 by omega, zpow_add, hw3, one_mul, zpow_one]
        exact E.centralizer_le_normalizer_T hgw hw₀Z E.w₀_ne_one
          (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hfix))
      · have hinv : r * E.w₀ * r⁻¹ = E.w₀⁻¹ := by
          rw [hrw, show a' = 3 * (a' / 3 + 1) + (-1) by omega, zpow_add, hw3, one_mul,
            zpow_neg_one]
        have hfix : (r * D.y) * E.w₀ * (r * D.y)⁻¹ = E.w₀ := by
          rw [conj_mul_eq, D.y_W _ E.w₀_mem_W, conj_inv_eq, hinv, inv_inv]
        have hry := E.centralizer_le_normalizer_T hgw hw₀Z E.w₀_ne_one
          (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq hfix))
        have e : r = r * D.y * D.y⁻¹ := by group
        rw [e]
        exact mul_mem hry (inv_mem D.y_mem_normalizer_T)
    have hrP := D.mem_normalizer_primaryPart (r := 3) (inv_mem hrT)
    apply hvP
    have e : v = r⁻¹ * u * r⁻¹⁻¹ := by rw [← hrv]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hrP u).mp hg
  ·
    exfalso
    obtain ⟨ν, hν⟩ : ∃ ν : ℕ, (3 : ℤ) ∣ a' - ν * (E.s₀ * b) := by
      have hsb : ¬ (3 : ℤ) ∣ E.s₀ * b := fun h =>
        (Int.prime_three.dvd_or_dvd h).elim E.hs₀ hb
      generalize E.s₀ * b = c at hsb ⊢
      have h1 : c % 3 = 1 ∨ c % 3 = 2 := by omega
      have h2 : a' % 3 = 0 ∨ a' % 3 = 1 ∨ a' % 3 = 2 := by omega
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 | h2
      · exact ⟨0, by push_cast; omega⟩
      · exact ⟨1, by push_cast; omega⟩
      · exact ⟨2, by push_cast; omega⟩
      · exact ⟨0, by push_cast; omega⟩
      · exact ⟨2, by push_cast; omega⟩
      · exact ⟨1, by push_cast; omega⟩
    have htconj : ∀ n : ℕ, ∀ c : ℤ, D.t ^ n * (E.u₀ ^ (3 ^ (E.h - 1) * c) * E.u₁ ^ b) *
        (D.t ^ n)⁻¹ = E.u₀ ^ (3 ^ (E.h - 1) * (c - n * (E.s₀ * b))) * E.u₁ ^ b := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ', conj_mul_eq, ih, E.t_conj, E.coord]
        constructor
        · have e : (1 + E.l * E.s₀) * (3 ^ (E.h - 1) * (c - n * (E.s₀ * b))) +
              -(E.l * E.s₀) * b - 3 ^ (E.h - 1) * (c - ((n + 1 : ℕ) : ℤ) * (E.s₀ * b)) =
              (E.l * E.l) * (E.s₀ * (c - n * (E.s₀ * b))) := by
            push_cast
            ring
          rw [e]
          exact dvd_mul_of_dvd_left E.l_mul_l _
        · have e : 1 * (3 ^ (E.h - 1) * (c - n * (E.s₀ * b))) + 1 * b - b =
              E.l * (c - n * (E.s₀ * b)) := by ring
          rw [e]
          exact dvd_mul_of_dvd_left E.three_dvd_l _
    have h1 := htconj ν a'
    obtain ⟨m, hm⟩ := hν
    have h2 : E.u₀ ^ (3 ^ (E.h - 1) * (a' - ν * (E.s₀ * b))) = 1 := by
      rw [hm, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega), zpow_mul,
        show ((3 : ℤ) ^ E.h) = ((3 ^ E.h : ℕ) : ℤ) by push_cast; rfl, zpow_natCast, E.h_def,
        ← E.hu₀o, pow_orderOf_eq_one, one_zpow]
    rw [h2, one_mul, ← hab] at h1
    have hconj : (D.t ^ ν * r) * E.w₀ * (D.t ^ ν * r)⁻¹ = E.u₁ ^ b := by
      rw [conj_mul_eq, h1]
    have hcard := card_centralizer_conj (D.t ^ ν * r) E.w₀
    rw [hconj] at hcard
    have hu₁b1 : E.u₁ ^ b ≠ 1 := by
      intro h
      apply hb
      have := orderOf_dvd_iff_zpow_eq_one.mpr h
      rwa [E.hu₁o] at this
    have hCN : Subgroup.centralizer ({E.u₁ ^ b} : Set G) = D.N := by
      apply le_antisymm (D.A_confine _ (D.A.zpow_mem E.u₁_mem_A b) hu₁b1)
      intro n hn
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact D.A_central _ (D.A.zpow_mem E.u₁_mem_A b) n hn
    rw [hCN] at hcard
    have hQw : D.QT ≤ Subgroup.centralizer {E.w₀} := by
      intro q hq
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact E.Z_comm_QT E.w₀_mem_Z hq
    have hdvd : 3 ^ (E.h + 2) ∣ Nat.card D.N := by
      rw [← E.card_QT_eq, hcard]
      exact Subgroup.card_dvd_of_le hQw
    have hN := D.factorization_card_N Nat.prime_three (by norm_num) E.three_dvd_q
    rw [E.hk] at hN
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
    rw [hN, E.h_def] at h3
    omega

include E in
theorem odd_card_centralizer (hgw : D.GWStep) {v : G} (hv : v ∈ D.QT)
    (hvP : v ∉ D.primaryPart 3) : Odd (Nat.card (Subgroup.centralizer ({v} : Set G))) := by
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({v} : Set G)) 2
    (even_iff_two_dvd.mp heven)
  have hi' : orderOf (i : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hi
  have hiv : (i : G) * v = v * i := Subgroup.mem_centralizer_singleton_iff.mp i.2
  obtain ⟨g, hg⟩ := D.exists_conj_mem_primaryPart_three E.three_dvd_q
    (D.three_element_of_mem_QT hv) hi' hiv
  exact E.not_conj_mem_P hgw hv hvP hg

end Exceptional

end DValueData

end CFSG.Semidihedral.UnitaryDValue
